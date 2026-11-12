"use strict";

// Simple Voice Chat 2.6.x / 26.x client (compat v20 & v21) for mineflayer.
// Handshake over "voicechat:" plugin channels, AES-128-GCM encrypted UDP voice.
// Speaking implemented; incoming audio parsing left as an event for STT later.

const dgram = require("dgram");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const { execFile } = require("child_process");
const OpusScript = require("opusscript");

const WHISPER_BIN =
  process.env.WHISPER_BIN ||
  path.join(process.env.HOME || "", "whisper.cpp/build/bin/whisper-cli");
const WHISPER_MODEL =
  process.env.WHISPER_MODEL ||
  path.join(process.env.HOME || "", "whisper.cpp/models/ggml-base.en.bin");

function exec(cmd, args) {
  return new Promise((resolve) => {
    execFile(cmd, args, { maxBuffer: 1e7, timeout: 60000 }, (err, so, se) =>
      resolve({ err, so: String(so || ""), se: String(se || "") }),
    );
  });
}

const MAGIC = 0xff;
const C2S = { MIC: 1, AUTH: 5, PING: 7, KEEPALIVE: 8, CONNCHECK: 9 };
const S2C = {
  POSITIONAL: 2,
  GROUP: 3,
  AUTH_ACK: 6,
  PING: 7,
  KEEPALIVE: 8,
  CONNCHECK_ACK: 10,
};

function varint(v) {
  const out = [];
  let n = v >>> 0;
  while (n >= 0x80) {
    out.push((n & 0x7f) | 0x80);
    n >>>= 7;
  }
  out.push(n);
  return Buffer.from(out);
}

function readVarint(buf, off) {
  let value = 0;
  let shift = 0;
  let i = off;
  while (i < buf.length) {
    const b = buf[i++];
    value |= (b & 0x7f) << shift;
    if ((b & 0x80) === 0) return { value: value >>> 0, size: i - off };
    shift += 7;
    if (shift > 35) break;
  }
  return null;
}

function bytesField(buf) {
  return Buffer.concat([varint(buf.length), buf]);
}

function strField(s) {
  return bytesField(Buffer.from(String(s), "utf8"));
}

function readString(buf, off) {
  const v = readVarint(buf, off);
  if (!v) return null;
  const start = off + v.size;
  const end = start + v.value;
  if (end > buf.length) return null;
  return { value: buf.subarray(start, end).toString("utf8"), size: v.size + v.value };
}

function uuidToBuf(hex) {
  return Buffer.from(String(hex).replace(/-/g, ""), "hex");
}

function bufToUuid(buf) {
  const h = buf.toString("hex");
  return `${h.slice(0, 8)}-${h.slice(8, 12)}-${h.slice(12, 16)}-${h.slice(16, 20)}-${h.slice(20)}`;
}

function pcmRms(buf) {
  const n = buf.length >> 1;
  if (!n) return 0;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    const s = buf.readInt16LE(i * 2);
    sum += s * s;
  }
  return Math.sqrt(sum / n);
}

// Boost quiet incoming audio (e.g. +300% => gain 3) before gating/STT.
function amplifyPcm(buf, gain) {
  if (!gain || gain === 1) return buf;
  const out = Buffer.allocUnsafe(buf.length);
  for (let i = 0; i + 1 < buf.length; i += 2) {
    let s = Math.round(buf.readInt16LE(i) * gain);
    if (s > 32767) s = 32767;
    else if (s < -32768) s = -32768;
    out.writeInt16LE(s, i);
  }
  return out;
}

// Stuff whisper likes to hallucinate on silence/noise/background.
const HALLUCINATIONS = [
  /^[\s.,!?\-]*$/,
  /^\(.*\)$/,
  /^\[.*\]$/,
  /chatter|background noise|crosstalk|inaudible|mumbling|noise/i,
  /thank you\.?$/i,
  /thanks for watching/i,
  /please subscribe/i,
  /subscribe to/i,
  /subtitles? by/i,
  /amara\.org/i,
  /\[blank.?audio\]/i,
  /\[music\]/i,
  /\[applause\]/i,
  /^\s*(you|bye|okay|ok|mm+|uh+|um+|hmm+|so|the|a|i|and)\.?\s*$/i,
];

function isNoiseText(text) {
  const t = text.trim();
  if (t.length < 3) return true;
  if (!/[a-z]{2,}/i.test(t)) return true;
  return HALLUCINATIONS.some((re) => re.test(t));
}

class Svc {
  constructor(bot, opts = {}, serverCfg = {}) {
    this.bot = bot;
    this.opts = opts;
    this.serverCfg = serverCfg;
    this.log = opts.log || (() => {});
    this.reset();
    this.socket = dgram.createSocket("udp4");
    this.socket.on("error", (e) => this.log("[SVC] socket error: " + e.message));
    this.socket.on("message", (m) => this.onDatagram(m));
    this.seq = 0n;
    this.micQueue = [];
    this.sending = false;
    this.keepTimer = null;
    this.attemptIndex = 0;
    this.flushTimer = setInterval(() => this.checkFlush(), 250);
  }

  reset() {
    this.key = null;
    this.connectionId = null;
    this.playerUuid = null;
    this.host = null;
    this.port = null;
    this.connected = false;
    this.authenticated = false;
    this.inGroup = null;
    this.secretTried = 0;
    this.names = new Map();
    this.buffers = new Map();
    this.decodeQueue = Promise.resolve();
    this.stt = (this.opts && this.opts.stt) || {};
    this.silenceMs = this.stt.silenceMs || 1800;
    this.minSpeechMs = this.stt.minSpeechMs || 350;
    this.maxMs = this.stt.maxMs || 12000;
    this.energyThreshold = this.stt.energyThreshold || 300;
    this.gain = this.stt.gain || 3;
    this.noiseFloor = this.energyThreshold;
    try {
      this.decoder = new OpusScript(48000, 1);
    } catch (e) {
      this.decoder = null;
    }
  }

  start() {
    this.bot.on("spawn", () => this.requestSecret());
    this.bot._client.on("custom_payload", (p) => this.onCustomPayload(p));
  }

  requestSecret() {
    if (this.key) return;
    // SVC requires an exact match; try newest first then walk down.
    const versions = [21, 20, 19, 18];
    const v = versions[this.attemptIndex % versions.length];
    this.attemptIndex++;
    this.log(`[SVC] requesting secret (compat v${v})`);
    this.writeControl("voicechat:request_secret", Buffer.from(Int32BE(v), "hex"));
    if (!this.secretTimer) {
      this.secretTimer = setInterval(() => {
        if (this.key) {
          clearInterval(this.secretTimer);
          this.secretTimer = null;
          return;
        }
        this.requestSecret();
      }, 6000);
    }
  }

  onCustomPayload(p) {
    if (!p) return;
    let ch = p.channel;
    if (Buffer.isBuffer(ch)) ch = ch.toString("utf8");
    if (typeof ch !== "string" || !ch.startsWith("voicechat:")) return;
    const name = ch.slice("voicechat:".length);
    const data = Buffer.isBuffer(p.data) ? p.data : Buffer.from(p.data || []);
    this.log(`[SVC] rx ${name} (${data.length}b)`);
    try {
      if (name === "secret") this.onSecret(data);
      else if (name === "add_group") this.onAddGroup(data);
      else if (name === "joined_group") this.onJoinedGroup(data);
      else if (name === "state") this.onState(data);
      else if (name === "states") this.onStates(data);
      else if (name === "remove_state") {
        this.names.delete(bufToUuid(data.subarray(0, 16)));
      }
    } catch (e) {
      this.log("[SVC] parse error on " + name + ": " + e.message);
    }
  }

  onSecret(data) {
    if (this.key) return;
    // v21: secret(16) + connectionId(16) + port(i32) + player(16) + codec(1) +
    //      mtu(i32) + distance(f64) + keepAlive(i32) + groups(1) + host(str) + rec(1)
    // v20: secret(16) + port(i32) + player(16) + ... (no connectionId)
    let off = 0;
    const secret = data.subarray(off, off + 16);
    off += 16;
    let connectionId = null;
    let port;
    let player;
    // Heuristic: v21 has 16 more bytes before port. Peek plausible port.
    const tryPort = (o) => (o + 4 <= data.length ? data.readInt32BE(o) : -1);
    if (tryPort(off) > 0 && tryPort(off) < 65536) {
      // looks like v20 (port right after secret)
      port = tryPort(off);
      off += 4;
    } else {
      connectionId = data.subarray(off, off + 16);
      off += 16;
      port = data.readInt32BE(off);
      off += 4;
    }
    player = data.subarray(off, off + 16);
    off += 16;
    off += 1; // codec
    off += 4; // mtu
    off += 8; // distance
    off += 4; // keepAlive
    off += 1; // groups
    let host = "";
    const hs = readString(data, off);
    if (hs) {
      host = hs.value;
      off += hs.size;
    }
    this.key = Buffer.from(secret);
    this.connectionId = connectionId;
    this.playerUuid = player;
    this.port = port;
    this.host = host || this.serverCfg.ip;
    this.mtu = 1024;
    this.log(
      `[SVC] got secret: port=${port} host=${this.host} conn=${connectionId ? bufToUuid(connectionId) : "none"}`,
    );
    this.connectUdp();
  }

  connectUdp() {
    const authBody = () =>
      this.connectionId ? Buffer.alloc(0) : Buffer.concat([this.playerUuid, this.key]);
    const resolveHost = this.host;
    this.socket.connect(this.port, resolveHost, () => {
      this.log("[SVC] UDP socket connected to " + resolveHost + ":" + this.port);
      this.sendPacket(C2S.AUTH, authBody());
      this.log("[SVC] sent authenticate");
    });
    // Retry auth/connection-check until connected (UDP can drop the first few)
    let tries = 0;
    const retry = setInterval(() => {
      if (this.connected || ++tries > 30) {
        clearInterval(retry);
        return;
      }
      if (this.authenticated) this.sendPacket(C2S.CONNCHECK, Buffer.alloc(0));
      else this.sendPacket(C2S.AUTH, authBody());
    }, 2000);
    // periodic keepalive once connected
    this.keepTimer = setInterval(() => {
      if (this.connected) this.sendPacket(C2S.KEEPALIVE, Buffer.alloc(0));
    }, 15000);
  }

  envelope(sealed) {
    const id = this.connectionId || this.playerUuid;
    return Buffer.concat([Buffer.from([MAGIC]), id, varint(sealed.length), sealed]);
  }

  seal(plain) {
    const iv = crypto.randomBytes(12);
    const cipher = crypto.createCipheriv("aes-128-gcm", this.key, iv);
    const ct = Buffer.concat([cipher.update(plain), cipher.final()]);
    const tag = cipher.getAuthTag();
    return Buffer.concat([iv, ct, tag]);
  }

  open(sealed) {
    if (sealed.length < 28) return null;
    const iv = sealed.subarray(0, 12);
    const tag = sealed.subarray(sealed.length - 16);
    const ct = sealed.subarray(12, sealed.length - 16);
    const d = crypto.createDecipheriv("aes-128-gcm", this.key, iv);
    d.setAuthTag(tag);
    return Buffer.concat([d.update(ct), d.final()]);
  }

  sendPacket(type, body) {
    if (!this.key) return;
    try {
      const plain = Buffer.concat([Buffer.from([type]), body]);
      const dg = this.envelope(this.seal(plain));
      this.socket.send(dg);
    } catch (e) {
      this.log("[SVC] send error: " + e.message);
    }
  }

  onDatagram(msg) {
    if (!this.key || msg.length < 3 || msg[0] !== MAGIC) return;
    const v = readVarint(msg, 1);
    if (!v) return;
    const sealed = msg.subarray(1 + v.size, 1 + v.size + v.value);
    let plain;
    try {
      plain = this.open(sealed);
    } catch (e) {
      return;
    }
    if (!plain || plain.length < 1) return;
    const type = plain[0];
    const body = plain.subarray(1);
    this.handlePacket(type, body);
  }

  handlePacket(type, body) {
    switch (type) {
      case S2C.AUTH_ACK:
        this.authenticated = true;
        this.log("[SVC] authenticated, sending connection check");
        this.sendPacket(C2S.CONNCHECK, Buffer.alloc(0));
        break;
      case S2C.CONNCHECK_ACK:
        this.connected = true;
        this.log("[SVC] connected to voice server");
        this.onConnected();
        break;
      case S2C.PING:
        this.sendPacket(C2S.PING, body);
        break;
      case S2C.KEEPALIVE:
        this.sendPacket(C2S.KEEPALIVE, Buffer.alloc(0));
        break;
      case S2C.POSITIONAL:
      case S2C.GROUP:
        this.onVoicePacket(type, body);
        break;
      default:
        break;
    }
  }

  onConnected() {
    const group = this.opts.group;
    if (!group) {
      this.log("[SVC] no group configured");
      return;
    }
    if (this.opts.create) {
      const body = Buffer.concat([
        strField(group),
        Buffer.from([this.opts.password ? 1 : 0]),
        this.opts.password ? strField(this.opts.password) : Buffer.alloc(0),
        Buffer.from([0, 0]), // kind normal (short)
      ]);
      this.writeControl("voicechat:create_group", body);
      this.log(`[SVC] creating group "${group}"`);
    }
  }

  onAddGroup(data) {
    if (data.length < 16) return;
    const id = data.subarray(0, 16);
    const nm = readString(data, 16);
    if (!nm) return;
    const name = nm.value;
    const want = this.opts.group;
    if (want && name === want && !this.inGroup) {
      const pw = this.opts.password || "";
      const body = Buffer.concat([
        id,
        Buffer.from([pw ? 1 : 0]),
        pw ? strField(pw) : Buffer.alloc(0),
      ]);
      this.writeControl("voicechat:set_group", body);
      this.log(`[SVC] joining group "${name}"`);
    }
  }

  onJoinedGroup(data) {
    if (data.length < 1) return;
    let off = 0;
    const has = data[off++] !== 0;
    let id = null;
    if (has && data.length >= off + 16) {
      id = data.subarray(off, off + 16);
      off += 16;
    }
    this.inGroup = id;
    this.log(`[SVC] joined group ${id ? bufToUuid(id) : "none"}`);
  }

  onState(data) {
    // flag disabled, flag disconnected, uuid(16), text name, flag + [uuid group]
    let off = 0;
    const disabled = data[off++] !== 0;
    const disconnected = data[off++] !== 0;
    const uuid = bufToUuid(data.subarray(off, off + 16));
    off += 16;
    const nm = readString(data, off);
    if (nm) {
      if (disconnected || disabled) this.names.delete(uuid);
      else this.names.set(uuid, nm.value);
    }
  }

  onStates(data) {
    if (data.length < 4) return;
    let off = 0;
    const count = data.readInt32BE(off);
    off += 4;
    for (let i = 0; i < count && off < data.length; i++) {
      const disabled = data[off++] !== 0;
      const disconnected = data[off++] !== 0;
      const uuid = bufToUuid(data.subarray(off, off + 16));
      off += 16;
      const nm = readString(data, off);
      if (nm) {
        off += nm.size;
        if (!disconnected && !disabled) this.names.set(uuid, nm.value);
      } else break;
      if (off < data.length) {
        const hasGroup = data[off++] !== 0;
        if (hasGroup) off += 16;
      }
    }
  }

  onVoicePacket(type, body) {
    if (!this.decoder) return;
    try {
      let off = 0;
      const senderBuf = body.subarray(0, 16);
      if (this.playerUuid && Buffer.compare(senderBuf, this.playerUuid) === 0) return; // own voice
      const sender = bufToUuid(senderBuf);
      off += 16;
      off += 16; // channel uuid
      const v = readVarint(body, off);
      if (!v) return;
      off += v.size;
      const opus = body.subarray(off, off + v.value);
      if (!opus.length) return;
      const pcm = this.decoder.decode(opus);
      this.bot.emit("svc_voice", { sender, opus });
      this.pushAudio(sender, pcm);
    } catch (e) {
      this.decodeErr = (this.decodeErr || 0) + 1;
      if (this.decodeErr <= 3) this.log("[SVC] voice decode error: " + e.message);
    }
  }

  pushAudio(sender, pcmRaw) {
    const pcm = amplifyPcm(pcmRaw, this.gain);
    let b = this.buffers.get(sender);
    if (!b) {
      b = { chunks: [], last: 0, lastVoice: 0, speechMs: 0 };
      this.buffers.set(sender, b);
    }
    b.chunks.push(pcm);
    b.last = Date.now();

    const rms = pcmRms(pcm);
    // Noise floor follows quiet levels quickly, creeps up slowly on loud ones.
    if (rms < this.noiseFloor) this.noiseFloor = this.noiseFloor * 0.95 + rms * 0.05;
    else this.noiseFloor = this.noiseFloor * 0.999 + rms * 0.001;
    const threshold = Math.max(this.energyThreshold, this.noiseFloor * 2);
    const active = rms > threshold;
    if (active) {
      b.lastVoice = Date.now();
      b.speechMs += 20;
    }
    this.voiceCount = (this.voiceCount || 0) + 1;
    if (this.voiceCount <= 5 || this.voiceCount % 100 === 0) {
      this.log(
        `[SVC] rx voice packets=${this.voiceCount} rms=${Math.round(rms)} floor=${Math.round(this.noiseFloor)} thresh=${Math.round(threshold)}`,
      );
    }

    const total = b.chunks.reduce((n, c) => n + c.length, 0);
    if (total >= 48000 * 2 * (this.maxMs / 1000)) this.flush(sender);
  }

  checkFlush() {
    if (!this.stt || !this.stt.enabled) return;
    const now = Date.now();
    for (const [sender, b] of this.buffers) {
      if (!b.chunks.length) continue;
      const sinceVoice = now - (b.lastVoice || b.last);
      if (sinceVoice > this.silenceMs) this.flush(sender);
    }
  }

  flush(sender) {
    const b = this.buffers.get(sender);
    if (!b) return;
    this.buffers.delete(sender);
    // Only transcribe if there was real, sustained speech (not a blip/noise)
    if (b.speechMs < this.minSpeechMs) {
      this.skipCount = (this.skipCount || 0) + 1;
      if (this.skipCount <= 5)
        this.log(`[STT] skipped short/noisy clip (${b.speechMs}ms < ${this.minSpeechMs}ms)`);
      return;
    }
    const pcm = Buffer.concat(b.chunks);
    this.decodeQueue = this.decodeQueue.then(() => this.transcribe(sender, pcm));
  }

  async transcribe(sender, pcm) {
    const base = path.join(require("os").tmpdir(), `svc_${Date.now()}`);
    const raw = base + ".raw";
    const wav = base + ".wav";
    try {
      fs.writeFileSync(raw, pcm);
      await exec(process.env.FFMPEG_PATH || "ffmpeg", [
        "-y",
        "-v",
        "error",
        "-f",
        "s16le",
        "-ar",
        "48000",
        "-ac",
        "1",
        "-i",
        raw,
        "-ar",
        "16000",
        "-ac",
        "1",
        wav,
      ]);
      const r = await exec(WHISPER_BIN, [
        "-m",
        WHISPER_MODEL,
        "-f",
        wav,
        "-nt",
        "-np",
        "-l",
        "en",
        "--prompt",
        "Jarvis. The player is talking to Jarvis, the AI assistant. Jarvis, Jarvis.",
      ]);
      const text = (r.so + "\n" + r.se)
        .split("\n")
        .map((l) => l.trim())
        .filter((l) => l && !l.startsWith("whisper_") && !l.includes("read_audio"))
        .join(" ")
        .replace(/\[[^\]]*\]/g, "")
        .replace(/\b(garos|joris|jervis|jarvus|jarves|jarvs|darvis|jaros|darrows)\b/gi, "Jarvis")
        .trim();
      if (text) {
        if (isNoiseText(text)) return;
        const name = this.names.get(sender) || "Unknown";
        this.log(`[STT] ${name}: ${text}`);
        this.bot.emit("svc_transcript", { sender, name, text });
      }
    } catch (e) {
      this.log("[STT] error: " + e.message);
    } finally {
      try {
        fs.unlinkSync(raw);
      } catch (e) {}
      try {
        fs.unlinkSync(wav);
      } catch (e) {}
    }
  }

  writeControl(channel, data) {
    try {
      this.bot._client.write("custom_payload", { channel, data });
    } catch (e) {
      this.log("[SVC] control write error: " + e.message);
    }
  }

  // ---------- speaking ----------
  enqueuePcm(pcm) {
    const frameBytes = 960 * 2; // 20ms mono s16le @48k
    for (let i = 0; i + frameBytes <= pcm.length; i += frameBytes) {
      this.micQueue.push(pcm.subarray(i, i + frameBytes));
    }
    this.pump();
  }

  stopSpeaking() {
    this.micQueue = [];
    this.sendMic(Buffer.alloc(0));
  }

  sendMic(opus) {
    const seq = Buffer.alloc(8);
    seq.writeBigInt64BE(this.seq++);
    const body = Buffer.concat([bytesField(opus), seq, Buffer.from([0])]);
    this.sendPacket(C2S.MIC, body);
  }

  async pump() {
    if (this.sending) return;
    this.sending = true;
    const frames = this.micQueue;
    this.micQueue = [];

    // Pre-encode everything up front (cheap, avoids per-frame GC hiccups).
    const enc = new OpusScript(48000, 1, OpusScript.Application.VOIP);
    try {
      enc.setBitrate(this.opts.bitrate || 32000);
    } catch (e) {}
    const packets = [];
    for (const f of frames) {
      try {
        packets.push(enc.encode(f, 960));
      } catch (e) {}
    }
    try {
      enc.delete();
    } catch (e) {}

    // Drift-corrected pacing: frame N is due at t0 + N*20ms, regardless of
    // how long encoding/sending actually took. Prevents underrun/choppiness.
    const t0 = performance.now();
    for (let i = 0; i < packets.length; i++) {
      if (!this.connected) break;
      const due = t0 + i * 20;
      const wait = due - performance.now();
      if (wait > 1) await new Promise((r) => setTimeout(r, wait));
      this.sendMic(packets[i]);
    }

    this.sending = false;
    if (this.micQueue.length) this.pump();
  }

  async speakFile(file, ffmpeg) {
    return new Promise((resolve) => {
      const chunks = [];
      ffmpeg(file)
        .audioCodec("pcm_s16le")
        .format("s16le")
        .audioChannels(1)
        .audioFrequency(48000)
        .on("error", (e) => {
          this.log("[SVC] ffmpeg error: " + e.message);
          resolve();
        })
        .pipe()
        .on("data", (c) => chunks.push(c))
        .on("end", () => {
          this.enqueuePcm(Buffer.concat(chunks));
          resolve();
        });
    });
  }
}

function Int32BE(v) {
  const b = Buffer.alloc(4);
  b.writeInt32BE(v, 0);
  return b.toString("hex");
}

module.exports = { Svc };