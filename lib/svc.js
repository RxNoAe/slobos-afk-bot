"use strict";

// Simple Voice Chat 2.6.x / 26.x client (compat v20 & v21) for mineflayer.
// Handshake over "voicechat:" plugin channels, AES-128-GCM encrypted UDP voice.
// Speaking implemented; incoming audio parsing left as an event for STT later.

const dgram = require("dgram");
const crypto = require("crypto");
const OpusScript = require("opusscript");

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
  }

  reset() {
    this.key = null;
    this.connectionId = null;
    this.playerUuid = null;
    this.host = null;
    this.port = null;
    this.connected = false;
    this.inGroup = null;
    this.secretTried = 0;
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
    const sendAuth = () => {
      // In v21 AuthenticatePacket is empty; in v20 it carries player+secret.
      let body = Buffer.alloc(0);
      if (!this.connectionId) body = Buffer.concat([this.playerUuid, this.key]);
      this.sendPacket(C2S.AUTH, body);
      this.log("[SVC] sent authenticate");
    };
    const resolveHost = this.host;
    this.socket.connect(this.port, resolveHost, () => {
      this.log("[SVC] UDP socket connected to " + resolveHost + ":" + this.port);
      sendAuth();
    });
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

  onVoicePacket(type, body) {
    // Placeholder for STT: emit decoded Opus frames
    try {
      let off = 0;
      const sender = body.subarray(0, 16);
      off += 16;
      off += 16; // channel uuid
      const v = readVarint(body, off);
      if (!v) return;
      off += v.size;
      const opus = body.subarray(off, off + v.value);
      this.bot.emit("svc_voice", { sender: bufToUuid(sender), opus });
    } catch (e) {}
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
    const enc = new OpusScript(48000, 1, OpusScript.Application.VOIP);
    while (this.micQueue.length) {
      if (!this.connected) {
        this.micQueue = [];
        break;
      }
      const frame = this.micQueue.shift();
      let opus;
      try {
        opus = enc.encode(frame, 960);
      } catch (e) {
        this.log("[SVC] opus encode error: " + e.message);
        continue;
      }
      this.sendMic(opus);
      await new Promise((r) => setTimeout(r, 20));
    }
    try {
      enc.delete();
    } catch (e) {}
    this.sending = false;
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