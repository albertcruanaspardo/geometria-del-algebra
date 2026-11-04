/* Geometría del Álgebra — núcleo de álgebra exacta.
   Expresiones como árboles: num (racional exacto con BigInt), sym, add, mul, pow, fn.
   Los constructores «crudos» (Add, Mul, Pow…) conservan la forma escrita por el estudiante;
   los canónicos (cadd, cmul, cpow…) simplifican: reducen semejantes, juntan potencias y ordenan. */
"use strict";
const CAS = (() => {
  /* ---------- racionales exactos ---------- */
  const babs = a => a < 0n ? -a : a;
  const bgcd = (a, b) => { a = babs(a); b = babs(b); while (b) [a, b] = [b, a % b]; return a; };
  function Q(n, d = 1n) {
    n = BigInt(n); d = BigInt(d); if (d === 0n) throw Error("División por cero");
    if (d < 0n) { n = -n; d = -d; } const g = bgcd(n, d) || 1n; return { n: n / g, d: d / g };
  }
  const ZERO = Q(0), ONE = Q(1);
  const qadd = (a, b) => Q(a.n * b.d + b.n * a.d, a.d * b.d), qsub = (a, b) => Q(a.n * b.d - b.n * a.d, a.d * b.d);
  const qmul = (a, b) => Q(a.n * b.n, a.d * b.d), qdiv = (a, b) => Q(a.n * b.d, a.d * b.n);
  const qneg = a => ({ n: -a.n, d: a.d }), qeq = (a, b) => a.n === b.n && a.d === b.d;
  const qnum = a => Number(a.n) / Number(a.d), qint = a => a.d === 1n, qsgn = a => a.n > 0n ? 1 : a.n < 0n ? -1 : 0;
  function qpow(a, k) { k = BigInt(k); if (k < 0n) { if (a.n === 0n) throw Error("División por cero"); return qpow(Q(a.d, a.n), -k); } let r = ONE; for (let i = 0n; i < k; i++) r = qmul(r, a); return r; }
  function qFromNumber(x) {
    if (!isFinite(x)) throw Error("Número no finito");
    if (Number.isInteger(x)) return Q(BigInt(x));
    let h0 = 0n, h1 = 1n, k0 = 1n, k1 = 0n, y = Math.abs(x);
    for (let i = 0; i < 40; i++) {
      const a = Math.floor(y), A = BigInt(a);
      [h0, h1] = [h1, A * h1 + h0]; [k0, k1] = [k1, A * k1 + k0];
      if (Math.abs(Number(h1) / Number(k1) - Math.abs(x)) <= 1e-12 * Math.max(1, Math.abs(x))) break;
      const f = y - a; if (f < 1e-15) break; y = 1 / f;
    }
    return Q(x < 0 ? -h1 : h1, k1);
  }
  const qFromDec = s => { const [i, f = ""] = s.split("."); return Q(BigInt((i || "0") + f), 10n ** BigInt(f.length)); };
  function iroot(n, k) {             // raíz k-ésima entera exacta de n ≥ 0, o null
    k = BigInt(k); if (n < 0n) return null; if (n < 2n) return n;
    let lo = 0n, hi = 1n; while (hi ** k <= n) hi *= 2n;
    while (lo < hi - 1n) { const m = (lo + hi) / 2n; if (m ** k <= n) lo = m; else hi = m; }
    return lo ** k === n ? lo : null;
  }

  /* ---------- nodos y constructores crudos ---------- */
  const num = q => ({ t: "num", q }), int = k => num(Q(k)), frac = (a, b) => num(Q(a, b)), sym = s => ({ t: "sym", s });
  const isNum = e => e.t === "num", isZero = e => isNum(e) && e.q.n === 0n, isOne = e => isNum(e) && qeq(e.q, ONE);
  function Add(...xs) { const a = []; for (const x of xs) x.t === "add" ? a.push(...x.a) : a.push(x); return a.length === 1 ? a[0] : a.length ? { t: "add", a } : int(0); }
  function Mul(...xs) { const a = []; for (const x of xs) x.t === "mul" ? a.push(...x.a) : a.push(x); return a.length === 1 ? a[0] : a.length ? { t: "mul", a } : int(1); }
  const Pow = (b, e) => ({ t: "pow", b, e }), Fn = (f, x) => ({ t: "fn", f, x });
  function Neg(x) {
    if (isNum(x)) return num(qneg(x.q));
    if (x.t === "mul" && isNum(x.a[0])) { const c = qneg(x.a[0].q); return qeq(c, ONE) ? Mul(...x.a.slice(1)) : Mul(num(c), ...x.a.slice(1)); }
    return Mul(int(-1), x);
  }
  const Sub = (a, b) => Add(a, Neg(b)), Div = (a, b) => Mul(a, Pow(b, int(-1))), Sqrt = x => Pow(x, frac(1, 2));

  function key(e) {
    if (e._k !== undefined) return e._k; let k;
    switch (e.t) {
      case "num": k = "#" + e.q.n + "/" + e.q.d; break;
      case "sym": k = e.s; break;
      case "add": k = "+(" + e.a.map(key).join(",") + ")"; break;
      case "mul": k = "*(" + e.a.map(key).join(",") + ")"; break;
      case "pow": k = "^(" + key(e.b) + "," + key(e.e) + ")"; break;
      case "fn": k = e.f + "(" + key(e.x) + ")"; break;
    }
    e._k = k; return k;
  }
  const termsOf = e => e.t === "add" ? e.a : [e];
  const factorsOf = e => e.t === "mul" ? e.a : [e];

  /* ---------- forma canónica ---------- */
  const ONEn = int(1);
  function split(t) {                // término = coeficiente racional · resto
    if (isNum(t)) return [t.q, null];
    if (t.t === "mul") { const ns = t.a.filter(isNum), rs = t.a.filter(f => !isNum(f)); let c = ONE; ns.forEach(n => c = qmul(c, n.q)); return [c, rs.length ? (rs.length === 1 ? rs[0] : { t: "mul", a: rs }) : null]; }
    return [ONE, t];
  }
  function withCoef(q, r) { if (!r) return num(q); if (qeq(q, ONE)) return r; return { t: "mul", a: [num(q), ...(r.t === "mul" ? r.a : [r])] }; }
  const byKey = (x, y) => key(x) < key(y) ? -1 : key(x) > key(y) ? 1 : 0;
  function cadd(...xs) {
    const ts = []; const fl = x => x.t === "add" ? x.a.forEach(fl) : ts.push(x); xs.forEach(fl);
    let c = ZERO; const m = new Map();
    for (const t of ts) { const [q, r] = split(t); if (!r) { c = qadd(c, q); continue; } const k = key(r), o = m.get(k); if (o) o.q = qadd(o.q, q); else m.set(k, { q, r }); }
    const out = []; for (const { q, r } of m.values()) if (q.n !== 0n) out.push(withCoef(q, r));
    if (c.n !== 0n) out.push(num(c));
    if (!out.length) return int(0); if (out.length === 1) return out[0];
    return { t: "add", a: out.sort(byKey) };
  }
  function cmul(...xs) {
    const fs = []; const fl = x => x.t === "mul" ? x.a.forEach(fl) : fs.push(x); xs.forEach(fl);
    let c = ONE; const m = new Map();
    for (const f of fs) {
      if (isNum(f)) { c = qmul(c, f.q); continue; }
      const [b, e] = f.t === "pow" ? [f.b, f.e] : [f, ONEn];
      const k = key(b), o = m.get(k); if (o) o.e = cadd(o.e, e); else m.set(k, { b, e });
    }
    if (c.n === 0n) return int(0);
    const out = [];
    for (const { b, e } of m.values()) {
      const p = cpow(b, e);
      if (isNum(p)) c = qmul(c, p.q); else if (p.t === "mul") p.a.forEach(f => isNum(f) ? (c = qmul(c, f.q)) : out.push(f)); else out.push(p);
    }
    out.sort(byKey);
    if (!out.length) return num(c);
    if (qeq(c, ONE)) return out.length === 1 ? out[0] : { t: "mul", a: out };
    return { t: "mul", a: [num(c), ...out] };
  }
  function cpow(b, e) {
    if (isNum(e)) {
      const q = e.q;
      if (q.n === 0n) return int(1);
      if (qeq(q, ONE)) return b;
      if (isNum(b)) {
        if (b.q.n === 0n) { if (q.n < 0n) throw Error("División por cero"); return int(0); }
        if (qeq(b.q, ONE)) return int(1);
        if (qint(q) && babs(q.n) <= 400n) return num(qpow(b.q, q.n));
        const neg = b.q.n < 0n, r = q.d;
        if (!neg || r % 2n === 1n) { const rn = iroot(babs(b.q.n), r), rd = iroot(b.q.d, r); if (rn !== null && rd !== null) return num(qpow(Q(neg ? -rn : rn, rd), q.n)); }
      }
      if (b.t === "pow" && qint(q)) return cpow(b.b, cmul(b.e, e));
      if (b.t === "mul" && qint(q)) return cmul(...b.a.map(f => cpow(f, e)));
    }
    return { t: "pow", b, e };
  }
  function cfn(f, x) {
    if (f === "sqrt") return cpow(x, frac(1, 2));
    if (f === "cbrt") return cpow(x, frac(1, 3));
    if (f === "exp") return cpow(sym("e"), x);
    if (isNum(x)) {
      const z = x.q.n === 0n;
      if (f === "abs") return num(Q(babs(x.q.n), x.q.d));
      if (z && ["sin", "tan", "asin", "atan"].includes(f)) return int(0);
      if (z && f === "cos") return int(1);
      if ((f === "ln" || f === "log") && qeq(x.q, ONE)) return int(0);
      if (f === "log" && qint(x.q) && x.q.n > 0n) { let n = x.q.n, k = 0; while (n > 1n && n % 10n === 0n) { n /= 10n; k++; } if (n === 1n) return int(k); }
    }
    if (f === "abs" && !symbols(x).length && evalN(x) > 0) return x;
    if (["sin", "cos", "tan"].includes(f) && !symbols(x).length) {          // seno, coseno y tangente de ángulos notables
      const r = evalN(x) / Math.PI;
      if ([1, 2, 3, 4, 6].some(d => Math.abs(r * d - Math.round(r * d)) < 1e-12)) {
        const v = FN[f](evalN(x)), s2 = cpow(int(2), frac(1, 2)), s3 = cpow(int(3), frac(1, 2));
        const cand = [int(0), int(1), int(-1), frac(1, 2), frac(-1, 2), cmul(frac(1, 2), s2), cmul(frac(-1, 2), s2), cmul(frac(1, 2), s3), cmul(frac(-1, 2), s3), cmul(frac(1, 3), s3), cmul(frac(-1, 3), s3), s3, cmul(int(-1), s3)];
        const hit = cand.find(c => Math.abs(evalN(c) - v) < 1e-12); if (hit) return hit;
      }
    }
    if (["asin", "acos", "atan"].includes(f) && !symbols(x).length) {        // ángulos notables exactos
      const v = evalN(x), g = { asin: Math.sin, acos: Math.cos, atan: Math.tan }[f], [k0, k1] = f === "acos" ? [0, 12] : [-6, 6];
      if (isFinite(v)) for (let k = k0; k <= k1; k++) { if (f === "atan" && Math.abs(k) === 6) continue; if (Math.abs(g(k * Math.PI / 12) - v) < 1e-12) return k === 0 ? int(0) : cmul(frac(k, 12), sym("π")); }
    }
    if (f === "ln" && x.t === "sym" && x.s === "e") return int(1);
    if (f === "ln" && x.t === "pow" && x.b.t === "sym" && x.b.s === "e") return x.e;
    return { t: "fn", f, x };
  }
  function simplify(e) {
    switch (e.t) {
      case "add": return cadd(...e.a.map(simplify));
      case "mul": return cmul(...e.a.map(simplify));
      case "pow": return cpow(simplify(e.b), simplify(e.e));
      case "fn": return cfn(e.f, simplify(e.x));
      default: return e;
    }
  }
  const dist = (A, B) => cadd(...termsOf(A).flatMap(a => termsOf(B).map(b => cmul(a, b))));
  function expand(e) {
    switch (e.t) {
      case "add": return cadd(...e.a.map(expand));
      case "mul": { let acc = int(1); for (const f of e.a.map(expand)) { acc = dist(acc, f); if (termsOf(acc).length > 4000) throw Error("Desarrollo demasiado grande"); } return acc; }
      case "pow": {
        const b = expand(e.b), ex = expand(e.e);
        if (b.t === "add" && isNum(ex) && qint(ex.q) && ex.q.n > 1n && ex.q.n <= 40n) { let r = b; for (let i = 1n; i < ex.q.n; i++) r = dist(r, b); return r; }
        if (b.t === "add" && isNum(ex) && qint(ex.q) && ex.q.n < 0n) { const p = expand(Pow(b, num(qneg(ex.q)))); return cpow(p, int(-1)); }
        return cpow(b, ex);
      }
      case "fn": return cfn(e.f, expand(e.x));
      default: return e;
    }
  }

  /* ---------- símbolos, evaluación y sustitución ---------- */
  function symbols(e, s = new Set()) {
    if (e.t === "sym") { if (e.s !== "π" && e.s !== "e") s.add(e.s); }
    else if (e.t === "add" || e.t === "mul") e.a.forEach(x => symbols(x, s));
    else if (e.t === "pow") { symbols(e.b, s); symbols(e.e, s); }
    else if (e.t === "fn") symbols(e.x, s);
    return [...s].sort();
  }
  const FN = { sin: Math.sin, cos: Math.cos, tan: Math.tan, asin: Math.asin, acos: Math.acos, atan: Math.atan, ln: Math.log, log: Math.log10, exp: Math.exp, abs: Math.abs, sqrt: Math.sqrt, cbrt: Math.cbrt };
  function evalN(e, env = {}) {
    switch (e.t) {
      case "num": return qnum(e.q);
      case "sym": return e.s === "π" ? Math.PI : e.s === "e" ? Math.E : (env[e.s] ?? NaN);
      case "add": return e.a.reduce((s, x) => s + evalN(x, env), 0);
      case "mul": return e.a.reduce((s, x) => s * evalN(x, env), 1);
      case "pow": {
        const b = evalN(e.b, env), x = evalN(e.e, env);
        if (b < 0 && isNum(e.e) && !qint(e.e.q) && e.e.q.d % 2n === 1n) return -Math.pow(-b, x);
        if (b === 0 && x < 0) return NaN;
        return Math.pow(b, x);
      }
      case "fn":
        if (e.f === "deriv") { const x = env.x, h = 1e-5 * (1 + Math.abs(x)); return (evalN(e.x, { ...env, x: x + h }) - evalN(e.x, { ...env, x: x - h })) / (2 * h); }
        if (e.f === "integ") return NaN;
        return FN[e.f](evalN(e.x, env));
    }
  }
  function subs(e, map) {
    switch (e.t) {
      case "sym": return map[e.s] ?? e;
      case "add": return Add(...e.a.map(x => subs(x, map)));
      case "mul": return Mul(...e.a.map(x => subs(x, map)));
      case "pow": return Pow(subs(e.b, map), subs(e.e, map));
      case "fn": return Fn(e.f, subs(e.x, map));
      default: return e;
    }
  }

  /* ---------- polinomios en una variable (coeficientes racionales) ---------- */
  function upoly(e, v) {
    const c = [];
    for (const t of termsOf(expand(e))) {
      const [q, r] = split(t); let k = 0;
      if (r) {
        if (r.t === "sym" && r.s === v) k = 1;
        else if (r.t === "pow" && r.b.t === "sym" && r.b.s === v && isNum(r.e) && qint(r.e.q) && r.e.q.n > 0n) k = Number(r.e.q.n);
        else return null;
      }
      c[k] = qadd(c[k] || ZERO, q);
    }
    for (let i = 0; i < c.length; i++) c[i] = c[i] || ZERO;
    return utrim(c.length ? c : [ZERO]);
  }
  const utrim = c => { c = c.slice(); while (c.length > 1 && c[c.length - 1].n === 0n) c.pop(); return c; };
  const uev = (c, x) => { let s = ZERO; for (let i = c.length - 1; i >= 0; i--) s = qadd(qmul(s, x), c[i]); return s; };
  function udivlin(c, r) { const n = c.length - 1, b = new Array(n); let acc = ZERO; for (let i = n; i >= 1; i--) { acc = qadd(qmul(acc, r), c[i]); b[i - 1] = acc; } return b; }
  function udivmod(a, b) {
    a = utrim(a); b = utrim(b); const db = b.length - 1, lc = b[db];
    if (a.length - 1 < db) return [[ZERO], a];
    const r = a.slice(), q = new Array(a.length - db).fill(ZERO);
    for (let k = a.length - 1 - db; k >= 0; k--) { const f = qdiv(r[k + db], lc); q[k] = f; for (let j = 0; j <= db; j++) r[k + j] = qsub(r[k + j], qmul(f, b[j])); }
    return [utrim(q), utrim(r.slice(0, Math.max(1, db)))];
  }
  function ugcd(a, b) {
    a = utrim(a); b = utrim(b);
    while (!(b.length === 1 && b[0].n === 0n)) { const [, r] = udivmod(a, b); a = b; b = r; }
    const lc = a[a.length - 1]; return lc.n === 0n ? [ONE] : a.map(x => qdiv(x, lc));
  }
  function fromU(c, v) {
    const ts = [];
    for (let k = c.length - 1; k >= 0; k--) if (c[k].n !== 0n) ts.push(withCoef(c[k], k === 0 ? null : k === 1 ? sym(v) : { t: "pow", b: sym(v), e: int(k) }));
    return ts.length ? Add(...ts) : int(0);
  }
  function divisors(n) { n = babs(n); if (n === 0n) return [1n]; const ds = []; for (let i = 1n; i * i <= n && i < 200000n; i++) if (n % i === 0n) { ds.push(i); if (i * i !== n) ds.push(n / i); } return ds; }
  function intCoefs(c) {
    let L = 1n; for (const q of c) L = L / bgcd(L, q.d) * q.d;
    const z = c.map(q => q.n * (L / q.d)); let g = 0n; for (const v of z) g = bgcd(g, v); if (g === 0n) g = 1n;
    return { z: z.map(v => v / g), content: Q(g, L) };
  }
  function ratRoots(c) {
    c = utrim(c); const out = []; if (c.length < 2) return out;
    let p = c, zero = false; while (p.length > 1 && p[0].n === 0n) { p = p.slice(1); zero = true; }
    if (zero) out.push(ZERO);
    if (p.length < 2) return out;
    const { z } = intCoefs(p);
    for (const a of divisors(z[0])) for (const b of divisors(z[z.length - 1])) for (const s of [1n, -1n]) {
      const r = Q(s * a, b); if (!out.some(x => qeq(x, r)) && uev(p, r).n === 0n) out.push(r);
    }
    return out.sort((x, y) => qsgn(qsub(x, y)));
  }
  function quartic2(p) {             // x⁴ + … = (x² + a x + b)(x² + c x + d) con enteros
    const { z } = intCoefs(p); if (z[4] !== 1n) return null;
    const [a0, a1, a2, a3] = z;
    for (const bb of divisors(a0)) for (const sg of [1n, -1n]) {
      const b = sg * bb; if (b === 0n || a0 % b !== 0n) continue; const d = a0 / b, m = a2 - b - d, disc = a3 * a3 - 4n * m;
      if (disc < 0n) continue; const r = iroot(disc, 2); if (r === null || (a3 + r) % 2n !== 0n) continue;
      const a = (a3 + r) / 2n, c = a3 - a; if (a * d + b * c === a1) return [[Q(b), Q(a), ONE], [Q(d), Q(c), ONE]];
    }
    return null;
  }
  function factorU(c, v) {
    c = utrim(c); if (c.length < 3) return null;
    const ic = intCoefs(c); let k = ic.content, p = ic.z.map(x => Q(x));
    if (p[p.length - 1].n < 0n) { p = p.map(qneg); k = qneg(k); }
    const facs = [];
    let m0 = 0; while (p.length > 1 && p[0].n === 0n) { p = p.slice(1); m0++; }
    if (m0) facs.push({ f: [ZERO, ONE], m: m0 });
    for (const r of ratRoots(p)) {
      let m = 0; while (p.length > 1 && uev(p, r).n === 0n) { p = udivlin(p, r); m++; }
      if (m) { facs.push({ f: [Q(-r.n), Q(r.d)], m }); k = qmul(k, qpow(Q(1n, r.d), m)); }
    }
    if (p.length === 5) { const two = quartic2(p); if (two) { facs.push({ f: two[0], m: 1 }, { f: two[1], m: 1 }); k = qmul(k, p[4]); p = [ONE]; } }
    if (p.length > 1) { const ic2 = intCoefs(p); k = qmul(k, ic2.content); facs.push({ f: ic2.z.map(x => Q(x)), m: 1 }); } else k = qmul(k, p[0]);
    if (facs.length === 1 && facs[0].m === 1) return null;
    const parts = facs.map(({ f, m }) => m > 1 ? Pow(fromU(f, v), int(m)) : fromU(f, v));
    if (qeq(k, ONE)) return Mul(...parts);
    if (qeq(k, Q(-1))) return Neg(Mul(...parts));
    return Mul(num(k), ...parts);
  }

  /* ---------- factorización general ---------- */
  function powParts(f) { return f.t === "pow" && isNum(f.e) ? [f.b, f.e.q] : [f, ONE]; }
  function commonFactor(sum) {
    const ts = termsOf(sum); if (ts.length < 2) return [int(1), sum];
    let gn = 0n, gd = 1n, first = true, mins = null;
    for (const t of ts) {
      const [q, r] = split(t); gn = bgcd(gn, q.n); gd = first ? q.d : gd / bgcd(gd, q.d) * q.d; first = false;
      const m = new Map(); for (const f of r ? factorsOf(r) : []) { const [b, e] = powParts(f); if (qint(e) && e.n > 0n) m.set(key(b), { b, e: e.n }); }
      if (!mins) mins = m; else for (const [k, o] of [...mins]) { const x = m.get(k); if (!x) mins.delete(k); else o.e = o.e < x.e ? o.e : x.e; }
    }
    let g = Q(gn || 1n, gd);
    const lead = ts[0]; if (split(lead)[0].n < 0n && ts.every(t => split(t)[0].n < 0n)) g = qneg(g);
    const G = cmul(num(g), ...[...mins.values()].map(o => cpow(o.b, num(Q(o.e)))));
    if (isOne(G)) return [G, sum];
    return [G, cadd(...ts.map(t => cmul(t, cpow(G, int(-1)))))];
  }
  function rootTerm(t, n) {         // raíz n-ésima exacta de un monomio, o null
    const [q, r] = split(t); n = BigInt(n);
    if (q.n < 0n && n % 2n === 0n) return null;
    const rn = iroot(babs(q.n), n), rd = iroot(q.d, n); if (rn === null || rd === null) return null;
    const fs = [num(Q(q.n < 0n ? -rn : rn, rd))];
    for (const f of r ? factorsOf(r) : []) { const [b, e] = powParts(f); const ex = qdiv(e, Q(n)); if (!qint(ex) || ex.n < 1n) return null; fs.push(cpow(b, num(ex))); }
    return cmul(...fs);
  }
  const sqrtTerm = t => rootTerm(t, 2);
  function patternFactor(sum) {
    const ts = termsOf(sum);
    if (ts.length === 2) {
      const [p, n] = split(ts[0])[0].n > 0n ? [ts[0], ts[1]] : [ts[1], ts[0]];
      if (split(p)[0].n > 0n && split(n)[0].n < 0n) { const A = sqrtTerm(p), B = sqrtTerm(Neg(n)); if (A && B) return Mul(Add(A, B), Add(A, Neg(B))); }
      const A3 = rootTerm(ts[0], 3), B3 = rootTerm(ts[1], 3);
      if (A3 && B3) return Mul(Add(A3, B3), Add(cpow(A3, int(2)), Neg(cmul(A3, B3)), cpow(B3, int(2))));
    }
    if (ts.length === 3) {
      for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) {
        if (i === j) continue; const k = 3 - i - j;
        const A = sqrtTerm(ts[i]), B = sqrtTerm(ts[j]); if (!A || !B || split(ts[i])[0].n < 0n || split(ts[j])[0].n < 0n) continue;
        const two = cmul(int(2), A, B);
        const mid = key(cmul(ts[k]));
        if (mid === key(two)) return Pow(Add(A, B), int(2));
        if (mid === key(cmul(int(-1), two))) return Pow(Add(A, Neg(B)), int(2));
      }
    }
    return null;
  }
  function factor(e) {
    const x = expand(e); if (x.t !== "add") return x;
    const [g, rest] = commonFactor(x);
    const vs = symbols(rest); let core = null;
    if (vs.length === 1) { const c = upoly(rest, vs[0]); if (c) core = factorU(c, vs[0]); }
    if (!core) core = patternFactor(rest);
    core = core ? order(core) : order(rest);
    if (isOne(g)) return core;
    if (isNum(g) && qeq(g.q, Q(-1))) return Neg(core);
    return Mul(g, core);
  }

  /* ---------- fracciones ---------- */
  function nd(e) {                  // numerador y denominador (crudos)
    if (isNum(e)) return [num(Q(e.q.n)), num(Q(e.q.d))];
    if (e.t === "pow" && isNum(e.e) && e.e.q.n < 0n) return [int(1), qeq(e.e.q, Q(-1)) ? e.b : Pow(e.b, num(qneg(e.e.q)))];
    if (e.t === "mul") {
      const N = [], D = [];
      for (const f of e.a) { const [a, b] = nd(f); if (!isOne(a)) N.push(a); if (!isOne(b)) D.push(b); }
      return [N.length ? Mul(...N) : int(1), D.length ? Mul(...D) : int(1)];
    }
    return [e, int(1)];
  }
  function cancel(e) {               // simplificar una fracción N/D; devuelve null si no cambia nada
    const [N, D] = nd(e); if (isOne(D)) return null;
    const vs = symbols(Add(N, D)); if (vs.length > 1) return null;
    const v = vs[0] || "x", a = upoly(N, v), b = upoly(D, v); if (!a || !b) return null;
    const g = ugcd(a, b); let n2 = a, d2 = b;
    if (g.length > 1) { n2 = udivmod(a, g)[0]; d2 = udivmod(b, g)[0]; }
    const ca = intCoefs(n2).content, cb = intCoefs(d2).content;
    let k = Q(bgcd(ca.n, cb.n) || 1n, ca.d / bgcd(ca.d, cb.d) * cb.d);
    if (d2[d2.length - 1].n < 0n) k = qneg(k);
    n2 = n2.map(x => qdiv(x, k)); d2 = d2.map(x => qdiv(x, k));
    const Ne = fromU(n2, v), De = fromU(d2, v), res = isOne(De) ? Ne : Div(Ne, De);
    return str(res) === str(e) ? null : res;
  }

  /* ---------- herramientas para resolver ---------- */
  function coeffs(e, x) {             // coeficientes (expresiones) de un polinomio en x; null si x no aparece como polinomio
    const out = [];
    for (const t of termsOf(expand(e))) {
      let k = 0; const rest = [];
      for (const f of factorsOf(t)) {
        if (f.t === "sym" && f.s === x) k += 1;
        else if (f.t === "pow" && f.b.t === "sym" && f.b.s === x && isNum(f.e) && qint(f.e.q) && f.e.q.n > 0n) k += Number(f.e.q.n);
        else { if (symbols(f).includes(x)) return null; rest.push(f); }
      }
      out[k] = cadd(out[k] || int(0), cmul(...rest));
    }
    for (let i = 0; i < out.length; i++) out[i] = out[i] || int(0);
    while (out.length > 1 && isZero(out[out.length - 1])) out.pop();
    return out.length ? out : [int(0)];
  }
  function ndC(t) {                   // término canónico → [numerador, denominador] canónicos
    const [q, r] = split(t), N = [num(Q(q.n))], D = [num(Q(q.d))];
    for (const f of r ? factorsOf(r) : []) { const [b, ex] = powParts(f); if (ex.n < 0n) D.push(cpow(b, num(qneg(ex)))); else N.push(f); }
    return [cmul(...N), cmul(...D)];
  }
  function monoGcd(A, B) {
    const [qa, ra] = split(A), [qb, rb] = split(B), m = new Map(), out = [];
    for (const f of ra ? factorsOf(ra) : []) { const [b, e] = powParts(f); m.set(key(b), { b, e }); }
    for (const f of rb ? factorsOf(rb) : []) { const [b, e] = powParts(f), o = m.get(key(b)); if (o && o.e.n > 0n && e.n > 0n) out.push(cpow(b, num(qnum(o.e) < qnum(e) ? o.e : e))); }
    return cmul(num(Q(bgcd(qa.n, qb.n) || 1n, 1n)), ...out);
  }
  function together(e, keep) {        // una sola fracción con denominador común (keep: sin simplificar factores comunes)
    e = expand(simplify(e));
    const parts = termsOf(e).map(ndC); let L = 1n; const dm = new Map();
    for (const [, D] of parts) for (const f of factorsOf(D)) {
      if (isNum(f)) { const n = babs(f.q.n); L = L / bgcd(L, n) * n; continue; }
      const [b, ex] = powParts(f), k = key(b), o = dm.get(k); if (!o || qnum(ex) > qnum(o.e)) dm.set(k, { b, e: ex });
    }
    const Dc = cmul(num(Q(L)), ...[...dm.values()].map(o => cpow(o.b, num(o.e))));
    if (isOne(Dc)) return e;
    let N = expand(cadd(...parts.map(([n, d]) => cmul(n, Dc, cpow(d, int(-1)))))), D = Dc;
    const G = keep ? int(1) : monoGcd(N.t === "add" ? commonFactor(N)[0] : N, D);
    if (!isOne(G)) { N = expand(cmul(N, cpow(G, int(-1)))); D = cmul(D, cpow(G, int(-1))); }
    if (split(D)[0].n < 0n) { N = expand(cmul(int(-1), N)); D = cmul(int(-1), D); }
    if (isOne(D)) return N;
    const r = Div(order(N), order(D)), c = keep ? null : cancel(r);
    return c || r;
  }
  function radsimp(e) {               // √(k²·m) = k·√m y √(p/q) = √(pq)/q
    switch (e.t) {
      case "add": return cadd(...e.a.map(radsimp));
      case "mul": return cmul(...e.a.map(radsimp));
      case "fn": return cfn(e.f, radsimp(e.x));
      case "pow": {
        const b = radsimp(e.b), ex = e.e;
        if (isNum(b) && b.q.n > 0n && isNum(ex) && qeq(ex.q, Q(1, 2))) {
          let n = b.q.n * b.q.d, k = 1n; for (let p = 2n; p * p <= n && p < 100000n; p++) while (n % (p * p) === 0n) { n /= p * p; k *= p; }
          const c = Q(k, b.q.d); return n === 1n ? num(c) : cmul(num(c), { t: "pow", b: num(Q(n)), e: ex });
        }
        return cpow(b, radsimp(ex));
      }
      default: return e;
    }
  }
  const approx = v => ({ t: "num", q: qFromNumber(+v.toPrecision(12)), ap: true });

  /* ---------- orden de presentación ---------- */
  function monoDeg(t) {               // [grado total, vector por letras]
    const m = {}; let tot = 0;
    for (const f of factorsOf(split(t)[1] || int(1))) { const [b, e] = powParts(f); if (b.t === "sym" && b.s !== "π" && b.s !== "e") { const x = qnum(e); m[b.s] = (m[b.s] || 0) + x; tot += x; } else if (!isNum(b)) tot += .5; }
    return [tot, m];
  }
  function cmpTerms(a, b) {
    const [da, ma] = monoDeg(a), [db, mb] = monoDeg(b);
    if (da !== db) return db - da;
    for (const v of [...new Set([...Object.keys(ma), ...Object.keys(mb)])].sort((p, q) => p === "x" ? -1 : q === "x" ? 1 : p < q ? -1 : 1)) { const x = (ma[v] || 0) - (mb[v] || 0); if (x) return -x; }
    return 0;
  }
  const rank = f => isNum(f) ? 0 : f.t === "pow" && isNum(f.b) ? 1 : f.t === "sym" || (f.t === "pow" && f.b.t === "sym" && isNum(f.e)) ? 2 : f.t === "fn" || f.t === "pow" ? 3 : 4;
  const baseName = f => f.t === "sym" ? f.s : f.t === "pow" && f.b.t === "sym" ? f.b.s : key(f);
  function order(e) {
    switch (e.t) {
      case "add": {
        const ts = e.a.map(order).sort(cmpTerms);
        // con el mismo grado, empezar por un término positivo: b² − 4ac mejor que −4ac + b²
        if (isNegT(ts[0])) { const d0 = monoDeg(ts[0])[0], j = ts.findIndex(t => !isNegT(t) && monoDeg(t)[0] === d0); if (j > 0) ts.unshift(ts.splice(j, 1)[0]); }
        return Add(...ts);
      }
      case "mul": return Mul(...e.a.map(order).sort((x, y) => rank(x) - rank(y) || (baseName(x) < baseName(y) ? -1 : baseName(x) > baseName(y) ? 1 : 0)));
      case "pow": return Pow(order(e.b), order(e.e));
      case "fn": return Fn(e.f, order(e.x));
      default: return e;
    }
  }
  const nice = e => order(simplify(e));

  /* ---------- escritura ---------- */
  const SUPD = "⁰¹²³⁴⁵⁶⁷⁸⁹", sup = n => (n < 0 ? "⁻" : "") + String(Math.abs(n)).split("").map(d => SUPD[+d]).join("");
  const MN = "−", qs = q => (q.n < 0n ? MN : "") + (q.d === 1n ? String(babs(q.n)) : babs(q.n) + "/" + q.d);
  const isNegT = t => isNum(t) ? t.q.n < 0n : t.t === "mul" && isNum(t.a[0]) && t.a[0].q.n < 0n;
  const atomic = e => e.t === "sym" || (isNum(e) && qint(e.q) && e.q.n >= 0n);
  const FNAME = { sin: "sen", asin: "arcsen", acos: "arccos", atan: "arctan" };
  function str(e, p = 0) {          // p: 0 arriba, 1 sumando, 2 factor, 3 base de potencia
    switch (e.t) {
      case "num": { const s = e.ap ? (e.q.n < 0n ? MN : "") + String(+Math.abs(qnum(e.q)).toPrecision(6)) : qs(e.q); return (p >= 2 && (e.q.n < 0n || (e.q.d !== 1n && !e.ap))) ? "(" + s + ")" : s; }
      case "sym": return e.s;
      case "add": { let o = ""; e.a.forEach((t, i) => { const ng = isNegT(t), u = ng ? Neg(t) : t, b = str(u, ng && u.t === "add" ? 2 : 1); o += i ? (ng ? " − " : " + ") + b : (ng ? MN : "") + b; }); return p >= 2 ? "(" + o + ")" : o; }
      case "mul": return mulStr(e, p);
      case "pow": return powStr(e, p);
      case "fn": {
        const x = str(e.x); if (e.f === "abs") return "|" + x + "|";
        if (e.f === "deriv") return "d/dx(" + x + ")";
        if (e.f === "integ") return "∫ " + (e.x.t === "add" ? "(" + x + ")" : x) + " dx";
        return (FNAME[e.f] || e.f) + "(" + x + ")";
      }
    }
  }
  function mulStr(e, p) {
    let fs = e.a.slice(), neg = false;
    if (isNum(fs[0]) && fs[0].q.n < 0n && fs.length > 1) { neg = true; fs[0] = num(qneg(fs[0].q)); if (isOne(fs[0])) fs = fs.slice(1); }
    const N = [], D = [];
    fs.forEach((f, i) => {
      if (isNum(f) && f.q.d !== 1n && i === 0 && fs.length > 1) { if (f.q.n !== 1n) N.push(num(Q(f.q.n))); D.push(num(Q(f.q.d))); return; }
      if (f.t === "pow" && isNum(f.e) && f.e.q.n < 0n) { D.push(qeq(f.e.q, Q(-1)) ? f.b : Pow(f.b, num(qneg(f.e.q)))); return; }
      N.push(f);
    });
    const join = list => { let o = ""; list.forEach((f, i) => { const s = str(f, 2); if (i) { const prev = list[i - 1]; const dot = /^[0-9−(]/.test(s) && !(s[0] === "(" && !isNum(f)) || (prev.t === "pow" && isNum(prev.b)) || /^[0-9]/.test(s) || (baseName(prev) === baseName(f) && !isNum(f)) || /^d\/dx|^∫/.test(s) || (prev.t === "fn" && /^(deriv|integ)$/.test(prev.f)) || (prev.t === "pow" && !isNum(prev.e) && /^[a-zα-ω]/i.test(s)); o += dot ? "·" + s : s; } else o = s; }); return o; };
    let s = N.length ? join(N) : "1";
    if (N.length === 1 && isOne(N[0]) && D.length) s = "1";
    if (D.length) s += "/" + (D.length === 1 ? (D[0].t === "add" || D[0].t === "mul" ? "(" + str(D[0]) + ")" : str(D[0], 2)) : "(" + join(D) + ")");
    if (neg) s = MN + s;
    return p >= 3 || (neg && p >= 2) ? "(" + s + ")" : s;
  }
  function powStr(e, p) {
    const ex = e.e; let s;
    if (isNum(ex) && ex.q.n < 0n) { const inv = qeq(ex.q, Q(-1)) ? e.b : Pow(e.b, num(qneg(ex.q))); s = "1/" + str(inv, 3); return p >= 2 ? "(" + s + ")" : s; }
    if (isNum(ex) && (qeq(ex.q, Q(1, 2)) || qeq(ex.q, Q(1, 3)))) { const r = qeq(ex.q, Q(1, 2)) ? "√" : "∛"; s = atomic(e.b) ? r + str(e.b, 3) : r + "(" + str(e.b) + ")"; return p >= 3 ? "(" + s + ")" : s; }
    const base = e.b.t === "fn" ? str(e.b) : str(e.b, 3);
    if (isNum(ex) && qint(ex.q)) s = base + sup(Number(ex.q.n));
    else s = base + "^" + (atomic(ex) ? str(ex) : "(" + str(ex) + ")");
    return p >= 3 ? "(" + s + ")" : s;
  }
  function tex(e, p = 0) {
    const qt = q => { const a = babs(q.n), s = q.n < 0n ? "-" : ""; return q.d === 1n ? s + a : `${s}\\frac{${a}}{${q.d}}`; };
    switch (e.t) {
      case "num": { const s = qt(e.q); return p >= 2 && e.q.n < 0n ? `\\left(${s}\\right)` : s; }
      case "sym": return e.s === "π" ? "\\pi" : e.s;
      case "add": { let o = ""; e.a.forEach((t, i) => { const ng = isNegT(t), u = ng ? Neg(t) : t, b = tex(u, ng && u.t === "add" ? 2 : 1); o += i ? (ng ? " - " : " + ") + b : (ng ? "-" : "") + b; }); return p >= 2 ? `\\left(${o}\\right)` : o; }
      case "mul": {
        const [N, D] = nd(e); if (!isOne(D)) { const s = `\\frac{${tex(N)}}{${tex(D)}}`; return s; }
        let fs = e.a.slice(), neg = false; if (isNum(fs[0]) && fs[0].q.n < 0n) { neg = true; fs[0] = num(qneg(fs[0].q)); if (isOne(fs[0]) && fs.length > 1) fs = fs.slice(1); }
        const s = fs.map((f, i) => (i && isNum(f) ? " \\cdot " : i ? " " : "") + tex(f, 2)).join("");
        return (neg ? "-" : "") + (p >= 3 ? `\\left(${s}\\right)` : s);
      }
      case "pow": {
        const ex = e.e;
        if (isNum(ex) && ex.q.n < 0n) return `\\frac{1}{${tex(qeq(ex.q, Q(-1)) ? e.b : Pow(e.b, num(qneg(ex.q))))}}`;
        if (isNum(ex) && qeq(ex.q, Q(1, 2))) return `\\sqrt{${tex(e.b)}}`;
        if (isNum(ex) && qeq(ex.q, Q(1, 3))) return `\\sqrt[3]{${tex(e.b)}}`;
        return `{${tex(e.b, 3)}}^{${tex(ex)}}`;
      }
      case "fn": return e.f === "deriv" ? `\\frac{d}{dx}\\left(${tex(e.x)}\\right)` : e.f === "integ" ? `\\int ${tex(e.x, 3)}\\,dx` : e.f === "abs" ? `\\left|${tex(e.x)}\\right|` : `\\${({ asin: "arcsin", acos: "arccos", atan: "arctan" })[e.f] || e.f}\\left(${tex(e.x)}\\right)`;
    }
  }

  /* ---------- lector (conserva la forma escrita) ---------- */
  const FNS = ["sqrt", "cbrt", "abs", "sin", "cos", "tan", "exp", "ln", "log", "asin", "acos", "atan", "deriv", "integ"];
  const ALIAS = { raiz: "sqrt", sen: "sin", tg: "tan", arcsen: "asin", arcsin: "asin", arccos: "acos", arctg: "atan", arctan: "atan" };
  const NAMES = [...FNS, ...Object.keys(ALIAS)].sort((a, b) => b.length - a.length);
  function tokenize(s) {
    const out = []; let i = 0;
    while (i < s.length) {
      const c = s[i];
      if (/[0-9.]/.test(c)) { const m = s.slice(i).match(/^(\d+\.?\d*|\.\d+)/); if (!m) throw Error("Número mal escrito"); out.push({ k: "num", v: qFromDec(m[0]) }); i += m[0].length; continue; }
      if (/[a-zA-Z]/.test(c)) {
        let w = s.slice(i).match(/^[a-zA-Z]+/)[0]; i += w.length;
        while (w) {
          const f = NAMES.find(f => w.startsWith(f));
          if (f) { out.push({ k: "fn", v: ALIAS[f] || f }); w = w.slice(f.length); continue; }
          if (w.startsWith("pi")) { out.push({ k: "sym", v: "π" }); w = w.slice(2); continue; }
          out.push({ k: "sym", v: w[0] }); w = w.slice(1);
        }
        continue;
      }
      if (c === "π") { out.push({ k: "sym", v: "π" }); i++; continue; }
      if (c === "√") { out.push({ k: "fn", v: "sqrt" }); i++; continue; }
      if (c === "∛") { out.push({ k: "fn", v: "cbrt" }); i++; continue; }
      if ("+-*/^()|".includes(c)) { out.push({ k: c }); i++; continue; }
      throw Error("Símbolo inesperado «" + c + "»");
    }
    return out;
  }
  function parse(src) {             // src ya normalizado (sin espacios)
    const tk = tokenize(src); let i = 0, absD = 0; const pk = () => tk[i];
    const starts = t => t && (t.k === "num" || t.k === "sym" || t.k === "fn" || t.k === "(" || (t.k === "|" && absD === 0));
    const expr = () => { let r = term(); while (pk() && (pk().k === "+" || pk().k === "-")) { const o = tk[i++].k, t = term(); r = o === "+" ? Add(r, t) : Add(r, Neg(t)); } return r; };
    const term = () => {
      let r = unary();
      for (;;) {
        const t = pk();
        if (t && t.k === "*") { i++; r = Mul(r, unary()); }
        else if (t && t.k === "/") { i++; r = Mul(r, Pow(unary(), int(-1))); }
        else if (starts(t)) r = Mul(r, power());
        else break;
      }
      return r;
    };
    const unary = () => { const t = pk(); if (t && t.k === "-") { i++; return Neg(unary()); } if (t && t.k === "+") { i++; return unary(); } return power(); };
    const power = () => { const b = atom(); if (pk() && pk().k === "^") { i++; return Pow(b, unaryPow()); } return b; };
    const unaryPow = () => { const t = pk(); if (t && t.k === "-") { i++; return Neg(unaryPow()); } return power(); };
    const atom = () => {
      const t = tk[i++]; if (!t) throw Error("Expresión incompleta");
      if (t.k === "num") return num(t.v);
      if (t.k === "sym") return sym(t.v);
      if (t.k === "(") { const r = expr(); if (!pk() || pk().k !== ")") throw Error("Falta un paréntesis «)»"); i++; return r; }
      if (t.k === "|") { absD++; const r = expr(); if (!pk() || pk().k !== "|") throw Error("Falta la barra de cierre «|»"); i++; absD--; return Fn("abs", r); }
      if (t.k === "fn") {
        const arg = pk() && pk().k === "(" ? atom() : power();
        return t.v === "sqrt" ? Sqrt(arg) : t.v === "cbrt" ? Pow(arg, frac(1, 3)) : t.v === "exp" ? Pow(sym("e"), arg) : Fn(t.v, arg);
      }
      throw Error("Símbolo inesperado «" + t.k + "»");
    };
    const r = expr(); if (i < tk.length) throw Error("Símbolo inesperado"); return r;
  }

  return {
    Q, ZERO, ONE, qadd, qsub, qmul, qdiv, qneg, qeq, qnum, qint, qsgn, qpow, qFromNumber, iroot,
    num, int, frac, sym, isNum, isZero, isOne, Add, Mul, Pow, Fn, Neg, Sub, Div, Sqrt,
    key, termsOf, factorsOf, split, withCoef, cadd, cmul, cpow, cfn, simplify, expand, nice, order,
    symbols, evalN, subs, upoly, fromU, ugcd, udivmod, ratRoots, factorU, factor, commonFactor, rootTerm, sqrtTerm, patternFactor, nd, cancel,
    str, tex, parse, coeffs, together, radsimp, approx, monoGcd, powParts,
  };
})();
