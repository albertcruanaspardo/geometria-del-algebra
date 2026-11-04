/* Geometría del Álgebra — resolutor paso a paso (fase 3).
   Para cada ecuación decide el paso siguiente (trasponer, dividir, completar el cuadrado, extraer la raíz,
   factorizar, quitar denominadores, elevar al cuadrado, separar casos, tomar logaritmos, arcoseno,
   eliminación de Gauss, sustitución…) y adjunta la figura que lo justifica.
   Funciona con letras (parámetros): ax² + bx + c = 0 da la fórmula general deducida con el gnomon. */
"use strict";
const RESOLVER = (() => {
  const { Q, num, int, frac, sym, isNum, isZero, isOne, Add, Mul, Pow, Fn, Neg, Sub, Div, Sqrt, key, cadd, cmul, cpow, cfn,
    simplify, expand, factor, order, str, evalN, symbols, subs, coeffs, together, radsimp, approx, nd, termsOf, factorsOf, rootTerm, qnum, qeq, qFromNumber } = CAS;
  const { ph, lerp, rect, txt, seg, PAL, scene, noFig, f2, bad, figComplete, figMean, figCube } = REGLAS.G;
  // forma más corta entre «una sola fracción» y «suma desarrollada»: (−b + √Δ)/(2a) pero kπ + π/12
  const clean = e => { const a = order(radsimp(together(e))), b = order(radsimp(expand(e))); return str(b).length < str(a).length ? b : a; };
  const has = (e, x) => symbols(e).includes(x);
  const S = e => str(e);
  const E = (lhs, rhs, rel = "=") => ({ lhs, rhs, rel });
  const flip = r => ({ "<": ">", ">": "<", "<=": ">=", ">=": "<=", "=": "=" })[r];
  const isConst = e => !symbols(e).length;
  const isSolved = (e, x) => e.rel === "=" && e.lhs.t === "sym" && e.lhs.s === x && !has(e.rhs, x);
  const contains = (n, pred) => pred(n) || (n.a && n.a.some(c => contains(c, pred))) || (n.b && contains(n.b, pred)) || (n.e && typeof n.e === "object" && n.e.t && contains(n.e, pred)) || (n.x && contains(n.x, pred));
  const neg0 = e => isConst(e) && evalN(e) < 0;

  /* ---------- construcción de polinomios para mostrar ---------- */
  const xpow = (x, k) => k === 0 ? null : k === 1 ? sym(x) : Pow(sym(x), int(k));
  function term(c, x, k) {
    c = clean(c); const m = xpow(x, k); if (!m) return c;
    if (isOne(c)) return m; if (isNum(c) && qeq(c.q, Q(-1))) return Neg(m);
    if (isNum(c) || c.t === "sym" || (c.t === "mul" && !c.a.some(f => f.t === "add"))) return order(cmul(c, m));
    return Mul(c, m);
  }
  function polyE(cs, x) { const ts = []; for (let k = cs.length - 1; k >= 0; k--) if (!isZero(clean(cs[k]))) ts.push(term(cs[k], x, k)); return ts.length ? Add(...ts) : int(0); }
  function sqrtE(R) {
    if (isConst(R)) return clean(Pow(R, frac(1, 2)));
    const [N, D] = nd(R), sN = rootTerm(simplify(N), 2);
    const top = sN || Sqrt(order(simplify(N)));
    if (isOne(D)) return top;
    const sD = rootTerm(simplify(D), 2);
    return sD ? Div(top, order(sD)) : Sqrt(R);
  }

  /* ---------- raíces numéricas ---------- */
  function numRoots(F, x, env, lo = -50, hi = 50, n = 4000) {
    const f = v => { const y = evalN(F, { ...env, [x]: v }); return isFinite(y) ? y : NaN; };
    const out = []; let pv = lo, pf = f(lo);
    for (let i = 1; i <= n; i++) {
      const v = lo + (hi - lo) * i / n, fv = f(v);
      if (pf === 0) out.push(pv);
      if (isFinite(pf) && isFinite(fv) && pf * fv < 0) {
        let a = pv, b = v, fa = pf; for (let k = 0; k < 70; k++) { const m = (a + b) / 2, fm = f(m); if (!isFinite(fm)) break; if (fa * fm <= 0) b = m; else { a = m; fa = fm; } }
        const r = (a + b) / 2; if (Math.abs(f(r)) < 1e-6 * (1 + Math.abs(pf) + Math.abs(fv))) out.push(r);
      }
      pv = v; pf = fv;
    }
    return out.filter((r, i) => !i || Math.abs(r - out[i - 1]) > 1e-7);
  }
  const intervalsText = (F, x, env, rel, fx = f2) => {
    const roots = numRoots(F, x, env), f = v => evalN(F, { ...env, [x]: v });
    const T = v => { const y = f(v); if (!isFinite(y)) return false; return rel === "<" ? y < -1e-12 : rel === ">" ? y > 1e-12 : rel === "<=" ? y <= 1e-12 : y >= -1e-12; };
    const pts = [-Infinity, ...roots, Infinity], out = [];
    for (let i = 0; i < pts.length - 1; i++) {
      const a = pts[i], b = pts[i + 1], m = a === -Infinity ? (b === Infinity ? 0 : b - 1) : b === Infinity ? a + 1 : (a + b) / 2;
      if (!T(m)) continue;
      if (out.length && out[out.length - 1].b === a && T(a)) out[out.length - 1].b = b; else out.push({ a, b });
    }
    roots.forEach(r => { if (T(r) && !out.some(I => I.a <= r && r <= I.b)) out.push({ a: r, b: r }); });
    out.forEach(I => { I.ca = isFinite(I.a) && T(I.a); I.cb = isFinite(I.b) && T(I.b); });
    out.sort((p, q) => p.a - q.a);
    const txtI = !out.length ? "∅ (ninguna)" : out.length === 1 && out[0].a === -Infinity && out[0].b === Infinity ? "ℝ (todos los números)"
      : out.map(I => I.a === I.b ? `{${fx(I.a)}}` : `${I.ca ? "[" : "("}${I.a === -Infinity ? "−∞" : fx(I.a)}, ${I.b === Infinity ? "+∞" : fx(I.b)}${I.cb ? "]" : ")"}`).join(" ∪ ");
    return { roots, out, txt: txtI };
  };

  /* ---------- un paso sobre una ecuación de una incógnita ---------- */
  function stepOne(e, x, env, ctx) {
    const L = e.lhs, R = e.rhs;
    if (!has(L, x) && !has(R, x)) {
      const l = evalN(L, env), r = evalN(R, env), ok = isFinite(l) && isFinite(r) && Math.abs(l - r) < 1e-9 * (1 + Math.abs(l));
      return { repl: [], desc: ok ? `Desaparece la ${x} y queda una igualdad cierta: vale cualquier ${x}` : `Desaparece la ${x} y queda una igualdad falsa: esta rama no da soluciones`, fig: null, ident: ok };
    }
    if (has(R, x) && !has(L, x)) return { repl: [E(R, L, flip(e.rel))], desc: "Intercambiar los miembros", fig: null };
    // producto (o potencia) igual a cero
    if (e.rel === "=" && isZero(clean(R)) && (L.t === "mul" || (L.t === "pow" && isNum(L.e) && qnum(L.e.q) > 0 && has(L.b, x)))) {
      const fs = (L.t === "mul" ? L.a : [L]).filter(f => has(f, x)).map(f => f.t === "pow" && isNum(f.e) && qnum(f.e.q) > 0 ? f.b : f);
      const uniq = fs.filter((f, i) => fs.findIndex(g => key(simplify(g)) === key(simplify(f))) === i);
      if (uniq.length >= 2 || L.t === "pow" || fs.length < L.a?.length) return { repl: uniq.map(f => E(f, int(0))), desc: L.t === "pow" ? "Un cuadrado de área cero tiene lado cero: la base vale 0" : "Producto nulo: si un rectángulo tiene área cero, uno de sus lados es cero", fig: { id: "op-zero", bind: { fs: uniq, x } } };
    }
    const F = Sub(L, R), cs = coeffs(F, x);
    if (cs) return polyStep(e, x, cs, env, ctx);
    // aislar la parte con x: k·g(x) = c  o  g(x) + m = c
    if (!has(R, x) && L.t === "add") {
      const xt = L.a.filter(t => has(t, x)), ot = L.a.filter(t => !has(t, x));
      if (xt.length === 1 && ot.length) return { repl: [E(xt[0], clean(Sub(R, Add(...ot))), e.rel)], desc: `Aislar el término con ${x}: pasar ${S(Add(...ot))} al otro miembro`, fig: { id: "op-add", bind: { L, R, d: clean(Neg(Add(...ot))), x } } };
    }
    if (!has(R, x) && L.t === "mul") {
      const xf = L.a.filter(f => has(f, x)), kf = L.a.filter(f => !has(f, x));
      if (xf.length === 1 && kf.length) { const k = clean(Mul(...kf)), rel = neg0(k) ? flip(e.rel) : e.rel; return { repl: [E(xf[0], clean(Div(R, k)), rel)], desc: `Dividir ambos miembros por ${S(k)}`, fig: { id: "op-div", bind: { A: k, c: R, x } } }; }
    }
    // valor absoluto
    const absN = n => n.t === "fn" && n.f === "abs" && has(n.x, x);
    if (absN(L) && !contains(R, absN)) { ctx.check = true; return { repl: [E(L.x, R), E(L.x, clean(Neg(R)))], desc: "|A| = B ⇔ A = B o A = −B (la distancia es la misma a ambos lados)", fig: { id: "op-abs", bind: { A: L.x, R, x } } }; }
    if (absN(L) && absN(R)) return { repl: [E(L.x, R.x), E(L.x, clean(Neg(R.x)))], desc: "|A| = |B| ⇔ A = B o A = −B", fig: { id: "op-abs", bind: { A: L.x, R: R.x, x } } };
    // raíces cuadradas
    const radN = n => n.t === "pow" && isNum(n.e) && qeq(n.e.q, Q(1, 2)) && has(n.b, x);
    if (contains(F, radN)) {
      const isoL = radN(L) || (L.t === "mul" && L.a.filter(radN).length === 1 && L.a.every(f => radN(f) || isConst(f)));
      if (isoL && !contains(R, radN)) { ctx.check = true; return { repl: [E(order(expand(Pow(L, int(2)))), order(expand(Pow(R, int(2)))))], desc: "Elevar al cuadrado ambos miembros (¡puede añadir soluciones ajenas!)", fig: { id: "op-square", bind: { L, R, x } } }; }
      const ts = [...termsOf(L).map(t => ({ t, s: 1 })), ...termsOf(R).map(t => ({ t, s: -1 }))], rad = ts.filter(o => contains(o.t, radN));
      if (rad.length >= 1) {
        const keep = rad[0], rest = ts.filter(o => o !== keep).map(o => cmul(int(-keep.s * o.s), o.t));
        const nl = keep.s > 0 ? keep.t : clean(Neg(keep.t)), nr = clean(cadd(...rest, int(0)));
        if (key(nl) !== key(L) || key(nr) !== key(R)) return { repl: [E(nl, nr)], desc: "Aislar la raíz en un miembro", fig: { id: "op-add", bind: { L, R, d: clean(Sub(nl, L)), x } } };
      }
    }
    // x en un denominador
    const denX = n => n.t === "pow" && isNum(n.e) && n.e.q.n < 0n && has(n.b, x);
    if (contains(F, denX) && e.rel === "=") {
      ctx.check = true;
      const [a, b] = nd(L), [c, d] = nd(R);
      if (!(isOne(b) && isOne(d)) && !contains(a, denX) && !contains(c, denX)) { ctx.excl.push(b, d); return { repl: [E(order(expand(cmul(a, d))), order(expand(cmul(c, b))))], desc: "Multiplicar en cruz: producto de extremos = producto de medios (Euclides VI.16)", fig: { id: "crossmul", bind: { a, b, c, d } } }; }
      const T = together(F, true), [N, D] = nd(T); ctx.excl.push(D);
      return { repl: [E(order(expand(N)), int(0))], desc: `Quitar denominadores: multiplicar por ${S(D)} (con ${S(D)} ≠ 0)`, fig: { id: "op-mul", bind: { L, R, k: D, x } } };
    }
    // exponenciales
    const expN = n => n.t === "pow" && !has(n.b, x) && has(n.e, x);
    if (expN(L) && expN(R) && key(simplify(L.b)) === key(simplify(R.b))) return { repl: [E(L.e, R.e)], desc: "Misma base: se igualan los exponentes", fig: { id: "op-log", bind: { base: L.b, R } } };
    if (expN(L) && !has(R, x)) {
      const rv = evalN(R, env), bv = evalN(L.b, env);
      if (!(rv > 0)) return { repl: [], desc: `Una potencia de base positiva nunca vale ${S(R)}: no hay solución`, fig: { id: "op-log", bind: { base: L.b, R } } };
      const k = Math.log(rv) / Math.log(bv), kq = num(qFromNumber(+k.toFixed(9)));
      if (isConst(R) && Math.abs(k - Math.round(k * 12) / 12) < 1e-9 && key(clean(Pow(L.b, kq))) === key(clean(R))) return { repl: [E(L.e, kq)], desc: `${S(R)} = ${S(L.b)}^${S(kq)}: se igualan los exponentes`, fig: { id: "op-log", bind: { base: L.b, R } } };
      const isE = L.b.t === "sym" && L.b.s === "e";
      return { repl: [E(L.e, isE ? Fn("ln", R) : Div(Fn("ln", R), Fn("ln", L.b)))], desc: "Tomar logaritmos en ambos miembros: el exponente es la posición en la escala logarítmica", fig: { id: "op-log", bind: { base: L.b, R } } };
    }
    // logaritmos
    const lnN = n => n.t === "fn" && (n.f === "ln" || n.f === "log") && has(n.x, x);
    if (L.t === "add" && L.a.every(lnN) && L.a.every(t => t.f === L.a[0].f)) return { repl: [E(Fn(L.a[0].f, Mul(...L.a.map(t => t.x))), R)], desc: "La suma de logaritmos es el logaritmo del producto", fig: { id: "op-log", bind: { base: sym("e"), R } } };
    if (lnN(L) && !has(R, x)) { ctx.check = true; const B = L.f === "ln" ? sym("e") : int(10); return { repl: [E(L.x, clean(Pow(B, R)))], desc: `Deshacer el logaritmo: el argumento es ${S(B)} elevado a ${S(R)}`, fig: { id: "op-log", bind: { base: B, R: Pow(B, R) } } }; }
    // trigonométricas
    const trigN = n => n.t === "fn" && ["sin", "cos", "tan"].includes(n.f) && has(n.x, x);
    if (trigN(L) && !has(R, x)) {
      const c = clean(R), cv = evalN(c, env), A = L.x, K = sym("k"), pi = sym("π"), twoK = cmul(int(2), K, pi);
      if (L.f !== "tan" && Math.abs(cv) > 1 + 1e-12) return { repl: [], desc: `El ${L.f === "sin" ? "seno" : "coseno"} es un segmento dentro de la circunferencia unidad: nunca vale ${S(c)}`, fig: { id: "op-trig", bind: { f: L.f, c } } };
      let repl;
      if (L.f === "sin") { const s0 = cfn("asin", c), s1 = clean(Sub(pi, s0)); repl = key(s0) === key(s1) ? [E(A, Add(s0, twoK))] : [E(A, Add(s0, twoK)), E(A, Add(s1, twoK))]; }
      else if (L.f === "cos") { const s0 = cfn("acos", c), s1 = clean(Neg(s0)); repl = key(s0) === key(s1) ? [E(A, Add(s0, twoK))] : [E(A, Add(s0, twoK)), E(A, Add(s1, twoK))]; }
      else repl = [E(A, Add(cfn("atan", c), cmul(K, pi)))];
      ctx.periodic = true;
      return { repl: repl.map(r => E(r.lhs, order(simplify(r.rhs)))), desc: L.f === "tan" ? "El ángulo cuya tangente es c, más medias vueltas kπ" : `Los ángulos cuyo ${L.f === "sin" ? "seno (altura)" : "coseno (abscisa)"} es ${S(c)}: dos puntos de la circunferencia, más vueltas completas 2kπ`, fig: { id: "op-trig", bind: { f: L.f, c } } };
    }
    if (!isZero(clean(R)) && has(R, x)) return { repl: [E(order(expand(F)), int(0))], desc: "Pasar todo al primer miembro", fig: { id: "op-add", bind: { L, R, d: clean(Neg(R)), x } } };
    return null;
  }

  function polyStep(e, x, cs, env, ctx) {
    const d = cs.length - 1;
    if (d === 0) { const ok = isZero(clean(cs[0])); return { repl: [], ident: ok, desc: ok ? `Al reducir desaparece la ${x}: es una identidad, vale cualquier ${x}` : `Al reducir desaparece la ${x} y queda una igualdad falsa: no hay solución`, fig: null }; }
    if (d === 1) return linStep(e, x, cs);
    if (d === 2) return quadStep(e, x, cs, env);
    return highStep(e, x, cs, env);
  }
  function linStep(e, x, cs) {
    const a = clean(cs[1]), b = clean(cs[0]), lc = coeffs(e.lhs, x), rc = coeffs(e.rhs, x);
    const isAx = lc && rc && lc.length === 2 && isZero(clean(lc[0])) && rc.length === 1 && (e.lhs.t === "mul" || e.lhs.t === "sym" || (e.lhs.t === "num"));
    if (!isAx) { const nl = term(a, x, 1), nr = clean(Neg(b)); return { repl: [E(nl, nr, e.rel)], desc: `Trasponer: los términos con ${x} a un lado y los números al otro`, fig: { id: "op-add", bind: { L: e.lhs, R: e.rhs, d: clean(Sub(nl, e.lhs)), x } } }; }
    const A = clean(lc[1]); if (isOne(A)) return { repl: [E(sym(x), clean(e.rhs), e.rel)], desc: "Simplificar", fig: null };
    const rel = neg0(A) ? flip(e.rel) : e.rel;
    return { repl: [E(sym(x), clean(Div(e.rhs, A)), rel)], desc: `Dividir ambos miembros por ${S(A)}` + (isConst(A) ? "" : ` (suponiendo ${S(A)} ≠ 0)`) + (rel !== e.rel ? " — al dividir por un negativo se invierte el sentido" : ""), fig: { id: "op-div", bind: { A, c: e.rhs, x } } };
  }
  function quadStep(e, x, cs, env) {
    const L = e.lhs, R = e.rhs;
    const isSqOf = n => n.t === "pow" && isNum(n.e) && qeq(n.e.q, Q(2)) && (() => { const c = coeffs(n.b, x); return c && c.length === 2; })();
    if (isSqOf(L) && !has(R, x)) return rootStep(L.b, R, x);
    const lc = coeffs(L, x), rc = coeffs(R, x);
    const a = clean(cs[2]), b = clean(cs[1]), c = clean(cs[0]);
    if (!isZero(clean(R)) && !(lc && rc && lc.length === 3 && isOne(clean(lc[2])) && isZero(clean(lc[0])) && rc.length === 1))
      return { repl: [E(polyE(cs, x), int(0))], desc: "Forma normal: todo al primer miembro", fig: { id: "op-add", bind: { L, R, d: clean(Neg(R)), x } } };
    if (isZero(clean(R)) && !isOne(a)) return { repl: [E(polyE(cs.map(k => clean(Div(k, a))), x), int(0))], desc: `Dividir por ${S(a)}` + (isConst(a) ? "" : ` (suponiendo ${S(a)} ≠ 0)`), fig: { id: "op-mul", bind: { L, R, k: clean(Div(int(1), a)), x } } };
    if (isZero(clean(R)) && isZero(c) && !isZero(b)) return { repl: [E(Mul(sym(x), Add(sym(x), b)), int(0))], desc: `Sacar factor común ${x} (Euclides II.1)`, fig: { id: "commonf", bind: { g: sym(x), rest: Add(sym(x), b) } } };
    if (isZero(clean(R)) && !isZero(c)) return { repl: [E(polyE([int(0), b, int(1)], x), clean(Neg(c)))], desc: "Pasar el término independiente al otro miembro", fig: { id: "op-add", bind: { L, R, d: clean(Neg(c)), x } } };
    const p = clean(lc[1]);
    if (isZero(p)) return rootStep(sym(x), R, x);
    const h = clean(Div(p, int(2)));
    return { repl: [E(Pow(Add(sym(x), h), int(2)), clean(Add(R, Pow(h, int(2)))))], desc: `Completar el cuadrado: sumar (${S(h)})² a los dos miembros (Euclides II.6, el gnomon)`, fig: { id: "op-complete", bind: { x, p } } };
  }
  function rootStep(B, R, x) {
    const Rc = clean(R);
    if (isConst(Rc) && evalN(Rc) < -1e-12) return { repl: [], desc: `Un cuadrado no puede tener área ${S(Rc)} (negativa): no hay solución real`, fig: { id: "op-sqrt", bind: { R: Rc } } };
    if (isZero(Rc)) return { repl: [E(B, int(0))], desc: "El cuadrado tiene área 0: su lado es 0", fig: { id: "op-sqrt", bind: { R: Rc } } };
    const s = sqrtE(Rc);
    return { repl: [E(B, s), E(B, clean(Neg(s)))], desc: `Extraer la raíz: el lado del cuadrado de área ${S(Rc)} mide ±${S(s)} (media proporcional, VI.13)` + (isConst(Rc) ? "" : ` (si ${S(Rc)} ≥ 0)`), fig: { id: "op-sqrt", bind: { R: Rc } } };
  }
  function highStep(e, x, cs, env) {
    const L = e.lhs, R = e.rhs;
    if (!isZero(clean(R)) || !coeffs(L, x)) return { repl: [E(polyE(cs, x), int(0))], desc: "Forma normal: todo al primer miembro", fig: { id: "op-add", bind: { L, R, d: clean(Neg(R)), x } } };
    // potencia pura: a·xⁿ + c = 0 → x = ⁿ√(−c/a)
    const nzI = cs.map((c, i) => isZero(clean(c)) ? -1 : i).filter(i => i >= 0);
    if (nzI.length === 2 && nzI[0] === 0) {
      const n = nzI[1], K = clean(Div(Neg(cs[0]), cs[n])), r = clean(Pow(K, frac(1, n)));
      if (n % 2) return { repl: [E(sym(x), r)], desc: `Raíz ${n === 3 ? "cúbica" : "de índice " + n}: ${x}${n === 3 ? "³" : "^" + n} = ${S(K)}` + (n === 3 ? " es la arista del cubo de ese volumen (Menecmo)" : ""), fig: { id: "op-root", bind: { K, n } } };
      if (neg0(K)) return { repl: [], desc: `Una potencia par no puede valer ${S(K)}: no hay solución real`, fig: { id: "op-root", bind: { K, n } } };
      return { repl: [E(sym(x), r), E(sym(x), clean(Neg(r)))], desc: `Raíz de índice ${n}: dos soluciones opuestas`, fig: { id: "op-root", bind: { K, n } } };
    }
    const allC = cs.every(c => isConst(clean(c)));
    if (allC) {
      const f = factor(polyE(cs, x));
      if (f.t === "mul" && f.a.filter(g => has(g, x)).length >= 2 || (f.t === "pow" && has(f.b, x)) || (f.t === "mul" && f.a.some(g => g.t === "pow" && has(g, x))))
        if (S(f) !== S(L)) return { repl: [E(f, int(0))], desc: "Factorizar buscando raíces racionales (Ruffini)", fig: { id: "trinom", bind: { f, v: x } } };
      if (cs.length - 1 === 3) return cardanoStep(cs.map(clean), x);
    }
    return null;
  }
  function cardanoStep(cs, x) {
    const [d, c, b, a] = cs.map(k => evalN(k)), p = (3 * a * c - b * b) / (3 * a * a), q = (2 * b ** 3 - 9 * a * b * c + 27 * a * a * d) / (27 * a ** 3), D = (q / 2) ** 2 + (p / 3) ** 3, sh = -b / (3 * a);
    if (D >= 0) {
      const u = Math.cbrt(-q / 2 + Math.sqrt(D)), v = Math.cbrt(q / 2 + Math.sqrt(D)), t = u - v;
      return { repl: [E(sym(x), approx(t + sh))], desc: `Fórmula de Cardano: con ${x} = t ${sh < 0 ? "−" : "+"} ${f2(Math.abs(sh))}, t = u − v con u³ − v³ = ${f2(-q)} y 3uv = ${f2(p)} (cubo binómico); las otras dos raíces son imaginarias`, fig: { id: "op-cardano", bind: { u, v } } };
    }
    const r = 2 * Math.sqrt(-p / 3), th = Math.acos(3 * q / (2 * p) * Math.sqrt(-3 / p)) / 3, roots = [0, 1, 2].map(k => r * Math.cos(th - 2 * Math.PI * k / 3) + sh);
    return { repl: roots.sort((m, n) => m - n).map(v => E(sym(x), approx(v))), desc: "Casus irreducibilis: tres raíces reales que Cardano solo da con imaginarios; se obtienen con el método trigonométrico de Viète (ángulo triple)", fig: { id: "op-numeric", bind: { L: polyE(cs, x), R: int(0), x } } };
  }
  function numericStep(e, x, env, ctx) {
    const F = Sub(e.lhs, e.rhs), lo = ctx.periodic ? -2 * Math.PI : -50, hi = ctx.periodic ? 2 * Math.PI : 50;
    const rs = numRoots(F, x, env, lo, hi).slice(0, 12);
    if (!rs.length) return { repl: [], desc: "Las dos curvas no se cortan: no hay solución real", fig: { id: "op-numeric", bind: { L: e.lhs, R: e.rhs, x } } };
    return { repl: rs.map(r => E(sym(x), approx(r))), desc: "No hay despeje algebraico: se aproxima el corte de las dos curvas (bisección)", fig: { id: "op-numeric", bind: { L: e.lhs, R: e.rhs, x } } };
  }

  /* ---------- bucle de resolución (con ramas «o») ---------- */
  function solveBranches(branches, x, env, push, orig) {
    const ctx = { check: false, excl: [], periodic: false };
    const state = () => ({ eqs: branches.slice(), join: branches.length > 1 ? "or" : null });
    let ident = false;
    for (let guard = 0; guard < 40; guard++) {
      const i = branches.findIndex(b => !isSolved(b, x)); if (i < 0) break;
      let r = null; try { r = stepOne(branches[i], x, env, ctx); } catch (err) { console.error(err); }
      if (!r) r = numericStep(branches[i], x, env, ctx);
      if (r.ident) ident = true;
      const nb = [...branches.slice(0, i), ...r.repl, ...branches.slice(i + 1)];
      branches = nb.filter((b, k) => nb.findIndex(c => S(c.lhs) + c.rel + S(c.rhs) === S(b.lhs) + b.rel + S(b.rhs)) === k);
      if (!branches.length) { push(orig, r.desc + (ident ? "" : " — no hay solución"), r.fig, { force: true }); return []; }
      push(state(), r.desc, r.fig);
    }
    if (ctx.check || ctx.excl.length) {
      const o = orig.eqs[0], cands = branches.filter(b => isSolved(b, x)), res = cands.map(b => {
        const v = evalN(b.rhs, env), en = { ...env, [x]: v }, l = evalN(o.lhs, en), r = evalN(o.rhs, en);
        const dz = ctx.excl.some(D => Math.abs(evalN(D, en)) < 1e-9);
        return { b, v, ok: !dz && isFinite(l) && isFinite(r) && Math.abs(l - r) <= 1e-7 * (1 + Math.abs(l) + Math.abs(r)), dz };
      });
      if (ctx.periodic) return branches;
      const bad = res.filter(r => !r.ok);
      if (bad.length) {
        branches = branches.filter(b => !bad.some(r => r.b === b));
        const d = `Comprobar en la ecuación de partida: ${bad.map(r => `${x} = ${S(r.b.rhs)}${r.dz ? " anula un denominador" : " no la cumple"}`).join("; ")} (solución ajena, se descarta)`;
        push(branches.length ? state() : orig, d + (branches.length ? "" : " — no queda ninguna solución"), { id: "op-check", bind: { o, cands: res.map(r => ({ e: r.b.rhs, ok: r.ok })), x } }, { force: true });
      } else if (res.length) push(state(), "Comprobar en la ecuación de partida: todas las soluciones la cumplen", { id: "op-check", bind: { o, cands: res.map(r => ({ e: r.b.rhs, ok: true })), x } }, { force: true });
    }
    return branches;
  }

  /* ---------- inecuaciones ---------- */
  function solveIneq(e, x, env, push) {
    let cur = e;
    for (let guard = 0; guard < 6; guard++) {
      const F = Sub(cur.lhs, cur.rhs), cs = coeffs(F, x);
      if (cs && cs.length === 2 && cs.every(c => true)) {
        if (isSolved({ ...cur, rel: "=" }, x)) break;
        const r = linStep(cur, x, cs); if (!r) break; cur = r.repl[0]; push({ eqs: [cur], join: null }, r.desc, r.fig); continue;
      }
      if (cs && cs.length > 2) {
        if (!isZero(clean(cur.rhs))) { cur = E(polyE(cs, x), int(0), cur.rel); push({ eqs: [cur], join: null }, "Forma normal: comparar con 0", { id: "op-add", bind: { L: e.lhs, R: e.rhs, d: clean(Neg(e.rhs)), x } }); continue; }
        if (cs.every(c => isConst(clean(c)))) { const f = factor(cur.lhs); if (S(f) !== S(cur.lhs)) { cur = E(f, int(0), cur.rel); push({ eqs: [cur], join: null }, "Factorizar: cada factor cambia de signo en su raíz", { id: "trinom", bind: { f, v: x } }); } }
      }
      break;
    }
    if (isSolved({ ...cur, rel: "=" }, x)) return;
    const it = intervalsText(Sub(cur.lhs, cur.rhs), x, env, cur.rel);
    push({ eqs: [cur], join: null }, `Tabla de signos: ${x} ∈ ${it.txt}`, { id: "op-signs", bind: { F: Sub(cur.lhs, cur.rhs), x, rel: cur.rel } }, { force: true });
  }

  /* ---------- sistemas ---------- */
  const UNK = ["x", "y", "z", "t", "u", "v", "w"];
  function linRows(eqs, vars) {
    const rows = [];
    for (const e of eqs) {
      const row = vars.map(() => int(0)); let c = int(0);
      for (const t of termsOf(expand(Sub(e.lhs, e.rhs)))) {
        const fv = factorsOf(t).map(f => vars.indexOf(f.t === "sym" ? f.s : f.t === "pow" && f.b.t === "sym" ? f.b.s : "")).filter(i => i >= 0);
        if (!fv.length) { c = cadd(c, t); continue; }
        if (fv.length > 1 || factorsOf(t).some(f => f.t === "pow" && f.b.t === "sym" && vars.includes(f.b.s))) return null;
        const i = fv[0]; row[i] = cadd(row[i], cmul(t, cpow(sym(vars[i]), int(-1))));
      }
      rows.push({ a: row.map(clean), b: clean(Neg(c)) });
    }
    return rows;
  }
  function rowEq(r, vars) { const ts = []; r.a.forEach((c, i) => { if (!isZero(clean(c))) ts.push(term(c, vars[i], 1)); }); return E(ts.length ? Add(...ts) : int(0), r.b); }
  const nz = (e, env) => { const c = clean(e); if (isZero(c)) return false; if (isConst(c)) return Math.abs(evalN(c)) > 1e-12; return Math.abs(evalN(c, env)) > 1e-12 || true; };
  function solveSystem(P, env, push) {
    const all = new Set(); P.eqs.forEach(e => [...symbols(e.lhs), ...symbols(e.rhs)].forEach(v => all.add(v)));
    let vars = UNK.filter(v => all.has(v)); if (vars.length < Math.min(P.eqs.length, all.size)) vars = [...all].sort();
    vars = vars.slice(0, Math.max(P.eqs.length, 1));
    const rows = linRows(P.eqs, vars);
    if (rows && rows.length === vars.length) return gauss(rows, vars, env, push);
    if (P.eqs.length === 2 && vars.length === 2) return substitution(P, vars, env, push);
    push(P, "Este sistema no es lineal ni se puede despejar una incógnita: se resuelve por el corte de las curvas", null, { force: true });
  }
  function gauss(rows, vars, env, push) {
    const n = vars.length, st = () => ({ eqs: rows.map(r => rowEq(r, vars)), join: "and" });
    for (let j = 0; j < n; j++) {
      let p = rows.findIndex((r, i) => i >= j && nz(r.a[j], env));
      if (p < 0) continue;
      if (p !== j) { [rows[p], rows[j]] = [rows[j], rows[p]]; push(st(), `Intercambiar E${j + 1} y E${p + 1}`, null); }
      for (let r = j + 1; r < n; r++) {
        if (!nz(rows[r].a[j], env)) continue;
        const before = rows.map(o => ({ a: o.a.slice(), b: o.b })), m = clean(Div(rows[r].a[j], rows[j].a[j]));
        rows[r] = { a: rows[r].a.map((c, k) => clean(Sub(c, cmul(m, rows[j].a[k])))), b: clean(Sub(rows[r].b, cmul(m, rows[j].b))) };
        push(st(), `E${r + 1} − (${S(m)})·E${j + 1}: se elimina ${vars[j]} (reducción de Gauss)`, { id: "op-gauss", bind: { rows: before, j, r, m, vars } });
      }
    }
    for (let i = n - 1; i >= 0; i--) {
      const r = rows[i];
      if (!nz(r.a[i], env)) {
        const ok = isZero(clean(r.b));
        push(st(), ok ? "Queda 0 = 0: el sistema es compatible indeterminado (infinitas soluciones)" : `Queda 0 = ${S(r.b)}: el sistema es incompatible (no tiene solución)`, null, { force: true }); return;
      }
      let rhs = r.b; for (let k = i + 1; k < n; k++) rhs = Sub(rhs, cmul(r.a[k], rows[k].b));
      const v = clean(Div(rhs, r.a[i]));
      rows[i] = { a: vars.map((_, k) => k === i ? int(1) : int(0)), b: v };
      push(st(), `Despejar ${vars[i]}` + (i < n - 1 ? " sustituyendo las incógnitas ya halladas" : ""), { id: "op-div", bind: { A: r.a[i], c: rhs, x: vars[i] } });
    }
  }
  function substitution(P, vars, env, push) {
    let pick = null;
    for (let i = 0; i < 2 && !pick; i++) for (const v of [vars[1], vars[0]]) {
      const cs = coeffs(Sub(P.eqs[i].lhs, P.eqs[i].rhs), v); if (!cs || cs.length !== 2 || !isConst(clean(cs[1])) || isZero(clean(cs[1]))) continue;
      const w = vars.find(z => z !== v); if (has(cs[1], w)) continue;
      pick = { i, v, w, expr: clean(Div(Neg(cs[0]), cs[1])) }; break;
    }
    if (!pick) { push(P, "No se puede despejar ninguna incógnita: se resuelve por el corte de las curvas", null, { force: true }); return; }
    const { i, v, w, expr } = pick, other = P.eqs[1 - i];
    const eqs1 = P.eqs.slice(); eqs1[i] = E(sym(v), expr);
    push({ eqs: eqs1, join: "and" }, `Despejar ${v} en E${i + 1}`, { id: "op-add", bind: { L: P.eqs[i].lhs, R: P.eqs[i].rhs, d: int(0), x: v } });
    const sub = E(order(simplify(subs(other.lhs, { [v]: expr }))), order(simplify(subs(other.rhs, { [v]: expr }))));
    push({ eqs: [sub], join: null }, `Sustituir ${v} = ${S(expr)} en E${2 - i}: queda una ecuación solo en ${w}`, { id: "op-subst", bind: { P, v, expr } });
    const sols = solveBranches([sub], w, env, push, { eqs: [sub], join: null });
    const pts = sols.filter(b => isSolved(b, w)).map(b => ({ w: b.rhs, v: clean(subs(expr, { [w]: b.rhs })) }));
    if (pts.length === 1) push({ eqs: [E(sym(w), pts[0].w), E(sym(v), pts[0].v)].sort((a, b) => a.lhs.s < b.lhs.s ? -1 : 1), join: "and" }, `Volver a ${v} = ${S(expr)}: la solución es el punto de corte`, { id: "op-subst", bind: { P, v, expr } });
    else if (pts.length) push({ eqs: sols, join: sols.length > 1 ? "or" : null }, `Soluciones (puntos de corte): ${pts.map(p => `(${vars[0]}, ${vars[1]}) = (${S(w === vars[0] ? p.w : p.v)}, ${S(w === vars[0] ? p.v : p.w)})`).join("; ")}`, { id: "op-subst", bind: { P, v, expr } }, { force: true });
  }

  /* ---------- entrada ---------- */
  function solve(P, env, unknown) {
    const steps = [], push = (P2, desc, fig, o = {}) => steps.push({ P: P2, desc, fig, ...o });
    try {
      if (P.join === "and" && P.eqs.length > 1) { solveSystem(P, env, push); return steps; }
      const vs = new Set(); P.eqs.forEach(e => [...symbols(e.lhs), ...symbols(e.rhs)].forEach(v => vs.add(v)));
      const x = unknown || ["x", "t", "y", "z"].find(v => vs.has(v)) || [...vs].sort()[0];
      if (!x) { push(P, "No hay ninguna incógnita: solo hay que calcular", null, { force: true }); return steps; }
      if (P.eqs.length === 1 && P.eqs[0].rel !== "=") { solveIneq(P.eqs[0], x, env, push); return steps; }
      solveBranches(P.eqs.slice(), x, env, push, P);
    } catch (err) { console.error(err); push(P, "No sé seguir resolviendo esta ecuación paso a paso", null, { force: true }); }
    return steps;
  }

  /* ---------- figuras de las operaciones ---------- */
  const V = (e, env) => evalN(e, env);
  // valor de la incógnita en el que se cumple la ecuación L = R de la figura (si hay varias ramas, la suya)
  function fit(b, env) {
    if (!b.x || !b.L || !b.R) return env;
    const l = V(b.L, env), r = V(b.R, env); if (isFinite(l) && isFinite(r) && Math.abs(l - r) < 1e-7 * (1 + Math.abs(l))) return env;
    const rs = numRoots(Sub(b.L, b.R), b.x, env).filter(v => { const en = { ...env, [b.x]: v }; return isFinite(V(b.L, en)) && isFinite(V(b.R, en)); });
    return rs.length ? { ...env, [b.x]: rs.find(v => v > 0) ?? rs[0] } : env;
  }
  const reg = (id, name, ref, fig) => REGLAS.register({ id, name, ref, fig });
  function rods(Lv, Rv, dv, t, labs, mode) {
    const items = [], p = ph(t, .2, .8), y1 = 1.2, y2 = 0, H = .35;
    const bar = (x0, w, y, col, o = {}) => rect(Math.min(x0, x0 + w), y, Math.abs(w), H, col, o);
    items.push(bar(0, Lv, y1, C.blue), bar(0, Rv, y2, C.gold), txt([Lv / 2, y1 + H], labs[0], C.blue, { dy: -10, f: 12 }), txt([Rv / 2, y2], labs[1], C.gold, { dy: 14, f: 12 }));
    if (mode === "add") { const col = dv < 0 ? C.red : C.green; items.push(bar(Lv, dv * p, y1, col, { dash: dv < 0 ? [5, 4] : null }), bar(Rv, dv * p, y2, col, { dash: dv < 0 ? [5, 4] : null })); if (p > .5) items.push(txt([Lv + dv / 2, y1 + H], labs[2], col, { dy: -10, f: 12, b: 1 })); }
    if (mode === "scale") { const k = dv; items.push(bar(0, Lv * lerp(1, k, p), y1 - .45, C.green, { a: .45 }), bar(0, Rv * lerp(1, k, p), y2 + .45, C.green, { a: .45 })); if (p > .5) items.push(txt([Lv * k / 2, y1 - .45], labs[2], C.green, { dy: -9, f: 12, b: 1 })); }
    return items;
  }
  reg("op-add", "Sumar lo mismo a los dos miembros", "igualdad de segmentos", (b, env, t) => {
    env = fit(b, env); const Lv = V(b.L, env), Rv = V(b.R, env), dv = V(b.d, env);
    if (bad(Lv, Rv, dv)) return noFig("Trasponer", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    return scene("Trasponer: lo mismo a las dos varillas", `Con ${b.x} = ${f2(env[b.x])} las dos varillas (los dos miembros) miden lo mismo. Si a las dos se les añade o quita el mismo trozo (${S(b.d)}), siguen siendo iguales: por eso un término «pasa» al otro miembro cambiado de signo.`,
      rods(Lv, Rv, dv, t, [`primer miembro = ${f2(Lv)}`, `segundo = ${f2(Rv)}`, (dv < 0 ? "− " : "+ ") + f2(Math.abs(dv))], "add"));
  });
  reg("op-div", "Dividir los dos miembros", "aplicación de áreas / Tales", (b, env, t) => {
    const A = V(b.A, env), c = V(b.c, env), X = c / A;
    if (bad(A, c, X) || !A) return noFig("Dividir", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const p = ph(t, .2, .85), W = Math.abs(A), w = lerp(W, 1, p), H = Math.abs(X);
    const items = [rect(0, 0, W, H || .05, C.blue, { a: .15, dash: [4, 4] }), rect(0, 0, w, H || .05, C.green, { a: .35 }), txt([W / 2, 0], `${S(b.A)} = ${f2(A)}`, C.blue, { dy: 14, f: 12 }), txt([w, H / 2], `${b.x} = ${f2(X)}`, C.green, { al: "left", dx: 8, b: 1 })];
    items.push(txt([W / 2, H], `área ${S(b.A)}·${b.x} = ${f2(c)}`, C.blue, { dy: -12, f: 12 }));
    return scene("Dividir: de un rectángulo a una franja", `${S(b.A)}·${b.x} = c es un rectángulo de base ${S(b.A)} y área c (Euclides I.44). Dividir por ${S(b.A)} es quedarse con la franja de base 1: su altura es ${b.x} = c / ${S(b.A)}.`, items);
  });
  reg("op-mul", "Multiplicar los dos miembros", "semejanza (Tales)", (b, env, t) => {
    env = fit(b, env); const Lv = V(b.L, env), Rv = V(b.R, env), k = V(b.k, env);
    if (bad(Lv, Rv, k)) return noFig("Multiplicar", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    return scene("Multiplicar: las dos varillas escalan igual", `Multiplicar los dos miembros por ${S(b.k)} (= ${f2(k)}) escala las dos varillas en la misma proporción (Tales): si eran iguales, siguen siéndolo. Si ${S(b.k)} vale 0 en algún punto, ese punto puede ser una solución ajena.`,
      rods(Lv, Rv, k, t, [`primer miembro = ${f2(Lv)}`, `segundo = ${f2(Rv)}`, `× ${f2(k)}`], "scale"));
  });
  reg("op-complete", "Completar el cuadrado", "Euclides II.6", (b, env, t) => {
    const X = Math.abs(env[b.x] ?? 2) || 2, P = V(b.p, env);
    return figComplete(X, P, b.x, S(b.p), t, "Completar el cuadrado (II.6)", `El rectángulo ${S(b.p)}·${b.x} se parte en dos tiras que se pegan al cuadrado ${b.x}²; falta la esquina (${S(b.p)}/2)², que se suma a los dos miembros para cerrar el cuadrado.`);
  });
  reg("op-sqrt", "Extraer la raíz", "media proporcional (VI.13)", (b, env, t) => {
    const Rv = V(b.R, env);
    if (bad(Rv)) return noFig("Extraer la raíz", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    if (Rv < 0) return scene("No hay cuadrado de área negativa", `El segundo miembro vale ${f2(Rv)} < 0: ningún cuadrado real tiene esa área, así que no hay solución real.`, [rect(0, 0, 2, 2, C.red, { nofill: 1, dash: [5, 4] }), txt([1, 1], `área ${f2(Rv)} ?`, C.red, { b: 1 })]);
    return figMean(1, Rv || 1e-6, "1", S(b.R), t, "Extraer la raíz: el lado del cuadrado", `El lado del cuadrado de área ${S(b.R)} es la media proporcional entre 1 y ${S(b.R)}. Hay dos lados con signo: + y −.`);
  });
  reg("op-square", "Elevar al cuadrado", "cuadrados sobre segmentos iguales", (b, env, t) => {
    env = fit(b, env); const Lv = V(b.L, env), Rv = V(b.R, env); if (bad(Lv, Rv)) return noFig("Elevar al cuadrado", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const p = ph(t, .2, .8), a = Math.abs(Lv), c = Math.abs(Rv), g = .3 * Math.max(a, c, 1);
    const items = [seg([0, 0], [a, 0], C.blue, { w: 4 }), seg([a + g, 0], [a + g + c, 0], C.gold, { w: 4 }), rect(0, 0, a, a * p, C.blue), rect(a + g, 0, c, c * p, C.gold)];
    items.push(txt([a / 2, a * p], `${f2(Lv)}² = ${f2(Lv * Lv)}`, C.blue, { dy: -12, f: 12 }), txt([a + g + c / 2, c * p], `${f2(Rv)}² = ${f2(Rv * Rv)}`, C.gold, { dy: -12, f: 12 }));
    return scene("Elevar al cuadrado los dos miembros", "Sobre segmentos iguales se levantan cuadrados iguales. Pero dos segmentos opuestos (a y −a) también dan el mismo cuadrado: por eso aparecen soluciones ajenas y hay que comprobar.", items);
  });
  reg("op-zero", "Producto nulo", "rectángulo de área cero", (b, env, t) => {
    const vs = b.fs.map(f => V(f, env)); if (bad(...vs)) return noFig("Producto nulo", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const p = ph(t, .15, .85), items = [];
    if (vs.length === 2) {
      const W = Math.abs(vs[0]) || 0, H = Math.abs(vs[1]) || 0, w = W || lerp(1.5, 0, p), h = H || lerp(1.5, 0, p);
      items.push(rect(0, 0, Math.max(w, .02), Math.max(h, .02), C.blue), txt([w / 2, 0], `${S(b.fs[0])} = ${f2(vs[0])}`, C.blue, { dy: 14, f: 12 }), txt([0, h / 2], `${S(b.fs[1])} = ${f2(vs[1])}`, C.gold, { al: "right", dx: -8, f: 12 }));
      items.push(txt([Math.max(w, 1) / 2, Math.max(h, 1)], `área = ${f2(vs[0] * vs[1])}`, C.ink, { dy: -12, b: 1 }));
    } else vs.forEach((v, i) => items.push(seg([0, -i * .6], [Math.abs(v) || .02, -i * .6], PAL()[i % 6], { w: 5 }), txt([0, -i * .6], `${S(b.fs[i])} = ${f2(v)}`, PAL()[i % 6], { al: "right", dx: -8, f: 12 })));
    return scene("Producto nulo", `Si el producto vale 0, la figura tiene área (o volumen) cero: uno de sus lados mide 0. Con ${b.x} = ${f2(env[b.x])} es nulo el factor que se anula aquí; las otras soluciones anulan los otros factores.`, items);
  });
  reg("op-abs", "Separar en casos", "distancia", (b, env, t) => {
    const Rv = V(b.R, env), Av = V(b.A, env); if (bad(Rv, Av)) return noFig("Valor absoluto", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const L = Math.max(Math.abs(Rv), Math.abs(Av), 1) * 1.4, items = [seg([-L, 0], [L, 0], C.ink, { w: 1.4 }), { k: "pt", p: [0, 0], c: C.ink, r: 4, lab: "0", dx: 0, dy: 16, al: "center" }];
    items.push(seg([0, .25], [Rv, .25], C.green, { w: 3 }), seg([0, .25], [-Rv, .25], C.green, { w: 3, dash: [5, 4] }), { k: "pt", p: [Rv, 0], c: C.green, r: 5, lab: f2(Rv), dx: 0, dy: 16, al: "center" }, { k: "pt", p: [-Rv, 0], c: C.green, r: 5, lab: f2(-Rv), dx: 0, dy: 16, al: "center" });
    items.push({ k: "pt", p: [Av, 0], c: C.violet, r: 4, lab: `${S(b.A)}`, dx: 0, dy: -14, al: "center" });
    return scene("|A| = B: dos puntos a la misma distancia", `${S(b.A)} está a distancia ${S(b.R)} del 0: a la derecha (A = B) o a la izquierda (A = −B). Si B fuese negativo, no habría solución.`, items, { box: [-L, L, -.6, .9] });
  });
  reg("op-log", "Logaritmos", "escala logarítmica", (b, env, t) => {
    const B = V(b.base, env), Rv = V(b.R, env); if (bad(B, Rv) || B <= 0 || B === 1) return noFig("Logaritmos", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const items = [], k = Math.log(Rv) / Math.log(B), lo = Math.floor(Math.min(0, k)) - 1, hi = Math.ceil(Math.max(3, k)) + 1;
    items.push(seg([lo, 0], [hi, 0], C.ink, { w: 1.4 }));
    for (let j = lo; j <= hi; j++) items.push(seg([j, -.1], [j, .1], C.muted, { w: 1 }), txt([j, 0], f2(Math.pow(B, j)), C.muted, { dy: 16, f: 11 }), txt([j, 0], String(j), C.blue, { dy: -16, f: 11 }));
    if (isFinite(k)) items.push({ k: "pt", p: [k * ph(t, .1, .8), 0], c: C.green, r: 6, lab: `${f2(Rv)} → exponente ${f2(k)}`, dx: 0, dy: -30, al: "center" });
    return scene("Escala logarítmica", `Arriba, exponentes (una progresión aritmética: se suman); abajo, potencias de ${f2(B)} (geométrica: se multiplican). El logaritmo de ${f2(Rv)} es su posición en la regla: ${f2(k)}.`, items, { box: [lo - .3, hi + .3, -1, 1] });
  });
  reg("op-trig", "Ángulos", "circunferencia unidad", (b, env, t) => {
    const c = V(b.c, env); if (bad(c)) return noFig("Ángulos", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const items = [{ k: "circ", o: [0, 0], r: 1, c: C.ink, w: 1.8 }, seg([-1.3, 0], [1.3, 0], C.muted, { w: 1 }), seg([0, -1.3], [0, 1.3], C.muted, { w: 1 })];
    const angs = b.f === "sin" ? (Math.abs(c) <= 1 ? [Math.asin(c), Math.PI - Math.asin(c)] : []) : b.f === "cos" ? (Math.abs(c) <= 1 ? [Math.acos(c), -Math.acos(c)] : []) : [Math.atan(c), Math.atan(c) + Math.PI];
    if (b.f === "sin") items.push(seg([-1.3, c], [1.3, c], C.gold, { w: 2, dash: [6, 4] }));
    if (b.f === "cos") items.push(seg([c, -1.3], [c, 1.3], C.blue, { w: 2, dash: [6, 4] }));
    if (b.f === "tan") items.push(seg([-1.3 * Math.cos(angs[0]), -1.3 * Math.sin(angs[0])], [1.3 * Math.cos(angs[0]), 1.3 * Math.sin(angs[0])], C.green, { w: 2, dash: [6, 4] }));
    angs.forEach((a, i) => { const P = [Math.cos(a), Math.sin(a)], q = ph(t, .1 + .3 * i, .6 + .3 * i); items.push(seg([0, 0], [P[0] * q, P[1] * q], C.violet, { w: 2.4 }), { k: "pt", p: P, c: C.violet, r: 5, lab: f2(a), dx: P[0] >= 0 ? 8 : -8, al: P[0] >= 0 ? "left" : "right" }); });
    return scene("Ángulos en la circunferencia unidad", `${b.f === "sin" ? "El seno es la altura" : b.f === "cos" ? "El coseno es la abscisa" : "La tangente es la pendiente"}: la recta ${b.f === "tan" ? "por el origen" : `${b.f === "sin" ? "y" : "x"} = ${f2(c)}`} corta la circunferencia en dos puntos (dos ángulos), y cada vuelta completa repite la solución.`, items, { box: [-1.5, 1.5, -1.4, 1.4] });
  });
  reg("op-check", "Comprobar", "sustituir en la ecuación de partida", (b, env, t) => {
    const items = [];
    b.cands.forEach((c, i) => {
      const v = V(c.e, env), en = { ...env, [b.x]: v }, l = V(b.o.lhs, en), r = V(b.o.rhs, en), y = -i * 1.4, m = Math.max(Math.abs(l), Math.abs(r), 1e-9), sc = 4 / m;
      if (bad(l, r)) { items.push(txt([0, y], `${b.x} = ${f2(v)}: la expresión no existe (${c.ok ? "" : "ajena"})`, C.red, { al: "left", f: 12 })); return; }
      items.push(rect(0, y, l * sc, .4, C.blue), rect(0, y - .5, r * sc, .4, C.gold), txt([0, y + .2], `${b.x} = ${f2(v)}`, c.ok ? C.green : C.red, { al: "right", dx: -10, b: 1, f: 13 }), txt([Math.max(l, r) * sc, y - .05], c.ok ? `${f2(l)} = ${f2(r)} ✓` : `${f2(l)} ≠ ${f2(r)} ✗ ajena`, c.ok ? C.green : C.red, { al: "left", dx: 10, f: 12, b: 1 }));
    });
    return scene("Comprobar en la ecuación de partida", "Para cada candidata se miden los dos miembros de la ecuación original: si las dos varillas coinciden, es solución; si no, es ajena (la introdujo elevar al cuadrado, quitar denominadores o separar casos).", items);
  });
  reg("op-numeric", "Aproximar", "corte de curvas", (b, env, t) => {
    const f = e => v => evalN(e, { ...env, [b.x]: v }), Lf = f(b.L), Rf = f(b.R), rs = numRoots(Sub(b.L, b.R), b.x, env);
    const lo = Math.min(...rs, 0) - 2, hi = Math.max(...rs, 0) + 2, ys = [];
    for (let i = 0; i <= 80; i++) { const v = lo + (hi - lo) * i / 80; [Lf(v), Rf(v)].forEach(y => isFinite(y) && ys.push(y)); }
    ys.sort((p, q) => p - q); const y0 = Math.min(ys[Math.floor(ys.length * .05)] ?? -1, 0), y1 = Math.max(ys[Math.ceil(ys.length * .95) - 1] ?? 1, 0);
    const items = [seg([lo, 0], [hi, 0], C.muted, { w: 1 }), { k: "curve", f: Lf, c: C.red, w: 2.2, x0: lo, x1: hi }, { k: "curve", f: Rf, c: C.blue, w: 2.2, x0: lo, x1: hi }];
    rs.forEach(r => items.push({ k: "pt", p: [r, Lf(r)], c: C.green, r: 5, lab: f2(r), dy: -12 }));
    return { title: "Corte de las dos curvas", cap: "Rojo: primer miembro; azul: segundo. Donde se cortan, los dos miembros miden lo mismo; la bisección encierra cada corte en intervalos cada vez más pequeños.", items, box: [lo, hi, y0 - .1 * (y1 - y0 || 1), y1 + .1 * (y1 - y0 || 1)], free: true };
  });
  reg("op-signs", "Tabla de signos", "regiones de la recta", (b, env, t) => {
    const it = intervalsText(b.F, b.x, env, b.rel), rs = it.roots, lo = Math.min(...rs, 0) - 2, hi = Math.max(...rs, 0) + 2, items = [seg([lo, 0], [hi, 0], C.ink, { w: 1.4 })];
    it.out.forEach(I => items.push(seg([Math.max(I.a, lo), .18], [Math.min(I.b, hi), .18], C.green, { w: 6 })));
    const pts = [lo, ...rs, hi]; for (let i = 0; i < pts.length - 1; i++) { const m = (pts[i] + pts[i + 1]) / 2, y = evalN(b.F, { ...env, [b.x]: m }); items.push(txt([m, 0], y > 0 ? "+" : y < 0 ? "−" : "0", y > 0 ? C.green : C.red, { dy: -22, b: 1, f: 16 })); }
    rs.forEach(r => items.push({ k: "pt", p: [r, 0], c: C.ink, r: 4, lab: f2(r), dx: 0, dy: 16, al: "center" }));
    return scene("Tabla de signos", `El polinomio solo cambia de signo en sus raíces. Verde: donde se cumple ${S(b.F)} ${b.rel} 0, es decir ${b.x} ∈ ${it.txt}.`, items, { box: [lo, hi, -.6, .8] });
  });
  reg("op-gauss", "Reducción de Gauss", "haz de rectas", (b, env, t) => {
    if (b.vars.length !== 2) {
      const items = []; b.rows.forEach((r, i) => { r.a.forEach((c, k) => items.push(txt([k * 2.2, -i], S(c), i === b.r ? C.red : i === b.j ? C.blue : C.ink, { f: 13, b: i === b.r })) ); items.push(txt([b.vars.length * 2.2 + .4, -i], "| " + S(r.b), C.ink, { f: 13, al: "left" })); });
      return scene("Reducción de Gauss", `Se resta a E${b.r + 1} la ecuación E${b.j + 1} multiplicada por ${S(b.m)}, para que desaparezca ${b.vars[b.j]}. Cada ecuación lineal en ${b.vars.length} incógnitas es un hiperplano; la combinación pasa por los mismos puntos comunes.`, items, { box: [-1, b.vars.length * 2.2 + 2, -b.rows.length, 1] });
    }
    const row = r => [V(r.a[0], env), V(r.a[1], env), V(r.b, env)], A1 = row(b.rows[b.j]), A2 = row(b.rows[b.r]), m = V(b.m, env), p = ph(t, .15, .85);
    const Ax = [A2[0] - p * m * A1[0], A2[1] - p * m * A1[1], A2[2] - p * m * A1[2]], D = A1[0] * A2[1] - A2[0] * A1[1];
    const P0 = Math.abs(D) > 1e-12 ? [(A1[2] * A2[1] - A2[2] * A1[1]) / D, (A1[0] * A2[2] - A2[0] * A1[2]) / D] : [0, 0], Sz = 4 + Math.max(Math.abs(P0[0]), Math.abs(P0[1])) * .5;
    const line = (r, col, o = {}) => { const [a, c, d] = r, pts = []; if (Math.abs(c) > 1e-9) for (const xx of [P0[0] - Sz, P0[0] + Sz]) pts.push([xx, (d - a * xx) / c]); else if (Math.abs(a) > 1e-9) for (const yy of [P0[1] - Sz, P0[1] + Sz]) pts.push([d / a, yy]); return pts.length ? seg(pts[0], pts[1], col, o) : null; };
    const items = [line(A1, C.blue, { w: 2.2 }), line(A2, C.red, { w: 1.4, dash: [5, 5] }), line(Ax, C.green, { w: 2.6 }), { k: "pt", p: P0, c: C.ink, r: 5, lab: `(${f2(P0[0])}, ${f2(P0[1])})` }].filter(Boolean);
    return { title: "Gauss: la recta gira alrededor del punto común", cap: `E${b.r + 1} − (${S(b.m)})·E${b.j + 1} es otra recta del mismo haz: gira alrededor del punto de corte hasta quedar ${Math.abs(A2[0] - m * A1[0]) < 1e-9 ? "horizontal" : "vertical"} (sin ${b.vars[b.j]}). La solución no cambia.`, items, box: [P0[0] - Sz, P0[0] + Sz, P0[1] - Sz, P0[1] + Sz], axes: true };
  });
  reg("op-subst", "Sustitución", "corte de curvas", (b, env, t) => {
    const [x, y] = [...new Set(b.P.eqs.flatMap(e => [...symbols(e.lhs), ...symbols(e.rhs)]))].sort(), items = [], cols = [C.red, C.blue];
    b.P.eqs.forEach((e, i) => { const F = Sub(e.lhs, e.rhs), cs = coeffs(F, y); if (cs && cs.length === 2) items.push({ k: "curve", f: v => -evalN(cs[0], { ...env, [x]: v }) / evalN(cs[1], { ...env, [x]: v }), c: cols[i], w: 2.2 }); else { const cx = coeffs(F, x); if (!(cx && cx.length === 2)) return; const g = v => -evalN(cx[0], { ...env, [y]: v }) / evalN(cx[1], { ...env, [y]: v }); const pts = []; for (let k = 0; k <= 60; k++) { const yy = -8 + 16 * k / 60; pts.push([g(yy), yy]); } items.push({ k: "poly", p: pts, close: false, c: cols[i], w: 2.2 }); } });
    return { title: "Sustituir: recorrer una curva sobre la otra", cap: `Al despejar ${b.v} = ${S(b.expr)} y sustituir, se buscan los puntos de una curva que están también sobre la otra: los cortes.`, items, box: [-8, 8, -8, 8], axes: true };
  });
  reg("op-root", "Raíz n-ésima", "arista del cubo (Menecmo)", (b, env, t) => {
    const K = V(b.K, env); if (bad(K)) return noFig("Raíz", "Con los valores actuales de las letras esta figura no existe: mueve los deslizadores de las letras");
    const s = Math.pow(Math.abs(K), 1 / b.n);
    if (b.n === 3) return figCube(s, 1e-6 + s * 0, "∛K", "", t, false, "La raíz cúbica es la arista del cubo", `Un cubo de volumen ${f2(K)} tiene arista ${f2(Math.sign(K) * s)}. Hallarla con regla y compás es imposible (duplicación del cubo); Menecmo lo hizo cortando dos cónicas.`);
    return scene("Raíz n-ésima", `La raíz de índice ${b.n} de ${f2(K)} es el lado de un «cubo» de dimensión ${b.n} y volumen ${f2(K)}: mide ${f2(s)}.`, [rect(0, 0, s, s, C.green), txt([s / 2, 0], `lado = ${f2(s)}`, C.green, { dy: 14 })]);
  });
  reg("op-cardano", "Cardano", "cubo binómico", (b, env, t) => figCube(Math.abs(b.u - b.v) || 1, Math.abs(b.v) || 1, "t", "v", t, false, "Cardano: la incógnita como diferencia de aristas", `t = u − v: el cubo de arista u se despieza en el cubo t³, el cubo v³ y las losas y vigas; u ≈ ${f2(b.u)}, v ≈ ${f2(b.v)}.`));

  return { solve };
})();
