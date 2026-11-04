/* Geometría del Álgebra — cálculo (fase 5): derivadas e integrales paso a paso con su geometría.
   Derivar es medir cómo crece una figura: el cuadrado x² crece en dos tiras 2x·dx (el gnomon),
   el cubo en tres losas 3x²·dx, el rectángulo u·v en u·dv + v·du (Leibniz).
   Integrar es medir un área: rectángulos cada vez más finos (Riemann), Arquímedes para la parábola,
   la hipérbola para el logaritmo y la regla de Barrow. Usa del visor: C, AL, fmt; de REGLAS.G el dibujo. */
"use strict";
const CALC = (() => {
  const { Q, num, int, frac, sym, isNum, isZero, isOne, Add, Mul, Pow, Fn, Neg, Sub, Div, key, cmul, cpow, simplify, expand, order, str, evalN, symbols, subs, coeffs, together, radsimp, qnum } = CAS;
  const { ph, lerp, rect, txt, seg, scene, noFig, f2, bad, figCube } = REGLAS.G;
  const X = sym("x"), D = u => Fn("deriv", u), I = u => Fn("integ", u), S = e => str(e);
  const hasX = e => symbols(e).includes("x");
  const isD = n => n.t === "fn" && n.f === "deriv", isI = n => n.t === "fn" && n.f === "integ";
  const clean = e => { const a = order(radsimp(together(e))), b = order(radsimp(expand(e))); return str(b).length < str(a).length ? b : a; };
  const children = e => e.t === "add" || e.t === "mul" ? e.a : e.t === "pow" ? [e.b, e.e] : e.t === "fn" ? [e.x] : [];
  function find(e, pred, path = []) { if (pred(e)) return path; const ch = children(e); for (let i = 0; i < ch.length; i++) { const p = find(ch[i], pred, path.concat(i)); if (p) return p; } return null; }
  function at(e, path) { for (const i of path) e = children(e)[i]; return e; }
  function put(e, path, sub) {
    if (!path.length) return sub;
    const [i, ...r] = path;
    if (e.t === "add" || e.t === "mul") { const a = e.a.slice(); a[i] = put(a[i], r, sub); return e.t === "add" ? Add(...a) : Mul(...a); }
    if (e.t === "pow") return i === 0 ? Pow(put(e.b, r, sub), e.e) : Pow(e.b, put(e.e, r, sub));
    return Fn(e.f, put(e.x, r, sub));
  }
  // juntar los números de cada producto: x·(−1)·cos x → −x·cos x; −(−∫…) → +∫…; 1·eˣ → eˣ
  function tidy(e) {
    if (e.t === "add") return Add(...e.a.map(tidy));
    if (e.t === "mul") {
      const fs = e.a.map(tidy).flatMap(f => f.t === "mul" ? f.a : [f]); let q = CAS.ONE; const rest = [];
      for (const f of fs) { if (isNum(f)) q = CAS.qmul(q, f.q); else rest.push(f); }
      if (q.n === 0n) return int(0);
      if (!rest.length) return num(q);
      return CAS.qeq(q, CAS.ONE) ? Mul(...rest) : CAS.qeq(q, Q(-1)) ? Neg(Mul(...rest)) : Mul(num(q), ...rest);
    }
    if (e.t === "pow") return Pow(tidy(e.b), tidy(e.e));
    if (e.t === "fn") return Fn(e.f, tidy(e.x));
    return e;
  }
  const isLinX = u => { const c = coeffs(u, "x"); return c && c.length === 2 && !hasX(c[1]) ? c : null; };

  /* ---------- un paso de derivación: se aplica una regla al primer d/dx(…) ---------- */
  function dStep(e) {
    const p = find(e, isD); if (!p) return null;
    const u = at(e, p).x, R = (res, id, desc, bind = {}) => ({ e: tidy(put(e, p, res)), id, desc, bind: { u, ...bind } });
    if (!hasX(u)) return R(int(0), "d-const0", `La derivada de una constante es 0: lo que no cambia no crece`);
    if (u.t === "sym") return R(int(1), "d-x", "d/dx(x) = 1: si x crece dx, x crece dx");
    if (u.t === "add") return R(Add(...u.a.map(D)), "d-sum", "La derivada de una suma es la suma de derivadas: los crecimientos se apilan");
    if (u.t === "mul") {
      const k = u.a.filter(f => !hasX(f) && !isOne(f)), v = u.a.filter(hasX);
      if (!k.length && v.length === 1) return R(D(v[0]), "d-const", "Simplificar el factor 1");
      if (k.length && v.length) return R(Mul(...k, D(Mul(...v))), "d-const", `Una constante sale fuera: ${S(Mul(...k))} escala la pendiente (Tales)`, { k: Mul(...k), v: Mul(...v) });
      const a = v[0], b = Mul(...v.slice(1));
      if (b.t === "pow" && isNum(b.e) && b.e.q.n < 0n && v.length === 2) {} // cociente: se trata como producto con potencia −1 (cadena)
      return R(Add(Mul(D(a), b), Mul(a, D(b))), "d-prod", "Regla del producto (Leibniz): el rectángulo u·v crece en v·du + u·dv", { a, b });
    }
    if (u.t === "pow") {
      const B = u.b, E = u.e;
      if (!hasX(E)) {
        const n = E, n1 = simplify(Add(E, int(-1)));
        if (B.t === "sym" && B.s === "x") return R(cmul(n, cpow(X, n1)), "d-pow", `Regla de la potencia: d/dx(x${isNum(n) && qnum(n.q) === 2 ? "²" : isNum(n) && qnum(n.q) === 3 ? "³" : "^" + S(n)}) = ${S(cmul(n, cpow(X, n1)))}`, { n });
        return R(Mul(cmul(n, cpow(B, n1)), D(B)), "d-chain", `Regla de la cadena: potencia de ${S(B)} por la derivada de ${S(B)}`, { outer: Pow(sym("u"), n), g: B });
      }
      if (!hasX(B)) {
        const isE = B.t === "sym" && B.s === "e", lnB = isE ? null : Fn("ln", B);
        const res = E.t === "sym" ? (isE ? u : Mul(u, lnB)) : (isE ? Mul(u, D(E)) : Mul(u, lnB, D(E)));
        return R(res, "d-exp", isE ? "d/dx(eˣ) = eˣ: la exponencial crece en proporción a su altura" : `d/dx(${S(B)}^u) = ${S(B)}^u·ln(${S(B)})·u′`, { E });
      }
      return R(Mul(u, D(Mul(E, Fn("ln", B)))), "d-chain", "Base y exponente variables: derivada logarítmica", { outer: u, g: E });
    }
    if (u.t === "fn") {
      const g = u.x, chain = r => g.t === "sym" ? r : Mul(r, D(g)), id = g.t === "sym" ? null : "d-chain";
      const T = {
        sin: [Fn("cos", g), "d-trig", "d/dx(sen x) = cos x: en la circunferencia, la altura crece al ritmo de la abscisa"],
        cos: [Neg(Fn("sin", g)), "d-trig", "d/dx(cos x) = −sen x: la abscisa decrece al ritmo de la altura"],
        tan: [Add(int(1), Pow(Fn("tan", g), int(2))), "d-trig", "d/dx(tan x) = 1 + tan²x"],
        ln: [Pow(g, int(-1)), "d-ln", "d/dx(ln x) = 1/x: el área bajo la hipérbola crece en franjas de altura 1/x"],
        log: [Pow(Mul(g, Fn("ln", int(10))), int(-1)), "d-ln", "d/dx(log x) = 1/(x·ln 10)"],
        abs: [Mul(g, Pow(Fn("abs", g), int(-1))), "d-const", "d/dx|x| = signo de x"],
        asin: [Pow(Sub(int(1), Pow(g, int(2))), frac(-1, 2)), "d-trig", "d/dx(arcsen x) = 1/√(1 − x²)"],
        acos: [Neg(Pow(Sub(int(1), Pow(g, int(2))), frac(-1, 2))), "d-trig", "d/dx(arccos x) = −1/√(1 − x²)"],
        atan: [Pow(Add(int(1), Pow(g, int(2))), int(-1)), "d-trig", "d/dx(arctan x) = 1/(1 + x²)"],
      }[u.f];
      if (T) return R(chain(T[0]), id || T[1], g.t === "sym" ? T[2] : `Regla de la cadena: ${T[2].split(":")[0]} con ${S(g)} en lugar de x, por la derivada de ${S(g)}`, { f: u.f, g, outer: Fn(u.f, sym("u")) });
    }
    return null;
  }
  /* ---------- un paso de integración: tabla de primitivas ---------- */
  function iStep(e) {
    const p = find(e, isI); if (!p) return null;
    const u = at(e, p).x, R = (res, id, desc, bind = {}) => ({ e: tidy(put(e, p, res)), id, desc, bind: { u, ...bind } });
    if (!hasX(u)) return R(Mul(u, X), "i-const0", `∫${S(u)} dx = ${S(u)}x: un rectángulo de altura ${S(u)} y base x`);
    if (u.t === "add") return R(Add(...u.a.map(I)), "i-sum", "La integral de una suma es la suma de integrales: las áreas se apilan");
    if (u.t === "mul") {
      const k = u.a.filter(f => !hasX(f) && !isOne(f)), v = u.a.filter(hasX);
      if (!k.length && v.length === 1 && u.a.length > 1) return iStep(put(e, p, I(v[0])));
      if (k.length && v.length) return R(Mul(...k, I(Mul(...v))), "i-const", `La constante ${S(Mul(...k))} sale fuera: escala todas las alturas`, { k: Mul(...k) });
      const ex = expand(u); if (ex.t === "add") return R(I(order(ex)), "i-expand", "Desarrollar el producto para integrar término a término (Euclides II.1)");
      // por partes: ∫u·dv = u·v − ∫v·du con u polinomio y dv = eˣ, sen, cos
      const poly = v.find(f => coeffs(f, "x")), other = v.find(f => f !== poly);
      if (poly && other && v.length === 2) { const Vp = primitive(other); if (Vp) { const du = diff(poly); return R(Sub(Mul(poly, Vp), I(Mul(Vp, du))), "i-parts", `Por partes: ∫u·dv = u·v − ∫v·du con u = ${S(poly)} y dv = ${S(other)}·dx: el rectángulo u·v se reparte en dos áreas`, { uu: poly, vv: Vp }); } }
    }
    if (u.t === "sym") return R(Div(Pow(X, int(2)), int(2)), "i-pow", "∫x dx = x²/2: el área bajo y = x es un triángulo, la mitad del cuadrado", { n: int(1) });
    if (u.t === "pow") {
      const B = u.b, E = u.e;
      if (!hasX(E)) {
        const lin = isLinX(B);
        if (isNum(E) && qnum(E.q) === -1 && lin) return R(isOne(simplify(lin[1])) ? Fn("ln", Fn("abs", B)) : Div(Fn("ln", Fn("abs", B)), lin[1]), "i-recip", B.t === "sym" ? "∫dx/x = ln|x|: el área bajo la hipérbola (Gregorio de San Vicente)" : `∫dx/(${S(B)}) = ln|${S(B)}|/${S(lin[1])}`);
        if (lin) { const n1 = simplify(Add(E, int(1))); return R(Div(Pow(B, n1), cmul(n1, lin[1])), "i-pow", B.t === "sym" ? `Regla de la potencia: ∫x^n dx = x^(n+1)/(n+1)${isNum(E) && qnum(E.q) === 2 ? " (Arquímedes: la parábola encierra 1/3 del rectángulo)" : ""}` : `Potencia de una expresión lineal: se divide por ${S(lin[1])}`, { n: E }); }
        const ex = expand(u); if (ex.t === "add") return R(I(order(ex)), "i-expand", "Desarrollar la potencia para integrar término a término");
      }
      if (!hasX(B)) { const lin = isLinX(E); if (lin) { const isE = B.t === "sym" && B.s === "e", den = isE ? lin[1] : cmul(lin[1], Fn("ln", B)); return R(isOne(simplify(den)) ? u : Div(u, den), "i-exp", isE ? "∫eˣ dx = eˣ: el área bajo la exponencial hasta x es su altura" : `∫${S(B)}^x dx = ${S(B)}^x/ln(${S(B)})`); } }
    }
    if (u.t === "fn") {
      const lin = isLinX(u.x); if (lin) {
        const a = lin[1], d = r => isOne(simplify(a)) ? r : Div(r, a), g = u.x;
        const T = { sin: [Neg(Fn("cos", g)), "∫sen x dx = −cos x"], cos: [Fn("sin", g), "∫cos x dx = sen x: el área bajo el coseno es la altura en la circunferencia"] }[u.f];
        if (T) return R(d(T[0]), "i-trig", T[1], { f: u.f });
      }
    }
    return null;
  }

  /* ---------- derivar o integrar entero (para gráficas) ---------- */
  function diff(f) { let e = D(f); for (let i = 0; i < 200; i++) { const s = dStep(e); if (!s) break; e = s.e; } return find(e, isD) ? null : clean(e); }
  function primitive(f) { let e = I(f); for (let i = 0; i < 100; i++) { const s = iStep(e); if (!s) break; e = s.e; } return find(e, isI) ? null : clean(e); }

  /* ---------- estados y pasos ---------- */
  const base = o => ({ kind: "calc", rel: "=", v: "x", v0: "x", shift: 0, found: [], tag: null, notes: [], manual: false, rule: null, prop: null, desc: o.desc || "" });
  function state(op, f, cur, o = {}) {
    const lhs = op === "deriv" || op === "tan" ? D(f) : I(f);
    return { ...base(o), op, f, a: o.a, b: o.b, cur, final: !!o.final, dres: op === "deriv" || op === "tan" ? diff(f) : null, F: op !== "deriv" && op !== "tan" ? primitive(f) : null, params: [], cas: { eqs: [{ lhs, rhs: cur, rel: "=" }], join: null } };
  }
  function text(s) {
    if (s.op === "tan") return `f(x) = ${S(s.f)};  f′(x) = ${s.dres ? S(s.dres) : "…"}`;
    const fx = s.f.t === "add" ? `(${S(s.f)})` : S(s.f);
    const lhs = s.op === "defint" ? `∫[${S(s.a)}, ${S(s.b)}] ${fx} dx` : s.op === "deriv" ? `d/dx(${S(s.f)})` : `∫ ${fx} dx`;
    return `${lhs} = ${S(s.cur)}${s.op === "integ" && s.final ? " + C" : ""}`;
  }
  const tex = s => s.op === "defint" ? `\\int_{${CAS.tex(s.a)}}^{${CAS.tex(s.b)}} ${CAS.tex(s.f)}\\,dx = ${CAS.tex(s.cur)}` : `${CAS.tex(s.cas.eqs[0].lhs)} = ${CAS.tex(s.cur)}${s.op === "integ" && s.final ? " + C" : ""}`;
  function steps(op, f, a, b) {
    const out = [], first = op === "deriv" ? D(f) : I(f);
    out.push({ s: state(op, f, first, { a, b, desc: op === "deriv" ? "Derivar" : op === "defint" ? `Área bajo la curva entre ${S(a)} y ${S(b)}` : "Buscar una primitiva" }) });
    let e = first;
    for (let i = 0; i < 60; i++) {
      const st = op === "deriv" ? dStep(e) : iStep(e); if (!st) break;
      e = st.e; out.push({ s: state(op, f, e, { a, b, desc: st.desc }), fig: { id: st.id, bind: { ...st.bind, f } } });
    }
    const left = find(e, op === "deriv" ? isD : isI);
    if (left) { out.push({ s: state(op, f, e, { a, b, desc: op === "deriv" ? "No sé seguir derivando esta parte" : "Esta primitiva no está en la tabla elemental: el área se calcula numéricamente" }) }); }
    else {
      // simplificar solo si queda más corto: (x + 1)³/3 no se desarrolla
      let c = clean(e); if (S(c).length >= S(e).length) c = e;
      if (S(c) !== S(e)) out.push({ s: state(op, f, c, { a, b, desc: "Simplificar", final: true }) }); else out[out.length - 1].s.final = true;
      if (op === "defint") {
        const F = c, Fb = subs(F, { x: b }), Fa = subs(F, { x: a }), raw = Sub(Fb, Fa), v = clean(raw);
        out.push({ s: state(op, f, raw, { a, b, desc: `Regla de Barrow: F(${S(b)}) − F(${S(a)}) con F(x) = ${S(F)}` }), fig: { id: "i-barrow", bind: { f, F, a, b } } });
        out.push({ s: state(op, f, v, { a, b, desc: "Calcular", final: true }), fig: { id: "i-barrow", bind: { f, F, a, b } } });
      }
    }
    if (op === "integ" && !left) out[out.length - 1].s.desc += " — se añade la constante C (cualquier traslación vertical tiene la misma derivada)";
    return out;
  }
  /* comprobar una línea de cálculo frente a la anterior */
  function verdict(a, b) {
    if (b.op !== a.op || key(simplify(b.f)) !== key(simplify(a.f))) return { lvl: "info", msg: "nuevo cálculo" };
    const xs = [-1.7, -.6, .4, 1.3, 2.2, 3.1], env = x => ({ x });
    if (b.op === "integ" && !find(b.cur, isI)) {   // la primitiva se comprueba derivándola
      const ok = xs.every(x => { const d = evalN(D(b.cur), env(x)), f = evalN(b.f, env(x)); return !isFinite(d) || !isFinite(f) || Math.abs(d - f) < 1e-5 * (1 + Math.abs(f)); });
      return ok ? { lvl: "ok", msg: "su derivada es la función de partida" } : { lvl: "bad", msg: "al derivarla no se obtiene la función de partida" };
    }
    if (find(a.cur, isI) || find(b.cur, isI)) return { lvl: "info", msg: "" };
    let n = 0; for (const x of xs) { const p = evalN(a.cur, env(x)), q = evalN(b.cur, env(x)); if (!isFinite(p) || !isFinite(q)) continue; if (Math.abs(p - q) > 1e-4 * (1 + Math.abs(p))) return { lvl: "bad", msg: "no es igual a la línea anterior" }; n++; }
    return n ? { lvl: "ok", msg: "equivalente" } : { lvl: "info", msg: "" };
  }
  /* lectura de líneas: d/dx(…), (…)', derivada(…), ∫(…)dx, ∫_a^b(…)dx, integral(…), integral(…, a, b) */
  function parseLine(t) {
    const s = normalizeSrc(t), P = x => CAS.parse(x);
    // el paréntesis abierto en «open» debe cerrarse justo al final: «d/dx(x²)·sen x» no es una derivada entera
    const whole = (str, open) => { let d = 0; for (let i = open; i < str.length; i++) { if (str[i] === "(") d++; else if (str[i] === ")") { d--; if (!d) return i === str.length - 1; } } return false; };
    let m;
    if (s.startsWith("d/dx(") && whole(s, 4)) return { op: "deriv", f: P(s.slice(5, -1)) };
    if ((m = s.match(/^d\/dx([^(].*)$/)) && !/d\/dx/.test(m[1])) return { op: "deriv", f: P(m[1]) };
    if (s.startsWith("derivada(") && whole(s, 8)) return { op: "deriv", f: P(s.slice(9, -1)) };
    if ((m = s.match(/^\((.+)\)'$/)) && whole(s.slice(0, -1), 0)) return { op: "deriv", f: P(m[1]) };
    if ((m = s.match(/^([fg])'\(x\)$/))) return { op: "deriv", f: FUNC.defs[m[1]] };
    if ((m = s.match(/^∫_(-?[\d.π]+)\^(-?[\d.π]+)(.+)dx$/))) return { op: "defint", f: P(m[3]), a: P(m[1]), b: P(m[2]) };
    if ((m = s.match(/^integral\((.+),(-?[\d.π]+),(-?[\d.π]+)\)$/))) return { op: "defint", f: P(m[1]), a: P(m[2]), b: P(m[3]) };
    if ((m = s.match(/^∫(.+)dx$/)) || (m = s.match(/^integral\((.+)\)$/))) return { op: "integ", f: P(m[1]) };
    return null;
  }
  const isLine = t => !!parseLine(t);

  /* ---------- figuras de los pasos ---------- */
  const reg = (id, name, ref, fig) => REGLAS.register({ id, name, ref, fig });
  const fn = (e, env) => x => evalN(e, { ...env, x });
  const X0 = env => env.x0 ?? 1.2;
  function slopeTri(f, x0, dx, col, items, lab) {
    const y0 = f(x0), y1 = f(x0 + dx); items.push(seg([x0, y0], [x0 + dx, y0], col, { w: 1.6 }), seg([x0 + dx, y0], [x0 + dx, y1], col, { w: 2.4 }), seg([x0, y0], [x0 + dx, y1], col, { w: 1, dash: [4, 3] }));
    if (lab) items.push(txt([x0 + dx, (y0 + y1) / 2], lab, col, { al: "left", dx: 6, f: 11 }));
  }
  reg("d-pow", "Regla de la potencia", "gnomon del crecimiento", (b, env, t) => {
    const x = X0(env) + 1, n = isNum(b.n) ? qnum(b.n.q) : NaN, dx = lerp(.55 * x, .06 * x, ph(t, .1, .9));
    if (n === 2) {
      const items = [rect(0, 0, x, x, C.blue), txt([x / 2, x / 2], "x²", C.blue, { b: 1, f: 14 }), rect(x, 0, dx, x, C.gold), rect(0, x, x, dx, C.gold), rect(x, x, dx, dx, C.red, { a: .5 })];
      items.push(txt([x + dx / 2, x / 2], "x·dx", C.gold, { f: 11 }), txt([x / 2, x + dx / 2], "x·dx", C.gold, { f: 11 }), txt([x + dx, x + dx], "dx²", C.red, { al: "left", dx: 4, f: 11 }));
      return scene("El cuadrado crece en un gnomon", `Si el lado x crece dx, el cuadrado gana dos tiras x·dx y una esquina dx² (dx = ${f2(dx)}). Al hacer dx muy pequeño la esquina no cuenta: d(x²) = 2x·dx.`, items);
    }
    if (n === 3) return figCube(x, dx, "x", "dx", t, false, "El cubo crece en tres losas", `Si la arista x crece dx, el cubo gana tres losas x²·dx, tres vigas x·dx² y un cubito dx³ (dx = ${f2(dx)}). Al achicar dx solo cuentan las losas: d(x³) = 3x²·dx.`);
    if (n === 1) return scene("x crece dx", "Un segmento de longitud x que crece dx gana exactamente dx: d(x)/dx = 1.", [seg([0, 0], [x, 0], C.blue, { w: 5 }), seg([x, 0], [x + dx, 0], C.gold, { w: 5 }), txt([x + dx / 2, 0], "dx", C.gold, { dy: -12 })]);
    return tangentFig(fn(Pow(X, b.n), env), x, t, `Regla de la potencia`, `Para x^${S(b.n)} la pendiente de la tangente es ${S(b.n)}·x^(${S(b.n)} − 1): en dimensión n, el «hipercubo» crece por sus n caras.`);
  });
  function tangentFig(f, x0, t, title, cap) {
    const h = lerp(1.6, .002, ph(t, .05, .85)), y0 = f(x0), y1 = f(x0 + h), m = (y1 - y0) / h; if (bad(y0, y1, m)) return noFig(title, "Con los valores actuales de las letras esta figura no existe: mueve los deslizadores");
    const items = [{ k: "curve", f, c: C.blue, w: 2.2 }, seg([x0 - 2, y0 - 2 * m], [x0 + 2.5, y0 + 2.5 * m], C.green, { w: 2 }), { k: "pt", p: [x0, y0], c: C.ink, r: 4 }, { k: "pt", p: [x0 + h, y1], c: C.red, r: 4 }];
    slopeTri(f, x0, h, C.red, items, `Δy/Δx = ${f2(m)}`);
    return { title, cap: cap + ` Aquí la secante se acerca a la tangente al encoger Δx = ${f2(h)}.`, items, box: [x0 - 2.5, x0 + 2.5, Math.min(y0, y1) - 2.5, Math.max(y0, y1) + 2.5], axes: true, free: true };
  }
  reg("d-x", "d/dx(x) = 1", "segmento", (b, env, t) => scene("x crece dx", "Si x crece dx, la recta y = x sube exactamente dx: su pendiente es 1.", [seg([0, 0], [3, 3], C.blue, { w: 2.4 }), seg([1, 1], [2, 1], C.gold, { w: 2 }), seg([2, 1], [2, 2], C.green, { w: 3 }), txt([1.5, 1], "dx", C.gold, { dy: 12 }), txt([2, 1.5], "dx", C.green, { al: "left", dx: 6 })]));
  reg("d-const0", "Constante", "recta horizontal", () => scene("Lo que no cambia no crece", "La gráfica de una constante es una recta horizontal: su pendiente es 0.", [seg([-2, 1], [3, 1], C.blue, { w: 2.4 }), txt([.5, 1], "pendiente 0", C.blue, { dy: -12 })]));
  reg("d-sum", "Suma", "crecimientos apilados", (b, env, t) => {
    const parts = b.u.a.slice(0, 5), x = X0(env), dx = .4, items = []; let y = 0;
    parts.forEach((p, i) => { const g = fn(p, env), d = g(x + dx) - g(x); if (bad(d)) return; items.push(rect(i * .5 * (1 - ph(t, .2, .8)), y, .4, d, [C.blue, C.gold, C.green, C.violet, C.teal][i], { a: .4 }), txt([i * .5 * (1 - ph(t, .2, .8)) + .45, y + d / 2], `Δ(${S(p)}) = ${f2(d)}`, C.ink, { al: "left", f: 11 })); y += d; });
    items.push(txt([0, y], `Δ total = ${f2(y)}`, C.ink, { dy: -12, al: "left", b: 1 }));
    return scene("La suma crece lo que crecen sus partes", `Con dx = ${dx} en x = ${f2(x)}, el incremento de la suma es la pila de los incrementos de cada sumando: d(u + v) = du + dv.`, items);
  });
  reg("d-const", "Constante por función", "semejanza (Tales)", (b, env, t) => {
    const k = b.k ? evalN(b.k, env) : 2, g = fn(b.v || b.u, env), x0 = X0(env), dx = .8, d = g(x0 + dx) - g(x0), p = ph(t, .2, .8), kk = lerp(1, k, p);
    if (bad(k, d)) return noFig("Constante", "Con los valores actuales de las letras esta figura no existe");
    const items = [{ k: "poly", p: [[0, 0], [dx, 0], [dx, d]], c: C.blue, fill: AL(C.blue, .2), w: 1.6 }, { k: "poly", p: [[0, 0], [dx, 0], [dx, kk * d]], c: C.green, fill: AL(C.green, .2), w: 2 }];
    items.push(txt([dx, d / 2], `dv = ${f2(d)}`, C.blue, { al: "left", dx: 6, f: 11 }), txt([dx, kk * d], `k·dv = ${f2(kk * d)}`, C.green, { al: "left", dx: 6, f: 11 }));
    return scene("Una constante escala la pendiente", `Multiplicar por k = ${f2(k)} estira el triángulo de la pendiente en vertical: la pendiente queda multiplicada por k (semejanza de Tales).`, items);
  });
  reg("d-prod", "Regla del producto", "Leibniz: el rectángulo crece", (b, env, t) => {
    const x0 = X0(env), A = fn(b.a, env), Bf = fn(b.b, env), u = A(x0), v = Bf(x0), dx = lerp(.5, .03, ph(t, .1, .9)), du = A(x0 + dx) - u, dv = Bf(x0 + dx) - v;
    if (bad(u, v, du, dv)) return noFig("Producto", "Con los valores actuales esta figura no existe");
    const U = Math.abs(u), Vv = Math.abs(v), items = [rect(0, 0, U, Vv, C.blue), txt([U / 2, Vv / 2], `u·v`, C.blue, { b: 1 }), rect(U, 0, Math.abs(du), Vv, C.gold), rect(0, Vv, U, Math.abs(dv), C.green), rect(U, Vv, Math.abs(du), Math.abs(dv), C.red, { a: .5 })];
    items.push(txt([U + Math.abs(du) / 2, Vv / 2], "v·du", C.gold, { f: 11 }), txt([U / 2, Vv + Math.abs(dv) / 2], "u·dv", C.green, { f: 11 }), txt([U, 0], `u = ${S(b.a)} = ${f2(u)}`, C.ink, { dy: 14, al: "right", f: 11 }), txt([0, Vv], `v = ${S(b.b)} = ${f2(v)}`, C.ink, { dx: -6, al: "right", f: 11 }));
    return scene("Leibniz: el rectángulo u·v crece en dos tiras", `Cuando x crece dx = ${f2(dx)}, u crece du y v crece dv: el rectángulo gana la tira v·du, la tira u·dv y una esquina du·dv que se desvanece. Por eso d(uv) = v·du + u·dv.`, items);
  });
  reg("d-chain", "Regla de la cadena", "pendientes encadenadas", (b, env, t) => {
    const x0 = X0(env), g = fn(b.g, env), dx = .5, gx = g(x0), du = g(x0 + dx) - gx, outer = b.outer, Fo = u => evalN(outer, { ...env, u }), dy = Fo(gx + du) - Fo(gx);
    if (bad(gx, du, dy)) return noFig("Cadena", "Con los valores actuales esta figura no existe");
    const p = ph(t, .15, .85), items = [{ k: "poly", p: [[0, 0], [dx, 0], [dx, du]], c: C.blue, fill: AL(C.blue, .2), w: 1.8 }, txt([dx / 2, 0], "dx", C.blue, { dy: 12 }), txt([dx, du / 2], `du = ${f2(du)}`, C.blue, { al: "left", dx: 6, f: 11 })];
    const ox = dx + .6; items.push({ k: "poly", p: [[ox, 0], [ox + Math.abs(du) * p, 0], [ox + Math.abs(du) * p, dy * p]], c: C.green, fill: AL(C.green, .2), w: 1.8 }, txt([ox + Math.abs(du) / 2, 0], "du", C.green, { dy: 12 }), txt([ox + Math.abs(du), dy / 2], `dy = ${f2(dy)}`, C.green, { al: "left", dx: 6, f: 11 }));
    return scene("Regla de la cadena: dos triángulos de pendiente", `x mueve a u = ${S(b.g)} (primer triángulo, pendiente du/dx) y u mueve a y (segundo triángulo, pendiente dy/du). La pendiente total es el producto: dy/dx = (dy/du)·(du/dx).`, items);
  });
  reg("d-exp", "Exponencial", "subtangente constante", (b, env, t) => {
    const x0 = Math.min(X0(env), 1.5), f = Math.exp, y0 = f(x0), items = [{ k: "curve", f, c: C.blue, w: 2.2 }, seg([x0 - 1, 0], [x0 + .6, y0 * 1.6], C.green, { w: 2 }), seg([x0 - 1, 0], [x0, 0], C.red, { w: 4 }), seg([x0, 0], [x0, y0], C.gold, { w: 3 }), txt([x0 - .5, 0], "1", C.red, { dy: 12, b: 1 }), txt([x0, y0 / 2], `eˣ = ${f2(y0)}`, C.gold, { al: "left", dx: 6, f: 12 })];
    return { title: "eˣ: la tangente corta el eje una unidad atrás", cap: "La subtangente de la exponencial mide siempre 1: la pendiente (altura / 1) es igual a la altura. Por eso d/dx(eˣ) = eˣ.", items, box: [x0 - 2.5, x0 + 1.5, -.5, y0 * 1.8], axes: true, free: true };
  });
  function hyperArea(x, t, title, cap) {
    const f = v => 1 / v, X1 = Math.max(1.2, Math.min(x, 6)), q = ph(t, .1, .8), xe = lerp(1, X1, q), items = [];
    const pts = [[1, 0]]; for (let i = 0; i <= 40; i++) { const v = 1 + (xe - 1) * i / 40; pts.push([v, f(v)]); } pts.push([xe, 0]);
    items.push({ k: "poly", p: pts, c: null, fill: AL(C.green, .3) }, { k: "curve", f, c: C.blue, w: 2.2, x0: .2 }, rect(xe, 0, .25, f(xe), C.gold, { a: .5 }), txt([(1 + xe) / 2, .3], `ln ${f2(xe)} = ${f2(Math.log(xe))}`, C.green, { b: 1 }), txt([xe + .12, f(xe)], "1/x·dx", C.gold, { dy: -12, f: 11 }));
    return { title, cap, items, box: [0, X1 + 1, -.2, 2.2], axes: true, free: true };
  }
  reg("d-ln", "Logaritmo", "área bajo la hipérbola", (b, env, t) => hyperArea(X0(env) + 1.5, t, "ln x es el área bajo la hipérbola", "ln x es el área bajo y = 1/t entre 1 y x (Gregorio de San Vicente). Al avanzar dx se añade una franja de altura 1/x: la derivada de ln x es 1/x."));
  reg("i-recip", "∫dx/x", "área bajo la hipérbola", (b, env, t) => hyperArea(X0(env) + 1.5, t, "∫dx/x = ln|x|", "El área bajo la hipérbola y = 1/x desde 1 hasta x es ln x: las áreas entre 1–2, 2–4, 4–8 son iguales (crecimiento logarítmico)."));
  reg("d-trig", "Seno y coseno", "circunferencia unidad", (b, env, t) => {
    const th = lerp(.3, 1.1, ph(t, 0, 1)), dth = .25, P = [Math.cos(th), Math.sin(th)], Q2 = [Math.cos(th + dth), Math.sin(th + dth)];
    const items = [{ k: "circ", o: [0, 0], r: 1, c: C.ink, w: 1.6 }, seg([0, 0], P, C.violet, { w: 2 }), seg([P[0], 0], P, C.gold, { w: 3 }), seg([0, 0], [P[0], 0], C.blue, { w: 3 })];
    items.push(seg(P, [Q2[0], P[1]], C.blue, { w: 2 }), seg([Q2[0], P[1]], Q2, C.gold, { w: 2 }), seg(P, Q2, C.green, { w: 2.4 }), txt([P[0], P[1] / 2], "sen θ", C.gold, { al: "left", dx: 6, f: 11 }), txt([P[0] / 2, 0], "cos θ", C.blue, { dy: 12, f: 11 }));
    return { title: "La altura crece al ritmo del coseno", cap: "Al girar dθ, el punto avanza un arco dθ perpendicular al radio. El triángulo pequeño es semejante al grande (girado 90°): la altura sube cos θ·dθ y la abscisa baja sen θ·dθ.", items, box: [-1.3, 1.3, -1.2, 1.3], axes: true };
  });
  function riemann(f, a, b, t, title, cap, exact) {
    const n = Math.min(64, 2 ** (1 + Math.floor(ph(t, 0, .9) * 6))), w = (b - a) / n, items = [{ k: "curve", f, c: C.blue, w: 2.2 }]; let sum = 0;
    for (let i = 0; i < n; i++) { const xm = a + (i + .5) * w, y = f(xm); if (!isFinite(y)) continue; sum += y * w; items.push(rect(a + i * w, 0, w, y, y < 0 ? C.red : C.green, { a: .3, w: .6 })); }
    const ys = []; for (let i = 0; i <= 60; i++) { const y = f(a + (b - a) * i / 60); if (isFinite(y)) ys.push(y); }
    items.push(txt([(a + b) / 2, Math.max(...ys, 0)], `${n} rectángulos: ${f2(sum)}` + (exact !== undefined ? `   (exacto: ${f2(exact)})` : ""), C.ink, { dy: -14, b: 1 }));
    const pad = .2 * (b - a || 1);
    return { title, cap, items, box: [a - pad, b + pad, Math.min(0, ...ys) - .2, Math.max(0, ...ys) * 1.25 + .2], axes: true, free: true };
  }
  reg("i-pow", "Regla de la potencia", "Arquímedes", (b, env, t) => {
    const n = isNum(b.n) ? qnum(b.n.q) : 2, xe = 2, f = x => Math.pow(x, n);
    if (n === 1) return riemann(f, 0, xe, t, "∫x dx: el triángulo", "El área bajo y = x de 0 a x es un triángulo, la mitad del cuadrado: x²/2. Los rectángulos de Riemann la encierran cada vez mejor.", xe * xe / 2);
    if (n === 2) { const sc = riemann(f, 0, xe, t, "Arquímedes: la parábola encierra 1/3", "El área bajo y = x² de 0 a x es exactamente un tercio del rectángulo x·x² (Arquímedes, Cuadratura de la parábola): x³/3.", xe ** 3 / 3); sc.items.push(rect(0, 0, xe, xe * xe, C.gold, { nofill: 1, dash: [5, 4] })); return sc; }
    return riemann(f, 0, xe, t, `∫x^${f2(n)} dx`, "El área bajo la curva se aproxima con rectángulos cada vez más finos; su límite es x^(n+1)/(n+1).", Math.pow(xe, n + 1) / (n + 1));
  });
  reg("i-const0", "∫k dx", "rectángulo", (b, env, t) => { const k = evalN(b.u, env), x = 2 * ph(t, 0, .9) + .01; return scene("∫k dx = k·x: un rectángulo", "El área bajo una recta horizontal de altura k hasta x es el rectángulo k·x.", [rect(0, 0, x, k, C.green), txt([x / 2, k / 2], `${f2(k)}·${f2(x)} = ${f2(k * x)}`, C.green, { b: 1 })]); });
  reg("i-sum", "∫(u + v)", "áreas apiladas", (b, env, t) => riemann(fn(b.u, env), 0, 2, t, "Las áreas de los sumandos se suman", "Cada rectángulo de Riemann de la suma es la pila de los rectángulos de cada sumando: ∫(u + v) = ∫u + ∫v."));
  reg("i-const", "∫k·u", "alturas escaladas", (b, env, t) => riemann(fn(b.u, env), 0, 2, t, "Una constante escala todas las alturas", "Multiplicar la función por k multiplica la altura de cada rectángulo por k: el área queda multiplicada por k."));
  reg("i-expand", "Desarrollar", "Euclides II.1", (b, env, t) => riemann(fn(b.u, env), 0, 2, t, "Desarrollar para integrar", "El producto se desarrolla en una suma (Euclides II.1) y cada sumando se integra con la tabla."));
  reg("i-exp", "∫eˣ", "área hasta x = altura", (b, env, t) => riemann(Math.exp, -4, 1, t, "∫eˣ dx = eˣ", "El área bajo la exponencial desde muy a la izquierda hasta x es igual a su altura en x.", Math.exp(1) - Math.exp(-4)));
  reg("i-trig", "∫ seno y coseno", "área bajo la onda", (b, env, t) => riemann(b.f === "sin" ? Math.sin : Math.cos, 0, Math.PI / 2, t, b.f === "sin" ? "∫sen x dx = −cos x" : "∫cos x dx = sen x", "El área bajo un cuarto de onda del coseno es 1, la altura máxima del seno: la integral convierte abscisas en alturas.", 1));
  reg("i-barrow", "Regla de Barrow", "teorema fundamental", (b, env, t) => {
    const f = fn(b.f, env), F = fn(b.F, env), a = evalN(b.a, env), bb = evalN(b.b, env), exact = F(bb) - F(a);
    if (bad(a, bb, exact)) return noFig("Barrow", "Con los valores actuales esta figura no existe");
    const sc = riemann(f, a, bb, t, "Barrow: el área es F(b) − F(a)", `El área bajo f entre ${f2(a)} y ${f2(bb)} es lo que sube la primitiva F entre esos dos puntos: F(b) − F(a) = ${f2(exact)} (teorema fundamental del cálculo).`, exact);
    return sc;
  });

  reg("i-parts", "Por partes", "el rectángulo u·v en dos áreas", (b, env, t) => {
    const U = fn(b.uu, env), Vf = fn(b.vv, env), x0 = 0, x1 = lerp(.2, 1.5, ph(t, 0, .8)), pts = [];
    for (let i = 0; i <= 40; i++) { const x = x0 + (x1 - x0) * i / 40, p = [Vf(x), U(x)]; if (p.every(isFinite)) pts.push(p); }
    if (pts.length < 2) return noFig("Por partes", "Con los valores actuales esta figura no existe");
    const [v0, u0] = pts[0], [v1, u1] = pts[pts.length - 1];
    const items = [{ k: "poly", p: [[v0, 0], ...pts, [v1, 0]], c: null, fill: AL(C.green, .3) }, { k: "poly", p: [[0, u0], ...pts, [0, u1]], c: null, fill: AL(C.gold, .3) },
      { k: "poly", p: pts, close: false, c: C.blue, w: 2.4 }, rect(0, 0, v1, u1, C.ink, { nofill: 1, dash: [5, 4], w: 1.2 }),
      txt([(v0 + v1) / 2, Math.min(u0, u1) / 2], "∫u dv", C.green, { b: 1 }), txt([Math.min(v0, v1) / 2, (u0 + u1) / 2], "∫v du", C.gold, { b: 1, al: "right", dx: -4 }), txt([v1, u1], "u·v", C.ink, { dx: 8, al: "left" })];
    return { title: "Por partes: el rectángulo u·v en dos áreas", cap: `La curva de puntos (v, u), con u = ${S(b.uu)} y v = ${S(b.vv)}, parte el rectángulo u·v en el área bajo ella (∫u dv) y el área a su izquierda (∫v du). Por eso ∫u dv = u·v − ∫v du.`, items, box: bboxOf(items), axes: true };
  });
  const bboxOf = items => { const pts = items.flatMap(i => i.p || (i.k === "txt" ? [i.p] : [])); const b = boxOf(pts.filter(p => p && p.every && p.every(isFinite))); const m = .1 * Math.max(b[1] - b[0], b[3] - b[2], 1); return [b[0] - m, b[1] + m, b[2] - m, b[3] + m]; };

  /* ---------- paneles principales: tangente y área ---------- */
  function tanScene(s, env, t) {
    const f = fn(s.f, env), d = s.dres ? fn(s.dres, env) : (x => (f(x + 1e-5) - f(x - 1e-5)) / 2e-5), items = [{ k: "curve", f, c: C.blue, w: 2.2 }];
    const ys = []; for (let i = 0; i <= 80; i++) { const x = -4 + 8 * i / 80; [f(x), d(x)].forEach(y => isFinite(y) && ys.push(y)); } ys.sort((p, q) => p - q);
    const y0 = Math.min(ys[Math.floor(ys.length * .05)] ?? -1, 0), y1 = Math.max(ys[Math.ceil(ys.length * .95) - 1] ?? 1, 0);
    if (t < .4) { const sc = tangentFig(f, 1, t / .4, "", ""); items.push(...sc.items.slice(1)); }
    else {
      const x0 = lerp(-3.5, 3.5, ph(t, .4, 1)), yv = f(x0), m = d(x0);
      items.push({ k: "curve", f: d, c: C.green, w: 2.4, x1: x0 }, seg([x0 - 1, yv - m], [x0 + 1, yv + m], C.red, { w: 2 }), { k: "pt", p: [x0, yv], c: C.ink, r: 4 }, { k: "pt", p: [x0, m], c: C.green, r: 4.5, lab: `f′ = ${f2(m)}` });
      slopeTri(f, x0, 1, C.red, items, "");
    }
    return { title: "Tangente y función derivada", cap: `Azul: f(x) = ${S(s.f)}. Primero la secante se convierte en tangente al encoger Δx; después la tangente recorre la curva y su pendiente (triángulo de base 1) dibuja f′(x)${s.dres ? " = " + S(s.dres) : ""} en verde.`, items, box: [-4, 4, y0 - .1 * (y1 - y0 || 1), y1 + .1 * (y1 - y0 || 1)], axes: true, free: true };
  }
  function areaScene(s, env, t) {
    const f = fn(s.f, env);
    if (s.op === "defint") { const a = evalN(s.a, env), b = evalN(s.b, env), ex = s.F ? evalN(s.F, { ...env, x: b }) - evalN(s.F, { ...env, x: a }) : undefined; return riemann(f, a, b, t, "Área como límite de rectángulos (Riemann)", `Rectángulos cada vez más finos bajo f(x) = ${S(s.f)} entre ${f2(a)} y ${f2(b)}: su suma tiende al área exacta.`, ex); }
    const Fp = s.F ? fn(s.F, env) : null, xe = lerp(-.01, 3, ph(t, .05, .95)), items = [{ k: "curve", f, c: C.blue, w: 2.2 }];
    const pts = [[0, 0]]; for (let i = 0; i <= 50; i++) { const v = xe * i / 50; pts.push([v, f(v)]); } pts.push([xe, 0]);
    items.push({ k: "poly", p: pts, c: null, fill: AL(C.green, .3) });
    if (Fp) { const F0 = Fp(0); items.push({ k: "curve", f: x => Fp(x) - F0, c: C.gold, w: 2.4, x0: 0, x1: xe }, { k: "pt", p: [xe, Fp(xe) - F0], c: C.gold, r: 4.5, lab: `A(x) = ${f2(Fp(xe) - F0)}` }); }
    const ys = []; for (let i = 0; i <= 60; i++) { const v = -1 + 4.5 * i / 60; [f(v), Fp ? Fp(v) - Fp(0) : NaN].forEach(y => isFinite(y) && ys.push(y)); }
    return { title: "La función área crece a ritmo f(x)", cap: `El área verde bajo f desde 0 hasta x es la función A(x) (oro). Al avanzar dx se añade una franja f(x)·dx: A′(x) = f(x). Por eso integrar es buscar una primitiva${s.F ? ": F(x) = " + S(s.F) + " + C" : ""}.`, items, box: [-1, 3.5, Math.min(0, ...ys) - .3, Math.max(0, ...ys) + .3], axes: true, free: true };
  }
  const GEO = { deriv: "La derivada mide cómo crece una figura cuando x crece un poco: la pendiente de la tangente.", integ: "La integral mide un área: la primitiva es la función área, que crece en franjas f(x)·dx.", defint: "La integral definida es el área bajo la curva entre a y b: límite de sumas de rectángulos.", tan: "La tangente es el límite de las secantes; su pendiente en cada punto es la derivada." };
  return { steps, state, text, tex, verdict, parseLine, isLine, diff, primitive, tanScene, areaScene, GEO, isD, isI, find };
})();
