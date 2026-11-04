/* Geometría del Álgebra — operaciones entre funciones (fase 4).
   Cada operación tiene su construcción: la suma apila segmentos, el producto es un rectángulo,
   el cociente una pendiente (Tales), la composición un camino por la diagonal y = x, la inversa
   una simetría respecto de la diagonal y las transformaciones son traslaciones, afinidades y simetrías.
   Usa del visor: normalizeSrc, C, AL, fmt; de REGLAS.G las piezas de dibujo; de RESOLVER la inversa. */
"use strict";
const FUNC = (() => {
  const { Add, Sub, Mul, Div, Pow, Neg, Fn, sym, int, subs, evalN, str, order, expand, together, radsimp, symbols } = CAS;
  const { ph, lerp, txt, seg, rect } = REGLAS.G;
  const X = sym("x"), A_ = sym("a"), S = e => str(e);
  const P = s => CAS.parse(normalizeSrc(s));
  const clean = e => { const a = order(radsimp(together(e))), b = order(radsimp(expand(e))); return str(b).length < str(a).length ? b : a; };
  const defs = { f: CAS.parse("x^2"), g: CAS.parse("x+1") };

  const OPS = {
    sum: { lab: "f + g", name: "Suma", text: "f(x) + g(x)", expr: (f, g) => Add(f, g) },
    dif: { lab: "f − g", name: "Diferencia", text: "f(x) − g(x)", expr: (f, g) => Sub(f, g) },
    prod: { lab: "f · g", name: "Producto", text: "f(x)·g(x)", expr: (f, g) => Mul(f, g) },
    quot: { lab: "f / g", name: "Cociente", text: "f(x)/g(x)", expr: (f, g) => Div(f, g) },
    comp: { lab: "f ∘ g", name: "Composición", text: "f(g(x))", expr: (f, g) => subs(f, { x: g }) },
    compr: { lab: "g ∘ f", name: "Composición", text: "g(f(x))", expr: (f, g) => subs(g, { x: f }) },
    inv: { lab: "f⁻¹", name: "Inversa", text: "f⁻¹(x)", expr: null },
    shift: { lab: "f(x − a)", name: "Traslación horizontal", text: "f(x − a)", expr: f => subs(f, { x: Sub(X, A_) }) },
    vshift: { lab: "f(x) + a", name: "Traslación vertical", text: "f(x) + a", expr: f => Add(f, A_) },
    vscale: { lab: "a·f(x)", name: "Dilatación vertical", text: "a·f(x)", expr: f => Mul(A_, f) },
    hscale: { lab: "f(a·x)", name: "Contracción horizontal", text: "f(a·x)", expr: f => subs(f, { x: Mul(A_, X) }) },
    neg: { lab: "−f(x)", name: "Simetría respecto del eje x", text: "−f(x)", expr: f => Neg(f) },
    negx: { lab: "f(−x)", name: "Simetría respecto del eje y", text: "f(−x)", expr: f => subs(f, { x: Neg(X) }) },
    abs: { lab: "|f(x)|", name: "Valor absoluto", text: "|f(x)|", expr: f => Fn("abs", f) },
  };
  const GEO = {
    sum: "Para cada x, el segmento vertical g(x) se coloca encima del segmento f(x): sumar funciones es sumar segmentos (1D).",
    dif: "Para cada x, al segmento f(x) se le quita el segmento g(x): restar funciones es restar segmentos.",
    prod: "Para cada x, f(x) y g(x) son los lados de un rectángulo: el valor del producto es su área (2D).",
    quot: "f(x)/g(x) es la pendiente del triángulo de catetos g(x) (horizontal) y f(x) (vertical): una razón entre segmentos (Tales).",
    comp: "Componer es encadenar: de x se sube a g(x), se lleva a la diagonal y = x para usarlo como nueva entrada y se sube a f.",
    compr: "Componer es encadenar: de x se sube a f(x), se lleva a la diagonal y = x para usarlo como nueva entrada y se sube a g.",
    inv: "La inversa intercambia los papeles de x e y: su gráfica es la simétrica de la de f respecto de la diagonal y = x.",
    shift: "f(x − a) traslada la gráfica a unidades hacia la derecha: una traslación no cambia la forma.",
    vshift: "f(x) + a traslada la gráfica a unidades hacia arriba.",
    vscale: "a·f(x) estira la gráfica verticalmente en razón a: una afinidad (semejanza en una sola dirección).",
    hscale: "f(a·x) comprime la gráfica horizontalmente en razón a: afinidad en la dirección del eje x.",
    neg: "−f(x) refleja la gráfica en el eje x (simetría axial).",
    negx: "f(−x) refleja la gráfica en el eje y (simetría axial).",
    abs: "|f(x)|: lo que queda por debajo del eje x se refleja hacia arriba; lo de arriba no cambia.",
    expr: "Una combinación de funciones: su gráfica se obtiene punto a punto.",
    def: "Una función asigna a cada x un segmento vertical f(x): su gráfica es la curva que forman los extremos.",
  };

  /* f⁻¹ despejando y en x = f(y) con el resolutor */
  function inverse(f, env) {
    const steps = RESOLVER.solve({ eqs: [{ lhs: subs(f, { x: sym("y") }), rhs: X, rel: "=" }], join: null }, env, "y");
    const last = steps[steps.length - 1];
    if (!last) return null;
    const br = last.P.eqs.filter(e => e.lhs.t === "sym" && e.lhs.s === "y").map(e => order(e.rhs));
    const hasAp = e => !!e.ap || (e.a && e.a.some(hasAp)) || (e.t === "pow" && (hasAp(e.b) || hasAp(e.e))) || (e.t === "fn" && hasAp(e.x));
    if (!br.length || br.some(hasAp)) return null;
    return br;
  }
  /* sustituir llamadas f(…), g(…) por su expresión */
  function expandCalls(t) {
    for (let guard = 0; guard < 30; guard++) {
      const m = /(^|[^a-zA-Z])([fg])\(/.exec(t); if (!m) return t;
      const start = m.index + m[1].length, open = start + 1; let d = 0, end = -1;
      for (let i = open; i < t.length; i++) { if (t[i] === "(") d++; else if (t[i] === ")") { d--; if (!d) { end = i; break; } } }
      if (end < 0) throw Error("Falta un paréntesis");
      const inner = P(expandCalls(t.slice(open + 1, end)));
      t = t.slice(0, start) + "(" + S(subs(defs[m[2]], { x: inner })) + ")" + t.slice(end + 1);
    }
    return t;
  }
  const base = o => ({ kind: "func", rel: "=", v: "x", v0: "x", shift: 0, found: [], tag: null, notes: [], manual: false, desc: o.desc || "", rule: null, prop: null });
  function defState(name, expr, o = {}) {
    defs[name] = expr;
    return { ...base(o), op: "def", name, f: defs.f, g: defs.g, res: expr, params: symbols(expr).filter(s => s !== "x"), cas: { eqs: [{ lhs: sym(name), rhs: expr, rel: "=" }], join: null }, desc: o.desc || `Definir ${name}(x)` };
  }
  function opState(op, env = {}, o = {}) {
    const f = defs.f, g = defs.g; let res, branches = null;
    if (op === "inv") { branches = inverse(f, env); res = branches ? branches[0] : null; }
    else if (op === "expr") res = o.res;
    else res = OPS[op].expr(f, g);
    const raw = res ? order(res) : null;
    return { ...base(o), op, f, g, res: raw, branches, resClean: raw ? clean(raw) : null, params: raw ? symbols(raw).filter(s => s !== "x") : [],
      cas: raw ? { eqs: [{ lhs: sym("h"), rhs: raw, rel: "=" }], join: null } : null, desc: o.desc || (OPS[op] ? `${OPS[op].name}: h(x) = ${OPS[op].text}` : "Combinación de funciones") };
  }
  function text(s) {
    if (s.op === "def") return `${s.name}(x) = ${S(s.res)}`;
    if (s.op === "inv") return s.branches ? `f⁻¹(x) = ${s.branches.map(S).join("  o  ")}` : "f⁻¹(x): sin fórmula cerrada (se dibuja reflejando)";
    const head = OPS[s.op] ? `h(x) = ${OPS[s.op].text} = ` : "h(x) = ";
    const r = S(s.res), c = s.resClean ? S(s.resClean) : r;
    return head + r + (c !== r ? ` = ${c}` : "");
  }
  const tex = s => text(s).replace(/·/g, "\\cdot ").replace(/−/g, "-").replace(/⁻¹/g, "^{-1}").replace(/²/g, "^2").replace(/³/g, "^3");
  function isLine(t) { return /^\s*[fgh]\s*\(\s*x\s*\)\s*=/.test(t) || /^\s*f\s*(\^\s*-\s*1|⁻¹)/.test(t); }
  const PAT = [["sum", "f(x)+g(x)"], ["dif", "f(x)-g(x)"], ["prod", "f(x)*g(x)"], ["prod", "f(x)g(x)"], ["quot", "f(x)/g(x)"], ["comp", "f(g(x))"], ["compr", "g(f(x))"], ["shift", "f(x-a)"], ["vshift", "f(x)+a"], ["vscale", "a*f(x)"], ["vscale", "af(x)"], ["hscale", "f(a*x)"], ["hscale", "f(ax)"], ["neg", "-f(x)"], ["negx", "f(-x)"], ["abs", "|f(x)|"]];
  function fromLine(t, env) {
    const s = normalizeSrc(t);
    if (/^f(\^-1|⁻¹)/.test(s)) return opState("inv", env);
    const m = s.match(/^([fgh])\(x\)=(.+)$/); if (!m) return null;
    if (m[1] !== "h") return defState(m[1], P(expandCalls(m[2])), { desc: `Definir ${m[1]}(x)` });
    const hit = PAT.find(([, p]) => p === m[2]);
    if (hit) return opState(hit[0], env);
    return opState("expr", env, { res: P(expandCalls(m[2])), desc: "h(x) como combinación de f y g" });
  }
  function sameFn(a, b, env) {
    const ea = a.res, eb = b.res; if (!ea || !eb) return null;
    let n = 0; for (const v of [-2.3, -1.1, -.4, .3, .9, 1.7, 2.6]) { const p = evalN(ea, { ...env, x: v }), q = evalN(eb, { ...env, x: v }); if (!isFinite(p) || !isFinite(q)) continue; if (Math.abs(p - q) > 1e-7 * (1 + Math.abs(p))) return false; n++; }
    return n >= 3;
  }

  /* ---------- figuras ---------- */
  const fn = (e, env) => v => evalN(e, { ...env, x: v });
  function yRange(fs, x0, x1, extra = []) {
    const ys = [...extra]; for (let i = 0; i <= 120; i++) { const v = x0 + (x1 - x0) * i / 120; for (const f of fs) { const y = f(v); if (isFinite(y)) ys.push(y); } }
    ys.sort((p, q) => p - q); let a = ys[Math.floor(ys.length * .04)] ?? -1, b = ys[Math.ceil(ys.length * .96) - 1] ?? 1; a = Math.min(a, 0); b = Math.max(b, 0);
    const pd = .1 * (b - a || 2); return [a - pd, b + pd];
  }
  const curve = (f, c, w = 2.2, o = {}) => ({ k: "curve", f, c, w, ...o });
  function scene(s, env, t) {
    const F = fn(s.f, env), G = fn(s.g, env), H = s.res ? fn(s.res, env) : null, op = s.op;
    const x0 = -4, x1 = 4, items = [], a = env.a ?? 2;
    const title = OPS[op] ? `${OPS[op].name}: ${OPS[op].text}` : op === "def" ? `${s.name}(x) = ${S(s.res)}` : "h(x)";
    const cap = (GEO[op] || GEO.expr) + (s.params && s.params.includes("a") ? ` (a = ${fmt(a)}).` : "");
    const out = (box, o = {}) => ({ title, cap, items, box, axes: true, free: o.free ?? true });
    if (op === "def") { const [y0, y1] = yRange([F], x0, x1); const p = ph(t, 0, .9); items.push(curve(F, C.blue, 2.4, { x1: lerp(x0, x1, p) })); for (let v = -4; v <= 4; v += 1) { const y = F(v); if (isFinite(y) && v <= lerp(x0, x1, p)) items.push(seg([v, 0], [v, y], C.blue, { w: 1, dash: [3, 3] })); } return out([x0, x1, y0, y1]); }
    if (op === "sum" || op === "dif") {
      const [y0, y1] = yRange([F, G, H], x0, x1), p = ph(t, .1, .65), q = ph(t, .6, .95), sg = op === "sum" ? 1 : -1;
      items.push(curve(F, C.blue), curve(G, C.gold, 1.4, { dash: [6, 4] }));
      for (let v = -3.5; v <= 3.6; v += .875) { const fv = F(v), gv = G(v); if (!isFinite(fv) || !isFinite(gv)) continue; const b0 = lerp(0, fv, p); items.push(seg([v, b0], [v, b0 + sg * gv], C.gold, { w: 3 }), { k: "pt", p: [v, fv], c: C.blue, r: 3 }); if (p > .98) items.push({ k: "pt", p: [v, fv + sg * gv], c: C.green, r: 4 }); }
      if (q > 0) items.push(curve(H, C.green, 2.6, { x1: lerp(x0, x1, q) }));
      return out([x0, x1, y0, y1]);
    }
    if (op === "prod" || op === "quot") {
      const [y0, y1] = yRange([F, G, H], x0, x1), xv = lerp(-3.2, 3.2, ph(t, 0, 1)), fv = F(xv), gv = G(xv), hv = H(xv);
      items.push(curve(F, C.blue, 1.6), curve(G, C.gold, 1.6), curve(H, C.green, 2.6, { x1: xv }), seg([xv, 0], [xv, fv], C.blue, { w: 3 }), seg([xv + .06, 0], [xv + .06, gv], C.gold, { w: 3 }));
      if (isFinite(hv)) items.push({ k: "pt", p: [xv, hv], c: C.green, r: 5, lab: `h = ${fmt(hv)}` });
      // recuadro: rectángulo (producto) o triángulo (cociente) con los dos segmentos
      const W = x1 - x0, Hh = y1 - y0, ox = x0 + .04 * W, oy = y1 - .04 * Hh, m = Math.max(Math.abs(fv), Math.abs(gv), 1e-9), sx = .22 * W / m, sy = .3 * Hh / m;
      if (op === "prod") { items.push(rect(ox, oy - Math.abs(gv) * sy, Math.abs(fv) * sx, Math.abs(gv) * sy, fv * gv < 0 ? C.red : C.green, { a: .3 }), txt([ox + Math.abs(fv) * sx / 2, oy - Math.abs(gv) * sy], `${fmt(fv)} · ${fmt(gv)} = ${fmt(fv * gv)}`, C.green, { dy: 13, f: 12, b: 1 })); }
      else if (isFinite(hv)) { const bx = ox, by = oy - .3 * Hh; items.push({ k: "poly", p: [[bx, by], [bx + gv * sx, by], [bx + gv * sx, by + fv * sy]], c: C.green, fill: AL(C.green, .2), w: 1.8 }, txt([bx + gv * sx / 2, by], `g = ${fmt(gv)}`, C.gold, { dy: 13, f: 11 }), txt([bx + gv * sx, by + fv * sy / 2], `f = ${fmt(fv)}`, C.blue, { al: "left", dx: 6, f: 11 }), txt([bx, by + .32 * Hh], `pendiente = f/g = ${fmt(hv)}`, C.green, { al: "left", f: 12, b: 1 })); }
      return out([x0, x1, y0, y1]);
    }
    if (op === "comp" || op === "compr") {
      const [In, Out] = op === "comp" ? [G, F] : [F, G], L = 4.5, items2 = items;
      items2.push(seg([-L, -L], [L, L], C.muted, { w: 1, dash: [4, 4] }), curve(In, C.blue, 1.8), curve(Out, C.gold, 1.8));
      const pts = [-2, -1.4, -.8, -.2, .4, 1, 1.6, 2.2], k = Math.min(pts.length - 1, Math.floor(t * pts.length)), loc = t * pts.length - k;
      pts.forEach((xv, i) => {
        const a1 = In(xv), b1 = Out(a1); if (!isFinite(a1) || !isFinite(b1)) return;
        if (i < k || (i === k && loc > .95)) { items2.push({ k: "pt", p: [xv, b1], c: C.green, r: 4 }); return; }
        if (i > k) return;
        const segs = [[[xv, 0], [xv, a1], C.blue], [[xv, a1], [a1, a1], C.muted], [[a1, a1], [a1, b1], C.gold], [[a1, b1], [xv, b1], C.green]];
        segs.forEach(([p0, p1, c], j) => { const q = Math.max(0, Math.min(1, loc * 4 - j)); if (q > 0) items2.push(seg(p0, [lerp(p0[0], p1[0], q), lerp(p0[1], p1[1], q)], c, { w: 2.4, dash: c === C.muted ? [4, 4] : null })); });
        items2.push({ k: "pt", p: [xv, 0], c: C.ink, r: 3.5, lab: `x = ${fmt(xv)}`, dx: 0, dy: 15, al: "center" });
      });
      if (t > .97 && H) items2.push(curve(H, C.green, 2.6));
      const [y0, y1] = yRange([In, Out, H || (() => NaN)], -L, L);
      return out([-L, L, Math.max(y0, -L), Math.min(y1, L * 1.6)], { free: false });   // misma escala: la diagonal a 45°
    }
    if (op === "inv") {
      const L = 5, p = ph(t, .15, .85), items2 = items;
      items2.push(seg([-L, -L], [L, L], C.muted, { w: 1.2, dash: [5, 4] }), curve(F, C.blue, 2.2));
      const pts = []; for (let i = 0; i <= 160; i++) { const v = -L + 2 * L * i / 160, y = F(v); if (isFinite(y) && Math.abs(y) < 3 * L) pts.push([lerp(v, y, p), lerp(y, v, p)]); }
      for (let i = 1; i < pts.length; i++) items2.push(seg(pts[i - 1], pts[i], C.green, { w: 2.4 }));
      for (let v = -2; v <= 2.01; v += 1) { const y = F(v); if (isFinite(y) && Math.abs(y) < L) items2.push(seg([v, y], [y, v], C.muted, { w: .8, dash: [2, 3] }), { k: "pt", p: [lerp(v, y, p), lerp(y, v, p)], c: C.green, r: 3.5 }); }
      return { title, cap: cap + (s.branches && s.branches.length > 1 ? " f no es inyectiva: la reflexión da dos ramas (una por cada signo)." : s.branches ? "" : " No hay fórmula cerrada: la inversa existe como figura."), items: items2, box: [-L, L, -L, L], axes: true, free: false };
    }
    // transformaciones: la curva se mueve desde f hasta el resultado
    const p = ph(t, .1, .9), T = {
      shift: v => F(v - a * p), vshift: v => F(v) + a * p, vscale: v => lerp(1, a, p) * F(v), hscale: v => F(lerp(1, a, p) * v),
      neg: v => lerp(1, -1, p) * F(v), negx: v => F(lerp(1, -1, p) * v), abs: v => { const y = F(v); return y >= 0 ? y : lerp(y, -y, p); },
    }[op];
    const [y0, y1] = yRange([F, H || F], x0, x1);
    items.push(curve(F, C.blue, 1.4, { dash: [6, 4] }), curve(T || H || F, C.green, 2.6));
    if (op === "shift") items.push(seg([0, y0 * .9], [a * p, y0 * .9], C.red, { w: 3 }), txt([a * p / 2, y0 * .9], `a = ${fmt(a)}`, C.red, { dy: -11, f: 12 }));
    if (op === "vshift") items.push(seg([0, 0], [0, a * p], C.red, { w: 3 }));
    return out([x0, x1, y0, y1]);
  }
  function graphScene(s, env) {
    const F = fn(s.f, env), G = fn(s.g, env), H = s.res && s.op !== "def" ? fn(s.res, env) : null, items = [curve(F, C.blue), curve(G, C.gold)];
    if (s.op === "inv" && s.branches) s.branches.forEach((b, i) => items.push(curve(fn(b, env), i ? C.teal : C.green, 2.6)));
    else if (H) items.push(curve(H, C.green, 2.6));
    const [y0, y1] = yRange([F, G, H || F], -4, 4);
    return { title: "Las tres gráficas", cap: `Azul: f(x) = ${S(s.f)}. Oro: g(x) = ${S(s.g)}.` + (H || s.branches ? ` Verde: ${text(s)}.` : ""), items, box: [-4, 4, y0, y1], axes: true, free: true };
  }
  return { OPS, GEO, defs, opState, defState, fromLine, isLine, text, tex, scene, graphScene, sameFn, expandCalls };
})();
