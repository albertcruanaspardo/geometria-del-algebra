/* Geometría del Álgebra — reglas de transformación con su geometría.
   Cada regla es un teorema: un patrón algebraico, su reescritura y la figura que la demuestra.
   Las figuras se dibujan con los valores actuales de las letras y se animan con t ∈ [0, 1].
   Usa del visor: C, AL, boxOf, fmt, PRJ, DV, dot3. */
"use strict";
const REGLAS = (() => {
  const { Q, num, int, frac, sym, isNum, isOne, isZero, Add, Mul, Pow, Fn, Neg, Div, key, split, withCoef, termsOf,
    cadd, cmul, cpow, simplify, expand, evalN, str, qeq, qint, qnum, iroot, commonFactor, sqrtTerm, order, upoly, factorU, symbols, nd, cancel } = CAS;

  /* ---------- recorrido del árbol ---------- */
  const children = e => e.t === "add" || e.t === "mul" ? e.a : e.t === "pow" ? [e.b, e.e] : e.t === "fn" ? [e.x] : [];
  function* walk(e, path = []) { yield [e, path]; const ch = children(e); for (let i = 0; i < ch.length; i++) yield* walk(ch[i], path.concat(i)); }
  function replaceAt(e, path, sub) {
    if (!path.length) return sub;
    const [i, ...rest] = path;
    if (e.t === "add" || e.t === "mul") { const a = e.a.slice(); a[i] = replaceAt(a[i], rest, sub); return e.t === "add" ? Add(...a) : Mul(...a); }
    if (e.t === "pow") return i === 0 ? Pow(replaceAt(e.b, rest, sub), e.e) : Pow(e.b, replaceAt(e.e, rest, sub));
    if (e.t === "fn") return Fn(e.f, replaceAt(e.x, rest, sub));
    return e;
  }
  const isPowN = (e, k) => e.t === "pow" && isNum(e.e) && (k === undefined || qeq(e.e.q, typeof k === "object" ? k : Q(k)));
  const isDen = f => f.t === "pow" && isNum(f.e) && f.e.q.n < 0n;
  const hasDen = e => (e.t === "mul" && e.a.some(isDen)) || isDen(e) || (isNum(e) && e.q.d !== 1n);
  const S = e => str(e);

  /* ---------- utilidades de dibujo ---------- */
  const ease = t => t < .5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
  const ph = (t, a, b) => ease(Math.max(0, Math.min(1, (t - a) / (b - a))));
  const lerp = (a, b, t) => a + (b - a) * t;
  const rect = (x, y, w, h, col, o = {}) => ({ k: "poly", p: [[x, y], [x + w, y], [x + w, y + h], [x, y + h]], c: col, fill: o.nofill ? null : AL(col, o.a ?? .28), w: o.w ?? 1.6, dash: o.dash || null });
  const rot = (cx, cy, w, h, ang, col, o = {}) => { const c = Math.cos(ang), s = Math.sin(ang); return { k: "poly", p: [[-w / 2, -h / 2], [w / 2, -h / 2], [w / 2, h / 2], [-w / 2, h / 2]].map(([x, y]) => [cx + x * c - y * s, cy + x * s + y * c]), c: col, fill: AL(col, o.a ?? .3), w: 1.6 }; };
  const txt = (p, s, c, o = {}) => ({ k: "txt", p, s, c, ...o });
  const seg = (a, b, c, o = {}) => ({ k: "seg", a, b, c, w: o.w ?? 1.6, dash: o.dash || null });
  const PAL = () => [C.blue, C.gold, C.green, C.violet, C.teal, C.red];
  function bbox(items) {
    const pts = [];
    for (const it of items) {
      if (it.k === "poly") pts.push(...it.p); else if (it.k === "seg") pts.push(it.a, it.b); else if (it.k === "txt") pts.push(it.p);
      else if (it.k === "circ" || it.k === "ell") { const rx = it.r ?? it.rx, ry = it.r ?? it.ry; pts.push([it.o[0] - rx, it.o[1] - ry], [it.o[0] + rx, it.o[1] + ry]); }
    }
    const b = boxOf(pts), w = b[1] - b[0], h = b[3] - b[2], m = .06 * Math.max(w, h, 1e-9);
    return [b[0] - m, b[1] + m, b[2] - m, b[3] + m];
  }
  const scene = (title, cap, items, o = {}) => ({ title, cap, items, box: o.box || bbox(items), notes: o.notes || [] });
  const noFig = (title, why) => ({ title, cap: why, items: [], box: [-1, 1, -1, 1], notes: [why] });
  const f2 = v => fmt(v);
  const bad = (...vs) => vs.some(v => !isFinite(v));

  /* ---------- figuras reutilizables ---------- */
  // II.1: rectángulo de altura k partido en franjas k·tᵢ
  function figStrips(k, parts, t, rev, title, cap) {
    const K = k.v, H = Math.abs(K); if (bad(K, ...parts.map(p => p.v)) || H < 1e-9) return noFig(title, "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const sep = rev ? 1 - ph(t, .15, .8) : ph(t, .15, .8), tot = parts.reduce((s, p) => s + Math.abs(p.v), 0) || 1, g = .14 * Math.max(tot, H) * sep;
    const items = []; let x = 0;
    parts.forEach((p, i) => {
      const w = Math.abs(p.v), neg = p.v * K < 0, col = neg ? C.red : PAL()[i % 6];
      items.push(rect(x, 0, w, H, col, { dash: neg ? [5, 4] : null }), txt([x + w / 2, H / 2], S(cmul(k.e, p.e)) + " = " + f2(K * p.v), col, { b: 1, f: 12 }), txt([x + w / 2, 0], S(p.e), col, { dy: 13, f: 11 }));
      x += w + g;
    });
    items.push(txt([0, H / 2], S(k.e) + " = " + f2(K), C.ink, { al: "right", dx: -8, f: 12, b: 1 }));
    if (sep < .05) items.push(txt([x / 2, H], S(k.e) + "·(" + parts.map(p => S(p.e)).join(" + ") + ")", C.ink, { dy: -12, f: 12 }));
    return scene(title, cap, items);
  }
  // rectángulo de lados (Σaᵢ)×(Σbⱼ) partido en celdas aᵢ·bⱼ
  function figGrid(As, Bs, t, rev, title, cap, square) {
    if (bad(...As.map(a => a.v), ...Bs.map(b => b.v))) return noFig(title, "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
    const sep = rev ? 1 - ph(t, .15, .8) : ph(t, .15, .8);
    const W = As.reduce((s, a) => s + Math.abs(a.v), 0), H = Bs.reduce((s, b) => s + Math.abs(b.v), 0), g = .07 * Math.max(W, H) * sep;
    const items = []; let x = 0;
    As.forEach((a, i) => {
      const w = Math.abs(a.v); let y = 0;
      Bs.forEach((b, j) => {
        const h = Math.abs(b.v), neg = a.v * b.v < 0, col = neg ? C.red : square ? (i === j ? C.blue : C.gold) : PAL()[(i + 2 * j) % 6];
        items.push(rect(x + i * g, y + j * g, w, h, col, { dash: neg ? [5, 4] : null }));
        if (w * h > 0) items.push(txt([x + i * g + w / 2, y + j * g + h / 2], S(cmul(a.e, b.e)), col, { b: 1, f: 12 }));
        y += h;
      });
      items.push(txt([x + i * g + w / 2, 0], S(a.e), C.ink, { dy: 14, f: 11 }));
      x += w;
    });
    let y = 0; Bs.forEach((b, j) => { const h = Math.abs(b.v); items.push(txt([0, y + j * g + h / 2], S(b.e), C.ink, { al: "right", dx: -8, f: 11 })); y += h; });
    return scene(title, cap, items);
  }
  // II.7: (a − b)² = a² − 2ab + b²
  function figSqMinus(A, B, la, lb, t, rev, title, cap) {
    if (bad(A, B) || A <= 0 || B <= 0) return noFig(title, "Se necesita a > 0 y b > 0");
    const big = Math.max(A, B), sm = Math.min(A, B), D = big - sm;
    const p1 = rev ? 1 - ph(t, .55, .95) : ph(t, .1, .4), p2 = rev ? 1 - ph(t, .3, .6) : ph(t, .4, .7), p3 = rev ? 1 - ph(t, .05, .3) : ph(t, .7, .95);
    const items = [rect(0, 0, big, big, C.gold, { a: .12 }), txt([big / 2, big], `${la}² = ${f2(big * big)}`, C.gold, { dy: -12, f: 12, b: 1 })];
    items.push(rect(0, D, big, sm, C.red, { a: .25 * p1, dash: [5, 4], nofill: p1 < .02 }), rect(D, 0, sm, big, C.red, { a: .25 * p1, dash: [5, 4], nofill: p1 < .02 }));
    if (p1 > .3) items.push(txt([D / 2, D + sm / 2], `−${la}·${lb}`, C.red, { f: 12 }), txt([D + sm / 2, D / 2], `−${la}·${lb}`, C.red, { f: 12 }));
    items.push(rect(D, D, sm, sm, C.green, { a: .5 * p2, nofill: p2 < .02 }));
    if (p2 > .3) items.push(txt([D + sm / 2, D + sm / 2], `+${lb}²`, C.green, { f: 12, b: 1 }));
    items.push(rect(0, 0, D, D, C.blue, { a: .35 * p3, w: 2.4, nofill: p3 < .02 }));
    if (p3 > .3) items.push(txt([D / 2, D / 2], `(${la} − ${lb})² = ${f2(D * D)}`, C.blue, { f: 12, b: 1 }));
    return scene(title, cap, items);
  }
  // II.5: a² − b² = (a + b)(a − b): la tira se gira y se pega
  function figGnomon(U, W, la, lb, t, rev, title, cap) {
    if (bad(U, W) || U <= 0 || W <= 0 || Math.abs(U - W) < 1e-9) return noFig(title, "Se necesitan dos longitudes positivas distintas");
    if (U < W) [U, W] = [W, U];
    const D = U - W, p = rev ? 1 - ph(t, .2, .85) : ph(t, .2, .85);
    const items = [rect(0, 0, U, U, C.muted, { nofill: 1, dash: [4, 4], w: 1 }), rect(D, D, W, W, C.red, { a: .1, dash: [5, 4] }), txt([D + W / 2, D + W / 2], lb + "²", C.red, { f: 12 })];
    items.push(rect(0, 0, U, D, C.blue));
    const c0 = [D / 2, D + W / 2], c1 = [U + W / 2, D / 2];
    items.push(rot(lerp(c0[0], c1[0], p), lerp(c0[1], c1[1], p), D, W, p * Math.PI / 2, C.gold));
    items.push(txt([U / 2, -0.02], `${la} + ${lb}`, C.ink, { dy: 14, f: 12 }));
    if (p > .95) items.push(txt([(U + W) / 2, D / 2], `(${la} + ${lb})(${la} − ${lb}) = ${f2((U + W) * D)}`, C.ink, { f: 12, b: 1, dy: -2 }));
    else items.push(txt([U / 2, U], `gnomon = ${la}² − ${lb}² = ${f2(U * U - W * W)}`, C.ink, { dy: -12, f: 12 }));
    return scene(title, cap, items);
  }
  // cubo binómico en 8 piezas
  function figCube(A, B, la, lb, t, rev, title, cap) {
    if (bad(A, B) || A <= 0 || B <= 0) return noFig(title, "Se necesitan dos longitudes positivas");
    const E = .5 * (A + B) * (rev ? 1 - ph(t, .1, .85) : ph(t, .1, .85)), iv = [[0, A], [A, A + B]], parts = [], items = [];
    for (let i = 0; i < 2; i++) for (let j = 0; j < 2; j++) for (let k = 0; k < 2; k++) parts.push([i, j, k]);
    const depth = ([i, j, k]) => dot3([(iv[i][0] + iv[i][1]) / 2 + i * E, (iv[j][0] + iv[j][1]) / 2 + j * E, (iv[k][0] + iv[k][1]) / 2 + k * E], DV);
    parts.sort((a, b) => depth(a) - depth(b));
    const cols = [C.blue, C.gold, C.green, C.red];
    for (const [i, j, k] of parts) {
      const m = i + j + k, lo = [iv[i][0] + i * E, iv[j][0] + j * E, iv[k][0] + k * E], hi = [iv[i][1] + i * E, iv[j][1] + j * E, iv[k][1] + k * E];
      const V = (x, y, z) => PRJ([x ? hi[0] : lo[0], y ? hi[1] : lo[1], z ? hi[2] : lo[2]]), col = cols[m];
      items.push({ k: "poly", p: [V(1, 0, 0), V(1, 1, 0), V(1, 1, 1), V(1, 0, 1)], c: col, fill: AL(col, .42), w: 1.2 });
      items.push({ k: "poly", p: [V(0, 1, 0), V(1, 1, 0), V(1, 1, 1), V(0, 1, 1)], c: col, fill: AL(col, .28), w: 1.2 });
      items.push({ k: "poly", p: [V(0, 0, 1), V(1, 0, 1), V(1, 1, 1), V(0, 1, 1)], c: col, fill: AL(col, .55), w: 1.2 });
    }
    const b = bbox(items), lx = b[1], dy = (b[3] - b[2]) / 8;
    [[C.blue, `${la}³ = ${f2(A ** 3)}`], [C.gold, `3·${la}²${lb} = ${f2(3 * A * A * B)}`], [C.green, `3·${la}${lb}² = ${f2(3 * A * B * B)}`], [C.red, `${lb}³ = ${f2(B ** 3)}`]]
      .forEach(([c, s], n) => items.push(txt([lx, b[3] - n * dy], "■ " + s, c, { al: "left", f: 12 })));
    return scene(title, cap, items, { box: [b[0], b[1] + (b[1] - b[0]) * .9, b[2], b[3]] });
  }
  // II.6 y completar el cuadrado: x² + p·x → (x + p/2)² − (p/2)²
  function figComplete(X, P, lx, lp, t, title, cap) {
    if (bad(X, P) || X <= 0) return noFig(title, "Se necesita un valor positivo para " + lx);
    if (P < 0) return figSqMinus(X, -P / 2, lx, `|${lp}|/2`, t, false, title, cap);
    const h = P / 2, g = .25 * X, p1 = ph(t, 0, .22), p2 = ph(t, .25, .62), p3 = ph(t, .66, .92);
    const items = [rect(0, 0, X, X, C.blue), txt([X / 2, X / 2], lx + "²", C.blue, { b: 1, f: 14 })];
    const s1x = lerp(X + g, X, p2), s1 = rect(s1x, 0, h, X, C.gold);
    items.push(s1, txt([s1x + h / 2, X / 2], `(${lp}/2)·${lx}`, C.gold, { f: 11 }));
    const c0 = [X + g + h + .1 * X * p1 + h / 2, X / 2], c1 = [X / 2, X + h / 2];
    const cx = lerp(c0[0], c1[0], p2), cy = lerp(c0[1], c1[1], p2);
    items.push(rot(cx, cy, h, X, p2 * Math.PI / 2, C.gold), txt([cx, cy], `(${lp}/2)·${lx}`, C.gold, { f: 11 }));
    if (p2 > .98) {
      items.push(rect(X, X, h, h, C.red, { a: .35 * p3, dash: p3 < .5 ? [5, 4] : null, nofill: p3 < .05 }));
      items.push(txt([X + h / 2, X + h / 2], p3 < .5 ? "falta" : `(${lp}/2)²`, C.red, { f: 11, b: 1 }));
      if (p3 > .5) items.push(rect(0, 0, X + h, X + h, C.ink, { nofill: 1, w: 2.2 }), txt([(X + h) / 2, X + h], `(${lx} + ${lp}/2)² = ${f2((X + h) ** 2)}`, C.ink, { dy: -12, f: 12, b: 1 }));
    }
    if (p1 < .99 && p2 < .01) items.push(txt([X + g + h, X], `${lp}·${lx} partido en dos`, C.gold, { dy: -12, f: 11 }));
    return scene(title, cap, items);
  }
  // II.14 y VI.13: media proporcional
  function figMean(A, B, la, lb, t, title, cap) {
    if (bad(A, B) || A <= 0 || B <= 0) return noFig(title, "Se necesitan valores positivos");
    const h = Math.sqrt(A * B), r = (A + B) / 2, cx = (B - A) / 2, p = ph(t, 0, .45), q = ph(t, .45, .8), z = ph(t, .8, 1);
    const items = [seg([-A, 0], [B, 0], C.ink, { w: 1.4 }), seg([-A, -.05 * r], [0, -.05 * r], C.red, { w: 3 }), seg([0, -.05 * r], [B, -.05 * r], C.gold, { w: 3 }),
      txt([-A / 2, -.05 * r], `${la} = ${f2(A)}`, C.red, { dy: 13, f: 12 }), txt([B / 2, -.05 * r], `${lb} = ${f2(B)}`, C.gold, { dy: 13, f: 12 })];
    items.push({ k: "circ", o: [cx, 0], r, a0: Math.PI * (1 - p), a1: Math.PI, c: C.blue, w: 2 });
    if (q > 0) items.push(seg([0, 0], [0, h * q], C.green, { w: 3.2 }));
    if (q > .99) items.push(txt([0, h / 2], `√(${la}·${lb}) = ${f2(h)}`, C.green, { al: "left", dx: 8, f: 12, b: 1 }), seg([-A, 0], [0, h], C.muted, { dash: [4, 4], w: 1 }), seg([B, 0], [0, h], C.muted, { dash: [4, 4], w: 1 }));
    if (z > 0) {
      const y0 = -.3 * r - Math.max(h, A);
      items.push(rect(-A - .1 * r - h * 0, y0, A, B * 0 + Math.min(B, A * 3), C.gold, { a: .25 * z }));
      items.push(rect(.1 * r, y0, h, h, C.green, { a: .3 * z }));
      items.push(txt([-A - .1 * r + A / 2, y0], `rectángulo ${la}·${lb} = ${f2(A * B)}`, C.gold, { dy: 13, f: 11 }), txt([.1 * r + h / 2, y0], `cuadrado = ${f2(h * h)}`, C.green, { dy: 13, f: 11 }));
    }
    return scene(title, cap, items);
  }
  // potencias como dimensiones o como fichas
  function figDims(X, m, n, lb, t, title, cap) {
    const items = [], tot = m + n;
    if (bad(X) || X <= 0) return noFig(title, "Se necesita un valor positivo");
    if (Number.isInteger(m) && Number.isInteger(n) && m >= 1 && n >= 1 && tot <= 3) {
      const p = ph(t, .15, .85), o = [.45 * X, .3 * X];
      if (tot === 2) { items.push(seg([0, 0], [X, 0], C.blue, { w: 4 }), rect(0, 0, X, X * p, C.gold), txt([X / 2, 0], lb, C.blue, { dy: 14, f: 12 }), txt([X / 2, X * p / 2], p > .9 ? lb + "²" : "", C.gold, { b: 1, f: 14 })); }
      else {
        items.push(rect(0, 0, X, X, C.gold), txt([X / 2, X / 2], lb + "²", C.gold, { b: 1, f: 13 }));
        const d = [o[0] * p * 2, o[1] * p * 2];
        items.push({ k: "poly", p: [[0, X], [X, X], [X + d[0], X + d[1]], [d[0], X + d[1]]], c: C.green, fill: AL(C.green, .3), w: 1.4 }, { k: "poly", p: [[X, 0], [X + d[0], d[1]], [X + d[0], X + d[1]], [X, X]], c: C.green, fill: AL(C.green, .2), w: 1.4 });
        if (p > .9) items.push(txt([X + d[0] / 2, X + d[1] / 2], lb + "³", C.green, { b: 1, f: 14, dx: 10 }));
      }
      return scene(title, cap, items);
    }
    const sz = 1, p = ph(t, .2, .85);
    for (let i = 0; i < m; i++) items.push(rect(i * 1.15 * sz, 1.4 * (1 - p), sz, sz, C.blue), txt([i * 1.15 * sz + sz / 2, 1.4 * (1 - p) + sz / 2], lb, C.blue, { f: 12 }));
    for (let i = 0; i < n; i++) items.push(rect((m + i) * 1.15 * sz + .6 * (1 - p), 0, sz, sz, C.gold), txt([(m + i) * 1.15 * sz + .6 * (1 - p) + sz / 2, sz / 2], lb, C.gold, { f: 12 }));
    items.push(txt([(tot * 1.15) / 2, 0], `${m} + ${n} = ${tot} factores`, C.ink, { dy: 16, f: 12 }));
    return scene(title, cap, items);
  }
  // fracciones en el cuadrado unidad
  function figFracs(a, b, c, d, op, t, title, cap) {
    const ok = [a, b, c, d].every(v => Number.isInteger(v) && v > 0) && b <= 12 && d <= 12 && a <= b && c <= d;
    if (!ok) {
      const A = a / b, Bv = c / d; if (bad(A, Bv)) return noFig(title, "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
      const items = [seg([0, 0], [Math.abs(A), 0], C.blue, { w: 5 }), txt([Math.abs(A) / 2, 0], f2(A), C.blue, { dy: -12 })];
      if (op === "+") items.push(seg([Math.abs(A), 0], [Math.abs(A) + Math.abs(Bv), 0], C.gold, { w: 5 }), txt([Math.abs(A) + Math.abs(Bv) / 2, 0], f2(Bv), C.gold, { dy: -12 }), txt([(Math.abs(A) + Math.abs(Bv)) / 2, 0], "suma = " + f2(A + Bv), C.ink, { dy: 18, b: 1 }));
      else items.push(rect(0, -.2, Math.abs(A), -Math.abs(Bv), C.green), txt([Math.abs(A) / 2, -.2 - Math.abs(Bv) / 2], "producto = " + f2(A * Bv), C.green, { b: 1 }));
      return scene(title, cap, items);
    }
    const U = 4, items = [], p = ph(t, .2, .7), q = ph(t, .7, .95);
    const unit = ox => { items.push(rect(ox, 0, U, U, C.ink, { nofill: 1, w: 1.6 })); };
    if (op === "*") {
      unit(0);
      for (let i = 0; i < a; i++) items.push(rect(i * U / b, 0, U / b, U, C.blue, { a: .18, w: .6 }));
      for (let j = 0; j < c; j++) items.push(rect(0, j * U / d, U, U / d, C.gold, { a: .18 * p, w: .6 }));
      if (q > 0) for (let i = 0; i < a; i++) for (let j = 0; j < c; j++) items.push(rect(i * U / b, j * U / d, U / b, U / d, C.green, { a: .45 * q, w: .5 }));
      for (let i = 1; i < b; i++) items.push(seg([i * U / b, 0], [i * U / b, U], C.muted, { w: .6 }));
      for (let j = 1; j < d; j++) items.push(seg([0, j * U / d], [U, j * U / d], C.muted, { w: .6 * p }));
      items.push(txt([U / 2, 0], `${a}/${b}`, C.blue, { dy: 14 }), txt([0, U / 2], `${c}/${d}`, C.gold, { al: "right", dx: -8 }), txt([U / 2, U], `${a * c} de ${b * d} casillas = ${a * c}/${b * d}`, C.green, { dy: -12, b: 1 }));
      return scene(title, cap, items);
    }
    unit(0); unit(U * 1.25);
    for (let i = 0; i < a; i++) items.push(rect(i * U / b, 0, U / b, U, C.blue, { a: .3, w: .6 }));
    for (let j = 0; j < c; j++) items.push(rect(U * 1.25, j * U / d, U, U / d, C.gold, { a: .3, w: .6 }));
    for (const ox of [0, U * 1.25]) { for (let i = 1; i < b; i++) items.push(seg([ox + i * U / b, 0], [ox + i * U / b, U], C.muted, { w: ox ? .6 * p : .8 })); for (let j = 1; j < d; j++) items.push(seg([ox, j * U / d], [ox + U, j * U / d], C.muted, { w: ox ? .8 : .6 * p })); }
    items.push(txt([U / 2, 0], `${a}/${b} = ${a * d}/${b * d}`, C.blue, { dy: 14 }), txt([U * 1.75, 0], `${c}/${d} = ${c * b}/${b * d}`, C.gold, { dy: 14 }));
    if (q > 0) items.push(txt([U * 1.125, U], `${a * d} + ${c * b} = ${a * d + c * b} casillas de ${b * d}: ${a * d + c * b}/${b * d}`, C.green, { dy: -14, b: 1 }));
    return scene(title, cap, items);
  }

  /* ---------- REGLAS ---------- */
  const V = (e, env) => evalN(e, env);
  const R = [];
  const rule = r => (R.push(r), r);

  rule({ id: "arith", cat: "simp", name: "Calcular", ref: "aritmética de segmentos",
    match(e) {
      if (e.t === "add") { const ns = e.a.filter(isNum); return ns.length >= 2 ? { ns } : null; }
      if (e.t === "mul") { const ns = e.a.filter(f => isNum(f) || (isDen(f) && isNum(f.b))); return ns.length >= 2 && !(ns.length === 2 && isNum(ns[0]) && isDen(ns[1]) && e.a.length === 2 && cancel(e) === null) ? { ns } : null; }
      if (e.t === "pow" && isNum(e.b) && isNum(e.e) && isNum(cpow(e.b, e.e))) return { ns: [e] };
      return null;
    },
    apply(b, e) {
      if (e.t === "pow") return cpow(e.b, e.e);
      const v = e.t === "add" ? cadd(...b.ns) : cmul(...b.ns), rest = e.a.filter(f => !b.ns.includes(f));
      if (!rest.length) return v;
      return e.t === "add" ? (isZero(v) ? Add(...rest) : Add(...rest, v)) : (isOne(v) ? Mul(...rest) : Mul(v, ...rest));
    },
    fig(b, env, t, e) {
      const title = "Calcular con segmentos";
      if (e.t === "add") {
        const vs = b.ns.map(n => V(n, env)); let x = 0; const items = [];
        vs.forEach((v, i) => { const col = v < 0 ? C.red : PAL()[i % 6]; items.push(seg([x, i * .25], [x + v, i * .25], col, { w: 5 }), txt([x + v / 2, i * .25], f2(v), col, { dy: -11, f: 12 })); x += v; });
        items.push(seg([0, -.5], [x, -.5], C.ink, { w: 3 }), txt([x / 2, -.5], "suma = " + f2(x), C.ink, { dy: 14, b: 1 }));
        return scene(title, "Sumar es poner segmentos uno tras otro; restar es volver hacia atrás.", items);
      }
      const vs = (e.t === "pow" ? [V(e.b, env), V(e.e, env)] : b.ns.map(n => V(n, env)));
      if (e.t === "pow") { const [B0, n] = vs; if (Number.isInteger(B0) && B0 > 0 && B0 <= 12 && (n === 2 || n === 3)) { const items = []; for (let i = 0; i < B0; i++) for (let j = 0; j < B0; j++) items.push(rect(i, j, 1, 1, n === 2 ? C.blue : C.green, { a: .2, w: .7 })); items.push(txt([B0 / 2, 0], `${B0}${n === 2 ? "²" : "³"} = ${f2(B0 ** n)}${n === 3 ? ` (${B0} capas como esta)` : ""}`, C.ink, { dy: 15, b: 1 })); return scene("Potencia como figura", n === 2 ? "Un número al cuadrado es un cuadrado de casillas." : "Un cubo es una pila de capas cuadradas.", items); } return noFig("Potencia", f2(B0) + " elevado a " + f2(n) + " = " + f2(Math.pow(B0, n))); }
      if (vs.length === 2 && vs.every(v => Number.isInteger(v) && Math.abs(v) <= 15 && v !== 0)) { const [w, h] = vs.map(Math.abs), items = []; for (let i = 0; i < w; i++) for (let j = 0; j < h; j++) items.push(rect(i, j, 1, 1, vs[0] * vs[1] < 0 ? C.red : C.gold, { a: .25, w: .7 })); items.push(txt([w / 2, 0], f2(vs[0]), C.ink, { dy: 14 }), txt([0, h / 2], f2(vs[1]), C.ink, { al: "right", dx: -8 }), txt([w / 2, h], "producto = " + f2(vs[0] * vs[1]) + " casillas", C.ink, { dy: -12, b: 1 })); return scene("Producto como rectángulo", "Multiplicar dos números es construir el rectángulo de esos lados.", items); }
      return noFig(title, "Resultado: " + S(this.apply(b, e)));
    } });

  rule({ id: "collect", cat: "simp", name: "Reducir términos semejantes", ref: "Euclides II.1 (al revés)",
    match(e) {
      if (e.t !== "add") return null;
      const groups = new Map();
      e.a.forEach((t, i) => { const [q, r] = split(t); if (!r) return; const k = key(r); if (!groups.has(k)) groups.set(k, { r, idx: [] }); groups.get(k).idx.push(i); });
      for (const g of groups.values()) if (g.idx.length >= 2) return g;
      return null;
    },
    apply(b, e) {
      const sum = b.idx.reduce((s, i) => CAS.qadd(s, split(e.a[i])[0]), CAS.ZERO), merged = withCoef(sum, b.r), out = [];
      e.a.forEach((t, i) => { if (i === b.idx[0]) { if (sum.n !== 0n) out.push(merged); } else if (!b.idx.includes(i)) out.push(t); });
      return out.length ? Add(...out) : int(0);
    },
    fig(b, env, t, e) {
      const H = V(b.r, env), cs = b.idx.map(i => CAS.qnum(split(e.a[i])[0]));
      return figStrips({ e: b.r, v: H }, cs.map(c => ({ e: num(CAS.qFromNumber(c)), v: c })), t, true, "Reducir términos semejantes",
        `Los términos con la misma parte literal (${S(b.r)}) son rectángulos de la misma altura: se juntan en uno solo cuya base es la suma de coeficientes (II.1 leído al revés).`);
    } });

  rule({ id: "dist", cat: "exp", name: "Propiedad distributiva", ref: "Euclides II.1",
    match(e) {
      if (e.t !== "mul") return null;
      const adds = e.a.filter(f => f.t === "add"); if (adds.length !== 1) return null;
      const rest = e.a.filter(f => f !== adds[0]); if (!rest.length) return null;
      return { k: Mul(...rest), s: adds[0] };
    },
    apply: b => Add(...b.s.a.map(t => cmul(b.k, t))),
    fig: (b, env, t) => figStrips({ e: b.k, v: V(b.k, env) }, b.s.a.map(x => ({ e: x, v: V(x, env) })), t, false, "Euclides II.1: rectángulo partido en franjas",
      "Si un rectángulo tiene un lado partido en trozos, su área es la suma de los rectángulos parciales: k·(a + b + …) = k·a + k·b + …") });

  rule({ id: "prod", cat: "exp", name: "Producto de sumas", ref: "Euclides II.1 (rejilla)",
    match(e) { if (e.t !== "mul") return null; const adds = e.a.filter(f => f.t === "add"); return adds.length >= 2 ? { A: adds[0], B: adds[1], k: e.a.filter(f => f !== adds[0] && f !== adds[1]) } : null; },
    apply(b) { const terms = []; for (const x of b.A.a) for (const y of b.B.a) terms.push(cmul(...b.k, x, y)); const r = Add(...terms); return r; },
    fig: (b, env, t) => figGrid(b.A.a.map(x => ({ e: x, v: V(x, env) })), b.B.a.map(y => ({ e: y, v: V(y, env) })), t, false, "Producto de dos sumas: la rejilla",
      "El rectángulo de lados (a + b)·(c + d) se divide en una rejilla; cada casilla es un producto parcial. Las casillas rojas discontinuas son productos negativos.") });

  rule({ id: "sq", cat: "exp", name: "Cuadrado de una suma", ref: "Euclides II.4 / II.7",
    match: e => isPowN(e, 2) && e.b.t === "add" ? { s: e.b } : null,
    apply(b) {
      const ts = b.s.a;
      if (ts.length === 2) return Add(cpow(ts[0], int(2)), cmul(int(2), ts[0], ts[1]), cpow(ts[1], int(2)));
      const sq = ts.map(x => cpow(x, int(2))), cr = []; for (let i = 0; i < ts.length; i++) for (let j = i + 1; j < ts.length; j++) cr.push(cmul(int(2), ts[i], ts[j]));
      return Add(...sq, ...cr);
    },
    fig(b, env, t) {
      const ts = b.s.a, vs = ts.map(x => V(x, env));
      if (ts.length === 2 && vs[0] * vs[1] < 0) {
        const [pi, ni] = vs[0] > 0 ? [0, 1] : [1, 0];
        return figSqMinus(vs[pi], -vs[ni], S(ts[pi]), S(Neg(ts[ni])), t, false, "Euclides II.7: cuadrado de una diferencia",
          "Al cuadrado grande se le quitan dos rectángulos a·b; como la esquina b² se quitó dos veces, se devuelve una: (a − b)² = a² − 2ab + b².");
      }
      return figGrid(ts.map((x, i) => ({ e: x, v: vs[i] })), ts.map((x, i) => ({ e: x, v: vs[i] })), t, false, "Euclides II.4: el cuadrado partido",
        "El cuadrado de lado a + b se divide con dos cortes en los cuadrados a² y b² (azules) y dos rectángulos iguales a·b (oro): (a + b)² = a² + 2ab + b².", true);
    } });

  rule({ id: "diffsq", cat: "exp", name: "Suma por diferencia", ref: "Euclides II.5",
    match(e) {
      if (e.t !== "mul" || e.a.length !== 2) return null;
      const [A, B] = e.a; if (A.t !== "add" || B.t !== "add" || A.a.length !== 2 || B.a.length !== 2) return null;
      for (const i of [0, 1]) for (const j of [0, 1]) {
        const u = A.a[i], v = A.a[1 - i];
        if (key(cmul(u)) === key(cmul(B.a[j])) && key(cmul(Neg(v))) === key(cmul(B.a[1 - j]))) return { u, v: split(v)[0].n < 0n ? Neg(v) : v };
      }
      return null;
    },
    apply: b => Add(cpow(b.u, int(2)), Neg(cpow(b.v, int(2)))),
    fig: (b, env, t) => figGnomon(Math.abs(V(b.u, env)), Math.abs(V(b.v, env)), S(b.u), S(b.v), t, true, "Euclides II.5: suma por diferencia",
      "El rectángulo (a + b)(a − b) se recorta y la tira se gira hasta formar el gnomon: el cuadrado a² sin la esquina b². Por eso (a + b)(a − b) = a² − b².") });

  rule({ id: "cube", cat: "exp", name: "Cubo de una suma", ref: "cubo binómico",
    match: e => isPowN(e, 3) && e.b.t === "add" && e.b.a.length === 2 ? { a: e.b.a[0], b: e.b.a[1] } : null,
    apply: b => Add(cpow(b.a, int(3)), cmul(int(3), cpow(b.a, int(2)), b.b), cmul(int(3), b.a, cpow(b.b, int(2))), cpow(b.b, int(3))),
    fig: (b, env, t) => figCube(V(b.a, env), V(b.b, env), S(b.a), S(b.b), t, false, "El cubo binómico en 8 piezas",
      "El cubo de arista a + b se despieza en el cubo a³, el cubo b³, tres losas a²b y tres vigas ab²: (a + b)³ = a³ + 3a²b + 3ab² + b³.") });

  rule({ id: "pascal", cat: "exp", name: "Potencia de un binomio", ref: "triángulo de Pascal",
    match: e => isPowN(e) && qint(e.e.q) && e.e.q.n >= 4n && e.e.q.n <= 12n && e.b.t === "add" && e.b.a.length === 2 ? { a: e.b.a[0], b: e.b.a[1], n: Number(e.e.q.n) } : null,
    apply(b) { const ts = []; let c = 1n; for (let k = 0; k <= b.n; k++) { ts.push(cmul(num(Q(c)), cpow(b.a, int(b.n - k)), cpow(b.b, int(k)))); c = c * BigInt(b.n - k) / BigInt(k + 1); } return Add(...ts); },
    fig(b, env, t) {
      const items = [], rows = [[1]]; for (let i = 1; i <= b.n; i++) { const r = [1]; for (let k = 1; k < i; k++) r.push(rows[i - 1][k - 1] + rows[i - 1][k]); r.push(1); rows.push(r); }
      const shown = Math.ceil(ph(t, 0, .8) * (b.n + 1));
      rows.slice(0, shown).forEach((r, i) => r.forEach((c, k) => items.push(txt([k - i / 2, -i], String(c), i === b.n ? C.red : C.ink, { b: i === b.n, f: i === b.n ? 14 : 12 }))));
      return scene(`Triángulo de Pascal (n = ${b.n})`, `Cada coeficiente cuenta cuántas piezas iguales salen al despiezar el «hipercubo» de arista a + b en dimensión ${b.n}: en total 2^${b.n} piezas.`, items, { box: [-b.n / 2 - 1, b.n / 2 + 1, -b.n - 1, 1] });
    } });

  rule({ id: "powprod", cat: "exp", name: "Potencia de un producto", ref: "Euclides VI.20 (semejanza)",
    match: e => isPowN(e) && qint(e.e.q) && e.e.q.n >= 2n && e.b.t === "mul" ? { f: e.b.a, n: e.e } : null,
    apply: b => cmul(...b.f.map(f => cpow(f, b.n))),
    fig(b, env, t) {
      const n = Number(b.n.q.n), coef = b.f.find(isNum), k = coef ? Math.abs(CAS.qnum(coef.q)) : null, rest = Mul(...b.f.filter(f => f !== coef)), X = Math.abs(V(rest, env));
      if (k && Number.isInteger(k) && k >= 2 && k <= 8 && n === 2 && X > 0) {
        const items = [], p = ph(t, .15, .8);
        for (let i = 0; i < k; i++) for (let j = 0; j < k; j++) items.push(rect(i * X * (1 + .08 * p), j * X * (1 + .08 * p), X, X, (i + j) % 2 ? C.gold : C.blue, { a: .25 }));
        items.push(txt([k * X / 2, 0], `${k}·${S(rest)}`, C.ink, { dy: 14 }), txt([k * X / 2, k * X], `(${k}${S(rest)})² = ${k * k} cuadrados ${S(rest)}²`, C.ink, { dy: -12, b: 1 }));
        return scene("Semejanza: el área escala con el cuadrado", "Si el lado se multiplica por k, la figura semejante cabe k² veces (Euclides VI.20): (k·x)² = k²·x².", items);
      }
      return noFig("Potencia de un producto", "Cada factor se eleva a la potencia: las figuras semejantes escalan con el cuadrado (áreas) o el cubo (volúmenes).");
    } });

  rule({ id: "powmul", cat: "simp", name: "Producto de potencias", ref: "suma de dimensiones",
    match(e) {
      if (e.t !== "mul") return null;
      for (let i = 0; i < e.a.length; i++) for (let j = i + 1; j < e.a.length; j++) {
        const [b1, e1] = e.a[i].t === "pow" ? [e.a[i].b, e.a[i].e] : [e.a[i], int(1)], [b2, e2] = e.a[j].t === "pow" ? [e.a[j].b, e.a[j].e] : [e.a[j], int(1)];
        if (!isNum(b1) && key(b1) === key(b2) && isNum(e1) && isNum(e2)) return { i, j, base: b1, m: e1, n: e2 };
      }
      return null;
    },
    apply(b, e) { const out = e.a.filter((f, k) => k !== b.j); out[b.i] = cpow(b.base, cadd(b.m, b.n)); return Mul(...out); },
    fig: (b, env, t) => figDims(Math.abs(V(b.base, env)), CAS.qnum(b.m.q), CAS.qnum(b.n.q), S(b.base), t, "Producto de potencias: se suman las dimensiones",
      "Multiplicar potencias de la misma base suma los exponentes: un segmento por un cuadrado barre un cubo (x·x² = x³).") });

  rule({ id: "powpow", cat: "simp", name: "Potencia de una potencia", ref: "fichas",
    match: e => isPowN(e) && qint(e.e.q) && e.b.t === "pow" && isNum(e.b.e) && qint(e.b.e.q) ? { base: e.b.b, m: e.b.e, n: e.e } : null,
    apply: b => cpow(b.base, cmul(b.m, b.n)),
    fig(b, env, t) { const m = CAS.qnum(b.m.q), n = CAS.qnum(b.n.q); if (!(Number.isInteger(m) && Number.isInteger(n) && m > 0 && n > 0 && m * n <= 24)) return noFig("Potencia de una potencia", "Se multiplican los exponentes."); const items = [], p = ph(t, .2, .85); for (let g = 0; g < n; g++) for (let i = 0; i < m; i++) { const x = g * (m + .8 * (1 - p)) + i; items.push(rect(x, 0, .9, .9, PAL()[g % 6], { a: .3 }), txt([x + .45, .45], S(b.base), PAL()[g % 6], { f: 11 })); } items.push(txt([(m * n) / 2, 0], `${n} grupos de ${m} = ${m * n} factores`, C.ink, { dy: 15, b: 1 })); return scene("Potencia de una potencia", "Elevar a n una potencia m es repetir n grupos de m factores: (x^m)^n = x^(m·n).", items); } });

  rule({ id: "commonf", cat: "fac", name: "Sacar factor común", ref: "Euclides II.1 (al revés)",
    match(e) { if (e.t !== "add") return null; const [g, rest] = commonFactor(cadd(...e.a)); return isOne(g) || (isNum(g) && qeq(g.q, Q(-1))) ? null : { g, rest: order(rest) }; },
    apply: b => Mul(b.g, b.rest),
    fig: (b, env, t) => figStrips({ e: b.g, v: V(b.g, env) }, termsOf(b.rest).map(x => ({ e: x, v: V(x, env) })), t, true, "Factor común: las franjas se juntan",
      "Rectángulos con una altura común se unen en uno solo: a·b + a·c = a·(b + c) (Euclides II.1 leído al revés).") });

  rule({ id: "dsq", cat: "fac", name: "Diferencia de cuadrados", ref: "Euclides II.5 (al revés)",
    match(e) {
      if (e.t !== "add" || e.a.length !== 2) return null;
      const [p, n] = split(e.a[0])[0].n > 0n ? [e.a[0], e.a[1]] : [e.a[1], e.a[0]];
      if (split(p)[0].n < 0n || split(n)[0].n > 0n) return null;
      const A = sqrtTerm(cmul(p)), B = sqrtTerm(cmul(Neg(n))); return A && B ? { A, B } : null;
    },
    apply: b => Mul(Add(b.A, b.B), Add(b.A, Neg(b.B))),
    fig: (b, env, t) => figGnomon(Math.abs(V(b.A, env)), Math.abs(V(b.B, env)), S(b.A), S(b.B), t, false, "Euclides II.5: el gnomon se vuelve rectángulo",
      "El cuadrado a² sin la esquina b² es un gnomon; cortando su tira y girándola se forma el rectángulo (a + b)(a − b).") });

  rule({ id: "perfsq", cat: "fac", name: "Trinomio cuadrado perfecto", ref: "Euclides II.4 (al revés)",
    match(e) { if (e.t !== "add" || e.a.length !== 3) return null; const f = CAS.patternFactor(cadd(...e.a)); return f && f.t === "pow" ? { f } : null; },
    apply: b => b.f,
    fig(b, env, t) {
      const ts = b.f.b.a, vs = ts.map(x => V(x, env));
      if (vs[0] * vs[1] < 0) { const [pi, ni] = vs[0] > 0 ? [0, 1] : [1, 0]; return figSqMinus(vs[pi], -vs[ni], S(ts[pi]), S(Neg(ts[ni])), t, true, "Euclides II.7 al revés", "Las piezas a², −2ab y b² se recomponen en el cuadrado (a − b)²."); }
      return figGrid(ts.map((x, i) => ({ e: x, v: vs[i] })), ts.map((x, i) => ({ e: x, v: vs[i] })), t, true, "Euclides II.4 al revés: las piezas forman un cuadrado", "Dos cuadrados y dos rectángulos iguales encajan en el cuadrado de lado a + b.", true);
    } });

  rule({ id: "trinom", cat: "fac", name: "Factorizar el polinomio", ref: "raíces racionales (Ruffini)",
    match(e) { if (e.t !== "add") return null; const vs = symbols(e); if (vs.length !== 1) return null; const c = upoly(e, vs[0]); if (!c || c.length < 3) return null; const f = factorU(c, vs[0]); return f ? { f: order(f), v: vs[0] } : null; },
    apply: b => b.f,
    fig(b, env, t) {
      const fs = CAS.factorsOf(b.f).filter(f => f.t === "add" || (f.t === "pow" && f.b.t === "add"));
      const lin = fs.map(f => f.t === "pow" ? f.b : f);
      if (lin.length === 2 && lin.every(f => f.a.length === 2)) return figGrid(lin[0].a.map(x => ({ e: x, v: V(x, env) })), lin[1].a.map(y => ({ e: y, v: V(y, env) })), t, true, "Factorizar: las piezas forman un rectángulo", "Los términos del polinomio se recolocan como las casillas de un único rectángulo cuyos lados son los factores.");
      if (lin.length === 1 && b.f.t === "mul") { const k = Mul(...b.f.a.filter(f => f !== fs[0])); return figStrips({ e: k, v: V(k, env) }, lin[0].a.map(x => ({ e: x, v: V(x, env) })), t, true, "Factorizar: las franjas se juntan", "Los términos comparten un factor: sus rectángulos tienen la misma altura y se unen en uno solo."); }
      return noFig("Factorizar", "Factores: " + S(b.f));
    } });

  rule({ id: "complsq", cat: "exp", name: "Completar el cuadrado", ref: "Euclides II.6 (gnomon)",
    match(e) {
      if (e.t !== "add") return null;
      for (let i = 0; i < e.a.length; i++) {
        const t2 = e.a[i]; if (!(isPowN(t2, 2) && t2.b.t === "sym")) continue; const x = t2.b;
        for (let j = 0; j < e.a.length; j++) { if (j === i) continue; const [q, r] = split(e.a[j]); if (r && r.t === "sym" && r.s === x.s && q.n !== 0n) return { i, j, x, p: q }; }
      }
      return null;
    },
    apply(b, e) {
      const h = CAS.qdiv(b.p, Q(2)), sq = Pow(Add(b.x, num(h)), int(2)), comp = Neg(num(CAS.qmul(h, h)));
      const out = []; e.a.forEach((t, k) => { if (k === b.i) out.push(sq, comp); else if (k !== b.j) out.push(t); });
      return Add(...out);
    },
    fig: (b, env, t) => figComplete(V(b.x, env), CAS.qnum(b.p), b.x.s, CAS.qnum(b.p) < 0 ? fmt(-CAS.qnum(b.p)) : fmt(CAS.qnum(b.p)), t, "Completar el cuadrado (II.6)",
      "Los cuatro pasos: el rectángulo p·x se parte en dos tiras, se pegan a dos lados del cuadrado x² y queda un hueco (p/2)² en la esquina; se suma y se resta para cerrar el cuadrado.") });

  rule({ id: "fracadd", cat: "simp", name: "Sumar fracciones", ref: "denominador común",
    match(e) {
      if (e.t !== "add") return null;
      const idx = e.a.map((t, i) => hasDen(t) ? i : -1).filter(i => i >= 0); if (!idx.length) return null;
      const i = idx[0], j = idx.length > 1 ? idx[1] : e.a.findIndex((t, k) => k !== i);
      return j >= 0 ? { i, j } : null;
    },
    apply(b, e) {
      const [a, bb] = nd(e.a[b.i]), [c, d] = nd(e.a[b.j]);
      const same = key(simplify(bb)) === key(simplify(d));
      const top = same ? Add(a, c) : Add(cmul(a, d), cmul(c, bb)), den = same ? bb : cmul(bb, d);
      const f = Div(top, den), out = [];
      e.a.forEach((t, k) => { if (k === b.i) out.push(f); else if (k !== b.j) out.push(t); });
      return Add(...out);
    },
    fig(b, env, t, e) {
      const [a, bb] = nd(e.a[b.i]), [c, d] = nd(e.a[b.j]);
      return figFracs(V(a, env), V(bb, env), V(c, env), V(d, env), "+", t, "Sumar fracciones: la misma rejilla",
        "Para sumar partes de distinto tamaño se cortan las dos unidades con la misma rejilla (denominador común) y se cuentan las casillas.");
    } });

  rule({ id: "fracmul", cat: "simp", name: "Multiplicar fracciones", ref: "área en el cuadrado unidad",
    match(e) { if (e.t !== "mul") return null; const dens = e.a.filter(isDen), nums = e.a.filter(f => !isDen(f)); return dens.length >= 2 && nums.length >= 1 ? { dens, nums } : null; },
    apply: b => Div(cmul(...b.nums), cmul(...b.dens.map(f => cpow(f, int(-1))))),
    fig(b, env, t) {
      const ns = b.nums.map(f => V(f, env)), ds = b.dens.map(f => V(cpow(f, int(-1)), env));
      return figFracs(ns[0], ds[0], ns[1] ?? 1, ds[1], "*", t, "Multiplicar fracciones: rectángulo dentro de la unidad", "a/b · c/d es el rectángulo de lados a/b y c/d dentro del cuadrado unidad: ocupa a·c casillas de b·d.");
    } });

  rule({ id: "cancel", cat: "simp", name: "Simplificar la fracción", ref: "Tales (triángulos semejantes)",
    match(e) { if (!(e.t === "mul" && e.a.some(isDen)) && !isDen(e)) return null; const r = cancel(e); return r ? { r } : null; },
    apply: b => b.r,
    fig(b, env, t, e) {
      const [N, D] = nd(e), [n2, d2] = nd(b.r), A = Math.abs(V(D, env)), B = Math.abs(V(N, env)), a = Math.abs(V(d2, env)), bb = Math.abs(V(n2, env));
      if (bad(A, B, a, bb) || !A) return noFig("Simplificar", "Resultado: " + S(b.r));
      const p = ph(t, .15, .8), items = [{ k: "poly", p: [[0, 0], [A, 0], [A, B]], c: C.blue, fill: AL(C.blue, .15), w: 2 }, { k: "poly", p: [[0, 0], [a, 0], [a, bb]], c: C.gold, fill: AL(C.gold, .35 * p), w: 2 }];
      items.push(txt([A, B / 2], `${f2(B)}/${f2(A)}`, C.blue, { al: "left", dx: 8 }), txt([a, bb / 2], `${f2(bb)}/${f2(a)}`, C.gold, { al: "left", dx: 8 }));
      return scene("Simplificar: triángulos semejantes", "Dos fracciones son iguales cuando sus triángulos (base = denominador, altura = numerador) son semejantes: tienen la misma inclinación (Tales).", items);
    } });

  rule({ id: "sqrtsimp", cat: "simp", name: "Extraer factores de la raíz", ref: "disección de cuadrados",
    match(e) {
      if (!(isPowN(e, Q(1, 2)) && isNum(e.b) && qint(e.b.q) && e.b.q.n > 0n)) return null;
      let n = e.b.q.n, k = 1n; for (let p = 2n; p * p <= n && p < 10000n; p++) while (n % (p * p) === 0n) { n /= p * p; k *= p; }
      return k > 1n ? { k, m: n } : null;
    },
    apply: b => b.m === 1n ? num(Q(b.k)) : Mul(num(Q(b.k)), Pow(num(Q(b.m)), frac(1, 2))),
    fig(b, env, t) {
      const k = Number(b.k), m = Number(b.m), s = Math.sqrt(m), p = ph(t, .2, .85), items = [rect(0, 0, k * s, k * s, C.blue, { a: .12, w: 2 })];
      if (k <= 12) for (let i = 0; i < k; i++) for (let j = 0; j < k; j++) items.push(rect(i * s, j * s, s, s, (i + j) % 2 ? C.gold : C.green, { a: .3 * p, w: .8 }));
      items.push(txt([k * s / 2, 0], `lado = ${k}·√${m}`, C.ink, { dy: 14, b: 1 }), txt([k * s / 2, k * s], `área ${k * k * m} = ${k * k} cuadrados de área ${m}`, C.ink, { dy: -12 }));
      return scene("Extraer de la raíz: disección del cuadrado", `El cuadrado de área ${k * k * m} se parte en ${k}×${k} cuadrados de área ${m}; su lado mide ${k} veces √${m}.`, items);
    } });

  rule({ id: "sqrtmul", cat: "simp", name: "Producto de raíces", ref: "Euclides II.14 / VI.13",
    match(e) { if (e.t !== "mul") return null; const rs = e.a.map((f, i) => isPowN(f, Q(1, 2)) ? i : -1).filter(i => i >= 0); return rs.length >= 2 ? { i: rs[0], j: rs[1] } : null; },
    apply(b, e) { const out = e.a.filter((f, k) => k !== b.j); out[b.i] = Pow(cmul(e.a[b.i].b, e.a[b.j].b), frac(1, 2)); return Mul(...out); },
    fig: (b, env, t, e) => figMean(V(e.a[b.i].b, env), V(e.a[b.j].b, env), S(e.a[b.i].b), S(e.a[b.j].b), t, "√a·√b = √(ab): media proporcional",
      "Sobre a + b se traza la semicircunferencia; la perpendicular en el punto de unión mide √(ab) y su cuadrado iguala al rectángulo a·b (Euclides II.14 y VI.13).") });

  rule({ id: "sqrtsq", cat: "simp", name: "Cuadrado de una raíz", ref: "Euclides VI.13",
    match: e => isPowN(e, 2) && isPowN(e.b, Q(1, 2)) ? { a: e.b.b } : null,
    apply: b => b.a,
    fig: (b, env, t) => figMean(1, V(b.a, env), "1", S(b.a), t, "(√a)² = a", "√a es la media proporcional entre 1 y a; el cuadrado construido sobre ella tiene área a.") });

  /* reglas de ecuación completa */
  const EQ = [{
    id: "crossmul", cat: "simp", name: "Multiplicar en cruz", ref: "Euclides VI.16",
    match(eq) { if (eq.rel !== "=") return null; const [a, b] = nd(eq.lhs), [c, d] = nd(eq.rhs); return isOne(b) && isOne(d) ? null : { a, b, c, d }; },
    apply: (b, eq) => ({ lhs: order(cmul(b.a, b.d)), rhs: order(cmul(b.c, b.b)), rel: "=" }),
    fig(b, env, t) {
      const A = V(b.a, env), Bv = V(b.b, env), Cv = V(b.c, env), D = V(b.d, env);
      if (bad(A, Bv, Cv, D)) return noFig("Extremos y medios", "Con los valores actuales de las letras esta figura no existe (una raíz de un negativo o un denominador nulo): mueve los deslizadores de las letras");
      const p = ph(t, .2, .8), g = .25 * Math.max(Math.abs(A), Math.abs(D), Math.abs(Bv), Math.abs(Cv), 1);
      const items = [rect(0, 0, Math.abs(A), Math.abs(D), C.blue), txt([Math.abs(A) / 2, Math.abs(D) / 2], `extremos ${f2(A * D)}`, C.blue, { b: 1, f: 12 }),
        rect(Math.abs(A) + g, 0, Math.abs(Bv), Math.abs(Cv) * p, C.gold), txt([Math.abs(A) + g + Math.abs(Bv) / 2, Math.abs(Cv) * p / 2], `medios ${f2(Bv * Cv)}`, C.gold, { b: 1, f: 12 })];
      return scene("Euclides VI.16: extremos = medios", "a/b = c/d se cumple cuando el rectángulo de los extremos (a·d) iguala al de los medios (b·c). Con los valores actuales de las letras pueden no coincidir: la igualdad solo vale en las soluciones.", items);
    } }];

  /* ---------- búsqueda y aplicación ---------- */
  function find(P) {
    const out = [];
    P.eqs.forEach((eq, ei) => {
      for (const r of EQ) { let b = null; try { b = r.match(eq); } catch (e) { } if (b) { const after = r.apply(b, eq); out.push({ rule: r, ei, side: "eq", path: [], bind: b, before: eq, after, label: `${S(eq.lhs)} = ${S(eq.rhs)} → ${S(after.lhs)} = ${S(after.rhs)}` }); } }
      for (const side of ["lhs", "rhs"]) for (const [node, path] of walk(eq[side])) for (const r of R) {
        let b = null; try { b = r.match(node); } catch (e) { }
        if (!b) continue;
        let after; try { after = r.apply(b, node); if (r.cat !== "simp") after = order(after); } catch (e) { continue; }
        if (S(after) === S(node)) continue;
        out.push({ rule: r, ei, side, path, bind: b, before: node, after, label: `${S(node)} → ${S(after)}` });
      }
    });
    return out;
  }
  function apply(P, inst) {
    const eqs = P.eqs.map((eq, i) => {
      if (i !== inst.ei) return eq;
      if (inst.side === "eq") return inst.after;
      return { ...eq, [inst.side]: replaceAt(eq[inst.side], inst.path, inst.after) };
    });
    return { ...P, eqs };
  }
  const FIGS = [];                    // figuras de las operaciones del resolutor (resolver.js)
  const register = r => FIGS.push(r);
  const byId = id => R.find(r => r.id === id) || EQ.find(r => r.id === id) || FIGS.find(r => r.id === id);
  function figure(ref, env, t) {
    const r = byId(ref.id); if (!r) return null;
    try { const sc = r.fig(ref.bind, env, t, ref.before); sc.title = sc.title || r.name; return sc; } catch (e) { console.error(e); return noFig(r.name, "No se pudo dibujar esta regla con los valores actuales"); }
  }

  /* ---------- Libro II de Euclides: las 14 proposiciones ---------- */
  const E = (env, k, d) => env[k] ?? d;
  const PROPS = [
    { id: "II.1", eq: "a(b + c + d) = ab + ac + ad", name: "Rectángulo y segmento partido",
      fig: (env, t) => figStrips({ e: sym("a"), v: E(env, "a", 3) }, ["b", "c", "d"].map((s, i) => ({ e: sym(s), v: E(env, s, [2, 1.5, 1][i]) })), t, false, "Euclides II.1", "Si una de dos rectas se corta en partes, el rectángulo de ambas es igual a la suma de los rectángulos de la recta entera con cada parte.") },
    { id: "II.2", eq: "(a + b)a + (a + b)b = (a + b)^2", name: "Cuadrado como suma de dos rectángulos",
      fig: (env, t) => figStrips({ e: Add(sym("a"), sym("b")), v: E(env, "a", 3) + E(env, "b", 2) }, [{ e: sym("a"), v: E(env, "a", 3) }, { e: sym("b"), v: E(env, "b", 2) }], t, true, "Euclides II.2", "El cuadrado de una recta es igual a la suma de los rectángulos de la recta entera con cada una de sus partes.") },
    { id: "II.3", eq: "(a + b)a = a^2 + ab", name: "Rectángulo partido en cuadrado y rectángulo",
      fig: (env, t) => figStrips({ e: sym("a"), v: E(env, "a", 3) }, [{ e: sym("a"), v: E(env, "a", 3) }, { e: sym("b"), v: E(env, "b", 2) }], t, false, "Euclides II.3", "El rectángulo de la recta entera con una parte es igual al cuadrado de esa parte más el rectángulo de las dos partes.") },
    { id: "II.4", eq: "(a + b)^2 = a^2 + 2ab + b^2", name: "Cuadrado de una suma",
      fig: (env, t) => { const a = { e: sym("a"), v: E(env, "a", 3) }, b = { e: sym("b"), v: E(env, "b", 2) }; return figGrid([a, b], [a, b], t, false, "Euclides II.4", "El cuadrado de la recta entera es igual a los cuadrados de las partes más el doble del rectángulo de las partes.", true); } },
    { id: "II.5", eq: "ab + ((a - b)/2)^2 = ((a + b)/2)^2", name: "Segmento cortado en partes iguales y desiguales",
      fig: (env, t) => { const a = E(env, "a", 3), b = E(env, "b", 2); return figGnomon((a + b) / 2, Math.abs(a - b) / 2, "(a+b)/2", "(a−b)/2", t, true, "Euclides II.5", "Si una recta se corta en partes iguales y desiguales, el rectángulo de las desiguales más el cuadrado de la diferencia iguala al cuadrado de la mitad: el gnomon."); } },
    { id: "II.6", eq: "(2a + b)b + a^2 = (a + b)^2", name: "Segmento prolongado (completar el cuadrado)",
      fig: (env, t) => figComplete(E(env, "b", 2), 2 * E(env, "a", 3), "b", "2a", t, "Euclides II.6", "Si a una recta bisecada se le añade otra, el rectángulo de la entera con la añadida más el cuadrado de la mitad iguala al cuadrado de mitad más añadida: es completar el cuadrado.") },
    { id: "II.7", eq: "(a + b)^2 + a^2 = 2(a + b)a + b^2", name: "Cuadrado de una diferencia",
      fig: (env, t) => figSqMinus(E(env, "a", 3) + E(env, "b", 2), E(env, "a", 3), "(a+b)", "a", t, false, "Euclides II.7", "Los cuadrados de la entera y de una parte suman el doble rectángulo de ambas más el cuadrado de la otra parte: es (u − v)² = u² − 2uv + v².") },
    { id: "II.8", eq: "4(a + b)a + b^2 = (2a + b)^2", name: "Cuatro rectángulos y un cuadrado",
      fig(env, t) {
        const a = E(env, "a", 3), b = E(env, "b", 2), L = 2 * a + b, s = (1 - ph(t, .2, .85)) * .18 * L, items = [rect(0, 0, L, L, C.ink, { nofill: 1, dash: [4, 4], w: 1 })];
        const R4 = [[0, 0, a + b, a, -1, -1], [a + b, 0, a, a + b, 1, -1], [a, a + b, a + b, a, 1, 1], [0, a, a, a + b, -1, 1]];
        R4.forEach(([x, y, w, h, dx, dy], i) => items.push(rect(x + dx * s, y + dy * s, w, h, PAL()[i], { a: .3 }), txt([x + dx * s + w / 2, y + dy * s + h / 2], "a(a+b)", PAL()[i], { f: 11 })));
        items.push(rect(a, a, b, b, C.red, { a: .35 }), txt([a + b / 2, a + b / 2], "b²", C.red, { b: 1 }));
        return scene("Euclides II.8", "El cuadrado de lado 2a + b se compone de cuatro rectángulos a·(a + b) que giran alrededor de un cuadrado central b².", items);
      } },
    { id: "II.9", eq: "a^2 + b^2 = 2((a + b)/2)^2 + 2((a - b)/2)^2", name: "Suma de cuadrados de las partes",
      fig: (env, t) => figAreas([[E(env, "a", 3), "a"], [E(env, "b", 2), "b"]], [[(E(env, "a", 3) + E(env, "b", 2)) / 2, "(a+b)/2"], [(E(env, "a", 3) + E(env, "b", 2)) / 2, "(a+b)/2"], [Math.abs(E(env, "a", 3) - E(env, "b", 2)) / 2, "(a−b)/2"], [Math.abs(E(env, "a", 3) - E(env, "b", 2)) / 2, "(a−b)/2"]], t, "Euclides II.9", "Los cuadrados de las partes desiguales valen el doble de los cuadrados de la mitad y de la diferencia.") },
    { id: "II.10", eq: "(2a + b)^2 + b^2 = 2a^2 + 2(a + b)^2", name: "Segmento bisecado y prolongado",
      fig: (env, t) => { const a = E(env, "a", 3), b = E(env, "b", 2); return figAreas([[2 * a + b, "2a+b"], [b, "b"]], [[a, "a"], [a, "a"], [a + b, "a+b"], [a + b, "a+b"]], t, "Euclides II.10", "El cuadrado de la recta prolongada más el de la prolongación valen el doble de los cuadrados de la mitad y de mitad más prolongación."); } },
    { id: "II.11", eq: "x^2 + ax = a^2", name: "Sección áurea",
      fig(env, t) {
        const a = E(env, "a", 3), eb = a * Math.sqrt(5) / 2, x = eb - a / 2, p = ph(t, .1, .5), q = ph(t, .5, .9), items = [];
        items.push(rect(0, 0, a, a, C.muted, { nofill: 1, dash: [4, 4], w: 1 }), seg([0, a / 2], [a, 0], C.violet, { w: 1.4 }), { k: "pt", p: [0, a / 2], c: C.violet, r: 3.5, lab: "E", dx: -10, al: "right" });
        items.push({ k: "circ", o: [0, a / 2], r: eb, a0: -Math.atan2(a / 2, a), a1: -Math.atan2(a / 2, a) - p * (Math.PI / 2 - Math.atan2(a / 2, a) + Math.asin(Math.min(1, (eb - a / 2) / eb)) * 0 + .46), c: C.violet, w: 1, dash: [4, 4] });
        items.push(rect(0, -x, x, x, C.gold, { a: .35 * q, nofill: q < .05 }), rect(x, 0, a - x, a, C.blue, { a: .3 * q, nofill: q < .05 }));
        if (q > .5) items.push(txt([x / 2, -x / 2], `x² = ${f2(x * x)}`, C.gold, { b: 1, f: 12 }), txt([(a + x) / 2, a / 2], `a(a − x) = ${f2(a * (a - x))}`, C.blue, { b: 1, f: 12 }));
        items.push(txt([x / 2, 0], `x = ${f2(x)}`, C.gold, { dy: 12, f: 11 }), txt([a / 2, a], `a = ${f2(a)}`, C.ink, { dy: -12, f: 12 }));
        return scene("Euclides II.11: la sección áurea", "Cortar a en x y a − x de modo que el cuadrado de x iguale al rectángulo a·(a − x): x² + ax = a², x = a(√5 − 1)/2 (con E punto medio del lado y EF = EB).", items);
      } },
    { id: "II.12", eq: "c^2 = a^2 + b^2 + 2ap", name: "Triángulo obtusángulo", fig: (env, t) => figCos(E(env, "a", 3), E(env, "b", 2), 120, t, "Euclides II.12", "En el triángulo obtusángulo, el cuadrado del lado opuesto al ángulo obtuso excede a los cuadrados de los otros dos en el doble rectángulo a·p (p: proyección).") },
    { id: "II.13", eq: "c^2 = a^2 + b^2 - 2ap", name: "Triángulo acutángulo", fig: (env, t) => figCos(E(env, "a", 3), E(env, "b", 2), 60, t, "Euclides II.13", "En el triángulo acutángulo, el cuadrado del lado opuesto a un ángulo agudo es menor que los de los otros dos en el doble rectángulo a·p.") },
    { id: "II.14", eq: "x^2 = ab", name: "Cuadrar un rectángulo", fig: (env, t) => figMean(E(env, "a", 3), E(env, "b", 2), "a", "b", t, "Euclides II.14", "Construir un cuadrado igual a un rectángulo dado: su lado es la media proporcional entre los lados del rectángulo.") },
  ];
  function figAreas(left, right, t, title, cap) {
    const items = [], p = ph(t, .3, .9); let x = 0;
    left.forEach(([s, l], i) => { items.push(rect(x, 0, s, s, PAL()[i], { a: .3 }), txt([x + s / 2, s / 2], l + "²", PAL()[i], { f: 11, b: 1 })); x += s + .3; });
    const tl = left.reduce((s, [v]) => s + v * v, 0);
    items.push(txt([x / 2, 0], "suma = " + f2(tl), C.ink, { dy: 14, b: 1 }));
    let y = -Math.max(...right.map(r => r[0])) - 1.2, x2 = 0;
    right.forEach(([s, l], i) => { items.push(rect(x2, y, s, s, PAL()[(i + 2) % 6], { a: .3 * p, nofill: p < .05 }), txt([x2 + s / 2, y + s / 2], p > .3 ? l + "²" : "", PAL()[(i + 2) % 6], { f: 11 })); x2 += s + .3; });
    if (p > .5) items.push(txt([x2 / 2, y], "suma = " + f2(right.reduce((s, [v]) => s + v * v, 0)), C.ink, { dy: 14, b: 1 }));
    return scene(title, cap, items);
  }
  function figCos(a, b, deg, t, title, cap) {
    const th = deg * Math.PI / 180, A = [b * Math.cos(th), b * Math.sin(th)], Bp = [a, 0], c = Math.hypot(A[0] - a, A[1]), p = Math.abs(b * Math.cos(th)), q = ph(t, .3, .9);
    const items = [{ k: "poly", p: [[0, 0], Bp, A], c: C.ink, fill: AL(C.blue, .1), w: 2 }, seg([Math.min(0, A[0]), 0], [Math.max(a, A[0]), 0], C.muted, { dash: [4, 4], w: 1 }), seg(A, [A[0], 0], C.green, { dash: [4, 4] })];
    items.push(txt([a / 2, 0], `a = ${f2(a)}`, C.ink, { dy: 13 }), txt([A[0] / 2, A[1] / 2], `b = ${f2(b)}`, C.ink, { al: "right", dx: -6 }), txt([(A[0] + a) / 2, A[1] / 2], `c = ${f2(c)}`, C.red, { al: "left", dx: 6, b: 1 }));
    items.push(seg([0, -.12 * a], [A[0], -.12 * a], C.green, { w: 3 }), txt([A[0] / 2, -.12 * a], `p = ${f2(p)}`, C.green, { dy: 13 }));
    if (q > 0) items.push(rect(Math.min(0, A[0]) - 0, -a * .5 - .3 * a, a * q, -2 * p * 0 - p, C.gold, { a: .3 }), txt([a * q / 2, -a * .8 - p / 2], `a·p = ${f2(a * p)}`, C.gold, { f: 11 }));
    items.push(txt([a / 2, A[1]], `c² = ${f2(c * c)} = a² + b² ${deg > 90 ? "+" : "−"} 2ap`, C.ink, { dy: -16, b: 1 }));
    return scene(title, cap, items);
  }
  /* ---------- Libro VI: aplicación de áreas (VI.28 con defecto, VI.29 con exceso) ----------
     Sobre AB = a se aplica un rectángulo de área b al que le falta (VI.28) o le sobra (VI.29) un cuadrado.
     Algebraicamente x(a − x) = b y x(a + x) = b: las dos ecuaciones de segundo grado griegas.
     Euclides lo hace con paralelogramos semejantes a uno dado; aquí el paralelogramo es un cuadrado. */
  function figApply(a, B, t, exceso) {
    const title = exceso ? "Euclides VI.29: aplicar un área con exceso" : "Euclides VI.28: aplicar un área con defecto";
    if (bad(a, B) || a <= 0 || B <= 0) return noFig(title, "Se necesitan un segmento a > 0 y un área b > 0");
    const h = a / 2, items = [];
    const pt = (p, lab, col = C.ink, o = {}) => ({ k: "pt", p, c: col, r: 3.5, lab, ...o });
    if (!exceso) {
      if (B > h * h + 1e-12) return noFig(title, `Diorismo (VI.27): el área b = ${f2(B)} no puede superar el cuadrado de la mitad, (a/2)² = ${f2(h * h)}. De todos los rectángulos aplicados a a con defecto cuadrado, el mayor es el cuadrado de la mitad; aquí el discriminante es negativo y no hay solución real.`);
      const c = Math.sqrt(Math.max(0, h * h - B)), s = h + c, d = h - c;
      const p1 = ph(t, 0, .2), p2 = ph(t, .2, .45), p3 = ph(t, .5, .8), p4 = ph(t, .82, 1);
      items.push(rect(h, 0, h, h, C.muted, { nofill: 1, dash: [4, 4], w: 1 }));
      if (p1 > .4 && p4 === 0) items.push(txt([h * 1.5, h], `(a/2)² = ${f2(h * h)}`, C.muted, { dy: -12, f: 12 }));
      if (p2 > .02) {
        items.push(rect(h, d, c, c, C.red, { a: .3 * p2 * (1 - p4), dash: [5, 4] }), rect(h, 0, c, d, C.gold, { a: .32 * p2 }));
        if (p2 > .5 && p4 === 0 && c > .04 * a) items.push(txt([h + c / 2, d + c / 2], `c² = (a/2)² − b`, C.red, { f: 11 }));
        const cx = lerp((s + a) / 2, h / 2, p3), cy = lerp(h / 2, d / 2, p3);
        items.push(rot(cx, cy, d, h, p3 * Math.PI / 2, C.gold, { a: .32 * p2 }));
        if (p2 > .5 && p3 < .05) items.push(txt([(h + a) / 2, d / 2], `gnomon = b = ${f2(B)}`, C.ink, { f: 12, b: 1 }));
      }
      if (p4 > 0) {
        items.push(rect(s, 0, d, d, C.green, { a: .4 * p4 }), rect(0, 0, s, d, C.blue, { nofill: 1, w: 2.6 }));
        items.push(txt([s / 2, d], `x(a − x) = ${f2(s * d)} = b`, C.blue, { b: 1, f: 12, dy: -12 }), txt([s + d / 2, d / 2], "(a − x)²", C.green, { f: 11, b: 1 }), txt([s + d / 2, 0], "defecto", C.green, { dy: 15, f: 11 }));
        items.push(txt([s / 2, 0], `x = AS = ${f2(s)}`, C.blue, { dy: 15, f: 12 }), pt([s, 0], "S", C.blue, { dy: 12 }));
      }
      items.push(seg([0, 0], [a, 0], C.ink, { w: 2.4 }), pt([0, 0], "A", C.ink, { al: "right", dx: -8 }), pt([h, 0], "E", C.violet), pt([a, 0], "B"));
      return scene(title, `x(a − x) = b: sobre EB, el cuadrado de la mitad menos c² = (a/2)² − b deja un gnomon de área b (II.5); su tira gira y forma el rectángulo AS·SB con defecto cuadrado. x = a/2 + c = ${f2(s)} (o a/2 − c = ${f2(d)}).`, items);
    }
    const r = Math.sqrt(B), c = Math.hypot(h, r), x = c - h, D = a + x, th = Math.atan2(r, h);
    const p1 = ph(t, 0, .25), p2 = ph(t, .27, .45), p3 = ph(t, .5, .8), p4 = ph(t, .82, 1);
    items.push({ k: "poly", p: [[h, 0], [a, 0], [a, -r]], c: C.violet, fill: AL(C.violet, .12), w: 1.4 }, txt([a, -r / 2], `√b = ${f2(r)}`, C.violet, { al: "left", dx: 7, f: 11 }),
      txt([(h + a) / 2, -r / 2], "I.47", C.violet, { al: "right", dx: -8, f: 11, b: 1 }));
    if (p1 > .01) items.push({ k: "circ", o: [h, 0], r: c, a0: -th, a1: -th + th * p1, c: C.violet, w: 1.2, dash: [4, 4] });
    items.push(seg([a, 0], [a + x * p1, 0], C.ink, { w: 2.4, dash: [6, 4] }));
    if (p2 > .02) {
      items.push(rect(h, 0, c, c, C.ink, { nofill: 1, dash: [4, 4], w: 1 }), rect(h, x, h, h, C.red, { a: .28 * p2 * (1 - p4), dash: [5, 4] }), rect(h, 0, c, x, C.gold, { a: .32 * p2 }));
      if (p2 > .5 && p4 === 0) items.push(txt([h * 1.5, x + h / 2], `(a/2)²`, C.red, { f: 11 }), txt([h + c / 2, c], `c² = (a/2)² + b = ${f2(c * c)}`, C.ink, { dy: -12, f: 12 }));
      const cx = lerp(a + x / 2, h / 2, p3), cy = lerp(x + h / 2, x / 2, p3);
      items.push(rot(cx, cy, x, h, p3 * Math.PI / 2, C.gold, { a: .32 * p2 }));
      if (p2 > .5 && p3 < .05) items.push(txt([a + x / 2, x + h / 2], `gnomon = b`, C.ink, { al: "left", dx: x * 0 + 6, f: 12, b: 1 }));
    }
    if (p4 > 0) {
      items.push(rect(a, 0, x, x, C.green, { a: .4 * p4 }), rect(0, 0, D, x, C.blue, { nofill: 1, w: 2.6 }));
      items.push(txt([D / 2, x], `x(a + x) = ${f2(x * D)} = b`, C.blue, { b: 1, f: 12, dy: -12 }), txt([a + x / 2, x / 2], "x²", C.green, { f: 11, b: 1 }));
      items.push(txt([D, x / 2], `x = BD = ${f2(x)}`, C.blue, { al: "left", dx: 10, f: 12 }));
    }
    items.push(seg([0, 0], [a, 0], C.ink, { w: 2.4 }), { k: "pt", p: [0, 0], c: C.ink, r: 3.5, lab: "A", al: "right", dx: -8 }, { k: "pt", p: [h, 0], c: C.violet, r: 3.5, lab: "E" }, { k: "pt", p: [a, 0], c: C.ink, r: 3.5, lab: "B" });
    if (p1 > .98) items.push({ k: "pt", p: [D, 0], c: C.blue, r: 3.5, lab: "D" });
    const bx = bbox(items.filter(i => i.k !== "circ").concat([seg([0, -r], [h + c, c], null)]));   // el arco no debe contar como círculo entero
    return scene(title, `x(a + x) = b: c = √((a/2)² + b) por I.47; el cuadrado c² menos el de la mitad deja un gnomon de área b (II.6), que forma el rectángulo AD·BD con exceso x². x = c − a/2 = ${f2(x)}; siempre hay solución.`, items, { box: bx });
  }

  /* ---------- Libro I: I.47, el teorema de Pitágoras (el «molino» de Euclides) ----------
     Cada cuadrado de un cateto se cizalla (misma base, misma altura: I.35–I.41) hasta caber
     en uno de los dos rectángulos en que la altura parte el cuadrado de la hipotenusa. */
  function figPyth(a, b, t) {
    const title = "Euclides I.47: el teorema de Pitágoras";
    if (bad(a, b) || a <= 0 || b <= 0) return noFig(title, "Se necesitan dos catetos positivos");
    const c = Math.hypot(a, b), Hx = b * b / c, hh = a * b / c, A = [0, 0], Bp = [c, 0], Cp = [Hx, hh], Hp = [Hx, 0];
    const add = (p, q, k = 1) => [p[0] + k * q[0], p[1] + k * q[1]];
    const u = [Hx / b, hh / b], n1 = [-u[1], u[0]], v = [(Hx - c) / a, hh / a], n2 = [v[1], -v[0]];
    const up = [0, c], dn = [0, -c];
    // las cuatro etapas de cada cuadrado: cuadrado → paralelogramo → rectángulo → bajado a su sitio
    const sb = [[A, Cp, add(Cp, n1, b), add(A, n1, b)], [A, Cp, add(Cp, up), up], [A, Hp, add(Hp, up), up]];
    const sa = [[Bp, Cp, add(Cp, n2, a), add(Bp, n2, a)], [Bp, Cp, add(Cp, up), add(Bp, up)], [Bp, Hp, add(Hp, up), add(Bp, up)]];
    sb.push(sb[2].map(p => add(p, dn))); sa.push(sa[2].map(p => add(p, dn)));
    const s = [ph(t, .12, .38), ph(t, .42, .66), ph(t, .7, .92)], k = s.findIndex(x => x < 1), st = k < 0 ? 2 : k, f = k < 0 ? 1 : s[k];
    const at = S4 => S4[st].map((p, i) => [lerp(p[0], S4[st + 1][i][0], f), lerp(p[1], S4[st + 1][i][1], f)]);
    const poly = (p, col, o = {}) => ({ k: "poly", p, c: col, fill: o.nofill ? null : AL(col, o.a ?? .3), w: o.w ?? 1.6, dash: o.dash || null });
    const cen = P => [P.reduce((x, p) => x + p[0], 0) / 4, P.reduce((y, p) => y + p[1], 0) / 4];
    const items = [poly(sb[0], C.gold, { nofill: 1, dash: [4, 4], w: 1 }), poly(sa[0], C.blue, { nofill: 1, dash: [4, 4], w: 1 }), rect(0, -c, c, c, C.ink, { nofill: 1, w: 1.4 })];
    if (s[1] > .5) items.push(seg(Cp, [Hx, -c], C.green, { dash: [5, 4], w: 1.2 }));
    const PB = at(sb), PA = at(sa);
    items.push(poly(PB, C.gold), poly(PA, C.blue));
    items.push(txt(cen(PB), "b²", C.gold, { b: 1, f: 12 }), txt(cen(PA), "a²", C.blue, { b: 1, f: 12 }));
    items.push({ k: "poly", p: [A, Bp, Cp], c: C.ink, fill: AL(C.ink, .08), w: 2.2 });
    items.push(txt([Hx / 2, hh / 2], "b", C.ink, { al: "right", dx: -8, f: 12, it: 1 }), txt([(Hx + c) / 2, hh / 2], "a", C.ink, { al: "left", dx: 8, f: 12, it: 1 }), txt([c / 2, 0], "x", C.ink, { dy: 12, f: 12, it: 1 }));
    if (s[2] > .99) items.push(txt([c / 2, -c], `x² = a² + b² = ${f2(a * a)} + ${f2(b * b)} = ${f2(c * c)},  x = ${f2(c)}`, C.ink, { dy: 16, b: 1, f: 12 }));
    else items.push(txt([c / 2, -c / 2], `x² = ${f2(c * c)}`, C.muted, { f: 12 }));
    return scene(title, `La altura parte el cuadrado de la hipotenusa en dos rectángulos; cada cuadrado de un cateto se cizalla sin cambiar de área (I.35–41) hasta llenar el suyo: a² + b² = x², x = ${f2(c)}.`, items);
  }
  /* ---------- I.43: los complementos en torno a la diagonal son iguales ---------- */
  function figComplements(a, b, c, t) {
    const title = "Euclides I.43: los complementos";
    if (bad(a, b, c) || a <= 0 || b <= 0) return noFig(title, "Se necesitan a > 0 y b > 0");
    if (c <= 0 || c >= a) return noFig(title, `K debe caer dentro de la diagonal: 0 < c < a (ahora c = ${f2(c)}, a = ${f2(a)})`);
    const u = lerp(.85 * a, c, ph(t, 0, .75)), v = b * u / a, q = ph(t, .2, .5);
    const items = [rect(0, 0, u, v, C.muted, { a: .1 }), rect(u, v, a - u, b - v, C.muted, { a: .1 }),
      rect(0, v, u, b - v, C.gold, { a: .35 * q }), rect(u, 0, a - u, v, C.blue, { a: .35 * q }),
      rect(0, 0, a, b, C.ink, { nofill: 1, w: 2 }), seg([0, 0], [a, b], C.violet, { w: 1.6 }), { k: "pt", p: [u, v], c: C.violet, r: 4, lab: "K", dx: 8, dy: 10 }];
    if (q > .5) items.push(txt([u / 2, (v + b) / 2], f2(u * (b - v)), C.gold, { b: 1, f: 12 }), txt([(u + a) / 2, v / 2], f2((a - u) * v), C.blue, { b: 1, f: 12 }));
    items.push(txt([a / 2, 0], `a = ${f2(a)}`, C.ink, { dy: 14, f: 12 }), txt([0, b / 2], `b = ${f2(b)}`, C.ink, { al: "right", dx: -8, f: 12 }), txt([u, 0], `c = ${f2(u)}`, C.violet, { dy: 28, f: 11 }));
    return scene(title, "K recorre la diagonal y los dos complementos (oro y azul) miden siempre lo mismo: c·(b − bc/a) = (a − c)·bc/a. Es la llave de I.44 y de la regla de tres.", items);
  }
  /* ---------- I.44: aplicar a un segmento un rectángulo igual a uno dado: a·x = b·c ---------- */
  function figApplyLine(a, b, c, t) {
    const title = "Euclides I.44: aplicar un área a un segmento";
    if (bad(a, b, c) || a <= 0 || b <= 0 || c <= 0) return noFig(title, "Se necesitan a, b y c positivos");
    const x = b * c / a, p1 = ph(t, 0, .25), p2 = ph(t, .25, .55), p3 = ph(t, .6, .9), P0 = [-a, c], P1 = [b, -x];
    const items = [rect(0, 0, b, c, C.gold, { a: .35 }), txt([b / 2, c / 2], `b·c = ${f2(b * c)}`, C.gold, { b: 1, f: 12 })];
    if (p1 > .02) items.push(rect(-a, 0, a, c, C.muted, { nofill: 1, dash: [4, 4], w: 1 }));
    if (p2 > .02) items.push(seg(P0, [lerp(P0[0], P1[0], p2), lerp(P0[1], P1[1], p2)], C.violet, { w: 1.6 }), seg([b, 0], [b, -x * p2], C.muted, { dash: [4, 4], w: 1 }), seg([-a, 0], [-a, -x * p2], C.muted, { dash: [4, 4], w: 1 }));
    if (p3 > 0) {
      items.push(rect(-a, -x, a + b, x + c, C.ink, { nofill: 1, dash: [4, 4], w: 1 }), rect(-a, -x, a, x, C.blue, { a: .4 * p3 }));
      if (p3 > .5) items.push(txt([-a / 2, -x / 2], `a·x = ${f2(a * x)}`, C.blue, { b: 1, f: 12 }), txt([-a, -x / 2], `x = ${f2(x)}`, C.blue, { al: "right", dx: -8, f: 12, b: 1 }));
    }
    items.push(seg([-a, 0], [0, 0], C.blue, { w: 3.2 }), txt([-a / 2, 0], `a = ${f2(a)}`, C.blue, { dy: -12, f: 12 }), txt([b / 2, c], "b", C.gold, { dy: -12, f: 11 }), txt([b, c / 2], "c", C.gold, { al: "left", dx: 8, f: 11 }),
      { k: "pt", p: [0, 0], c: C.violet, r: 4, lab: "K", dx: 8, dy: 10 });
    return scene(title, `a·x = b·c: el segmento a se pone junto al rectángulo dado; la diagonal por K corta la prolongación y el complemento (I.43) es el rectángulo buscado. x = bc/a = ${f2(x)}.`, items);
  }
  /* ---------- VI.12: la cuarta proporcional (Tales) ---------- */
  function figFourth(a, b, c, t) {
    const title = "Euclides VI.12: la cuarta proporcional";
    if (bad(a, b, c) || a <= 0 || b <= 0 || c <= 0) return noFig(title, "Se necesitan a, b y c positivos");
    const x = b * c / a, th = 35 * Math.PI / 180, d = [Math.cos(th), Math.sin(th)], at = k => [k * d[0], k * d[1]];
    const A = [a, 0], B = [a + b, 0], Cc = at(c), D = at(c + x), p1 = ph(t, 0, .3), p2 = ph(t, .35, .75), p3 = ph(t, .8, 1), L = Math.max(a + b, c + x) * 1.12;
    const items = [seg([0, 0], [L, 0], C.muted, { w: 1 }), seg([0, 0], at(L), C.muted, { w: 1 }),
      seg([0, 0], A, C.blue, { w: 3.2 }), seg(A, B, C.gold, { w: 3.2 }), seg([0, 0], Cc, C.blue, { w: 3.2 }),
      txt([a / 2, 0], `a = ${f2(a)}`, C.blue, { dy: 14, f: 12 }), txt([a + b / 2, 0], `b = ${f2(b)}`, C.gold, { dy: 14, f: 12 }), txt(at(c / 2), `c = ${f2(c)}`, C.blue, { al: "right", dx: -6, dy: -6, f: 12 })];
    if (p1 > .02) items.push(seg(A, [lerp(A[0], Cc[0], p1), lerp(A[1], Cc[1], p1)], C.violet, { w: 1.6 }));
    if (p2 > .02) items.push(seg(B, [lerp(B[0], D[0], p2), lerp(B[1], D[1], p2)], C.violet, { w: 1.6, dash: [6, 4] }));
    if (p3 > 0) items.push(seg(Cc, D, C.green, { w: 3.6 }), txt(at(c + x / 2), `x = ${f2(x)}`, C.green, { al: "right", dx: -6, dy: -6, f: 12, b: 1 }));
    items.push({ k: "pt", p: [0, 0], c: C.ink, r: 3.5, lab: "O", al: "right", dx: -8 });
    return scene(title, `a : b = c : x. Se une el extremo de a con el de c y por el extremo de b se traza la paralela (VI.2, Tales): corta la otra recta en x = bc/a = ${f2(x)}. Es la regla de tres.`, items);
  }
  /* ---------- VI.27: el diorismo, el mayor rectángulo aplicado con defecto ---------- */
  function figMaxRect(a, t) {
    const title = "Euclides VI.27: el máximo es el cuadrado de la mitad";
    if (bad(a) || a <= 0) return noFig(title, "Se necesita a > 0");
    const h = a / 2, s = h + .38 * a * Math.cos(Math.PI / 2 + 2.5 * Math.PI * t) * (1 - ph(t, .55, 1)), d = a - s, e = Math.abs(s - h);
    const items = [rect(0, 0, h, h, C.muted, { nofill: 1, dash: [4, 4], w: 1.2 }), rect(0, 0, s, d, C.blue, { a: .3 }), rect(s, 0, d, d, C.green, { a: .25, dash: [5, 4] })];
    items.push(rect(a + .12 * a, 0, e, e, C.red, { a: .35 }), txt([a + .12 * a + Math.max(e, .02 * a) / 2, 0], `(x − a/2)² = ${f2(e * e)}`, C.red, { dy: 14, f: 11 }));
    // la curva x(a − x) bajo el segmento: su cumbre está en x = a/2
    const K = .6 / a, curve = []; for (let i = 0; i <= 40; i++) { const xx = a * i / 40; curve.push([xx, -.25 * a - K * (h * h - xx * (a - xx))]); }
    items.push({ k: "poly", p: curve, c: C.violet, fill: null, w: 1.4, close: false }, { k: "pt", p: [s, -.25 * a - K * (h * h - s * d)], c: C.violet, r: 4 });
    items.push(seg([0, 0], [a, 0], C.ink, { w: 2.4 }), { k: "pt", p: [s, 0], c: C.blue, r: 3.5, lab: "S", dy: 12 });
    items.push(txt([s / 2, d / 2], `x(a − x) = ${f2(s * d)}`, C.blue, { b: 1, f: 12 }), txt([h / 2, h], `(a/2)² = ${f2(h * h)}`, C.muted, { dy: -12, f: 12 }));
    return scene(title, "S recorre AB: x(a − x) = (a/2)² − (x − a/2)², así que el rectángulo nunca supera el cuadrado de la mitad y solo lo iguala en el punto medio. Por eso VI.28 exige b ≤ (a/2)²: el discriminante.", items);
  }
  /* ---------- VI.30: razón extrema y media = VI.29 con b = a² ---------- */
  function figExtreme(a, t) {
    const sc = figApply(a, a * a, t, true), x = a * (Math.sqrt(5) - 1) / 2;
    sc.title = "Euclides VI.30: razón extrema y media";
    if (ph(t, .82, 1) > .5) sc.items.push({ k: "pt", p: [x, 0], c: C.gold, r: 4.5, lab: "C", dy: 12 }, txt([x / 2, 0], `AC = x = ${f2(x)}`, C.gold, { dy: 28, f: 12, b: 1 }));
    sc.cap = `a : x = x : (a − x) equivale a x(a + x) = a²: es VI.29 con el área a². El segmento BD = x = a(√5 − 1)/2 = ${f2(x)} se lleva sobre AB y lo corta en C en la proporción áurea (lo mismo que II.11).`;
    return sc;
  }
  /* ---------- Libro III: potencia de un punto ---------- */
  // III.35: cuerdas que se cortan en P: PA·PB = PC·PD  →  c·x = a·b
  function figChords(a, b, c, t) {
    const title = "Euclides III.35: cuerdas que se cortan";
    if (bad(a, b, c) || a <= 0 || b <= 0 || c <= 0) return noFig(title, "Se necesitan a, b y c positivos");
    const x = a * b / c, need = 1.25 * Math.max(c, x, a, b), ox = (b - a) / 2;
    let k = 0, R, op; for (let i = 0; i < 400; i++) { R = Math.hypot((a + b) / 2, k); op = Math.hypot(ox, k); if (R + op >= need) break; k += .05 * need; }
    // C: corte de la circunferencia (O, R) con la de centro P y radio c
    const O = [ox, k], d = op, l = (c * c - R * R + d * d) / (2 * d), hh = Math.sqrt(Math.max(0, c * c - l * l)), e = [O[0] / d, O[1] / d];
    const Cp = [l * e[0] - hh * e[1], l * e[1] + hh * e[0]], D = [-Cp[0] * x / c, -Cp[1] * x / c];
    const p1 = ph(t, 0, .3), p2 = ph(t, .3, .6), p3 = ph(t, .65, .95);
    const items = [{ k: "circ", o: O, r: R, c: C.muted, w: 1.4 }, seg([-a, 0], [0, 0], C.blue, { w: 3 }), seg([0, 0], [b, 0], C.gold, { w: 3 }),
      txt([-a / 2, 0], `a = ${f2(a)}`, C.blue, { dy: 14, f: 12 }), txt([b / 2, 0], `b = ${f2(b)}`, C.gold, { dy: 14, f: 12 })];
    if (p1 > .02) items.push(seg([0, 0], [Cp[0] * p1, Cp[1] * p1], C.violet, { w: 3 }));
    if (p1 > .5) items.push(txt([Cp[0] / 2, Cp[1] / 2], `c = ${f2(c)}`, C.violet, { al: "left", dx: 8, f: 12 }));
    if (p2 > .02) items.push(seg([0, 0], [D[0] * p2, D[1] * p2], C.green, { w: 3 }));
    if (p2 > .5) items.push(txt([D[0] / 2, D[1] / 2], `x = ${f2(x)}`, C.green, { al: "left", dx: 8, f: 12, b: 1 }));
    if (p3 > 0) {
      const y0 = k - R - .15 * R, w = Math.max(a, x);
      items.push(rect(-w - .1 * R, y0 - b, a, b, C.gold, { a: .35 * p3 }), txt([-w - .1 * R + a / 2, y0 - b / 2], `a·b = ${f2(a * b)}`, C.gold, { b: 1, f: 12 }));
      items.push(rect(.1 * R, y0 - c, x, c, C.green, { a: .35 * p3 }), txt([.1 * R + x / 2, y0 - c / 2], `c·x = ${f2(c * x)}`, C.green, { b: 1, f: 12 }));
    }
    items.push({ k: "pt", p: [0, 0], c: C.ink, r: 4, lab: "P", dx: -10, dy: -10, al: "right" });
    return scene(title, `Si dos cuerdas se cortan en P, el rectángulo de los trozos de una iguala al de la otra: c·x = a·b, x = ab/c = ${f2(x)}. Cada punto tiene una «potencia» fija respecto del círculo.`, items, { box: bbox(items.filter(i => i.k !== "circ").concat([seg([O[0] - R, O[1] - R], [O[0] + R, O[1] + R], null)])) });
  }
  // III.36: secante y tangente desde P: PA·PB = PT²  →  x(x + a) = t² (la construcción de Descartes)
  function figTangent(a, tt, t) {
    const title = "Euclides III.36: secante y tangente";
    if (bad(a, tt) || a <= 0 || tt <= 0) return noFig(title, "Se necesitan a > 0 y t > 0");
    const r = a / 2, x = Math.hypot(r, tt) - r, P = [-x, 0], O = [r, 0], dd = x + r, al = Math.asin(r / dd);
    const T = [P[0] + tt * Math.cos(al), P[1] + tt * Math.sin(al)];
    const p1 = ph(t, 0, .25), p2 = ph(t, .25, .5), p3 = ph(t, .5, .7), p4 = ph(t, .72, 1);
    const items = [seg(P, [lerp(P[0], T[0], p1), lerp(P[1], T[1], p1)], C.red, { w: 3 })];
    if (p1 > .5) items.push(txt([(P[0] + T[0]) / 2, (P[1] + T[1]) / 2], `t = ${f2(tt)}`, C.red, { al: "right", dx: -6, dy: -8, f: 12 }));
    if (p2 > .02) items.push(seg(T, [lerp(T[0], O[0], p2), lerp(T[1], O[1], p2)], C.violet, { w: 1.6 }), { k: "circ", o: O, r, a0: 0, a1: Math.max(.01, 2 * Math.PI * p2), c: C.muted, w: 1.4 });
    if (p2 > .5) items.push(txt([(T[0] + O[0]) / 2, (T[1] + O[1]) / 2], "a/2", C.violet, { al: "left", dx: 6, f: 11 }));
    if (p3 > .02) items.push(seg(P, [lerp(P[0], a, p3), 0], C.ink, { w: 1.2, dash: [5, 4] }));
    if (p4 > 0) {
      items.push(seg(P, [0, 0], C.green, { w: 3.6 }), seg([0, 0], [a, 0], C.blue, { w: 3 }), txt([-x / 2, 0], `x = ${f2(x)}`, C.green, { dy: 14, f: 12, b: 1 }), txt([r, 0], `a = ${f2(a)}`, C.blue, { dy: 14, f: 11 }));
      const y0 = -r - .25 * a;
      items.push(rect(-x, y0 - x, x + a, x, C.green, { a: .3 * p4 }), txt([-x + (x + a) / 2, y0 - x / 2], `x(x + a) = ${f2(x * (x + a))}`, C.green, { b: 1, f: 12 }));
      items.push(rect(a + .1 * a, y0 - tt, tt, tt, C.red, { a: .3 * p4 }), txt([a + .1 * a + tt / 2, y0 - tt / 2], `t² = ${f2(tt * tt)}`, C.red, { b: 1, f: 12 }));
    }
    items.push({ k: "pt", p: P, c: C.ink, r: 4, lab: "P", al: "right", dx: -8 }, { k: "pt", p: T, c: C.red, r: 3.5, lab: "T" }, { k: "pt", p: O, c: C.violet, r: 3, lab: "O", dy: 12 });
    return scene(title, `Desde P, el rectángulo de la secante entera por su parte exterior iguala al cuadrado de la tangente: x(x + a) = t². Para resolverla se traza el círculo de diámetro a tangente a PT en T (Descartes): x = √((a/2)² + t²) − a/2 = ${f2(x)}.`, items, { box: bbox(items.filter(i => i.k !== "circ").concat([seg([0, -r], [a, r], null)])) });
  }
  /* ---------- VII.1–2 y X.2: la antifairesis (restar el menor del mayor una y otra vez) ----------
     El rectángulo a×b se recorta en cuadrados: si termina, el último lado es el m.c.d. (VII.2);
     si no termina nunca, las magnitudes son inconmensurables (X.2). Los cocientes son la fracción continua. */
  function figAnthy(A, B, t, title, irr) {
    if (bad(A, B) || A <= 0 || B <= 0) return noFig(title, "Se necesitan dos magnitudes positivas");
    const W = Math.max(A, B), H0 = Math.min(A, B), sq = [], qs = [];
    let x0 = 0, y0 = 0, w = W, h = H0, lev = 0, done = false;
    while (lev < 14 && sq.length < 40) {
      const across = w >= h, s = across ? h : w, q = Math.floor((across ? w : h) / s + 1e-9);
      for (let i = 0; i < q && sq.length < 40; i++) sq.push(across ? [x0 + i * s, y0, s, lev] : [x0, y0 + i * s, s, lev]);
      if (across) { x0 += q * s; w -= q * s; } else { y0 += q * s; h -= q * s; }
      qs.push(q); lev++;
      if (Math.min(w, h) < 1e-9 * W) { done = true; break; }
    }
    const n = Math.max(1, Math.ceil(ph(t, .05, .9) * sq.length)), items = [rect(0, 0, W, H0, C.ink, { nofill: 1, w: 2 })];
    sq.slice(0, n).forEach(([x, y, s, l]) => { const col = PAL()[l % 6]; items.push(rect(x, y, s, s, col, { a: .3, w: 1.1 })); if (s > .07 * W) items.push(txt([x + s / 2, y + s / 2], f2(s), col, { f: s > .2 * W ? 12 : 10 })); });
    const cf = `[${qs[0]}; ${qs.slice(1, 6).join(", ")}${done && qs.length <= 6 ? "" : ", …"}]`, fin = n >= sq.length;
    items.push(txt([W / 2, 0], `${f2(W)}`, C.ink, { dy: 14, f: 12 }), txt([0, H0 / 2], `${f2(H0)}`, C.ink, { al: "right", dx: -8, f: 12 }));
    if (fin) items.push(txt([W / 2, H0], done ? `m.c.d. = ${f2(sq[sq.length - 1][2])}   ·   ${f2(W)}/${f2(H0)} = ${cf}` : `no termina: inconmensurables   ·   ${cf}`, done ? C.green : C.red, { dy: -14, f: 12, b: 1 }));
    const cap = irr ? `x = √2 frente a 1: al quitar cuadrados siempre queda un rectángulo semejante al anterior, así que el proceso no acaba nunca y no existe medida común (X.2). La fracción continua [1; 2, 2, 2, …] lo muestra.`
      : `Se quita del rectángulo a×b el mayor cuadrado posible, una y otra vez (a = q·b + r). Si acaba, el último cuadrado mide el m.c.d. y la cuenta de cuadrados de cada tamaño es la fracción continua de a/b; si acaba en 1, son primos entre sí (VII.1). Mueve a y b a valores enteros.`;
    return scene(title, cap, items);
  }
  /* ---------- IX.35: la suma de una progresión geométrica ---------- */
  function figGeoSum(a, k, t) {
    const title = "Euclides IX.35: la suma de la progresión geométrica";
    if (bad(a, k) || a <= 0 || k <= 0 || Math.abs(k - 1) < 1e-9) return noFig(title, "Se necesitan a > 0 y una razón k > 0 distinta de 1");
    const T = [0, 1, 2, 3].map(i => a * k ** i), last = a * k ** 4, S = T.reduce((s, v) => s + v, 0), L = Math.max(last, S, a), H = .07 * L;
    const p1 = ph(t, 0, .35), p2 = ph(t, .35, .7), p3 = ph(t, .72, 1), items = [];
    // fila de arriba: el exceso del último sobre el primero, partido en los excesos sucesivos
    const pts = [a, ...T.slice(1), last];
    items.push(seg([0, 0], [Math.max(a, last), 0], C.muted, { w: 1 }), rect(0, 0, a, H, C.ink, { a: .12 }), txt([a / 2, H], "a", C.ink, { dy: -10, f: 11 }));
    for (let i = 0; i < 4; i++) {
      const x1 = pts[i], x2 = pts[i + 1], col = PAL()[i];
      items.push(rect(Math.min(x1, x2), 0, Math.abs(x2 - x1) * p1, H, col, { a: .35 }));
      if (p1 > .9 && Math.abs(x2 - x1) > .06 * L) items.push(txt([(x1 + x2) / 2, H / 2], `(k−1)·${i ? "ak" + (i > 1 ? (i === 2 ? "²" : "³") : "") : "a"}`, col, { f: 10 }));
    }
    items.push(txt([Math.max(a, last), H], `ak⁴ = ${f2(last)}`, C.ink, { dy: -10, f: 11, al: "right" }));
    // fila de abajo: los términos uno tras otro, que suman S
    let x = 0;
    if (p2 > 0) T.forEach((v, i) => { items.push(rect(x, -3 * H, v * p2, H, PAL()[i], { a: .35 })); if (p2 > .9 && v > .06 * L) items.push(txt([x + v / 2, -2.5 * H], f2(v), PAL()[i], { f: 11 })); x += v * p2; });
    if (p2 > .9) items.push(txt([S, -2.5 * H], `S = ${f2(S)}`, C.ink, { al: "left", dx: 8, f: 12, b: 1 }));
    if (p3 > .5) items.push(txt([L / 2, -3 * H], `ak⁴ − a = (k − 1)·S  →  S = ${f2(last - a)}/${f2(k - 1)} = ${f2(S)}`, C.green, { dy: 18, f: 12, b: 1 }));
    return scene(title, "Arriba, el exceso del último término sobre el primero se parte en los excesos sucesivos; cada uno es (k − 1) veces un término. Abajo, los términos uno tras otro: el exceso total es (k − 1) veces la suma.", items);
  }
  /* ---------- Libro XII: el método de exhaución ----------
     XII.2: los círculos son como los cuadrados de sus diámetros (polígonos inscritos que se duplican).
     XII.18: las esferas son como los cubos de sus diámetros (aquí, rodajas cilíndricas inscritas). */
  function figExhaust(a, b, t, solid) {
    const title = solid ? "Euclides XII.18: las esferas y el cubo del diámetro" : "Euclides XII.2: los círculos y el cuadrado del diámetro";
    if (bad(a, b) || a <= 0 || b <= 0) return noFig(title, "Se necesitan dos diámetros positivos");
    const lv = Math.min(5, Math.floor(ph(t, 0, .95) * 6)), n = 4 * 2 ** lv, gap = .25 * Math.max(a, b), ox = [a / 2, a + gap + b / 2];
    const items = [], meas = [], ex = solid ? 3 : 2;
    [a, b].forEach((d, j) => {
      const R = d / 2, o = [ox[j], 0], col = j ? C.gold : C.blue;
      items.push({ k: "circ", o, r: R, c: C.ink, w: 1.6 });
      if (!solid) {
        const P = []; for (let i = 0; i < n; i++) { const th = Math.PI / 2 + 2 * Math.PI * i / n; P.push([o[0] + R * Math.cos(th), R * Math.sin(th)]); }
        items.push({ k: "poly", p: P, c: col, fill: AL(col, .3), w: 1.1 });
        meas.push([n / 2 * R * R * Math.sin(2 * Math.PI / n), Math.PI * R * R]);
      } else {
        const h = d / n; let V = 0;
        for (let i = 0; i < n; i++) { const y1 = -R + i * h, y2 = y1 + h, r = Math.sqrt(Math.max(0, R * R - Math.max(y1 * y1, y2 * y2))); V += Math.PI * r * r * h; if (r > 0) items.push(rect(o[0] - r, y1, 2 * r, h, col, { a: .3, w: .8 })); }
        items.push({ k: "ell", o, rx: R, ry: .22 * R, c: C.muted, w: .8, dash: [4, 4] });
        meas.push([V, 4 / 3 * Math.PI * R ** 3]);
      }
      items.push(txt([o[0], -R], `d = ${f2(d)}`, col, { dy: 14, f: 12 }), txt([o[0], R], `${solid ? "llena" : "cubre"} ${(100 * meas[j][0] / meas[j][1]).toFixed(2)} %`, col, { dy: -12, f: 11 }));
    });
    const sup = solid ? "³" : "²", nm = solid ? `${n} rodajas` : `${n} lados`;
    items.push(txt([(a + gap + b / 2 + a / 2) / 2 + 0 * gap, -Math.max(a, b) / 2], `${nm}:  ${solid ? "V₂/V₁" : "P₂/P₁"} = ${f2(meas[1][0] / meas[0][0])} = (b/a)${sup} = ${f2((b / a) ** ex)}`, C.ink, { dy: 34, f: 12, b: 1 }));
    return scene(title, solid ? "Las rodajas cilíndricas inscritas en dos esferas guardan siempre la razón de los cubos de los diámetros; al hacerlas más finas agotan las esferas, así que las esferas también la guardan: x = (b/a)³. Euclides usa poliedros inscritos; la idea es la misma."
      : "Los polígonos inscritos semejantes están siempre en la razón de los cuadrados de los diámetros (XII.1). Al duplicar sus lados agotan los círculos (X.1), así que los círculos también: x = (b/a)². Es el origen del número π y del cálculo integral.", items);
  }
  /* ---------- Libro V: una proporción es una recta por el origen ----------
     a : b = c : x  ⇔  los puntos (b, a) y (x, c) están en la misma recta por O.
     V.16 (alternar): los dos triángulos son homotéticos, así que a : c = b : x (la razón de la homotecia).
     V.18 (componer): la cizalla (u, v) → (u, u + v) lleva rectas por O a rectas por O: (a + b) : b = (c + x) : x.
     V.12 (sumar): (b, a) + (x, c) sigue en la recta: (a + c) : (b + x) = a : b. */
  function figRatio(a, b, c, t, mode) {
    const T = { alt: "Euclides V.16: alternar una proporción", comp: "Euclides V.18: componer una proporción", sum: "Euclides V.12: sumar antecedentes y consecuentes" }[mode];
    if (bad(a, b, c) || a <= 0 || b <= 0 || c <= 0) return noFig(T, "Se necesitan a, b y c positivos");
    const x = b * c / a, s = mode === "comp" ? ph(t, .3, .85) : 0, P = [b, a + s * b], Q = [x, c + s * x], q = ph(t, .3, .85);
    const R = mode === "sum" ? [b + x * q, a + c * q] : null, far = Math.max(b, x, R ? R[0] : 0) * 1.2, m = P[1] / P[0];
    const items = [seg([0, 0], [far, 0], C.muted, { w: 1 }), seg([0, 0], [0, far * Math.max(m, .3)], C.muted, { w: 1 }), seg([0, 0], [far, far * m], C.violet, { w: 1.4, dash: [6, 4] })];
    const tri = (p, col) => items.push({ k: "poly", p: [[0, 0], [p[0], 0], p], c: col, fill: AL(col, .15), w: 1.6 }, seg([p[0], 0], p, col, { w: 3.2 }), seg([0, 0], [p[0], 0], col, { w: 3.2 }));
    tri(P, C.blue); tri(Q, C.gold);
    const lab = (p, sx, sy, col) => items.push(txt([p[0] / 2, 0], sx, col, { dy: 14, f: 12 }), txt([p[0], p[1] / 2], sy, col, { al: "left", dx: 6, f: 12 }));
    if (mode === "comp" && s > .5) { lab(P, "b", "a + b", C.blue); lab(Q, "x", "c + x", C.gold); } else { lab(P, "b", "a", C.blue); lab(Q, `x = ${f2(x)}`, "c", C.gold); }
    let res;
    if (mode === "alt") { if (q > .5) items.push(txt([far / 2, far * m], `a : c = ${f2(a / c)}   b : x = ${f2(b / x)}`, C.ink, { dy: -14, f: 12, b: 1 })); res = "los dos triángulos son semejantes con la misma razón, así que los lados homólogos están en proporción: a : c = b : x"; }
    if (mode === "comp") { if (s > .5) items.push(txt([far / 2, far * m], `(a + b) : b = ${f2(P[1] / P[0])} = (c + x) : x`, C.ink, { dy: -14, f: 12, b: 1 })); res = "la cizalla que sube cada punto lo que mide su abscisa mantiene la recta por O: (a + b) : b = (c + x) : x"; }
    if (mode === "sum") { items.push(seg(P, R, C.gold, { w: 2, dash: [4, 3] }), { k: "pt", p: R, c: C.green, r: 4.5, lab: "suma" }); if (q > .95) items.push(txt([R[0], R[1]], `(a + c) : (b + x) = ${f2((a + c) / (b + x))} = a : b`, C.green, { al: "right", dx: -10, dy: -14, f: 12, b: 1 })); res = "al poner un triángulo a continuación del otro, el vértice sigue en la recta: (a + c) : (b + x) = a : b"; }
    return scene(T, `a : b = c : x significa que (b, a) y (x, c) están en la misma recta por O. Aquí ${res}. x = bc/a = ${f2(x)}.`, items);
  }
  /* ---------- IV.10–11: el triángulo áureo y el pentágono ---------- */
  function figGolden(a, t, penta) {
    const title = penta ? "Euclides IV.11: el pentágono regular" : "Euclides IV.10: el triángulo áureo (36°, 72°, 72°)";
    if (bad(a) || a <= 0) return noFig(title, "Se necesita a > 0");
    const phi = (1 + Math.sqrt(5)) / 2, x = a * phi, p = ph(t, .25, .6), q = ph(t, .6, .95), items = [];
    if (!penta) {
      const B = [0, 0], Cc = [a, 0], A = [a / 2, Math.sqrt(x * x - a * a / 4)];
      // la bisectriz desde B corta AC en D con BD = a = AD, y CD = x − a
      const Dp = [A[0] + (Cc[0] - A[0]) * (a / x), A[1] + (Cc[1] - A[1]) * (a / x)];
      items.push({ k: "poly", p: [B, Cc, A], c: C.ink, fill: AL(C.gold, .12), w: 2 });
      if (p > .02) items.push(seg(B, [lerp(B[0], Dp[0], p), lerp(B[1], Dp[1], p)], C.violet, { w: 1.6 }));
      if (q > 0) items.push({ k: "poly", p: [B, Cc, Dp], c: C.blue, fill: AL(C.blue, .35 * q), w: 1.6 }, { k: "poly", p: [A, B, Dp], c: C.green, fill: AL(C.green, .25 * q), w: 1.2 });
      items.push(txt([a / 2, 0], `a = ${f2(a)}`, C.ink, { dy: 14, f: 12 }), txt([A[0] / 2 - .02 * a, A[1] / 2], `x = ${f2(x)}`, C.ink, { al: "right", dx: -8, f: 12 }), txt(A, "36°", C.ink, { dy: 18, f: 11 }));
      if (q > .5) items.push(txt([(Dp[0] + Cc[0]) / 2, (Dp[1] + Cc[1]) / 2], `x − a`, C.blue, { al: "left", dx: 8, f: 11 }), txt([(A[0] + Dp[0]) / 2, (A[1] + Dp[1]) / 2], "a", C.green, { al: "left", dx: 8, f: 11 }));
      return scene(title, `La bisectriz del ángulo de 72° corta un triángulo semejante al grande (azul) y otro isósceles (verde, AD = BD = a). Semejanza: x : a = a : (x − a), es decir x² = ax + a²: el lado es la sección áurea del doble (II.11). x = a·φ = ${f2(x)}.`, items);
    }
    const R = a / (2 * Math.sin(Math.PI / 5)), V = [0, 1, 2, 3, 4].map(i => { const th = Math.PI / 2 + 2 * Math.PI * i / 5; return [R * Math.cos(th), R * Math.sin(th)]; });
    items.push({ k: "circ", o: [0, 0], r: R, c: C.muted, w: 1, dash: [4, 4] }, { k: "poly", p: V, c: C.ink, fill: AL(C.gold, .1), w: 2 });
    if (p > .02) [[0, 2], [2, 4], [4, 1], [1, 3], [3, 0]].forEach(([i, j], n) => { if (p * 5 > n) items.push(seg(V[i], V[j], C.violet, { w: 1.3 })); });
    if (q > 0) items.push({ k: "poly", p: [V[0], V[2], V[3]], c: C.blue, fill: AL(C.blue, .3 * q), w: 2 });
    items.push(txt([(V[2][0] + V[3][0]) / 2, V[2][1]], `a = ${f2(a)}`, C.ink, { dy: 14, f: 12 }));
    if (q > .5) items.push(txt([(V[0][0] + V[3][0]) / 2, (V[0][1] + V[3][1]) / 2], `x = ${f2(x)}`, C.blue, { al: "left", dx: 8, f: 12, b: 1 }));
    return scene(title, `Las diagonales del pentágono forman con un lado el triángulo áureo de IV.10 (azul): por eso se inscribe con regla y compás. Diagonal : lado = φ, x² = ax + a², x = ${f2(x)}.`, items, { box: bbox(items.filter(i => i.k !== "circ").concat([seg([-R, -R], [R, R], null)])) });
  }
  /* ---------- XIII.1, 3, 4: identidades de la sección áurea (x = parte mayor de a) ---------- */
  function figXIII(a, t, n) {
    const title = `Euclides XIII.${n}: la sección áurea`;
    if (bad(a) || a <= 0) return noFig(title, "Se necesita a > 0");
    const x = a * (Math.sqrt(5) - 1) / 2, y = a - x, H = [a / 2, "a/2"], hx = [x / 2, "x/2"];
    const sp = { 1: [[[x + a / 2, "(x + a/2)"]], [H, H, H, H, H], "El cuadrado de la parte mayor más la mitad del todo vale cinco veces el cuadrado de la mitad: (x + a/2)² = 5(a/2)²."],
      3: [[[a - x / 2, "(a − x/2)"]], [hx, hx, hx, hx, hx], "El cuadrado de la parte menor más la mitad de la mayor vale cinco veces el cuadrado de esa mitad: (a − x/2)² = 5(x/2)²."],
      4: [[[a, "a"], [y, "(a − x)"]], [[x, "x"], [x, "x"], [x, "x"]], "El cuadrado del todo más el de la parte menor vale tres veces el de la mayor: a² + (a − x)² = 3x²."] }[n];
    const sc = figAreas(sp[0], sp[1], t, title, `${sp[2]} Todas equivalen a x² + ax = a², x = ${f2(x)}.`);
    const y0 = Math.max(...sp[0].map(r => r[0])) + .25 * a;
    sc.items.push(seg([0, y0], [x, y0], C.gold, { w: 3.2 }), seg([x, y0], [a, y0], C.blue, { w: 3.2 }), { k: "pt", p: [x, y0], c: C.ink, r: 3.5 }, txt([x / 2, y0], "x", C.gold, { dy: -12, f: 12 }), txt([(a + x) / 2, y0], "a − x", C.blue, { dy: -12, f: 11 }));
    sc.box = bbox(sc.items);
    return sc;
  }
  PROPS.push(
    { id: "IV.10", book: "IV", eq: "x^2 = a x + a^2", name: "El triángulo áureo", fig: (env, t) => figGolden(E(env, "a", 3), t, false) },
    { id: "IV.11", book: "IV", eq: "x^2 = a x + a^2", name: "El pentágono regular", fig: (env, t) => figGolden(E(env, "a", 3), t, true) },
    { id: "V.12", book: "V", eq: "(a + c)/(b + x) = a/b", name: "Sumar antecedentes y consecuentes", fig: (env, t) => figRatio(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t, "sum") },
    { id: "V.16", book: "V", eq: "a/c = b/x", name: "Alternar una proporción", fig: (env, t) => figRatio(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t, "alt") },
    { id: "V.18", book: "V", eq: "(a + b)/b = (c + x)/x", name: "Componer una proporción", fig: (env, t) => figRatio(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t, "comp") },
    { id: "XIII.1", book: "XIII", eq: "(x + a/2)^2 = 5(a/2)^2", name: "Parte mayor más la mitad", fig: (env, t) => figXIII(E(env, "a", 3), t, 1) },
    { id: "XIII.3", book: "XIII", eq: "(a - x/2)^2 = 5(x/2)^2", name: "Parte menor más la mitad de la mayor", fig: (env, t) => figXIII(E(env, "a", 3), t, 3) },
    { id: "XIII.4", book: "XIII", eq: "a^2 + (a - x)^2 = 3x^2", name: "Todo y parte menor frente a la mayor", fig: (env, t) => figXIII(E(env, "a", 3), t, 4) });
  PROPS.push(
    { id: "XII.2", book: "XII", eq: "a^2 x = b^2", name: "Los círculos y el cuadrado del diámetro", fig: (env, t) => figExhaust(E(env, "a", 3), E(env, "b", 2), t, false) },
    { id: "XII.18", book: "XII", eq: "a^3 x = b^3", name: "Las esferas y el cubo del diámetro", fig: (env, t) => figExhaust(E(env, "a", 3), E(env, "b", 2), t, true) });
  PROPS.push(
    { id: "VII.2", book: "VII", eq: "a = q b + r", name: "Algoritmo de Euclides (m.c.d.)", fig: (env, t) => figAnthy(E(env, "a", 3), E(env, "b", 2), t, "Euclides VII.1–2: el máximo común divisor", false) },
    { id: "IX.35", book: "IX", eq: "x(k - 1) = a(k^4 - 1)", name: "Suma de la progresión geométrica", fig: (env, t) => figGeoSum(E(env, "a", 3), E(env, "k", 2), t) },
    { id: "X.2", book: "X", eq: "x^2 = 2", name: "Inconmensurables: √2 frente a 1", fig: (env, t) => figAnthy(Math.SQRT2, 1, t, "Euclides X.2: la diagonal y el lado", true) });
  PROPS.push(
    { id: "III.35", book: "III", eq: "c x = a b", name: "Cuerdas que se cortan (potencia de un punto)", fig: (env, t) => figChords(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t) },
    { id: "III.36", book: "III", eq: "x(x + a) = t^2", name: "Secante y tangente", fig: (env, t) => figTangent(E(env, "a", 3), E(env, "t", 2), t) });
  PROPS.unshift(
    { id: "I.43", book: "I", eq: "c(b - bc/a) = (a - c)(bc/a)", name: "Los complementos son iguales", fig: (env, t) => figComplements(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t) },
    { id: "I.44", book: "I", eq: "a x = b c", name: "Aplicar un área a un segmento", fig: (env, t) => figApplyLine(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t) },
    { id: "I.47", book: "I", eq: "x^2 = a^2 + b^2", name: "Teorema de Pitágoras (el molino)", fig: (env, t) => figPyth(E(env, "a", 3), E(env, "b", 2), t) });
  PROPS.push(
    { id: "VI.12", book: "VI", eq: "a/b = c/x", name: "La cuarta proporcional (regla de tres)", fig: (env, t) => figFourth(E(env, "a", 3), E(env, "b", 2), E(env, "c", 1.5), t) },
    { id: "VI.13", book: "VI", eq: "a/x = x/b", name: "La media proporcional", fig: (env, t) => figMean(E(env, "a", 3), E(env, "b", 2), "a", "b", t, "Euclides VI.13: la media proporcional", "a : x = x : b. Sobre a + b se traza la semicircunferencia; la perpendicular en el punto de unión es x = √(ab).") },
    { id: "VI.27", book: "VI", eq: "x(a - x) = (a/2)^2", name: "El diorismo: el mayor rectángulo", fig: (env, t) => figMaxRect(E(env, "a", 3), t) },
    { id: "VI.28", book: "VI", eq: "x(a - x) = b", name: "Aplicación de áreas con defecto", fig: (env, t) => figApply(E(env, "a", 3), E(env, "b", 2), t, false) },
    { id: "VI.29", book: "VI", eq: "x(a + x) = b", name: "Aplicación de áreas con exceso", fig: (env, t) => figApply(E(env, "a", 3), E(env, "b", 2), t, true) },
    { id: "VI.30", book: "VI", eq: "a/x = x/(a - x)", name: "Razón extrema y media", fig: (env, t) => figExtreme(E(env, "a", 3), t) });

  const prop = id => PROPS.find(p => p.id === id);
  function propFigure(id, env, t) { const p = prop(id); if (!p) return null; try { return p.fig(env, t); } catch (e) { console.error(e); return noFig(id, "No se pudo dibujar"); } }

  const G = { ph, lerp, rect, rot, txt, seg, PAL, bbox, scene, noFig, f2, bad, figStrips, figGrid, figSqMinus, figGnomon, figCube, figComplete, figMean };
  return { find, apply, figure, byId, register, G, rules: R, eqRules: EQ, PROPS, prop, propFigure, cats: { exp: ["dist", "prod", "sq", "diffsq", "cube", "pascal", "powprod", "arith", "collect", "powmul", "powpow", "sqrtsq"], fac: ["commonf", "dsq", "perfsq", "trinom"], simp: ["sqrtsq", "arith", "collect", "powmul", "powpow", "sqrtsimp", "sqrtmul", "cancel", "fracmul", "fracadd"] } };
})();
