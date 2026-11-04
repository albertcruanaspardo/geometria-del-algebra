/* Geometría del Álgebra — lectura de la tiza.
   Cada símbolo se reconoce combinando cuatro pistas:
   1) la nube de puntos $P (Vatavu, Anthony y Wobbrock, 2012): forma, sin importar orden ni sentido de los trazos;
   2) una malla de 7×7 casillas: qué zonas del recuadro del símbolo tienen tiza;
   3) el tamaño y la proporción respecto a las líneas guía (una «c» es la mitad de alta que un «(»);
   4) la dirección: hacia qué lado se curva un trazo y si tiene esquina (< frente a c).
   La línea se lee agrupando trazos según el orden en que se dibujan y su solape, ordenando por el centro,
   con los exponentes por encima de la línea media y las fracciones por su raya horizontal. */
"use strict";
const TIZA = (() => {
  const N = 32, G = 7;
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
  const pathLen = p => { let d = 0; for (let i = 1; i < p.length; i++) if (p[i].id === p[i - 1].id) d += dist(p[i - 1], p[i]); return d; };
  function resample(p, n) {
    p = p.map(q => ({ ...q })); const I = pathLen(p) / (n - 1) || 1e-6; let D = 0; const out = [p[0]];
    for (let i = 1; i < p.length; i++) {
      if (p[i].id !== p[i - 1].id) continue;
      const d = dist(p[i - 1], p[i]);
      if (d > 0 && D + d >= I) { const t = (I - D) / d, q = { x: p[i - 1].x + t * (p[i].x - p[i - 1].x), y: p[i - 1].y + t * (p[i].y - p[i - 1].y), id: p[i].id }; out.push(q); p.splice(i, 0, q); D = 0; }
      else D += d;
    }
    while (out.length < n) out.push({ ...p[p.length - 1] });
    return out.slice(0, n);
  }
  function normalize(p) {
    let a = Infinity, b = -Infinity, c = Infinity, d = -Infinity;
    for (const o of p) { a = Math.min(a, o.x); b = Math.max(b, o.x); c = Math.min(c, o.y); d = Math.max(d, o.y); }
    const s = Math.max(b - a, d - c) || 1, q = p.map(o => ({ x: (o.x - a) / s, y: (o.y - c) / s, id: o.id }));
    const cx = q.reduce((t, o) => t + o.x, 0) / q.length, cy = q.reduce((t, o) => t + o.y, 0) / q.length;
    return q.map(o => ({ x: o.x - cx, y: o.y - cy, id: o.id }));
  }
  function cloud(strokes) {
    let pts = []; strokes.forEach((s, id) => s.forEach(([x, y]) => pts.push({ x, y, id })));
    if (pts.length === 1) pts.push({ ...pts[0], x: pts[0].x + 1e-3 });
    return normalize(resample(pts, N));
  }
  function cloudDist(a, b, start) {
    const n = a.length, used = new Array(n).fill(false); let sum = 0, i = start;
    do {
      let m = Infinity, idx = -1;
      for (let j = 0; j < n; j++) if (!used[j]) { const d = dist(a[i], b[j]); if (d < m) { m = d; idx = j; } }
      used[idx] = true; sum += (1 - ((i - start + n) % n) / n) * m; i = (i + 1) % n;
    } while (i !== start);
    return sum;
  }
  function match(a, b) { const n = a.length, step = Math.floor(Math.sqrt(n)); let m = Infinity; for (let i = 0; i < n; i += step) m = Math.min(m, cloudDist(a, b, i), cloudDist(b, a, i)); return m; }

  /* ---------- la malla: tinta por casilla en el recuadro del símbolo (conservando su proporción) ---------- */
  const bb = s => { const a = [Infinity, -Infinity, Infinity, -Infinity]; for (const [x, y] of s) { a[0] = Math.min(a[0], x); a[1] = Math.max(a[1], x); a[2] = Math.min(a[2], y); a[3] = Math.max(a[3], y); } return a; };
  const union = (A, B) => [Math.min(A[0], B[0]), Math.max(A[1], B[1]), Math.min(A[2], B[2]), Math.max(A[3], B[3])];
  function grid(strokes) {
    const b = strokes.map(bb).reduce(union), w = b[1] - b[0], h = b[3] - b[2], s = Math.max(w, h) || 1;
    const ox = b[0] - (s - w) / 2, oy = b[2] - (s - h) / 2, M = new Float32Array(G * G);
    const mark = (x, y) => { const gx = (x - ox) / s * G - .5, gy = (y - oy) / s * G - .5; for (let j = Math.floor(gy) - 1; j <= Math.ceil(gy) + 1; j++) for (let i = Math.floor(gx) - 1; i <= Math.ceil(gx) + 1; i++) { if (i < 0 || j < 0 || i >= G || j >= G) continue; const d = Math.hypot(i - gx, j - gy); if (d < 1.2) M[j * G + i] += 1.2 - d; } };
    for (const st of strokes) for (let k = 0; k < st.length; k++) {
      if (!k) { mark(...st[0]); continue; }
      const [x0, y0] = st[k - 1], [x1, y1] = st[k], n = Math.max(1, Math.ceil(Math.hypot(x1 - x0, y1 - y0) / s * G * 3));
      for (let q = 1; q <= n; q++) mark(x0 + (x1 - x0) * q / n, y0 + (y1 - y0) * q / n);
    }
    const tot = M.reduce((t, v) => t + v, 0) || 1; for (let i = 0; i < M.length; i++) M[i] /= tot;
    return M;
  }
  const gridDist = (A, B) => { let d = 0; for (let i = 0; i < A.length; i++) d += Math.abs(A[i] - B[i]); return d; };

  /* ---------- dirección de un trazo: hacia dónde se curva y si tiene esquina ---------- */
  function shape(s) {
    let p = s; if (p[0][1] > p[p.length - 1][1]) p = p.slice().reverse();
    const [x0, y0] = p[0], [x1, y1] = p[p.length - 1], h = Math.max(1, Math.abs(y1 - y0)), L = Math.max(h, Math.abs(x1 - x0));
    let dev = 0; for (const [x, y] of p) { if (y < y0 + .18 * h || y > y1 - .18 * h) continue; const xc = x0 + (y - y0) * (x1 - x0) / h, d = x - xc; if (Math.abs(d) > Math.abs(dev)) dev = d; }
    // esquina: el mayor giro entre tramos de la cuerda remuestreada
    const q = resample(s.map(([x, y]) => ({ x, y, id: 0 })), 24); let turn = 0;
    for (let i = 3; i < q.length - 3; i++) { const a1 = Math.atan2(q[i].y - q[i - 3].y, q[i].x - q[i - 3].x), a2 = Math.atan2(q[i + 3].y - q[i].y, q[i + 3].x - q[i].x); let d = Math.abs(a2 - a1); if (d > Math.PI) d = 2 * Math.PI - d; turn = Math.max(turn, d); }
    // «<» o «>»: el punto más alejado de la cuerda parte el trazo en dos tramos casi rectos
    let far = 0, fd = 0; q.forEach((o, i) => { const d = Math.abs((q[23].x - q[0].x) * (q[0].y - o.y) - (q[0].x - o.x) * (q[23].y - q[0].y)) / (Math.hypot(q[23].x - q[0].x, q[23].y - q[0].y) || 1); if (d > fd) { fd = d; far = i; } });
    const straight = (a, b) => { const A = q[a], B = q[b], len = Math.hypot(B.x - A.x, B.y - A.y) || 1; let m = 0; for (let i = a; i <= b; i++) m = Math.max(m, Math.abs((B.x - A.x) * (A.y - q[i].y) - (A.x - q[i].x) * (B.y - A.y)) / len); return m / len; };
    const ys = [q[0].y, q[23].y], cyr = (q[far].y - Math.min(...ys)) / (Math.abs(ys[1] - ys[0]) || 1);   // la esquina de < y > queda entre los extremos, no arriba como en el 7
    const vee = far > 4 && far < 19 && fd / L > .3 && straight(0, far) < .09 && straight(far, 23) < .09 && cyr > .25 && cyr < .75;
    return { dev: dev / L, slope: (x1 - x0) / h, turn, vee, closed: Math.hypot(s[0][0] - s[s.length - 1][0], s[0][1] - s[s.length - 1][1]) / L };
  }

  /* ---------- plantillas de serie (coordenadas de pantalla: y hacia abajo) ---------- */
  const L = (...v) => { const s = []; for (let i = 0; i < v.length; i += 2) s.push([v[i], v[i + 1]]); return s; };
  const ARC = (cx, cy, rx, ry, a0, a1, n = 24) => { const s = []; for (let k = 0; k <= n; k++) { const t = (a0 + (a1 - a0) * k / n) * Math.PI / 180; s.push([cx + rx * Math.cos(t), cy + ry * Math.sin(t)]); } return s; };
  const BASE = {
    "0": [[ARC(.5, .5, .32, .5, -90, 270)], [ARC(.5, .5, .32, .5, -90, -450)]],
    "1": [[L(.5, 0, .5, 1)], [L(.3, .22, .5, 0, .5, 1)], [L(.25, .25, .55, 0, .55, 1), L(.25, 1, .85, 1)]],
    "2": [[L(.15, .25, .3, .05, .55, 0, .8, .12, .82, .35, .6, .6, .15, 1, .85, 1)], [L(.1, .3, .25, .05, .6, 0, .85, .2, .75, .5, .1, 1, .9, .98)]],
    "3": [[L(.15, .1, .45, 0, .75, .12, .75, .35, .45, .48, .8, .6, .82, .85, .5, 1, .15, .9)], [L(.15, .05, .8, .05, .45, .45, .8, .6, .82, .85, .5, 1, .15, .9)]],
    "4": [[L(.6, 0, .1, .65, .9, .65), L(.65, .3, .65, 1)], [L(.15, 0, .1, .6, .9, .6), L(.7, 0, .7, 1)], [L(.55, 0, .1, .62, .95, .62), L(.68, .25, .66, 1)]],
    "5": [[L(.8, 0, .25, 0, .2, .42, .5, .38, .8, .55, .82, .82, .55, 1, .18, .9)], [L(.25, 0, .2, .42, .5, .38, .8, .55, .82, .82, .55, 1, .18, .9), L(.25, 0, .8, 0)]],
    "6": [[L(.75, .05, .4, .15, .2, .5, .25, .85, .5, 1, .78, .85, .78, .6, .5, .48, .22, .6)]],
    "7": [[L(.15, 0, .85, 0, .4, 1)], [L(.15, 0, .85, 0, .4, 1), L(.35, .5, .75, .5)], [L(.1, .05, .9, 0, .45, 1), L(.3, .52, .8, .5)]],
    "8": [[L(.5, .5, .2, .3, .3, .05, .5, 0, .72, .05, .8, .3, .5, .5, .2, .72, .3, .95, .5, 1, .72, .95, .82, .72, .5, .5)], [ARC(.5, .25, .26, .25, 90, 450), ARC(.5, .74, .3, .26, -90, 270)]],
    "9": [[L(.78, .4, .5, .52, .22, .4, .25, .1, .5, 0, .78, .12, .78, .4, .75, .7, .6, 1)], [L(.78, .4, .5, .52, .22, .4, .25, .1, .5, 0, .78, .12, .78, .4, .78, 1)], [L(.8, .35, .55, .5, .2, .4, .2, .12, .5, 0, .8, .15, .8, .45, .78, 1)]],
    "x": [[L(0, 0, 1, 1), L(1, 0, 0, 1)], [L(0, 0, .5, .45, 1, 1), L(.95, 0, .05, 1)], [ARC(.25, .5, .25, .5, -90, 90), ARC(.75, .5, .25, .5, 270, 90)]],
    "y": [[L(0, 0, .5, .5), L(1, 0, .25, 1)], [L(0, 0, .2, .45, .5, .5, .8, .4, 1, 0), L(1, 0, .8, .8, .6, 1)],
      [L(0, 0, .1, .4, .4, .5, .7, .4, .8, 0, .78, .7, .6, 1, .3, .95, .15, .8)], [L(0, 0, .45, .55, .9, 0, .45, .55, .25, 1)]],
    "a": [[L(.8, .3, .5, .15, .2, .35, .2, .75, .5, .9, .8, .6, .8, .15, .82, .95)], [ARC(.45, .55, .32, .38, 0, 360), L(.78, .2, .8, 1)]],
    "b": [[L(.25, 0, .25, 1, .25, .6, .5, .45, .78, .6, .75, .9, .5, 1, .25, .92)]],
    "c": [[L(.8, .2, .5, .05, .2, .3, .2, .7, .5, .95, .8, .8)], [L(.85, .15, .45, 0, .12, .35, .15, .75, .5, 1, .9, .85)]],
    "t": [[L(.45, 0, .45, .85, .6, 1, .8, .9), L(.15, .3, .8, .3)]],
    "+": [[L(.5, 0, .5, 1), L(0, .5, 1, .5)]],
    "(": [[L(.65, 0, .35, .25, .3, .5, .35, .75, .65, 1)], [L(.8, 0, .35, .2, .2, .5, .35, .8, .8, 1)]],
    ")": [[L(.35, 0, .65, .25, .7, .5, .65, .75, .35, 1)], [L(.2, 0, .65, .2, .8, .5, .65, .8, .2, 1)]],
    "/": [[L(.8, 0, .2, 1)]],
    "<": [[L(.85, .1, .15, .5, .85, .9)]],
    ">": [[L(.15, .1, .85, .5, .15, .9)]],
    "π": [[L(0, .15, 1, .15), L(.3, .15, .25, 1), L(.7, .15, .75, 1)]],
    "-": [[L(0, .5, 1, .5)]],
    "=": [[L(0, .3, 1, .3), L(0, .7, 1, .7)]],
  };
  /* tamaño real de cada símbolo: altura respecto a la línea (de la guía superior a la base) */
  const RELH = { x: .55, a: .55, c: .55, y: .85, t: .9, "+": .6, "<": .6, ">": .6, "π": .6, "(": 1.15, ")": 1.15 };
  const SYMBOLS = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "x", "y", "a", "b", "c", "t", "+", "-", "=", "(", ")", "/", "<", ">", "π"];
  /* todos los símbolos que entiende la pizarra, por grupos (para corregir y para enseñar);
     los que no tienen plantilla de serie se reconocen en cuanto el estudiante los enseña o los corrige una vez */
  const GROUPS = [
    ["cifras", "0123456789".split("")],
    ["letras", "abcdefghijkmnpqrstuvwxyz".split("")],
    ["griegas", "αβγδθλμφωπ".split("")],
    ["signos", ["+", "-", "·", "/", "^", "=", "<", ">", "≤", "≥", "(", ")", "|", "√", "∛", "²", "³", ".", ";", "∫", "'"]],
  ];
  const ALL = [...new Set(GROUPS.flatMap(g => g[1]))];

  /* ---------- muestras del estudiante (con su tamaño y proporción) ---------- */
  const KEY = "gda-tiza-v2";
  let user = {}; try { user = JSON.parse(localStorage.getItem(KEY) || "{}"); } catch (e) { user = {}; }
  let cache = null;
  const aspectOf = strokes => { const b = strokes.map(bb).reduce(union); return Math.max(.05, (b[1] - b[0]) / Math.max(1e-6, b[3] - b[2])); };
  function templates() {
    if (cache) return cache;
    cache = [];
    const add = (sym, v, mine, relh, asp) => cache.push({ sym, c: cloud(v), g: grid(v), n: v.length, asp: asp ?? aspectOf(v), relh: relh ?? RELH[sym] ?? 1, mine });
    for (const [sym, vars] of Object.entries(BASE)) vars.forEach(v => add(sym, v, false));
    for (const [sym, vars] of Object.entries(user)) vars.forEach(o => add(sym, o.s, true, o.relh, o.asp));
    return cache;
  }
  function train(sym, strokes, Href) {
    const b = strokes.map(bb).reduce(union), s = Math.max(b[1] - b[0], b[3] - b[2]) || 1;
    (user[sym] = user[sym] || []).push({ s: strokes.map(st => st.filter((p, i) => i % 2 === 0 || i === st.length - 1).map(([x, y]) => [+((x - b[0]) / s).toFixed(3), +((y - b[2]) / s).toFixed(3)])), relh: Href ? +((b[3] - b[2]) / Href).toFixed(3) : undefined, asp: +aspectOf(strokes).toFixed(3) });
    try { localStorage.setItem(KEY, JSON.stringify(user)); } catch (e) { }
    cache = null;
  }
  function forget() { user = {}; cache = null; try { localStorage.removeItem(KEY); } catch (e) { } }
  const samples = () => Object.values(user).reduce((n, v) => n + v.length, 0);

  let lastRank = [];                  // candidatos ordenados del último símbolo clasificado (para corregir)
  /* aprender de la propia letra: cada corrección o línea aceptada se guarda (como mucho 12 por símbolo) */
  function learn(sym, strokes, Href) {
    if (!sym || !strokes.length) return;
    train(sym, strokes, Href);
    if (user[sym].length > 12) { user[sym] = user[sym].slice(-12); try { localStorage.setItem(KEY, JSON.stringify(user)); } catch (e) { } cache = null; }
  }
  /* ---------- clasificar un grupo de trazos ---------- */
  function classify(strokes, Href) {
    const b = strokes.map(bb).reduce(union), w = b[1] - b[0], h = b[3] - b[2], relh = h / Href, asp = Math.max(.05, w / Math.max(1e-6, h));
    // rayas: «−» y «=» se reconocen por su geometría
    const flat = strokes.map(s => { const c = bb(s); return (c[3] - c[2]) < .32 * Math.max(c[1] - c[0], 1) && (c[1] - c[0]) > .2 * Href; });
    if (flat.every(Boolean)) { if (strokes.length === 1) { lastRank = ["-", "=", "1"]; return "-"; } if (strokes.length === 2) { lastRank = ["=", "-"]; return "="; } }
    // pesos medidos: la nube de puntos es la pista más clara, la malla ayuda, el tamaño decide casos
    // concretos (c frente a «(») y la proporción ancho/alto apenas, porque cada mano escribe más ancho o más estrecho
    const c = cloud(strokes), g = grid(strokes), score = {};
    for (const t of templates()) {
      if (t.sym === "-" || t.sym === "=") continue;
      const d = (match(c, t.c) + 1.2 * gridDist(g, t.g) + 1.6 * Math.abs(Math.log(Math.max(relh, .05) / t.relh)) + .15 * Math.abs(Math.log(asp / t.asp)) + .3 * Math.abs(strokes.length - t.n)) * (t.mine ? .93 : 1);
      if (score[t.sym] === undefined || d < score[t.sym]) score[t.sym] = d;
    }
    const rank = Object.keys(score).sort((p, q) => score[p] - score[q]); lastRank = rank;
    if (strokes.length === 2 && ["t", "1", "x", "+", "4", "7"].includes(rank[0])) {
      // palo con raya horizontal: al pie es el «1» con base, arriba es la «t»; si la raya cruza el palo por el centro, «+»
      const fl = strokes.map(bb).findIndex(c => (c[3] - c[2]) < Math.max(.3 * (c[1] - c[0]), .12 * Href) && (c[1] - c[0]) > (c[3] - c[2])), stick = strokes.map(bb).findIndex(c => (c[3] - c[2]) > 1.6 * (c[1] - c[0]));
      if (fl >= 0 && stick >= 0 && fl !== stick) { const c = bb(strokes[fl]), yr = ((c[2] + c[3]) / 2 - b[2]) / (h || 1); if (yr > .8) return "1"; if (yr < .45 && relh > .7) return "t"; }
    }
    if (strokes.length !== 1) return rank[0];
    // un solo trazo: la dirección decide entre recta (1, /), curva suave («(», «)», «c») y esquina (<, >)
    const f = shape(strokes[0]), DIR = ["1", "(", ")", "<", ">", "/", "c"], other = rank.find(s => !DIR.includes(s));
    if (f.vee && relh < 1.05) return f.dev < 0 ? "<" : ">";                       // dos tramos rectos en ángulo
    if (relh < .8 && f.dev < -.25 && f.turn < 1.75 && f.closed > .35 && !f.vee && ["c", "6", "(", "<", "0", "a"].includes(rank[0])) return "c";
    if (!DIR.includes(rank[0])) return rank[0];
    if (relh > .8) {
      if (Math.abs(f.dev) < .07 && f.turn < .6) return Math.abs(f.slope) > .35 ? "/" : "1";
      if (f.turn < .8 && Math.abs(f.dev) >= .07) return f.dev < 0 ? "(" : ")";
      return other;
    }
    if (Math.abs(f.dev) < .07 && f.turn < .6 && relh > .3) return Math.abs(f.slope) > .35 ? "/" : "1";
    if (f.dev < -.25 && f.turn < 1.75 && f.closed > .35) return "c";
    return other;
  }

  /* ---------- lectura de una línea ---------- */
  const median = a => { const s = a.slice().sort((p, q) => p - q); return s.length ? s[Math.floor(s.length / 2)] : 0; };
  function group(S, Href) {
    // en el orden en que se dibujaron: un trazo se une al grupo del anterior si se solapan,
    // o a cualquier grupo anterior si queda casi dentro de él (el palo del 4, la barra de la t)
    const groups = [];
    S.forEach((o, i) => {
      const ovr = g => { const ov = Math.min(g.b[1], o.b[1]) - Math.max(g.b[0], o.b[0]), wmin = Math.max(1, Math.min(g.b[1] - g.b[0], o.b[1] - o.b[0])); return ov / wmin; };
      const thin = A => A[1] - A[0] < .25 * Href, cIn = (A, B) => { const c = (A[0] + A[1]) / 2; return c > B[0] + .1 * (B[1] - B[0]) && c < B[1] - .1 * (B[1] - B[0]); };
      const last = groups[groups.length - 1];
      const ovAbs = g => Math.min(g.b[1], o.b[1]) - Math.max(g.b[0], o.b[0]), vSame = g => Math.min(g.b[3], o.b[3]) - Math.max(g.b[2], o.b[2]) > .6 * Math.min(g.b[3] - g.b[2], o.b[3] - o.b[2]);
      // dos curvas que se tocan sin solaparse, dibujadas seguidas, forman un símbolo: la «x» como «)(»
      const touch = g => g.s.length === 1 && ovAbs(g) > -.04 * Href && vSame(g) && (g.b[3] - g.b[2]) < .9 * Href && (o.b[3] - o.b[2]) < .9 * Href;
      if (last && last.idx.includes(i - 1) && (ovr(last) > .3 || touch(last) || (thin(o.b) && (cIn(o.b, last.b) || ovr(last) >= 0)) || (thin(last.b) && cIn(last.b, o.b)))) { last.s.push(o.s); last.b = union(last.b, o.b); last.idx.push(i); return; }
      const g = groups.find(g => ovr(g) > .6 && Math.abs((g.b[2] + g.b[3]) / 2 - (o.b[2] + o.b[3]) / 2) < .8 * Href);
      if (g) { g.s.push(o.s); g.b = union(g.b, o.b); g.idx.push(i); return; }
      groups.push({ s: [o.s], b: o.b.slice(), idx: [i] });
    });
    return groups;
  }
  /* modo casillas: un símbolo por casilla de la malla */
  function cellGroup(S, guide) {
    const m = new Map();
    for (const o of S) { const k = Math.floor(((o.b[0] + o.b[1]) / 2 - guide.x0) / guide.cell); if (!m.has(k)) m.set(k, { s: [], b: o.b.slice(), idx: [], gis: [] }); const g = m.get(k); g.s.push(o.s); g.b = union(g.b, o.b); g.gis.push(o.gi); }
    return [...m.values()];
  }
  function readLine(S, Href, guide, ctx) {
    const items = []; let rest = S.slice();
    const flatBar = o => { const w = o.b[1] - o.b[0], h = o.b[3] - o.b[2]; return w > 1.1 * Href && h < .25 * w; };
    for (const bar of S.filter(flatBar).sort((a, b) => (b.b[1] - b.b[0]) - (a.b[1] - a.b[0]))) {
      if (!rest.includes(bar)) continue;
      const mid = o => (o.b[0] + o.b[1]) / 2, yb = (bar.b[2] + bar.b[3]) / 2;
      const inside = o => o !== bar && rest.includes(o) && mid(o) > bar.b[0] && mid(o) < bar.b[1];
      const up = S.filter(o => inside(o) && o.b[3] < yb + 2), dn = S.filter(o => inside(o) && o.b[2] > yb - 2);
      if (up.length && dn.length) { rest = rest.filter(o => o !== bar && !up.includes(o) && !dn.includes(o)); items.push({ frac: true, b: [...up, ...dn, bar].map(o => o.b).reduce(union), num: up, den: dn }); }
    }
    const gs = ctx && ctx.boxed ? cellGroup(rest, ctx.boxed) : group(rest, Href);
    gs.forEach(g => { if (!g.gis) g.gis = g.idx.map(i => rest[i].gi); });
    items.push(...gs);
    items.sort((a, b) => (a.b[0] + a.b[1]) / 2 - (b.b[0] + b.b[1]) / 2);
    const normal = items.filter(i => !i.frac && i.b[3] - i.b[2] > .55 * Href);
    const base = guide ? guide.base : median((normal.length ? normal : items).map(i => i.b[3]));
    const midY = guide ? guide.mid : base - .5 * Href;
    let out = "", sup = "", prevCh = "";
    const flush = () => { if (sup) { out += "^" + (sup.length > 1 ? "(" + sup + ")" : sup); sup = ""; } };
    items.forEach((it, k) => {
      if (it.frac) { flush(); out += "(" + readLine(it.num, Href, null, ctx && { ...ctx, boxed: null }) + ")/(" + readLine(it.den, Href, null, ctx && { ...ctx, boxed: null }) + ")"; prevCh = ")"; return; }
      const w = it.b[1] - it.b[0], h = it.b[3] - it.b[2];
      // exponente: pequeño y con el pie por encima de la línea media; se mide con su propia escala (≈ 60 %)
      const raised = k > 0 && it.b[3] < midY + .08 * Href && h < .75 * Href;
      let ch = Math.max(w, h) < .16 * Href ? "·" : classify(it.s, raised ? .6 * Href : Href);
      const alts = ch === "·" ? ["·", "."] : [ch, ...lastRank.filter(c => c !== ch)].slice(0, 6);
      const key = it.gis && it.gis.length ? Math.min(...it.gis) : null, fixed = ctx && ctx.ov && key !== null && ctx.ov[key] !== undefined;
      if (fixed) ch = ctx.ov[key];
      if (ctx && ctx.items) ctx.items.push({ b: it.b, key, ch, alts, strokes: it.s, Href: raised ? .6 * Href : Href, fixed });
      const isSup = k > 0 && raised && !["-", "=", "·", "+", "<", ">", "≤", "≥", "²", "³", "^", ";", "'", "|"].includes(ch) && (sup || /[0-9a-zα-ω)]/i.test(prevCh));
      if (isSup) sup += ch; else { flush(); out += ch; }
      prevCh = ch;
    });
    flush();
    return out.replace(/(\d)·(\d)/g, "$1.$2");
  }
  function smooth(s) { if (s.length < 4) return s; return s.map((p, i) => i === 0 || i === s.length - 1 ? p : [(s[i - 1][0] + 2 * p[0] + s[i + 1][0]) / 4, (s[i - 1][1] + 2 * p[1] + s[i + 1][1]) / 4]); }
  /* guide: {top, mid, base, [x0, cell]} en píxeles de la zona de escritura (opcional);
     overrides: {índice del primer trazo del símbolo: carácter} con las correcciones del estudiante */
  function readDetailed(strokes, guide, overrides) {
    const ctx = { ov: overrides || {}, items: [], boxed: guide && guide.cell ? guide : null };
    const S = strokes.map((s, gi) => ({ s: smooth(s), b: bb(s), gi })).filter(o => o.s.length);
    if (!S.length) return { text: "", items: [] };
    let Href;
    const tall = S.map(o => o.b[3] - o.b[2]).filter((h, i) => h > 6 && h > .4 * (S[i].b[1] - S[i].b[0])).sort((p, q) => p - q);
    const est = tall.length ? tall[Math.floor(tall.length * .75)] : 30;
    if (guide) { Href = guide.base - guide.top; if (est > 1.6 * Href || est < .45 * Href) { Href = est; guide = null; } }
    else Href = est;
    return { text: readLine(S, Href, guide, ctx), items: ctx.items };
  }
  function read(strokes, guide) {
    strokes = strokes.filter(s => s.length).map(smooth);
    if (!strokes.length) return "";
    const S = strokes.map((s, gi) => ({ s, b: bb(s), gi }));
    let Href;
    const tall = S.map(o => o.b[3] - o.b[2]).filter((h, i) => h > 6 && h > .4 * (S[i].b[1] - S[i].b[0])).sort((p, q) => p - q);
    const est = tall.length ? tall[Math.floor(tall.length * .75)] : 30;
    if (guide) { Href = guide.base - guide.top; if (est > 1.6 * Href || est < .45 * Href) { Href = est; guide = null; } }   // si se escribe muy fuera de las guías, se mide la letra
    else Href = est;
    return readLine(S, Href, guide);
  }
  function breakdown(strokes, Href) {
    const b = strokes.map(bb).reduce(union), w = b[1] - b[0], h = b[3] - b[2], relh = h / Href, asp = Math.max(.05, w / Math.max(1e-6, h)), c = cloud(strokes), g = grid(strokes), best = {};
    for (const t of templates()) { if (t.sym === "-" || t.sym === "=") continue; const r = { p: match(c, t.c), g: gridDist(g, t.g), s: Math.abs(Math.log(Math.max(relh, .05) / t.relh)), a: Math.abs(Math.log(asp / t.asp)) }; if (!best[t.sym] || r.p + r.g < best[t.sym].p + best[t.sym].g) best[t.sym] = r; }
    return best;
  }
  /* diagnóstico: grupos con su lectura y sus medidas */
  function debug(strokes, guide) {
    strokes = strokes.filter(s => s.length).map(smooth);
    const S = strokes.map(s => ({ s, b: bb(s) })), Href = guide ? guide.base - guide.top : 30;
    return group(S, Href).sort((a, b) => (a.b[0] + a.b[1]) / 2 - (b.b[0] + b.b[1]) / 2).map(g => ({ ch: classify(g.s, Href), n: g.s.length, relh: +((g.b[3] - g.b[2]) / Href).toFixed(2), asp: +((g.b[1] - g.b[0]) / (g.b[3] - g.b[2])).toFixed(2), sh: g.s.length === 1 ? shape(g.s[0]) : null }));
  }
  return { read, readDetailed, classify, train, learn, forget, samples, SYMBOLS, GROUPS, ALL, BASE, debug, breakdown };
})();
