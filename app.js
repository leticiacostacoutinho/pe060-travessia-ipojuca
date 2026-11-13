// PE-060 · Travessia Urbana de Ipojuca — modelo 3D conceitual interativo
import * as THREE from 'three';
import { OrbitControls } from 'three/addons/OrbitControls.js';
import { Sky } from 'three/addons/Sky.js';
import { mergeGeometries } from 'three/addons/BufferGeometryUtils.js';

const QR_URL = window.QR_URL || '';
const V3 = THREE.Vector3;
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const lerp = (a, b, t) => a + (b - a) * t;
const smooth = (e0, e1, x) => { const t = clamp((x - e0) / (e1 - e0), 0, 1); return t * t * (3 - 2 * t); };
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
let R = mulberry32(60606);
const rnd = (a = 0, b = 1) => a + (b - a) * R();
const pick = a => a[Math.floor(R() * a.length)];
const SR = Math.random; // agentes (não determinístico)
const srnd = (a = 0, b = 1) => a + (b - a) * SR();
function hash2(x, y) { let h = Math.imul(x | 0, 374761393) + Math.imul(y | 0, 668265263); h = Math.imul(h ^ (h >>> 13), 1274126177); return ((h ^ (h >>> 16)) >>> 0) / 4294967295; }
function noise2(x, y) { const xi = Math.floor(x), yi = Math.floor(y), xf = x - xi, yf = y - yi; const u = xf * xf * (3 - 2 * xf), v = yf * yf * (3 - 2 * yf); return lerp(lerp(hash2(xi, yi), hash2(xi + 1, yi), u), lerp(hash2(xi, yi + 1), hash2(xi + 1, yi + 1), u), v); }
function fbm(x, y) { return noise2(x, y) * 0.5 + noise2(x * 2.1 + 7, y * 2.1) * 0.3 + noise2(x * 4.3, y * 4.3 + 3) * 0.2; }
const ldTxt = document.getElementById('ldTxt');

// ============================================================ Eixo da PE-060
// x = leste, -z = norte. u = estaca ao longo do eixo (sul → norte), s = afastamento lateral (+ leste)
function cxz(z) { return 12 * Math.sin(-z / 220) - 0.0003 * Math.max(0, z) ** 2; }
const cpts = []; for (let z = 330; z >= -340; z -= 10) cpts.push(new V3(cxz(z), 0, z));
const curve = new THREE.CatmullRomCurve3(cpts, false, 'centripetal');
const L = curve.getLength();
const NL = 1600, LP = new Float32Array(NL * 2), LR = new Float32Array(NL * 2);
for (let i = 0; i < NL; i++) {
  const t = i / (NL - 1), p = curve.getPointAt(t), T = curve.getTangentAt(t);
  const rx = -T.z, rz = T.x, l = Math.hypot(rx, rz);
  LP[2 * i] = p.x; LP[2 * i + 1] = p.z; LR[2 * i] = rx / l; LR[2 * i + 1] = rz / l;
}
function at(u, s = 0) {
  const f = clamp(u / L, 0, 1) * (NL - 1), i = Math.min(NL - 2, Math.floor(f)), t = f - i;
  const px = lerp(LP[2 * i], LP[2 * i + 2], t), pz = lerp(LP[2 * i + 1], LP[2 * i + 3], t);
  const rx = lerp(LR[2 * i], LR[2 * i + 2], t), rz = lerp(LR[2 * i + 1], LR[2 * i + 3], t);
  return [px + rx * s, pz + rz * s, rx, rz];
}
function yawAt(u, dir) { const r = at(u, 0); return Math.atan2(r[3] * dir, -r[2] * dir); }
function lateralOf(x, z) { const c = cxz(z), d = (cxz(z - 1) - cxz(z + 1)) / 2; return (x - c) / Math.sqrt(1 + d * d); }

const uA = 135, uB = Math.round(L - 135);       // trecho tratado (travessia urbana)
const SIG_U = Math.round(uA + 0.5 * (uB - uA));
const CROSS = [{ u: uA + 70, type: 'raised' }, { u: SIG_U, type: 'signal' }, { u: uB - 75, type: 'raised' }];
const BUS = [{ u: SIG_U + 38, side: 'E' }, { u: SIG_U - 42, side: 'W' }];
const BAYS = [[SIG_U + 26, SIG_U + 50, 'bus'], [uA + 105, uA + 135, 'park'], [uB - 140, uB - 112, 'park']];
const WZ = 90;
const CUTS = CROSS.map(c => [c.u - 4.6, c.u + 4.6]);
function subtract(a, b, cuts) { let out = [[a, b]]; for (const [c0, c1] of cuts) { const n = []; for (const [x0, x1] of out) { if (c1 <= x0 || c0 >= x1) { n.push([x0, x1]); continue; } if (c0 > x0) n.push([x0, c0]); if (c1 < x1) n.push([c1, x1]); } out = n; } return out.filter(r => r[1] - r[0] > 0.2); }

// ============================================================ Estado
const state = { phase: 'hoje', prog: 0.45, hour: 9.5, month: 2, weather: 'sol', labels: true, agents: true, anim: false, daySpeed: 0.35, fCars: 420, fPeds: 70, fBikes: 60, cam: 'aerea' };
const ufront = () => uA + state.prog * (uB - uA - WZ);
function isBuilt(u) { if (state.phase === 'op') return u >= uA && u <= uB; if (state.phase === 'obra') return u >= uA && u < ufront(); return false; }
function inWork(u) { if (state.phase !== 'obra') return false; const f = ufront(); return u >= f && u <= f + WZ; }
function roadY(u) {
  let y = 0;
  for (const c of CROSS) { if (c.type !== 'raised' || !isBuilt(c.u)) continue; const d = Math.abs(u - c.u); if (d < 3) y = 0.15; else if (d < 4.6) y = Math.max(y, 0.15 * (4.6 - d) / 1.6); }
  return y;
}

// ============================================================ Renderer / cena
const canvas = document.getElementById('c');
const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, powerPreference: 'high-performance' });
const isMobile = Math.min(innerWidth, innerHeight) < 700;
renderer.setPixelRatio(Math.min(devicePixelRatio, isMobile ? 1.5 : 1.75));
renderer.setSize(innerWidth, innerHeight);
renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 0.62;
renderer.outputColorSpace = THREE.SRGBColorSpace;
const scene = new THREE.Scene();
scene.fog = new THREE.FogExp2(0xb9c9d6, 0.0012);
const camera = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, 1, 7000);
const controls = new OrbitControls(camera, renderer.domElement);
controls.enableDamping = true; controls.dampingFactor = 0.08; controls.maxPolarAngle = Math.PI * 0.495; controls.minDistance = 2; controls.maxDistance = 1600;
controls.screenSpacePanning = false;
const ANISO = renderer.capabilities.getMaxAnisotropy();

// Céu
const sky = new Sky(); sky.scale.setScalar(6000); scene.add(sky);
const skyU = sky.material.uniforms;
skyU.turbidity.value = 6; skyU.rayleigh.value = 1.5; skyU.mieCoefficient.value = 0.005; skyU.mieDirectionalG.value = 0.8;
const pmrem = new THREE.PMREMGenerator(renderer);
const envScene = new THREE.Scene(); const sky2 = new Sky(); sky2.scale.setScalar(1000); envScene.add(sky2);
let envRT = null;

// Luzes
const sun = new THREE.DirectionalLight(0xffffff, 3);
sun.castShadow = true; const SMS = isMobile ? 2048 : 4096; sun.shadow.mapSize.set(SMS, SMS);
Object.assign(sun.shadow.camera, { left: -160, right: 160, top: 160, bottom: -160, near: 10, far: 1400 });
sun.shadow.camera.updateProjectionMatrix(); sun.shadow.bias = -0.0004; sun.shadow.normalBias = 0.35;
scene.add(sun, sun.target);
const hemi = new THREE.HemisphereLight(0xbcd6ff, 0x6b5a46, 0.9); scene.add(hemi);
const PL = []; for (let i = 0; i < 10; i++) { const p = new THREE.PointLight(0xfff1dc, 0, 34, 1.6); scene.add(p); PL.push(p); }

// ============================================================ Texturas procedurais
function ctex(size, draw, opts = {}) {
  const c = document.createElement('canvas'); c.width = c.height = size; const g = c.getContext('2d'); draw(g, size);
  const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.anisotropy = ANISO;
  if (opts.color !== false) t.colorSpace = THREE.SRGBColorSpace; return t;
}
function ctexWH(w, h, draw) { const c = document.createElement('canvas'); c.width = w; c.height = h; const g = c.getContext('2d'); draw(g, w, h); const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = ANISO; return t; }
function speck(g, s, n, cols, r0, r1, a0 = 0.35) { for (let i = 0; i < n; i++) { g.fillStyle = pick(cols); g.globalAlpha = rnd(a0, 1); const r = rnd(r0, r1); g.fillRect(rnd(0, s), rnd(0, s), r, r); } g.globalAlpha = 1; }
function blobs(g, s, n, cols, r0, r1, a = 0.25) { for (let i = 0; i < n; i++) { g.fillStyle = pick(cols); g.globalAlpha = a * rnd(0.4, 1); g.beginPath(); g.ellipse(rnd(0, s), rnd(0, s), rnd(r0, r1), rnd(r0, r1), rnd(0, 3), 0, 7); g.fill(); } g.globalAlpha = 1; }
const T = {};
T.asphNew = ctex(512, (g, s) => { g.fillStyle = '#353638'; g.fillRect(0, 0, s, s); blobs(g, s, 40, ['#2c2d2f', '#3d3e40'], 20, 70, 0.4); speck(g, s, 14000, ['#26272a', '#46474a', '#55565a', '#1f2022'], 1, 2.4); g.fillStyle = 'rgba(0,0,0,.08)'; for (const x of [0.22, 0.36, 0.64, 0.78]) g.fillRect(x * s - 14, 0, 28, s); });
T.asphOld = ctex(512, (g, s) => {
  g.fillStyle = '#5c5c5b'; g.fillRect(0, 0, s, s); blobs(g, s, 60, ['#525251', '#6a6a68', '#4a4a4a'], 15, 60, 0.45);
  speck(g, s, 16000, ['#4b4b4b', '#6e6e6c', '#7a7a78', '#3e3e3e'], 1, 2.6);
  for (let i = 0; i < 9; i++) { g.fillStyle = pick(['#444546', '#3b3c3d', '#4d4e4f']); g.globalAlpha = 0.85; g.save(); g.translate(rnd(0, s), rnd(0, s)); g.rotate(rnd(-0.2, 0.2)); g.fillRect(-rnd(15, 45), -rnd(15, 60), rnd(30, 90), rnd(30, 120)); g.restore(); }
  g.globalAlpha = 0.7; g.strokeStyle = '#2f2f2f'; g.lineWidth = 1.3; for (let i = 0; i < 26; i++) { g.beginPath(); let x = rnd(0, s), y = rnd(0, s); g.moveTo(x, y); for (let k = 0; k < 7; k++) { x += rnd(-18, 18); y += rnd(-18, 18); g.lineTo(x, y); } g.stroke(); }
  g.globalAlpha = 1; g.fillStyle = 'rgba(0,0,0,.10)'; for (const x of [0.2, 0.34, 0.66, 0.8]) g.fillRect(x * s - 16, 0, 32, s);
});
T.dirt = ctex(512, (g, s) => { g.fillStyle = '#a8673f'; g.fillRect(0, 0, s, s); blobs(g, s, 90, ['#94572f', '#b97a4c', '#7f4b2b', '#c08455', '#8b6a48'], 10, 55, 0.4); speck(g, s, 9000, ['#6e3f24', '#c99366', '#8d8d86', '#5c3a24'], 1, 3); blobs(g, s, 22, ['#6f7a3a', '#5d6b2f', '#83904a'], 4, 18, 0.55); });
T.grass = ctex(512, (g, s) => { g.fillStyle = '#5b7a33'; g.fillRect(0, 0, s, s); blobs(g, s, 120, ['#4e6c2a', '#6b8a3c', '#7c934a', '#46612a', '#8a8f4a'], 10, 50, 0.35); speck(g, s, 16000, ['#3f5a22', '#78963f', '#9aa95a', '#57722f'], 1, 2.2); });
T.paver = ctex(512, (g, s) => { g.fillStyle = '#8f8c86'; g.fillRect(0, 0, s, s); const bw = 32, bh = 16; for (let r = 0; r < s / bh; r++) for (let c = -1; c < s / bw + 1; c++) { const x = c * bw + (r % 2) * bw / 2; const v = rnd(-12, 12); g.fillStyle = `rgb(${190 + v},${187 + v},${179 + v})`; g.fillRect(x + 1, r * bh + 1, bw - 2, bh - 2); } speck(g, s, 6000, ['#a9a69f', '#cfccc4', '#9a978f'], 1, 2, 0.3); blobs(g, s, 10, ['#77746e'], 10, 40, 0.12); });
T.tactile = ctex(256, (g, s) => { g.fillStyle = '#d9b020'; g.fillRect(0, 0, s, s); g.fillStyle = '#e8c33a'; for (let i = 0; i < 4; i++) g.fillRect(i * 64 + 18, 0, 28, s); speck(g, s, 1500, ['#b89418', '#f0d055'], 1, 2, 0.3); });
T.bike = ctex(512, (g, s) => { g.fillStyle = '#9b3a30'; g.fillRect(0, 0, s, s); blobs(g, s, 40, ['#8a322a', '#a8463a'], 15, 60, 0.4); speck(g, s, 12000, ['#7d2b24', '#b4544a', '#6b6b6b'], 1, 2.2); });
T.concrete = ctex(256, (g, s) => { g.fillStyle = '#b7b4ac'; g.fillRect(0, 0, s, s); blobs(g, s, 30, ['#a7a49c', '#c6c3bb'], 8, 30, 0.35); speck(g, s, 4000, ['#9d9a92', '#d0cdc5'], 1, 2, 0.3); });
T.brick = ctex(512, (g, s) => { g.fillStyle = '#b3a08a'; g.fillRect(0, 0, s, s); const bw = 96, bh = 46; for (let r = 0; r < s / bh + 1; r++) for (let c = -1; c < s / bw + 1; c++) { const x = c * bw + (r % 2) * bw / 2; g.fillStyle = pick(['#a5502e', '#b25c36', '#9a4a2a', '#c06a40', '#a85a3a', '#8f4527']); g.fillRect(x + 3, r * bh + 3, bw - 5, bh - 5); } speck(g, s, 5000, ['#7a3a20', '#c98a66'], 1, 3, 0.3); });
T.plaster = ctex(256, (g, s) => { g.fillStyle = '#e9e7e1'; g.fillRect(0, 0, s, s); blobs(g, s, 40, ['#d8d5ce', '#f3f1ec', '#cfcac0'], 10, 40, 0.35); g.fillStyle = 'rgba(90,70,50,.10)'; g.fillRect(0, s * 0.85, s, s * 0.15); });
T.slab = ctex(256, (g, s) => { g.fillStyle = '#9c988f'; g.fillRect(0, 0, s, s); blobs(g, s, 30, ['#86827a', '#b0aca3', '#6e6b64'], 10, 50, 0.35); });
T.fibro = ctex(256, (g, s) => { g.fillStyle = '#a3a59f'; g.fillRect(0, 0, s, s); for (let i = 0; i < 16; i++) { g.fillStyle = i % 2 ? '#8c8e88' : '#b2b4ae'; g.fillRect(i * 16, 0, 8, s); } blobs(g, s, 20, ['#6f706b', '#4f5a46'], 10, 40, 0.25); });
T.portal = ctex(256, (g, s) => { g.fillStyle = '#8e3d2e'; g.fillRect(0, 0, s, s); for (let r = 0; r < 16; r++) for (let c = 0; c < 8; c++) { g.fillStyle = pick(['#9a4434', '#843629', '#a64d3a']); g.fillRect(c * 32 + (r % 2) * 16 + 1, r * 16 + 1, 30, 14); } });
T.glow = ctex(128, (g, s) => { const gr = g.createRadialGradient(s / 2, s / 2, 0, s / 2, s / 2, s / 2); gr.addColorStop(0, 'rgba(255,240,215,1)'); gr.addColorStop(0.4, 'rgba(255,225,180,.45)'); gr.addColorStop(1, 'rgba(255,210,160,0)'); g.fillStyle = gr; g.fillRect(0, 0, s, s); });
T.beam = ctexWH(64, 256, (g, w, h) => { const gr = g.createLinearGradient(0, h, 0, 0); gr.addColorStop(0, 'rgba(255,245,220,.9)'); gr.addColorStop(1, 'rgba(255,245,220,0)'); g.fillStyle = gr; g.beginPath(); g.moveTo(w * 0.35, h); g.lineTo(w * 0.65, h); g.lineTo(w, 0); g.lineTo(0, 0); g.fill(); });
T.clouds = ctex(512, (g, s) => { g.clearRect(0, 0, s, s); for (let i = 0; i < 260; i++) { const x = rnd(0, s), y = rnd(0, s), r = rnd(12, 60); const gr = g.createRadialGradient(x, y, 0, x, y, r); gr.addColorStop(0, 'rgba(255,255,255,.55)'); gr.addColorStop(1, 'rgba(255,255,255,0)'); g.fillStyle = gr; g.fillRect(x - r, y - r, 2 * r, 2 * r); } });
T.bikeIcon = ctexWH(128, 128, (g, w) => { g.strokeStyle = '#fff'; g.lineWidth = 7; g.beginPath(); g.arc(34, 82, 22, 0, 7); g.stroke(); g.beginPath(); g.arc(94, 82, 22, 0, 7); g.stroke(); g.beginPath(); g.moveTo(34, 82); g.lineTo(56, 50); g.lineTo(84, 50); g.lineTo(94, 82); g.moveTo(56, 50); g.lineTo(64, 82); g.lineTo(84, 50); g.moveTo(50, 42); g.lineTo(64, 42); g.moveTo(84, 50); g.lineTo(80, 36); g.stroke(); });
T.n30 = ctexWH(128, 256, (g, w, h) => { g.fillStyle = '#fff'; g.font = 'bold 150px Inter,Arial'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.save(); g.translate(w / 2, h / 2); g.scale(0.55, 1.5); g.fillText('30', 0, 0); g.restore(); });
function signTex(kind, txt) {
  return ctexWH(256, 256, (g, s) => {
    g.clearRect(0, 0, s, s);
    if (kind === 'lim') { g.fillStyle = '#fff'; g.beginPath(); g.arc(128, 128, 120, 0, 7); g.fill(); g.strokeStyle = '#d0262c'; g.lineWidth = 26; g.beginPath(); g.arc(128, 128, 106, 0, 7); g.stroke(); g.fillStyle = '#111'; g.font = 'bold 110px Inter,Arial'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(txt, 128, 136); }
    if (kind === 'ped' || kind === 'obra' || kind === 'bike-w') { g.fillStyle = kind === 'obra' ? '#f08a1c' : '#f4c418'; g.save(); g.translate(128, 128); g.rotate(Math.PI / 4); g.fillRect(-84, -84, 168, 168); g.strokeStyle = '#111'; g.lineWidth = 8; g.strokeRect(-76, -76, 152, 152); g.restore(); g.fillStyle = '#111'; g.textAlign = 'center'; g.textBaseline = 'middle';
      if (kind === 'ped') { g.beginPath(); g.arc(128, 70, 14, 0, 7); g.fill(); g.lineWidth = 14; g.strokeStyle = '#111'; g.lineCap = 'round'; g.beginPath(); g.moveTo(128, 92); g.lineTo(122, 140); g.lineTo(100, 180); g.moveTo(122, 140); g.lineTo(150, 178); g.moveTo(126, 104); g.lineTo(100, 126); g.moveTo(126, 104); g.lineTo(156, 122); g.stroke(); }
      else if (kind === 'obra') { g.font = 'bold 46px Inter,Arial'; g.fillText(txt || 'OBRAS', 128, 132); }
      else { g.font = 'bold 34px Inter,Arial'; g.fillText('CICLISTAS', 128, 132); } }
    if (kind === 'info') { g.fillStyle = '#1f5fa8'; g.fillRect(8, 40, 240, 176); g.strokeStyle = '#fff'; g.lineWidth = 6; g.strokeRect(16, 48, 224, 160); g.fillStyle = '#fff'; g.textAlign = 'center'; g.textBaseline = 'middle'; const ls = txt.split('|'); g.font = 'bold 30px Inter,Arial'; ls.forEach((l, i) => g.fillText(l, 128, 128 + (i - (ls.length - 1) / 2) * 38)); }
    if (kind === 'bike') { g.fillStyle = '#1f5fa8'; g.beginPath(); g.arc(128, 128, 118, 0, 7); g.fill(); g.strokeStyle = '#fff'; g.lineWidth = 8; g.beginPath(); g.arc(80, 150, 34, 0, 7); g.stroke(); g.beginPath(); g.arc(176, 150, 34, 0, 7); g.stroke(); g.beginPath(); g.moveTo(80, 150); g.lineTo(112, 100); g.lineTo(158, 100); g.lineTo(176, 150); g.moveTo(112, 100); g.lineTo(128, 150); g.lineTo(158, 100); g.stroke(); }
    if (kind === 'bus') { g.fillStyle = '#1f5fa8'; g.fillRect(28, 28, 200, 200); g.fillStyle = '#fff'; g.fillRect(64, 70, 128, 96); g.fillStyle = '#1f5fa8'; g.fillRect(76, 82, 104, 40); g.fillStyle = '#fff'; g.beginPath(); g.arc(88, 178, 14, 0, 7); g.arc(168, 178, 14, 0, 7); g.fill(); }
    if (kind === 'pare') { g.fillStyle = txt === 'SIGA' ? '#1f9a4a' : '#c8242b'; g.beginPath(); for (let i = 0; i < 8; i++) { const a = Math.PI / 8 + i * Math.PI / 4; g.lineTo(128 + 118 * Math.cos(a), 128 + 118 * Math.sin(a)); } g.fill(); g.fillStyle = '#fff'; g.font = 'bold 64px Inter,Arial'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(txt, 128, 132); }
  });
}
function wideSign(lines, bg = '#1d6b3a', w = 1024, h = 256) { return ctexWH(w, h, (g) => { g.fillStyle = bg; g.fillRect(0, 0, w, h); g.strokeStyle = '#fff'; g.lineWidth = 10; g.strokeRect(14, 14, w - 28, h - 28); g.fillStyle = '#fff'; g.textAlign = 'center'; g.textBaseline = 'middle'; lines.forEach((l, i) => { g.font = `bold ${l[1]}px Inter,Arial`; g.fillText(l[0], w / 2, h / 2 + (i - (lines.length - 1) / 2) * (l[1] * 1.15)); }); }); }
function pedLampTex(green) { return ctexWH(128, 128, (g, s) => { g.fillStyle = '#111'; g.fillRect(0, 0, s, s); g.fillStyle = green ? '#3cff7a' : '#ff3b2f'; if (green) { g.beginPath(); g.arc(64, 26, 11, 0, 7); g.fill(); g.lineWidth = 12; g.strokeStyle = g.fillStyle; g.lineCap = 'round'; g.beginPath(); g.moveTo(64, 44); g.lineTo(60, 78); g.lineTo(42, 110); g.moveTo(60, 78); g.lineTo(84, 108); g.moveTo(62, 54); g.lineTo(40, 70); g.moveTo(62, 54); g.lineTo(88, 66); g.stroke(); } else { g.fillRect(44, 34, 40, 56); for (let i = 0; i < 4; i++) g.fillRect(44 + i * 10, 18, 8, 20); g.fillRect(28, 56, 18, 12); } }); }
const SHOPNAMES = ['MERCADINHO', 'LAVA JATO', 'MAT. DE CONSTRUÇÃO', 'AÇAÍ & LANCHES', 'OFICINA', 'BAR DO ALTO', 'FARMÁCIA', 'PADARIA', 'CONVENIÊNCIA', 'ASSISTÊNCIA TÉCNICA', 'SALÃO', 'DEPÓSITO'];
const shopTex = SHOPNAMES.map((n, i) => ctexWH(512, 96, (g, w, h) => { const bgs = ['#c8242b', '#1f5fa8', '#f2c230', '#1f8a4a', '#6a2d8a', '#e46b1c', '#0e7c86', '#333']; const bg = bgs[i % bgs.length]; g.fillStyle = bg; g.fillRect(0, 0, w, h); g.fillStyle = bg === '#f2c230' ? '#222' : '#fff'; g.font = 'bold 46px Inter,Arial'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(n, w / 2, h / 2 + 2); }));

// ============================================================ Materiais
const MS = (o) => new THREE.MeshStandardMaterial(o);
const M = {
  asphNew: MS({ map: T.asphNew, roughness: 0.9 }), asphOld: MS({ map: T.asphOld, roughness: 0.95 }),
  dirt: MS({ map: T.dirt, roughness: 1 }), grass: MS({ map: T.grass, roughness: 1 }), paver: MS({ map: T.paver, roughness: 0.85 }),
  tactile: MS({ map: T.tactile, roughness: 0.8 }), bike: MS({ map: T.bike, roughness: 0.85 }), concrete: MS({ map: T.concrete, roughness: 0.9 }),
  curb: MS({ map: T.concrete, color: 0xe6e4de, roughness: 0.85, side: THREE.DoubleSide }), portal: MS({ map: T.portal, roughness: 0.85 }),
  white: MS({ color: 0xf2f2ee, roughness: 0.6, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2 }),
  yellow: MS({ color: 0xf0b41c, roughness: 0.6, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2 }),
  whiteOld: MS({ color: 0xd9d8d2, roughness: 0.8, transparent: true, opacity: 0.45, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2 }),
  yellowOld: MS({ color: 0xd9a63a, roughness: 0.8, transparent: true, opacity: 0.5, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2 }),
  vc: MS({ vertexColors: true, roughness: 0.85 }), vcMetal: MS({ vertexColors: true, roughness: 0.45, metalness: 0.55 }),
  brick: MS({ map: T.brick, vertexColors: true, roughness: 0.95 }), plaster: MS({ map: T.plaster, vertexColors: true, roughness: 0.95 }),
  slab: MS({ map: T.slab, vertexColors: true, roughness: 0.95 }), fibro: MS({ map: T.fibro, vertexColors: true, roughness: 0.8, side: THREE.DoubleSide }),
  glass: MS({ color: 0x24303a, roughness: 0.12, metalness: 0.7 }), winLit: MS({ color: 0x000000, emissive: 0xffc77a, emissiveIntensity: 1.6 }),
  carBody: MS({ vertexColors: true, roughness: 0.32, metalness: 0.45 }), head: MS({ color: 0xfffbe8, emissive: 0xfff2cc, emissiveIntensity: 0.2 }),
  tail: MS({ color: 0x5a0a0a, emissive: 0xff1a10, emissiveIntensity: 0.15 }), brake: MS({ color: 0x8a0e0e, emissive: 0xff1a10, emissiveIntensity: 3 }),
  beam: new THREE.MeshBasicMaterial({ map: T.beam, transparent: true, opacity: 0, blending: THREE.AdditiveBlending, depthWrite: false, fog: false }),
  glow: new THREE.MeshBasicMaterial({ map: T.glow, transparent: true, opacity: 0, blending: THREE.AdditiveBlending, depthWrite: false, color: 0xfff0d8 }),
  glowOld: new THREE.MeshBasicMaterial({ map: T.glow, transparent: true, opacity: 0, blending: THREE.AdditiveBlending, depthWrite: false, color: 0xffb35c }),
  lampLED: MS({ color: 0xeeeeee, emissive: 0xfff4e0, emissiveIntensity: 0 }), lampOld: MS({ color: 0xddccaa, emissive: 0xffa040, emissiveIntensity: 0 }),
  human: MS({ vertexColors: true, roughness: 0.9 }), trunk: MS({ color: 0x5b4632, roughness: 1 }),
  crown: MS({ color: 0xffffff, roughness: 0.95, flatShading: true }), frond: MS({ color: 0xffffff, roughness: 0.9, side: THREE.DoubleSide }),
  wire: new THREE.LineBasicMaterial({ color: 0x1c1c1c, transparent: true, opacity: 0.8 }),
  terrain: MS({ map: T.grass, vertexColors: true, roughness: 1 }),
};
const ROADMATS = [M.asphNew, M.asphOld, M.paver, M.bike, M.concrete, M.dirt, M.tactile, M.portal];
ROADMATS.forEach(m => { m.userData.r0 = m.roughness; });
function sigMats() { const mk = (c) => MS({ color: 0x111111, emissive: c, emissiveIntensity: 0.04, roughness: 0.4 }); return { r: mk(0xff2a1a), y: mk(0xffb01a), g: mk(0x2aff7a), pr: MS({ map: pedLampTex(false), emissive: 0xffffff, emissiveMap: pedLampTex(false), emissiveIntensity: 0.05 }), pg: MS({ map: pedLampTex(true), emissive: 0xffffff, emissiveMap: pedLampTex(true), emissiveIntensity: 0.05 }) }; }
const SIGM = sigMats(), SIGT = sigMats();
const VCKEYS = new Set(['vc', 'vcMetal', 'brick', 'plaster', 'slab', 'fibro']);

// ============================================================ Geometria
function prepGeo(g, key, color) {
  if (!g.attributes.normal) g.computeVertexNormals();
  if (!g.attributes.uv) g.setAttribute('uv', new THREE.BufferAttribute(new Float32Array(g.attributes.position.count * 2), 2));
  if (VCKEYS.has(key) || color !== undefined) { if (!g.attributes.color || color !== undefined) { const c = new THREE.Color(color ?? 0xffffff); const n = g.attributes.position.count, a = new Float32Array(n * 3); for (let i = 0; i < n; i++) { a[3 * i] = c.r; a[3 * i + 1] = c.g; a[3 * i + 2] = c.b; } g.setAttribute('color', new THREE.BufferAttribute(a, 3)); } }
  else if (g.attributes.color) g.deleteAttribute('color');
  for (const k of Object.keys(g.attributes)) if (!['position', 'normal', 'uv', 'color'].includes(k)) g.deleteAttribute(k);
  return g;
}
class Bucket {
  constructor() { this.m = new Map(); }
  add(key, g, color) { prepGeo(g, key, color); if (!this.m.has(key)) this.m.set(key, []); this.m.get(key).push(g); }
  flush(group, { cast = false, receive = true, castKeys = [] } = {}) {
    for (const [k, list] of this.m) {
      const anyNI = list.some(g => !g.index); const L2 = anyNI ? list.map(g => g.index ? g.toNonIndexed() : g) : list;
      const geo = mergeGeometries(L2, false); if (!geo) { console.warn('merge fail', k); continue; }
      const mesh = new THREE.Mesh(geo, M[k]); mesh.castShadow = cast || castKeys.includes(k); mesh.receiveShadow = receive; group.add(mesh);
    }
    this.m.clear();
  }
}
function ribbon(u0, u1, sA, sB, o = {}) {
  const step = o.step || 2, n = Math.max(1, Math.ceil((u1 - u0) / step)), pos = [], uv = [], idx = [];
  const tS = o.tileS || 1, tU = o.tileU || 1;
  for (let i = 0; i <= n; i++) {
    const u = u0 + (u1 - u0) * i / n; const a = o.sAFn ? o.sAFn(u) : sA, b = o.sBFn ? o.sBFn(u) : sB;
    for (const s of [a, b]) { const p = at(u, s); const y = o.yFn ? o.yFn(u, s, p[0], p[1]) : (o.y || 0); pos.push(p[0], y, p[1]); uv.push((o.uvS ? s - a : s) / tS, u / tU); }
    if (i < n) { const j = i * 2; idx.push(j, j + 1, j + 2, j + 1, j + 3, j + 2); }
  }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); g.setIndex(idx); g.computeVertexNormals(); return g;
}
function wallR(u0, u1, s, y0Fn, y1Fn, step = 2) {
  const n = Math.max(1, Math.ceil((u1 - u0) / step)), pos = [], uv = [], idx = [];
  for (let i = 0; i <= n; i++) { const u = u0 + (u1 - u0) * i / n, p = at(u, s); const a = typeof y0Fn === 'function' ? y0Fn(u) : y0Fn, b = typeof y1Fn === 'function' ? y1Fn(u) : y1Fn; pos.push(p[0], a, p[1], p[0], b, p[1]); uv.push(u / 2, 0, u / 2, (b - a) / 2); if (i < n) { const j = i * 2; idx.push(j, j + 2, j + 1, j + 1, j + 2, j + 3); } }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); g.setIndex(idx); g.computeVertexNormals(); return g;
}
const _m4 = new THREE.Matrix4(), _q = new THREE.Quaternion(), _e = new THREE.Euler();
function placeMat(u, s, y, yawOff = 0, dir = 1, scale = 1) { const p = at(u, s); _e.set(0, yawAt(u, dir) + yawOff, 0); _q.setFromEuler(_e); return new THREE.Matrix4().compose(new V3(p[0], y, p[1]), _q, new V3(scale, scale, scale)); }
function boxUV(w, h, d, tile = 1) { const g = new THREE.BoxGeometry(w, h, d); const uv = g.attributes.uv; const dims = [[d, h], [d, h], [w, d], [w, d], [w, h], [w, h]]; for (let f = 0; f < 6; f++) for (let k = 0; k < 4; k++) { const i = f * 4 + k; uv.setXY(i, uv.getX(i) * dims[f][0] / tile, uv.getY(i) * dims[f][1] / tile); } return g; }
function box(w, h, d, x = 0, y = 0, z = 0) { const g = new THREE.BoxGeometry(w, h, d); g.translate(x, y, z); return g; }
function cyl(r0, r1, h, seg, x = 0, y = 0, z = 0) { const g = new THREE.CylinderGeometry(r0, r1, h, seg); g.translate(x, y + h / 2, z); return g; }
const tf = (g, m) => { g.applyMatrix4(m); return g; };

// ============================================================ Terreno
function terrainH(x, z) {
  const s = lateralOf(x, z); let h = -0.04;
  if (s < -11.5) { const d = -11.5 - s; h = d < 4 ? d * 0.95 : 3.8 + 42 * (1 - Math.exp(-(d - 4) / 55)); if (d > 8) h += (fbm(x * 0.03, z * 0.03) - 0.5) * 4 * smooth(8, 30, d); }
  else if (s > 9.6) { const d = s - 9.6; h = -0.35 * smooth(0, 12, d) + (fbm(x * 0.02 + 5, z * 0.02) - 0.5) * 1.6 * smooth(10, 40, d); if (d > 80) h += 6 * smooth(80, 300, d) * fbm(x * 0.01, z * 0.01); }
  const hill = 95 * Math.exp(-(((x + 60) / 300) ** 2 + ((z + 690) / 210) ** 2)); h += hill * smooth(13, 40, Math.abs(s + 1));
  if (z > 340 || z < -350) h += 0; return h;
}
function buildTerrain() {
  const W = 1100, H = 1500, g = new THREE.PlaneGeometry(W, H, 240, 330); g.rotateX(-Math.PI / 2); g.translate(0, 0, -220);
  const p = g.attributes.position, uv = g.attributes.uv, col = new Float32Array(p.count * 3);
  const cG = new THREE.Color(), grass = new THREE.Color('#ffffff'), lat = new THREE.Color('#d08a5a'), dark = new THREE.Color('#9fa48a'), field = new THREE.Color('#dfe8b0');
  for (let i = 0; i < p.count; i++) {
    const x = p.getX(i), z = p.getZ(i), y = terrainH(x, z); p.setY(i, y); uv.setXY(i, x / 9, z / 9);
    const s = lateralOf(x, z); cG.copy(grass);
    if (s < -11.5 && s > -16.5) cG.lerp(lat, 0.85);
    else if (s < -16.5 && s > -115) cG.lerp(dark, 0.45 + 0.3 * fbm(x * 0.05, z * 0.05));
    else if (s > -11.5 && s < 9.6) cG.lerp(lat, 0.5);
    else if (s > 40) cG.lerp(field, 0.25 * fbm(x * 0.02, z * 0.02));
    const n = 0.85 + 0.3 * fbm(x * 0.08, z * 0.08); col[3 * i] = cG.r * n; col[3 * i + 1] = cG.g * n; col[3 * i + 2] = cG.b * n;
  }
  g.setAttribute('color', new THREE.BufferAttribute(col, 3)); g.computeVertexNormals();
  const m = new THREE.Mesh(g, M.terrain); m.receiveShadow = true; return m;
}

// ============================================================ Árvores (instanciadas)
const crownGeos = [0, 1, 2].map(k => { const g = new THREE.IcosahedronGeometry(1, 1); const p = g.attributes.position; for (let i = 0; i < p.count; i++) { const v = new V3().fromBufferAttribute(p, i); const n = 0.78 + 0.4 * hash2(Math.round(v.x * 50 + k * 7), Math.round(v.y * 50 + v.z * 30)); p.setXYZ(i, v.x * n, v.y * n * 0.85, v.z * n); } g.computeVertexNormals(); return g; });
const frondGeo = (() => { const parts = []; for (let i = 0; i < 11; i++) { const a = i / 11 * Math.PI * 2; const pos = [], idx = []; const segs = 6; for (let k = 0; k <= segs; k++) { const t = k / segs, r = t * 3.6, y = 0.55 * Math.sin(t * 2.2) - t * t * 1.6, w = 0.42 * Math.sin(Math.PI * Math.min(1, t * 1.15)) + 0.05; const cx = Math.cos(a) * r, cz = Math.sin(a) * r, nx = -Math.sin(a) * w, nz = Math.cos(a) * w; pos.push(cx - nx, y, cz - nz, cx + nx, y - 0.08, cz + nz); if (k < segs) { const j = k * 2; idx.push(j, j + 1, j + 2, j + 1, j + 3, j + 2); } } const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals(); parts.push(g); } return mergeGeometries(parts); })();
const bananaGeo = (() => { const parts = []; for (let i = 0; i < 7; i++) { const a = i / 7 * Math.PI * 2 + 0.3; const pos = [], idx = []; for (let k = 0; k <= 4; k++) { const t = k / 4, r = t * 2.0, y = 0.9 * Math.sin(t * 1.6) - t * t * 0.7, w = 0.45 * Math.sin(Math.PI * Math.min(1, t * 1.05)) + 0.04; const cx = Math.cos(a) * r, cz = Math.sin(a) * r, nx = -Math.sin(a) * w, nz = Math.cos(a) * w; pos.push(cx - nx, y, cz - nz, cx + nx, y, cz + nz); if (k < 4) { const j = k * 2; idx.push(j, j + 1, j + 2, j + 1, j + 3, j + 2); } } const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setIndex(idx); g.computeVertexNormals(); parts.push(g); } return mergeGeometries(parts); })();
const TREECOL = { oiti: ['#2f5a24', '#36652a', '#2a5020'], mango: ['#2d4f22', '#3b6b2c', '#27461d'], ipe: ['#e6c22c', '#f0cf3c', '#d7b020'], young: ['#4f8a34', '#5b9a3c'], palm: ['#5f7f35', '#6b8a3a', '#4f6e2c'], banana: ['#5e8f3a', '#6fa043'] };
function makeTrees(list, group) {
  const tr = [], cr = [[], [], []], fr = [], ba = [];
  for (const t of list) {
    if (t.type === 'palm') { const h = t.h || rnd(7, 12); tr.push({ x: t.x, y: t.y, z: t.z, sx: 0.22, sy: h, tilt: rnd(-0.08, 0.08), rot: rnd(0, 6) }); fr.push({ x: t.x + Math.sin(tr[tr.length - 1].tilt) * h, y: t.y + h, z: t.z, s: rnd(0.85, 1.15), rot: rnd(0, 6), c: pick(TREECOL.palm) }); continue; }
    if (t.type === 'banana') { const h = rnd(2.2, 3.4); tr.push({ x: t.x, y: t.y, z: t.z, sx: 0.16, sy: h, tilt: 0, rot: 0, green: true }); ba.push({ x: t.x, y: t.y + h, z: t.z, s: rnd(0.9, 1.3), rot: rnd(0, 6), c: pick(TREECOL.banana) }); continue; }
    const sc = t.s || 1, h = (t.type === 'young' ? 2.4 : rnd(2.6, 3.6)) * sc, R0 = (t.type === 'mango' ? rnd(3.2, 4.6) : t.type === 'young' ? 1.3 : rnd(2.4, 3.2)) * sc;
    tr.push({ x: t.x, y: t.y, z: t.z, sx: 0.28 * sc * (t.type === 'mango' ? 1.6 : 1), sy: h + R0 * 0.5, tilt: 0, rot: 0 });
    const cols = TREECOL[t.type] || TREECOL.oiti; const nb = t.type === 'young' ? 1 : 3;
    for (let k = 0; k < nb; k++) { const a = rnd(0, 6.28), d = k === 0 ? 0 : R0 * 0.45; cr[k % 3].push({ x: t.x + Math.cos(a) * d, y: t.y + h + R0 * (k === 0 ? 0.55 : 0.35), z: t.z + Math.sin(a) * d, s: R0 * (k === 0 ? 1 : 0.7), rot: rnd(0, 6), c: pick(cols) }); }
  }
  const m4 = new THREE.Matrix4(), q = new THREE.Quaternion(), e = new THREE.Euler(), col = new THREE.Color();
  if (tr.length) { const g = new THREE.CylinderGeometry(0.6, 1, 1, 7); g.translate(0, 0.5, 0); const im = new THREE.InstancedMesh(g, M.trunk, tr.length); tr.forEach((t, i) => { e.set(0, t.rot, t.tilt); q.setFromEuler(e); m4.compose(new V3(t.x, t.y, t.z), q, new V3(t.sx, t.sy, t.sx)); im.setMatrixAt(i, m4); im.setColorAt(i, col.set(t.green ? '#8aa05a' : '#ffffff')); }); im.castShadow = true; im.receiveShadow = true; group.add(im); }
  cr.forEach((list2, k) => { if (!list2.length) return; const im = new THREE.InstancedMesh(crownGeos[k], M.crown, list2.length); list2.forEach((c, i) => { e.set(0, c.rot, 0); q.setFromEuler(e); m4.compose(new V3(c.x, c.y, c.z), q, new V3(c.s, c.s, c.s)); im.setMatrixAt(i, m4); im.setColorAt(i, col.set(c.c)); }); im.castShadow = true; im.receiveShadow = true; group.add(im); });
  for (const [geo, list2] of [[frondGeo, fr], [bananaGeo, ba]]) { if (!list2.length) continue; const im = new THREE.InstancedMesh(geo, M.frond, list2.length); list2.forEach((c, i) => { e.set(0, c.rot, 0); q.setFromEuler(e); m4.compose(new V3(c.x, c.y, c.z), q, new V3(c.s, c.s, c.s)); im.setMatrixAt(i, m4); im.setColorAt(i, col.set(c.c)); }); im.castShadow = true; group.add(im); }
}
function treeAt(u, s, type, extra = {}) { const p = at(u, s); return { x: p[0], z: p[1], y: extra.y ?? terrainH(p[0], p[1]), type, ...extra }; }

// ============================================================ Cenário compartilhado (casas, postes, vegetação)
const HOUSES = []; const OLD_LAMPS = []; const POLES = [];
const PLASTER = ['#efe9dc', '#f2e2b0', '#cfe3e8', '#d9ecd0', '#f0d0c8', '#e8d9b8', '#c7d6e8', '#f5f1e6', '#e3c9a8', '#a8d5c2', '#f4f4f2', '#e9c46a'];
function addHouse(B, u, sC, w, d, side, opt = {}) {
  const fsign = side === 'W' ? 1 : -1;
  const pC = at(u, sC), pF = at(u, sC + fsign * d / 2), pBk = at(u, sC - fsign * d / 2);
  const yF = terrainH(pF[0], pF[1]), yC = terrainH(pC[0], pC[1]), yBk = terrainH(pBk[0], pBk[1]);
  const base = Math.min(yF, yC, yBk) - 0.4, floorY = opt.floorY ?? Math.max(yF, (yF + yC) / 2) + 0.1;
  const floors = opt.floors || (R() < 0.42 ? 1 : R() < 0.75 ? 2 : 3), fh = opt.fh || 2.9;
  const top = floorY + floors * fh, H = top - base;
  // base: X = tangente*fsign, Z = face para a via
  const rx = pC[2] * fsign, rz = pC[3] * fsign; const tx = rz, tz = -rx;
  const m = new THREE.Matrix4().makeBasis(new V3(tx, 0, tz), new V3(0, 1, 0), new V3(rx, 0, rz)); m.setPosition(pC[0], 0, pC[1]);
  const brick = opt.brick ?? (R() < 0.5);
  const wall = boxUV(w, H, d, brick ? 1 : 2); wall.translate(0, base + H / 2, 0); B.add(brick ? 'brick' : 'plaster', tf(wall, m), brick ? pick(['#ffffff', '#f2e6dc', '#e8d8cc']) : (opt.color || pick(PLASTER)));
  const roofT = opt.roof || (R() < 0.55 ? 'slab' : 'fibro');
  if (roofT === 'slab') { const r = boxUV(w + 0.25, 0.2, d + 0.25, 3); r.translate(0, top + 0.1, 0); B.add('slab', tf(r, m), pick(['#ffffff', '#d8d4cc', '#c4c0b8'])); if (R() < 0.6) { const t = cyl(0.55, 0.55, 0.75, 12, rnd(-w / 3, w / 3), top + 0.2, rnd(-d / 3, d / 3)); B.add('vc', tf(t, m), '#2f6fb6'); } if (R() < 0.3) { const pp = boxUV(w + 0.25, 0.9, 0.12, 2); pp.translate(0, top + 0.55, d / 2 + 0.06); B.add(brick ? 'brick' : 'plaster', tf(pp, m), '#ffffff'); } }
  else { const rh = d * 0.12, ov = 0.35; const pos = [-w / 2 - ov, top, -d / 2 - ov, w / 2 + ov, top, -d / 2 - ov, w / 2 + ov, top + rh, 0, -w / 2 - ov, top + rh, 0, -w / 2 - ov, top, d / 2 + ov, w / 2 + ov, top, d / 2 + ov]; const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute([0, 0, w / 2, 0, w / 2, d / 4, 0, d / 4, 0, d / 2, w / 2, d / 2], 2)); g.setIndex([0, 3, 1, 1, 3, 2, 4, 5, 3, 5, 2, 3]); g.computeVertexNormals(); B.add('fibro', tf(g, m), pick(['#ffffff', '#c9cbc4', '#b07a5a', '#9fb0c0'])); if (R() < 0.35) { const t = cyl(0.5, 0.5, 0.7, 12, rnd(-w / 3, w / 3), top + rh * 0.4, rnd(-d / 4, d / 4)); B.add('vc', tf(t, m), '#2f6fb6'); } }
  // janelas/portas na fachada frontal (+Z) e posterior
  const nWin = Math.max(1, Math.floor((w - 0.8) / 2.3));
  for (let f = 0; f < floors; f++) for (let k = 0; k < nWin; k++) {
    const x = -w / 2 + (k + 0.5) * w / nWin, y = floorY + f * fh + 1.45;
    if (f === 0 && k === 0 && !opt.shop) { const dr = new THREE.PlaneGeometry(0.9, 2.1); dr.translate(x, floorY + 1.05, d / 2 + 0.03); B.add('vc', tf(dr, m), pick(['#5a3a24', '#3b4a5a', '#7a2a22', '#2e5a3a'])); continue; }
    if (opt.shop && f === 0) continue;
    const wi = new THREE.PlaneGeometry(1.0, 1.05); wi.translate(x, y, d / 2 + 0.03); const g2 = tf(wi, m); B.add('glassK', g2); if (R() < 0.38) { const wl = new THREE.PlaneGeometry(0.92, 0.97); wl.translate(x, y, d / 2 + 0.045); B.add('winLitK', tf(wl, m)); }
    if (R() < 0.5) { const wb = new THREE.PlaneGeometry(1.0, 1.05); wb.rotateY(Math.PI); wb.translate(x, y, -d / 2 - 0.03); B.add('glassK', tf(wb, m)); }
  }
  if (opt.shop) { const rd = new THREE.PlaneGeometry(Math.min(w - 1, 4.2), 2.7); rd.translate(0, floorY + 1.35, d / 2 + 0.03); B.add('vcMetal', tf(rd, m), pick(['#8e949a', '#6f7a84', '#a4a9ae'])); }
  HOUSES.push({ u, sC, w, d, side, x: pC[0], z: pC[1], rx, rz, tx, tz, top, floorY, shop: !!opt.shop });
  return { m, top, floorY };
}
M.glassK = M.glass; M.winLitK = M.winLit;
function buildShared() {
  const g = new THREE.Group(), B = new Bucket(), BL = new Bucket(); const trees = [];
  g.add(buildTerrain());
  // encosta oeste — Rurópolis 2 / Alto São João
  for (let row = 0; row < 11; row++) {
    let u = rnd(0, 8) - 10;
    while (u < L + 20) {
      const w = rnd(4.8, 8.2), d = rnd(6, 9.5), s0 = -12.6 - row * 10.2 - rnd(0, 1.5), sC = s0 - d / 2;
      const pc = at(u + w / 2, sC);
      if (Math.abs(sC + 72) < 5.5 || (pc[1] < -200 && row > 4) || (pc[1] < -300) || R() < 0.08) { if (R() < 0.6) trees.push(treeAt(u + w / 2, sC, pick(['mango', 'banana', 'banana', 'palm', 'oiti']))); u += w + rnd(1, 4); continue; }
      addHouse(B, u + w / 2, sC, w, d, 'W'); u += w + rnd(0.15, 1.6);
      if (R() < 0.12) trees.push(treeAt(u - 0.5, sC - d / 2 - 1, pick(['banana', 'palm', 'mango'])));
    }
  }
  // R. Alto São João (rua da encosta)
  B.add('concrete', ribbon(0, L, -75, -69, { step: 4, tileS: 3, tileU: 3, yFn: (u, s, x, z) => terrainH(x, z) + 0.25 }));
  // lado leste: comércio de frente + casas + almoxarifado
  let u = 6;
  while (u < L - 5) {
    const inField = (u > 300 && u < 360) || (u > L * 0.62 && u < L * 0.62 + 80);
    if (inField || R() < 0.22) { const n = Math.floor(rnd(2, 5)); for (let k = 0; k < n; k++) trees.push(treeAt(u + rnd(0, 10), rnd(11, 26), pick(['oiti', 'mango', 'palm', 'banana', 'oiti']))); u += rnd(10, 22); continue; }
    const w = rnd(6, 12), d = rnd(7, 11);
    const shop = R() < 0.7; const r = addHouse(B, u + w / 2, 9.9 + d / 2, w, d, 'E', { shop, floors: shop ? 1 : (R() < 0.6 ? 1 : 2), fh: shop ? rnd(3.4, 4.2) : 2.9, floorY: 0.1, brick: R() < 0.3, roof: shop ? (R() < 0.5 ? 'fibro' : 'slab') : undefined });
    if (shop) { const st = shopTex[Math.floor(R() * shopTex.length)]; const pl = new THREE.Mesh(new THREE.PlaneGeometry(Math.min(w - 0.4, 6), 1.1), MS({ map: st, roughness: 0.6 })); const p = at(u + w / 2, 9.85); pl.position.set(p[0], r.top - 0.7, p[1]); pl.rotation.y = Math.atan2(-p[2], -p[3]); pl.castShadow = false; g.add(pl); }
    u += w + rnd(0.5, 5);
  }
  for (let i = 0; i < 70; i++) { const uu = rnd(L * 0.45, L - 20), s = rnd(32, 85); if (uu > L * 0.66 && uu < L * 0.66 + 70 && s < 75) continue; addHouse(B, uu, s, rnd(5, 8), rnd(6, 9), 'E', { floorY: terrainH(...at(uu, s).slice(0, 2)) + 0.1 }); }
  for (let i = 0; i < 260; i++) trees.push(treeAt(rnd(0, L), rnd(18, 140), pick(['oiti', 'mango', 'palm', 'oiti', 'banana'])));
  for (let i = 0; i < 160; i++) { const uu = rnd(-20, L + 20), s = -rnd(120, 230); trees.push(treeAt(uu, s, pick(['mango', 'oiti', 'palm']))); }
  // almoxarifado (galpão)
  { const u0 = L * 0.66, w = 62, d = 34, sC = 36 + d / 2; const p = at(u0 + w / 2, sC); const m = new THREE.Matrix4().makeBasis(new V3(p[3], 0, -p[2]), new V3(0, 1, 0), new V3(p[2], 0, p[3])); m.setPosition(p[0], 0, p[1]); const wl = boxUV(w, 9, d, 3); wl.translate(0, 4.4, 0); B.add('plaster', tf(wl, m), '#e8e6e0'); const rf = boxUV(w + 1, 0.4, d + 1, 3); rf.translate(0, 9.1, 0); B.add('vcMetal', tf(rf, m), '#c7ccd0'); HOUSES.push({ x: p[0], z: p[1], w, d, rx: p[2], rz: p[3], tx: p[3], tz: -p[2], label: 'Almoxarifado Central' }); }
  // postes de concreto + fiação
  const wires = [];
  for (const [side, s, off] of [['W', -11.25, 0], ['E', 9.3, 19]]) {
    let prev = null;
    for (let uu = off + 4; uu < L - 2; uu += 38) {
      const m = placeMat(uu, s, 0, 0, 1); const p = at(uu, s);
      B.add('vc', tf(cyl(0.11, 0.19, 10.5, 6), m.clone()), '#b8b5ad'); B.add('vc', tf(box(2.2, 0.12, 0.12, 0, 9.6, 0), m.clone()), '#9a978f');
      POLES.push({ u: uu, s, side });
      const pt = (k) => { const rr = at(uu, s + (k - 1) * 0.9 * (side === 'W' ? 1 : -1)); return new V3(rr[0], 9.75, rr[1]); };
      if (prev) for (let k = 0; k < 3; k++) { const a = prev[k], b = pt(k); for (let j = 0; j < 10; j++) { const t0 = j / 10, t1 = (j + 1) / 10; const sag = (t) => -0.9 * 4 * t * (1 - t); wires.push(a.x + (b.x - a.x) * t0, a.y + (b.y - a.y) * t0 + sag(t0), a.z + (b.z - a.z) * t0, a.x + (b.x - a.x) * t1, a.y + (b.y - a.y) * t1 + sag(t1), a.z + (b.z - a.z) * t1); } }
      prev = [pt(0), pt(1), pt(2)];
      if (side === 'W' && Math.round((uu - 4) / 38) % 2 === 0) { const dirS = 1; const arm = box(0.08, 0.08, 2.6, 0, 8.6, 0); const mm = placeMat(uu, s + 1.3 * dirS, 0, Math.PI / 2, 1); B.add('vc', tf(arm, mm), '#777'); const hp = at(uu, s + 2.6); const hd = box(0.5, 0.18, 0.28, 0, 8.5, 0); B.add('vc', tf(hd, placeMat(uu, s + 2.6, 0, 0, 1)), '#666'); BL.add('lampOld', tf(box(0.4, 0.04, 0.2, 0, 8.39, 0), placeMat(uu, s + 2.6, 0, 0, 1))); OLD_LAMPS.push({ x: hp[0], y: 8.3, z: hp[1], u: uu, s: s + 2.6 }); }
    }
  }
  const wg = new THREE.BufferGeometry(); wg.setAttribute('position', new THREE.Float32BufferAttribute(wires, 3)); g.add(new THREE.LineSegments(wg, M.wire));
  // pórtico de sinalização existente (norte)
  { const uu = L - 45; for (const s of [-6.5, 6.5]) B.add('vcMetal', tf(cyl(0.18, 0.18, 7.2, 10), placeMat(uu, s, 0)), '#8d949a'); const beam = box(13.4, 0.35, 0.35, 0, 7.0, 0); B.add('vcMetal', tf(beam, placeMat(uu, 0, 0, 0, 1)), '#8d949a'); const sg = new THREE.Mesh(new THREE.PlaneGeometry(9, 2.2), MS({ map: wideSign([['PE-060  ·  IPOJUCA', 70], ['Porto de Galinhas  ↑     Recife  ↑', 52]]), roughness: 0.5 })); const p = at(uu, 0); sg.position.set(p[0], 7.9, p[1]); sg.rotation.y = yawAt(uu, -1); g.add(sg); }
  // rodovia além do trecho modelado (continuidade visual)
  makeTrees(trees, g);
  B.flush(g, { receive: true, castKeys: ['brick', 'plaster', 'slab', 'fibro', 'vc', 'vcMetal'] });
  BL.flush(g, { receive: false });
  // brilho no chão das luminárias antigas
  const gg = []; for (const l of OLD_LAMPS) { const pl = new THREE.PlaneGeometry(14, 14); pl.rotateX(-Math.PI / 2); pl.translate(l.x, 0.06, l.z); gg.push(pl); }
  if (gg.length) g.add(new THREE.Mesh(mergeGeometries(gg), M.glowOld));
  // janelas acesas (malha separada)
  g.traverse(o => { if (o.material === M.winLit) { o.name = 'winLit'; o.castShadow = false; } if (o.material === M.glass) o.castShadow = false; });
  return g;
}

// ============================================================ Sinais / mobiliário
const SIGNMESH = [];
function addSign(group, B, u, s, dir, tex, size = 0.75, h = 2.2, w2 = null) {
  B.add('vcMetal', tf(cyl(0.045, 0.045, h + size / 2, 8), placeMat(u, s, 0)), '#9aa0a6');
  const pl = new THREE.Mesh(new THREE.PlaneGeometry(w2 || size, size), MS({ map: tex, transparent: true, alphaTest: 0.5, roughness: 0.5, side: THREE.FrontSide }));
  const p = at(u, s); pl.position.set(p[0], h + size / 2, p[1]); pl.rotation.y = yawAt(u, -dir); pl.position.x += Math.sin(pl.rotation.y) * 0.03; pl.position.z += Math.cos(pl.rotation.y) * 0.03;
  const bk = new THREE.Mesh(new THREE.PlaneGeometry(w2 || size, size), MS({ color: 0x8a9096, roughness: 0.6, transparent: true, alphaMap: tex, alphaTest: 0.5 })); bk.position.copy(pl.position); bk.rotation.y = pl.rotation.y + Math.PI; bk.position.x -= Math.sin(pl.rotation.y) * 0.02; bk.position.z -= Math.cos(pl.rotation.y) * 0.02;
  group.add(pl, bk);
}
const TEX = { lim30: signTex('lim', '30'), lim60: signTex('lim', '60'), ped: signTex('ped'), obra: signTex('obra', 'OBRAS'), pista: signTex('obra', 'MEIA PISTA'), bikeR: signTex('bike'), bikeW: signTex('bike-w'), bus: signTex('bus'), pare: signTex('pare', 'PARE'), siga: signTex('pare', 'SIGA'), info: signTex('info', 'TRAVESSIA|URBANA'), info2: signTex('info', 'ZONA 30|IPOJUCA') };
function signalHead(group, B, mats, u, s, y, dir, arm = 0) {
  // mastro + cabeça com 3 focos
  const yaw = yawAt(u, -dir);
  if (arm) { B.add('vcMetal', tf(cyl(0.11, 0.13, y + 0.8, 10), placeMat(u, s, 0)), '#3a3f44'); const p0 = at(u, s), p1 = at(u, s + arm); const len = Math.abs(arm); const a = box(len, 0.12, 0.12, 0, 0, 0); const mid = at(u, s + arm / 2); const mm = placeMat(u, s + arm / 2, y + 0.75, 0, 1); a.rotateY(0); B.add('vcMetal', tf(a, new THREE.Matrix4().compose(new V3(mid[0], y + 0.75, mid[1]), new THREE.Quaternion().setFromEuler(new THREE.Euler(0, yawAt(u, 1), 0)), new V3(1, 1, 1))), '#3a3f44'); }
  else B.add('vcMetal', tf(cyl(0.07, 0.08, y - 0.4, 8), placeMat(u, s, 0)), '#3a3f44');
  const hs = arm ? s + arm * 0.8 : s; const p = at(u, hs);
  const hb = box(0.42, 1.15, 0.3); hb.rotateY(yaw); hb.translate(p[0], y, p[1]); B.add('vc', hb, '#1b1e21');
  const vis = box(0.6, 1.4, 0.04); vis.rotateY(yaw); vis.translate(p[0] - Math.sin(yaw) * 0.16, y, p[1] - Math.cos(yaw) * 0.16); B.add('vc', vis, '#111');
  [['r', 0.36], ['y', 0], ['g', -0.36]].forEach(([k, dy]) => { const c = new THREE.Mesh(new THREE.CircleGeometry(0.13, 16), mats[k]); c.position.set(p[0] + Math.sin(yaw) * 0.16, y + dy, p[1] + Math.cos(yaw) * 0.16); c.rotation.y = yaw; group.add(c); });
}
function pedHead(group, B, mats, u, s, y, faceDir) {
  B.add('vcMetal', tf(cyl(0.06, 0.07, y + 0.5, 8), placeMat(u, s, 0)), '#3a3f44');
  const yaw = yawAt(u, 1) - faceDir * Math.PI / 2; const p = at(u, s);
  const hb = box(0.36, 0.72, 0.24); hb.rotateY(yaw); hb.translate(p[0], y, p[1]); B.add('vc', hb, '#1b1e21');
  [['pr', 0.17], ['pg', -0.17]].forEach(([k, dy]) => { const c = new THREE.Mesh(new THREE.PlaneGeometry(0.3, 0.3), mats[k]); c.position.set(p[0] + Math.sin(yaw) * 0.13, y + dy, p[1] + Math.cos(yaw) * 0.13); c.rotation.y = yaw; group.add(c); });
  const bt = box(0.12, 0.18, 0.1); bt.rotateY(yaw); bt.translate(p[0] + Math.sin(yaw) * 0.08, 1.1, p[1] + Math.cos(yaw) * 0.08); B.add('vc', bt, '#f2c230');
}
function busShelter(B, u, s, side) {
  const f = side === 'E' ? -1 : 1; // abre para a via
  const m = placeMat(u, s, 0.15, f > 0 ? -Math.PI / 2 : Math.PI / 2, 1);
  for (const x of [-1.9, 1.9]) for (const z of [-0.7, 0.7]) B.add('vcMetal', tf(cyl(0.05, 0.05, 2.6, 8, x, 0, z), m.clone()), '#4a5058');
  B.add('vcMetal', tf(box(4.4, 0.12, 1.9, 0, 2.66, 0), m.clone()), '#2f6fb6');
  B.add('glassK', tf(box(3.8, 1.8, 0.04, 0, 1.4, -0.72), m.clone()));
  B.add('vc', tf(box(3.0, 0.08, 0.45, 0, 0.48, -0.4), m.clone()), '#8a5a34');
  B.add('vc', tf(box(0.06, 0.48, 0.06, -1.2, 0.24, -0.4), m.clone()), '#4a5058'); B.add('vc', tf(box(0.06, 0.48, 0.06, 1.2, 0.24, -0.4), m.clone()), '#4a5058');
}
function lamp(B, BL, lampsOut, u, s, armDir, h = 9, armLen = 2.2, kind = 'led') {
  B.add('vcMetal', tf(cyl(0.08, 0.13, h, 10), placeMat(u, s, 0.15)), '#7d858c');
  const p1 = at(u, s + armDir * armLen); const mid = at(u, s + armDir * armLen / 2);
  const a = box(armLen, 0.07, 0.07); a.rotateY(yawAt(u, 1)); a.translate(mid[0], h + 0.1, mid[1]); B.add('vcMetal', a, '#7d858c');
  const hd = box(0.75, 0.12, 0.32); hd.rotateY(yawAt(u, 1)); hd.translate(p1[0], h + 0.05, p1[1]); B.add('vcMetal', hd, '#5f666d');
  const em = box(0.62, 0.03, 0.24); em.rotateY(yawAt(u, 1)); em.translate(p1[0], h - 0.03, p1[1]); BL.add('lampLED', em);
  lampsOut.push({ x: p1[0], y: h - 0.2, z: p1[1], u, s: s + armDir * armLen, kind });
}

// ============================================================ Construtores de fase
let phaseGroup = null, PHASE_LAMPS = [], PHASE_LABELS = [], workRig = [];
function buildOld(g, B, u0, u1) {
  if (u1 - u0 < 0.5) return;
  const nE = (u) => 0.18 * (noise2(u * 0.3, 3) - 0.5), nW = (u) => 0.18 * (noise2(u * 0.3, 9) - 0.5);
  B.add('asphOld', ribbon(u0, u1, -3.5, 3.5, { tileS: 7, tileU: 7, sAFn: (u) => -3.5 + nW(u), sBFn: (u) => 3.5 + nE(u), uvS: true }));
  B.add('dirt', ribbon(u0, u1, -11.7, -3.3, { y: -0.025, tileS: 5, tileU: 5, step: 3 }));
  B.add('dirt', ribbon(u0, u1, 3.3, 9.9, { y: -0.025, tileS: 5, tileU: 5, step: 3 }));
  B.add('grass', ribbon(u0, u1, -11.7, -10, { y: -0.012, tileS: 4, tileU: 4, step: 3, sBFn: (u) => -11.4 + 2.6 * Math.max(0, noise2(u * 0.12, 1) - 0.35) }));
  B.add('grass', ribbon(u0, u1, 8, 9.9, { y: -0.012, tileS: 4, tileU: 4, step: 3, sAFn: (u) => 9.6 - 2.8 * Math.max(0, noise2(u * 0.12, 5) - 0.3) }));
  // sinalização horizontal desgastada
  for (const s of [-0.18, 0.06]) B.add('yellowOld', ribbon(u0, u1, s, s + 0.12, { y: 0.008, step: 4 }));
  for (let u = u0; u < u1; u += 1) { const len = noise2(u * 0.5, 2) > 0.35 ? 1 : 0; if (len) B.add('whiteOld', ribbon(u, Math.min(u1, u + 1), 3.18, 3.3, { y: 0.008, step: 1 })); }
}
function buildNew(g, B, BL, u0, u1, young = false) {
  if (u1 - u0 < 0.5) return;
  const trees = [];
  const yR = (u) => roadY(u), yR2 = (u) => roadY(u) + 0.012;
  const cutsIn = CUTS.filter(c => c[1] > u0 && c[0] < u1 && isBuilt((c[0] + c[1]) / 2));
  B.add('asphNew', ribbon(u0, u1, -3.15, 3.15, { tileS: 6.3, tileU: 6.3, yFn: yR, step: 1, uvS: true }));
  B.add('bike', ribbon(u0, u1, -6.15, -3.65, { tileS: 4, tileU: 4, yFn: yR, step: 1 }));
  // separador da ciclovia
  for (const [a, b] of subtract(u0, u1, cutsIn)) { B.add('curb', ribbon(a, b, -3.65, -3.15, { y: 0.13 })); B.add('curb', wallR(a, b, -3.65, 0, 0.13)); B.add('curb', wallR(a, b, -3.15, 0, 0.13)); }
  for (const [a, b] of cutsIn) { const aa = Math.max(a, u0), bb = Math.min(b, u1); if (bb > aa) B.add('asphNew', ribbon(aa, bb, -3.65, -3.15, { yFn: yR, step: 0.5 })); }
  // calçada oeste
  B.add('paver', ribbon(u0, u1, -10.9, -7.35, { y: 0.15, tileS: 4, tileU: 4 }));
  B.add('tactile', ribbon(u0, u1, -9.45, -9.05, { y: 0.158, tileS: 0.4, tileU: 0.4 }));
  B.add('concrete', ribbon(u0, u1, -11.6, -10.9, { y: 0.7, tileS: 2, tileU: 2 })); B.add('concrete', wallR(u0, u1, -10.9, 0.15, 0.7));
  for (const [a, b] of subtract(u0, u1, cutsIn)) { B.add('grass', ribbon(a, b, -7.35, -6.3, { y: 0.15, tileS: 3, tileU: 3 })); B.add('curb', ribbon(a, b, -6.3, -6.15, { y: 0.15 })); B.add('curb', wallR(a, b, -6.15, 0, 0.15)); B.add('curb', ribbon(a, b, -7.4, -7.3, { y: 0.17 })); }
  for (const [a, b] of cutsIn) { const aa = Math.max(a, u0), bb = Math.min(b, u1); if (bb > aa) { B.add('paver', ribbon(aa, bb, -7.35, -6.15, { y: 0.15, tileS: 4, tileU: 4 })); B.add('tactile', ribbon(aa, bb, -6.55, -6.15, { y: 0.158, tileS: 0.4, tileU: 0.4 })); } }
  // lado leste: canteiro / baias / calçada
  const bays = BAYS.filter(b => b[1] > u0 && b[0] < u1);
  const eCuts = [...cutsIn, ...bays.map(b => [b[0], b[1]])];
  for (const [a, b] of subtract(u0, u1, eCuts)) { B.add('grass', ribbon(a, b, 3.3, 5.55, { y: 0.15, tileS: 3, tileU: 3 })); B.add('curb', ribbon(a, b, 3.15, 3.3, { y: 0.15 })); B.add('curb', wallR(a, b, 3.15, 0, 0.15)); }
  for (const [a, b] of cutsIn) { const aa = Math.max(a, u0), bb = Math.min(b, u1); if (bb > aa) { B.add('paver', ribbon(aa, bb, 3.15, 5.55, { y: 0.15, tileS: 4, tileU: 4 })); B.add('tactile', ribbon(aa, bb, 3.15, 3.55, { y: 0.158, tileS: 0.4, tileU: 0.4 })); } }
  for (const [b0, b1, kind] of bays) { const a = Math.max(b0, u0), b = Math.min(b1, u1); if (b <= a) continue; B.add('asphNew', ribbon(a, b, 3.15, 5.55, { tileS: 6, tileU: 6 })); B.add('curb', wallR(a, b, 5.55, 0, 0.15)); B.add('curb', ribbon(a, b, 5.4, 5.55, { y: 0.152 })); if (kind === 'park') for (let uu = a; uu <= b; uu += 5.5) B.add('white', ribbon(uu, uu + 0.12, 3.2, 5.5, { y: 0.012 })); else { B.add('yellow', ribbon(a, b, 3.2, 3.32, { y: 0.012 })); B.add('yellow', ribbon(a, b, 5.38, 5.5, { y: 0.012 })); B.add('white', ribbon(a, a + 0.15, 3.2, 5.5, { y: 0.012 })); B.add('white', ribbon(b - 0.15, b, 3.2, 5.5, { y: 0.012 })); } }
  B.add('paver', ribbon(u0, u1, 5.55, 8.6, { y: 0.15, tileS: 4, tileU: 4 }));
  B.add('tactile', ribbon(u0, u1, 6.9, 7.3, { y: 0.158, tileS: 0.4, tileU: 0.4 }));
  B.add('concrete', ribbon(u0, u1, 8.6, 9.95, { y: 0.15, tileS: 3, tileU: 3 }));
  // sinalização horizontal
  const linCuts = cutsIn.map(c => [c[0] - 2, c[1] + 2]);
  for (const [a, b] of subtract(u0, u1, linCuts)) { for (const s of [-0.21, 0.09]) B.add('yellow', ribbon(a, b, s, s + 0.12, { yFn: yR2, step: 2 })); for (const s of [-3.08, 2.96]) B.add('white', ribbon(a, b, s, s + 0.12, { yFn: yR2, step: 2 })); }
  for (let uu = u0; uu < u1 - 1; uu += 3) if (!cutsIn.some(c => uu > c[0] - 1 && uu < c[1] + 1)) B.add('white', ribbon(uu, uu + 1.2, -4.96, -4.84, { yFn: yR2, step: 1.2 }));
  for (const c of CROSS) { if (c.u < u0 || c.u > u1) continue; for (let s = -6.0; s < 3.0; s += 0.8) B.add('white', ribbon(c.u - 2, c.u + 2, s, s + 0.4, { yFn: yR2, step: 0.5 })); if (c.type === 'raised') for (const sgn of [-1, 1]) for (let s = -3.0; s < 3.0; s += 0.75) { const pos = [], uu0 = c.u + sgn * 3.05, uu1 = c.u + sgn * 4.3; const pa = at(uu0, s), pb = at(uu0, s + 0.5), pc = at(uu1, s + 0.25); const g2 = new THREE.BufferGeometry(); g2.setAttribute('position', new THREE.Float32BufferAttribute([pa[0], roadY(uu0) + 0.014, pa[1], pb[0], roadY(uu0) + 0.014, pb[1], pc[0], roadY(uu1) + 0.014, pc[1]], 3)); g2.setIndex(sgn > 0 ? [0, 2, 1] : [0, 1, 2]); g2.computeVertexNormals(); B.add('white', g2); } }
  if (SIG_U >= u0 && SIG_U <= u1) { B.add('white', ribbon(SIG_U - 5.4, SIG_U - 5, 0.1, 3.1, { y: 0.012 })); B.add('white', ribbon(SIG_U + 5, SIG_U + 5.4, -3.1, -0.1, { y: 0.012 })); }
  // pictogramas de bicicleta e "30"
  const bikeG = [], n30 = [];
  for (let uu = u0 + 12; uu < u1 - 5; uu += 45) { if (cutsIn.some(c => Math.abs(uu - c[0]) < 10 || Math.abs(uu - c[1]) < 10)) continue; for (const [s, d] of [[-4.35, 1], [-5.5, -1]]) { const pl = new THREE.PlaneGeometry(1.1, 1.1); pl.rotateX(-Math.PI / 2); pl.rotateY(yawAt(uu, d) + Math.PI); const p = at(uu, s); pl.translate(p[0], 0.02, p[1]); bikeG.push(pl); } }
  if (bikeG.length) { const mm = new THREE.Mesh(mergeGeometries(bikeG), new THREE.MeshStandardMaterial({ map: T.bikeIcon, transparent: true, roughness: 0.7, polygonOffset: true, polygonOffsetFactor: -3 })); mm.receiveShadow = true; g.add(mm); }
  for (const [uu, s, d] of [[uA + 8, 1.6, 1], [uB - 8, -1.6, -1]]) { if (uu < u0 || uu > u1) continue; const pl = new THREE.PlaneGeometry(1.6, 4.2); pl.rotateX(-Math.PI / 2); pl.rotateY(yawAt(uu, d) + Math.PI); const p = at(uu, s); pl.translate(p[0], 0.02, p[1]); n30.push(pl); }
  if (n30.length) { const mm = new THREE.Mesh(mergeGeometries(n30), new THREE.MeshStandardMaterial({ map: T.n30, transparent: true, roughness: 0.7, polygonOffset: true, polygonOffsetFactor: -3 })); g.add(mm); }
  // portais de entrada (Zona 30)
  for (const [pu, d] of [[uA, 1], [uB, -1]]) {
    if (pu < u0 - 1 || pu > u1 + 1) continue;
    const a = d > 0 ? pu - 18 : pu, b = d > 0 ? pu : pu + 18; B.add('portal', ribbon(a, b, -3.5, 3.5, { y: 0.01, tileS: 2, tileU: 2 }));
    const gu = d > 0 ? pu - 10 : pu + 10; for (const s of [-5.2, 5.2]) B.add('vcMetal', tf(cyl(0.2, 0.2, 6.4, 12), placeMat(gu, s, 0)), '#2f6fb6');
    B.add('vcMetal', tf(box(10.8, 0.5, 0.4, 0, 6.2, 0), placeMat(gu, 0, 0)), '#2f6fb6');
    const sg = new THREE.Mesh(new THREE.PlaneGeometry(8, 1.6), MS({ map: wideSign([['TRAVESSIA URBANA · IPOJUCA', 64], ['ZONA 30  ·  PEDESTRES E CICLISTAS', 44]], '#1f5fa8'), roughness: 0.5 }));
    const p = at(gu, 0); sg.position.set(p[0], 5.35, p[1]); sg.rotation.y = yawAt(gu, -d); sg.position.x += Math.sin(sg.rotation.y) * 0.25; sg.position.z += Math.cos(sg.rotation.y) * 0.25; g.add(sg);
    addSign(g, B, d > 0 ? pu + 4 : pu - 4, d > 0 ? 8.1 : -10.4, d, TEX.lim30, 0.8);
    addSign(g, B, d > 0 ? pu + 30 : pu - 30, d > 0 ? 8.1 : -10.4, d, TEX.bikeW, 0.75);
  }
  // árvores nos canteiros
  for (const side of ['W', 'E']) {
    for (let uu = u0 + 4; uu < u1 - 2; uu += 9) {
      if (cutsIn.some(c => uu > c[0] - 1.5 && uu < c[1] + 1.5)) continue;
      if (side === 'E' && bays.some(b => uu > b[0] - 1 && uu < b[1] + 1)) continue;
      const s = side === 'W' ? -6.82 : 4.4; const typ = young ? 'young' : (hash2(Math.round(uu), side === 'W' ? 1 : 2) < 0.22 ? 'ipe' : 'oiti');
      trees.push(treeAt(uu, s, typ, { y: 0.15, s: young ? 0.8 : rnd(0.85, 1.05) }));
    }
  }
  makeTrees(trees, g);
  // iluminação
  for (let uu = u0 + 6; uu < u1 - 2; uu += 30) { if (cutsIn.some(c => Math.abs(uu - (c[0] + c[1]) / 2) < 6)) continue; lamp(B, BL, PHASE_LAMPS, uu, -6.75, 1, 9, 2.6); lamp(B, BL, PHASE_LAMPS, uu + 15 < u1 ? uu + 15 : uu, 4.4, -1, 9, 2.4); lamp(B, BL, PHASE_LAMPS, uu + 8 < u1 ? uu + 8 : uu, -10.55, 1, 4.5, 0.6, 'ped'); lamp(B, BL, PHASE_LAMPS, uu + 22 < u1 ? uu + 22 : uu, 8.35, -1, 4.5, 0.6, 'ped'); }
  for (const c of CROSS) { if (c.u < u0 || c.u > u1) continue; lamp(B, BL, PHASE_LAMPS, c.u - 3.5, -6.6, 1, 8, 3.4); lamp(B, BL, PHASE_LAMPS, c.u + 3.5, 4.0, -1, 8, 3.4); }
  // travessias: sinalização vertical, balizadores
  for (const c of CROSS) {
    if (c.u < u0 || c.u > u1) continue;
    addSign(g, B, c.u - 45, 8.1, 1, TEX.ped, 0.8); addSign(g, B, c.u + 45, -10.4, -1, TEX.ped, 0.8);
    for (const s of [-7.0, 3.75]) for (const du of [-4.3, -2.6, 2.6, 4.3]) B.add('vc', tf(cyl(0.08, 0.08, 0.9, 8), placeMat(c.u + du, s, 0.15)), '#30363c');
    if (c.type === 'signal') { signalHead(g, B, SIGM, c.u - 6.5, 3.7, 5.4, 1, -2.4); signalHead(g, B, SIGM, c.u - 6.5, 3.7, 3.1, 1, 0); signalHead(g, B, SIGM, c.u + 6.5, -3.4, 5.4, -1, 2.0); signalHead(g, B, SIGM, c.u + 6.5, -3.4, 3.1, -1, 0); pedHead(g, B, SIGM, c.u + 2.6, -6.6, 2.6, 1); pedHead(g, B, SIGM, c.u - 2.6, 3.6, 2.6, -1); pedHead(g, B, SIGM, c.u - 2.6, -3.4, 2.6, -1); pedHead(g, B, SIGM, c.u + 2.6, -3.4, 2.6, 1); }
  }
  for (const b of BUS) { if (b.u < u0 || b.u > u1) continue; busShelter(B, b.u, b.side === 'E' ? 7.9 : -10.0, b.side); addSign(g, B, b.u + (b.side === 'E' ? -3 : 3), b.side === 'E' ? 6.0 : -7.7, b.side === 'E' ? 1 : -1, TEX.bus, 0.6, 2.4); for (let k = 0; k < 3; k++) B.add('vcMetal', tf(new THREE.TorusGeometry(0.38, 0.03, 6, 14, Math.PI), placeMat(b.u + (b.side === 'E' ? 6 : -6) + k * 0.8, b.side === 'E' ? 8.2 : -10.3, 0.15, Math.PI / 2)), '#8d949a'); }
  // bancos e lixeiras
  for (let uu = u0 + 20; uu < u1; uu += 55) { for (const [s, f] of [[-10.45, 1], [8.25, -1]]) { const m = placeMat(uu, s, 0.15, f > 0 ? -Math.PI / 2 : Math.PI / 2); B.add('vc', tf(box(1.8, 0.08, 0.45, 0, 0.45, 0), m.clone()), '#8a5a34'); B.add('vc', tf(box(1.8, 0.45, 0.06, 0, 0.75, -0.2), m.clone()), '#8a5a34'); B.add('vcMetal', tf(cyl(0.22, 0.2, 0.8, 10, 1.6, 0, 0), m.clone()), '#2f7a4a'); } }
  // contenção do talude (gabião/concreto) ao longo da calçada oeste
  B.add('concrete', wallR(u0, u1, -11.6, 0.7, (u) => { const p = at(u, -12.2); return Math.min(2.4, terrainH(p[0], p[1]) + 0.2); }));
  if (u0 <= SIG_U && u1 >= SIG_U) addSign(g, B, SIG_U - 30, 8.1, 1, TEX.info, 1.0, 2.2);
}
function buildWork(g, B, u0, u1) {
  // pista existente permanece; frente de obra no lado oeste
  buildOld(g, B, u0, u1);
  const mid = (u0 + u1) / 2;
  B.add('dirt', ribbon(u0 + 4, u1 - 4, -8.8, -4.0, { y: -0.01, tileS: 3, tileU: 3, step: 2 }));
  B.add('vc', ribbon(u0 + 8, mid + 18, -7.6, -6.4, { y: -0.005, step: 2 }), '#4a3324');
  B.add('curb', ribbon(u0 + 2, mid, -6.3, -6.15, { y: 0.15 })); B.add('curb', wallR(u0 + 2, mid, -6.15, -0.02, 0.15));
  B.add('concrete', ribbon(u0 + 2, u0 + 30, -10.9, -7.35, { y: 0.1, tileS: 2, tileU: 2 }));
  // tubos de drenagem
  for (let uu = mid + 8; uu < u1 - 10; uu += 3.2) { const t = new THREE.CylinderGeometry(0.5, 0.5, 1.5, 14, 1, true); t.rotateZ(Math.PI / 2); t.rotateY(yawAt(uu, 1)); const p = at(uu, -9.4); t.translate(p[0], 0.5, p[1]); B.add('curb', t); }
  // montes de material
  for (const [uu, s, r, c] of [[mid - 20, -9.6, 1.8, '#b97a4c'], [mid + 30, -9.8, 1.5, '#9a9488'], [mid - 35, -9.9, 1.3, '#d8c49a']]) { const sg = new THREE.SphereGeometry(r, 14, 8, 0, Math.PI * 2, 0, Math.PI / 2); sg.scale(1.4, 0.6, 1); const p = at(uu, s); sg.translate(p[0], 0, p[1]); B.add('vc', sg, c); }
  // cones: fechamento da faixa oeste (com transições)
  const cones = [];
  for (let uu = u0 - 22; uu <= u1 + 22; uu += 3) { let s = -0.1; if (uu < u0) s = lerp(-3.3, -0.1, clamp((uu - (u0 - 22)) / 22, 0, 1)); if (uu > u1) s = lerp(-0.1, -3.3, clamp((uu - u1) / 22, 0, 1)); cones.push([uu, s]); }
  for (let uu = u0; uu <= u1; uu += 5) cones.push([uu, -3.6]);
  for (const [uu, s] of cones) { const p = at(uu, s); const cg = new THREE.ConeGeometry(0.17, 0.72, 10); cg.translate(p[0], 0.36, p[1]); B.add('vc', cg, '#f06a12'); const band = new THREE.CylinderGeometry(0.105, 0.125, 0.12, 10); band.translate(p[0], 0.42, p[1]); B.add('vc', band, '#f2f2f2'); const bs = box(0.42, 0.04, 0.42); bs.translate(p[0], 0.02, p[1]); B.add('vc', bs, '#222'); }
  // barreiras plásticas nas extremidades
  for (const uu of [u0 - 2, u1 + 2]) for (let s = -3.2; s < -0.3; s += 1.1) { const m = placeMat(uu, s + 0.5, 0, 0); B.add('vc', tf(box(1.0, 0.8, 0.4, 0, 0.4, 0), m), Math.round(s * 2) % 2 ? '#f06a12' : '#f2f2f2'); }
  // placas de obra
  addSign(g, B, u0 - 90, 5.0, 1, TEX.obra, 0.9, 1.5); addSign(g, B, u0 - 55, 5.0, 1, TEX.lim30, 0.8, 1.6); addSign(g, B, u0 - 35, 5.0, 1, TEX.pista, 0.9, 1.5);
  addSign(g, B, u1 + 90, -5.0, -1, TEX.obra, 0.9, 1.5); addSign(g, B, u1 + 55, -5.0, -1, TEX.lim30, 0.8, 1.6); addSign(g, B, u1 + 35, -5.0, -1, TEX.pista, 0.9, 1.5);
  // semáforos provisórios (pare-e-siga)
  signalHead(g, B, SIGT, u0 - 20, 4.4, 2.6, 1, 0); signalHead(g, B, SIGT, u1 + 25, -4.3, 2.6, -1, 0);
  // contêiner do canteiro + banheiro químico
  { const m = placeMat(mid + 5, 7.4, 0, 0); B.add('vcMetal', tf(box(2.4, 2.6, 6.0, 0, 1.3, 0), m), '#e9eef2'); const m2 = placeMat(mid + 12, 7.6, 0, 0); B.add('vc', tf(box(1.2, 2.3, 1.2, 0, 1.15, 0), m2), '#2f6fb6'); }
  workRig = buildMachines(g, mid, u0, u1);
}
function machineMat(c) { return MS({ color: c, roughness: 0.55, metalness: 0.2 }); }
function buildMachines(g, mid, u0, u1) {
  const rig = [];
  const yel = machineMat(0xf2b01e), dark = machineMat(0x2a2a2a), grey = machineMat(0x8d949a), org = machineMat(0xe2661b);
  // escavadeira
  const ex = new THREE.Group(); const p = at(mid - 5, -7.2); ex.position.set(p[0], 0, p[1]); ex.rotation.y = yawAt(mid, 1);
  ex.add(Object.assign(new THREE.Mesh(box(2.6, 0.8, 4.2, 0, 0.4, 0), dark), { castShadow: true }));
  const up = new THREE.Group(); up.position.y = 0.85; ex.add(up);
  up.add(Object.assign(new THREE.Mesh(box(2.4, 1.0, 3.0, 0, 0.5, -0.4), yel), { castShadow: true }));
  up.add(Object.assign(new THREE.Mesh(box(1.0, 1.4, 1.2, -0.6, 1.6, 0.6), yel), { castShadow: true }));
  up.add(new THREE.Mesh(box(0.9, 0.9, 1.0, -0.6, 1.75, 0.62), M.glass));
  const boom = new THREE.Group(); boom.position.set(0.5, 1.0, 1.0); up.add(boom);
  boom.add(Object.assign(new THREE.Mesh(box(0.4, 0.5, 4.2, 0, 0, 2.0), yel), { castShadow: true })); boom.rotation.x = -0.55;
  const stick = new THREE.Group(); stick.position.set(0, 0, 4.0); boom.add(stick); stick.rotation.x = 1.5;
  stick.add(Object.assign(new THREE.Mesh(box(0.32, 0.4, 2.8, 0, 0, 1.3), yel), { castShadow: true }));
  stick.add(Object.assign(new THREE.Mesh(box(1.0, 0.7, 0.8, 0, -0.2, 2.8), dark), { castShadow: true }));
  g.add(ex); rig.push({ type: 'ex', up, boom, stick });
  // rolo compactador
  const ro = new THREE.Group(); const p2 = at(mid + 22, -1.7); ro.position.set(p2[0], 0, p2[1]); ro.rotation.y = yawAt(mid, -1);
  const dr = new THREE.CylinderGeometry(0.75, 0.75, 1.9, 18); dr.rotateZ(Math.PI / 2); dr.translate(0, 0.75, 1.3); ro.add(Object.assign(new THREE.Mesh(dr, grey), { castShadow: true }));
  ro.add(Object.assign(new THREE.Mesh(box(1.7, 1.2, 2.4, 0, 1.0, -0.6), yel), { castShadow: true })); ro.add(Object.assign(new THREE.Mesh(box(1.4, 1.1, 1.2, 0, 2.15, -0.9), M.glass), {}));
  g.add(ro); rig.push({ type: 'roll', obj: ro, u: mid + 22, a: mid + 5, b: mid + 35 });
  // caminhão basculante
  const tk = new THREE.Group(); const p3 = at(u0 + 12, -1.7); tk.position.set(p3[0], 0, p3[1]); tk.rotation.y = yawAt(u0, 1);
  tk.add(Object.assign(new THREE.Mesh(box(2.4, 2.2, 2.2, 0, 1.7, 2.6), org), { castShadow: true })); tk.add(new THREE.Mesh(box(2.3, 0.8, 0.1, 0, 2.3, 3.72), M.glass));
  tk.add(Object.assign(new THREE.Mesh(box(2.5, 1.4, 4.6, 0, 1.9, -1.1), org), { castShadow: true }));
  for (const [x, z] of [[-1.1, 2.6], [1.1, 2.6], [-1.1, -1.6], [1.1, -1.6], [-1.1, -2.8], [1.1, -2.8]]) { const w = new THREE.CylinderGeometry(0.5, 0.5, 0.35, 14); w.rotateZ(Math.PI / 2); w.translate(x, 0.5, z); tk.add(new THREE.Mesh(w, dark)); }
  g.add(tk);
  // trabalhadores
  const wk = [[mid - 2, -8.2], [mid + 3, -6.9], [mid - 12, -7.5], [mid + 14, -9.2], [mid + 24, -2.9], [u0 + 18, -2.6], [u0 + 25, -6.6]];
  for (const [uu, s] of wk) { const h = makeHuman(true); const pp = at(uu, s); h.group.position.set(pp[0], 0, pp[1]); h.group.rotation.y = srnd(0, 6.28); g.add(h.group); rig.push({ type: 'worker', h, t: srnd(0, 10) }); }
  // sinaleiros (pare/siga)
  for (const [uu, s, dir] of [[u0 - 16, 2.0 + 2.2, 1], [u1 + 21, -4.1, -1]]) { const h = makeHuman(true); const pp = at(uu, s); h.group.position.set(pp[0], 0, pp[1]); h.group.rotation.y = yawAt(uu, -dir); g.add(h.group); const pad = new THREE.Mesh(new THREE.CircleGeometry(0.28, 8), MS({ map: TEX.pare, side: THREE.DoubleSide })); pad.position.set(0.35, 2.05, 0.15); h.group.add(pad); const st = new THREE.Mesh(box(0.03, 0.9, 0.03, 0.35, 1.5, 0.15), grey); h.group.add(st); rig.push({ type: 'flag', pad, dir }); }
  return rig;
}
function buildPhase() {
  if (phaseGroup) { scene.remove(phaseGroup); phaseGroup.traverse(o => { if (o.geometry) o.geometry.dispose(); }); }
  phaseGroup = new THREE.Group(); PHASE_LAMPS = []; workRig = [];
  const B = new Bucket(), BL = new Bucket(); const ph = state.phase;
  if (ph === 'hoje') { buildOld(phaseGroup, B, 0, L); addSign(phaseGroup, B, uA - 20, 4.6, 1, TEX.lim60, 0.8, 1.7); addSign(phaseGroup, B, uB + 20, -4.6, -1, TEX.lim60, 0.8, 1.7); }
  else if (ph === 'op') { buildOld(phaseGroup, B, 0, uA - 18); buildOld(phaseGroup, B, uB + 18, L); buildOld(phaseGroup, B, uA - 18, uA); buildOld(phaseGroup, B, uB, uB + 18); buildNew(phaseGroup, B, BL, uA, uB); }
  else { const f = ufront(); buildOld(phaseGroup, B, 0, uA); buildOld(phaseGroup, B, uB, L); if (f > uA + 1) buildNew(phaseGroup, B, BL, uA, f, true); buildWork(phaseGroup, B, f, f + WZ); buildOld(phaseGroup, B, f + WZ, uB); }
  B.flush(phaseGroup, { receive: true, castKeys: ['vc', 'vcMetal', 'curb', 'concrete'] }); BL.flush(phaseGroup, { receive: false });
  const gg = []; for (const l of PHASE_LAMPS) { const sz = l.kind === 'ped' ? 9 : 17; const pl = new THREE.PlaneGeometry(sz, sz); pl.rotateX(-Math.PI / 2); pl.translate(l.x, 0.2, l.z); gg.push(pl); }
  if (gg.length) phaseGroup.add(new THREE.Mesh(mergeGeometries(gg), M.glow));
  phaseGroup.traverse(o => { if (o.isMesh && o.material === M.glass) o.castShadow = false; });
  scene.add(phaseGroup); buildLabels(); lightCandidates = [...PHASE_LAMPS, ...OLD_LAMPS];
}
let lightCandidates = [];

// ============================================================ Pessoas, veículos e bicicletas
const SKIN = ['#8d5524', '#c68642', '#e0ac69', '#f1c27d', '#5a3825', '#a86b3c', '#7a4a2a'];
const SHIRT = ['#e63946', '#f1faee', '#457b9d', '#1d3557', '#2a9d8f', '#e9c46a', '#f4a261', '#264653', '#ffffff', '#111111', '#8e44ad', '#27ae60', '#d35400', '#c0392b', '#f39c12', '#7f8c8d'];
const PANTS = ['#1d2b44', '#2c2c2c', '#4a5a6a', '#6b5a45', '#3a4a7a', '#1a1a1a', '#5d6d7e'];
const legGeos = PANTS.map(c => { const g = box(0.15, 0.86, 0.17, 0, -0.43, 0); prepGeo(g, 'x', c); const sh = box(0.16, 0.08, 0.26, 0, -0.84, 0.04); prepGeo(sh, 'x', '#1b1b1b'); return mergeGeometries([g, sh]); });
function makeHuman(worker = false, opts = {}) {
  const shirt = worker ? '#f26a1b' : pick(SHIRT), skin = pick(SKIN), hair = pick(['#1a1a1a', '#2b1a10', '#4a3020', '#111', '#6b4a2a']);
  const parts = [];
  const add = (g, c) => parts.push(prepGeo(g.index ? g.toNonIndexed() : g, 'x', c));
  add(box(0.42, 0.6, 0.24, 0, 1.17, 0), shirt); add(box(0.4, 0.14, 0.22, 0, 0.84, 0), pick(PANTS));
  add(box(0.1, 0.56, 0.12, -0.27, 1.17, 0), shirt); add(box(0.1, 0.56, 0.12, 0.27, 1.17, 0), shirt);
  add(box(0.09, 0.14, 0.1, -0.27, 0.83, 0), skin); add(box(0.09, 0.14, 0.1, 0.27, 0.83, 0), skin);
  add(cyl(0.06, 0.06, 0.08, 8, 0, 1.47, 0), skin); { const hd = new THREE.SphereGeometry(0.12, 12, 10); hd.scale(1, 1.15, 1.05); hd.translate(0, 1.64, 0); add(hd, skin); }
  if (worker) { const hm = new THREE.SphereGeometry(0.14, 12, 8, 0, Math.PI * 2, 0, Math.PI / 2); hm.translate(0, 1.7, 0); add(hm, '#f7d21c'); add(box(0.44, 0.08, 0.26, 0, 1.25, 0), '#d8ff3a'); }
  else if (R() < 0.75) { const hm = new THREE.SphereGeometry(0.128, 12, 8, 0, Math.PI * 2, 0, Math.PI / 2.1); hm.translate(0, 1.67, -0.01); add(hm, hair); }
  const geo = mergeGeometries(parts);
  const group = new THREE.Group(); const sc = opts.scale || rnd(0.92, 1.07); group.scale.setScalar(sc);
  const body = new THREE.Mesh(geo, M.human); body.castShadow = true; group.add(body);
  const lg = legGeos[Math.floor(R() * legGeos.length)];
  const l1 = new THREE.Mesh(lg, M.human), l2 = new THREE.Mesh(lg, M.human); l1.position.set(-0.1, 0.86, 0); l2.position.set(0.1, 0.86, 0); l1.castShadow = l2.castShadow = true; group.add(l1, l2);
  let umb = null; if (!worker) { umb = new THREE.Group(); const c = new THREE.Mesh(new THREE.ConeGeometry(0.55, 0.28, 8, 1, true), MS({ color: pick(['#1d3557', '#c0392b', '#111', '#27ae60', '#8e44ad', '#f39c12']), side: THREE.DoubleSide, roughness: 0.5 })); c.position.y = 2.05; const st = new THREE.Mesh(box(0.02, 0.6, 0.02, 0, 1.75, 0), M.trunk); umb.add(c, st); umb.position.set(0.22, 0, 0.05); umb.visible = false; group.add(umb); }
  return { group, l1, l2, umb };
}
// Veículos
const CARCOL = ['#f2f2f0', '#f2f2f0', '#e8e8e6', '#c9ccd0', '#c9ccd0', '#8a8f96', '#2b2d31', '#1d1f22', '#9e1b1b', '#1f3a6b', '#5a6b3a', '#d8d2c2', '#7a1f2b'];
const carGeoCache = new Map();
function carGeo(type, color) {
  const key = type + color; if (carGeoCache.has(key)) return carGeoCache.get(key);
  const parts = [], head = [], tail = []; const glass = '#141c24', dark = '#161616', chrome = '#a4a9ae', plast = '#2a2a2a';
  const add = (g, c) => parts.push(prepGeo(g.index ? g.toNonIndexed() : g, 'x', c));
  const P = (pts, width, c, x0 = 0) => { const sh = new THREE.Shape(pts.map(p => new THREE.Vector2(p[0] + x0, p[1]))); let g = new THREE.ExtrudeGeometry(sh, { depth: width, bevelEnabled: true, bevelThickness: 0.03, bevelSize: 0.03, bevelSegments: 1, curveSegments: 1 }); g.translate(0, 0, -width / 2); g.rotateY(-Math.PI / 2); add(g, c); };
  const WH = (r, x, z, wd = 0.22) => { const g = new THREE.CylinderGeometry(r, r, wd, 16); g.rotateZ(Math.PI / 2); g.translate(x, r, z); add(g, dark); const h = new THREE.CylinderGeometry(r * 0.58, r * 0.58, wd + 0.02, 10); h.rotateZ(Math.PI / 2); h.translate(x, r, z); add(h, chrome); };
  const LT = (arr, w, h, d, x, y, z) => { const g = box(w, h, d, x, y, z); arr.push(prepGeo(g.toNonIndexed(), 'x', '#ffffff')); };
  let len, w, hy = 0.7, ty = 0.75;
  if (type === 'hatch' || type === 'sedan' || type === 'suv') {
    const S = type === 'suv' ? 0.18 : 0; len = type === 'hatch' ? 3.85 : type === 'sedan' ? 4.45 : 4.5; w = type === 'suv' ? 1.82 : 1.72; const hl = len / 2;
    const lower = type === 'sedan' ? [[-hl, 0.3 + S], [hl, 0.3 + S], [hl + 0.02, 0.62 + S], [hl - 0.15, 0.78 + S], [hl - 1.15, 0.9 + S], [-hl + 0.75, 0.94 + S], [-hl, 0.88 + S]] : [[-hl, 0.3 + S], [hl, 0.3 + S], [hl + 0.02, 0.6 + S], [hl - 0.12, 0.78 + S], [hl - 1.0, 0.9 + S], [-hl + 0.05, 0.95 + S], [-hl - 0.02, 0.8 + S]];
    P(lower, w, color);
    const cab = type === 'sedan' ? [[-hl + 0.8, 0.92 + S], [hl - 1.2, 0.9 + S], [hl - 1.95, 1.4 + S], [-hl + 1.45, 1.42 + S]] : [[-hl + 0.12, 0.93 + S], [hl - 1.05, 0.9 + S], [hl - 1.75, 1.4 + S * 1.6], [-hl + 0.3, 1.43 + S * 1.6]];
    P(cab, w - 0.14, glass);
    const rf = type === 'sedan' ? [[-hl + 1.4, 1.39 + S], [hl - 1.93, 1.37 + S], [hl - 1.97, 1.45 + S], [-hl + 1.45, 1.47 + S]] : [[-hl + 0.28, 1.39 + S * 1.6], [hl - 1.72, 1.37 + S * 1.6], [hl - 1.76, 1.46 + S * 1.6], [-hl + 0.3, 1.48 + S * 1.6]];
    P(rf, w - 0.1, color);
    add(box(w + 0.02, 0.16, 0.12, 0, 0.42 + S, hl + 0.02), plast); add(box(w + 0.02, 0.16, 0.12, 0, 0.42 + S, -hl - 0.02), plast);
    const r = type === 'suv' ? 0.36 : 0.31, wb = len * 0.31; for (const x of [-w / 2 + 0.12, w / 2 - 0.12]) for (const z of [-wb, wb]) WH(r, x, z);
    hy = 0.7 + S; ty = 0.78 + S; LT(head, 0.32, 0.1, 0.05, -w / 2 + 0.3, hy, hl + 0.02); LT(head, 0.32, 0.1, 0.05, w / 2 - 0.3, hy, hl + 0.02); LT(tail, 0.3, 0.12, 0.05, -w / 2 + 0.25, ty, -hl - 0.02); LT(tail, 0.3, 0.12, 0.05, w / 2 - 0.25, ty, -hl - 0.02);
  } else if (type === 'pickup') {
    len = 5.2; w = 1.85; const hl = len / 2;
    P([[-hl, 0.4], [hl, 0.4], [hl + 0.02, 0.78], [hl - 0.2, 0.98], [hl - 1.3, 1.08], [-hl, 1.08]], w, color);
    P([[-0.35, 1.06], [hl - 1.32, 1.06], [hl - 2.0, 1.62], [-0.3, 1.64]], w - 0.14, glass); P([[-0.32, 1.6], [hl - 1.98, 1.58], [hl - 2.0, 1.67], [-0.3, 1.69]], w - 0.1, color);
    add(box(w - 0.2, 0.05, 1.9, 0, 1.06, -hl + 1.0), '#222'); for (const x of [-w / 2 + 0.12, w / 2 - 0.12]) for (const z of [-1.65, 1.6]) WH(0.38, x, z, 0.26);
    hy = 0.82; ty = 0.92; LT(head, 0.34, 0.12, 0.05, -w / 2 + 0.3, hy, hl + 0.02); LT(head, 0.34, 0.12, 0.05, w / 2 - 0.3, hy, hl + 0.02); LT(tail, 0.12, 0.3, 0.05, -w / 2 + 0.1, ty, -hl - 0.02); LT(tail, 0.12, 0.3, 0.05, w / 2 - 0.1, ty, -hl - 0.02);
  } else if (type === 'bus') {
    len = 12; w = 2.5; const hl = len / 2;
    add(box(w, 2.6, len, 0, 1.7, 0), color); add(box(w + 0.02, 0.95, len - 1.2, 0, 2.15, -0.3), glass); add(box(w - 0.2, 1.4, 0.05, 0, 2.1, hl + 0.01), glass);
    add(box(w + 0.03, 0.25, len - 0.4, 0, 1.15, 0), '#1f5fa8'); add(box(w + 0.03, 0.12, len - 0.4, 0, 1.45, 0), '#f2b233');
    add(box(w - 0.3, 0.1, len - 0.6, 0, 3.05, 0), '#d0d4d8');
    for (const x of [-w / 2 + 0.15, w / 2 - 0.15]) for (const z of [-hl + 2.6, hl - 2.4]) WH(0.5, x, z, 0.3);
    hy = 0.9; ty = 1.0; LT(head, 0.4, 0.15, 0.05, -w / 2 + 0.35, hy, hl + 0.02); LT(head, 0.4, 0.15, 0.05, w / 2 - 0.35, hy, hl + 0.02); LT(tail, 0.15, 0.5, 0.05, -w / 2 + 0.15, ty, -hl - 0.02); LT(tail, 0.15, 0.5, 0.05, w / 2 - 0.15, ty, -hl - 0.02);
  } else if (type === 'truck') {
    len = 8.4; w = 2.45; const hl = len / 2;
    add(box(w, 2.3, 2.1, 0, 1.85, hl - 1.05), color); add(box(w - 0.1, 0.9, 0.05, 0, 2.4, hl + 0.01), glass);
    add(box(w + 0.05, 2.9, 5.9, 0, 2.25, -hl + 2.95), pick(['#e8e8e6', '#c9ccd0', '#2f6fb6', '#d8d2c2'])); add(box(w - 0.4, 0.3, len - 0.4, 0, 0.75, 0), '#222');
    for (const x of [-w / 2 + 0.15, w / 2 - 0.15]) for (const z of [hl - 1.2, -hl + 1.6, -hl + 2.7]) WH(0.5, x, z, 0.3);
    hy = 0.95; ty = 1.0; LT(head, 0.4, 0.15, 0.05, -w / 2 + 0.35, hy, hl + 0.02); LT(head, 0.4, 0.15, 0.05, w / 2 - 0.35, hy, hl + 0.02); LT(tail, 0.2, 0.25, 0.05, -w / 2 + 0.2, ty, -hl - 0.02); LT(tail, 0.2, 0.25, 0.05, w / 2 - 0.2, ty, -hl - 0.02);
  } else { // moto
    len = 2.0; w = 0.7;
    for (const z of [-0.68, 0.68]) { const t = new THREE.TorusGeometry(0.3, 0.08, 8, 16); t.rotateY(Math.PI / 2); t.translate(0, 0.33, z); add(t, dark); }
    add(box(0.28, 0.32, 1.1, 0, 0.62, 0), color); add(box(0.3, 0.14, 0.7, 0, 0.84, -0.25), '#1a1a1a'); add(box(0.5, 0.05, 0.05, 0, 1.05, 0.5), chrome);
    add(box(0.38, 0.55, 0.26, 0, 1.25, -0.2), pick(SHIRT)); add(box(0.15, 0.5, 0.15, -0.15, 0.85, 0.05), '#1d2b44'); add(box(0.15, 0.5, 0.15, 0.15, 0.85, 0.05), '#1d2b44');
    { const hm = new THREE.SphereGeometry(0.15, 12, 10); hm.translate(0, 1.66, -0.15); add(hm, pick(['#111', '#c0392b', '#f2f2f2', '#1f3a6b'])); }
    add(box(0.08, 0.45, 0.1, -0.22, 1.2, 0.2), pick(SHIRT)); add(box(0.08, 0.45, 0.1, 0.22, 1.2, 0.2), '#333');
    hy = 0.95; ty = 0.8; LT(head, 0.16, 0.12, 0.05, 0, hy, 0.68); LT(tail, 0.14, 0.08, 0.05, 0, ty, -0.85);
  }
  const res = { body: mergeGeometries(parts), head: mergeGeometries(head), tail: mergeGeometries(tail), len, w, hy };
  carGeoCache.set(key, res); return res;
}
const beamGeo = (() => { const g = new THREE.PlaneGeometry(3.4, 16); g.rotateX(-Math.PI / 2); g.translate(0, 0.06, 8.2); return g; })();
const CARTYPES = [['hatch', 30], ['sedan', 18], ['suv', 12], ['pickup', 8], ['moto', 19], ['bus', 5], ['truck', 8]];
function pickType() { let r = SR() * 100; for (const [t, w] of CARTYPES) { if ((r -= w) < 0) return t; } return 'hatch'; }
const agentsGroup = new THREE.Group(); scene.add(agentsGroup);
const cars = [], peds = [], bikes = [];
function spawnCar(dir, x, v) {
  const type = pickType(); const col = type === 'bus' ? pick(['#f2f2f0', '#e8e8e6']) : type === 'truck' ? pick(['#f2f2f0', '#c8242b', '#1f5fa8', '#2b2d31']) : pick(CARCOL);
  const G = carGeo(type, col); const grp = new THREE.Group();
  const body = new THREE.Mesh(G.body, M.carBody); body.castShadow = true; body.receiveShadow = true; grp.add(body);
  const hd = new THREE.Mesh(G.head, M.head); const tl = new THREE.Mesh(G.tail, M.tail); grp.add(hd, tl);
  let beam = null; if (type !== 'moto') { beam = new THREE.Mesh(beamGeo, M.beam); beam.position.z = G.len / 2 - 0.5; beam.scale.x = G.w / 1.8; grp.add(beam); } else { beam = new THREE.Mesh(beamGeo, M.beam); beam.scale.set(0.45, 1, 0.8); beam.position.z = 0.6; grp.add(beam); }
  agentsGroup.add(grp);
  const heavy = type === 'bus' || type === 'truck';
  const c = { grp, tl, type, len: G.len, dir, x, u: dir > 0 ? x : L - x, v: v ?? 10, vmax: heavy ? srnd(13, 15.5) : type === 'moto' ? srnd(15, 21) : srnd(14.5, 19.5), agg: heavy ? srnd(0.85, 0.98) : type === 'moto' ? srnd(0.95, 1.18) : srnd(0.9, 1.12), off: 0, mo: type === 'moto' ? srnd(0.2, 0.7) : srnd(-0.12, 0.12), lastConf: -99, brake: false, counted: false };
  c.off = laneOff(c.u, dir) + c.mo * dir; cars.push(c); return c;
}
function laneOff(u, dir) {
  const base = isBuilt(u) ? 1.6 : 1.75;
  if (dir > 0) return base;
  if (state.phase === 'obra') { const f = ufront(); const k = smooth(f + WZ + 24, f + WZ + 6, u) * smooth(f - 24, f - 6, u); return lerp(-base, 1.65, k); }
  return -base;
}
function bikeOff(u, dir) { if (isBuilt(u)) return dir > 0 ? -4.3 : -5.5; if (inWork(u)) return dir > 0 ? 4.5 : -2.0; return dir > 0 ? 4.5 : -4.6; }
function spawnBike(dir, u) {
  const parts = []; const add = (g, c) => parts.push(prepGeo(g.index ? g.toNonIndexed() : g, 'x', c)); const fc = pick(['#c0392b', '#111', '#1f5fa8', '#27ae60', '#f39c12', '#ddd']);
  for (const z of [-0.52, 0.52]) { const t = new THREE.TorusGeometry(0.33, 0.03, 6, 18); t.rotateY(Math.PI / 2); t.translate(0, 0.35, z); add(t, '#151515'); }
  add(box(0.04, 0.04, 0.9, 0, 0.62, 0), fc); add(box(0.04, 0.5, 0.04, 0, 0.55, -0.1), fc); add(box(0.04, 0.45, 0.04, 0, 0.6, 0.45), fc); add(box(0.5, 0.03, 0.03, 0, 0.92, 0.45), '#333'); add(box(0.16, 0.05, 0.26, 0, 0.92, -0.12), '#222');
  const shirt = pick(SHIRT), skin = pick(SKIN); add(box(0.38, 0.55, 0.24, 0, 1.25, 0.05), shirt); add(box(0.14, 0.5, 0.15, -0.1, 0.8, 0.05), pick(PANTS)); add(box(0.14, 0.5, 0.15, 0.1, 0.8, 0.05), '#2c2c2c');
  { const hd = new THREE.SphereGeometry(0.12, 10, 8); hd.translate(0, 1.66, 0.12); add(hd, skin); } if (SR() < 0.5) { const hm = new THREE.SphereGeometry(0.14, 10, 8, 0, 6.3, 0, 1.6); hm.translate(0, 1.7, 0.12); add(hm, pick(['#f2f2f2', '#c0392b', '#111'])); }
  add(box(0.08, 0.45, 0.09, -0.22, 1.2, 0.3), shirt); add(box(0.08, 0.45, 0.09, 0.22, 1.2, 0.3), shirt);
  const mesh = new THREE.Mesh(mergeGeometries(parts), M.human); mesh.castShadow = true; agentsGroup.add(mesh);
  const b = { mesh, dir, u, v: srnd(3.6, 5.2), vmax: srnd(3.6, 5.4), off: bikeOff(u, dir), ph: srnd(0, 6) }; bikes.push(b); return b;
}
function pedWalkS(p) { if (inWork(p.u) && p.side === 'W') return -2.2 + p.o * 0.3; if (isBuilt(p.u)) return p.side === 'W' ? -9.0 + p.o * 1.1 : 7.1 + p.o * 0.9; return p.side === 'W' ? -5.1 + p.o * 0.7 : 5.0 + p.o * 0.7; }
const frontS = (side) => side === 'W' ? -11.0 : 9.6;
function spawnPed(initial = false) {
  const h = makeHuman(false); agentsGroup.add(h.group);
  const p = { h, u: srnd(uA - 50, uB + 50), side: SR() < 0.5 ? 'W' : 'E', dir: SR() < 0.5 ? 1 : -1, speed: srnd(1.0, 1.5), o: srnd(-1, 1), state: initial ? 'walk' : 'exit', life: srnd(40, 160), lastCross: -1, lastCrossT: -99, waitT: 0, cross: null, ph: srnd(0, 6), umb: SR() < 0.65 };
  p.s = initial ? pedWalkS(p) : frontS(p.side); peds.push(p); return p;
}
function removeFrom(arr, i, obj) { agentsGroup.remove(obj); arr.splice(i, 1); }
const sig = { op: { veh: 'G', ped: 'D', rem: 0 }, tmp: { n: 'G', s: 'R', rem: 0 } };
function updateSignals(t) {
  const c = t % 62; // ciclo semafórico da travessia
  if (c < 36) Object.assign(sig.op, { veh: 'G', ped: 'D', rem: 36 - c }); else if (c < 39) Object.assign(sig.op, { veh: 'Y', ped: 'D', rem: 39 - c }); else if (c < 41) Object.assign(sig.op, { veh: 'R', ped: 'D', rem: 41 - c }); else if (c < 55) Object.assign(sig.op, { veh: 'R', ped: 'W', rem: 55 - c }); else if (c < 60) Object.assign(sig.op, { veh: 'R', ped: 'F', rem: 60 - c }); else Object.assign(sig.op, { veh: 'R', ped: 'D', rem: 62 - c });
  const k = t % 84; // pare-e-siga provisório
  if (k < 22) Object.assign(sig.tmp, { n: 'G', s: 'R', rem: 22 - k }); else if (k < 25) Object.assign(sig.tmp, { n: 'Y', s: 'R', rem: 25 - k }); else if (k < 42) Object.assign(sig.tmp, { n: 'R', s: 'R', rem: 42 - k }); else if (k < 64) Object.assign(sig.tmp, { n: 'R', s: 'G', rem: 64 - k }); else if (k < 67) Object.assign(sig.tmp, { n: 'R', s: 'Y', rem: 67 - k }); else Object.assign(sig.tmp, { n: 'R', s: 'R', rem: 84 - k });
  const on = 3.2, off = 0.04, blink = Math.floor(t * 2) % 2;
  SIGM.r.emissiveIntensity = sig.op.veh === 'R' ? on : off; SIGM.y.emissiveIntensity = sig.op.veh === 'Y' ? on : off; SIGM.g.emissiveIntensity = sig.op.veh === 'G' ? on : off;
  SIGM.pg.emissiveIntensity = sig.op.ped === 'W' ? 2.5 : 0.04; SIGM.pr.emissiveIntensity = sig.op.ped === 'D' || (sig.op.ped === 'F' && blink) ? 2.5 : 0.04;
  // provisório: cabeças compartilham material → mostram o estado do sentido norte; sentido sul usa as mesmas cores invertidas via userData
  SIGT.r.emissiveIntensity = sig.tmp.n === 'R' ? on : off; SIGT.y.emissiveIntensity = sig.tmp.n === 'Y' ? on : off; SIGT.g.emissiveIntensity = sig.tmp.n === 'G' ? on : off;
}
let conflicts = 0, conflictsT0 = 0, flowCount = [], simT = 0;
const spawnAcc = { 1: 0, '-1': 0 }, bikeAcc = { 1: 0, '-1': 0 };
function zones() {
  const z = [];
  if (state.phase === 'op') { z.push({ u0: uA - 12, u1: uB + 12, v: 8.3 }); for (const c of CROSS) if (c.type === 'raised') z.push({ u0: c.u - 6, u1: c.u + 6, v: 4.0 }); }
  else if (state.phase === 'obra') { const f = ufront(); if (f > uA + 5) z.push({ u0: uA - 12, u1: f, v: 8.3 }); for (const c of CROSS) if (c.type === 'raised' && isBuilt(c.u)) z.push({ u0: c.u - 6, u1: c.u + 6, v: 4.0 }); z.push({ u0: f - 45, u1: f + WZ + 45, v: 8.3 }); }
  return z;
}
function updateAgents(dt) {
  simT += dt; updateSignals(simT);
  const Z = zones(); const raining = state.weather === 'chuva' || state.weather === 'tempestade';
  const wetK = raining ? 0.82 : 1; const f = ufront();
  // -------- veículos
  for (const dir of [1, -1]) {
    spawnAcc[dir] += state.fCars / 3600 * dt;
    const list = cars.filter(c => c.dir === dir).sort((a, b) => b.x - a.x);
    if (spawnAcc[dir] >= 1) { const lastC = list[list.length - 1]; if (!lastC || lastC.x > 22) { spawnCar(dir, 0, lastC ? Math.min(14, lastC.v + 2) : 14); spawnAcc[dir] -= 1; } else spawnAcc[dir] = Math.min(spawnAcc[dir], 3); }
    const stops = [];
    if (isBuilt(SIG_U)) { const su = dir > 0 ? SIG_U - 6 : SIG_U + 6; stops.push({ x: dir > 0 ? su : L - su, red: sig.op.veh === 'R', yel: sig.op.veh === 'Y' }); }
    if (state.phase === 'obra') { if (dir > 0) stops.push({ x: f - 20, red: sig.tmp.n === 'R', yel: sig.tmp.n === 'Y' }); else stops.push({ x: L - (f + WZ + 25), red: sig.tmp.s === 'R', yel: sig.tmp.s === 'Y' }); }
    for (let i = 0; i < list.length; i++) {
      const c = list[i], ld = list[i - 1];
      let gap = 1e9, dv = 0, isPed = false;
      if (ld) { gap = ld.x - c.x - (ld.len + c.len) / 2; dv = c.v - ld.v; if (c.type === 'moto' && ld.type === 'moto') gap += 1; }
      for (const st of stops) { const d = st.x - c.x - c.len / 2; if (d > -0.8 && d < gap) { if (st.red || (st.yel && d > c.v * c.v / (2 * 3.2))) { gap = Math.max(0.01, d); dv = c.v; } } }
      for (const p of peds) { if (Math.abs(p.s) > 3.5) continue; const lo = laneOff(p.u, dir); if (Math.abs(p.s - lo) > 1.8) continue; const px = dir > 0 ? p.u : L - p.u; const d = px - c.x - c.len / 2 - 1.5; if (d > -1.2 && d < 50 && d < gap) { gap = Math.max(0.01, d); dv = c.v; isPed = true; } }
      let v0 = c.vmax * wetK;
      for (const z of Z) { const xs = dir > 0 ? z.u0 : L - z.u1, xe = dir > 0 ? z.u1 : L - z.u0; const zv = z.v * c.agg; if (c.x >= xs && c.x <= xe) v0 = Math.min(v0, zv); else if (c.x < xs) v0 = Math.min(v0, Math.sqrt(zv * zv + 2 * 1.1 * (xs - c.x))); }
      const sStar = 2.2 + c.v * 1.25 + c.v * dv / (2 * Math.sqrt(1.6 * 2.6));
      let acc = 1.6 * (1 - Math.pow(c.v / Math.max(v0, 0.5), 4) - Math.pow(Math.max(sStar, 0) / Math.max(gap, 0.05), 2));
      acc = clamp(acc, -7.5, 2.2);
      if (isPed && acc < -3.2 && simT - c.lastConf > 5) { conflicts++; c.lastConf = simT; }
      c.v = Math.max(0, c.v + acc * dt); c.x += c.v * dt; c.u = dir > 0 ? c.x : L - c.x; c.brake = acc < -0.7 || c.v < 0.3;
      if (!c.counted && c.u > SIG_U - 1 && c.u < SIG_U + 1) { c.counted = true; flowCount.push(simT); }
      const tOff = laneOff(c.u, dir) + c.mo * dir; c.off += (tOff - c.off) * Math.min(1, dt * 1.8);
      const p = at(c.u, c.off); c.grp.position.set(p[0], roadY(c.u), p[1]); c.grp.rotation.y = yawAt(c.u, dir);
      c.tl.material = c.brake ? M.brake : M.tail;
    }
  }
  for (let i = cars.length - 1; i >= 0; i--) if (cars[i].x > L + 4) removeFrom(cars, i, cars[i].grp);
  while (cars.length > 140) removeFrom(cars, 0, cars[0].grp);
  // -------- bicicletas
  for (const dir of [1, -1]) {
    bikeAcc[dir] += state.fBikes / 3600 * dt;
    if (bikeAcc[dir] >= 1) { bikeAcc[dir] -= 1; spawnBike(dir, dir > 0 ? uA - 60 : uB + 60); }
  }
  for (let i = bikes.length - 1; i >= 0; i--) {
    const b = bikes[i]; let v = b.vmax * (raining ? 0.85 : 1);
    for (const o of bikes) { if (o === b || o.dir !== b.dir) continue; const d = (o.u - b.u) * b.dir; if (d > 0 && d < 5 && Math.abs(o.off - b.off) < 0.8) v = Math.min(v, o.v * 0.98); }
    b.v += (v - b.v) * Math.min(1, dt * 2); b.u += b.dir * b.v * dt;
    const t = bikeOff(b.u, b.dir); b.off += (t - b.off) * Math.min(1, dt * 0.9);
    const p = at(b.u, b.off); const onSide = Math.abs(b.off) > 6.2 || (isBuilt(b.u) && b.off > 3.15);
    b.mesh.position.set(p[0], (isBuilt(b.u) && b.off < -3.6 ? roadY(b.u) : 0) + Math.abs(Math.sin(b.ph += dt * 8)) * 0.01, p[1]); b.mesh.rotation.y = yawAt(b.u, b.dir);
    if (b.u < uA - 70 || b.u > uB + 70) removeFrom(bikes, i, b.mesh);
  }
  // -------- pedestres
  const target = Math.round(state.fPeds * (raining ? 0.6 : 1));
  if (peds.length < target && SR() < dt * 6) spawnPed(false);
  for (let i = peds.length - 1; i >= 0; i--) {
    const p = peds[i]; const built = isBuilt(p.u); let moving = true, yaw = yawAt(p.u, p.dir);
    if (p.state === 'exit') { const t = pedWalkS(p); p.s += Math.sign(t - p.s) * Math.min(Math.abs(t - p.s), p.speed * dt); yaw = yawAt(p.u, 1) + (t > p.s ? Math.PI / 2 : -Math.PI / 2); if (Math.abs(t - p.s) < 0.05) p.state = 'walk'; }
    else if (p.state === 'walk') {
      const pu = p.u; p.u += p.dir * p.speed * dt; const t = pedWalkS(p); p.s += (t - p.s) * Math.min(1, dt * 0.9);
      if (built) { for (const c of CROSS) { if (!isBuilt(c.u)) continue; if ((pu - c.u) * (p.u - c.u) <= 0 && p.lastCross !== c.u && SR() < 0.55) { p.state = 'toCurb'; p.cross = c; } } }
      else if (!inWork(p.u) && simT - p.lastCrossT > 30 && SR() < dt * 0.03) { p.state = 'wait'; p.waitT = 0; p.cross = null; }
      p.life -= dt; if (p.life < 0 && p.state === 'walk') p.state = 'enter';
    } else if (p.state === 'toCurb') { const t = p.side === 'W' ? -6.5 : 3.45; p.u += (p.cross.u - p.u) * Math.min(1, dt * 2); p.s += Math.sign(t - p.s) * Math.min(Math.abs(t - p.s), p.speed * dt); yaw = yawAt(p.u, 1) + (t > p.s ? Math.PI / 2 : -Math.PI / 2); if (Math.abs(t - p.s) < 0.05) { p.state = 'wait'; p.waitT = 0; } }
    else if (p.state === 'wait') {
      moving = false; p.waitT += dt; yaw = yawAt(p.u, 1) + (p.side === 'W' ? Math.PI / 2 : -Math.PI / 2); let go = false;
      if (p.cross && p.cross.type === 'signal' && isBuilt(p.cross.u)) go = sig.op.ped === 'W' && p.waitT > 0.4;
      else if (p.cross) go = p.waitT > 0.8;
      else { let ok = true; for (const c of cars) { const ahead = (p.u - c.u) * c.dir; if (ahead > 0 && ahead < 70 && ahead / Math.max(c.v, 2) < 4.2) { ok = false; break; } } go = (ok && p.waitT > 1) || p.waitT > 14; }
      if (go) { p.state = 'cross'; p.tgt = p.side === 'W' ? (p.cross ? 3.45 : 4.9 + p.o * 0.5) : (p.cross ? -6.5 : -5.0 + p.o * 0.5); }
    } else if (p.state === 'cross') {
      const spd = p.speed * (p.cross ? 1.05 : 1.25); p.s += Math.sign(p.tgt - p.s) * Math.min(Math.abs(p.tgt - p.s), spd * dt); yaw = yawAt(p.u, 1) + (p.tgt > p.s ? Math.PI / 2 : -Math.PI / 2);
      if (Math.abs(p.tgt - p.s) < 0.05) { p.side = p.side === 'W' ? 'E' : 'W'; p.lastCross = p.cross ? p.cross.u : -1; p.lastCrossT = simT; p.cross = null; p.state = 'walk'; if (SR() < 0.5) p.dir *= -1; }
    } else if (p.state === 'enter') { const t = frontS(p.side); p.s += Math.sign(t - p.s) * Math.min(Math.abs(t - p.s), p.speed * dt); yaw = yawAt(p.u, 1) + (t > p.s ? Math.PI / 2 : -Math.PI / 2); if (Math.abs(t - p.s) < 0.05) { removeFrom(peds, i, p.h.group); continue; } }
    if (p.u < uA - 70 || p.u > uB + 70 || peds.length > target + 25) { removeFrom(peds, i, p.h.group); continue; }
    const pp = at(p.u, p.s); const onWalk = built && ((p.s < -6.15 && p.s > -11) || (p.s > 3.15 && p.s < 10));
    const y = onWalk ? 0.15 : (Math.abs(p.s) <= 3.2 || (built && p.s < -3.1 && p.s > -6.2)) ? roadY(p.u) : 0;
    p.h.group.position.set(pp[0], y, pp[1]); p.h.group.rotation.y = yaw;
    if (moving) { p.ph += dt * p.speed * 5.6; const a = Math.sin(p.ph) * 0.5; p.h.l1.rotation.x = a; p.h.l2.rotation.x = -a; } else { p.h.l1.rotation.x *= 0.8; p.h.l2.rotation.x *= 0.8; }
    if (p.h.umb) p.h.umb.visible = raining && p.umb;
  }
  // -------- canteiro animado
  for (const r of workRig) {
    if (r.type === 'ex') { r.up.rotation.y = Math.sin(simT * 0.35) * 0.9; r.boom.rotation.x = -0.55 + Math.sin(simT * 0.7) * 0.18; r.stick.rotation.x = 1.5 + Math.sin(simT * 0.7 + 1) * 0.35; }
    if (r.type === 'roll') { r.u = lerp(r.a, r.b, 0.5 + 0.5 * Math.sin(simT * 0.12)); const p = at(r.u, -1.7); r.obj.position.set(p[0], 0, p[1]); }
    if (r.type === 'worker') { r.h.l1.rotation.x = Math.sin(simT * 2 + r.t) * 0.08; r.h.group.rotation.y += Math.sin(simT * 0.3 + r.t) * 0.003; }
    if (r.type === 'flag') { const go = r.dir > 0 ? sig.tmp.n === 'G' : sig.tmp.s === 'G'; r.pad.material.map = go ? TEX.siga : TEX.pare; }
  }
}
function seedAgents() {
  for (const dir of [1, -1]) { let x = 5; while (x < L - 5 && state.fCars > 0) { spawnCar(dir, x, 12); x += Math.max(25, 3600 / state.fCars * 13 * srnd(0.4, 1.6)); } }
  for (let i = 0; i < state.fPeds; i++) spawnPed(true);
  for (const dir of [1, -1]) for (let k = 0; k < state.fBikes / 25; k++) spawnBike(dir, srnd(uA - 40, uB + 40));
  for (let i = 0; i < 160; i++) updateAgents(0.1);
}
function clearAgents() { for (const a of [...cars]) agentsGroup.remove(a.grp); for (const a of [...peds]) agentsGroup.remove(a.h.group); for (const a of [...bikes]) agentsGroup.remove(a.mesh); cars.length = peds.length = bikes.length = 0; }

// ============================================================ Ambiente: sol, clima, noite
const LAT = -8.40 * Math.PI / 180, MONTH_DOY = [15, 46, 74, 105, 135, 166, 196, 227, 258, 288, 319, 349];
const MONTHS = ['janeiro', 'fevereiro', 'março', 'abril', 'maio', 'junho', 'julho', 'agosto', 'setembro', 'outubro', 'novembro', 'dezembro'];
function sunDir(hour, month) {
  const N = MONTH_DOY[month]; const dec = 23.44 * Math.PI / 180 * Math.sin(2 * Math.PI * (284 + N) / 365);
  const solar = hour + 0.66; const H = (solar - 12) * 15 * Math.PI / 180;
  const sinEl = Math.sin(LAT) * Math.sin(dec) + Math.cos(LAT) * Math.cos(dec) * Math.cos(H); const el = Math.asin(sinEl);
  let cosAz = (Math.sin(dec) - sinEl * Math.sin(LAT)) / (Math.cos(el) * Math.cos(LAT)); cosAz = clamp(cosAz, -1, 1); let az = Math.acos(cosAz); if (H > 0) az = 2 * Math.PI - az;
  return { v: new V3(Math.sin(az) * Math.cos(el), sinEl, -Math.cos(az) * Math.cos(el)), sinEl, el, az };
}
const WEATHER = {
  sol: { sun: 1, hemi: 1, fog: 0.0011, turb: 4, ray: 1.3, cloud: 0.22, rain: 0, wet: 0, fogCol: '#bcd0de', name: 'Sol' },
  nublado: { sun: 0.32, hemi: 0.85, fog: 0.0022, turb: 14, ray: 3, cloud: 0.9, rain: 0, wet: 0.1, fogCol: '#a9b3bb', name: 'Nublado' },
  chuva: { sun: 0.12, hemi: 0.62, fog: 0.006, turb: 20, ray: 4, cloud: 1, rain: 1, wet: 0.85, fogCol: '#8e979e', name: 'Chuva' },
  tempestade: { sun: 0.05, hemi: 0.42, fog: 0.011, turb: 20, ray: 4, cloud: 1, rain: 2.2, wet: 1, fogCol: '#6f777e', name: 'Chuva forte' },
  neblina: { sun: 0.25, hemi: 0.8, fog: 0.022, turb: 18, ray: 2, cloud: 0.5, rain: 0, wet: 0.35, fogCol: '#c6cbcf', name: 'Neblina' },
};
// nuvens, estrelas, chuva
const clouds = new THREE.Mesh(new THREE.PlaneGeometry(5000, 5000), new THREE.MeshBasicMaterial({ map: T.clouds, transparent: true, opacity: 0.3, depthWrite: false, fog: false }));
T.clouds.repeat.set(4, 4); clouds.rotation.x = Math.PI / 2; clouds.position.y = 420; scene.add(clouds);
const stars = (() => { const n = 1800, a = new Float32Array(n * 3); for (let i = 0; i < n; i++) { const th = rnd(0, 6.28), ph = Math.acos(rnd(0.05, 1)); a[3 * i] = 2500 * Math.sin(ph) * Math.cos(th); a[3 * i + 1] = 2500 * Math.cos(ph); a[3 * i + 2] = 2500 * Math.sin(ph) * Math.sin(th); } const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.BufferAttribute(a, 3)); return new THREE.Points(g, new THREE.PointsMaterial({ color: 0xffffff, size: 2.2, sizeAttenuation: false, transparent: true, opacity: 0, fog: false, depthWrite: false })); })();
scene.add(stars);
const RAIN_N = 9000; const rainPos = new Float32Array(RAIN_N * 6); const rainGeo = new THREE.BufferGeometry(); rainGeo.setAttribute('position', new THREE.BufferAttribute(rainPos, 3));
const rain = new THREE.LineSegments(rainGeo, new THREE.LineBasicMaterial({ color: 0xc8d4de, transparent: true, opacity: 0.38, depthWrite: false })); rain.frustumCulled = false; rain.visible = false; scene.add(rain);
const rainSeed = new Float32Array(RAIN_N * 3); for (let i = 0; i < RAIN_N; i++) { rainSeed[3 * i] = Math.random(); rainSeed[3 * i + 1] = Math.random(); rainSeed[3 * i + 2] = Math.random(); }
let envKey = '', envTimer = 0, lightTimer = 0, nightK = 0;
const cSunLow = new THREE.Color('#ff9a52'), cSunHigh = new THREE.Color('#fff4e6'), cNight = new THREE.Color('#0a1020');
function updateEnvironment(dt) {
  const nowMs = performance.now();
  const W = WEATHER[state.weather]; const sd = sunDir(state.hour, state.month); const sinEl = sd.sinEl;
  const day = smooth(-0.1, 0.12, sinEl); nightK = 1 - smooth(-0.14, 0.04, sinEl);
  skyU.sunPosition.value.copy(sd.v); skyU.turbidity.value = W.turb; skyU.rayleigh.value = W.ray * (0.6 + 0.4 * day) + 0.2; skyU.mieCoefficient.value = W.cloud > 0.8 ? 0.02 : 0.005;
  const tgt = controls.target; const snap = new V3(Math.round(tgt.x / 8) * 8, 0, Math.round(tgt.z / 8) * 8);
  if (sinEl > -0.02) { sun.position.copy(snap).addScaledVector(sd.v, 600); sun.color.copy(cSunLow).lerp(cSunHigh, smooth(0.0, 0.45, sinEl)); sun.intensity = 3.3 * smooth(-0.02, 0.18, sinEl) * W.sun; }
  else { sun.position.copy(snap).add(new V3(150, 420, 200)); sun.color.set('#9fb4ff'); sun.intensity = 0.22 * (W.sun > 0.2 ? 1 : 0.4); }
  sun.target.position.copy(snap); sun.target.updateMatrixWorld();
  hemi.intensity = (0.04 + 1.1 * day) * W.hemi + 0.09; hemi.color.set('#bcd6ff').lerp(new THREE.Color('#33405e'), nightK); hemi.groundColor.set('#6b5a46').lerp(new THREE.Color('#141414'), nightK);
  const fogC = new THREE.Color(W.fogCol); if (sinEl < 0.2) fogC.lerp(new THREE.Color('#e8a878'), smooth(0.2, 0.03, sinEl) * smooth(-0.1, 0.03, sinEl) * (W.sun > 0.5 ? 0.6 : 0.2)); fogC.lerp(cNight, nightK * 0.95);
  scene.fog.color.copy(fogC); scene.fog.density = W.fog * (1 + nightK * 0.3) * (1 - 0.8 * smooth(70, 320, camera.position.y));
  const heavy = W.fog > 0.005; const dark = nightK > 0.92; sky.visible = !heavy && !dark; scene.background = heavy ? fogC : dark ? new THREE.Color('#05080f') : null;
  clouds.material.opacity = W.cloud * (0.35 + 0.65 * day); clouds.material.color.set(W.rain ? '#8a9097' : '#ffffff').multiplyScalar(0.15 + 0.85 * day); T.clouds.offset.x += dt * 0.0015;
  stars.material.opacity = nightK * (W.cloud > 0.8 ? 0.05 : 0.9 - W.cloud * 0.6);
  renderer.toneMappingExposure = lerp(0.6, 0.82, nightK) * (W.rain ? 1.1 : 1);
  // chuva
  rain.visible = W.rain > 0; if (rain.visible) { const n = Math.floor(RAIN_N * Math.min(1, W.rain / 2.2 + 0.4)); rainGeo.setDrawRange(0, n * 2); const c = camera.position, t = performance.now() / 1000; const len = 0.55 + W.rain * 0.2; for (let i = 0; i < n; i++) { const y = (((rainSeed[3 * i + 1] * 40 - t * 18 * (0.8 + rainSeed[3 * i + 2] * 0.4)) % 40) + 40) % 40 - 10; const x = c.x + (rainSeed[3 * i] - 0.5) * 70, z = c.z + (rainSeed[3 * i + 2] - 0.5) * 70; const j = 6 * i; rainPos[j] = x; rainPos[j + 1] = c.y + y; rainPos[j + 2] = z; rainPos[j + 3] = x + 0.04; rainPos[j + 4] = c.y + y - len; rainPos[j + 5] = z + 0.02; } rainGeo.attributes.position.needsUpdate = true; rain.material.opacity = 0.25 + 0.1 * W.rain - nightK * 0.12; }
  // superfícies molhadas
  for (const m of ROADMATS) { m.roughness = lerp(m.userData.r0, 0.22, W.wet); m.color.setScalar(lerp(1, 0.72, W.wet)); }
  // iluminação pública e veículos
  const lampsOn = nightK > 0.35 || (W.sun < 0.15 && sinEl < 0.25);
  const lk = lampsOn ? Math.max(nightK, 0.45) : 0;
  M.lampLED.emissiveIntensity = lk * 5; M.lampOld.emissiveIntensity = lk * 4; M.glow.opacity = lk * 0.55; M.glowOld.opacity = lk * 0.38;
  M.head.emissiveIntensity = lampsOn ? 5 : 0.25; M.beam.opacity = lk * 0.32; M.tail.emissiveIntensity = lampsOn ? 1.4 : 0.15;
  M.winLit.emissiveIntensity = 1.6; winLitMeshes.forEach(m => m.visible = nightK > 0.45);
  if (nowMs - lightTimer > 400) { lightTimer = nowMs; assignPointLights(); }
  for (const p of PL) p.intensity = p.userData.base * lk;
  const key = state.weather + '|' + Math.round(state.hour * 4) + '|' + state.month;
  if (key !== envKey && nowMs - envTimer > 500) { envKey = key; envTimer = nowMs; for (const k of ['turbidity', 'rayleigh', 'mieCoefficient', 'mieDirectionalG']) sky2.material.uniforms[k].value = skyU[k].value; sky2.material.uniforms.sunPosition.value.copy(sd.v); if (envRT) envRT.dispose(); envRT = pmrem.fromScene(envScene, 0, 1, 2000); scene.environment = envRT.texture; setEnvK((0.04 + 0.96 * day) * (0.5 + 0.5 * W.hemi)); }
}
let winLitMeshes = []; let envK = 1;
function setEnvK(k) { envK = k; scene.traverse(o => { if (!o.material) return; const ms = Array.isArray(o.material) ? o.material : [o.material]; for (const m of ms) if (m.isMeshStandardMaterial) m.envMapIntensity = k; }); }
function assignPointLights() {
  const t = controls.target; const cand = lightCandidates.map(l => ({ l, d: (l.x - t.x) ** 2 + (l.z - t.z) ** 2 })).sort((a, b) => a.d - b.d).slice(0, PL.length);
  PL.forEach((p, i) => { const c = cand[i]; if (!c) { p.userData.base = 0; return; } p.position.set(c.l.x, c.l.y - 0.4, c.l.z); const led = c.l.kind; p.color.set(led ? (led === 'ped' ? '#fff3e0' : '#fff6ea') : '#ffb060'); p.distance = led === 'ped' ? 16 : 32; p.userData.base = led ? (led === 'ped' ? 60 : 220) : 110; });
}

// ============================================================ Rótulos
const labelsEl = document.getElementById('labels'); let LBL = [];
function buildLabels() {
  labelsEl.innerHTML = ''; LBL = [];
  const ph = state.phase, f = ufront();
  const defs = ph === 'hoje' ? [
    [SIG_U - 30, -7.5, 1.8, 'Acostamento de terra — sem calçada', 'w'], [SIG_U + 22, 6.2, 1.8, 'Pedestres disputam espaço com veículos', 'w'], [SIG_U, 0, 2.2, 'Travessia sem proteção · 60 km/h', 'w'],
    [SIG_U - 75, -13, 5, 'Talude exposto e erosão', 'w'], [SIG_U + 70, -3.6, 1.2, 'Sem drenagem superficial / meio-fio', 'w'], [SIG_U + 110, 10.5, 4.6, 'Comércio sem acesso organizado', 'w'], [SIG_U - 140, -40, 18, 'Comunidade Rurópolis 2 / Alto São João', '']]
    : ph === 'op' ? [
      [SIG_U - 25, -9.1, 1.6, 'Calçada acessível 3,5 m + piso tátil', 'p'], [SIG_U - 60, -4.9, 1.2, 'Ciclovia bidirecional 2,5 m', 'p'], [SIG_U - 90, 1.6, 1.8, 'Faixas de 3,0 m · Zona 30 km/h', 'p'],
      [SIG_U, -1.5, 6.4, 'Travessia semaforizada com botoeira', 'p'], [CROSS[0].u, 0, 1.6, 'Travessia elevada (traffic calming)', 'p'], [CROSS[2].u, 0, 1.6, 'Travessia elevada', 'p'], [BUS[0].u, 7.9, 3.4, 'Abrigo de ônibus + baia', 'p'],
      [SIG_U + 70, 4.4, 6.5, 'Canteiro arborizado (oiti / ipê)', 'p'], [SIG_U - 120, -6.8, 9.8, 'Iluminação LED veicular + pedonal', 'p'], [uA - 10, 0, 7.2, 'Portal de entrada — Zona 30', 'p'], [SIG_U + 100, 7.1, 1.6, 'Calçada 3,0 m', 'p'], [SIG_U - 150, -11.3, 1.6, 'Contenção do talude', 'p'], [BAYS[1][0] + 15, 4.4, 1.4, 'Baia de estacionamento', 'p']]
      : [[f + WZ / 2, -7, 4.5, 'Frente de obra: drenagem, meio-fio e calçada', 'o'], [f - 20, 4.4, 4.0, 'Pare-e-siga com semáforo provisório', 'o'], [Math.max(uA + 20, f - 60), -4.9, 1.6, 'Trecho concluído', 'p'], [Math.min(uB - 10, f + WZ + 50), 0, 1.6, 'Trecho a executar', 'w'], [f + WZ / 2 + 5, 7.4, 3.4, 'Canteiro de obras', 'o'], [f + 30, -2.2, 1.9, 'Passagem protegida de pedestres', 'o'], [f - 90, 5, 2.6, 'Sinalização provisória · 30 km/h', 'o']];
  for (const [u, s, h, t, c] of defs) { const p = at(u, s); const el = document.createElement('div'); el.className = 'lbl ' + c; el.textContent = t; labelsEl.appendChild(el); LBL.push({ el, v: new V3(p[0], h + (s < -11 ? terrainH(p[0], p[1]) : 0), p[1]) }); }
}
const _v = new V3();
function updateLabels() {
  labelsEl.style.display = state.labels ? '' : 'none'; if (!state.labels) return;
  const W = innerWidth, H = innerHeight;
  for (const l of LBL) { _v.copy(l.v).project(camera); const d = camera.position.distanceTo(l.v); if (_v.z > 1 || d > 320 || Math.abs(_v.x) > 1.1 || Math.abs(_v.y) > 1.1) { l.el.style.display = 'none'; continue; } l.el.style.display = ''; l.el.style.left = ((_v.x * 0.5 + 0.5) * W) + 'px'; l.el.style.top = ((-_v.y * 0.5 + 0.5) * H) + 'px'; l.el.style.opacity = clamp(1.5 - d / 260, 0.4, 1); }
}

// ============================================================ Câmeras
let camTween = null, follow = null;
function camSpec(name) {
  const S = (u, s, h) => { const p = at(u, s); return new V3(p[0], h, p[1]); };
  const f = ufront();
  switch (name) {
    case 'aerea': { const t = S(SIG_U, 0, 0); return { pos: t.clone().add(new V3(135, 105, 120)), tgt: t }; }
    case 'planta': { const t = S(SIG_U, -1, 0); return { pos: t.clone().add(new V3(0, 430, 1)), tgt: t }; }
    case 'drone': return { pos: S(SIG_U - 62, -0.8, 13), tgt: S(SIG_U - 8, -0.8, 2.2) };
    case 'pedestre': return { pos: S(SIG_U - 48, state.phase === 'op' ? -9.2 : -5.4, 1.65), tgt: S(SIG_U + 10, -2.5, 1.3) };
    case 'obra': return { pos: S(f - 35, 22, 22), tgt: S(f + 25, -3, 0) };
    case 'sinal': return { pos: S(SIG_U - 30, 7.2, 3.2), tgt: S(SIG_U + 2, -2, 1.5) };
    case 'elevada': return { pos: S(CROSS[0].u - 28, -9.4, 2.6), tgt: S(CROSS[0].u + 4, -1, 0.6) };
    case 'noite': return { pos: S(SIG_U - 70, 10, 9), tgt: S(SIG_U + 10, -2, 1) };
    case 'secao': return { pos: S(SIG_U - 18, 0.5, 2.4), tgt: S(SIG_U + 30, 0.5, 1.2) };
    case 'geral': { const t = S(SIG_U, 0, 0); return { pos: t.clone().add(new V3(-210, 160, 260)), tgt: S(SIG_U - 20, 0, 0) }; }
  }
  return null;
}
function setCam(name, instant = false) {
  state.cam = name; follow = null; document.querySelectorAll('#camRow button').forEach(b => b.classList.toggle('on', b.dataset.cam === name));
  if (name === 'motorista' || name === 'ciclista') { follow = name; return; }
  const sp = camSpec(name); if (!sp) return; flyTo(sp.pos, sp.tgt, instant ? 0 : 1.6);
}
function flyTo(pos, tgt, dur = 1.6) { if (dur <= 0) { camera.position.copy(pos); controls.target.copy(tgt); controls.update(); camTween = null; return; } camTween = { p0: camera.position.clone(), t0: controls.target.clone(), p1: pos.clone(), t1: tgt.clone(), k: 0, dur }; }
let followObj = null;
function updateCamera(dt) {
  if (camTween) { camTween.k = Math.min(1, camTween.k + dt / camTween.dur); const e = camTween.k < 0.5 ? 4 * camTween.k ** 3 : 1 - Math.pow(-2 * camTween.k + 2, 3) / 2; camera.position.lerpVectors(camTween.p0, camTween.p1, e); controls.target.lerpVectors(camTween.t0, camTween.t1, e); if (camTween.k >= 1) camTween = null; }
  if (follow) {
    if (follow === 'motorista') { if (!followObj || !cars.includes(followObj) || followObj.x > L - 30) followObj = cars.filter(c => c.dir > 0 && c.type !== 'bus' && c.type !== 'truck' && c.type !== 'moto' && c.x < uA - 20).sort((a, b) => b.x - a.x)[0] || cars[0]; }
    else { if (!followObj || !bikes.includes(followObj) || followObj.u > uB + 40) followObj = bikes.filter(b => b.dir > 0 && b.u < SIG_U - 60).sort((a, b) => b.u - a.u)[0] || bikes[0]; }
    if (followObj) { const u = followObj.u, d = followObj.dir; const o = followObj.off; const back = follow === 'motorista' ? 8 : 4, up = follow === 'motorista' ? 2.8 : 1.9; const p = at(u - back * d, o), t = at(u + 14 * d, o * 0.7); const P = new V3(p[0], up + roadY(u), p[1]), Tg = new V3(t[0], 1.2, t[1]); camera.position.lerp(P, Math.min(1, dt * 4)); controls.target.lerp(Tg, Math.min(1, dt * 4)); }
  }
}

// ============================================================ Interface
const $ = (id) => document.getElementById(id);
function fmtH(h) { const hh = Math.floor(h), mm = Math.floor((h - hh) * 60); return String(hh).padStart(2, '0') + ':' + String(mm).padStart(2, '0'); }
const monthSel = $('month'); MONTHS.forEach((m, i) => { const o = document.createElement('option'); o.value = i; o.textContent = m[0].toUpperCase() + m.slice(1); monthSel.appendChild(o); });
function syncUI() {
  document.querySelectorAll('#phaseBar button').forEach(b => b.classList.toggle('on', b.dataset.phase === state.phase));
  document.querySelectorAll('#weatherRow button').forEach(b => b.classList.toggle('on', b.dataset.w === state.weather));
  $('secObra').style.display = state.phase === 'obra' ? '' : 'none'; $('prog').value = state.prog; $('progV').textContent = Math.round(state.prog * 100) + '%';
  $('hour').value = state.hour; $('hourV').textContent = fmtH(state.hour); monthSel.value = state.month;
  $('tLabels').classList.toggle('on', state.labels); $('tAgents').classList.toggle('on', state.agents); $('tAnim').classList.toggle('on', state.anim);
  $('fCars').value = state.fCars; $('fCarsV').textContent = state.fCars; $('fPeds').value = state.fPeds; $('fPedsV').textContent = state.fPeds; $('fBikes').value = state.fBikes; $('fBikesV').textContent = state.fBikes;
  $('daySpeed').value = state.daySpeed; $('daySpeedV').textContent = state.daySpeed.toFixed(2).replace('.', ',') + ' h/s';
}
function setPhase(ph, prog) { const changed = ph !== state.phase || (prog !== undefined && prog !== state.prog); state.phase = ph; if (prog !== undefined) state.prog = prog; if (changed) { buildPhase(); conflicts = 0; conflictsT0 = simT; flowCount = []; } syncUI(); }
document.querySelectorAll('#phaseBar button').forEach(b => b.onclick = () => { stopPres(); setPhase(b.dataset.phase); });
let progT = null; $('prog').oninput = (e) => { state.prog = +e.target.value; $('progV').textContent = Math.round(state.prog * 100) + '%'; clearTimeout(progT); progT = setTimeout(() => { buildPhase(); }, 120); };
$('hour').oninput = (e) => { state.hour = +e.target.value; $('hourV').textContent = fmtH(state.hour); };
monthSel.onchange = (e) => { state.month = +e.target.value; };
$('daySpeed').oninput = (e) => { state.daySpeed = +e.target.value; syncUI(); };
for (const [id, k] of [['tLabels', 'labels'], ['tAgents', 'agents'], ['tAnim', 'anim']]) $(id).onclick = () => { state[k] = !state[k]; if (k === 'agents') agentsGroup.visible = state.agents; syncUI(); };
document.querySelectorAll('#weatherRow button').forEach(b => b.onclick = () => { state.weather = b.dataset.w; syncUI(); });
for (const [id, k] of [['fCars', 'fCars'], ['fPeds', 'fPeds'], ['fBikes', 'fBikes']]) $(id).oninput = (e) => { state[k] = +e.target.value; syncUI(); };
document.querySelectorAll('#camRow button').forEach(b => b.onclick = () => { stopPres(); setCam(b.dataset.cam); });
const PRESETS = { dia: { hour: 10, weather: 'sol' }, noite: { hour: 20, weather: 'sol' }, sol: { weather: 'sol', hour: 12.5 }, chuva: { weather: 'chuva', hour: 15 }, neblina: { weather: 'neblina', hour: 6.3 }, pessoas: { fPeds: 230 }, carros: { fCars: 950 }, bikes: { fBikes: 340, cam: 'ciclista' }, pico: { hour: 17.6, fCars: 900, fPeds: 180, fBikes: 160 }, calmo: { fCars: 150, fPeds: 40, fBikes: 40 } };
document.querySelectorAll('#presetRow button').forEach(b => b.onclick = () => { const p = PRESETS[b.dataset.p]; Object.assign(state, p); if (p.hour !== undefined) state.anim = false; if (p.cam) setCam(p.cam); syncUI(); });
$('panelToggle').onclick = () => $('panel').classList.toggle('open');
controls.addEventListener('start', () => { if (follow) { follow = null; document.querySelectorAll('#camRow button').forEach(b => b.classList.remove('on')); } camTween = null; });
// HUD
let hudT = 0;
function updateHUD(dt) {
  hudT -= dt; if (hudT > 0) return; hudT = 0.25;
  $('hTime').textContent = fmtH(state.hour) + ' · ' + 15 + ' de ' + MONTHS[state.month];
  $('hPhase').textContent = state.phase === 'hoje' ? 'Hoje (situação atual)' : state.phase === 'obra' ? `Obra · ${Math.round(state.prog * 100)}% executado` : 'Operação (proposta)';
  $('hW').textContent = WEATHER[state.weather].name;
  const inSeg = cars.filter(c => c.u > uA && c.u < uB); $('hCars').textContent = cars.filter(c => c.u > uA - 40 && c.u < uB + 40).length;
  $('hSpd').textContent = inSeg.length ? Math.round(inSeg.reduce((a, c) => a + c.v, 0) / inSeg.length * 3.6) + ' km/h' : '–';
  $('hPeds').textContent = peds.length + ' / ' + bikes.filter(b => b.u > uA - 40 && b.u < uB + 40).length;
  flowCount = flowCount.filter(t => simT - t < 120); $('hFlow').textContent = simT - conflictsT0 > 20 ? Math.round(flowCount.length * 3600 / Math.min(120, simT - conflictsT0)) + ' veíc./h' : 'medindo…';
  const mins = Math.max(1, (simT - conflictsT0) / 60); $('hConf').textContent = conflicts + ' (' + (conflicts / mins).toFixed(1).replace('.', ',') + '/min)';
  const sc = $('sigchip'); const dot = (c) => `<span class="dot" style="background:${c}"></span>`;
  if (state.phase === 'op' || (state.phase === 'obra' && isBuilt(SIG_U))) sc.innerHTML = `${dot(sig.op.veh === 'G' ? '#2aff7a' : sig.op.veh === 'Y' ? '#ffb01a' : '#ff2a1a')} Veículos &nbsp; ${dot(sig.op.ped === 'W' ? '#3cff7a' : sig.op.ped === 'F' ? '#ff8a3a' : '#ff3b2f')} Pedestres · ${Math.ceil(sig.op.rem)} s`;
  else if (state.phase === 'obra') sc.innerHTML = `Pare-e-siga: ${dot(sig.tmp.n === 'G' ? '#2aff7a' : sig.tmp.n === 'Y' ? '#ffb01a' : '#ff2a1a')} sentido norte &nbsp; ${dot(sig.tmp.s === 'G' ? '#2aff7a' : sig.tmp.s === 'Y' ? '#ffb01a' : '#ff2a1a')} sentido sul`;
  else sc.innerHTML = '<span class="k">Sem semáforo ou travessia protegida</span>';
}

// ============================================================ Apresentação
const STEPS = [
  { t: 'PE-060 · Travessia urbana de Ipojuca', x: 'Segmento urbano da PE-060 junto às comunidades de <b>Rurópolis 2 / Alto São João</b>, em Ipojuca. A rodovia estadual funciona como rua principal do bairro: concentra comércio, pontos de ônibus e a travessia diária de moradores. O trecho integra o eixo de <b>Travessias Urbanas</b> do Componente 3 (Obras Seguras e Resilientes) do Programa Rodovias Resilientes — DER-PE / Banco Mundial.', ph: 'hoje', cam: 'geral', hour: 9.5, w: 'sol' },
  { t: 'Diagnóstico — como é hoje', x: '<ul><li>Pista simples de ~7 m, sem calçadas, com acostamentos de terra irregulares.</li><li>Pedestres caminhando na borda da pista e atravessando em qualquer ponto.</li><li>Velocidade praticada incompatível com o uso urbano (≈ 60 km/h).</li><li>Talude exposto a oeste e drenagem superficial inexistente.</li></ul>', ph: 'hoje', cam: 'pedestre', hour: 10, w: 'sol', labels: true },
  { t: 'Conflitos entre veículos e pedestres', x: 'Com fluxo intenso, as travessias sem proteção geram frenagens bruscas. O painel ao lado conta os <b>conflitos simulados veículo × pedestre</b>. Compare depois com a fase de operação.', ph: 'hoje', cam: 'drone', hour: 17.5, w: 'sol', fCars: 750, fPeds: 160 },
  { t: 'Concepção — diretrizes do Banco Mundial', x: 'Inspirada no estudo <i>Urban Crossings Transformation</i> (World Bank, E. Urcola), a proposta transforma a rodovia em <b>rua completa</b>:<ul><li>Zona 30 km/h com portais de entrada e travessias elevadas;</li><li>Segregação de modos: calçadas acessíveis, ciclovia e faixas de 3,0 m;</li><li>Travessia semaforizada no ponto de maior demanda;</li><li>Arborização, iluminação LED, drenagem e contenção do talude.</li></ul>', ph: 'op', cam: 'aerea', hour: 10, w: 'sol', fCars: 420, fPeds: 80 },
  { t: 'Seção transversal proposta (≈ 21 m)', x: 'Oeste → leste: contenção + <b>calçada 3,5 m</b> com piso tátil · canteiro 1,2 m · <b>ciclovia bidirecional 2,5 m</b> · separador 0,5 m · <b>2 faixas de 3,0 m</b> · canteiro/baia 2,4 m · <b>calçada 3,0 m</b> · testada 1,4 m. Abra <i>Planta baixa & seção</i> para ver as cotas e os quantitativos.', ph: 'op', cam: 'secao', hour: 11, w: 'sol', btn: ['Abrir seção transversal', () => openPlan('sec')] },
  { t: 'Execução — mobilização e 1ª frente', x: 'A obra avança por frentes de ~90 m no sentido sul → norte. Na frente ativa, a faixa oeste é fechada e o tráfego passa em <b>meia pista com pare-e-siga</b> e semáforo provisório. Executam-se drenagem (tubos e caixas), meio-fio, base da calçada e da ciclovia.', ph: 'obra', prog: 0.08, cam: 'obra', hour: 9, w: 'sol' },
  { t: 'Execução — avanço da obra', x: 'Atrás da frente, o trecho já recebe pavimento novo, sinalização e arborização jovem. Pedestres circulam por <b>passagem protegida</b> entre cones, separada da escavação. Use o controle <i>Avanço da obra</i> para ver qualquer etapa.', ph: 'obra', prog: 0.55, cam: 'obra', hour: 14, w: 'nublado' },
  { t: 'Execução — fase final', x: 'A última frente fecha o trecho norte. Concluídos, os segmentos já operam como Zona 30, com travessias e iluminação definitivas.', ph: 'obra', prog: 0.96, cam: 'obra', hour: 16, w: 'sol' },
  { t: 'Operação — travessia semaforizada', x: 'No ponto de maior demanda, semáforo veicular e de pedestres com <b>botoeira</b>, faixa de pedestres contínua sobre a ciclovia e rampas acessíveis. O ciclo simulado é de 62 s, com 14 s de verde para pedestres e 5 s de verde piscante.', ph: 'op', cam: 'sinal', hour: 16.5, w: 'sol', fPeds: 110 },
  { t: 'Operação — travessias elevadas e ciclovia', x: 'As <b>travessias elevadas</b> (no nível da calçada) reduzem a velocidade dos veículos para ~15 km/h e dão prioridade ao pedestre. A ciclovia bidirecional segregada liga as duas pontas do bairro.', ph: 'op', cam: 'elevada', hour: 8, w: 'sol', fBikes: 180 },
  { t: 'Noite — iluminação LED', x: 'Postes LED veiculares a cada 30 m em cada lado, intercalados, mais luminárias pedonais de 4,5 m nas calçadas e reforço sobre as travessias. Compare com a iluminação pontual de hoje (vapor de sódio em poste de concreto).', ph: 'op', cam: 'noite', hour: 19.6, w: 'sol' },
  { t: 'Chuva — drenagem e acessibilidade', x: 'Meio-fio, sarjeta e rede de drenagem retiram a água da pista; a calçada elevada permanece transitável. Com a chuva há menos pedestres, mais guarda-chuvas e velocidades menores.', ph: 'op', cam: 'drone', hour: 15, w: 'chuva' },
  { t: 'Resultado esperado', x: 'Uma rua segura para quem mora, compra e circula: velocidade média próxima de 30 km/h, pedestres e ciclistas segregados, travessias protegidas e espaço público qualificado. Veja os <b>quantitativos indicativos</b> em <i>Planta baixa & seção</i>.', ph: 'op', cam: 'aerea', hour: 10, w: 'sol', fCars: 420, fPeds: 80, fBikes: 80, btn: ['Ver quantitativos', () => openPlan('qt')] },
];
let presI = -1, presPlay = true, presTimer = 0; const PRES_DUR = 14;
function showStep(i) {
  presI = clamp(i, 0, STEPS.length - 1); const s = STEPS[presI]; presTimer = 0;
  $('pres').classList.add('show'); $('pStep').textContent = `Etapa ${presI + 1} de ${STEPS.length}`; $('pTitle').textContent = s.t; $('pText').innerHTML = s.x;
  if (s.btn) { const b = document.createElement('button'); b.textContent = s.btn[0]; b.style.marginTop = '8px'; b.onclick = s.btn[1]; $('pText').appendChild(document.createElement('br')); $('pText').appendChild(b); }
  state.anim = false; Object.assign(state, { hour: s.hour ?? state.hour, weather: s.w ?? state.weather, fCars: s.fCars ?? 420, fPeds: s.fPeds ?? 80, fBikes: s.fBikes ?? 60, labels: s.labels ?? true });
  setPhase(s.ph, s.prog ?? state.prog); setCam(s.cam); syncUI();
}
function stopPres() { presI = -1; $('pres').classList.remove('show'); }
$('bPres').onclick = () => { presPlay = true; $('pPlay').textContent = '⏸ Pausar'; showStep(0); };
$('pNext').onclick = () => showStep(presI + 1); $('pPrev').onclick = () => showStep(presI - 1); $('pClose').onclick = stopPres;
$('pPlay').onclick = () => { presPlay = !presPlay; $('pPlay').textContent = presPlay ? '⏸ Pausar' : '▶ Continuar'; };
function updatePres(dt) { if (presI < 0) return; if (presPlay) presTimer += dt; $('pBar').style.width = ((presI + Math.min(1, presTimer / PRES_DUR)) / STEPS.length * 100) + '%'; if (presPlay && presTimer > PRES_DUR) { if (presI < STEPS.length - 1) showStep(presI + 1); else { presPlay = false; $('pPlay').textContent = '▶ Continuar'; } } }

// ============================================================ Planta baixa, seção e quantitativos
document.querySelectorAll('.modal').forEach(m => { m.addEventListener('click', (e) => { if (e.target === m || e.target.dataset.close !== undefined) m.classList.remove('show'); }); });
$('bPlan').onclick = () => openPlan('plan-op');
document.querySelectorAll('#mPlan .tab').forEach(b => b.onclick = () => openPlan(b.dataset.tab));
function openPlan(tab) { $('mPlan').classList.add('show'); document.querySelectorAll('#mPlan .tab').forEach(b => b.classList.toggle('on', b.dataset.tab === tab)); const body = $('planBody'); if (tab.startsWith('plan')) body.innerHTML = planHTML(tab === 'plan-op'); else if (tab === 'sec') body.innerHTML = sectionHTML(); else body.innerHTML = quantHTML(); if (tab.startsWith('plan')) enablePanZoom(); }
const PX = (x, z) => [(-z).toFixed(2), (x).toFixed(2)];
function strip(u0, u1, a, b, fill, step = 3, extra = '') { const pts = []; for (let u = u0; u <= u1 + 0.01; u += Math.min(step, Math.max(0.5, u1 - u))) { const p = at(Math.min(u, u1), a); pts.push(PX(p[0], p[1]).join(',')); if (u >= u1) break; } { const p = at(u1, a); pts.push(PX(p[0], p[1]).join(',')); } for (let u = u1; u >= u0 - 0.01; u -= Math.min(step, Math.max(0.5, u - u0))) { const p = at(Math.max(u, u0), b); pts.push(PX(p[0], p[1]).join(',')); if (u <= u0) break; } { const p = at(u0, b); pts.push(PX(p[0], p[1]).join(',')); } return `<polygon points="${pts.join(' ')}" fill="${fill}" ${extra}/>`; }
function line(u0, u1, s, stroke, w, dash = '') { const pts = []; for (let u = u0; u <= u1; u += 4) { const p = at(u, s); pts.push(PX(p[0], p[1]).join(',')); } const p = at(u1, s); pts.push(PX(p[0], p[1]).join(',')); return `<polyline points="${pts.join(' ')}" fill="none" stroke="${stroke}" stroke-width="${w}" ${dash ? `stroke-dasharray="${dash}"` : ''}/>`; }
function txt(u, s, t, size = 2.4, col = '#222', anchor = 'middle', weight = 600) { const p = at(u, s); const [x, y] = PX(p[0], p[1]); return `<text x="${x}" y="${y}" font-size="${size}" fill="${col}" text-anchor="${anchor}" font-family="Inter,Arial" font-weight="${weight}">${t}</text>`; }
function circ(u, s, r, fill, stroke = 'none') { const p = at(u, s); const [x, y] = PX(p[0], p[1]); return `<circle cx="${x}" cy="${y}" r="${r}" fill="${fill}" stroke="${stroke}" stroke-width="0.15"/>`; }
function planSVG(prop) {
  const a = uA - 40, b = uB + 40; let s = '';
  // edificações
  for (const h of HOUSES) { const d = lateralOf(h.x, h.z); if (Math.abs(d) > 70) continue; const hu = h.u ?? 0; if (h.u !== undefined && (h.u < a - 10 || h.u > b + 10)) continue; const c = [[-1, -1], [1, -1], [1, 1], [-1, 1]].map(([i, j]) => PX(h.x + h.tx * i * h.w / 2 + h.rx * j * h.d / 2, h.z + h.tz * i * h.w / 2 + h.rz * j * h.d / 2).join(',')); s += `<polygon points="${c.join(' ')}" fill="${h.shop ? '#d9cbb3' : '#d4cfc6'}" stroke="#a9a293" stroke-width="0.15"/>`; if (h.label) { const [x, y] = PX(h.x, h.z); s += `<text x="${x}" y="${y}" font-size="3" text-anchor="middle" fill="#555" font-family="Inter">${h.label}</text>`; } }
  if (!prop) { s += strip(a, b, -11.7, -3.4, '#d3a27a') + strip(a, b, 3.4, 9.9, '#d3a27a') + strip(a, b, -3.5, 3.5, '#8b8b8a') + line(a, b, 0, '#e0b040', 0.15) + line(a, b, 3.25, '#eee', 0.12, '1 1'); }
  else {
    s += strip(a, uA, -11.7, -3.4, '#d3a27a') + strip(a, uA, 3.4, 9.9, '#d3a27a') + strip(a, uA, -3.5, 3.5, '#8b8b8a') + strip(uB, b, -11.7, -3.4, '#d3a27a') + strip(uB, b, 3.4, 9.9, '#d3a27a') + strip(uB, b, -3.5, 3.5, '#8b8b8a');
    s += strip(uA - 18, uA, -3.5, 3.5, '#9a4434') + strip(uB, uB + 18, -3.5, 3.5, '#9a4434');
    s += strip(uA, uB, -11.6, -10.9, '#b9b5ac') + strip(uA, uB, -10.9, -7.35, '#cfccc4') + strip(uA, uB, -9.45, -9.05, '#e6c22c') + strip(uA, uB, -7.35, -6.15, '#86ad5a') + strip(uA, uB, -6.15, -3.65, '#b4554a') + strip(uA, uB, -3.65, -3.15, '#e8e6e0') + strip(uA, uB, -3.15, 3.15, '#55565a') + strip(uA, uB, 3.15, 5.55, '#86ad5a') + strip(uA, uB, 5.55, 8.6, '#cfccc4') + strip(uA, uB, 6.9, 7.3, '#e6c22c') + strip(uA, uB, 8.6, 9.95, '#bdb9b0');
    for (const [b0, b1, k] of BAYS) s += strip(b0, b1, 3.15, 5.55, '#55565a') + txt((b0 + b1) / 2, 4.6, k === 'bus' ? 'BAIA ÔNIBUS' : 'ESTAC.', 1.1, '#fff');
    for (const c of CROSS) { s += strip(c.u - 4.6, c.u + 4.6, -7.35, -6.15, '#cfccc4') + strip(c.u - 4.6, c.u + 4.6, 3.15, 5.55, '#cfccc4') + strip(c.u - 4.6, c.u + 4.6, -3.65, -3.15, '#55565a'); if (c.type === 'raised') s += strip(c.u - 4.6, c.u + 4.6, -6.15, 3.15, '#6e6f73'); for (let k = -6.0; k < 3.0; k += 0.8) s += strip(c.u - 2, c.u + 2, k, k + 0.4, '#fff', 1); }
    const cuts = CUTS.map(c => [c[0] - 2, c[1] + 2]); for (const [p0, p1] of subtract(uA, uB, cuts)) { s += line(p0, p1, -0.15, '#f0b41c', 0.12) + line(p0, p1, 0.15, '#f0b41c', 0.12) + line(p0, p1, -4.9, '#fff', 0.12, '1 2'); }
    for (let u = uA + 4; u < uB; u += 9) { if (CUTS.some(c => u > c[0] - 1.5 && u < c[1] + 1.5)) continue; s += circ(u, -6.82, 1.6, 'rgba(60,120,50,.55)', '#2f5a24'); if (!BAYS.some(bb => u > bb[0] - 1 && u < bb[1] + 1)) s += circ(u, 4.4, 1.6, 'rgba(60,120,50,.55)', '#2f5a24'); }
    for (let u = uA + 6; u < uB - 2; u += 30) { s += circ(u, -6.75, 0.35, '#f2b233', '#333') + circ(u + 15, 4.4, 0.35, '#f2b233', '#333'); }
    for (const bb of BUS) { const ss = bb.side === 'E' ? 7.9 : -10.0; s += strip(bb.u - 2.2, bb.u + 2.2, ss - 0.95, ss + 0.95, '#2f6fb6'); }
    s += circ(SIG_U - 6.5, 3.7, 0.5, '#c8242b', '#111') + circ(SIG_U + 6.5, -3.4, 0.5, '#c8242b', '#111');
    s += txt(SIG_U, -14.5, 'TRAVESSIA SEMAFORIZADA', 1.8, '#c8242b') + txt(CROSS[0].u, -14.5, 'TRAVESSIA ELEVADA', 1.8, '#333') + txt(CROSS[2].u, -14.5, 'TRAVESSIA ELEVADA', 1.8, '#333') + txt(uA - 9, -6, 'PORTAL ZONA 30', 1.8, '#9a4434') + txt(uB + 9, -6, 'PORTAL ZONA 30', 1.8, '#9a4434');
    const cu = SIG_U + 70; s += txt(cu, -9.1, 'calçada 3,50', 0.9, '#333') + txt(cu, -4.9, 'ciclovia 2,50', 0.9, '#fff') + txt(cu, -1.6, 'faixa 3,00', 0.9, '#fff') + txt(cu, 1.6, 'faixa 3,00', 0.9, '#fff') + txt(cu, 7.1, 'calçada 3,00', 0.9, '#333');
  }
  for (const p of POLES) if (p.u > a && p.u < b) s += circ(p.u, p.s, 0.3, '#777');
  // estaqueamento
  for (let u = Math.ceil(a / 20) * 20; u <= b; u += 20) { const p0 = at(u, 11.5), p1 = at(u, 13); const [x0, y0] = PX(p0[0], p0[1]), [x1, y1] = PX(p1[0], p1[1]); s += `<line x1="${x0}" y1="${y0}" x2="${x1}" y2="${y1}" stroke="#444" stroke-width="0.15"/>`; if (u % 100 === 0) s += txt(u, 15.6, `Est. ${Math.floor((u - uA) / 20)} (${u - uA} m)`, 1.5, '#444'); }
  s += txt(a + 5, -30, prop ? 'PLANTA BAIXA — PROPOSTA (conceitual)' : 'PLANTA BAIXA — SITUAÇÃO ATUAL', 3.2, '#111', 'start', 700);
  s += txt(a + 5, -26, 'PE-060 · Travessia urbana de Ipojuca/PE · sem escala — cotas em metros', 1.8, '#555', 'start', 500);
  const [nx, ny] = PX(...at(b - 10, -24).slice(0, 2)); s += `<g transform="translate(${nx},${ny})"><polygon points="0,-1.4 5,0 0,1.4" fill="#111"/><text x="7" y="1" font-size="2.6" font-family="Inter" font-weight="700">N</text></g>`;
  const [sx, sy] = PX(...at(b - 70, -20).slice(0, 2)); s += `<g transform="translate(${sx},${sy})"><rect x="0" y="0" width="25" height="0.8" fill="#111"/><rect x="25" y="0" width="25" height="0.8" fill="#fff" stroke="#111" stroke-width="0.15"/><text x="0" y="3" font-size="1.6" font-family="Inter">0</text><text x="25" y="3" font-size="1.6" font-family="Inter" text-anchor="middle">25</text><text x="50" y="3" font-size="1.6" font-family="Inter" text-anchor="middle">50 m</text></g>`;
  const pA = at(a, 0), pB = at(b, 0); const xs = [-pA[1], -pB[1]], ys = [pA[0], pB[0]]; const minX = Math.min(...xs) - 10, maxX = Math.max(...xs) + 10, minY = Math.min(...ys) - 40, maxY = Math.max(...ys) + 40;
  return `<svg id="planSvg" xmlns="http://www.w3.org/2000/svg" viewBox="${minX} ${minY} ${maxX - minX} ${maxY - minY}" preserveAspectRatio="xMidYMid meet"><rect x="${minX - 500}" y="${minY - 500}" width="${maxX - minX + 1000}" height="${maxY - minY + 1000}" fill="#f4f1ea"/>${s}</svg>`;
}
function planHTML(prop) {
  const lg = prop ? [['#cfccc4', 'Calçada (piso intertravado)'], ['#e6c22c', 'Piso tátil'], ['#b4554a', 'Ciclovia bidirecional'], ['#55565a', 'Pista (pavimento novo)'], ['#86ad5a', 'Canteiro arborizado'], ['#6e6f73', 'Travessia elevada'], ['#9a4434', 'Pavimento colorido — portal'], ['#2f6fb6', 'Abrigo de ônibus'], ['#f2b233', 'Poste LED'], ['#d4cfc6', 'Edificações']] : [['#8b8b8a', 'Pista existente (~7 m)'], ['#d3a27a', 'Acostamento de terra'], ['#d4cfc6', 'Edificações'], ['#777', 'Postes existentes']];
  return `<div id="planSvgWrap">${planSVG(prop)}</div><div class="legend">${lg.map(l => `<span><i style="background:${l[0]}"></i>${l[1]}</span>`).join('')}</div><div class="note">Arraste para mover e use a roda do mouse (ou pinça) para aproximar. Planta gerada a partir do mesmo modelo do 3D: dimensões indicativas, sujeitas a levantamento topográfico e cadastral.</div>`;
}
function enablePanZoom() {
  const wrap = $('planSvgWrap'), svg = $('planSvg'); if (!svg) return; let vb = svg.getAttribute('viewBox').split(' ').map(Number); const vb0 = vb.slice();
  // começa ampliado no trecho da travessia semaforizada
  const p = at(SIG_U, 0); const [cx, cy] = [-p[1], p[0]]; const w0 = 160, h0 = w0 * (wrap.clientHeight / wrap.clientWidth || 0.5); vb = [cx - w0 / 2, cy - h0 / 2, w0, h0]; svg.setAttribute('viewBox', vb.join(' '));
  let drag = null; const pts = new Map();
  wrap.onpointerdown = (e) => { wrap.setPointerCapture(e.pointerId); pts.set(e.pointerId, [e.clientX, e.clientY]); drag = { x: e.clientX, y: e.clientY, vb: vb.slice() }; wrap.style.cursor = 'grabbing'; };
  wrap.onpointermove = (e) => { if (!pts.has(e.pointerId)) return; pts.set(e.pointerId, [e.clientX, e.clientY]); if (pts.size === 2) { const [a2, b2] = [...pts.values()]; const d = Math.hypot(a2[0] - b2[0], a2[1] - b2[1]); if (drag.pd) zoom(drag.pd / d, (a2[0] + b2[0]) / 2, (a2[1] + b2[1]) / 2); drag.pd = d; return; } if (!drag) return; const r = wrap.getBoundingClientRect(); const k = vb[2] / r.width; vb[0] = drag.vb[0] - (e.clientX - drag.x) * k; vb[1] = drag.vb[1] - (e.clientY - drag.y) * k; svg.setAttribute('viewBox', vb.join(' ')); };
  wrap.onpointerup = wrap.onpointercancel = (e) => { pts.delete(e.pointerId); drag = null; wrap.style.cursor = 'grab'; };
  function zoom(f, mx, my) { const r = wrap.getBoundingClientRect(); const px = vb[0] + (mx - r.left) / r.width * vb[2], py = vb[1] + (my - r.top) / r.height * vb[3]; const nw = clamp(vb[2] * f, 20, vb0[2] * 1.2), k = nw / vb[2]; vb = [px - (px - vb[0]) * k, py - (py - vb[1]) * k, nw, vb[3] * k]; svg.setAttribute('viewBox', vb.join(' ')); }
  wrap.onwheel = (e) => { e.preventDefault(); zoom(Math.exp(e.deltaY * 0.0012), e.clientX, e.clientY); };
}
function sectionHTML() {
  const Y = (y) => (-y * 10).toFixed(1), X = (x) => (x * 10).toFixed(1);
  function sec(items, title, oy, cars) {
    let s = `<g transform="translate(${oy === 140 && title.startsWith('PROP') ? 500 : 150},${oy})"><text x="${X(-13)}" y="-112" font-size="13" font-weight="700" font-family="Inter" fill="#111">${title}</text>`;
    s += `<path d="M ${X(-14)} ${Y(0)} L ${X(-11.8)} ${Y(0)} L ${X(-11.8)} ${Y(0.7)} L ${X(-13)} ${Y(4)} L ${X(-14)} ${Y(5)} Z" fill="#c88b5c" opacity=".7"/>`;
    for (const it of items) { s += `<rect x="${X(it[0])}" y="${Y(it[2] + (it[5] || 0.25))}" width="${X(it[1] - it[0])}" height="${((it[5] || 0.25) + it[2]) * 10}" fill="${it[3]}" stroke="#555" stroke-width=".6"/>`; const mx = (it[0] + it[1]) / 2; s += `<line x1="${X(it[0])}" y1="38" x2="${X(it[0])}" y2="50" stroke="#333" stroke-width=".6"/><line x1="${X(it[1])}" y1="38" x2="${X(it[1])}" y2="50" stroke="#333" stroke-width=".6"/><line x1="${X(it[0])}" y1="46" x2="${X(it[1])}" y2="46" stroke="#333" stroke-width=".6"/><text x="${X(mx)}" y="43" font-size="7.5" text-anchor="middle" font-family="Inter" fill="#111">${(it[1] - it[0]).toFixed(2).replace('.', ',')}</text><text x="${X(mx)}" y="58" font-size="8" text-anchor="start" font-family="Inter" fill="#444" transform="rotate(50 ${X(mx)} 58)">${it[4]}</text>`; }
    for (const c of cars) s += c;
    s += `</g>`; return s;
  }
  const car = (x, y = 0) => `<g transform="translate(${X(x)},${Y(y)})"><rect x="-9" y="-14" width="18" height="9" rx="2" fill="#5f7d9a"/><rect x="-6" y="-20" width="12" height="7" rx="2" fill="#2a3a4a"/><circle cx="-5.5" cy="-4" r="3" fill="#222"/><circle cx="5.5" cy="-4" r="3" fill="#222"/></g>`;
  const ped = (x, y = 0) => `<g transform="translate(${X(x)},${Y(y)})" stroke="#222" stroke-width="1.6" fill="none"><circle cx="0" cy="-15.5" r="1.8" fill="#222"/><line x1="0" y1="-13.5" x2="0" y2="-7"/><line x1="0" y1="-7" x2="-2" y2="0"/><line x1="0" y1="-7" x2="2" y2="0"/><line x1="0" y1="-11.5" x2="-2.5" y2="-8"/><line x1="0" y1="-11.5" x2="2.5" y2="-8"/></g>`;
  const bike = (x, y = 0) => `<g transform="translate(${X(x)},${Y(y)})" stroke="#222" stroke-width="1.2" fill="none"><circle cx="-3.5" cy="-3.3" r="3.3"/><circle cx="3.5" cy="-3.3" r="3.3"/><line x1="-3.5" y1="-3.3" x2="0" y2="-8"/><line x1="0" y1="-8" x2="3.5" y2="-3.3"/><circle cx="0" cy="-16" r="1.8" fill="#222"/><line x1="0" y1="-14" x2="0" y2="-8"/></g>`;
  const tree = (x, y = 0.15) => `<g transform="translate(${X(x)},${Y(y)})"><rect x="-1" y="-30" width="2" height="30" fill="#5b4632"/><circle cx="0" cy="-40" r="16" fill="#3e7a32" opacity=".85"/></g>`;
  const lampG = (x, dir) => `<g transform="translate(${X(x)},${Y(0.15)})" stroke="#555" stroke-width="1.2"><line x1="0" y1="0" x2="0" y2="-90"/><line x1="0" y1="-90" x2="${dir * 24}" y2="-90"/><rect x="${dir * 24 - 4}" y="-92" width="8" height="3" fill="#f2b233" stroke="none"/></g>`;
  const hoje = [[-11.8, -3.5, 0, '#d3a27a', 'acost. terra', 0.08], [-3.5, 0, 0, '#8b8b8a', 'faixa 3,50'], [0, 3.5, 0, '#8b8b8a', 'faixa 3,50'], [3.5, 9.9, 0, '#d3a27a', 'acost. terra', 0.08]];
  const prop = [[-11.6, -10.9, 0.45, '#b9b5ac', 'cont.', 0.25], [-10.9, -7.35, 0.15, '#cfccc4', 'calçada'], [-7.35, -6.15, 0.15, '#86ad5a', 'canteiro'], [-6.15, -3.65, 0, '#b4554a', 'ciclovia'], [-3.65, -3.15, 0.13, '#e8e6e0', 'sep.'], [-3.15, 0, 0, '#55565a', 'faixa'], [0, 3.15, 0, '#55565a', 'faixa'], [3.15, 5.55, 0.15, '#86ad5a', 'canteiro/baia'], [5.55, 8.6, 0.15, '#cfccc4', 'calçada'], [8.6, 9.95, 0.15, '#bdb9b0', 'testada']];
  const svg = `<svg viewBox="-6 8 700 230" xmlns="http://www.w3.org/2000/svg" style="width:100%;background:#f4f1ea;border-radius:8px"><g transform="translate(0,0)">${sec(hoje, 'SITUAÇÃO ATUAL — ≈ 21,7 m, sem calçadas', 140, [ped(-6), ped(5.5), car(-1.75), car(1.75), bike(4.6)])}</g><g>${sec(prop, 'PROPOSTA — rua completa / Zona 30 (≈ 21,6 m)', 140, [ped(-9.6), ped(-8.2), ped(7), tree(-6.75), tree(4.35), bike(-5.4), bike(-4.4), car(-1.6), car(1.6), lampG(-6.9, 1), lampG(4.5, -1)])}</g></svg>`;
  return `${svg}<div class="note">Seções-tipo esquemáticas (ampliação vertical 1:1). Oeste à esquerda (encosta / Alto São João), leste à direita (comércio). Cotas em metros, indicativas — a confirmar com levantamento planialtimétrico, cadastro de lotes e projeto executivo. Cores: concreto/piso intertravado (cinza claro), ciclovia (vermelho), pista (cinza escuro), canteiros (verde).</div>
  <table class="q" style="margin-top:10px"><tr><th>Elemento</th><th>Hoje</th><th>Proposta</th></tr>
  <tr><td>Faixas de rolamento</td><td>2 × 3,50 m</td><td>2 × 3,00 m</td></tr><tr><td>Velocidade regulamentada</td><td>60 km/h</td><td>30 km/h (Zona 30)</td></tr>
  <tr><td>Calçadas</td><td>inexistentes</td><td>3,50 m (O) e 3,00 m (L), com piso tátil</td></tr><tr><td>Ciclovia</td><td>inexistente</td><td>bidirecional 2,50 m + separador 0,50 m</td></tr>
  <tr><td>Travessias</td><td>sem proteção</td><td>1 semaforizada + 2 elevadas</td></tr><tr><td>Drenagem</td><td>superficial, sem meio-fio</td><td>meio-fio, sarjeta e rede tubular</td></tr></table>`;
}
function quantHTML() {
  const len = uB - uA, cutL = CROSS.length * 9.2; const bayL = BAYS.reduce((a, b) => a + (b[1] - b[0]), 0);
  let trees = 0; for (const side of ['W', 'E']) for (let u = uA + 4; u < uB - 2; u += 9) { if (CUTS.some(c => u > c[0] - 1.5 && u < c[1] + 1.5)) continue; if (side === 'E' && BAYS.some(b => u > b[0] - 1 && u < b[1] + 1)) continue; trees++; }
  let leds = 0, pedL = 0; for (let u = uA + 6; u < uB - 2; u += 30) { if (CUTS.some(c => Math.abs(u - (c[0] + c[1]) / 2) < 6)) continue; leds += 2; pedL += 2; } leds += CROSS.length * 2;
  const f = (n, d = 0) => n.toLocaleString('pt-BR', { maximumFractionDigits: d, minimumFractionDigits: d });
  const rows = [['Extensão tratada (travessia urbana)', f(len), 'm'], ['Pavimento novo da pista (fresagem + recapeamento)', f(6.3 * len), 'm²'], ['Calçadas em piso intertravado', f(3.55 * len + 3.05 * len + 2 * 1.2 * 9.2 * CROSS.length), 'm²'], ['Piso tátil direcional/alerta', f(0.4 * 2 * len + 0.4 * 2 * cutL), 'm²'], ['Ciclovia bidirecional (2,50 m)', f(len), 'm'], ['Separador físico da ciclovia', f(len - cutL), 'm'], ['Meio-fio de concreto', f(2 * (len - cutL) + (len - cutL - bayL) + bayL + 2 * (len - cutL)), 'm'], ['Canteiros arborizados', f(1.2 * (len - cutL) + 2.4 * (len - cutL - bayL)), 'm²'], ['Árvores (oiti / ipê-amarelo)', f(trees), 'un'], ['Postes LED veiculares', f(leds), 'un'], ['Luminárias pedonais', f(pedL), 'un'], ['Travessias elevadas', '2', 'un'], ['Travessia semaforizada c/ botoeira', '1', 'un'], ['Abrigos de ônibus', f(BUS.length), 'un'], ['Baias (ônibus / estacionamento)', f(bayL), 'm'], ['Portais de entrada Zona 30', '2', 'un'], ['Muro de contenção do talude (lado oeste)', f(len), 'm']];
  return `<table class="q"><tr><th>Item</th><th>Quantidade</th></tr>${rows.map(r => `<tr><td>${r[0]}</td><td>${r[1]} ${r[2]}</td></tr>`).join('')}</table><div class="note">Quantitativos <b>indicativos</b>, extraídos automaticamente da geometria do modelo conceitual (extensão de ${f(len)} m entre os portais). Servem para dimensionar a ordem de grandeza da intervenção e não substituem orçamento nem projeto executivo.</div>`;
}
// referências → vistas equivalentes
document.querySelectorAll('[data-goto]').forEach(b => b.onclick = () => { const [cam, ph] = b.dataset.goto.split('-'); $('mRefs').classList.remove('show'); stopPres(); setPhase(ph); setCam(cam); });
$('bRefs').onclick = () => $('mRefs').classList.add('show');
$('bShot').onclick = () => { renderer.render(scene, camera); const url = renderer.domElement.toDataURL('image/png'); $('shotImg').src = url; $('mShot').classList.add('show'); };
$('bQR').onclick = () => { $('qrBox').innerHTML = QR_URL ? `<img src="img/qr.png" alt="QR code"><div style="max-width:260px"><b>Aponte a câmera do celular</b><p class="note">Abre este modelo 3D. Link público — não precisa de conta.</p><p class="note" style="word-break:break-all">${QR_URL}</p></div>` : '<p class="note">QR code ainda não gerado.</p>'; $('mQR').classList.add('show'); };

// ============================================================ Inicialização
addEventListener('resize', () => { camera.aspect = innerWidth / innerHeight; camera.updateProjectionMatrix(); renderer.setSize(innerWidth, innerHeight); });
function init() {
  ldTxt.textContent = 'terreno, edificações e vegetação'; const shared = buildShared(); scene.add(shared);
  winLitMeshes = []; shared.traverse(o => { if (o.name === 'winLit') winLitMeshes.push(o); });
  buildPhase(); syncUI(); setCam('aerea', true);
  seedAgents(); updateEnvironment(0.016);
  const hash = location.hash.replace('#', ''); if (['hoje', 'obra', 'op'].includes(hash)) setPhase(hash);
  if (hash === 'apresentacao') showStep(0);
  $('loading').style.display = 'none';
  let last = performance.now();
  renderer.setAnimationLoop((now) => {
    const dt = Math.min(0.05, (now - last) / 1000); last = now;
    if (state.anim) { state.hour = (state.hour + dt * state.daySpeed) % 24; $('hour').value = state.hour; $('hourV').textContent = fmtH(state.hour); }
    updateEnvironment(dt); if (state.agents) updateAgents(dt); updatePres(dt); updateCamera(dt); controls.update(); updateLabels(); renderer.render(scene, camera); updateHUD(dt);
  });
  window.__ready = true;
}
window.__app = { state, setPhase, setCam, showStep, updateAgents, buildPhase, syncUI, camera, controls, renderer, scene, flyTo, openPlan };
setTimeout(() => { try { init(); } catch (e) { console.error(e); ldTxt.textContent = 'Erro: ' + e.message; } }, 30);
