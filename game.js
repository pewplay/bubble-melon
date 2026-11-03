/*
 * Bubble Melon — a fruit-merge physics puzzle.
 * Everything (art, physics, sound) is generated in code. No external assets.
 *
 * World units: the jar's inner area spans x 0..JW, y 0..JH (y grows downward).
 * The physics is a sequential-impulse circle solver with sub-stepping and
 * split position correction, which keeps tall stacks calm and jitter-free.
 */
(function () {
  'use strict';

  var GAME_ID = 'bubble-melon';
  var TAU = Math.PI * 2;

  /* ------------------------------------------------------------------ */
  /* Storage (all keys prefixed with the game id)                        */
  /* ------------------------------------------------------------------ */
  var store = {
    get: function (k, d) {
      try {
        var v = localStorage.getItem(GAME_ID + ':' + k);
        return v === null ? d : v;
      } catch (e) { return d; }
    },
    set: function (k, v) {
      try { localStorage.setItem(GAME_ID + ':' + k, String(v)); } catch (e) { /* ignore */ }
    }
  };

  /* ------------------------------------------------------------------ */
  /* World constants                                                     */
  /* ------------------------------------------------------------------ */
  var JW = 420, JH = 540;               // jar inner size
  var BOX_X0 = -30, BOX_Y0 = -128;       // visible world box (includes dropper)
  var BOXW = JW + 60, BOXH = JH + 128 + 30;
  var RAIL_Y = -112, DROP_Y = -62;       // dropper rail and held fruit height
  var LINE_Y = 0;                        // danger line (jar rim)
  var GRAVITY = 1300;
  var STEP = 1 / 60, SUBSTEPS = 8, VEL_ITERS = 6, POS_ITERS = 3;
  var CM = 0.6;                          // contact margin (keeps resting contacts alive)
  var SLOP = 0.25, MU = 0.35, MU_WALL = 0.3, RESTITUTION = 0.18;
  var DANGER_TIME = 2.6;                 // seconds above the line before game over
  var DROP_COOLDOWN = 0.42;

  // Fruit ladder: radius (world units), colours. Index = level.
  var FRUITS = [
    { name: 'Cherry',     r: 14, base: '#ec2a45', light: '#ff8c99', dark: '#a50f2b', line: '#7d0b25' },
    { name: 'Strawberry', r: 19, base: '#ff4d6a', light: '#ffa3b0', dark: '#d02a4a', line: '#9c1838' },
    { name: 'Grape',      r: 25, base: '#9b5de5', light: '#d2b2ff', dark: '#6a35b0', line: '#4e2386' },
    { name: 'Lemon',      r: 31, base: '#ffd83a', light: '#fff6b0', dark: '#eaa80c', line: '#b77f05' },
    { name: 'Orange',     r: 38, base: '#ff9124', light: '#ffc98a', dark: '#e0640a', line: '#a84705' },
    { name: 'Apple',      r: 46, base: '#7ccf3c', light: '#d2f59a', dark: '#4c9a1c', line: '#356f12' },
    { name: 'Pear',       r: 54, base: '#d6d54a', light: '#f8f7b8', dark: '#a2a421', line: '#727315' },
    { name: 'Peach',      r: 63, base: '#ffa27c', light: '#ffe0cc', dark: '#f0675d', line: '#bf4a43' },
    { name: 'Pineapple',  r: 73, base: '#ffc233', light: '#ffe995', dark: '#dd8b12', line: '#a3620a' },
    { name: 'Melon',      r: 84, base: '#93dcae', light: '#e2fbe9', dark: '#56ad7f', line: '#3b8560' },
    { name: 'Watermelon', r: 96, base: '#3aa655', light: '#8fe09c', dark: '#1f6e34', line: '#154f25' }
  ];
  var LAST = FRUITS.length - 1;
  var DROP_WEIGHTS = [30, 26, 20, 14, 10];  // only the five smallest can be dropped

  /* ------------------------------------------------------------------ */
  /* DOM                                                                 */
  /* ------------------------------------------------------------------ */
  var canvas = document.getElementById('game');
  var ctx = canvas.getContext('2d');
  var $ = function (id) { return document.getElementById(id); };
  var ui = {
    corner: $('corner'), btnPause: $('btnPause'), btnMute: $('btnMute'),
    menu: $('menu'), btnPlay: $('btnPlay'), menuBest: $('menuBest'), menuHint: $('menuHint'), menuFruits: $('menuFruits'),
    pause: $('pause'), btnResume: $('btnResume'), btnRestart: $('btnRestart'),
    over: $('over'), btnAgain: $('btnAgain'), newBest: $('newBest'), finalScore: $('finalScore'),
    finalBest: $('finalBest'), finalBigImg: $('finalBigImg'), finalBigName: $('finalBigName')
  };

  /* ------------------------------------------------------------------ */
  /* Small helpers                                                       */
  /* ------------------------------------------------------------------ */
  function clamp(v, a, b) { return v < a ? a : v > b ? b : v; }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function rand(a, b) { return a + Math.random() * (b - a); }
  // deterministic pseudo random (for fruit textures)
  function seeded(seed) {
    var s = seed >>> 0;
    return function () { s = (s * 1664525 + 1013904223) >>> 0; return s / 4294967296; };
  }
  function pickDropType() {
    var total = 0, i;
    for (i = 0; i < DROP_WEIGHTS.length; i++) total += DROP_WEIGHTS[i];
    var r = Math.random() * total;
    for (i = 0; i < DROP_WEIGHTS.length; i++) { r -= DROP_WEIGHTS[i]; if (r < 0) return i; }
    return 0;
  }
  function pointsFor(level) { return (level + 1) * (level + 2) / 2; }

  /* ------------------------------------------------------------------ */
  /* Sound: tiny Web Audio synth                                         */
  /* ------------------------------------------------------------------ */
  var Snd = {
    ac: null, master: null, muted: store.get('muted', '0') === '1', lastThud: 0,
    init: function () {
      if (!this.ac) {
        var AC = window.AudioContext || window.webkitAudioContext;
        if (!AC) return;
        try { this.ac = new AC(); } catch (e) { return; }
        var comp = this.ac.createDynamicsCompressor();
        comp.connect(this.ac.destination);
        this.master = this.ac.createGain();
        this.master.gain.value = this.muted ? 0 : 0.55;
        this.master.connect(comp);
      }
      if (this.ac.state === 'suspended') this.ac.resume();
    },
    setMuted: function (m) {
      this.muted = m;
      store.set('muted', m ? '1' : '0');
      if (this.master) this.master.gain.setTargetAtTime(m ? 0 : 0.55, this.ac.currentTime, 0.02);
    },
    ok: function () { return this.ac && this.ac.state === 'running' && !this.muted; },
    tone: function (f0, f1, dur, type, vol, delay) {
      var ac = this.ac, t = ac.currentTime + (delay || 0);
      var o = ac.createOscillator(), g = ac.createGain();
      o.type = type || 'sine';
      o.frequency.setValueAtTime(f0, t);
      if (f1 && f1 !== f0) o.frequency.exponentialRampToValueAtTime(f1, t + dur);
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(vol, t + 0.008);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      o.connect(g); g.connect(this.master);
      o.start(t); o.stop(t + dur + 0.02);
    },
    noise: function (dur, vol, freq, q, delay) {
      var ac = this.ac, t = ac.currentTime + (delay || 0);
      if (!this.nbuf) {
        var len = ac.sampleRate * 0.5 | 0;
        this.nbuf = ac.createBuffer(1, len, ac.sampleRate);
        var d = this.nbuf.getChannelData(0);
        for (var i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
      }
      var src = ac.createBufferSource(), f = ac.createBiquadFilter(), g = ac.createGain();
      src.buffer = this.nbuf;
      f.type = 'bandpass'; f.frequency.value = freq; f.Q.value = q || 1;
      g.gain.setValueAtTime(vol, t);
      g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
      src.connect(f); f.connect(g); g.connect(this.master);
      src.start(t); src.stop(t + dur + 0.02);
    },
    // soap-bubble pop when a fruit is released
    drop: function () {
      if (!this.ok()) return;
      this.tone(1500, 500, 0.07, 'sine', 0.25);
      this.noise(0.05, 0.25, 3200, 2);
    },
    // juicy "bloop" whose pitch falls as fruits get bigger
    merge: function (level, chain) {
      if (!this.ok()) return;
      var f = 720 * Math.pow(0.88, level);
      this.tone(f * 0.55, f * 1.5, 0.12, 'sine', 0.45);
      this.tone(f * 1.5, f * 2.2, 0.09, 'triangle', 0.16, 0.05);
      this.noise(0.12, 0.35, 900 + 200 * (10 - level), 1.4);
      if (chain >= 2) {
        var notes = [0, 4, 7, 12, 16, 19, 24];
        var base = 523 * Math.pow(2, Math.min(chain - 2, 6) / 12);
        for (var i = 0; i < Math.min(chain, 4); i++) {
          this.tone(base * Math.pow(2, notes[i] / 12), 0, 0.12, 'triangle', 0.12, 0.06 + i * 0.05);
        }
      }
    },
    thud: function (strength) {
      if (!this.ok()) return;
      var now = this.ac.currentTime;
      if (now - this.lastThud < 0.07) return;
      this.lastThud = now;
      this.tone(170, 70, 0.1, 'sine', clamp(strength, 0.04, 0.22));
    },
    warn: function () {
      if (!this.ok()) return;
      this.tone(660, 620, 0.12, 'square', 0.06);
    },
    melon: function () {
      if (!this.ok()) return;
      var seq = [523, 659, 784, 1047, 1319];
      for (var i = 0; i < seq.length; i++) this.tone(seq[i], 0, 0.22, 'triangle', 0.2, i * 0.08);
      this.noise(0.5, 0.25, 2500, 0.7, 0.05);
    },
    over: function () {
      if (!this.ok()) return;
      var seq = [523, 440, 392, 330, 262];
      for (var i = 0; i < seq.length; i++) this.tone(seq[i], seq[i] * 0.97, 0.26, 'triangle', 0.2, i * 0.14);
    },
    click: function () {
      if (!this.ok()) return;
      this.tone(880, 1320, 0.06, 'sine', 0.18);
    }
  };

  /* ------------------------------------------------------------------ */
  /* Fruit art (drawn once per size into sprite canvases)                */
  /* ------------------------------------------------------------------ */
  function ellipse(c, x, y, rx, ry, rot) {
    c.beginPath();
    c.ellipse(x, y, Math.max(0.1, rx), Math.max(0.1, ry), rot || 0, 0, TAU);
  }

  function leaf(c, x, y, len, ang, col, dark) {
    c.save();
    c.translate(x, y);
    c.rotate(ang);
    c.beginPath();
    c.moveTo(0, 0);
    c.quadraticCurveTo(len * 0.45, -len * 0.42, len, 0);
    c.quadraticCurveTo(len * 0.45, len * 0.42, 0, 0);
    var g = c.createLinearGradient(0, -len * 0.3, 0, len * 0.3);
    g.addColorStop(0, '#9be36a');
    g.addColorStop(1, col || '#3fae4a');
    c.fillStyle = g;
    c.fill();
    c.lineWidth = Math.max(1, len * 0.08);
    c.strokeStyle = dark || '#23752f';
    c.stroke();
    c.beginPath();
    c.moveTo(len * 0.1, 0);
    c.quadraticCurveTo(len * 0.5, -len * 0.04, len * 0.85, 0);
    c.lineWidth = Math.max(0.8, len * 0.05);
    c.stroke();
    c.restore();
  }

  function stem(c, x0, y0, cx, cy, x1, y1, w, col) {
    c.beginPath();
    c.moveTo(x0, y0);
    c.quadraticCurveTo(cx, cy, x1, y1);
    c.lineCap = 'round';
    c.lineWidth = w;
    c.strokeStyle = col || '#7a4a22';
    c.stroke();
  }

  // Parts drawn behind the body (stems, crowns, lemon tips)
  function drawBack(c, t, R) {
    switch (t) {
      case 0: // cherry: long stem + leaf
        stem(c, 0, -R * 0.7, R * 0.15, -R * 1.25, R * 0.5, -R * 1.55, R * 0.16, '#6f8f2a');
        leaf(c, R * 0.48, -R * 1.52, R * 0.75, -0.25, '#3fae4a');
        break;
      case 2: // grape
        stem(c, 0, -R * 0.75, -R * 0.05, -R * 1.05, -R * 0.15, -R * 1.25, R * 0.14);
        break;
      case 3: { // lemon: pointy tips at both sides
        var F = FRUITS[3];
        for (var s = -1; s <= 1; s += 2) {
          ellipse(c, s * R * 0.93, -R * 0.05, R * 0.2, R * 0.15, 0);
          c.fillStyle = F.base; c.fill();
          c.lineWidth = Math.max(1, R * 0.065); c.strokeStyle = F.line; c.stroke();
        }
        break;
      }
      case 5: // apple
      case 6: // pear
        stem(c, 0, -R * 0.75, R * 0.05, -R * 1.05, R * 0.2, -R * 1.22, R * 0.11);
        break;
      case 8: { // pineapple crown
        var blades = [[-0.62, 0.7], [-0.32, 0.88], [0, 0.98], [0.32, 0.88], [0.62, 0.7]];
        for (var i = 0; i < blades.length; i++) {
          var a = blades[i][0], L = R * blades[i][1];
          c.save();
          c.translate(0, -R * 0.78);
          c.rotate(a);
          c.beginPath();
          c.moveTo(-R * 0.13, 0);
          c.quadraticCurveTo(-R * 0.08, -L * 0.6, 0, -L);
          c.quadraticCurveTo(R * 0.08, -L * 0.6, R * 0.13, 0);
          c.closePath();
          var g = c.createLinearGradient(0, 0, 0, -L);
          g.addColorStop(0, '#2f9a44');
          g.addColorStop(1, '#8fe06a');
          c.fillStyle = g; c.fill();
          c.lineWidth = Math.max(1, R * 0.045); c.strokeStyle = '#1f6a2c'; c.stroke();
          c.restore();
        }
        break;
      }
      case 9: // melon: curly vine
      case 10:
        c.beginPath();
        c.moveTo(0, -R * 0.85);
        c.bezierCurveTo(R * 0.02, -R * 1.1, R * 0.25, -R * 1.12, R * 0.22, -R * 0.98);
        c.bezierCurveTo(R * 0.2, -R * 0.9, R * 0.08, -R * 0.95, R * 0.12, -R * 1.04);
        c.lineCap = 'round'; c.lineWidth = R * 0.07; c.strokeStyle = '#4f8a2a'; c.stroke();
        break;
    }
  }

  // Surface patterns (clipped to the body circle)
  function drawPattern(c, t, R) {
    var F = FRUITS[t], rnd = seeded(t * 977 + 13), i, x, y;
    switch (t) {
      case 1: // strawberry seeds, kept away from the face
        for (y = -0.55; y <= 0.95; y += 0.28) {
          for (x = -0.95; x <= 0.95; x += 0.3) {
            var sx = (x + ((Math.round(y / 0.28) & 1) ? 0.15 : 0)) * R, sy = y * R;
            if (sx * sx + sy * sy > R * R * 0.85) continue;
            if (Math.abs(sx) < R * 0.66 && sy > -R * 0.15 && sy < R * 0.48) continue;
            ellipse(c, sx, sy, R * 0.045, R * 0.075, 0.2);
            c.fillStyle = '#fff1a0'; c.fill();
          }
        }
        break;
      case 2: // grape: soft cluster bumps
        c.lineWidth = R * 0.05;
        c.strokeStyle = 'rgba(255,255,255,0.18)';
        for (i = 0; i < 7; i++) {
          var a = i / 7 * TAU + 0.3;
          c.beginPath(); c.arc(Math.cos(a) * R * 0.72, Math.sin(a) * R * 0.72, R * 0.42, 0, TAU); c.stroke();
        }
        break;
      case 3: // lemon pores
      case 4: // orange pores
        c.fillStyle = t === 3 ? 'rgba(255,255,255,0.45)' : 'rgba(190,70,0,0.22)';
        for (i = 0; i < 46; i++) {
          x = (rnd() * 2 - 1) * R; y = (rnd() * 2 - 1) * R;
          if (x * x + y * y > R * R) continue;
          ellipse(c, x, y, R * 0.028, R * 0.028, 0); c.fill();
        }
        break;
      case 5: { // apple: red-ish cheek glow
        var g5 = c.createRadialGradient(R * 0.55, R * 0.1, 0, R * 0.55, R * 0.1, R * 0.9);
        g5.addColorStop(0, 'rgba(255,120,80,0.45)');
        g5.addColorStop(1, 'rgba(255,120,80,0)');
        c.fillStyle = g5; c.fillRect(-R, -R, 2 * R, 2 * R);
        break;
      }
      case 6: // pear speckles
        c.fillStyle = 'rgba(140,110,30,0.35)';
        for (i = 0; i < 40; i++) {
          x = (rnd() * 2 - 1) * R; y = (rnd() * 2 - 1) * R;
          if (x * x + y * y > R * R) continue;
          ellipse(c, x, y, R * 0.022, R * 0.018, rnd() * 3); c.fill();
        }
        break;
      case 7: { // peach: rosy side + crease
        var g7 = c.createRadialGradient(R * 0.6, R * 0.2, 0, R * 0.6, R * 0.2, R * 1.1);
        g7.addColorStop(0, 'rgba(240,70,90,0.5)');
        g7.addColorStop(1, 'rgba(240,70,90,0)');
        c.fillStyle = g7; c.fillRect(-R, -R, 2 * R, 2 * R);
        c.beginPath();
        c.moveTo(R * 0.05, -R * 0.98);
        c.bezierCurveTo(R * 0.7, -R * 0.6, R * 0.85, -R * 0.1, R * 0.7, R * 0.45);
        c.lineWidth = R * 0.05; c.strokeStyle = 'rgba(200,60,70,0.35)'; c.stroke();
        break;
      }
      case 8: // pineapple diamonds
        c.lineWidth = R * 0.045;
        c.strokeStyle = 'rgba(170,95,10,0.55)';
        for (i = -6; i <= 6; i++) {
          c.beginPath(); c.moveTo(i * R * 0.34 - R * 1.2, -R * 1.2); c.lineTo(i * R * 0.34 + R * 1.2, R * 1.2); c.stroke();
          c.beginPath(); c.moveTo(i * R * 0.34 + R * 1.2, -R * 1.2); c.lineTo(i * R * 0.34 - R * 1.2, R * 1.2); c.stroke();
        }
        c.fillStyle = 'rgba(255,240,170,0.55)';
        for (i = -6; i <= 6; i++) {
          for (var j = -6; j <= 6; j++) {
            x = (i + j) * R * 0.17; y = (j - i) * R * 0.17;
            if (x * x + y * y > R * R) continue;
            ellipse(c, x, y, R * 0.03, R * 0.03, 0); c.fill();
          }
        }
        break;
      case 9: // melon net
        c.lineWidth = R * 0.03;
        c.strokeStyle = 'rgba(255,255,240,0.6)';
        for (i = 0; i < 26; i++) {
          x = (rnd() * 2 - 1) * R; y = (rnd() * 2 - 1) * R;
          c.beginPath(); c.moveTo(x, y);
          for (var k = 0; k < 3; k++) {
            x += (rnd() - 0.5) * R * 0.5; y += (rnd() - 0.5) * R * 0.5;
            c.lineTo(x, y);
          }
          c.stroke();
        }
        break;
      case 10: // watermelon stripes
        c.lineWidth = R * 0.14;
        c.lineJoin = 'round';
        c.strokeStyle = '#1b6430';
        for (i = -3; i <= 3; i++) {
          var bx = i * R * 0.34;
          c.beginPath();
          for (y = -R; y <= R + 1; y += R * 0.14) {
            var curve = bx * (1 - (y * y) / (R * R) * 0.45);
            var zz = ((Math.round(y / (R * 0.14)) & 1) ? 1 : -1) * R * 0.045;
            if (y === -R) c.moveTo(curve + zz, y); else c.lineTo(curve + zz, y);
          }
          c.stroke();
        }
        break;
    }
  }

  // Parts drawn in front of the body (leaves, crowns)
  function drawFront(c, t, R) {
    switch (t) {
      case 1: { // strawberry sepals
        var sepals = [Math.PI + 0.25, Math.PI - 0.4, -0.25, 0.4, -Math.PI / 2];
        for (var i = 0; i < sepals.length; i++) leaf(c, 0, -R * 0.84, R * (i === 4 ? 0.35 : 0.52), sepals[i], '#3fae4a');
        ellipse(c, 0, -R * 0.86, R * 0.13, R * 0.1, 0); c.fillStyle = '#3fae4a'; c.fill();
        stem(c, 0, -R * 0.9, 0, -R * 1.05, R * 0.06, -R * 1.18, R * 0.1, '#3a8a3a');
        break;
      }
      case 2: leaf(c, -R * 0.12, -R * 1.15, R * 0.6, -0.35); break;
      case 4:
        stem(c, 0, -R * 0.82, 0, -R * 0.9, R * 0.02, -R * 0.98, R * 0.1, '#6a4a22');
        leaf(c, R * 0.04, -R * 0.95, R * 0.55, -0.45);
        break;
      case 5: leaf(c, R * 0.16, -R * 1.12, R * 0.55, -0.4); break;
      case 6: leaf(c, R * 0.18, -R * 1.18, R * 0.5, -0.2); break;
      case 7:
        leaf(c, 0, -R * 0.92, R * 0.45, -0.5);
        leaf(c, 0, -R * 0.92, R * 0.4, Math.PI + 0.55);
        break;
    }
  }

  function drawFace(c, t, R, mood) {
    var ink = t === 10 ? '#0d220f' : '#3b1d2e';
    var ex = R * 0.3, ey = R * 0.1, er = Math.max(1.1, R * 0.11);
    // cheeks
    c.fillStyle = t === 1 || t === 0 ? 'rgba(255,220,230,0.45)' : 'rgba(255,90,125,0.38)';
    ellipse(c, -R * 0.53, R * 0.32, R * 0.15, R * 0.085, 0); c.fill();
    ellipse(c, R * 0.53, R * 0.32, R * 0.15, R * 0.085, 0); c.fill();
    c.lineCap = 'round';
    c.strokeStyle = ink;
    c.fillStyle = ink;
    var s;
    if (mood === 1) { // happy: ^ ^ eyes + open mouth
      c.lineWidth = er * 0.62;
      for (s = -1; s <= 1; s += 2) {
        c.beginPath(); c.arc(s * ex, ey + er * 0.5, er * 0.95, Math.PI * 1.15, Math.PI * 1.85); c.stroke();
      }
      c.beginPath(); c.arc(0, R * 0.22, R * 0.12, 0, Math.PI); c.closePath(); c.fill();
      c.fillStyle = '#ff7f9c';
      ellipse(c, 0, R * 0.29, R * 0.06, R * 0.035, 0); c.fill();
    } else if (mood === 2) { // worried: big eyes, tiny "o" mouth, sweat drop
      for (s = -1; s <= 1; s += 2) {
        c.fillStyle = '#fff';
        ellipse(c, s * ex, ey, er * 1.25, er * 1.4, 0); c.fill();
        c.lineWidth = er * 0.3; c.stroke();
        c.fillStyle = ink;
        ellipse(c, s * ex, ey + er * 0.25, er * 0.55, er * 0.6, 0); c.fill();
      }
      c.lineWidth = er * 0.45;
      ellipse(c, 0, R * 0.32, R * 0.05, R * 0.06, 0); c.stroke();
      c.fillStyle = 'rgba(140,210,255,0.95)';
      c.beginPath();
      c.moveTo(R * 0.62, -R * 0.2);
      c.quadraticCurveTo(R * 0.52, -R * 0.02, R * 0.62, R * 0.02);
      c.quadraticCurveTo(R * 0.72, -R * 0.02, R * 0.62, -R * 0.2);
      c.fill();
    } else { // normal: shiny dot eyes + smile
      for (s = -1; s <= 1; s += 2) {
        c.fillStyle = ink;
        ellipse(c, s * ex, ey, er, er * 1.12, 0); c.fill();
        c.fillStyle = '#fff';
        ellipse(c, s * ex - er * 0.32, ey - er * 0.38, er * 0.4, er * 0.4, 0); c.fill();
      }
      c.lineWidth = Math.max(0.9, er * 0.48);
      c.beginPath(); c.arc(0, R * 0.2, R * 0.1, Math.PI * 0.15, Math.PI * 0.85); c.stroke();
    }
  }

  // Draws a complete fruit centred at (0,0) with radius R (pixels).
  function drawFruit(c, t, R, mood) {
    var F = FRUITS[t];
    var lw = Math.max(1, R * 0.065);
    drawBack(c, t, R);
    // body
    c.save();
    c.beginPath(); c.arc(0, 0, R, 0, TAU);
    var g = c.createRadialGradient(-R * 0.35, -R * 0.42, R * 0.05, 0, 0, R * 1.08);
    g.addColorStop(0, F.light);
    g.addColorStop(0.42, F.base);
    g.addColorStop(1, F.dark);
    c.fillStyle = g;
    c.fill();
    c.clip();
    drawPattern(c, t, R);
    // soft bounce light along the bottom edge
    var bl = c.createRadialGradient(R * 0.2, R * 1.25, R * 0.2, R * 0.2, R * 1.25, R * 0.75);
    bl.addColorStop(0, 'rgba(255,255,255,0.32)');
    bl.addColorStop(1, 'rgba(255,255,255,0)');
    c.fillStyle = bl; c.fillRect(-R, -R, 2 * R, 2 * R);
    c.restore();
    // outline
    c.beginPath(); c.arc(0, 0, R - lw / 2, 0, TAU);
    c.lineWidth = lw; c.strokeStyle = F.line; c.stroke();
    drawFront(c, t, R);
    drawFace(c, t, R, mood);
    // glossy highlight
    c.fillStyle = 'rgba(255,255,255,0.78)';
    ellipse(c, -R * 0.45, -R * 0.45, R * 0.24, R * 0.12, -0.75); c.fill();
    ellipse(c, -R * 0.7, -R * 0.12, R * 0.055, R * 0.055, 0); c.fill();
  }

  // Sprite cache: sprites[mood][type] = { cv, R, size }
  var sprites = [[], [], []];
  var spriteScale = 0;
  var SPRITE_PAD = 1.78;

  function bakeSprite(t, Rpx, mood) {
    var size = Math.ceil(Rpx * SPRITE_PAD * 2) + 4;
    var cv = document.createElement('canvas');
    cv.width = cv.height = size;
    var c = cv.getContext('2d');
    c.translate(size / 2, size / 2);
    drawFruit(c, t, Rpx, mood);
    return { cv: cv, R: Rpx, size: size };
  }

  function bakeAll(pxPerUnit) {
    // never bake tiny sprites: they are also used for HUD icons
    var k = Math.max(pxPerUnit, 1.2);
    if (Math.abs(k - spriteScale) < 0.01) return;
    spriteScale = k;
    for (var m = 0; m < 3; m++) {
      for (var t = 0; t < FRUITS.length; t++) {
        sprites[m][t] = bakeSprite(t, Math.max(12, FRUITS[t].r * k), m);
      }
    }
  }

  // Draws a cached sprite so that the fruit radius is rr in current units.
  function blitFruit(t, mood, x, y, rr, angle, sx, sy, alpha) {
    var sp = sprites[mood][t];
    var k = rr / sp.R, d = sp.size * k;
    ctx.save();
    ctx.translate(x, y);
    if (sx !== 1 || sy !== 1) ctx.scale(sx, sy);
    if (angle) ctx.rotate(angle);
    if (alpha !== undefined && alpha < 1) ctx.globalAlpha = alpha;
    ctx.drawImage(sp.cv, -d / 2, -d / 2, d, d);
    ctx.restore();
  }

  /* ------------------------------------------------------------------ */
  /* Game state                                                          */
  /* ------------------------------------------------------------------ */
  var state = 'menu';          // menu | play | paused | ending | over
  var fruits = [];
  var particles = [];
  var popups = [];
  var bgBubbles = [];
  var score = 0, displayScore = 0;
  var best = parseInt(store.get('best', '0'), 10) || 0;
  var maxLevel = 0;
  var current = 0, next = 0, cooldown = 0;
  var aimX = JW / 2, aimTarget = JW / 2;
  var dangerT = 0, warnBeat = 0, endT = 0;
  var chain = 0, lastMergeT = -10, clock = 0;
  var shake = 0, flash = 0;
  var keys = { left: false, right: false };
  var nextId = 1;
  var holdBob = 0, heldPop = 0, nextPop = 0;
  var isTouch = window.matchMedia && window.matchMedia('(pointer: coarse)').matches;

  function makeFruit(t, x, y) {
    var r = FRUITS[t].r;
    return {
      id: nextId++, t: t, x: x, y: y, vx: 0, vy: 0, w: 0, a: rand(-0.3, 0.3),
      r: r, R: r, m: r * r, im: 1 / (r * r), grow: 1, armed: false, age: 0,
      sq: 0, sqv: 0, happy: 0, dead: false, merged: false
    };
  }

  function setMass(f) {
    f.m = f.r * f.r;
    f.im = 1 / f.m;
  }

  function resetGame() {
    fruits.length = 0;
    particles.length = 0;
    popups.length = 0;
    score = 0; displayScore = 0;
    maxLevel = 0;
    current = pickDropType();
    next = pickDropType();
    cooldown = 0;
    dangerT = 0;
    chain = 0;
    shake = 0; flash = 0;
    aimX = aimTarget = JW / 2;
    heldPop = 1; nextPop = 1;
  }

  // A calm decorative pile shown behind the start menu
  function menuPile() {
    fruits.length = 0;
    var lv = [6, 4, 5, 2, 3, 1, 0, 3, 2, 1, 0, 4];
    for (var i = 0; i < lv.length; i++) {
      var f = makeFruit(lv[i], 40 + ((i * 97) % 340), JH - 60 - i * 40);
      f.armed = true;
      fruits.push(f);
    }
    current = 2; next = 4;
  }

  /* ------------------------------------------------------------------ */
  /* Physics                                                             */
  /* ------------------------------------------------------------------ */
  // contact pool: a = fruit, b = fruit or null (wall), n = normal from a to b
  var contacts = [], nContacts = 0;
  var mergePairs = [];

  // Impulses from the previous sub-step, used to warm-start persistent contacts.
  var warmPrev = new Map(), warmNext = new Map();

  function addContact(a, b, nx, ny, pen, wall) {
    var c = contacts[nContacts];
    if (!c) { c = contacts[nContacts] = {}; }
    nContacts++;
    c.a = a; c.b = b; c.nx = nx; c.ny = ny; c.pen = pen;
    var flip = 1;
    if (b) {
      if (a.id < b.id) c.key = a.id * 1048576 + b.id;
      else { c.key = b.id * 1048576 + a.id; flip = -1; }
    } else c.key = a.id * 1048576 + 1048570 + wall;
    c.flip = flip;
    var w = warmPrev.get(c.key);
    if (w) { c.jn = w[0] * 0.9; c.jt = w[1] * flip * 0.9; } else { c.jn = 0; c.jt = 0; }
    var vn = b ? (b.vx - a.vx) * nx + (b.vy - a.vy) * ny : -(a.vx * nx + a.vy * ny);
    c.bounce = vn < -90 ? -vn * RESTITUTION : 0;
    var ib = b ? b.im : 0;
    c.kn = a.im + ib;
    c.kt = 3 * (a.im + ib);    // includes rotational inertia of solid discs
    c.mu = b ? MU : MU_WALL;
    if (vn < -260) impact(a, b, -vn);
  }

  function impact(a, b, speed) {
    var s = clamp((speed - 260) / 1400, 0, 0.18);
    a.sqv += s * 30;
    if (b) b.sqv += s * 30;
    if (state === 'play') Snd.thud(0.04 + s);
  }

  function buildContacts() {
    nContacts = 0;
    var n = fruits.length, i, j;
    for (i = 0; i < n; i++) {
      var A = fruits[i];
      if (A.x < A.r + CM) { addContact(A, null, -1, 0, A.r - A.x, 0); A.armed = true; }
      if (A.x > JW - A.r - CM) { addContact(A, null, 1, 0, A.x - (JW - A.r), 1); A.armed = true; }
      if (A.y > JH - A.r - CM) { addContact(A, null, 0, 1, A.y - (JH - A.r), 2); A.armed = true; }
      for (j = i + 1; j < n; j++) {
        var B = fruits[j];
        var dx = B.x - A.x, dy = B.y - A.y, rr = A.r + B.r + CM;
        if (dx > rr || dx < -rr || dy > rr || dy < -rr) continue;
        var d2 = dx * dx + dy * dy;
        if (d2 >= rr * rr) continue;
        var d = Math.sqrt(d2);
        var nx, ny;
        if (d > 1e-6) { nx = dx / d; ny = dy / d; } else { nx = 0; ny = 1; d = 0; }
        addContact(A, B, nx, ny, rr - d);
        A.armed = true; B.armed = true;
        if (A.t === B.t && d < A.r + B.r + 0.2 && !A.merged && !B.merged) mergePairs.push(A, B);
      }
    }
  }

  function applyImpulse(c, jn, jt) {
    var A = c.a, B = c.b, nx = c.nx, ny = c.ny, tx = -ny, ty = nx;
    var px = jn * nx + jt * tx, py = jn * ny + jt * ty;
    A.vx -= px * A.im; A.vy -= py * A.im;
    A.w -= jt * 2 * A.im / A.r;
    if (B) {
      B.vx += px * B.im; B.vy += py * B.im;
      B.w -= jt * 2 * B.im / B.r;
    }
  }

  function solveVelocities() {
    var k, c;
    // warm start
    for (k = 0; k < nContacts; k++) {
      c = contacts[k];
      if (c.jt > c.mu * c.jn) c.jt = c.mu * c.jn; else if (c.jt < -c.mu * c.jn) c.jt = -c.mu * c.jn;
      if (c.jn || c.jt) applyImpulse(c, c.jn, c.jt);
    }
    for (var it = 0; it < VEL_ITERS; it++) {
      for (var k = 0; k < nContacts; k++) {
        var c = contacts[k], A = c.a, B = c.b, nx = c.nx, ny = c.ny;
        // normal impulse (accumulated, never pulling)
        var vn = B ? (B.vx - A.vx) * nx + (B.vy - A.vy) * ny : -(A.vx * nx + A.vy * ny);
        var dj = (c.bounce - vn) / c.kn;
        var old = c.jn;
        c.jn = Math.max(0, old + dj);
        dj = c.jn - old;
        A.vx -= dj * nx * A.im; A.vy -= dj * ny * A.im;
        if (B) { B.vx += dj * nx * B.im; B.vy += dj * ny * B.im; }
        // friction impulse along the tangent, coupled with spin
        var tx = -ny, ty = nx;
        var vt = -(A.vx * tx + A.vy * ty + A.w * A.r);
        if (B) vt += B.vx * tx + B.vy * ty - B.w * B.r;
        var jt = -vt / c.kt;
        var maxF = c.mu * c.jn;
        var oldt = c.jt;
        c.jt = clamp(oldt + jt, -maxF, maxF);
        jt = c.jt - oldt;
        A.vx -= jt * tx * A.im; A.vy -= jt * ty * A.im;
        A.w -= jt * A.r * 2 * A.im / (A.r * A.r);
        if (B) {
          B.vx += jt * tx * B.im; B.vy += jt * ty * B.im;
          B.w -= jt * B.r * 2 * B.im / (B.r * B.r);
        }
      }
    }
    // remember impulses for the next sub-step
    warmNext.clear();
    for (k = 0; k < nContacts; k++) {
      c = contacts[k];
      if (c.jn > 0) warmNext.set(c.key, [c.jn, c.jt * c.flip]);
    }
    var tmp = warmPrev; warmPrev = warmNext; warmNext = tmp;
  }

  // Split position correction: removes overlap without adding velocity.
  function solvePositions() {
    for (var it = 0; it < POS_ITERS; it++) {
      for (var k = 0; k < nContacts; k++) {
        var c = contacts[k], A = c.a, B = c.b;
        if (!B) continue;
        var dx = B.x - A.x, dy = B.y - A.y, rr = A.r + B.r;
        var d2 = dx * dx + dy * dy;
        if (d2 >= rr * rr) continue;
        var d = Math.sqrt(d2), nx, ny;
        if (d > 1e-6) { nx = dx / d; ny = dy / d; } else { nx = c.nx; ny = c.ny; }
        var pen = rr - d - SLOP;
        if (pen <= 0) continue;
        var corr = Math.min(pen * 0.45, 2.5) / (A.im + B.im);
        A.x -= nx * corr * A.im; A.y -= ny * corr * A.im;
        B.x += nx * corr * B.im; B.y += ny * corr * B.im;
      }
      // walls are hard limits
      for (var i = 0; i < fruits.length; i++) {
        var f = fruits[i];
        if (f.x < f.r) f.x = f.r;
        else if (f.x > JW - f.r) f.x = JW - f.r;
        if (f.y > JH - f.r) f.y = JH - f.r;
      }
    }
  }

  function physics(dt) {
    var h = dt / SUBSTEPS, i, f;
    var lin = 1 - 0.15 * h, ang = 1 - 1.6 * h;
    for (var s = 0; s < SUBSTEPS; s++) {
      for (i = 0; i < fruits.length; i++) {
        f = fruits[i];
        f.vy += GRAVITY * h;
        f.vx *= lin; f.vy *= lin; f.w *= ang;
      }
      buildContacts();
      solveVelocities();
      for (i = 0; i < fruits.length; i++) {
        f = fruits[i];
        var sp = f.vx * f.vx + f.vy * f.vy;
        if (sp > 1800 * 1800) { var q = 1800 / Math.sqrt(sp); f.vx *= q; f.vy *= q; }
        f.x += f.vx * h; f.y += f.vy * h; f.a += f.w * h;
      }
      solvePositions();
    }
  }

  /* ------------------------------------------------------------------ */
  /* Merging                                                             */
  /* ------------------------------------------------------------------ */
  function doMerges() {
    if (!mergePairs.length) return;
    var born = [];
    for (var i = 0; i < mergePairs.length; i += 2) {
      var A = mergePairs[i], B = mergePairs[i + 1];
      if (A.merged || B.merged || A.dead || B.dead) continue;
      A.merged = B.merged = true;
      A.dead = B.dead = true;
      var x = (A.x + B.x) / 2, y = (A.y + B.y) / 2;
      var t = A.t + 1;
      // chain / combo bookkeeping
      chain = clock - lastMergeT < 0.9 ? chain + 1 : 1;
      lastMergeT = clock;
      var pts, F;
      if (t > LAST) {
        // two giant watermelons: both burst for a huge bonus
        pts = 250;
        F = FRUITS[LAST];
        burst(x, y, LAST, 2.2);
        sparkles(x, y, 40, 160);
        shake = Math.max(shake, 14);
        flash = 1;
        Snd.melon();
      } else {
        var f = makeFruit(t, x, y);
        f.vx = (A.vx + B.vx) / 2;
        f.vy = Math.min((A.vy + B.vy) / 2, 0) - 60;
        f.w = (A.w + B.w) / 2;
        f.armed = true;
        // grow smoothly so neighbours are pushed aside gently
        f.grow = 0;
        f.r = Math.max(A.r, B.r);
        setMass(f);
        f.sq = 0.32; f.sqv = 0;
        f.happy = 0.9;
        born.push(f);
        pts = pointsFor(t);
        F = FRUITS[t];
        burst(x, y, t, 1);
        if (t >= 7) shake = Math.max(shake, 3 + t);
        if (t === LAST) { sparkles(x, y, 30, 130); flash = 0.7; Snd.melon(); }
        if (t > maxLevel) maxLevel = t;
        Snd.merge(t, chain);
      }
      var bonus = chain >= 2 ? Math.round(pts * 0.5 * (chain - 1)) : 0;
      if (state === 'play') {
        score += pts + bonus;
        popups.push({ x: x, y: y - 10, text: '+' + (pts + bonus), color: F.line, life: 1, size: 18 + Math.min(t, 10) * 1.6 });
        if (chain >= 2) {
          for (var pi = popups.length - 1; pi >= 0; pi--) if (popups[pi].combo) popups.splice(pi, 1);
          popups.push({ combo: true, x: x, y: y - 42, text: 'Combo x' + chain + '!', color: '#ff5f86', life: 1.2, size: 20 + Math.min(chain, 6) * 2 });
        }
      }
    }
    mergePairs.length = 0;
    // remove dead fruits, add the newborns
    var w = 0;
    for (var k = 0; k < fruits.length; k++) if (!fruits[k].dead) fruits[w++] = fruits[k];
    fruits.length = w;
    for (k = 0; k < born.length; k++) fruits.push(born[k]);
  }

  /* ------------------------------------------------------------------ */
  /* Particles                                                           */
  /* ------------------------------------------------------------------ */
  function burst(x, y, t, scale) {
    var F = FRUITS[Math.min(t, LAST)], R = F.r;
    var n = Math.round((10 + t * 3) * scale);
    for (var i = 0; i < n; i++) {
      var a = rand(0, TAU), sp = rand(120, 330 + t * 25) * scale;
      particles.push({
        k: 0, x: x + Math.cos(a) * R * 0.5, y: y + Math.sin(a) * R * 0.5,
        vx: Math.cos(a) * sp, vy: Math.sin(a) * sp - 120,
        life: rand(0.45, 0.85), max: 0.85, s: rand(2.5, 4.5 + t * 0.4),
        c: Math.random() < 0.6 ? F.base : F.light
      });
    }
    for (i = 0; i < 4 + t; i++) {
      particles.push({
        k: 1, x: x + rand(-R, R) * 0.6, y: y + rand(-R, R) * 0.6, vx: rand(-30, 30), vy: rand(-140, -60),
        life: rand(0.8, 1.4), max: 1.4, s: rand(3, 6 + t * 0.6), c: '#fff'
      });
    }
    particles.push({ k: 2, x: x, y: y, vx: 0, vy: 0, life: 0.4, max: 0.4, s: R, c: '#fff' });
  }

  function sparkles(x, y, n, spread) {
    var cols = ['#ffd93d', '#ff86a5', '#7ee0c8', '#ffffff', '#b98cff'];
    for (var i = 0; i < n; i++) {
      var a = rand(0, TAU), sp = rand(80, 260) * spread / 130;
      particles.push({
        k: 3, x: x, y: y, vx: Math.cos(a) * sp, vy: Math.sin(a) * sp - 160,
        life: rand(0.8, 1.5), max: 1.5, s: rand(4, 9), c: cols[i % cols.length], rot: rand(0, TAU)
      });
    }
  }

  function updateParticles(dt) {
    var w = 0;
    for (var i = 0; i < particles.length; i++) {
      var p = particles[i];
      p.life -= dt;
      if (p.life <= 0) continue;
      if (p.k === 0 || p.k === 3) { p.vy += 900 * dt * (p.k === 3 ? 0.45 : 1); p.vx *= 1 - 1.2 * dt; }
      else if (p.k === 1) { p.vx *= 1 - 2 * dt; p.x += Math.sin((p.life + p.s) * 7) * 12 * dt; }
      p.x += p.vx * dt; p.y += p.vy * dt;
      if (p.rot !== undefined) p.rot += dt * 4;
      particles[w++] = p;
    }
    particles.length = w;
    w = 0;
    for (i = 0; i < popups.length; i++) {
      var q = popups[i];
      q.life -= dt;
      if (q.life <= 0) continue;
      q.y -= 40 * dt;
      popups[w++] = q;
    }
    popups.length = w;
  }

  /* ------------------------------------------------------------------ */
  /* Update                                                              */
  /* ------------------------------------------------------------------ */
  function dropFruit() {
    if (state !== 'play' || cooldown > 0 || current < 0) return;
    // a hair of randomness so perfectly centred towers can still topple
    var f = makeFruit(current, aimX + rand(-0.4, 0.4), DROP_Y);
    f.vy = 60;
    f.sq = -0.12;
    fruits.push(f);
    Snd.drop();
    // the soap bubble that held the fruit pops
    for (var i = 0; i < 10; i++) {
      var a = i / 10 * TAU;
      particles.push({ k: 1, x: aimX + Math.cos(a) * (f.r + 6), y: DROP_Y + Math.sin(a) * (f.r + 6), vx: Math.cos(a) * 70, vy: Math.sin(a) * 70 - 20, life: 0.4, max: 0.4, s: 2.5, c: '#fff' });
    }
    current = -1;
    cooldown = DROP_COOLDOWN;
  }

  function clampAim(x) {
    var r = current >= 0 ? FRUITS[current].r : FRUITS[0].r;
    return clamp(x, r + 1, JW - r - 1);
  }

  function update(dt) {
    clock += dt;
    if (state === 'play') {
      if (keys.left) aimTarget -= 330 * dt;
      if (keys.right) aimTarget += 330 * dt;
      aimTarget = clampAim(aimTarget);
      aimX += (aimTarget - aimX) * Math.min(1, dt * 22);
      aimX = clampAim(aimX);
      if (current < 0) {
        cooldown -= dt;
        if (cooldown <= 0) {
          current = next;
          next = pickDropType();
          heldPop = 1; nextPop = 1;
          aimTarget = clampAim(aimTarget);
        }
      }
    }

    physics(dt);
    if (state === 'play' || state === 'ending') doMerges();
    else mergePairs.length = 0;

    // per-fruit animation (growth, squash springs, faces)
    var above = false, i, f;
    for (i = 0; i < fruits.length; i++) {
      f = fruits[i];
      f.age += dt;
      f.merged = false;
      if (f.grow < 1) {
        f.grow = Math.min(1, f.grow + dt / 0.16);
        var e = 1 - Math.pow(1 - f.grow, 3);
        f.r = lerp(f.r, f.R, e);
        if (f.grow >= 1) f.r = f.R;
        setMass(f);
      }
      f.sqv += (-f.sq * 260 - f.sqv * 11) * dt;
      f.sq += f.sqv * dt;
      f.sq = clamp(f.sq, -0.35, 0.4);
      if (f.happy > 0) f.happy -= dt;
      f.worried = false;
      if (f.armed && f.age > 0.6 && f.y - f.r < LINE_Y - 2) { above = true; f.worried = true; }
    }

    if (state === 'play') {
      if (above) {
        dangerT += dt;
        warnBeat -= dt;
        if (warnBeat <= 0) { Snd.warn(); warnBeat = 0.5; }
        if (dangerT >= DANGER_TIME) gameOver();
      } else {
        dangerT = Math.max(0, dangerT - dt * 2);
        warnBeat = 0;
      }
    } else if (state === 'ending') {
      endT += dt;
      if (endT > 1.3) showOver();
    }
  }

  function updateFx(dt) {
    updateParticles(dt);
    shake = Math.max(0, shake - dt * 30);
    flash = Math.max(0, flash - dt * 2.2);
    holdBob += dt;
    heldPop = Math.max(0, heldPop - dt * 4);
    nextPop = Math.max(0, nextPop - dt * 4);
    displayScore += (score - displayScore) * Math.min(1, dt * 10);
    if (Math.abs(score - displayScore) < 0.5) displayScore = score;
    // ambient bubbles in the background
    var target = Math.round(W * H / 26000);
    while (bgBubbles.length < target) {
      bgBubbles.push({ x: rand(0, W), y: rand(0, H + 40), r: rand(4, 22), sp: rand(12, 34), ph: rand(0, TAU) });
    }
    if (bgBubbles.length > target) bgBubbles.length = target;
    for (var i = 0; i < bgBubbles.length; i++) {
      var b = bgBubbles[i];
      b.y -= b.sp * dt;
      b.ph += dt;
      if (b.y < -b.r * 2) { b.y = H + b.r * 2; b.x = rand(0, W); }
    }
  }

  /* ------------------------------------------------------------------ */
  /* Layout & resize                                                     */
  /* ------------------------------------------------------------------ */
  var W = 0, H = 0, dpr = 1, S = 1, ox = 0, oy = 0, landscape = false;
  var hudH = 0, stripH = 0, panelL = null, panelR = null;

  function layout() {
    W = Math.max(1, document.documentElement.clientWidth || window.innerWidth);
    H = Math.max(1, document.documentElement.clientHeight || window.innerHeight);
    dpr = Math.min(window.devicePixelRatio || 1, 2.5);
    canvas.width = Math.round(W * dpr);
    canvas.height = Math.round(H * dpr);
    landscape = W >= H * 1.1;
    var bw, bh;
    if (landscape) {
      var m = Math.max(8, H * 0.025);
      S = Math.min((H - 2 * m) / BOXH, (W * 0.5) / BOXW);
      bw = BOXW * S; bh = BOXH * S;
      ox = (W - bw) / 2; oy = (H - bh) / 2;
      panelL = { x: 0, y: 0, w: ox, h: H };
      panelR = { x: ox + bw, y: 0, w: W - ox - bw, h: H };
    } else {
      hudH = clamp(H * 0.095, 66, 108);
      stripH = clamp(H * 0.065, 38, 70);
      S = Math.min((W - 16) / BOXW, (H - hudH - stripH - 6) / BOXH);
      bw = BOXW * S; bh = BOXH * S;
      // share spare height between a roomier HUD and fruit strip
      var spare = H - hudH - stripH - bh - 6;
      if (spare > 0) {
        var addH = Math.min(spare * 0.4, 150 - hudH);
        if (addH > 0) { hudH += addH; spare -= addH; }
        var addS = Math.min(spare * 0.5, 96 - stripH);
        if (addS > 0) { stripH += addS; }
      }
      ox = (W - bw) / 2;
      oy = hudH + (H - hudH - stripH - bh) / 2;
    }
    bakeAll(S * dpr);
  }

  // screen (CSS px) -> world x
  function toWorldX(px) { return (px - ox) / S + BOX_X0; }
  function wx(x) { return ox + (x - BOX_X0) * S; }
  function wy(y) { return oy + (y - BOX_Y0) * S; }

  /* ------------------------------------------------------------------ */
  /* Rendering                                                           */
  /* ------------------------------------------------------------------ */
  var FONT = '"Trebuchet MS", "Segoe UI", ui-rounded, system-ui, sans-serif';
  var INK = '#5b2a5e';

  function rrect(x, y, w, h, r) {
    r = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  function drawBackground() {
    var g = ctx.createLinearGradient(0, 0, W * 0.3, H);
    g.addColorStop(0, '#c8efe2');
    g.addColorStop(0.55, '#e7e6f6');
    g.addColorStop(1, '#f8d8ea');
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, W, H);
    // soft polka dots
    ctx.fillStyle = 'rgba(255,255,255,0.28)';
    var step = 46;
    for (var y = 0, row = 0; y < H + step; y += step, row++) {
      for (var x = (row & 1) ? step / 2 : 0; x < W + step; x += step) {
        ctx.beginPath(); ctx.arc(x, y, 4, 0, TAU); ctx.fill();
      }
    }
    // drifting bubbles
    ctx.lineWidth = 1.5;
    for (var i = 0; i < bgBubbles.length; i++) {
      var b = bgBubbles[i], bx = b.x + Math.sin(b.ph * 0.8) * 8;
      ctx.strokeStyle = 'rgba(255,255,255,0.6)';
      ctx.fillStyle = 'rgba(255,255,255,0.12)';
      ctx.beginPath(); ctx.arc(bx, b.y, b.r, 0, TAU); ctx.fill(); ctx.stroke();
      ctx.fillStyle = 'rgba(255,255,255,0.7)';
      ctx.beginPath(); ctx.arc(bx - b.r * 0.4, b.y - b.r * 0.4, b.r * 0.2, 0, TAU); ctx.fill();
    }
  }

  function jarPath(inset) {
    var x0 = -inset, x1 = JW + inset, y0 = -4, y1 = JH + inset, r = 22 + inset * 0.5;
    ctx.beginPath();
    ctx.moveTo(x0, y0);
    ctx.lineTo(x0, y1 - r);
    ctx.quadraticCurveTo(x0, y1, x0 + r, y1);
    ctx.lineTo(x1 - r, y1);
    ctx.quadraticCurveTo(x1, y1, x1, y1 - r);
    ctx.lineTo(x1, y0);
  }

  function drawJarBack() {
    // shadow on the table
    ctx.fillStyle = 'rgba(91,42,94,0.13)';
    ellipse(ctx, JW / 2, JH + 20, JW * 0.58, 12, 0); ctx.fill();
    // glass interior
    jarPath(0);
    ctx.closePath();
    var g = ctx.createLinearGradient(0, 0, 0, JH);
    g.addColorStop(0, 'rgba(255,255,255,0.25)');
    g.addColorStop(1, 'rgba(255,255,255,0.55)');
    ctx.fillStyle = g;
    ctx.fill();
    // danger line
    var pulse = dangerT > 0 ? 0.5 + 0.5 * Math.sin(clock * 16) : 0;
    ctx.save();
    ctx.setLineDash([10, 8]);
    ctx.lineDashOffset = -clock * 20;
    ctx.lineWidth = dangerT > 0 ? 3 + pulse * 2 : 2.5;
    ctx.strokeStyle = dangerT > 0 ? 'rgba(255,60,100,' + (0.6 + 0.4 * pulse) + ')' : 'rgba(255,95,134,0.45)';
    ctx.beginPath(); ctx.moveTo(4, LINE_Y); ctx.lineTo(JW - 4, LINE_Y); ctx.stroke();
    ctx.restore();
  }

  function drawJarFront() {
    // thick glass walls
    jarPath(6);
    ctx.lineWidth = 12;
    ctx.lineJoin = 'round';
    ctx.strokeStyle = 'rgba(255,255,255,0.62)';
    ctx.stroke();
    jarPath(12.5);
    ctx.lineWidth = 2;
    ctx.strokeStyle = 'rgba(91,42,94,0.28)';
    ctx.stroke();
    jarPath(0);
    ctx.lineWidth = 1.5;
    ctx.strokeStyle = 'rgba(255,255,255,0.9)';
    ctx.stroke();
    // rim lips
    ctx.fillStyle = '#fff';
    rrect(-16, -10, 20, 10, 5); ctx.fill();
    rrect(JW - 4, -10, 20, 10, 5); ctx.fill();
    ctx.strokeStyle = 'rgba(91,42,94,0.25)'; ctx.lineWidth = 1.5;
    rrect(-16, -10, 20, 10, 5); ctx.stroke();
    rrect(JW - 4, -10, 20, 10, 5); ctx.stroke();
    // glass reflections
    ctx.fillStyle = 'rgba(255,255,255,0.22)';
    rrect(12, 30, 10, JH - 90, 5); ctx.fill();
    rrect(30, 40, 4, JH * 0.4, 2); ctx.fill();
    ctx.fillStyle = 'rgba(255,255,255,0.14)';
    rrect(JW - 24, 60, 8, JH * 0.55, 4); ctx.fill();
  }

  function drawFruits() {
    var danger = state === 'play' && dangerT > 0;
    for (var i = 0; i < fruits.length; i++) {
      var f = fruits[i];
      var mood = f.happy > 0 ? 1 : (danger && f.worried) || state === 'ending' || state === 'over' ? 2 : 0;
      var sx = 1 + f.sq, sy = 1 - f.sq;
      // shadow-ish rim to separate overlapping fruit
      blitFruit(f.t, mood, f.x, f.y + f.r * f.sq * 0.6, f.r, f.a, sx, sy);
    }
  }

  // Ray-casts straight down from the dropper to find where the fruit would land.
  function landingY(x, r) {
    var y = JH - r;
    for (var i = 0; i < fruits.length; i++) {
      var f = fruits[i], dx = Math.abs(f.x - x), rr = f.r + r;
      if (dx >= rr) continue;
      var cy = f.y - Math.sqrt(rr * rr - dx * dx);
      if (cy < y && cy > DROP_Y) y = cy;
    }
    return y;
  }

  function drawDropper() {
    var inPlay = state === 'play';
    // rail
    ctx.fillStyle = 'rgba(255,255,255,0.85)';
    rrect(-24, RAIL_Y - 5, JW + 48, 10, 5); ctx.fill();
    ctx.strokeStyle = 'rgba(91,42,94,0.25)'; ctx.lineWidth = 1.5; ctx.stroke();
    var x = aimX;
    // guide line
    if (inPlay && current >= 0) {
      var r = FRUITS[current].r;
      var ly = landingY(x, r);
      ctx.save();
      ctx.setLineDash([2, 9]);
      ctx.lineCap = 'round';
      ctx.lineWidth = 4;
      ctx.strokeStyle = 'rgba(255,255,255,0.9)';
      ctx.beginPath(); ctx.moveTo(x, DROP_Y + r + 8); ctx.lineTo(x, ly + r); ctx.stroke();
      ctx.restore();
      ctx.strokeStyle = 'rgba(255,255,255,0.75)';
      ctx.lineWidth = 2;
      ctx.beginPath(); ctx.arc(x, ly, r, 0.15 * Math.PI, 0.85 * Math.PI); ctx.stroke();
    }
    // cloud carriage
    ctx.save();
    ctx.translate(x, RAIL_Y);
    ctx.fillStyle = '#fff';
    ctx.strokeStyle = 'rgba(91,42,94,0.35)';
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(-14, 2, 10, 0, TAU); ctx.arc(0, -4, 13, 0, TAU); ctx.arc(14, 2, 10, 0, TAU);
    ctx.stroke();
    ctx.beginPath(); ctx.arc(-14, 2, 10, 0, TAU); ctx.fill();
    ctx.beginPath(); ctx.arc(0, -4, 13, 0, TAU); ctx.fill();
    ctx.beginPath(); ctx.arc(14, 2, 10, 0, TAU); ctx.fill();
    ctx.fillStyle = '#3b1d2e';
    ctx.beginPath(); ctx.arc(-4, -2, 1.8, 0, TAU); ctx.arc(4, -2, 1.8, 0, TAU); ctx.fill();
    ctx.fillStyle = 'rgba(255,110,150,0.5)';
    ctx.beginPath(); ctx.arc(-9, 2, 2.6, 0, TAU); ctx.arc(9, 2, 2.6, 0, TAU); ctx.fill();
    ctx.restore();
    // fruit in a soap bubble
    if (current >= 0 && (inPlay || state === 'menu' || state === 'paused')) {
      var F = FRUITS[current];
      var pop = heldPop;
      var sc = 1 - pop * 0.5 + Math.sin(pop * Math.PI) * 0.25;
      var by = DROP_Y + Math.sin(holdBob * 3) * 2;
      var br = (F.r + 7) * sc;
      ctx.strokeStyle = 'rgba(255,255,255,0.5)';
      ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.moveTo(x, RAIL_Y + 8); ctx.lineTo(x, by - br); ctx.stroke();
      blitFruit(current, 0, x, by, F.r * sc, Math.sin(holdBob * 2) * 0.08, 1, 1);
      var bg = ctx.createRadialGradient(x - br * 0.3, by - br * 0.3, br * 0.2, x, by, br);
      bg.addColorStop(0, 'rgba(255,255,255,0)');
      bg.addColorStop(0.8, 'rgba(200,240,255,0.18)');
      bg.addColorStop(1, 'rgba(255,200,240,0.45)');
      ctx.fillStyle = bg;
      ctx.beginPath(); ctx.arc(x, by, br, 0, TAU); ctx.fill();
      ctx.strokeStyle = 'rgba(255,255,255,0.85)';
      ctx.lineWidth = 2;
      ctx.stroke();
      ctx.fillStyle = 'rgba(255,255,255,0.85)';
      ellipse(ctx, x - br * 0.5, by - br * 0.55, br * 0.16, br * 0.08, -0.7); ctx.fill();
    }
  }

  function drawParticles() {
    for (var i = 0; i < particles.length; i++) {
      var p = particles[i], k = p.life / p.max;
      if (p.k === 0) {
        ctx.globalAlpha = Math.min(1, k * 1.6);
        ctx.fillStyle = p.c;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.s * (0.5 + k * 0.5), 0, TAU); ctx.fill();
      } else if (p.k === 1) {
        ctx.globalAlpha = Math.min(1, k * 2) * 0.85;
        ctx.strokeStyle = p.c; ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.s, 0, TAU); ctx.stroke();
        ctx.fillStyle = 'rgba(255,255,255,0.8)';
        ctx.beginPath(); ctx.arc(p.x - p.s * 0.35, p.y - p.s * 0.35, p.s * 0.25, 0, TAU); ctx.fill();
      } else if (p.k === 2) {
        ctx.globalAlpha = k * 0.9;
        ctx.strokeStyle = p.c; ctx.lineWidth = 6 * k + 1;
        ctx.beginPath(); ctx.arc(p.x, p.y, p.s * (1.6 - k * 0.6), 0, TAU); ctx.stroke();
      } else {
        ctx.globalAlpha = Math.min(1, k * 2);
        ctx.fillStyle = p.c;
        star(p.x, p.y, p.s, p.rot);
      }
    }
    ctx.globalAlpha = 1;
  }

  function star(x, y, s, rot) {
    ctx.save();
    ctx.translate(x, y); ctx.rotate(rot);
    ctx.beginPath();
    for (var i = 0; i < 8; i++) {
      var rr = i & 1 ? s * 0.4 : s, a = i / 8 * TAU;
      if (i === 0) ctx.moveTo(Math.cos(a) * rr, Math.sin(a) * rr); else ctx.lineTo(Math.cos(a) * rr, Math.sin(a) * rr);
    }
    ctx.closePath(); ctx.fill();
    ctx.restore();
  }

  function drawPopups() {
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    for (var i = 0; i < popups.length; i++) {
      var q = popups[i], k = q.life;
      var sc = k > 0.85 ? 1 + (k - 0.85) * 3 : 1;
      ctx.globalAlpha = Math.min(1, k * 2.5);
      ctx.font = '900 ' + Math.round(q.size * sc) + 'px ' + FONT;
      ctx.lineWidth = 5; ctx.lineJoin = 'round';
      ctx.strokeStyle = '#fff';
      ctx.strokeText(q.text, q.x, q.y);
      ctx.fillStyle = q.color;
      ctx.fillText(q.text, q.x, q.y);
    }
    ctx.globalAlpha = 1;
  }

  function drawDangerCountdown() {
    if (state !== 'play' || dangerT <= 0.35) return;
    var left = Math.max(0, DANGER_TIME - dangerT);
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.font = '900 30px ' + FONT;
    ctx.lineWidth = 6; ctx.strokeStyle = '#fff';
    var txt = left.toFixed(1);
    ctx.strokeText(txt, JW / 2, 30);
    ctx.fillStyle = '#ff3c64';
    ctx.fillText(txt, JW / 2, 30);
  }

  // ---- HUD (screen space) ----
  function card(x, y, w, h, r) {
    ctx.save();
    ctx.shadowColor = 'rgba(91,42,94,0.18)';
    ctx.shadowBlur = 12; ctx.shadowOffsetY = 4;
    rrect(x, y, w, h, r);
    ctx.fillStyle = 'rgba(255,255,255,0.78)';
    ctx.fill();
    ctx.restore();
    rrect(x, y, w, h, r);
    ctx.lineWidth = 2; ctx.strokeStyle = '#fff'; ctx.stroke();
  }

  function label(text, x, y, size, align, color, weight) {
    ctx.font = (weight || 800) + ' ' + Math.round(size) + 'px ' + FONT;
    ctx.textAlign = align || 'center';
    ctx.textBaseline = 'middle';
    ctx.fillStyle = color || INK;
    ctx.fillText(text, x, y);
  }

  function fitText(text, maxW, size, weight) {
    ctx.font = (weight || 900) + ' ' + Math.round(size) + 'px ' + FONT;
    var w = ctx.measureText(text).width;
    return w > maxW ? size * maxW / w : size;
  }

  function nextBubble(cx, cy, rad) {
    var g = ctx.createRadialGradient(cx - rad * 0.3, cy - rad * 0.3, rad * 0.2, cx, cy, rad);
    g.addColorStop(0, 'rgba(255,255,255,0.6)');
    g.addColorStop(1, 'rgba(255,215,240,0.75)');
    ctx.fillStyle = g;
    ctx.beginPath(); ctx.arc(cx, cy, rad, 0, TAU); ctx.fill();
    ctx.lineWidth = 2.5; ctx.strokeStyle = '#fff'; ctx.stroke();
    if (next >= 0 && state !== 'menu') {
      var sc = 1 - nextPop * 0.4;
      var fr = rad * 0.6 * (0.6 + 0.4 * FRUITS[next].r / FRUITS[4].r) * sc;
      blitFruit(next, 0, cx, cy + fr * 0.08, fr, 0, 1, 1);
    }
  }

  function evolutionRing(cx, cy, rad) {
    var n = FRUITS.length;
    ctx.strokeStyle = 'rgba(255,255,255,0.8)';
    ctx.lineWidth = 3;
    ctx.setLineDash([3, 7]);
    ctx.beginPath(); ctx.arc(cx, cy, rad, 0, TAU); ctx.stroke();
    ctx.setLineDash([]);
    for (var i = 0; i < n; i++) {
      var a = -Math.PI / 2 + i / n * TAU;
      var fr = rad * (0.13 + 0.12 * i / (n - 1));
      blitFruit(i, 0, cx + Math.cos(a) * rad, cy + Math.sin(a) * rad, fr, 0, 1, 1, i <= maxLevel || state === 'menu' ? 1 : 0.35);
    }
  }

  function evolutionStrip(x0, x1, cy, hgt) {
    var n = FRUITS.length, total = 0, i;
    var sizes = [];
    for (i = 0; i < n; i++) { sizes[i] = 0.42 + 0.58 * i / (n - 1); total += sizes[i]; }
    var avail = x1 - x0;
    var unit = Math.min(hgt * 0.5, avail / (total * 2 + n * 0.25));
    var gap = (avail - total * 2 * unit) / (n - 1);
    var x = x0;
    for (i = 0; i < n; i++) {
      var fr = sizes[i] * unit;
      blitFruit(i, 0, x + fr, cy + (unit - fr) * 0.6, fr, 0, 1, 1, i <= maxLevel || state === 'menu' ? 1 : 0.35);
      x += fr * 2 + gap;
    }
  }

  function drawHUD() {
    var scoreTxt = String(Math.round(displayScore));
    var bestTxt = String(Math.max(best, score));
    if (landscape) {
      // left panel: title + score + best
      var pw = panelL.w, u = clamp(Math.min(pw / 260, H / 560), 0.55, 1.7);
      var cw = Math.min(pw - 24 * u, 240 * u), cx = pw / 2;
      var y = H * 0.1;
      var ts = fitText('Bubble', cw, 40 * u);
      ctx.save();
      ctx.lineJoin = 'round';
      label('Bubble', cx, y, ts, 'center', '#3fb6a8', 900);
      label('Melon', cx, y + ts * 0.95, ts, 'center', '#ff5f86', 900);
      ctx.restore();
      y += ts * 1.6;
      var ch = 92 * u;
      card(cx - cw / 2, y, cw, ch, 22 * u);
      label('SCORE', cx, y + 22 * u, 15 * u, 'center', INK, 800);
      label(scoreTxt, cx, y + 58 * u, fitText(scoreTxt, cw - 20, 42 * u), 'center', '#ff5f86', 900);
      y += ch + 12 * u;
      var bh = 62 * u;
      card(cx - cw / 2, y, cw, bh, 20 * u);
      label('BEST', cx, y + 18 * u, 13 * u, 'center', INK, 800);
      label(bestTxt, cx, y + 42 * u, fitText(bestTxt, cw - 20, 26 * u), 'center', '#3fb6a8', 900);

      // right panel: next + evolution ring
      var rx = panelR.x + panelR.w / 2;
      var ry = Math.max(70, H * 0.12);
      var nr = Math.min(52 * u, panelR.w * 0.25);
      label('NEXT', rx, ry, 15 * u, 'center', INK, 800);
      nextBubble(rx, ry + 14 * u + nr, nr);
      var top = ry + 14 * u + nr * 2 + 18 * u;
      var ringR = Math.min(panelR.w * 0.32, (H - top - 16) / 2 - 18 * u);
      if (ringR > 40) evolutionRing(rx, top + (H - top) / 2 - 4, ringR);
    } else {
      var s = clamp(hudH / 90, 0.8, 1.5);
      var lx = Math.max(14, ox + 10 * s);
      var nrr = Math.min(hudH * 0.3, 40 * s);
      var nx = Math.min(W / 2 + 10, W - 112 - nrr);
      var ncy = hudH * 0.56;
      var maxW = nx - nrr - 14 - lx;
      label('SCORE', lx, hudH * 0.24, 13 * s, 'left', INK, 800);
      label(scoreTxt, lx, hudH * 0.52, fitText(scoreTxt, maxW, 36 * s), 'left', '#ff5f86', 900);
      label('BEST ' + bestTxt, lx, hudH * 0.8, fitText('BEST ' + bestTxt, maxW, 14 * s), 'left', '#3fb6a8', 900);
      label('NEXT', nx, ncy - nrr - 9 * s, 12 * s, 'center', INK, 800);
      nextBubble(nx, ncy, nrr);
      // evolution strip below the jar
      var sy = Math.min(H - stripH / 2 - 2, wy(JH + 30) + stripH / 2);
      var sx0 = Math.max(10, wx(-10)), sx1 = Math.min(W - 10, wx(JW + 10));
      evolutionStrip(sx0, sx1, sy, stripH);
    }
  }

  function render() {
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    drawBackground();
    ctx.save();
    var shx = shake > 0 ? rand(-shake, shake) * 0.5 : 0, shy = shake > 0 ? rand(-shake, shake) * 0.5 : 0;
    ctx.translate(ox + shx - BOX_X0 * S, oy + shy - BOX_Y0 * S);
    ctx.scale(S, S);
    drawJarBack();
    drawFruits();
    drawJarFront();
    drawDropper();
    drawParticles();
    drawPopups();
    drawDangerCountdown();
    ctx.restore();
    drawHUD();
    if (flash > 0) {
      ctx.fillStyle = 'rgba(255,255,255,' + flash * 0.5 + ')';
      ctx.fillRect(0, 0, W, H);
    }
  }

  /* ------------------------------------------------------------------ */
  /* State transitions & UI                                              */
  /* ------------------------------------------------------------------ */
  function show(el, on) { el.classList.toggle('hidden', !on); }

  function startGame() {
    Snd.init();
    Snd.click();
    resetGame();
    state = 'play';
    show(ui.menu, false); show(ui.over, false); show(ui.pause, false);
    show(ui.corner, true);
    show(ui.btnPause, true);
  }

  function pauseGame() {
    if (state !== 'play') return;
    state = 'paused';
    keys.left = keys.right = false;
    aiming = false;
    show(ui.pause, true);
  }

  function resumeGame() {
    if (state !== 'paused') return;
    Snd.init();
    state = 'play';
    show(ui.pause, false);
    last = performance.now();
  }

  function gameOver() {
    state = 'ending';
    endT = 0;
    shake = 8;
    Snd.over();
    if (score > best) {
      best = score;
      store.set('best', best);
      gameOver.newBest = true;
    } else gameOver.newBest = false;
    show(ui.btnPause, false);
  }

  function showOver() {
    state = 'over';
    ui.finalScore.textContent = score;
    ui.finalBest.textContent = best;
    ui.finalBigName.textContent = FRUITS[maxLevel].name;
    ui.finalBigImg.src = iconURL(maxLevel);
    show(ui.newBest, !!gameOver.newBest);
    show(ui.over, true);
  }

  var iconCache = {};
  function iconURL(t) {
    if (!iconCache[t]) {
      var sp = bakeSprite(t, 44 / SPRITE_PAD / 1.05, 0);
      try { iconCache[t] = sp.cv.toDataURL('image/png'); } catch (e) { iconCache[t] = ''; }
    }
    return iconCache[t];
  }

  function buildMenu() {
    ui.menuBest.textContent = best;
    ui.menuHint.textContent = isTouch
      ? 'Drag anywhere to aim, release to drop.'
      : 'Move the mouse or use ← → to aim. Click or press Space to drop.';
    var lv = [0, 2, 4, 7, 10];
    var sizes = [30, 38, 46, 54, 64];
    ui.menuFruits.innerHTML = '';
    for (var i = 0; i < lv.length; i++) {
      var img = document.createElement('img');
      img.src = iconURL(lv[i]);
      img.alt = '';
      img.width = img.height = sizes[i];
      img.style.animationDelay = (i * 0.18) + 's';
      ui.menuFruits.appendChild(img);
    }
  }

  function tapButton(btn, fn) {
    btn.addEventListener('click', function (e) {
      e.preventDefault();
      btn.blur();
      Snd.init();
      fn();
    });
  }

  tapButton(ui.btnPlay, startGame);
  tapButton(ui.btnAgain, startGame);
  tapButton(ui.btnRestart, startGame);
  tapButton(ui.btnResume, resumeGame);
  tapButton(ui.btnPause, pauseGame);
  tapButton(ui.btnMute, function () {
    Snd.setMuted(!Snd.muted);
    ui.btnMute.classList.toggle('muted', Snd.muted);
    ui.btnMute.setAttribute('aria-label', Snd.muted ? 'Unmute sound' : 'Mute sound');
    Snd.click();
  });
  ui.btnMute.classList.toggle('muted', Snd.muted);

  /* ------------------------------------------------------------------ */
  /* Input                                                               */
  /* ------------------------------------------------------------------ */
  var aiming = false, aimPointer = -1;

  canvas.addEventListener('pointerdown', function (e) {
    Snd.init();
    if (state !== 'play') return;
    e.preventDefault();
    aiming = true;
    aimPointer = e.pointerId;
    try { canvas.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    aimTarget = clampAim(toWorldX(e.clientX));
    if (e.pointerType !== 'mouse') aimX = aimTarget;
  });
  canvas.addEventListener('pointermove', function (e) {
    if (state !== 'play') return;
    if (aiming && e.pointerId === aimPointer) aimTarget = clampAim(toWorldX(e.clientX));
    else if (e.pointerType === 'mouse') aimTarget = clampAim(toWorldX(e.clientX));
  });
  function release(e) {
    if (!aiming || e.pointerId !== aimPointer) return;
    aiming = false;
    if (state !== 'play') return;
    if (e.type === 'pointerup') {
      aimTarget = clampAim(toWorldX(e.clientX));
      aimX = aimTarget;
      dropFruit();
    }
  }
  canvas.addEventListener('pointerup', release);
  canvas.addEventListener('pointercancel', release);
  canvas.addEventListener('contextmenu', function (e) { e.preventDefault(); });
  document.addEventListener('contextmenu', function (e) { e.preventDefault(); });

  window.addEventListener('keydown', function (e) {
    var k = e.key;
    Snd.init();
    if (k === 'ArrowLeft' || k === 'a' || k === 'A') { keys.left = true; e.preventDefault(); }
    else if (k === 'ArrowRight' || k === 'd' || k === 'D') { keys.right = true; e.preventDefault(); }
    else if (k === ' ' || k === 'Spacebar' || k === 'ArrowDown' || k === 'Enter' || k === 's' || k === 'S') {
      e.preventDefault();
      if (e.repeat) return;
      if (state === 'play') dropFruit();
      else if (state === 'menu' || state === 'over') startGame();
      else if (state === 'paused') resumeGame();
    } else if (k === 'p' || k === 'P' || k === 'Escape') {
      if (state === 'play') pauseGame(); else if (state === 'paused') resumeGame();
    }
  });
  window.addEventListener('keyup', function (e) {
    var k = e.key;
    if (k === 'ArrowLeft' || k === 'a' || k === 'A') keys.left = false;
    else if (k === 'ArrowRight' || k === 'd' || k === 'D') keys.right = false;
  });
  window.addEventListener('blur', function () { keys.left = keys.right = false; });

  document.addEventListener('visibilitychange', function () {
    if (document.hidden) pauseGame();
    last = performance.now();
  });

  window.addEventListener('resize', layout);
  window.addEventListener('orientationchange', function () { setTimeout(layout, 120); });

  /* ------------------------------------------------------------------ */
  /* Main loop                                                           */
  /* ------------------------------------------------------------------ */
  var last = performance.now(), acc = 0;
  function frame(now) {
    requestAnimationFrame(frame);
    var dt = (now - last) / 1000;
    last = now;
    if (!(dt > 0)) dt = 0;
    if (dt > 0.1) dt = 0.1;
    if (state !== 'paused') {
      acc += dt;
      var n = 0;
      while (acc >= STEP && n < 6) { update(STEP); acc -= STEP; n++; }
      if (n === 6) acc = 0;
      updateFx(dt);
    }
    render();
  }

  // Small hook used by automated tests/screenshots (reads real game state).
  window.BubbleMelon = {
    get state() { return state; },
    get score() { return score; },
    get current() { return current < 0 ? next : current; },
    get maxLevel() { return maxLevel; },
    get fruits() { return fruits.length; },
    get list() { return fruits.map(function (f) { return [f.t, +f.x.toFixed(2), +f.y.toFixed(2), Math.round(f.vx), Math.round(f.vy), +f.r.toFixed(1), f.grow, f.id]; }); },
    get maxSpeed() { var m = 0; for (var i = 0; i < fruits.length; i++) m = Math.max(m, Math.hypot(fruits[i].vx, fruits[i].vy)); return m; },
    get overlap() { var m = 0; for (var i = 0; i < fruits.length; i++) for (var j = i + 1; j < fruits.length; j++) { var a = fruits[i], b = fruits[j]; m = Math.max(m, a.r + b.r - Math.hypot(a.x - b.x, a.y - b.y)); } return m; },
    screenX: function (x) { return wx(x); },
    aim: function (x) { aimTarget = aimX = clampAim(x); },
    drop: function (x) { if (current < 0) { current = next; next = pickDropType(); } cooldown = 0; if (x !== undefined) { aimTarget = aimX = clampAim(x); } dropFruit(); },
    step: function (sec) { var n = Math.round(sec / STEP); for (var i = 0; i < n; i++) { update(STEP); updateFx(STEP); } }
  };

  layout();
  menuPile();
  for (var i = 0; i < 180; i++) update(STEP);  // let the decorative pile settle
  buildMenu();
  requestAnimationFrame(frame);
})();
