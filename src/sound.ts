// @ts-nocheck
// サウンドマネージャ：効果音（public/sounds のmp3）+ WebAudio生成BGM

// イベント名 → 実ファイル名（拡張子なし）のマッピング
// public/sounds/ にファイルを追加したらここを書き換えるだけでOK
const SFX_FILES = {
  dice: "「えいっ！」",
  build: "刀の素振り",
  gameStart: "「始まるよ～」",
  steal: "「なんだザコかあ」",
  buy: "「ひとつ」",
  discard: "「もう…だめ…」",
  error: "「お金が足りないよ」",
  broke: "「挿入金が不足しています」",
  win: "start",
  lose: "「もう…だめ…」",
};

// ─── 効果音 ──────────────────────────────────────────────
let sfxOn = localStorage.getItem("catan:sfx") !== "off";

export const isSfxOn = () => sfxOn;

export function toggleSfx() {
  sfxOn = !sfxOn;
  localStorage.setItem("catan:sfx", sfxOn ? "on" : "off");
  return sfxOn;
}

export function playSfx(key) {
  if (!sfxOn) return;
  const file = SFX_FILES[key];
  if (!file) return;
  // 日本語ファイル名はURLエンコードしないと環境によって404になる
  const a = new Audio(`/sounds/${encodeURIComponent(file)}.mp3`);
  a.volume = 0.5;
  a.play().catch(() => {}); // autoplay制限は無視
}

// ─── BGM（WebAudioで生成するループ曲。mp3ファイル不要）───────────
let ctx = null;
let master = null;
let timer = null;
let nextBar = 0;
let barIdx = 0;
let bgmOn = false;

// C → Am → F → G の穏やかな進行
const CHORDS = [
  [261.63, 329.63, 392.00],
  [220.00, 261.63, 329.63],
  [174.61, 220.00, 261.63],
  [196.00, 246.94, 293.66],
];
const PENTA = [523.25, 587.33, 659.25, 783.99, 880.00];
const BAR = 3.2; // 1コード=3.2秒

function scheduleBar(t, chord) {
  // パッド（和音）
  chord.forEach(f => {
    const o = ctx.createOscillator();
    const g = ctx.createGain();
    o.type = "triangle";
    o.frequency.value = f / 2;
    g.gain.setValueAtTime(0, t);
    g.gain.linearRampToValueAtTime(0.05, t + 0.7);
    g.gain.setValueAtTime(0.05, t + BAR - 0.8);
    g.gain.linearRampToValueAtTime(0, t + BAR);
    o.connect(g).connect(master);
    o.start(t);
    o.stop(t + BAR + 0.05);
  });
  // ランダムなペンタトニックの爪弾き
  const steps = 8;
  for (let i = 0; i < steps; i++) {
    if (Math.random() < 0.4) {
      const f = PENTA[(Math.random() * PENTA.length) | 0];
      const st = t + i * (BAR / steps);
      const o = ctx.createOscillator();
      const g = ctx.createGain();
      o.type = "sine";
      o.frequency.value = f;
      g.gain.setValueAtTime(0.05, st);
      g.gain.exponentialRampToValueAtTime(0.0001, st + 0.6);
      o.connect(g).connect(master);
      o.start(st);
      o.stop(st + 0.65);
    }
  }
}

export const isBgmOn = () => bgmOn;

export function startBgm() {
  if (bgmOn) return;
  bgmOn = true;
  if (!ctx) {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) { bgmOn = false; return; }
    ctx = new AC();
    master = ctx.createGain();
    master.gain.value = 0.55;
    master.connect(ctx.destination);
  }
  ctx.resume().catch(() => {});
  nextBar = ctx.currentTime + 0.1;
  timer = setInterval(() => {
    while (nextBar < ctx.currentTime + 1.0) {
      scheduleBar(nextBar, CHORDS[barIdx % CHORDS.length]);
      barIdx++;
      nextBar += BAR;
    }
  }, 300);
}

export function stopBgm() {
  bgmOn = false;
  if (timer) { clearInterval(timer); timer = null; }
  if (ctx) ctx.suspend().catch(() => {});
}

export function toggleBgm() {
  if (bgmOn) { stopBgm(); localStorage.setItem("catan:bgm", "off"); }
  else { startBgm(); localStorage.setItem("catan:bgm", "on"); }
  return bgmOn;
}

// 最初のユーザー操作時に、設定がoffでなければBGMを開始する
export function ensureBgmPref() {
  if (localStorage.getItem("catan:bgm") !== "off" && !bgmOn) startBgm();
}
