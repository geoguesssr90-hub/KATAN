// ゲーム全体で使う定数
export const SQ3 = Math.sqrt(3);
export const HS = 44;
export const BCX = 290;
export const BCY = 290;

// 地形ごとのグラデーション（上→下）
export const TERRAIN_GRAD: Record<string, [string, string]> = {
  forest: ["#3a8a40", "#1d5424"],
  hills: ["#d2622e", "#93381a"],
  pasture: ["#8fd05a", "#559a34"],
  fields: ["#eec84f", "#c39a28"],
  mountains: ["#97a0b5", "#5c6377"],
  desert: ["#ecd9a8", "#c4a468"],
};

export const TR: Record<string, string | null> = {
  forest: "lumber", hills: "brick", pasture: "wool", fields: "grain", mountains: "ore", desert: null,
};

export const RI: Record<string, string> = {
  lumber: "🪵", brick: "🧱", wool: "🐑", grain: "🌾", ore: "⛏️",
};

export const RN: Record<string, string> = {
  lumber: "木材", brick: "レンガ", wool: "羊毛", grain: "小麦", ore: "鉄鉱石",
};

// プレイヤーカラー（紋章風）と建物の屋根用の暗色
export const PC = ["#c23b2e", "#2f6db3", "#3e8f4e", "#d9822b"];
export const PC_DARK = ["#8c261d", "#1f4c80", "#2a6336", "#9e5a16"];

export const COSTS: Record<string, Record<string, number>> = {
  road: { lumber: 1, brick: 1 },
  settlement: { lumber: 1, brick: 1, wool: 1, grain: 1 },
  city: { grain: 2, ore: 3 },
  devCard: { ore: 1, grain: 1, wool: 1 },
};

export const RES_KEYS = ["lumber", "brick", "wool", "grain", "ore"];

export const DEV_NAMES: Record<string, string> = {
  knight: "⚔️ 騎士", vp: "⭐ 勝利点", roadBuilding: "🛣️ 道路建設", yearOfPlenty: "🌟 年の実り", monopoly: "💰 独占",
};

// 数字トークンの確率ドット数
export const NUM_PIPS: Record<number, number> = {
  2: 1, 3: 2, 4: 3, 5: 4, 6: 5, 8: 5, 9: 4, 10: 3, 11: 2, 12: 1,
};

// サイコロの目の座標
export const DOT_POS: Record<number, [number, number][]> = {
  1: [[50, 50]],
  2: [[28, 28], [72, 72]],
  3: [[28, 28], [50, 50], [72, 72]],
  4: [[28, 28], [72, 28], [28, 72], [72, 72]],
  5: [[28, 28], [72, 28], [50, 50], [28, 72], [72, 72]],
  6: [[28, 25], [72, 25], [28, 50], [72, 50], [28, 75], [72, 75]],
};
