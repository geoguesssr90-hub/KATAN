// @ts-nocheck
// 共通テーマ：古い航海図・羊皮紙スタイル

export const FONT_BODY = '"Zen Kaku Gothic New", "Hiragino Kaku Gothic ProN", "Yu Gothic UI", system-ui, sans-serif';
export const FONT_HEAD = '"Shippori Mincho B1", "Hiragino Mincho ProN", "Yu Mincho", serif';

export const C = {
  // 羊皮紙の上のインク
  ink: "#3d2f1e",
  inkSub: "#6e5b3e",
  inkDim: "#9a875f",
  // 羊皮紙
  parch: "#efe3c4",
  parchHi: "#f7edd4",
  parchLo: "#e2d0a8",
  line: "#b89d6a",
  lineSoft: "#d5c397",
  // 差し色
  red: "#9e3323",
  navy: "#2c5170",
  green: "#3e7a34",
  brass: "#8a6a2a",
  // 木のテーブルの上の文字
  cream: "#e8d9b0",
  creamDim: "#a08f68",
};

// 木のテーブル（ベースの色とノイズは index.css の body 側）
export const BG = "radial-gradient(1200px 800px at 50% -5%, rgba(130, 84, 46, 0.35), rgba(0,0,0,0) 60%)";

export const screenWrap = {
  minHeight: "100vh",
  background: BG,
  fontFamily: FONT_BODY,
  color: C.cream,
};

// 羊皮紙パネル
export const panelStyle = {
  background: "linear-gradient(170deg, #f4e9cb, #e7d6ae)",
  border: "1px solid #b89d6a",
  borderRadius: "6px",
  padding: "10px 12px",
  boxShadow: "inset 0 1px 0 #fff8, 0 3px 12px #00000066",
  color: C.ink,
};

// 革張りボタン
export const btnStyle = (disabled, active) => ({
  padding: "8px 10px",
  width: "100%",
  background: disabled
    ? "#d9c9a4"
    : active
      ? "linear-gradient(#7c3b22, #5c2917)"
      : "linear-gradient(#54402e, #3b2a1c)",
  color: disabled ? "#a3906a" : "#f0e2c0",
  border: `1px solid ${disabled ? "#c0ab7e" : active ? "#8a4a2a" : "#2c1d12"}`,
  borderRadius: "4px",
  cursor: disabled ? "not-allowed" : "pointer",
  fontSize: "12.5px",
  fontWeight: 600,
  letterSpacing: "0.5px",
  fontFamily: "inherit",
  boxShadow: disabled ? "none" : "inset 0 1px 0 #ffffff22, 0 2px 4px #00000044",
});

export const inputStyle = {
  display: "block",
  width: "100%",
  padding: "10px 12px",
  background: "#faf2dc",
  border: "1px solid #b89d6a",
  borderRadius: "5px",
  color: C.ink,
  fontSize: "14px",
  boxSizing: "border-box",
  outline: "none",
  marginBottom: "12px",
  fontFamily: "inherit",
  boxShadow: "inset 0 2px 4px #00000018",
};

// 封蝋レッドの主ボタン
export const primaryBtn = (enabled = true) => ({
  display: "block",
  width: "100%",
  padding: "12px",
  background: enabled ? "linear-gradient(#a83a28, #7e2417)" : "#d9c9a4",
  color: enabled ? "#f7ead0" : "#a3906a",
  border: `1px solid ${enabled ? "#5c180e" : "#c0ab7e"}`,
  borderRadius: "4px",
  fontSize: "15px",
  fontWeight: 700,
  letterSpacing: "2px",
  cursor: enabled ? "pointer" : "not-allowed",
  fontFamily: FONT_HEAD,
  boxShadow: enabled ? "inset 0 1px 0 #ffffff2e, 0 3px 8px #00000055" : "none",
});

// +/− のステッパーボタン
export const stepBtn = {
  padding: "2px 9px",
  background: "linear-gradient(#54402e, #3b2a1c)",
  border: "1px solid #2c1d12",
  borderRadius: "4px",
  color: "#f0e2c0",
  cursor: "pointer",
  fontSize: "14px",
  fontFamily: "inherit",
};

// セクション見出し（羊皮紙上）
export const sectionHead = {
  fontSize: "11px",
  color: C.inkSub,
  marginBottom: "6px",
  letterSpacing: "2px",
  fontWeight: 700,
  borderBottom: "1px solid #d5c397",
  paddingBottom: "3px",
  fontFamily: FONT_HEAD,
};
