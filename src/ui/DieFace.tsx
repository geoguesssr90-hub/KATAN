// @ts-nocheck
import { DOT_POS } from "../game/constants";

export default function DieFace({ value, size = 36, rolling = false }) {
  const dots = DOT_POS[value] || DOT_POS[1];
  return (
    <svg width={size} height={size} viewBox="0 0 100 100" className={rolling ? "die-rolling" : ""}
      style={{ filter: "drop-shadow(0 2px 3px #0007)" }}>
      <rect x="4" y="4" width="92" height="92" rx="16" ry="16" fill="#f6ecd0" stroke="#6a4e26" strokeWidth="5" />
      <rect x="12" y="12" width="76" height="30" rx="12" fill="#ffffff" opacity="0.4" />
      {dots.map(([cx, cy], i) => <circle key={i} cx={cx} cy={cy} r="10" fill="#3a2c18" />)}
    </svg>
  );
}
