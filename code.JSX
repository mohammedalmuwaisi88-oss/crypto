import { useState, useEffect, useRef, useMemo, useCallback } from "react";
 
/* ============================================================================
   CRYPTO TRADING INTELLIGENCE — live client-side engine
   Data: CoinGecko public /coins/markets endpoint (sparkline=true gives ~168
   hourly close prices per coin for the last 7 days — no API key required).
   Everything below (EMA/trend/BOS/breakout/DCA/position sizing) is computed
   in the browser from that real data. A few fields (marked "proxy" in the UI)
   are disclosed estimates because true on-chain / multi-year OHLC data needs
   a paid provider (Glassnode, Nansen, CryptoQuant, Binance klines) — see the
   README notes at the bottom of this file for how to wire those in later.
   ============================================================================ */
 
const REFRESH_MS = 20000; // 20s polling — gentle on CoinGecko's free rate limit
const MARKETS_URL =
  "https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd&order=market_cap_desc&per_page=100&page=1&sparkline=true&price_change_percentage=1h,24h,7d";
 
const STRATEGIES = [
  { id: "scalp", label: "Scalping", horizon: "Minutes–hours", weights: { trend: 0.15, smc: 0.30, breakout: 0.35, onchain: 0.10, dca: 0.10 } },
  { id: "swing", label: "Swing Trading", horizon: "Days–weeks", weights: { trend: 0.25, smc: 0.25, breakout: 0.20, onchain: 0.15, dca: 0.15 } },
  { id: "long", label: "Long-term Investing", horizon: "Months+", weights: { trend: 0.15, smc: 0.10, breakout: 0.10, onchain: 0.25, dca: 0.40 } },
];
 
/* ---------------------------- math utilities ---------------------------- */
 
function ema(values, period) {
  if (!values || values.length === 0) return null;
  const k = 2 / (period + 1);
  let prev = values[0];
  for (let i = 1; i < values.length; i++) prev = values[i] * k + prev * (1 - k);
  return prev;
}
 
function mean(a) { return a.reduce((s, v) => s + v, 0) / a.length; }
function stdev(a) {
  const m = mean(a);
  return Math.sqrt(mean(a.map((v) => (v - m) ** 2)));
}
 
// simple linear-regression slope, normalized to %/point relative to price level
function slopePct(values) {
  const n = values.length;
  if (n < 3) return 0;
  const xs = values.map((_, i) => i);
  const xm = mean(xs), ym = mean(values);
  let num = 0, den = 0;
  for (let i = 0; i < n; i++) { num += (xs[i] - xm) * (values[i] - ym); den += (xs[i] - xm) ** 2; }
  const slope = den === 0 ? 0 : num / den;
  return (slope / ym) * 100;
}
 
// pivot highs/lows (fractal: point higher/lower than `w` neighbors each side)
function findPivots(values, w = 4) {
  const highs = [], lows = [];
  for (let i = w; i < values.length - w; i++) {
    const win = values.slice(i - w, i + w + 1);
    if (values[i] === Math.max(...win)) highs.push({ i, v: values[i] });
    if (values[i] === Math.min(...win)) lows.push({ i, v: values[i] });
  }
  return { highs, lows };
}
 
// close-to-close ATR proxy (no true OHLC in sparkline data)
function atrProxy(values, lookback = 30) {
  const slice = values.slice(-lookback);
  const diffs = [];
  for (let i = 1; i < slice.length; i++) diffs.push(Math.abs(slice[i] - slice[i - 1]));
  return diffs.length ? mean(diffs) : 0;
}
 
function clamp(v, lo = 0, hi = 100) { return Math.max(lo, Math.min(hi, v)); }
function pct(a, b) { return b === 0 ? 0 : ((a - b) / b) * 100; }
 
/* ------------------------- per-coin analysis engine ------------------------ */
// series: array of hourly close prices (7d). coin: CoinGecko markets object.
// crossSection: { volRatioMedian, volatilityMedian } computed across the fetched universe.
 
function analyzeCoin(coin, series, crossSection) {
  if (!series || series.length < 30) return null;
 
  const price = series[series.length - 1];
  const emaShort = ema(series, 20);   // proxy for EMA20  (20h)
  const emaMid = ema(series, 50);     // proxy for EMA50  (50h)
  const emaLong = ema(series.length >= 120 ? series : series, 100); // proxy for EMA200 (100h)
  const trendSlope = slopePct(series.slice(-40));
  const adxProxy = clamp(Math.abs(trendSlope) * 12); // scaled 0-100 pseudo-ADX
 
  const { highs, lows } = findPivots(series, 4);
  const lastHighs = highs.slice(-3).map((p) => p.v);
  const lastLows = lows.slice(-3).map((p) => p.v);
  const higherHighsLows =
    lastHighs.length >= 2 && lastLows.length >= 2 &&
    lastHighs[lastHighs.length - 1] > lastHighs[0] &&
    lastLows[lastLows.length - 1] > lastLows[0];
 
  // A) Trend Following ------------------------------------------------------
  let trend = 0;
  if (price > emaMid && emaMid > emaLong) trend += 40;
  if (adxProxy > 25) trend += 30;
  if (higherHighsLows) trend += 30;
  trend = clamp(trend);
 
  // B) Price Action / Smart Money Concepts ----------------------------------
  const lastPivotHigh = highs.length ? highs[highs.length - 1].v : price;
  const priorPivotHigh = highs.length > 1 ? highs[highs.length - 2].v : lastPivotHigh;
  const bos = price > priorPivotHigh; // break of structure: close above prior swing high
 
  const lastPivotLow = lows.length ? lows[lows.length - 1].v : price;
  const nearOrderBlock = lastPivotLow > 0 && Math.abs(pct(price, lastPivotLow)) < 3 && price > lastPivotLow;
 
  // liquidity sweep: dipped below recent low then reclaimed it within the window
  const recentMinIdx = series.length - 20 > 0 ? series.length - 20 : 0;
  const recentWindow = series.slice(recentMinIdx);
  const recentLow = Math.min(...recentWindow);
  const dippedThenReclaimed =
    recentWindow.some((v) => v <= recentLow * 1.001) && price > recentLow * 1.01;
 
  let smc = 0;
  if (bos) smc += 30;
  if (nearOrderBlock) smc += 30;
  if (dippedThenReclaimed) smc += 40;
  smc = clamp(smc);
 
  // C) Breakout Strategy ------------------------------------------------------
  const resistanceWindow = series.slice(0, -6);
  const resistance = resistanceWindow.length ? Math.max(...resistanceWindow) : price;
  const brokeOut = price > resistance * 1.001;
  const volRatio = coin.total_volume / Math.max(coin.market_cap, 1); // turnover ratio
  const volumeSpike = volRatio > crossSection.volRatioMedian * 1.5;
  const range7d = Math.max(...series) - Math.min(...series);
  const closePercentile = range7d === 0 ? 100 : ((price - Math.min(...series)) / range7d) * 100;
  const strongClose = closePercentile > 80;
 
  let breakout = 0;
  if (brokeOut) breakout += 40;
  if (volumeSpike) breakout += 30;
  if (strongClose) breakout += 30;
  breakout = clamp(breakout);
 
  // D) On-Chain Analysis (disclosed proxy — no free reliable data source) -----
  const supplyRatio = coin.total_supply ? coin.circulating_supply / coin.total_supply : 0.85;
  const walletGrowthProxy = supplyRatio > 0.6; // more of supply liquid/circulating
  const outflowProxy = volumeSpike && trendSlope > 0; // heavy net buying volume during uptrend
  const whaleAccumProxy = strongClose && trend > 50;
 
  let onchain = 0;
  if (walletGrowthProxy) onchain += 30;
  if (outflowProxy) onchain += 40;
  if (whaleAccumProxy) onchain += 30;
  onchain = clamp(onchain);
 
  // E) DCA Suitability ---------------------------------------------------------
  const athChangePct = coin.ath_change_percentage ?? 0; // already negative, e.g. -55
  const farFromATH = athChangePct <= -30; // price < ATH * 0.7
  const returns = series.slice(1).map((v, i) => pct(v, series[i]));
  const volatility = stdev(returns);
  const lowVol = volatility < crossSection.volatilityMedian;
  const strongFundamentalsProxy = (coin.market_cap_rank ?? 999) <= 50;
 
  let dca = 0;
  if (farFromATH) dca += 40;
  if (lowVol) dca += 30;
  if (strongFundamentalsProxy) dca += 30;
  dca = clamp(dca);
 
  // Support / resistance / ATR for the recommendation engine -------------------
  const support = lows.length ? lows[lows.length - 1].v : Math.min(...series.slice(-30));
  const resistanceLvl = highs.length ? highs[highs.length - 1].v : Math.max(...series.slice(-30));
  const atr = atrProxy(series);
 
  return {
    price, emaShort, emaMid, emaLong, adxProxy, trendSlope,
    scores: { trend, smc, breakout, onchain, dca },
    flags: { bos, nearOrderBlock, dippedThenReclaimed, brokeOut, volumeSpike, strongClose, farFromATH, lowVol, strongFundamentalsProxy, walletGrowthProxy, outflowProxy, whaleAccumProxy, higherHighsLows },
    levels: { support, resistance: resistanceLvl, atr },
    volatility,
  };
}
 
function crossSectionStats(universe) {
  const volRatios = universe.map((c) => c.total_volume / Math.max(c.market_cap, 1));
  const vols = universe.map((c) => {
    const s = c._series;
    if (!s || s.length < 3) return 0;
    const returns = s.slice(1).map((v, i) => pct(v, s[i]));
    return stdev(returns);
  });
  const sorted = (a) => [...a].sort((x, y) => x - y);
  const median = (a) => { const s = sorted(a); return s[Math.floor(s.length / 2)] || 0; };
  return { volRatioMedian: median(volRatios) || 0.05, volatilityMedian: median(vols) || 1 };
}
 
function finalScoreFor(analysis, weights, btcBearish) {
  const s = analysis.scores;
  let raw =
    s.trend * weights.trend + s.smc * weights.smc + s.breakout * weights.breakout +
    s.onchain * weights.onchain + s.dca * weights.dca;
  if (btcBearish) raw *= 0.8; // market context filter
  const confidenceMultiplier = btcBearish ? 0.8 : 1.1;
  const confidence = clamp(raw * confidenceMultiplier, 0, 100);
  return { finalScore: clamp(raw), confidence };
}
 
function buildRecommendation(analysis) {
  const { support, resistance, atr } = analysis.levels;
  const entry = support;
  const stopLoss = support - atr * 1.5;
  const tp1 = resistance;
  const tp2 = resistance + atr * 2;
  return { entry, stopLoss, tp1, tp2 };
}
 
// deterministic, rule-based "AI explanation" — no external LLM key needed,
// generated straight from the real computed sub-scores/flags above.
function explain(coin, a, weights) {
  const s = a.scores;
  const top = Object.entries(s).sort((x, y) => y[1] - x[1])[0];
  const names = { trend: "trend strength", smc: "smart-money structure", breakout: "a breakout setup", onchain: "on-chain flow (proxy)", dca: "long-term value (DCA)" };
  const bits = [];
  if (a.flags.bos) bits.push("a break of structure to the upside");
  if (a.flags.dippedThenReclaimed) bits.push("a liquidity sweep that reversed back up");
  if (a.flags.brokeOut) bits.push("a close above recent resistance");
  if (a.flags.volumeSpike) bits.push("volume running well above its typical turnover");
  if (a.flags.farFromATH) bits.push("price sitting well below its all-time high");
  if (a.flags.higherHighsLows) bits.push("a sequence of higher highs and higher lows");
  const reasonList = bits.length ? bits.slice(0, 3).join(", ") : "mixed, non-committal signals across the five factors";
  return `${coin.symbol.toUpperCase()} is being led by ${names[top[0]]} (${top[1].toFixed(0)}/100). The engine flagged ${reasonList}. Weighting reflects the ${weights.label} profile you selected.`;
}
 
/* --------------------------------- UI bits -------------------------------- */
 
function Spark({ series, positive }) {
  if (!series || series.length < 2) return null;
  const w = 120, h = 36;
  const min = Math.min(...series), max = Math.max(...series);
  const range = max - min || 1;
  const pts = series
    .map((v, i) => `${(i / (series.length - 1)) * w},${h - ((v - min) / range) * h}`)
    .join(" ");
  return (
    <svg viewBox={`0 0 ${w} ${h}`} width={w} height={h} className="overflow-visible">
      <polyline points={pts} fill="none" stroke={positive ? "var(--gain)" : "var(--loss)"} strokeWidth="1.6" strokeLinejoin="round" strokeLinecap="round" />
    </svg>
  );
}
 
function ScoreBar({ label, value, weight }) {
  return (
    <div className="flex items-center gap-2 text-xs">
      <span className="w-20 shrink-0 text-[color:var(--text-muted)]">{label}</span>
      <div className="h-1.5 flex-1 rounded-full bg-[color:var(--surface-2)] overflow-hidden">
        <div className="h-full rounded-full" style={{ width: `${value}%`, background: "linear-gradient(90deg, var(--accent-dim), var(--accent))" }} />
      </div>
      <span className="w-8 text-right font-mono text-[color:var(--text-primary)]">{value.toFixed(0)}</span>
      <span className="w-9 text-right text-[10px] text-[color:var(--text-muted)]">×{weight}</span>
    </div>
  );
}
 
function ConfidenceGauge({ value }) {
  const r = 26, c = 2 * Math.PI * r;
  const offset = c - (clamp(value) / 100) * c;
  const color = value >= 70 ? "var(--gain)" : value >= 45 ? "var(--warn)" : "var(--loss)";
  return (
    <div className="relative flex h-16 w-16 items-center justify-center shrink-0">
      <svg width="64" height="64" className="-rotate-90">
        <circle cx="32" cy="32" r={r} fill="none" stroke="var(--surface-2)" strokeWidth="5" />
        <circle cx="32" cy="32" r={r} fill="none" stroke={color} strokeWidth="5" strokeLinecap="round"
          strokeDasharray={c} strokeDashoffset={offset} style={{ transition: "stroke-dashoffset .6s ease" }} />
      </svg>
      <span className="absolute font-mono text-sm font-semibold" style={{ color }}>{value.toFixed(0)}</span>
    </div>
  );
}
 
function fmt(n, d = 2) {
  if (n === null || n === undefined || Number.isNaN(n)) return "—";
  if (Math.abs(n) >= 1000) return n.toLocaleString(undefined, { maximumFractionDigits: 0 });
  if (Math.abs(n) < 1) return n.toLocaleString(undefined, { maximumFractionDigits: 6 });
  return n.toLocaleString(undefined, { maximumFractionDigits: d });
}
 
function CoinCard({ item, onSelect, active }) {
  const { coin, analysis, finalScore, confidence } = item;
  const positive = coin.price_change_percentage_24h >= 0;
  return (
    <button onClick={() => onSelect(item)}
      className={`text-left rounded-xl border p-4 transition-all hover:-translate-y-0.5 ${active ? "border-[color:var(--accent)]" : "border-[color:var(--border)]"}`}
      style={{ background: "var(--surface)" }}>
      <div className="flex items-start justify-between">
        <div className="flex items-center gap-2">
          <img src={coin.image} alt="" className="h-6 w-6 rounded-full" />
          <div>
            <div className="font-semibold text-sm">{coin.symbol.toUpperCase()}</div>
            <div className="text-[11px] text-[color:var(--text-muted)]">{coin.name}</div>
          </div>
        </div>
        <ConfidenceGauge value={confidence} />
      </div>
 
      <div className="mt-3 flex items-end justify-between">
        <div>
          <div className="font-mono text-lg leading-none">${fmt(coin.current_price)}</div>
          <div className="mt-1 font-mono text-xs" style={{ color: positive ? "var(--gain)" : "var(--loss)" }}>
            {positive ? "▲" : "▼"} {Math.abs(coin.price_change_percentage_24h).toFixed(2)}%
          </div>
        </div>
        <Spark series={coin._series?.slice(-48)} positive={positive} />
      </div>
 
      <div className="mt-3 space-y-1.5">
        <ScoreBar label="Trend" value={analysis.scores.trend} weight={item.weights.trend} />
        <ScoreBar label="SMC" value={analysis.scores.smc} weight={item.weights.smc} />
        <ScoreBar label="Breakout" value={analysis.scores.breakout} weight={item.weights.breakout} />
        <ScoreBar label="On-chain*" value={analysis.scores.onchain} weight={item.weights.onchain} />
        <ScoreBar label="DCA" value={analysis.scores.dca} weight={item.weights.dca} />
      </div>
 
      <div className="mt-3 flex items-center justify-between border-t border-[color:var(--border)] pt-2">
        <span className="text-[11px] text-[color:var(--text-muted)]">Final score</span>
        <span className="font-mono text-sm font-semibold" style={{ color: "var(--accent)" }}>{finalScore.toFixed(1)}</span>
      </div>
    </button>
  );
}
 
function DetailPanel({ item, weights }) {
  if (!item) return (
    <div className="rounded-xl border p-6 text-sm text-[color:var(--text-muted)]" style={{ borderColor: "var(--border)", background: "var(--surface)" }}>
      Select a coin from the list to see its full trade plan, levels, and reasoning.
    </div>
  );
  const { coin, analysis, rec, finalScore, confidence } = item;
  return (
    <div className="rounded-xl border p-5" style={{ borderColor: "var(--border)", background: "var(--surface)" }}>
      <div className="flex items-center gap-3">
        <img src={coin.image} alt="" className="h-9 w-9 rounded-full" />
        <div>
          <div className="text-base font-semibold">{coin.name} <span className="text-[color:var(--text-muted)]">({coin.symbol.toUpperCase()})</span></div>
          <div className="font-mono text-xs text-[color:var(--text-muted)]">Rank #{coin.market_cap_rank} · Vol/MCap {(coin.total_volume / coin.market_cap * 100).toFixed(1)}%</div>
        </div>
        <div className="ml-auto flex items-center gap-3">
          <div className="text-right">
            <div className="text-[10px] uppercase tracking-wide text-[color:var(--text-muted)]">Final score</div>
            <div className="font-mono text-lg" style={{ color: "var(--accent)" }}>{finalScore.toFixed(1)}</div>
          </div>
          <ConfidenceGauge value={confidence} />
        </div>
      </div>
 
      <p className="mt-4 text-sm leading-relaxed text-[color:var(--text-primary)]">{explain(coin, analysis, weights)}</p>
 
      <div className="mt-4 grid grid-cols-2 gap-3 sm:grid-cols-4">
        {[
          ["Entry (support/retest)", rec.entry],
          ["Stop loss", rec.stopLoss],
          ["Take profit 1 (resistance)", rec.tp1],
          ["Take profit 2 (ext.)", rec.tp2],
        ].map(([label, val]) => (
          <div key={label} className="rounded-lg p-3" style={{ background: "var(--surface-2)" }}>
            <div className="text-[10px] text-[color:var(--text-muted)]">{label}</div>
            <div className="font-mono text-sm">${fmt(val)}</div>
          </div>
        ))}
      </div>
 
      <div className="mt-4 grid grid-cols-2 gap-3 sm:grid-cols-5">
        {Object.entries(analysis.scores).map(([k, v]) => (
          <div key={k} className="rounded-lg p-2 text-center" style={{ background: "var(--surface-2)" }}>
            <div className="text-[10px] uppercase text-[color:var(--text-muted)]">{k === "onchain" ? "On-chain*" : k}</div>
            <div className="font-mono text-sm">{v.toFixed(0)}</div>
          </div>
        ))}
      </div>
      <div className="mt-2 text-[10px] text-[color:var(--text-muted)]">* On-chain factor is an estimated proxy from public market data — wire in Glassnode / Nansen / CryptoQuant for real wallet & flow data.</div>
    </div>
  );
}
 
function RiskCalculator({ item }) {
  const [capital, setCapital] = useState(1000);
  const [riskPct, setRiskPct] = useState(2);
  const rec = item?.rec;
  const riskAmount = capital * (riskPct / 100);
  const perUnitRisk = rec ? rec.entry - rec.stopLoss : 0;
  const positionSize = rec && perUnitRisk > 0 ? riskAmount / perUnitRisk : 0;
  const positionValue = positionSize * (rec?.entry ?? 0);
  const rr1 = rec && perUnitRisk > 0 ? (rec.tp1 - rec.entry) / perUnitRisk : 0;
  const rr2 = rec && perUnitRisk > 0 ? (rec.tp2 - rec.entry) / perUnitRisk : 0;
 
  return (
    <div className="rounded-xl border p-5" style={{ borderColor: "var(--border)", background: "var(--surface)" }}>
      <div className="mb-3 text-sm font-semibold">Position sizing</div>
      <div className="space-y-3">
        <label className="block text-xs text-[color:var(--text-muted)]">
          Capital (USD)
          <input type="number" value={capital} onChange={(e) => setCapital(Math.max(0, +e.target.value))}
            className="mt-1 w-full rounded-lg border bg-transparent px-3 py-2 font-mono text-sm outline-none"
            style={{ borderColor: "var(--border)" }} />
        </label>
        <label className="block text-xs text-[color:var(--text-muted)]">
          Risk per trade (%)
          <input type="number" value={riskPct} onChange={(e) => setRiskPct(Math.max(0.1, +e.target.value))}
            className="mt-1 w-full rounded-lg border bg-transparent px-3 py-2 font-mono text-sm outline-none"
            style={{ borderColor: "var(--border)" }} />
        </label>
      </div>
 
      {!rec ? (
        <div className="mt-4 text-xs text-[color:var(--text-muted)]">Select a coin to size a position against its entry / stop-loss.</div>
      ) : (
        <div className="mt-4 space-y-2 border-t pt-3 text-xs" style={{ borderColor: "var(--border)" }}>
          <div className="flex justify-between"><span className="text-[color:var(--text-muted)]">Risk amount</span><span className="font-mono">${fmt(riskAmount)}</span></div>
          <div className="flex justify-between"><span className="text-[color:var(--text-muted)]">Position size</span><span className="font-mono">{fmt(positionSize, 4)} units</span></div>
          <div className="flex justify-between"><span className="text-[color:var(--text-muted)]">Position value</span><span className="font-mono">${fmt(positionValue)}</span></div>
          <div className="flex justify-between"><span className="text-[color:var(--text-muted)]">R:R to TP1 / TP2</span><span className="font-mono">{rr1.toFixed(2)}R / {rr2.toFixed(2)}R</span></div>
        </div>
      )}
    </div>
  );
}
 
function MarketStrip({ btc, loading, lastUpdate, onRefresh }) {
  const bearish = btc?.bearish;
  return (
    <div className="flex flex-wrap items-center gap-3 rounded-xl border p-3 text-xs" style={{ borderColor: "var(--border)", background: "var(--surface)" }}>
      <span className="rounded-full px-2 py-1 font-medium" style={{ background: bearish ? "rgba(255,92,122,.12)" : "rgba(38,217,127,.12)", color: bearish ? "var(--loss)" : "var(--gain)" }}>
        BTC context: {bearish ? "Bearish · scores ×0.8" : "Bullish/Neutral · scores ×1.1 confidence"}
      </span>
      {btc && (
        <span className="font-mono text-[color:var(--text-muted)]">
          BTC ${fmt(btc.price)} · trend {btc.trend.toFixed(0)}/100
        </span>
      )}
      <span className="ml-auto text-[color:var(--text-muted)]">
        {loading ? "refreshing…" : lastUpdate ? `updated ${lastUpdate}` : ""}
      </span>
      <button onClick={onRefresh} className="rounded-lg border px-2 py-1 hover:bg-[color:var(--surface-2)]" style={{ borderColor: "var(--border)" }}>
        Refresh
      </button>
    </div>
  );
}
 
/* --------------------------------- main app -------------------------------- */
 
export default function CryptoIntel() {
  const [raw, setRaw] = useState([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState(null);
  const [lastUpdate, setLastUpdate] = useState(null);
  const [strategyId, setStrategyId] = useState("swing");
  const [selectedId, setSelectedId] = useState(null);
  const timerRef = useRef(null);
 
  const strategy = STRATEGIES.find((s) => s.id === strategyId);
 
  const fetchData = useCallback(async () => {
    try {
      setLoading(true);
      const res = await fetch(MARKETS_URL);
      if (!res.ok) throw new Error(`CoinGecko responded ${res.status}`);
      const data = await res.json();
      const withSeries = data
        .filter((c) => c.sparkline_in_7d?.price?.length > 30)
        .map((c) => ({ ...c, _series: c.sparkline_in_7d.price }));
      setRaw(withSeries);
      setError(null);
      setLastUpdate(new Date().toLocaleTimeString());
    } catch (e) {
      setError(e.message || "Failed to fetch market data");
    } finally {
      setLoading(false);
    }
  }, []);
 
  useEffect(() => {
    fetchData();
    timerRef.current = setInterval(fetchData, REFRESH_MS);
    return () => clearInterval(timerRef.current);
  }, [fetchData]);
 
  const universe = raw;
 
  const btcInfo = useMemo(() => {
    const btc = universe.find((c) => c.id === "bitcoin");
    if (!btc) return null;
    const cross = crossSectionStats(universe);
    const a = analyzeCoin(btc, btc._series, cross);
    if (!a) return null;
    const bearish = btc.current_price < a.emaMid && a.trendSlope < 0;
    return { price: btc.current_price, trend: a.scores.trend, bearish };
  }, [universe]);
 
  const analyzed = useMemo(() => {
    if (!universe.length) return [];
    const cross = crossSectionStats(universe);
    // Rank the universe by 24h performance (spec: "top 20 based on last 24h performance")
    const ranked = [...universe]
      .filter((c) => c.total_volume > 1_000_000) // liquidity floor to avoid noise/illiquid pumps
      .sort((a, b) => (b.price_change_percentage_24h ?? -999) - (a.price_change_percentage_24h ?? -999))
      .slice(0, 20);
 
    return ranked
      .map((coin) => {
        const analysis = analyzeCoin(coin, coin._series, cross);
        if (!analysis) return null;
        const { finalScore, confidence } = finalScoreFor(analysis, strategy.weights, !!btcInfo?.bearish);
        const rec = buildRecommendation(analysis);
        // Smart Coin Selection candidate score: momentum .4 + volume .3 + volatility .3
        const momentum = clamp(50 + (coin.price_change_percentage_24h ?? 0) * 2);
        const volumeRank = clamp((coin.total_volume / Math.max(coin.market_cap, 1)) * 400);
        const volatilityScore = clamp(100 - analysis.volatility * 8); // lower vol -> higher "quality" volatility score
        const candidateScore = momentum * 0.4 + volumeRank * 0.3 + volatilityScore * 0.3;
        return { coin, analysis, finalScore, confidence, rec, candidateScore, weights: strategy.weights };
      })
      .filter(Boolean)
      .sort((a, b) => b.finalScore - a.finalScore);
  }, [universe, strategy, btcInfo]);
 
  const top5 = useMemo(() => [...analyzed].sort((a, b) => b.candidateScore - a.candidateScore).slice(0, 5), [analyzed]);
  const selected = analyzed.find((i) => i.coin.id === selectedId) || null;
 
  return (
    <div className="min-h-screen w-full" style={{ background: "var(--bg)", color: "var(--text-primary)" }}>
      <style>{`
        :root {
          --bg: #0a0e14;
          --surface: #12161f;
          --surface-2: #1a1f2b;
          --border: #232936;
          --text-primary: #e8eaed;
          --text-muted: #7c8494;
          --accent: #7c6cf0;
          --accent-dim: #4a3f9c;
          --gain: #26d97f;
          --loss: #ff5c7a;
          --warn: #f5a623;
        }
        * { box-sizing: border-box; }
        body { -webkit-font-smoothing: antialiased; }
        input:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
        ::selection { background: var(--accent); color: white; }
      `}</style>
 
      <div className="mx-auto max-w-7xl p-4 sm:p-6">
        <header className="mb-5 flex flex-wrap items-center justify-between gap-3">
          <div>
            <h1 className="text-xl font-semibold tracking-tight">Crypto Trading Intelligence</h1>
            <p className="text-xs text-[color:var(--text-muted)]">Top 20 movers · multi-strategy scoring engine · live CoinGecko data</p>
          </div>
          <div className="flex rounded-xl border p-1" style={{ borderColor: "var(--border)" }}>
            {STRATEGIES.map((s) => (
              <button key={s.id} onClick={() => setStrategyId(s.id)}
                className="rounded-lg px-3 py-1.5 text-xs font-medium transition-colors"
                style={{ background: strategyId === s.id ? "var(--accent)" : "transparent", color: strategyId === s.id ? "white" : "var(--text-muted)" }}>
                {s.label}
              </button>
            ))}
          </div>
        </header>
 
        <div className="mb-5">
          <MarketStrip btc={btcInfo} loading={loading} lastUpdate={lastUpdate} onRefresh={fetchData} />
        </div>
 
        {error && (
          <div className="mb-5 rounded-xl border p-4 text-sm" style={{ borderColor: "var(--loss)", color: "var(--loss)", background: "rgba(255,92,122,.08)" }}>
            {error} — CoinGecko's free tier occasionally rate-limits; it will retry automatically on the next cycle.
          </div>
        )}
 
        {loading && !universe.length ? (
          <div className="grid grid-cols-1 gap-4 sm:grid-cols-2 lg:grid-cols-3">
            {Array.from({ length: 6 }).map((_, i) => (
              <div key={i} className="h-52 animate-pulse rounded-xl border" style={{ borderColor: "var(--border)", background: "var(--surface)" }} />
            ))}
          </div>
        ) : (
          <>
            <section className="mb-6">
              <h2 className="mb-2 text-sm font-semibold text-[color:var(--text-muted)]">Smart pick · top 5 ({strategy.label})</h2>
              <div className="grid grid-cols-1 gap-4 sm:grid-cols-2 lg:grid-cols-5">
                {top5.map((item) => (
                  <CoinCard key={item.coin.id} item={item} active={item.coin.id === selectedId} onSelect={(i) => setSelectedId(i.coin.id)} />
                ))}
              </div>
            </section>
 
            <section className="mb-6">
              <h2 className="mb-2 text-sm font-semibold text-[color:var(--text-muted)]">Top 20 by 24h performance</h2>
              <div className="grid grid-cols-1 gap-4 sm:grid-cols-2 lg:grid-cols-4">
                {analyzed.map((item) => (
                  <CoinCard key={item.coin.id} item={item} active={item.coin.id === selectedId} onSelect={(i) => setSelectedId(i.coin.id)} />
                ))}
              </div>
            </section>
 
            <section className="grid grid-cols-1 gap-4 lg:grid-cols-3">
              <div className="lg:col-span-2">
                <DetailPanel item={selected} weights={{ ...strategy.weights, label: strategy.label }} />
              </div>
              <RiskCalculator item={selected} />
            </section>
          </>
        )}
 
        <footer className="mt-8 text-[11px] leading-relaxed text-[color:var(--text-muted)]">
          Prices, volumes, market caps and 7-day series are live from CoinGecko. Trend/SMC/breakout/DCA scores are
          computed in-browser from that data; the on-chain factor is a disclosed estimate pending a paid data
          provider. This is a research/educational tool, not financial advice.
        </footer>
      </div>
    </div>
  );
}
