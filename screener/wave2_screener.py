#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""상승 2파 스크리너 — 정배열 상승 추세 속 '건전한 조정 → 재상승 준비' 종목 선별.

바닥 반전주·이미 급등한 추격주가 아니라, 이미 상승 추세가 검증된 종목 중에서
조정을 마치고 2파 상승을 준비하는 종목만 걸러낸다.

선별 기준 (일봉):
  1. 정배열        : 20일선 > 60일선 > 120일선, 20일선 상승 중
  2. 건전한 조정    : 최근 20일 고점 대비 -5% ~ -15%
  3. 거래량 감소    : 조정 구간(최근 5일) 평균 거래량 ≤ 직전 20일 평균의 80%
  4. 20일선 지지    : 종가가 20일선 -1.5% ~ +6% 구간에서 지지·회복
  5. RSI 과열 해소  : RSI(14) 45 ~ 60
  6. 반등 트리거    : 당일 양봉 또는 단기(5일) 고점 돌파 직전(-1.5% 이내)

출력 부류:
  ready    조정 완료·재상승 준비 — 기준 1~6 모두 충족
  ignited  재상승 당일 확인     — 정배열 + 고점 대비 -5% 이내 회복
                                + 당일 거래량 ≥ 20일 평균 + 고가권 마감 + RSI ≤ 65
  wait     아직 조정 중·대기    — 정배열이지만 일부 기준 미충족 (미충족 사유 표기)
  excluded 별도 분리            — 정배열 미충족(바닥 반전형), 신고가 돌파 추격형,
                                RSI 65 초과 과열, 고점 대비 -20% 초과(추세 훼손) 등

코어 로직은 표준 라이브러리만 사용한다. --csv 로 오프라인 데이터를 분석할 수 있고,
--live 실시간 스캔에만 pykrx(pip install pykrx)가 필요하다. 사용법은 README.md 참고.
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import dataclass

CFG = {
    "min_bars": 140,          # 120일선 + 여유 (신규 상장주 제외)
    "ma_short": 20,
    "ma_mid": 60,
    "ma_long": 120,
    "rsi_period": 14,
    "high_lookback": 20,      # 전고점 탐색 구간(거래일)
    "pullback_min": 0.05,     # 조정 깊이 하한 (5%)
    "pullback_max": 0.15,     # 조정 깊이 상한 (15%)
    "pullback_vol_days": 5,   # 조정 거래량 측정: 최근 5일
    "pullback_vol_base": 20,  # 그 이전 20일 평균 대비
    "vol_contract_max": 0.80, # 조정 거래량 ≤ 기준 평균의 80%
    "rsi_min": 45.0,
    "rsi_max": 60.0,
    "ma20_dist_min": -0.015,  # 종가의 20일선 이격 허용 범위
    "ma20_dist_max": 0.06,
    "confirm_near": 0.015,    # 단기 고점 돌파 '직전' 판정 (-1.5% 이내)
    "ignite_dd_max": 0.05,    # 시동형: 고점 대비 -5% 이내로 회복
    "ignite_vol_min": 1.0,    # 시동형: 당일 거래량 ≥ 20일 평균
    "ignite_range_pos": 0.6,  # 시동형: 당일 범위 상단 40% 이내 마감
    "chase_dd": 0.005,        # 고점 대비 -0.5% 이내 → 사실상 신고가(추격 구간)
    "overheat_rsi": 65.0,     # RSI 65 초과 → 과열 제외
    "trend_break_dd": 0.20,   # 고점 대비 -20% 초과 → 추세 훼손
}

TIER_LABEL = {
    "ready": "조정 완료·재상승 준비",
    "ignited": "재상승 당일 확인",
    "wait": "아직 조정 중·대기",
    "excluded": "별도 분리(바닥 반전형·돌파 추격형 등)",
}
TIER_GRADE = {
    "ready": "A급 재상승 준비형",
    "ignited": "A급 재상승 시동형",
    "wait": "조정 진행·대기",
}


@dataclass
class Bar:
    date: str
    open: float
    high: float
    low: float
    close: float
    volume: float


# ── 지표 ──────────────────────────────────────────────────────────────────────

def sma(vals, n):
    if len(vals) < n:
        return None
    return sum(vals[-n:]) / n


def rsi_wilder(closes, period=14):
    if len(closes) <= period:
        return None
    gains = losses = 0.0
    for i in range(1, period + 1):
        d = closes[i] - closes[i - 1]
        if d >= 0:
            gains += d
        else:
            losses -= d
    avg_gain, avg_loss = gains / period, losses / period
    for i in range(period + 1, len(closes)):
        d = closes[i] - closes[i - 1]
        avg_gain = (avg_gain * (period - 1) + (d if d > 0 else 0.0)) / period
        avg_loss = (avg_loss * (period - 1) + (-d if d < 0 else 0.0)) / period
    if avg_loss == 0:
        return 100.0
    return 100.0 - 100.0 / (1.0 + avg_gain / avg_loss)


def krx_tick(price):
    for limit, tick in ((2000, 1), (5000, 5), (20000, 10),
                        (50000, 50), (200000, 100), (500000, 500)):
        if price < limit:
            return tick
    return 1000


def to_tick(price):
    t = krx_tick(price)
    return int(round(price / t) * t)


def floor_grid(price):
    # 손절·경고 라인은 심리적 매물대 단위로 내림 (예: 169,214 → 169,000)
    g = 1000 if price >= 50000 else 100 if price >= 5000 else 10
    return int(price // g * g)


# ── 분석 ──────────────────────────────────────────────────────────────────────

def analyze(name, code, bars, cfg=CFG):
    """일봉 리스트(과거→현재)를 받아 지표·부류·대응 가격을 계산한다."""
    if len(bars) < cfg["min_bars"]:
        return None
    closes = [b.close for b in bars]
    highs = [b.high for b in bars]
    lows = [b.low for b in bars]
    vols = [b.volume for b in bars]
    last = bars[-1]
    close = last.close

    ma20 = sma(closes, cfg["ma_short"])
    ma60 = sma(closes, cfg["ma_mid"])
    ma120 = sma(closes, cfg["ma_long"])
    # 20일선 방향은 20일 전과 비교 — 건전한 조정 중의 단기 플랫은 허용
    ma20_prev = sma(closes[:-20], cfg["ma_short"])
    aligned = ma20 > ma60 > ma120
    ma20_rising = ma20_prev is not None and ma20 > ma20_prev
    rsi = rsi_wilder(closes, cfg["rsi_period"])
    ret60 = close / closes[-61] - 1

    # 조정 구간: 최근 20일 고점 → 그 이후 저점
    lb = cfg["high_lookback"]
    seg = highs[-lb:]
    pullback_high = max(seg)
    hi_off = seg.index(pullback_high)
    pullback_low = min(lows[len(lows) - lb + hi_off:])
    dd = close / pullback_high - 1

    nd, nb = cfg["pullback_vol_days"], cfg["pullback_vol_base"]
    vol_recent = sum(vols[-nd:]) / nd
    vol_base = sum(vols[-(nd + nb):-nd]) / nb
    contraction = vol_recent / vol_base if vol_base > 0 else 1.0
    avg20_prev = sum(vols[-21:-1]) / 20
    today_vol_ratio = vols[-1] / avg20_prev if avg20_prev > 0 else 1.0

    range_pos = ((close - last.low) / (last.high - last.low)
                 if last.high > last.low else 0.5)
    bullish = close > last.open
    dist20 = close / ma20 - 1
    confirm = max(highs[-5:])
    near_confirm = close >= confirm * (1 - cfg["confirm_near"])

    m = {
        "name": name, "code": code, "date": last.date,
        "close": close, "open": last.open, "high": last.high, "low": last.low,
        "ma20": ma20, "ma60": ma60, "ma120": ma120,
        "aligned": aligned, "ma20_rising": ma20_rising,
        "rsi": rsi, "ret60": ret60,
        "pullback_high": pullback_high, "pullback_low": pullback_low, "dd": dd,
        "contraction": contraction, "today_vol_ratio": today_vol_ratio,
        "range_pos": range_pos, "bullish": bullish,
        "dist20": dist20, "confirm": confirm, "near_confirm": near_confirm,
    }
    checks = checklist(m, cfg)
    tier, reasons = classify(m, checks, cfg)
    m["checklist"] = checks
    m["tier"] = tier
    m["reasons"] = reasons
    m["grade"] = TIER_GRADE.get(tier, "")
    m["score"] = ready_score(m, cfg) if tier in ("ready", "ignited") else 0.0
    m["levels"] = build_levels(m, tier, cfg)
    return m


def checklist(m, cfg):
    depth = -m["dd"]
    return [
        {"k": 1, "label": "정배열(20>60>120)·20일선 상승",
         "ok": m["aligned"] and m["ma20_rising"],
         "note": f"20일 {to_tick(m['ma20']):,} / 60일 {to_tick(m['ma60']):,} / 120일 {to_tick(m['ma120']):,}"},
        {"k": 2, "label": "고점 대비 5~15% 건전한 조정",
         "ok": cfg["pullback_min"] <= depth <= cfg["pullback_max"],
         "note": f"고점 {to_tick(m['pullback_high']):,} 대비 {m['dd']*100:+.1f}%"},
        {"k": 3, "label": "조정 거래량 감소(기준의 80% 이하)",
         "ok": m["contraction"] <= cfg["vol_contract_max"],
         "note": f"최근 5일 거래량 = 이전 20일 평균의 {m['contraction']*100:.0f}%"},
        {"k": 4, "label": "20일선 지지·회복",
         "ok": cfg["ma20_dist_min"] <= m["dist20"] <= cfg["ma20_dist_max"],
         "note": f"20일선 이격 {m['dist20']*100:+.1f}%"},
        {"k": 5, "label": "RSI 45~60 과열 해소",
         "ok": cfg["rsi_min"] <= m["rsi"] <= cfg["rsi_max"],
         "note": f"RSI {m['rsi']:.1f}"},
        {"k": 6, "label": "양봉 전환 또는 단기 고점 돌파 직전",
         "ok": m["bullish"] or m["near_confirm"],
         "note": f"{'양봉' if m['bullish'] else '음봉'}, 5일 고점 {to_tick(m['confirm']):,}"},
    ]


def classify(m, checks, cfg):
    if not (m["aligned"] and m["ma20_rising"]):
        return "excluded", ["정배열 미충족 — 바닥 반전형·역배열 분류"]
    if m["ret60"] <= 0:
        return "excluded", ["60거래일 수익률 마이너스 — 상승 추세 미검증"]
    depth = -m["dd"]
    if depth <= cfg["chase_dd"]:
        return "excluded", ["전고점 돌파 진행 중 — 눌림 매수형이 아닌 돌파 추격형"]
    if m["rsi"] > cfg["overheat_rsi"]:
        return "excluded", [f"RSI {m['rsi']:.1f} 과열 — 추격 위험 구간"]
    if depth > cfg["trend_break_dd"]:
        return "excluded", [f"고점 대비 {m['dd']*100:.1f}% — 조정 과다, 추세 훼손 점검 필요"]
    if (depth <= cfg["ignite_dd_max"]
            and m["today_vol_ratio"] >= cfg["ignite_vol_min"]
            and m["range_pos"] >= cfg["ignite_range_pos"]):
        return "ignited", [
            f"조정 마무리 후 당일 거래량 {m['today_vol_ratio']:.2f}배 증가, 고가권 유지 — 재상승 시동"]
    ok = {c["k"]: c["ok"] for c in checks}
    if ok[2] and ok[3] and ok[4] and ok[5] and ok[6]:
        return "ready", ["6개 기준 모두 충족 — 조정 완료·재상승 준비"]
    fails = []
    if not ok[2]:
        fails.append("조정 폭이 5~15% 범위 밖" if depth < cfg["pullback_min"]
                     else "조정 폭 15% 초과")
    if not ok[3]:
        fails.append(f"조정 거래량 미감소({m['contraction']*100:.0f}%)")
    if not ok[4]:
        fails.append(f"20일선 이격 {m['dist20']*100:+.1f}% — 지지권 밖")
    if not ok[5]:
        fails.append(f"RSI {m['rsi']:.1f} — 기준(45~60) 밖")
    if not ok[6]:
        fails.append("반등 트리거 부재(음봉·단기 고점과 거리)")
    if m["range_pos"] <= 0.3:
        fails.append("당일 저가권 마감")
    return "wait", fails or ["기준 재확인 필요"]


def ready_score(m, cfg):
    """READY 후보 정렬용 점수(0~100). 조정 깊이 10%, RSI 52.5, 20일선 +1% 부근이 이상적."""
    def clamp(x):
        return max(0.0, min(1.0, x))
    depth = -m["dd"]
    s_depth = clamp(1 - abs(depth - 0.10) / 0.05)
    s_vol = clamp((cfg["vol_contract_max"] - m["contraction"]) / 0.4)
    s_rsi = clamp(1 - abs(m["rsi"] - 52.5) / 7.5)
    s_sup = clamp(1 - abs(m["dist20"] - 0.01) / 0.05)
    return round(100 * (0.3 * s_depth + 0.3 * s_vol + 0.2 * s_rsi + 0.2 * s_sup), 1)


def build_levels(m, tier, cfg):
    """대응 가격: 목표·저항·확인·관심·경고·무효화 라인을 자동 산출한다."""
    depth = -m["dd"]
    levels = [{"type": "target", "label": "핵심 목표·전고점",
               "price": to_tick(m["pullback_high"])}]
    if depth >= cfg["ignite_dd_max"]:
        fib50 = m["pullback_low"] + 0.5 * (m["pullback_high"] - m["pullback_low"])
        levels.append({"type": "resist", "label": "1차 저항(되돌림 50%)",
                       "price": to_tick(fib50)})
    levels.append({"type": "confirm", "label": "재상승 확인(단기 고점 돌파)",
                   "price": to_tick(m["confirm"])})
    levels.append({"type": "current", "label": "현재가", "price": int(round(m["close"]))})
    if tier == "ignited":
        levels.append({"type": "interest", "label": "눌림 관심 구간",
                       "lo": to_tick(m["confirm"] * 0.970),
                       "hi": to_tick(m["confirm"] * 0.984)})
    else:
        # 눌림 매수 관심 구간은 항상 현재가 이하: 20일선 지지권과 현재가 사이
        hi = min(m["close"], m["ma20"] * 1.012)
        lo = max(m["pullback_low"], min(m["ma20"] * 0.996, hi * 0.985))
        if hi <= lo:
            lo = hi * 0.985
        levels.append({"type": "interest", "label": "관심 구간(20일선 지지권)",
                       "lo": to_tick(lo), "hi": to_tick(hi)})
    levels.append({"type": "warn", "label": "추세 경고(종가 이탈 주의)",
                   "price": floor_grid(m["pullback_low"])})
    if depth < cfg["ignite_dd_max"]:
        levels.append({"type": "invalid", "label": "추세 훼손(20일선 종가 이탈)",
                       "price": floor_grid(m["ma20"])})
    else:
        levels.append({"type": "invalid", "label": "상승 추세 무효화(60일선 이탈)",
                       "price": floor_grid(m["ma60"])})
    levels.sort(key=lambda x: x.get("price", x.get("hi", 0)), reverse=True)
    return levels


# ── 데이터 입력 ────────────────────────────────────────────────────────────────

CSV_ALIASES = {
    "date": "date", "날짜": "date", "일자": "date",
    "open": "open", "시가": "open",
    "high": "high", "고가": "high",
    "low": "low", "저가": "low",
    "close": "close", "종가": "close",
    "volume": "volume", "거래량": "volume",
}


def read_csv_bars(path):
    with open(path, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        cols = {}
        for raw in reader.fieldnames or []:
            key = CSV_ALIASES.get(raw.strip().lower(), CSV_ALIASES.get(raw.strip()))
            if key:
                cols[key] = raw
        missing = {"date", "open", "high", "low", "close", "volume"} - set(cols)
        if missing:
            sys.exit(f"CSV 컬럼 누락: {', '.join(sorted(missing))} "
                     f"(허용 헤더: 날짜/시가/고가/저가/종가/거래량 또는 영문)")
        bars = []
        for row in reader:
            try:
                bars.append(Bar(
                    date=row[cols["date"]].strip(),
                    open=float(str(row[cols["open"]]).replace(",", "")),
                    high=float(str(row[cols["high"]]).replace(",", "")),
                    low=float(str(row[cols["low"]]).replace(",", "")),
                    close=float(str(row[cols["close"]]).replace(",", "")),
                    volume=float(str(row[cols["volume"]]).replace(",", "")),
                ))
            except (ValueError, KeyError):
                continue
    bars.sort(key=lambda b: b.date)
    return bars


def fetch_live(top, date, cfg):
    """pykrx로 유동성(거래대금) 상위 top개 보통주를 스캔한다."""
    try:
        from pykrx import stock
    except ImportError:
        sys.exit("실시간 스캔에는 pykrx가 필요합니다: pip install pykrx")
    import datetime

    if not date:
        date = stock.get_nearest_business_day_in_a_week()
    snap = stock.get_market_ohlcv_by_ticker(date, market="ALL")
    snap = snap[snap["거래량"] > 0].sort_values("거래대금", ascending=False)

    picked = []
    for code in snap.index:
        if not code.endswith("0"):        # 우선주 제외(보통주 단축코드는 0으로 끝남)
            continue
        name = stock.get_market_ticker_name(code)
        if "스팩" in name:
            continue
        picked.append((code, name))
        if len(picked) >= top:
            break

    d = datetime.datetime.strptime(date, "%Y%m%d")
    frm = (d - datetime.timedelta(days=400)).strftime("%Y%m%d")
    results, scanned = [], 0
    for code, name in picked:
        scanned += 1
        try:
            df = stock.get_market_ohlcv(frm, date, code)
        except Exception as e:
            print(f"  ! {name}({code}) 조회 실패: {e}", file=sys.stderr)
            continue
        bars = [Bar(idx.strftime("%Y-%m-%d"), float(r["시가"]), float(r["고가"]),
                    float(r["저가"]), float(r["종가"]), float(r["거래량"]))
                for idx, r in df.iterrows() if r["거래량"] > 0 and r["시가"] > 0]
        a = analyze(name, code, bars, cfg)
        if a:
            results.append(a)
    asof = d.strftime("%Y-%m-%d")
    return results, asof, scanned


# ── 출력 ──────────────────────────────────────────────────────────────────────

def build_data(results, asof, scanned):
    tiers = {"ready": [], "ignited": [], "wait": [], "excluded": []}
    for a in results:
        tiers[a["tier"]].append(a)
    tiers["ready"].sort(key=lambda x: -x["score"])
    tiers["ignited"].sort(key=lambda x: -x["today_vol_ratio"])
    tiers["wait"].sort(key=lambda x: x["dd"])
    for i, a in enumerate(tiers["ready"], 1):
        a["rank"] = f"{i}순위"
    return {
        "asof": asof,
        "universe": {"scanned": scanned, "label": f"유동성 상위 상장주 {scanned}개"},
        "generated": True,
        "tiers": tiers,
    }


def fmt_levels_line(levels):
    parts = []
    for lv in levels:
        if lv["type"] == "current":
            continue
        if "price" in lv:
            parts.append(f"{lv['label']} {lv['price']:,}")
        else:
            parts.append(f"{lv['label']} {lv['lo']:,}~{lv['hi']:,}")
    return " / ".join(parts)


def print_report(data, max_excluded=10):
    u = data["universe"]
    print(f"\n■ 상승 2파 스크리너 — 기준일 {data['asof']} ({u['label']})")
    for tier in ("ready", "ignited", "wait", "excluded"):
        rows = data["tiers"][tier]
        print(f"\n[{TIER_LABEL[tier]}] {len(rows)}종목")
        if tier == "excluded":
            for a in rows[:max_excluded]:
                print(f"  - {a['name']}({a['code']}) {a['close']:,.0f}원 · {a['reasons'][0]}")
            if len(rows) > max_excluded:
                print(f"  … 외 {len(rows) - max_excluded}종목")
            continue
        for a in rows:
            head = (f"  {a.get('rank', '-')} {a['name']}({a['code']}) {a['close']:,.0f}원"
                    f" | 고점대비 {a['dd']*100:+.1f}% | RSI {a['rsi']:.1f}"
                    f" | 조정거래량 {a['contraction']*100:.0f}%"
                    f" | 당일거래량 {a['today_vol_ratio']:.2f}배"
                    f" | 60일 {a['ret60']*100:+.1f}%")
            if tier == "ready":
                head += f" | 점수 {a['score']:.1f}"
            print(head)
            if tier == "wait":
                print(f"      사유: {', '.join(a['reasons'])}")
            else:
                print(f"      {fmt_levels_line(a['levels'])}")
    print()


DATA_START = "/*WAVE2_DATA_START*/"
DATA_END = "/*WAVE2_DATA_END*/"


def update_html(path, data):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    payload = (DATA_START + "\nconst WAVE2_DATA = "
               + json.dumps(data, ensure_ascii=False, indent=2) + ";\n" + DATA_END)
    pattern = re.escape(DATA_START) + r".*?" + re.escape(DATA_END)
    new, cnt = re.subn(pattern, lambda _: payload, src, flags=re.S)
    if cnt != 1:
        sys.exit(f"{path}에서 WAVE2_DATA 마커를 찾지 못했습니다 (발견 {cnt}개)")
    with open(path, "w", encoding="utf-8") as f:
        f.write(new)
    print(f"HTML 데이터 갱신 완료: {path}")


def main(argv=None):
    p = argparse.ArgumentParser(description="상승 2파 스크리너 (자세한 기준은 파일 상단 docstring 참고)")
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--live", action="store_true", help="pykrx로 유동성 상위 종목 실시간 스캔")
    src.add_argument("--csv", metavar="FILE", help="일봉 CSV 1종목 분석 (날짜/시가/고가/저가/종가/거래량)")
    p.add_argument("--top", type=int, default=120, help="--live 스캔 종목 수 (기본 120)")
    p.add_argument("--date", help="--live 기준일 YYYYMMDD (기본: 최근 거래일)")
    p.add_argument("--name", default="종목", help="--csv 종목명")
    p.add_argument("--code", default="000000", help="--csv 종목코드")
    p.add_argument("--json", metavar="FILE", help="결과를 JSON으로 저장")
    p.add_argument("--update-html", metavar="FILE", help="wave2.html의 WAVE2_DATA 블록 갱신")
    args = p.parse_args(argv)

    if args.csv:
        bars = read_csv_bars(args.csv)
        a = analyze(args.name, args.code, bars)
        if a is None:
            sys.exit(f"데이터 부족: 일봉 {CFG['min_bars']}개 이상 필요 (현재 {len(bars)}개)")
        data = build_data([a], a["date"], 1)
    else:
        results, asof, scanned = fetch_live(args.top, args.date, CFG)
        data = build_data(results, asof, scanned)

    print_report(data)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        print(f"JSON 저장 완료: {args.json}")
    if args.update_html:
        update_html(args.update_html, data)
    return data


if __name__ == "__main__":
    main()
