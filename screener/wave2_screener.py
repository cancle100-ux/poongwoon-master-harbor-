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

시장 국면 게이트 (종목이 속한 지수 — KOSPI / KOSDAQ):
  우호  종가 > 20일선 > 60일선              → 판정 그대로
  위험  종가 < 60일선 이고 20일선 < 60일선    → 준비·시동 후보를 '대기'로 강등
  주의  그 외                              → 판정 유지, '비중 축소' 표기

출력 부류:
  ready    조정 완료·재상승 준비 — 기준 1~6 모두 충족
  ignited  재상승 당일 확인     — 정배열 + 고점 대비 -5% 이내 회복
                                + 당일 거래량 ≥ 20일 평균 + 고가권 마감 + RSI ≤ 65
  wait     아직 조정 중·대기    — 정배열이지만 일부 기준 미충족, 또는 시장 국면 위험
  excluded 별도 분리            — 정배열 미충족(바닥 반전형), 신고가 돌파 추격형,
                                RSI 65 초과 과열, 고점 대비 -20% 초과(추세 훼손) 등

백테스트 (--backtest):
  과거 구간을 하루씩 전진하며 그날까지의 데이터만으로 같은 판정을 재현하고,
  신호 → 진입(--entry) → 전고점 도달·추세 경고선 종가 이탈·보유 기간 만료 중 먼저 오는 조건으로 청산한다.
  시장 국면별 성과, 정배열 기준선 대비 신호 후 수익률, 조정 깊이 × RSI 범위 민감도(--sweep)를 출력한다.

데이터: 일봉·지수는 네이버 금융(수정주가, 로그인 불필요), 유동성 순위만 pykrx(KRX 로그인 필요).
코어 로직은 표준 라이브러리만 사용한다. 사용법은 README.md 참고.
"""
from __future__ import annotations

import argparse
import csv
import datetime
import json
import os
import re
import statistics
import sys
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter
from dataclasses import dataclass

CFG = {
    "min_bars": 140,          # 120일선 + 여유 (신규 상장주 제외)
    "window": 250,            # 판정에 쓰는 최근 일봉 수 (실시간 스캔·백테스트 공통)
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
    "regime_gate": True,      # 시장 국면 '위험'이면 준비·시동 후보를 대기로 강등
}

BT = {
    "entry": "open",          # open 다음날 시가 · zone 관심 구간 상단 지정가 · breakout 단기 고점 돌파
    "entry_wait": 5,          # zone·breakout 진입 대기 최대 거래일
    "hold": 20,               # 최대 보유 거래일
    "cost": 0.003,            # 왕복 거래비용 (세금·수수료·슬리피지 가정)
    "fwd": (5, 10, 20),       # 신호 후 N거래일 수익률
}
SWEEP_PULLBACK = ((0.03, 0.10), (0.05, 0.15), (0.08, 0.20))
SWEEP_RSI = ((40.0, 55.0), (45.0, 60.0), (50.0, 65.0))
WARMUP_DAYS = 400             # 판정 창(250봉) 확보용 달력 일수

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
REGIME_LABEL = {"favorable": "우호", "caution": "주의", "risk_off": "위험", "unknown": "미판정"}
ENTRY_LABEL = {
    "open": "신호 다음날 시가",
    "zone": "관심 구간 상단 지정가(최대 {wait}거래일 대기)",
    "breakout": "단기 고점 돌파 시 매수(최대 {wait}거래일 대기)",
}
EXIT_LABEL = {"target": "목표 도달", "stop": "손절", "time": "기간 만료"}
SKIP_LABEL = {
    "regime": "위험 국면 제외", "expired": "대기 만료", "invalidated": "진입 전 무효화",
    "gap_over_target": "시가가 목표가 이상", "gap_under_stop": "시가가 손절선 이하",
    "data_end": "데이터 종료", "open_position": "미청산",
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

def compute_metrics(name, code, bars, cfg=CFG):
    """최근 window개 일봉(과거→현재)으로 판정용 지표를 계산한다. 데이터 부족 시 None."""
    bars = bars[-cfg["window"]:]
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

    return {
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


def criteria(m, cfg=CFG):
    """선별 기준 1~6의 충족 여부 {번호: bool}."""
    depth = -m["dd"]
    return {
        1: m["aligned"] and m["ma20_rising"],
        2: cfg["pullback_min"] <= depth <= cfg["pullback_max"],
        3: m["contraction"] <= cfg["vol_contract_max"],
        4: cfg["ma20_dist_min"] <= m["dist20"] <= cfg["ma20_dist_max"],
        5: cfg["rsi_min"] <= m["rsi"] <= cfg["rsi_max"],
        6: m["bullish"] or m["near_confirm"],
    }


def checklist(m, cfg=CFG, ok=None):
    if ok is None:
        ok = criteria(m, cfg)
    labels = {
        1: "정배열(20>60>120)·20일선 상승",
        2: f"고점 대비 {cfg['pullback_min']*100:.0f}~{cfg['pullback_max']*100:.0f}% 건전한 조정",
        3: f"조정 거래량 감소(기준의 {cfg['vol_contract_max']*100:.0f}% 이하)",
        4: "20일선 지지·회복",
        5: f"RSI {cfg['rsi_min']:.0f}~{cfg['rsi_max']:.0f} 과열 해소",
        6: "양봉 전환 또는 단기 고점 돌파 직전",
    }
    notes = {
        1: f"20일 {to_tick(m['ma20']):,} / 60일 {to_tick(m['ma60']):,} / 120일 {to_tick(m['ma120']):,}",
        2: f"고점 {to_tick(m['pullback_high']):,} 대비 {m['dd']*100:+.1f}%",
        3: f"최근 5일 거래량 = 이전 20일 평균의 {m['contraction']*100:.0f}%",
        4: f"20일선 이격 {m['dist20']*100:+.1f}%",
        5: f"RSI {m['rsi']:.1f}",
        6: f"{'양봉' if m['bullish'] else '음봉'}, 5일 고점 {to_tick(m['confirm']):,}",
    }
    return [{"k": k, "label": labels[k], "ok": ok[k], "note": notes[k]} for k in range(1, 7)]


def classify(m, ok, cfg=CFG):
    if not ok[1]:
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
    if ok[2] and ok[3] and ok[4] and ok[5] and ok[6]:
        return "ready", ["6개 기준 모두 충족 — 조정 완료·재상승 준비"]
    fails = []
    if not ok[2]:
        fails.append(f"조정 폭 {depth*100:.1f}% — {cfg['pullback_min']*100:.0f}% 미만(조정 얕음)"
                     if depth < cfg["pullback_min"]
                     else f"조정 폭 {depth*100:.1f}% — {cfg['pullback_max']*100:.0f}% 초과")
    if not ok[3]:
        fails.append(f"조정 거래량 미감소({m['contraction']*100:.0f}%)")
    if not ok[4]:
        fails.append(f"20일선 이격 {m['dist20']*100:+.1f}% — 지지권 밖")
    if not ok[5]:
        fails.append(f"RSI {m['rsi']:.1f} — 기준({cfg['rsi_min']:.0f}~{cfg['rsi_max']:.0f}) 밖")
    if not ok[6]:
        fails.append("반등 트리거 부재(음봉·단기 고점과 거리)")
    if m["range_pos"] <= 0.3:
        fails.append("당일 저가권 마감")
    return "wait", fails or ["기준 재확인 필요"]


def ready_score(m, cfg=CFG):
    """READY 후보 정렬용 점수(0~100). 조정 깊이 10%, RSI 52.5, 20일선 +1% 부근이 이상적."""
    def clamp(x):
        return max(0.0, min(1.0, x))
    depth = -m["dd"]
    s_depth = clamp(1 - abs(depth - 0.10) / 0.05)
    s_vol = clamp((cfg["vol_contract_max"] - m["contraction"]) / 0.4)
    s_rsi = clamp(1 - abs(m["rsi"] - 52.5) / 7.5)
    s_sup = clamp(1 - abs(m["dist20"] - 0.01) / 0.05)
    return round(100 * (0.3 * s_depth + 0.3 * s_vol + 0.2 * s_rsi + 0.2 * s_sup), 1)


def build_levels(m, tier, cfg=CFG):
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


def evaluate(m, cfg=CFG, regime=None):
    """지표에 기준·시장 국면 게이트를 적용해 부류·사유·체크리스트·대응 가격을 붙인다."""
    ok = criteria(m, cfg)
    raw_tier, reasons = classify(m, ok, cfg)
    tier, reasons = apply_regime(raw_tier, reasons, regime, cfg)
    a = dict(m)
    a.update({
        "checklist": checklist(m, cfg, ok),
        "tier": tier,
        "raw_tier": raw_tier,
        "reasons": reasons,
        "regime": regime["state"] if regime else "unknown",
        "grade": "시장 국면 대기" if tier != raw_tier else TIER_GRADE.get(tier, ""),
        "score": ready_score(m, cfg) if raw_tier in ("ready", "ignited") else 0.0,
        "levels": build_levels(m, raw_tier, cfg),
    })
    return a


def analyze(name, code, bars, cfg=CFG, regime=None):
    """일봉 리스트(과거→현재)를 받아 지표·부류·대응 가격을 계산한다."""
    m = compute_metrics(name, code, bars, cfg)
    return evaluate(m, cfg, regime) if m else None


# ── 시장 국면 ─────────────────────────────────────────────────────────────────

def market_regime(name, bars, cfg=CFG):
    """지수 일봉으로 시장 국면을 판정한다: 우호 / 주의 / 위험 / 미판정."""
    closes = [b.close for b in bars]
    if len(closes) < cfg["ma_mid"]:
        return {"name": name, "state": "unknown", "label": REGIME_LABEL["unknown"],
                "note": "지수 데이터 부족"}
    c = closes[-1]
    ma20, ma60 = sma(closes, cfg["ma_short"]), sma(closes, cfg["ma_mid"])
    if c > ma20 > ma60:
        state, note = "favorable", "종가 > 20일선 > 60일선"
    elif c < ma60 and ma20 < ma60:
        state, note = "risk_off", "종가·20일선 모두 60일선 아래"
    elif c <= ma20:
        state, note = "caution", "종가가 20일선 아래 — 단기 조정"
    else:
        state, note = "caution", "20일선이 60일선 아래 — 추세 미확인"
    return {"name": name, "date": bars[-1].date, "state": state,
            "label": REGIME_LABEL[state], "note": note, "close": c,
            "ma20": ma20, "ma60": ma60, "ma120": sma(closes, cfg["ma_long"])}


def regime_series(name, bars, cfg=CFG):
    """거래일마다 그날까지의 지수 데이터만으로 국면을 판정한다 (백테스트용, {날짜: 국면})."""
    n = cfg["ma_mid"]
    return {b.date: market_regime(name, bars[max(0, i + 1 - n):i + 1], cfg)["state"]
            for i, b in enumerate(bars)}


def apply_regime(tier, reasons, regime, cfg=CFG):
    """시장 국면 게이트: 위험 국면은 준비·시동 후보를 대기로 강등, 주의 국면은 비중 축소 표기."""
    if not regime or not cfg.get("regime_gate", True) or tier not in ("ready", "ignited"):
        return tier, reasons
    if regime["state"] == "risk_off":
        return "wait", [f"시장 국면 위험({regime['name']}: {regime['note']}) — 신규 진입 보류"] + reasons
    if regime["state"] == "caution":
        return tier, reasons + [f"시장 국면 주의({regime['name']}: {regime['note']}) — 비중 축소"]
    return tier, reasons


# ── 백테스트 ──────────────────────────────────────────────────────────────────

def stock_metrics(name, code, bars, cfg=CFG, start=None, end=None):
    """거래일마다 그날까지의 일봉(최근 window개)만으로 지표를 계산한다 — 미래 데이터 미사용."""
    w = cfg["window"]
    out = [None] * len(bars)
    for t in range(cfg["min_bars"] - 1, len(bars)):
        d = bars[t].date
        if (start and d < start) or (end and d > end):
            continue
        out[t] = compute_metrics(name, code, bars[max(0, t + 1 - w):t + 1], cfg)
    return out


def plan_levels(m, tier, cfg=CFG):
    """신호일 대응 가격표에서 목표(전고점)·손절(추세 경고선)·돌파 확인선·관심 구간 상단을 꺼낸다."""
    lv = {x["type"]: x for x in build_levels(m, tier, cfg)}
    return {"target": lv["target"]["price"], "stop": lv["warn"]["price"],
            "confirm": lv["confirm"]["price"], "zone_hi": lv["interest"]["hi"]}


def find_entry(bars, t, plan, mode, wait):
    """신호일 t 다음 거래일부터 진입을 찾는다. 반환: ((진입일 인덱스, 진입가), None) 또는 (None, 사유)."""
    n = len(bars)
    if t + 1 >= n:
        return None, "data_end"
    stop, target = plan["stop"], plan["target"]
    if mode == "open":
        px = bars[t + 1].open
        if px >= target:
            return None, "gap_over_target"
        if px <= stop:
            return None, "gap_under_stop"
        return (t + 1, px), None
    trigger = plan["confirm"] + krx_tick(plan["confirm"])   # 단기 고점 '돌파' = 한 호가 위
    for j in range(t + 1, min(n, t + 1 + wait)):
        b = bars[j]
        if mode == "breakout" and b.high >= trigger:
            px = max(b.open, trigger)
            return ((j, px), None) if px < target else (None, "gap_over_target")
        if mode == "zone" and b.low <= plan["zone_hi"]:
            px = min(b.open, plan["zone_hi"])
            return ((j, px), None) if px > stop else (None, "gap_under_stop")
        if b.close < stop:
            return None, "invalidated"
    return None, ("expired" if t + wait < n else "data_end")


def run_exit(bars, ei, plan, hold, target_same_day=True):
    """진입 후 청산: 장중 목표가(전고점) 도달 → 목표가 체결, 종가가 손절선 아래 → 종가 청산,
    hold 거래일 경과 → 종가 청산. 같은 날 둘 다면 목표가 우선. 데이터가 먼저 끝나면 None(미청산)."""
    stop, target = plan["stop"], plan["target"]
    end = ei + hold
    for j in range(ei, min(end, len(bars))):
        b = bars[j]
        if b.high >= target and (j > ei or target_same_day):
            return j, (max(b.open, target) if j > ei else target), "target"
        if b.close < stop:
            return j, b.close, "stop"
    if end <= len(bars):
        return end - 1, bars[end - 1].close, "time"
    return None


def simulate_stock(name, code, bars, metrics, cfg, regimes, opts, gate=True,
                   tiers=("ready", "ignited")):
    """한 종목의 신호를 시간 순서대로 거래로 바꾼다. 보유 중에는 새 신호를 받지 않는다."""
    trades, skipped = [], Counter()
    # 관심 구간 지정가는 장중 하락 후 체결되므로 진입일의 목표가 도달은 인정하지 않는다
    target_same_day = opts["entry"] != "zone"
    t, n = 0, len(bars)
    while t < n:
        m = metrics[t]
        if m is None:
            t += 1
            continue
        tier, _ = classify(m, criteria(m, cfg), cfg)
        if tier not in tiers:
            t += 1
            continue
        regime = regimes.get(bars[t].date, "unknown")
        if gate and cfg.get("regime_gate", True) and regime == "risk_off":
            skipped["regime"] += 1
            t += 1
            continue
        plan = plan_levels(m, tier, cfg)
        entry, why = find_entry(bars, t, plan, opts["entry"], opts["entry_wait"])
        if entry is None:
            skipped[why] += 1
            if why == "data_end":
                break
            t += 1
            continue
        ei, px = entry
        ex = run_exit(bars, ei, plan, opts["hold"], target_same_day)
        if ex is None:
            skipped["open_position"] += 1
            break
        xi, xpx, reason = ex
        trades.append({
            "name": name, "code": code, "tier": tier, "regime": regime,
            "signal_date": bars[t].date, "entry_date": bars[ei].date, "exit_date": bars[xi].date,
            "entry": px, "exit": xpx, "stop": plan["stop"], "target": plan["target"],
            "reason": reason, "hold": xi - ei + 1, "ret": xpx / px - 1 - opts["cost"],
        })
        t = xi + 1
    return trades, skipped


def forward_returns(bars, t, days):
    """신호일 t 다음날 시가에 사서 N거래일째(t+N) 종가까지의 수익률."""
    if t + 1 >= len(bars) or bars[t + 1].open <= 0:
        return None
    base = bars[t + 1].open
    return {d: (bars[t + d].close / base - 1 if t + d < len(bars) else None) for d in days}


def run_backtest(universe, regimes_by_market, opts, cfg=CFG, start=None, end=None, sweep=False):
    """universe: [(이름, 코드, 시장, 일봉)], regimes_by_market: {시장: {날짜: 국면}}."""
    grid = [((pb, rs), dict(cfg, pullback_min=pb[0], pullback_max=pb[1],
                            rsi_min=rs[0], rsi_max=rs[1]))
            for pb in SWEEP_PULLBACK for rs in SWEEP_RSI] if sweep else []
    res = {"all": [], "gated": [], "skip_all": Counter(), "skip_gated": Counter(),
           "onset": [], "baseline": [], "sweep": {key: [] for key, _ in grid},
           "first": None, "last": None}
    for i, (name, code, market, bars) in enumerate(universe, 1):
        _progress(f"백테스트 {i}/{len(universe)} {name}")
        metrics = stock_metrics(name, code, bars, cfg, start, end)
        regimes = regimes_by_market.get(market, {})
        for gate, key in ((False, "all"), (True, "gated")):
            trades, skipped = simulate_stock(name, code, bars, metrics, cfg, regimes, opts, gate)
            res[key] += trades
            res["skip_" + key] += skipped
        # 이벤트 분석: 신호 첫날 vs 정배열 상승 추세 전체일의 신호 후 수익률
        prev = False
        for t, m in enumerate(metrics):
            if m is None:
                prev = False
                continue
            d = bars[t].date
            res["first"] = d if res["first"] is None or d < res["first"] else res["first"]
            res["last"] = d if res["last"] is None or d > res["last"] else res["last"]
            tier, _ = classify(m, criteria(m, cfg), cfg)
            sig = tier in ("ready", "ignited")
            fr = forward_returns(bars, t, opts["fwd"])
            if fr and sig and not prev:
                res["onset"].append(fr)
            if fr and m["aligned"] and m["ma20_rising"] and m["ret60"] > 0:
                res["baseline"].append(fr)
            prev = sig
        for key, gcfg in grid:
            trades, _ = simulate_stock(name, code, bars, metrics, gcfg, regimes, opts,
                                       gate=True, tiers=("ready",))
            res["sweep"][key] += trades
    print(file=sys.stderr)
    return res


def trade_stats(trades):
    n = len(trades)
    if not n:
        return {"n": 0}
    rets = [x["ret"] for x in trades]
    wins = [r for r in rets if r > 0]
    losses = [-r for r in rets if r <= 0]
    avg_win = sum(wins) / len(wins) if wins else 0.0
    avg_loss = sum(losses) / len(losses) if losses else 0.0
    return {
        "n": n,
        "win": len(wins) / n,
        "avg": sum(rets) / n,
        "median": statistics.median(rets),
        "payoff": avg_win / avg_loss if avg_loss > 0 else None,
        "pf": sum(wins) / sum(losses) if sum(losses) > 0 else None,
        "hold": sum(x["hold"] for x in trades) / n,
        "exits": dict(Counter(x["reason"] for x in trades)),
    }


def fwd_stats(rows, days):
    out = {}
    for d in days:
        vals = [r[d] for r in rows if r.get(d) is not None]
        out[str(d)] = ({"n": len(vals), "avg": sum(vals) / len(vals),
                        "median": statistics.median(vals),
                        "win": sum(v > 0 for v in vals) / len(vals)} if vals else {"n": 0})
    return out


def summarize_backtest(res, opts, cfg, ctx):
    gated = res["gated"]
    return {
        "mode": "backtest",
        "period": f"{res['first']} ~ {res['last']}" if res["first"] else "—",
        "universe": ctx["label"],
        "stocks": len(ctx["universe"]),
        "bias_note": ctx.get("bias_note"),
        "regime_source": sorted(ctx["index"]),
        "regime_gate": cfg.get("regime_gate", True),
        "criteria": {"pullback": [cfg["pullback_min"], cfg["pullback_max"]],
                     "rsi": [cfg["rsi_min"], cfg["rsi_max"]]},
        "opts": {"entry": opts["entry"],
                 "entry_label": ENTRY_LABEL[opts["entry"]].format(wait=opts["entry_wait"]),
                 "entry_wait": opts["entry_wait"], "hold": opts["hold"], "cost": opts["cost"],
                 "fwd": list(opts["fwd"])},
        "stats": {
            "all": trade_stats(res["all"]),
            "gated": trade_stats(gated),
            "by_tier": {k: trade_stats([x for x in gated if x["tier"] == k])
                        for k in ("ready", "ignited")},
            "by_regime": {k: trade_stats([x for x in res["all"] if x["regime"] == k])
                          for k in REGIME_LABEL},
        },
        "skipped": {"all": dict(res["skip_all"]), "gated": dict(res["skip_gated"])},
        "event": {"onset": fwd_stats(res["onset"], opts["fwd"]),
                  "baseline": fwd_stats(res["baseline"], opts["fwd"])},
        "sweep": [{"pullback": list(pb), "rsi": list(rs), **trade_stats(trades)}
                  for (pb, rs), trades in res["sweep"].items()],
        "trades": gated,
    }


# ── 데이터 입력 ────────────────────────────────────────────────────────────────

CSV_ALIASES = {
    "date": "date", "날짜": "date", "일자": "date",
    "open": "open", "시가": "open",
    "high": "high", "고가": "high",
    "low": "low", "저가": "low",
    "close": "close", "종가": "close",
    "volume": "volume", "거래량": "volume",
}


def norm_date(s):
    """20260807 · 2026.08.07 · 2026-08-07 00:00:00 → 2026-08-07 (그 외 형식은 그대로)."""
    s = str(s).strip()
    m = re.match(r"^(\d{4})[-./]?(\d{2})[-./]?(\d{2})", s)
    return f"{m.group(1)}-{m.group(2)}-{m.group(3)}" if m else s


def parse_day(s):
    try:
        return datetime.date.fromisoformat(norm_date(s))
    except ValueError:
        sys.exit(f"날짜 형식 오류: {s} (YYYYMMDD)")


def read_csv_bars(path):
    if not os.path.isfile(path):
        sys.exit(f"CSV 파일을 찾을 수 없습니다: {path}")
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
                    date=norm_date(row[cols["date"]]),
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


def csv_identity(path):
    """파일명 '105560_KB금융.csv' → ('KB금융', '105560'). 형식이 다르면 (파일명, '000000')."""
    stem = os.path.splitext(os.path.basename(path))[0]
    m = re.match(r"^(\d[0-9A-Z]{5})(?:[_\-\s]+(.+))?$", stem)
    if m:
        return (m.group(2) or m.group(1)), m.group(1)
    return stem, "000000"


NAVER_CHART = "fchart.stock.naver.com/sise.nhn"


def _decode_xml(raw):
    m = re.search(rb'encoding=["\']([\w\-]+)', raw[:200])
    enc = m.group(1).decode("ascii").lower() if m else "utf-8"
    if enc.replace("-", "").replace("_", "") in ("euckr", "ksc56011987"):
        enc = "cp949"
    try:
        return raw.decode(enc, errors="replace")
    except LookupError:
        return raw.decode("utf-8", errors="replace")


def parse_naver_chart(text, require_volume=True):
    """네이버 차트 XML → (종목명, [Bar]). 거래 없는 날(거래정지 등)은 require_volume이면 제외."""
    root = ET.fromstring(text)
    chart = root.find(".//chartdata")
    name = chart.get("name") if chart is not None else None
    bars = []
    for item in root.iter("item"):
        parts = (item.get("data") or "").split("|")
        if len(parts) < 6:
            continue
        try:
            o, h, lo, c, v = (float(x) for x in parts[1:6])
        except ValueError:
            continue
        if c <= 0 or (require_volume and (v <= 0 or o <= 0)):
            continue
        bars.append(Bar(norm_date(parts[0]), o, h, lo, c, v))
    bars.sort(key=lambda b: b.date)
    return name, bars


def naver_daily(symbol, count, require_volume=True):
    """네이버 금융 일봉(수정주가). symbol: 종목코드 또는 KOSPI·KOSDAQ. 로그인 불필요."""
    query = urllib.parse.urlencode({"symbol": symbol, "timeframe": "day",
                                    "count": max(1, int(count)), "requestType": 0})
    last = None
    for scheme in ("https", "http"):
        req = urllib.request.Request(f"{scheme}://{NAVER_CHART}?{query}",
                                     headers={"User-Agent": "Mozilla/5.0"})
        try:
            with urllib.request.urlopen(req, timeout=20) as r:
                return parse_naver_chart(_decode_xml(r.read()), require_volume)
        except (OSError, ET.ParseError) as e:
            last = e
    raise RuntimeError(f"네이버 일봉 조회 실패({symbol}): {last}")


KRX_LOGIN_HELP = (
    "유동성 순위 조회는 pykrx로 KRX 정보데이터시스템에 로그인해야 합니다.\n"
    "  1) data.krx.co.kr 회원가입  2) 환경변수 KRX_ID·KRX_PW 설정  3) pip install pykrx\n"
    "  또는 --tickers 105560,055550,214450.KQ 처럼 종목을 직접 지정하면 로그인 없이 실행됩니다.")


def require_krx_login():
    if not (os.getenv("KRX_ID") and os.getenv("KRX_PW")):
        sys.exit(KRX_LOGIN_HELP)


def krx_ranked(date_ymd):
    """KRX 전종목 시세의 거래대금 순위 [(코드, 시장)] — KOSPI·KOSDAQ 보통주."""
    require_krx_login()
    try:
        from pykrx import stock
    except ImportError:
        sys.exit("pykrx가 필요합니다: pip install pykrx\n" + KRX_LOGIN_HELP)
    rows = []
    try:
        for mkt in ("KOSPI", "KOSDAQ"):
            df = stock.get_market_ohlcv_by_ticker(date_ymd, market=mkt)
            for code, r in df.iterrows():
                code = str(code)
                if code.endswith("0") and r["거래량"] > 0:   # 우선주 제외(보통주 코드는 0으로 끝남)
                    rows.append((float(r["거래대금"]), code, mkt))
    except Exception as e:
        sys.exit(f"KRX 시세 조회 실패: {e}\n" + KRX_LOGIN_HELP)
    if not rows:
        sys.exit(f"{date_ymd} KRX 시세가 비어 있습니다 — 휴장일이거나 KRX 로그인에 실패했습니다.")
    rows.sort(reverse=True)
    return [(code, mkt) for _, code, mkt in rows]


def parse_tickers(s):
    """'105560,055550,214450.KQ' → [(코드, 시장)]. 접미사 .KQ는 KOSDAQ, 없거나 .KS면 KOSPI."""
    out = []
    for tok in re.split(r"[,\s]+", s.strip()):
        if tok:
            code, _, suffix = tok.upper().partition(".")
            out.append((code, "KOSDAQ" if suffix == "KQ" else "KOSPI"))
    return out


def _progress(msg):
    print(f"\r  {msg:<40}", end="", file=sys.stderr, flush=True)


def load_live(cands, count, end, top, need, asof=None):
    """후보 [(코드, 시장)]를 순서대로 조회해 스팩·데이터 부족·거래정지를 빼고 top개를 모은다."""
    out, total = [], min(top, len(cands))
    for code, mkt in cands:
        if len(out) >= top:
            break
        try:
            name, bars = naver_daily(code, count)
        except RuntimeError as e:
            print(f"\n  ! {e}", file=sys.stderr)
            continue
        name = name or code
        bars = [b for b in bars if b.date <= end]
        if "스팩" in name:
            continue
        if len(bars) < need or (asof and bars[-1].date != asof):
            print(f"\n  ! {name}({code}) 제외 — 일봉 {len(bars)}개"
                  f"{'' if not bars else ', 마지막 거래일 ' + bars[-1].date}", file=sys.stderr)
            continue
        out.append((name, code, mkt, bars))
        _progress(f"시세 조회 {len(out)}/{total}")
    print(file=sys.stderr)
    return out


def live_context(args, cfg):
    if not args.tickers:
        require_krx_login()   # 네트워크 조회 전에 먼저 확인
    today = datetime.date.today()
    end_d = min(parse_day(args.date), today) if args.date else today
    if args.backtest:
        start_d = (parse_day(args.start) if args.start
                   else end_d - datetime.timedelta(days=round(365.25 * args.years)))
    else:
        start_d = end_d
    count = (today - start_d).days + WARMUP_DAYS
    end = end_d.isoformat()
    index = {}
    for mkt in ("KOSPI", "KOSDAQ"):
        try:
            _, bars = naver_daily(mkt, count, require_volume=False)
            index[mkt] = [b for b in bars if b.date <= end]
        except RuntimeError as e:
            print(f"  ! {e} — {mkt} 시장 국면 미판정", file=sys.stderr)
    calendar = [b.date for b in index.get("KOSPI", [])]
    if not calendar:   # 지수 조회 실패 시 대형주 거래일로 대체
        try:
            calendar = [b.date for b in naver_daily("005930", count)[1] if b.date <= end]
        except RuntimeError as e:
            sys.exit(f"거래일 확인 실패: {e}")
    asof = calendar[-1]
    start = next((d for d in calendar if d >= start_d.isoformat()), asof)
    if args.tickers:
        cands, top = parse_tickers(args.tickers), None
        bias = "지정 종목 백테스트는 종목 선택 자체에 사후 편향이 섞일 수 있습니다"
    else:
        cands, top = krx_ranked((start if args.backtest else asof).replace("-", "")), args.top
        bias = ("유니버스는 시작일 기준 유동성 상위로 선정(생존 편향 완화) — "
                "이후 상장폐지돼 시세가 없는 종목은 빠집니다")
    universe = load_live(cands, count, end, top or len(cands), cfg["min_bars"],
                         None if args.backtest else asof)
    if args.tickers:
        label = f"지정 종목 {len(universe)}개"
    elif args.backtest:
        label = f"유동성 상위 {len(universe)}종목({start} 기준)"
    else:
        label = f"유동성 상위 상장주 {len(universe)}개"
    return {"universe": universe, "index": index, "asof": asof,
            "start": start if args.backtest else None, "label": label, "bias_note": bias}


def csv_context(args, cfg):
    end = norm_date(args.date) if args.date else None
    market = args.index_name if args.index_csv else ""
    universe = []
    for path in args.csv:
        name, code = csv_identity(path)
        if len(args.csv) == 1:
            name, code = args.name or name, args.code or code
        bars = [b for b in read_csv_bars(path) if not end or b.date <= end]
        universe.append((name, code, market, bars))
    index = {}
    if args.index_csv:
        index[market] = [b for b in read_csv_bars(args.index_csv) if not end or b.date <= end]
    dates = [bars[-1].date for *_, bars in universe if bars]
    return {"universe": universe, "index": index, "asof": max(dates) if dates else (end or "—"),
            "start": norm_date(args.start) if args.start else None,
            "label": f"CSV {len(universe)}종목",
            "bias_note": "CSV 종목 백테스트는 종목 선택 자체에 사후 편향이 섞일 수 있습니다"}


# ── 출력 ──────────────────────────────────────────────────────────────────────

def build_data(results, asof, scanned, regimes=None, label=None):
    tiers = {"ready": [], "ignited": [], "wait": [], "excluded": []}
    for a in results:
        tiers[a["tier"]].append(a)
    tiers["ready"].sort(key=lambda x: -x["score"])
    tiers["ignited"].sort(key=lambda x: -x["today_vol_ratio"])
    # 시장 국면 때문에 강등된 후보를 대기 목록 맨 앞에
    tiers["wait"].sort(key=lambda x: (x.get("raw_tier", x["tier"]) == x["tier"], x["dd"]))
    for i, a in enumerate(tiers["ready"], 1):
        a["rank"] = f"{i}순위"
    data = {
        "asof": asof,
        "universe": {"scanned": scanned, "label": label or f"유동성 상위 상장주 {scanned}개"},
        "generated": True,
        "tiers": tiers,
    }
    if regimes:
        data["regime"] = regimes
    return data


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
    for r in (data.get("regime") or {}).values():
        print(f"  시장 국면 {r['name']}: {r['label']} — {r['note']}")
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
                for r in a["reasons"][1:]:
                    print(f"      ⚠ {r}")
    print()


def _w(s):
    return sum(2 if unicodedata.east_asian_width(ch) in "WF" else 1 for ch in str(s))


def _lj(s, width):
    return str(s) + " " * max(0, width - _w(s))


def _rj(s, width):
    return " " * max(0, width - _w(s)) + str(s)


def _pct(x):
    return "—" if x is None else f"{x * 100:+.2f}%"


STAT_COLS = (("거래", 7), ("승률", 8), ("평균", 9), ("중앙값", 9), ("손익비", 8), ("PF", 7), ("보유", 8))


def _stat_line(label, s, lw):
    if not s or not s.get("n"):
        cells = ["0"] + ["—"] * (len(STAT_COLS) - 1)
    else:
        cells = [f"{s['n']:,}", f"{s['win'] * 100:.1f}%", _pct(s["avg"]), _pct(s["median"]),
                 "—" if s["payoff"] is None else f"{s['payoff']:.2f}",
                 "—" if s["pf"] is None else f"{s['pf']:.2f}", f"{s['hold']:.1f}일"]
    return "  " + _lj(label, lw) + "".join(_rj(c, w) for c, (_, w) in zip(cells, STAT_COLS))


def print_backtest(s):
    o, st, lw = s["opts"], s["stats"], 34
    gated_on = s["regime_gate"] and bool(s["regime_source"])
    print(f"\n■ 상승 2파 백테스트 — 신호 기간 {s['period']} · {s['universe']}")
    print(f"  진입: {o['entry_label']} · 청산: 전고점 도달(목표) / 추세 경고선 종가 이탈(손절) / "
          f"{o['hold']}거래일 경과 · 왕복비용 {o['cost'] * 100:.2f}%")

    print("\n[거래 성과]")
    print("  " + _lj("", lw) + "".join(_rj(h, w) for h, w in STAT_COLS))
    if gated_on:
        print(_stat_line("전체 신호 (국면 게이트 미적용)", st["all"], lw))
        print(_stat_line("국면 게이트 적용 (위험 국면 제외)", st["gated"], lw))
    else:
        print(_stat_line("전체 신호", st["gated"], lw))
    print(_stat_line(" ├ 조정 완료·재상승 준비", st["by_tier"]["ready"], lw))
    print(_stat_line(" └ 재상승 당일 확인", st["by_tier"]["ignited"], lw))
    if s["regime_source"]:
        rows = [k for k in REGIME_LABEL if st["by_regime"][k].get("n")]
        print("  시장 국면별 (신호일 국면 · 게이트 미적용)")
        for i, k in enumerate(rows):
            print(_stat_line((" └ " if i == len(rows) - 1 else " ├ ") + REGIME_LABEL[k],
                             st["by_regime"][k], lw))
    g = st["gated"]
    if g.get("n"):
        print("  청산 사유: " + " · ".join(
            f"{EXIT_LABEL[k]} {g['exits'].get(k, 0) / g['n'] * 100:.0f}%" for k in EXIT_LABEL))
    sk = s["skipped"]["gated"]
    if sk:
        print("  거래로 이어지지 않은 신호일: " + " · ".join(
            f"{SKIP_LABEL.get(k, k)} {v:,}" for k, v in sorted(sk.items(), key=lambda kv: -kv[1])))

    ev, days, cw = s["event"], [str(d) for d in o["fwd"]], 16
    on, base = ev["onset"], ev["baseline"]

    def cell(x):
        return f"{_pct(x['avg'])} · {x['win'] * 100:.0f}%" if x.get("n") else "—"

    print("\n[신호 후 수익률 vs 정배열 기준선]  다음날 시가 매수 → N거래일째 종가, 비용 미반영")
    print("  " + _lj("", lw) + "".join(_rj(f"{d}일 후", cw) for d in days))
    print("  " + _lj(f"신호 첫날 (n={on[days[0]].get('n', 0):,})", lw)
          + "".join(_rj(cell(on[d]), cw) for d in days))
    print("  " + _lj(f"정배열 추세 전체일 (n={base[days[0]].get('n', 0):,})", lw)
          + "".join(_rj(cell(base[d]), cw) for d in days))
    excess = [f"{(on[d]['avg'] - base[d]['avg']) * 100:+.2f}%p"
              if on[d].get("n") and base[d].get("n") else "—" for d in days]
    print("  " + _lj("초과 수익(평균)", lw) + "".join(_rj(x, cw) for x in excess))
    print("  (셀 = 평균 수익률 · 상승 마감 비율)")

    if s["sweep"]:
        cells = {(tuple(x["pullback"]), tuple(x["rsi"])): x for x in s["sweep"]}
        cur_pb, cur_rsi = tuple(s["criteria"]["pullback"]), tuple(s["criteria"]["rsi"])
        sw = 24
        print("\n[민감도 — 준비형 신호만, 조정 깊이 × RSI 범위]"
              + (" · 국면 게이트 적용" if gated_on else ""))
        print("  " + _lj("조정 깊이 \\ RSI", 16) + "".join(
            _rj(f"{lo:.0f}~{hi:.0f}" + (" *" if (lo, hi) == cur_rsi else ""), sw)
            for lo, hi in SWEEP_RSI))
        for pb in SWEEP_PULLBACK:
            row = "  " + _lj(f"{pb[0] * 100:.0f}~{pb[1] * 100:.0f}%"
                             + (" *" if pb == cur_pb else ""), 16)
            for rs in SWEEP_RSI:
                x = cells.get((pb, rs), {"n": 0})
                row += _rj(f"n={x['n']:,} {_pct(x['avg'])} {x['win'] * 100:.0f}%"
                           if x.get("n") else "n=0", sw)
            print(row)
        print("  * 현재 기준 · 셀 = 거래수 / 평균 수익률 / 승률 — 거래 30건 미만은 표본이 적어 참고만")

    print("\n  ※ 일봉 기준 체결 가정: 같은 날 목표가·손절선이 모두 닿으면 장중 목표가 체결 우선, "
          "관심 구간 진입일의 목표가 도달은 불인정")
    if s.get("bias_note"):
        print(f"  ※ {s['bias_note']}")
    print("  ※ 과거 성과가 미래 수익을 보장하지 않습니다 — 기준 검증·비교용으로만 사용하세요.\n")


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


# ── 실행 ──────────────────────────────────────────────────────────────────────

def screen_mode(ctx, cfg):
    regimes = {mkt: market_regime(mkt, bars, cfg) for mkt, bars in ctx["index"].items()}
    results, short = [], []
    for name, code, market, bars in ctx["universe"]:
        a = analyze(name, code, bars, cfg, regimes.get(market))
        if a is None:
            short.append(f"{name}({len(bars)}봉)")
            continue
        a["market"] = market
        results.append(a)
    if short:
        print(f"  ! 일봉 {cfg['min_bars']}개 미만으로 제외: {', '.join(short)}", file=sys.stderr)
    if not results:
        sys.exit(f"데이터 부족: 일봉 {cfg['min_bars']}개 이상 필요")
    return build_data(results, ctx["asof"], len(ctx["universe"]), regimes or None, ctx["label"])


def backtest_mode(ctx, cfg, opts, sweep):
    regimes = {mkt: regime_series(mkt, bars, cfg) for mkt, bars in ctx["index"].items()}
    res = run_backtest(ctx["universe"], regimes, opts, cfg, ctx["start"], ctx["asof"], sweep)
    summary = summarize_backtest(res, opts, cfg, ctx)
    print_backtest(summary)
    return summary


def build_parser():
    p = argparse.ArgumentParser(
        description="상승 2파 스크리너 — 스크린·시장 국면 게이트·백테스트 (기준은 파일 상단 docstring 참고)")
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--live", action="store_true",
                     help="네이버 금융 일봉으로 스캔 (유동성 순위는 pykrx·KRX 로그인 필요, --tickers면 불필요)")
    src.add_argument("--csv", metavar="FILE", nargs="+",
                     help="일봉 CSV (날짜/시가/고가/저가/종가/거래량). 파일명 '105560_KB금융.csv'면 코드·이름 인식")
    p.add_argument("--tickers", help="--live 종목 직접 지정, 쉼표 구분 (KOSDAQ은 .KQ — 예: 105560,214450.KQ)")
    p.add_argument("--top", type=int, default=120, help="--live 유동성 상위 스캔 종목 수 (기본 120)")
    p.add_argument("--date", help="기준일 YYYYMMDD — 스크린 기준일 / 백테스트 종료일 (기본: 최근 거래일)")
    p.add_argument("--name", help="--csv 1종목일 때 종목명")
    p.add_argument("--code", help="--csv 1종목일 때 종목코드")
    p.add_argument("--index-csv", metavar="FILE", help="--csv 시장 국면 판정용 지수 일봉 CSV")
    p.add_argument("--index-name", default="지수", help="--index-csv 지수 이름 (기본 '지수')")
    p.add_argument("--no-regime", action="store_true", help="시장 국면 게이트 끄기 (국면은 표시만)")
    bt = p.add_argument_group("백테스트")
    bt.add_argument("--backtest", action="store_true", help="과거 구간에서 신호를 재현해 성과 검증")
    bt.add_argument("--start", help="시작일 YYYYMMDD (기본: --live는 종료일 --years년 전, CSV는 전체 구간)")
    bt.add_argument("--years", type=float, default=3, help="--live 백테스트 기간(년, 기본 3)")
    bt.add_argument("--entry", choices=tuple(ENTRY_LABEL), default=BT["entry"],
                    help="진입: open 다음날 시가 / zone 관심 구간 지정가 / breakout 단기 고점 돌파 (기본 open)")
    bt.add_argument("--hold", type=int, default=BT["hold"], help="최대 보유 거래일 (기본 20)")
    bt.add_argument("--cost", type=float, default=BT["cost"], help="왕복 거래비용 비율 (기본 0.003)")
    bt.add_argument("--sweep", action="store_true", help="조정 깊이 × RSI 범위 민감도 분석")
    p.add_argument("--json", metavar="FILE", help="결과를 JSON으로 저장")
    p.add_argument("--update-html", metavar="FILE", help="wave2.html의 WAVE2_DATA 블록 갱신 (스크린 전용)")
    return p


def main(argv=None):
    p = build_parser()
    args = p.parse_args(argv)
    if args.backtest and args.update_html:
        p.error("--update-html은 스크린 모드에서만 사용할 수 있습니다")
    if args.tickers and not args.live:
        p.error("--tickers는 --live와 함께 사용합니다")
    cfg = dict(CFG, regime_gate=not args.no_regime)
    ctx = live_context(args, cfg) if args.live else csv_context(args, cfg)
    if not ctx["universe"]:
        sys.exit("분석할 종목이 없습니다 (조회 실패 또는 데이터 부족)")

    if args.backtest:
        opts = dict(BT, entry=args.entry, hold=args.hold, cost=args.cost)
        data = backtest_mode(ctx, cfg, opts, args.sweep)
    else:
        data = screen_mode(ctx, cfg)
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
