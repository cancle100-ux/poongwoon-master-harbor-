# -*- coding: utf-8 -*-
"""wave2_screener 단위 테스트 — 합성 일봉으로 분류·시장 국면 게이트·백테스트를 검증한다.

실행: python3 -m unittest discover -s screener -v
"""
import datetime
import io
import json
import math
import os
import random
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest import mock

import wave2_screener as w


def make_bars(closes, vols, opens=None):
    """종가·거래량 리스트로 일봉 생성. 시가=전일 종가, 고가/저가는 몸통 ±0.4%."""
    bars = []
    prev = closes[0]
    for i, (c, v) in enumerate(zip(closes, vols)):
        o = opens[i] if opens and opens[i] is not None else prev
        hi = max(o, c) * 1.004
        lo = min(o, c) * 0.996
        bars.append(w.Bar(f"D{i:03d}", o, hi, lo, c, v))
        prev = c
    return bars


def zigzag(start, days, up=0.015, down=0.010):
    """이틀 주기(+up, -down) 지그재그 상승 종가 시퀀스."""
    out, c = [], start
    for i in range(days):
        c *= (1 + up) if i % 2 == 0 else (1 - down)
        out.append(c)
    return out


def ready_series():
    """완만한 지그재그 상승 → 6일 급등 → 9일 조정 → 저점 다지기 → 반등 양봉 (마지막 날 D173이 준비형)."""
    closes = zigzag(120000, 155, up=0.016, down=0.011)   # ~174k 부근 도달
    peak_base = closes[-1]
    spike = [peak_base * (1 + 0.015 * (i + 1)) for i in range(6)]      # → ~190k
    top = spike[-1]
    drop = [top - (top - 169000) * (i + 1) / 9 for i in range(9)]      # → 169k
    closes = closes + spike + drop + [169400, 170300, 171200] + [177500]
    vols = [100000] * 155 + [150000] * 6 + \
           [90000, 85000, 80000, 78000, 75000, 60000, 55000, 52000, 50000] + \
           [48000, 46000, 45000] + [60000]
    return closes, vols


def ready_bars():
    return make_bars(*ready_series())


def dated(bars, end=datetime.date(2026, 9, 25)):
    """합성 일봉에 실제 날짜(주말 제외, end에서 거꾸로)를 붙인다."""
    days, d = [], end
    while len(days) < len(bars):
        if d.weekday() < 5:
            days.append(d.isoformat())
        d -= datetime.timedelta(days=1)
    days.reverse()
    return [w.Bar(dt, b.open, b.high, b.low, b.close, b.volume) for dt, b in zip(days, bars)]


def index_bars(n, daily):
    return make_bars([2500 * (1 + daily) ** i for i in range(n)], [1e6] * n)


def swing_stock(rng, n=520, start=20000.0):
    """상승 파동(거래량 증가) ↔ 눌림(거래량 감소)이 반복되는 합성 종목 — 신호가 여러 번 나오도록."""
    closes, vols, c, day = [], [], start, 0
    while day < n:
        for _ in range(rng.randint(18, 30)):            # 상승 파동
            c *= 1 + rng.gauss(0.009, 0.012)
            closes.append(c)
            vols.append(rng.uniform(90000, 140000))
        for _ in range(rng.randint(5, 9)):              # 눌림
            c *= 1 + rng.gauss(-0.012, 0.008)
            closes.append(c)
            vols.append(rng.uniform(40000, 70000))
        day = len(closes)
    closes, vols = closes[:n], vols[:n]
    opens = [None] + [closes[i - 1] * (1 + rng.gauss(0, 0.004)) for i in range(1, n)]
    return make_bars(closes, vols, opens)


class TestIndicators(unittest.TestCase):
    def test_rsi_all_up_is_100(self):
        closes = [100 + i for i in range(40)]
        self.assertEqual(w.rsi_wilder(closes), 100.0)

    def test_rsi_short_series_none(self):
        self.assertIsNone(w.rsi_wilder([1, 2, 3]))

    def test_krx_tick_bands(self):
        self.assertEqual(w.to_tick(175830), 175800)
        self.assertEqual(w.to_tick(378460), 378500)
        self.assertEqual(w.to_tick(1234), 1234)
        self.assertEqual(w.to_tick(503300), 503000)

    def test_floor_grid(self):
        self.assertEqual(w.floor_grid(169214), 169000)
        self.assertEqual(w.floor_grid(10450), 10400)
        self.assertEqual(w.floor_grid(4990), 4990)

    def test_norm_date(self):
        self.assertEqual(w.norm_date("20260807"), "2026-08-07")
        self.assertEqual(w.norm_date("2026.08.07"), "2026-08-07")
        self.assertEqual(w.norm_date("2026-08-07 00:00:00"), "2026-08-07")
        self.assertEqual(w.norm_date("D173"), "D173")


class TestClassification(unittest.TestCase):
    def ready_bars(self):
        return ready_bars()

    def test_ready_case(self):
        a = w.analyze("준비형", "000010", self.ready_bars())
        self.assertIsNotNone(a)
        detail = json.dumps({k: a[k] for k in
                             ("tier", "reasons", "dd", "rsi", "contraction",
                              "dist20", "range_pos")}, ensure_ascii=False, default=str)
        self.assertEqual(a["tier"], "ready", detail)
        self.assertTrue(all(c["ok"] for c in a["checklist"]), detail)
        self.assertTrue(0.05 <= -a["dd"] <= 0.15, detail)
        self.assertLessEqual(a["contraction"], 0.80, detail)
        self.assertGreater(a["score"], 0)

    def test_ready_levels_order_and_fib(self):
        a = w.analyze("준비형", "000010", self.ready_bars())
        prices = [lv.get("price", lv.get("hi")) for lv in a["levels"]]
        self.assertEqual(prices, sorted(prices, reverse=True), a["levels"])
        by_type = {lv["type"]: lv for lv in a["levels"]}
        fib = a["pullback_low"] + 0.5 * (a["pullback_high"] - a["pullback_low"])
        self.assertAlmostEqual(by_type["resist"]["price"], w.to_tick(fib), delta=1)
        self.assertEqual(by_type["target"]["price"], w.to_tick(a["pullback_high"]))
        self.assertEqual(by_type["invalid"]["label"], "상승 추세 무효화(60일선 이탈)")
        # 눌림 관심 구간은 현재가 이하, 조정 저점 이상
        zone = by_type["interest"]
        self.assertLessEqual(zone["hi"], w.to_tick(a["close"]) + w.krx_tick(a["close"]))
        self.assertLess(zone["lo"], zone["hi"])
        self.assertGreaterEqual(zone["lo"], w.floor_grid(a["pullback_low"]))

    def test_ignited_case(self):
        # 지그재그 상승 → 얕은 조정(-4%, 거래량 감소) → 당일 거래량 실린 양봉·고가권 마감
        closes = zigzag(80000, 172, up=0.015, down=0.010)    # ~113k 부근
        top = closes[-1]
        dip = [top * (1 - 0.006 * (i + 1)) for i in range(6)]  # -3.6%
        recover = [dip[-1] * 1.008, dip[-1] * 1.024]
        closes = closes + dip + recover
        vols = [100000] * 172 + [70000] * 6 + [80000, 130000]
        a = w.analyze("시동형", "000020", make_bars(closes, vols))
        detail = json.dumps({k: a[k] for k in
                             ("tier", "reasons", "dd", "rsi", "today_vol_ratio",
                              "range_pos")}, ensure_ascii=False, default=str)
        self.assertEqual(a["tier"], "ignited", detail)
        self.assertGreaterEqual(a["today_vol_ratio"], 1.0, detail)
        self.assertLessEqual(-a["dd"], 0.05, detail)
        by_type = {lv["type"]: lv for lv in a["levels"]}
        self.assertIn("lo", by_type["interest"])
        self.assertEqual(by_type["invalid"]["label"], "추세 훼손(20일선 종가 이탈)")

    def test_wait_case_no_volume_contraction_close_at_low(self):
        # 조정 폭은 기준(-10%)이지만 거래량이 줄지 않고 당일 저가권 음봉 마감
        closes = zigzag(120000, 155, up=0.016, down=0.011)
        peak_base = closes[-1]
        spike = [peak_base * (1 + 0.021 * (i + 1)) for i in range(6)]
        top = spike[-1]
        drop = [top - (top - 172000) * (i + 1) / 11 for i in range(11)]
        closes = closes + spike + drop
        vols = [100000] * 155 + [150000] * 6 + [110000] * 11
        a = w.analyze("대기형", "000030", make_bars(closes, vols))
        detail = json.dumps({k: a[k] for k in ("tier", "reasons", "dd", "contraction",
                                               "range_pos")}, ensure_ascii=False, default=str)
        self.assertEqual(a["tier"], "wait", detail)
        self.assertTrue(any("거래량 미감소" in r for r in a["reasons"]), detail)

    def test_excluded_breakout_chase(self):
        # 신고가 경신 중(고점 대비 0%) → 눌림형 아님, 돌파 추격형으로 분리
        closes = zigzag(50000, 190, up=0.015, down=0.010)
        vols = [100000] * 190
        bars = make_bars(closes, vols)
        last = bars[-1]
        bars[-1] = w.Bar(last.date, last.open, max(c.high for c in bars),
                         last.low, max(c.high for c in bars), last.volume)
        a = w.analyze("추격형", "000040", bars)
        self.assertEqual(a["tier"], "excluded", a["reasons"])
        self.assertTrue(any("돌파" in r or "과열" in r for r in a["reasons"]), a["reasons"])

    def test_excluded_not_aligned(self):
        closes = [200000 - 300 * i for i in range(160)]
        a = w.analyze("역배열", "000050", make_bars(closes, [100000] * 160))
        self.assertEqual(a["tier"], "excluded")
        self.assertIn("정배열 미충족", a["reasons"][0])

    def test_insufficient_bars_returns_none(self):
        closes = zigzag(10000, 100)
        self.assertIsNone(w.analyze("신규", "000060", make_bars(closes, [1000] * 100)))


class TestRegime(unittest.TestCase):
    def test_favorable(self):
        r = w.market_regime("KOSPI", index_bars(130, 0.003))
        self.assertEqual(r["state"], "favorable")
        self.assertEqual(r["label"], "우호")

    def test_risk_off(self):
        self.assertEqual(w.market_regime("KOSPI", index_bars(130, -0.003))["state"], "risk_off")

    def test_caution_short_term_dip(self):
        closes = [2000 * 1.003 ** i for i in range(120)]
        closes += [closes[-1] * (1 - 0.006 * (i + 1)) for i in range(6)]   # 20일선 아래, 60일선 위
        r = w.market_regime("KOSPI", make_bars(closes, [1e6] * len(closes)))
        self.assertEqual(r["state"], "caution")
        self.assertIn("20일선 아래", r["note"])

    def test_unknown_when_short(self):
        self.assertEqual(w.market_regime("KOSPI", index_bars(30, 0.003))["state"], "unknown")

    def test_series_uses_only_past_data(self):
        closes = [2000 * (1 + 0.04 * math.sin(i / 9)) * 1.001 ** i for i in range(220)]
        bars = make_bars(closes, [1e6] * 220)
        series = w.regime_series("KOSPI", bars)
        states = set(series.values())
        self.assertTrue({"favorable", "risk_off"} <= states, states)
        for i in range(len(bars)):
            self.assertEqual(series[bars[i].date],
                             w.market_regime("KOSPI", bars[:i + 1])["state"], i)


class TestRegimeGate(unittest.TestCase):
    @staticmethod
    def regime(state):
        return {"name": "KOSPI", "state": state, "label": w.REGIME_LABEL[state], "note": "테스트"}

    def test_risk_off_demotes_ready_to_wait(self):
        a = w.analyze("준비형", "000010", ready_bars(), regime=self.regime("risk_off"))
        self.assertEqual(a["tier"], "wait")
        self.assertEqual(a["raw_tier"], "ready")
        self.assertEqual(a["grade"], "시장 국면 대기")
        self.assertIn("시장 국면 위험", a["reasons"][0])
        self.assertTrue(a["levels"])            # 대응 가격은 그대로 제공

    def test_caution_keeps_tier_with_note(self):
        a = w.analyze("준비형", "000010", ready_bars(), regime=self.regime("caution"))
        self.assertEqual(a["tier"], "ready")
        self.assertTrue(any("비중 축소" in r for r in a["reasons"]), a["reasons"])

    def test_gate_off_keeps_tier(self):
        cfg = dict(w.CFG, regime_gate=False)
        a = w.analyze("준비형", "000010", ready_bars(), cfg, regime=self.regime("risk_off"))
        self.assertEqual(a["tier"], "ready")
        self.assertEqual(a["regime"], "risk_off")

    def test_blocked_candidates_listed_first_in_wait(self):
        blocked = w.analyze("강등", "000011", ready_bars(), regime=self.regime("risk_off"))
        normal = dict(blocked, name="일반대기", raw_tier="wait", dd=-0.30)
        data = w.build_data([normal, blocked], "2026-09-25", 2)
        self.assertEqual([a["name"] for a in data["tiers"]["wait"]], ["강등", "일반대기"])


PLAN = {"target": 110.0, "stop": 95.0, "confirm": 104.0, "zone_hi": 100.0}


def B(i, o, h, lo, c):
    return w.Bar(f"D{i:03d}", o, h, lo, c, 1000)


class TestEntryExit(unittest.TestCase):
    def test_open_entry_next_day(self):
        bars = [B(0, 100, 101, 99, 100), B(1, 101, 102, 100, 101)]
        self.assertEqual(w.find_entry(bars, 0, PLAN, "open", 5), ((1, 101), None))

    def test_open_gap_filters(self):
        over = [B(0, 100, 101, 99, 100), B(1, 111, 112, 110, 111)]
        under = [B(0, 100, 101, 99, 100), B(1, 94, 95, 93, 94)]
        self.assertEqual(w.find_entry(over, 0, PLAN, "open", 5), (None, "gap_over_target"))
        self.assertEqual(w.find_entry(under, 0, PLAN, "open", 5), (None, "gap_under_stop"))

    def test_breakout_waits_for_trigger_one_tick_above(self):
        bars = [B(0, 100, 101, 99, 100), B(1, 101, 104.5, 100, 103),   # 104 돌파 전(105 미만)
                B(2, 104, 106, 103, 105.5)]
        self.assertEqual(w.find_entry(bars, 0, PLAN, "breakout", 5), ((2, 105), None))

    def test_breakout_gap_up_fills_at_open(self):
        bars = [B(0, 100, 101, 99, 100), B(1, 106, 107, 105.5, 106)]
        self.assertEqual(w.find_entry(bars, 0, PLAN, "breakout", 5), ((1, 106), None))

    def test_breakout_invalidated_expired_data_end(self):
        broke = [B(0, 100, 101, 99, 100), B(1, 99, 100, 93, 94)]
        flat = [B(i, 100, 101, 99, 100) for i in range(7)]
        self.assertEqual(w.find_entry(broke, 0, PLAN, "breakout", 5), (None, "invalidated"))
        self.assertEqual(w.find_entry(flat, 0, PLAN, "breakout", 5), (None, "expired"))
        self.assertEqual(w.find_entry(flat[:3], 0, PLAN, "breakout", 5), (None, "data_end"))

    def test_zone_limit_fill_and_gap_below_stop(self):
        fill = [B(0, 102, 103, 101, 102), B(1, 101, 101.5, 99.5, 100.5)]
        gap = [B(0, 102, 103, 101, 102), B(1, 94, 95, 93, 94.5)]
        self.assertEqual(w.find_entry(fill, 0, PLAN, "zone", 5), ((1, 100), None))
        self.assertEqual(w.find_entry(gap, 0, PLAN, "zone", 5), (None, "gap_under_stop"))

    def test_exit_target_stop_time_and_open(self):
        base = [B(0, 100, 101, 99, 100), B(1, 101, 102, 100, 101)]
        target = base + [B(2, 105, 111, 104, 109)]
        gap_target = base + [B(2, 112, 113, 111, 112)]
        stop = base + [B(2, 100, 100.5, 93, 94)]
        both = base + [B(2, 100, 111, 93, 94)]
        flat = base + [B(i, 101, 102, 100, 101) for i in range(2, 6)]
        self.assertEqual(w.run_exit(target, 1, PLAN, 20), (2, 110.0, "target"))
        self.assertEqual(w.run_exit(gap_target, 1, PLAN, 20), (2, 112, "target"))
        self.assertEqual(w.run_exit(stop, 1, PLAN, 20), (2, 94, "stop"))
        self.assertEqual(w.run_exit(both, 1, PLAN, 20), (2, 110.0, "target"))   # 장중 목표가 우선
        self.assertEqual(w.run_exit(flat, 1, PLAN, 3), (3, 101, "time"))
        self.assertIsNone(w.run_exit(flat, 1, PLAN, 20))                         # 미청산

    def test_zone_entry_day_target_not_counted(self):
        bars = [B(0, 102, 103, 101, 102), B(1, 111, 111.5, 99, 101), B(2, 108, 111, 107, 110)]
        self.assertEqual(w.run_exit(bars, 1, PLAN, 20, target_same_day=False), (2, 110.0, "target"))
        self.assertEqual(w.run_exit(bars, 1, PLAN, 20, target_same_day=True), (1, 110.0, "target"))


class TestBacktest(unittest.TestCase):
    def run_stock(self, extra_closes, extra_vols):
        closes, vols = ready_series()
        bars = make_bars(closes + extra_closes, vols + extra_vols)
        metrics = w.stock_metrics("준비형", "000010", bars)
        return w.simulate_stock("준비형", "000010", bars, metrics, w.CFG, {}, dict(w.BT))

    def test_ready_signal_hits_target(self):
        rally = [177500 * 1.015 ** k for k in range(1, 9)]
        trades, _ = self.run_stock(rally, [60000] * 8)
        t = trades[0]
        self.assertEqual((t["signal_date"], t["entry_date"], t["exit_date"]), ("D173", "D174", "D179"))
        self.assertEqual((t["tier"], t["reason"], t["hold"]), ("ready", "target", 6))
        self.assertEqual((t["entry"], t["exit"], t["stop"], t["target"]), (177500, 193300, 168000, 193300))
        self.assertAlmostEqual(t["ret"], 193300 / 177500 - 1 - w.BT["cost"])

    def test_ready_signal_stopped_on_close(self):
        trades, _ = self.run_stock([175000, 172000, 169000, 166000, 165000], [60000] * 5)
        t = trades[0]
        self.assertEqual((t["signal_date"], t["exit_date"], t["reason"], t["exit"]),
                         ("D173", "D177", "stop", 166000))

    def test_metrics_never_use_future_bars(self):
        rng = random.Random(3)
        bars = swing_stock(rng)
        k = 380
        garbage = swing_stock(random.Random(99))[k + 1:]
        altered = bars[:k + 1] + [w.Bar(b.date, b.open * 3, b.high * 3, b.low * 3, b.close * 3,
                                        b.volume * 9) for b in garbage]
        m1 = w.stock_metrics("A", "1", bars)
        m2 = w.stock_metrics("A", "1", altered)
        self.assertEqual(m1[:k + 1], m2[:k + 1])
        self.assertNotEqual(m1[k + 1:], m2[k + 1:])

    def universe(self):
        rng = random.Random(11)
        return [(f"합성{i}", f"{i:06d}", "KOSPI", swing_stock(rng)) for i in range(4)]

    def test_random_universe_invariants(self):
        uni = self.universe()
        idx = make_bars([2500 * (1 + 0.05 * math.sin(i / 25)) for i in range(520)], [1e6] * 520)
        regimes = {"KOSPI": w.regime_series("KOSPI", idx)}
        opts = dict(w.BT)
        with redirect_stderr(io.StringIO()):
            res = w.run_backtest(uni, regimes, opts, w.CFG, sweep=True)
        self.assertGreater(len(res["all"]), 3, "합성 데이터에서 신호가 충분히 나와야 한다")
        self.assertTrue(any(t["regime"] == "risk_off" for t in res["all"]))
        for t in res["all"] + res["gated"]:
            self.assertLess(t["signal_date"], t["entry_date"])
            self.assertLessEqual(t["entry_date"], t["exit_date"])
            self.assertLessEqual(t["hold"], opts["hold"])
            self.assertAlmostEqual(t["ret"], t["exit"] / t["entry"] - 1 - opts["cost"])
            if t["reason"] == "stop":
                self.assertLess(t["exit"], t["stop"])
            if t["reason"] == "target":
                self.assertGreaterEqual(t["exit"], t["target"])
        self.assertFalse(any(t["regime"] == "risk_off" for t in res["gated"]))
        for trades in (res["all"], res["gated"]):
            by_code = {}
            for t in trades:
                by_code.setdefault(t["code"], []).append(t)
            for ts in by_code.values():                       # 보유 중에는 새 신호를 받지 않는다
                for a, b in zip(ts, ts[1:]):
                    self.assertGreater(b["signal_date"], a["exit_date"])
        self.assertTrue(res["onset"] and res["baseline"])
        self.assertEqual(len(res["sweep"]), 9)
        # 민감도 격자의 '현재 기준' 셀 = 현재 CFG로 준비형만 돌린 결과
        current = []
        for name, code, market, bars in uni:
            metrics = w.stock_metrics(name, code, bars)
            current += w.simulate_stock(name, code, bars, metrics, w.CFG, regimes["KOSPI"], opts,
                                        gate=True, tiers=("ready",))[0]
        self.assertEqual(res["sweep"][((0.05, 0.15), (45.0, 60.0))], current)

    def test_summary_and_report(self):
        uni = self.universe()
        idx = make_bars([2500 * (1 + 0.05 * math.sin(i / 25)) for i in range(520)], [1e6] * 520)
        ctx = {"universe": uni, "index": {"KOSPI": idx}, "asof": "D519", "start": None,
               "label": "합성 4종목", "bias_note": "테스트"}
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(io.StringIO()):
            s = w.backtest_mode(ctx, w.CFG, dict(w.BT), sweep=True)
        text = out.getvalue()
        for key in ("[거래 성과]", "국면 게이트 적용", "[신호 후 수익률", "[민감도", "15%"):
            self.assertIn(key, text)
        self.assertEqual(s["stats"]["gated"]["n"], len(s["trades"]))
        json.dumps(s, ensure_ascii=False)                       # JSON 저장 가능해야 한다


NAVER_XML = """<?xml version="1.0" encoding="EUC-KR" ?>
<protocol>
<chartdata symbol="105560" name="KB금융" count="3" timeframe="day" precision="0" origintime="20081010">
<item data="20260923|172000|174500|171000|174000|1200000" />
<item data="20260924|174000|176000|173500|175800|980000" />
<item data="20260925|0|0|0|175800|0" />
</chartdata>
</protocol>"""


class TestNaver(unittest.TestCase):
    def test_parse_chart_skips_no_trade_days(self):
        name, bars = w.parse_naver_chart(NAVER_XML)
        self.assertEqual(name, "KB금융")
        self.assertEqual([b.date for b in bars], ["2026-09-23", "2026-09-24"])
        self.assertEqual((bars[1].open, bars[1].close, bars[1].volume), (174000, 175800, 980000))
        _, all_bars = w.parse_naver_chart(NAVER_XML, require_volume=False)
        self.assertEqual(len(all_bars), 3)

    def test_decode_euc_kr_bytes(self):
        text = w._decode_xml(NAVER_XML.encode("cp949"))
        self.assertEqual(w.parse_naver_chart(text)[0], "KB금융")

    def test_parse_tickers(self):
        self.assertEqual(w.parse_tickers("105560, 214450.kq,055550.KS"),
                         [("105560", "KOSPI"), ("214450", "KOSDAQ"), ("055550", "KOSPI")])


class TestLivePipeline(unittest.TestCase):
    """네트워크 대신 가짜 네이버 응답으로 --live 경로 전체를 검증한다."""

    def setUp(self):
        stock = dated(ready_bars())
        n = len(stock)
        self.fake = {
            "105560": ("테스트준비", stock),
            "214450": ("테스트코스닥", stock),
            "KOSPI": ("코스피", dated(index_bars(n, 0.003))),
            "KOSDAQ": ("코스닥", dated(index_bars(n, -0.003))),
        }
        patcher = mock.patch.object(w, "naver_daily",
                                    side_effect=lambda sym, count, require_volume=True: self.fake[sym])
        patcher.start()
        self.addCleanup(patcher.stop)

    def run_main(self, argv):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            return w.main(argv)

    def test_screen_gates_each_stock_by_its_market(self):
        data = self.run_main(["--live", "--tickers", "105560,214450.KQ", "--date", "20260925"])
        self.assertEqual(data["asof"], "2026-09-25")
        self.assertEqual(data["regime"]["KOSPI"]["state"], "favorable")
        self.assertEqual(data["regime"]["KOSDAQ"]["state"], "risk_off")
        by_code = {a["code"]: a for rows in data["tiers"].values() for a in rows}
        self.assertEqual((by_code["105560"]["tier"], by_code["105560"]["market"]), ("ready", "KOSPI"))
        self.assertEqual((by_code["214450"]["tier"], by_code["214450"]["raw_tier"]), ("wait", "ready"))

    def test_no_regime_flag(self):
        data = self.run_main(["--live", "--tickers", "214450.KQ", "--date", "20260925", "--no-regime"])
        self.assertEqual(data["tiers"]["ready"][0]["regime"], "risk_off")

    def test_backtest_runs_on_live_path(self):
        s = self.run_main(["--live", "--tickers", "105560", "--date", "20260925",
                           "--backtest", "--start", "20260101", "--entry", "breakout"])
        self.assertEqual(s["mode"], "backtest")
        self.assertEqual(s["regime_source"], ["KOSDAQ", "KOSPI"])
        self.assertGreaterEqual(s["period"][:10], "2026-01-01")

    def test_ranking_requires_krx_login(self):
        env = {k: v for k, v in os.environ.items() if k not in ("KRX_ID", "KRX_PW")}
        with mock.patch.dict(os.environ, env, clear=True):
            with self.assertRaises(SystemExit) as cm:
                w.krx_ranked("20260925")
        self.assertIn("KRX_ID", str(cm.exception.code))
        self.assertIn("--tickers", str(cm.exception.code))


class TestOutputs(unittest.TestCase):
    def test_build_data_ranks_ready_by_score(self):
        base = {"tier": "ready", "grade": "A급 재상승 준비형", "today_vol_ratio": 1.0,
                "dd": -0.1, "reasons": [], "levels": [], "checklist": []}
        a = dict(base, name="A", code="1", score=90.0)
        b = dict(base, name="B", code="2", score=70.0)
        data = w.build_data([b, a], "2026-08-07", 2)
        ready = data["tiers"]["ready"]
        self.assertEqual([r["name"] for r in ready], ["A", "B"])
        self.assertEqual(ready[0]["rank"], "1순위")
        self.assertEqual(ready[1]["rank"], "2순위")

    def test_update_html_roundtrip(self):
        html = ("<html><script>\n" + w.DATA_START +
                "\nconst WAVE2_DATA = {};\n" + w.DATA_END + "\n</script></html>")
        with tempfile.NamedTemporaryFile("w", suffix=".html", delete=False,
                                         encoding="utf-8") as f:
            f.write(html)
            path = f.name
        try:
            data = {"asof": "2026-08-07", "universe": {"scanned": 1, "label": "테스트"},
                    "generated": True,
                    "tiers": {"ready": [], "ignited": [], "wait": [], "excluded": []}}
            with redirect_stdout(io.StringIO()):
                w.update_html(path, data)
            with open(path, encoding="utf-8") as f:
                out = f.read()
            self.assertIn('"asof": "2026-08-07"', out)
            self.assertEqual(out.count(w.DATA_START), 1)
            self.assertTrue(out.startswith("<html><script>"))
            self.assertTrue(out.endswith("</script></html>"))
        finally:
            os.unlink(path)

    def test_csv_cli_identity_regime_and_backtest_json(self):
        closes, vols = ready_series()
        rally = [177500 * 1.015 ** k for k in range(1, 9)]
        stock = dated(make_bars(closes + rally, vols + [60000] * 8))
        idx = dated(index_bars(len(stock), 0.003))
        with tempfile.TemporaryDirectory() as d:
            spath, ipath, jpath = (os.path.join(d, x) for x in
                                   ("105560_KB금융.csv", "kospi.csv", "bt.json"))
            for path, bars in ((spath, stock), (ipath, idx)):
                with open(path, "w", encoding="utf-8", newline="") as f:
                    f.write("날짜,시가,고가,저가,종가,거래량\n")
                    for b in bars:
                        f.write(f"{b.date.replace('-', '')},{b.open},{b.high},{b.low},{b.close},{b.volume}\n")
            with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
                data = w.main(["--csv", spath, "--index-csv", ipath, "--index-name", "KOSPI"])
                s = w.main(["--csv", spath, "--index-csv", ipath, "--index-name", "KOSPI",
                            "--backtest", "--sweep", "--json", jpath])
            a = [x for rows in data["tiers"].values() for x in rows][0]
            self.assertEqual((a["name"], a["code"], a["market"]), ("KB금융", "105560", "KOSPI"))
            self.assertEqual(data["regime"]["KOSPI"]["state"], "favorable")
            with open(jpath, encoding="utf-8") as f:
                saved = json.load(f)
            self.assertEqual(saved["stats"]["gated"]["n"], s["stats"]["gated"]["n"])
            self.assertGreaterEqual(s["stats"]["gated"]["n"], 1)
            self.assertEqual(saved["trades"][0]["signal_date"], stock[173].date)


if __name__ == "__main__":
    unittest.main()
