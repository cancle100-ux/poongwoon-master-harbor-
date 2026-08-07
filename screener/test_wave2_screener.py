# -*- coding: utf-8 -*-
"""wave2_screener 단위 테스트 — 합성 일봉으로 5개 부류 분류를 검증한다.

실행: python3 -m unittest discover -s screener -v
"""
import json
import os
import tempfile
import unittest

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


class TestClassification(unittest.TestCase):
    def ready_bars(self):
        # 완만한 지그재그 상승 → 6일 급등(스파이크) → 9일 조정 → 저점 다지기 → 반등 양봉
        closes = zigzag(120000, 155, up=0.016, down=0.011)   # ~174k 부근 도달
        peak_base = closes[-1]
        spike = [peak_base * (1 + 0.015 * (i + 1)) for i in range(6)]      # → ~190k
        top = spike[-1]
        drop = [top - (top - 169000) * (i + 1) / 9 for i in range(9)]      # → 169k
        stabilize = [169400, 170300, 171200]
        bounce = [177500]
        closes = closes + spike + drop + stabilize + bounce

        vols = [100000] * 155 + [150000] * 6 + \
               [90000, 85000, 80000, 78000, 75000, 60000, 55000, 52000, 50000] + \
               [48000, 46000, 45000] + [60000]
        return make_bars(closes, vols)

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
            w.update_html(path, data)
            with open(path, encoding="utf-8") as f:
                out = f.read()
            self.assertIn('"asof": "2026-08-07"', out)
            self.assertEqual(out.count(w.DATA_START), 1)
            self.assertTrue(out.startswith("<html><script>"))
            self.assertTrue(out.endswith("</script></html>"))
        finally:
            os.unlink(path)


if __name__ == "__main__":
    unittest.main()
