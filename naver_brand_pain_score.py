"""
네이버 쇼핑 급성장 브랜드 Pain Score 분석기
=============================================
Pain Score = 성장속도(0.4) + CS문제(0.4) + SKU복잡도(0.2)

성장 점수: 네이버 DataLab 검색 트렌드 API 기반 실측값
  - 최근 4주 평균 vs 이전 4주 평균 검색량 증가율로 계산

사용 전 준비사항:
  pip install requests pandas tqdm

네이버 개발자 센터(https://developers.naver.com)에서
Client ID / Client Secret 발급 후 아래 환경변수 설정:
  export NAVER_CLIENT_ID=...
  export NAVER_CLIENT_SECRET=...

DataLab API 사용 시 앱 설정에서 '검색' + '데이터랩(검색어트렌드)' 권한 필요
"""

import os
import time
import re
import csv
import json
import math
import random
import logging
import subprocess
from dataclasses import dataclass, field, asdict
from collections import Counter
from datetime import datetime, timedelta
from typing import Optional

import requests
import pandas as pd
from tqdm import tqdm

# ── 로깅 설정 ──────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)

# ── 환경 변수 ──────────────────────────────────────────────────────────────────
NAVER_CLIENT_ID     = os.getenv("NAVER_CLIENT_ID", "YOUR_CLIENT_ID")
NAVER_CLIENT_SECRET = os.getenv("NAVER_CLIENT_SECRET", "YOUR_CLIENT_SECRET")

NAVER_SEARCH_URL       = "https://openapi.naver.com/v1/search/shop.json"
NAVER_DATALAB_URL      = "https://openapi.naver.com/v1/datalab/search"
BRAND_NAVER_PRODUCT_URL = "https://brand.naver.com/n/v1/group-products/{product_id}?channelServiceType=STOREFARM"
REQUEST_DELAY          = 0.35   # 초 (API rate limit 준수)
DATALAB_DELAY          = 0.5    # DataLab API는 좀 더 여유있게
DATALAB_BATCH_SIZE     = 5      # 요청당 최대 키워드 그룹 수
TREND_TOTAL_WEEKS      = 8      # 분석 기간 (주)
TREND_RECENT_WEEKS     = 4      # 최근 기간 (주) — 성장 판단 기준
OUTPUT_CSV             = "brand_pain_score.csv"


# ── 배송 관련 부정 키워드 ──────────────────────────────────────────────────────
SHIPPING_PAIN_KEYWORDS = [
    # 배송 지연
    "배송지연", "배송 지연", "늦게옴", "늦게 왔", "안왔", "아직도 안왔",
    "언제오냐", "언제 오냐", "배송느려", "배송 느려", "너무늦어", "너무 늦어",
    "배송이 늦", "오래걸려", "오래 걸려", "한달째", "몇주째", "배달지연",
    # CS 불만
    "환불거절", "환불 거절", "교환거절", "교환 거절", "고객센터 연결",
    "연락두절", "답장없음", "답장 없음", "응대불량", "불친절",
    "cs최악", "cs 최악", "환불안해줌", "반품거절",
    # 품질 / 포장
    "파손", "박스파손", "포장불량", "포장 불량", "찌그러", "망가져",
    # 재고
    "품절", "재고없", "취소됨", "일방적취소", "일방적 취소",
]

# ── SKU 복잡도 판단 키워드 ─────────────────────────────────────────────────────
SKU_COMPLEXITY_SIGNALS = [
    "사이즈", "색상", "컬러", "옵션", "세트", "단품", "번들",
    "xl", "xxl", "s m l", "s/m/l", "free size",
    "1+1", "2+1", "증정", "구성품",
]

# ── 카테고리 목록 (분석 대상) ──────────────────────────────────────────────────
TARGET_CATEGORIES = [
    "패션의류",
    "스킨케어",
    "헬스/건강식품",
]

# ── Brand Store(brand.naver.com) 브랜드 위주 검색어 ───────────────────────────
# 카테고리 일반 검색어만으론 SmartStore 결과가 대부분을 차지함.
# 아래 키워드를 추가 검색해 brand.naver.com 상품을 더 많이 수집함.
BRAND_STORE_SEARCH_TERMS: dict[str, list[str]] = {
    "패션의류": [
        "나이키", "아디다스", "뉴발란스", "MLB", "폴로랄프로렌",
        "타미힐피거", "캘빈클라인", "리바이스", "아이더", "K2",
        "노스페이스", "컬럼비아", "네파", "블랙야크", "자라",
    ],
    "스킨케어": [
        "아모레퍼시픽", "설화수", "이니스프리", "헤라", "라네즈",
        "에스트라", "닥터자르트", "오휘", "후", "숨37",
        "LG생활건강", "CNP", "AHC", "달바", "토리든",
    ],
    "헬스/건강식품": [
        "종근당건강", "CJ웰케어", "한미약품", "일동제약", "유한양행",
        "GC녹십자", "동국제약", "광동제약", "네이처리퍼블릭", "뉴트리원",
        "암웨이", "뉴스킨", "한국암웨이", "솔가", "센트룸",
    ],
}


# ─────────────────────────────────────────────────────────────────────────────
# 데이터 클래스
# ─────────────────────────────────────────────────────────────────────────────
@dataclass
class BrandMetrics:
    brand: str
    category: str
    total_products: int         = 0
    avg_review_count: float     = 0.0
    avg_price: float            = 0.0
    price_range_ratio: float    = 0.0   # (max - min) / avg → SKU 복잡도 프록시
    sku_option_score: float     = 0.0   # 옵션 다양성 점수
    pain_keyword_count: int     = 0
    pain_keyword_ratio: float   = 0.0
    total_reviews_sampled: int  = 0
    # DataLab 트렌드 실측값
    trend_recent_avg: float     = 0.0   # 최근 N주 평균 검색량 (0~100)
    trend_prev_avg: float       = 0.0   # 이전 N주 평균 검색량 (0~100)
    trend_growth_rate: float    = 0.0   # (recent - prev) / max(prev, 1)
    datalab_available: bool     = False # DataLab 데이터 수집 여부
    growth_score_raw: float     = 0.0   # 0~1 정규화 전 원점수
    cs_score_raw: float         = 0.0
    sku_score_raw: float        = 0.0
    growth_score: float         = 0.0   # 정규화 후
    cs_score: float             = 0.0
    sku_score: float            = 0.0
    pain_score: float           = 0.0   # 최종
    top_pain_keywords: str      = ""
    # 판매 채널 (mallName 집계)
    main_sellers: str           = ""   # 상위 판매몰 목록 (mallName 기반)
    courier_company: str        = "미확인"  # 택배사
    threepl: str                = "미확인"  # 3PL 업체
    sampled_at: str             = field(default_factory=lambda: datetime.now().strftime("%Y-%m-%d"))


# ─────────────────────────────────────────────────────────────────────────────
# 네이버 API 클라이언트
# ─────────────────────────────────────────────────────────────────────────────
class NaverShoppingClient:
    """네이버 쇼핑 검색 API 래퍼"""

    def __init__(self, client_id: str, client_secret: str):
        self.headers = {
            "X-Naver-Client-Id":     client_id,
            "X-Naver-Client-Secret": client_secret,
        }
        self._demo_mode = (client_id == "YOUR_CLIENT_ID")
        if self._demo_mode:
            log.warning("⚠  API 키 미설정 → 데모 데이터로 실행합니다.")

    def search_products(self, query: str, display: int = 100, sort: str = "sim") -> list[dict]:
        """상품 검색 결과 반환 (sort: sim|date|asc|dsc)"""
        if self._demo_mode:
            return self._demo_products(query, display)

        params = {"query": query, "display": display, "sort": sort}
        try:
            resp = requests.get(NAVER_SEARCH_URL, headers=self.headers, params=params, timeout=10)
            resp.raise_for_status()
            return resp.json().get("items", [])
        except requests.RequestException as e:
            log.error("API 오류 (%s): %s", query, e)
            return []
        finally:
            time.sleep(REQUEST_DELAY)

    # ── 데모 데이터 생성 (API 키 없을 때) ────────────────────────────────────
    def _demo_products(self, query: str, display: int) -> list[dict]:
        rng = random.Random(hash(query) % (2**31))
        brands = ["BrandAlpha", "BrandBeta", "BrandGamma", "BrandDelta", "BrandEpsilon"]
        pain_words = SHIPPING_PAIN_KEYWORDS[:8]
        items = []
        for i in range(min(display, 50)):
            brand = rng.choice(brands)
            price = rng.randint(8000, 150000)
            review_count = rng.randint(0, 4000)
            # 일부 리뷰에 pain 키워드 삽입
            title_extra = rng.choice(pain_words) if rng.random() < 0.3 else ""
            sku_extra   = rng.choice(SKU_COMPLEXITY_SIGNALS) if rng.random() < 0.5 else ""
            items.append({
                "brand":       brand,
                "title":       f"{brand} {query} 상품{i+1} {sku_extra}",
                "lprice":      str(price),
                "hprice":      str(int(price * rng.uniform(1.0, 2.5))),
                "reviewCount": str(review_count),
                "category1":   query,
                "mallName":    brand,
                "_demo_review_text": f"배송 {title_extra} 제품 좋아요" if title_extra else "좋아요",
            })
        return items


# ─────────────────────────────────────────────────────────────────────────────
# 네이버 DataLab 클라이언트
# ─────────────────────────────────────────────────────────────────────────────
class NaverDataLabClient:
    """
    네이버 DataLab 검색어 트렌드 API 래퍼
    - 브랜드명을 키워드로 검색량 추이를 가져옴
    - 최대 5개 키워드 그룹 / 요청
    - 반환값: 상대 검색량 0~100 (네이버 기준 최고점 = 100)
    """

    def __init__(self, client_id: str, client_secret: str):
        self.headers = {
            "X-Naver-Client-Id":     client_id,
            "X-Naver-Client-Secret": client_secret,
            "Content-Type":          "application/json",
        }
        self._demo_mode   = (client_id == "YOUR_CLIENT_ID")
        self._scope_error = False   # 권한 오류 시 이후 호출 스킵

    def _date_range(self) -> tuple[str, str]:
        """분석 기간: 오늘 기준 TREND_TOTAL_WEEKS 전 ~ 오늘"""
        end   = datetime.now()
        start = end - timedelta(weeks=TREND_TOTAL_WEEKS)
        return start.strftime("%Y-%m-%d"), end.strftime("%Y-%m-%d")

    def get_trends(self, brand_names: list[str]) -> dict[str, dict]:
        """
        브랜드 이름 목록(최대 5개)의 주간 검색량 반환.
        Returns:
          { "브랜드명": {"recent_avg": float, "prev_avg": float, "growth_rate": float} }
        """
        if not brand_names:
            return {}

        chunk = brand_names[:DATALAB_BATCH_SIZE]

        if self._demo_mode:
            return self._demo_trends(chunk)

        if self._scope_error:
            return {}

        start_date, end_date = self._date_range()
        body = {
            "startDate":     start_date,
            "endDate":       end_date,
            "timeUnit":      "week",
            "keywordGroups": [
                {"groupName": b, "keywords": [b]}
                for b in chunk
            ],
        }

        try:
            resp = requests.post(
                NAVER_DATALAB_URL,
                headers=self.headers,
                json=body,
                timeout=15,
            )
            # 권한 오류(024) 감지 → 이후 호출 스킵 + 폴백 안내
            if resp.status_code in (401, 403):
                err = resp.json()
                if err.get("errorCode") == "024":
                    self._scope_error = True
                    log.warning(
                        "⚠  DataLab 권한 미등록 → 상품 기반 프록시 성장 점수로 폴백합니다.\n"
                        "   네이버 개발자센터 → 내 앱 → API 설정 → "
                        "'데이터랩(검색어트렌드)' 체크 후 재실행하면 실측값을 사용합니다."
                    )
                return {}
            resp.raise_for_status()
            results = resp.json().get("results", [])
        except requests.RequestException as e:
            log.warning("DataLab API 오류 (%s): %s", chunk, e)
            return {}
        finally:
            time.sleep(DATALAB_DELAY)

        output = {}
        for item in results:
            brand = item.get("title", "")
            ratios = [p.get("ratio", 0.0) for p in item.get("data", [])]
            if not ratios:
                continue
            mid = len(ratios) // 2
            recent_vals = ratios[mid:]
            prev_vals   = ratios[:mid]
            recent_avg  = sum(recent_vals) / max(len(recent_vals), 1)
            prev_avg    = sum(prev_vals)   / max(len(prev_vals), 1)
            growth_rate = (recent_avg - prev_avg) / max(prev_avg, 1.0)
            output[brand] = {
                "recent_avg":  round(recent_avg,  4),
                "prev_avg":    round(prev_avg,    4),
                "growth_rate": round(growth_rate, 4),
            }
        return output

    def get_trends_all(self, brand_names: list[str]) -> dict[str, dict]:
        """5개씩 나눠 전체 브랜드 트렌드 수집"""
        result = {}
        for i in range(0, len(brand_names), DATALAB_BATCH_SIZE):
            chunk  = brand_names[i: i + DATALAB_BATCH_SIZE]
            result.update(self.get_trends(chunk))
        return result

    def _demo_trends(self, brands: list[str]) -> dict[str, dict]:
        """데모용 난수 트렌드"""
        out = {}
        for b in brands:
            rng = random.Random(hash(b) % (2**31))
            prev   = rng.uniform(5, 60)
            recent = prev * rng.uniform(0.5, 2.5)
            out[b] = {
                "recent_avg":  round(recent, 4),
                "prev_avg":    round(prev,   4),
                "growth_rate": round((recent - prev) / max(prev, 1), 4),
            }
        return out



# ─────────────────────────────────────────────────────────────────────────────
# 분석 엔진
# ─────────────────────────────────────────────────────────────────────────────
class BrandAnalyzer:
    def __init__(self, client: NaverShoppingClient, datalab: NaverDataLabClient):
        self.client  = client
        self.datalab = datalab

    # ── 1. 브랜드별 상품 집계 ─────────────────────────────────────────────────
    def collect_brand_products(self, category: str) -> dict[str, list[dict]]:
        """카테고리 검색 → 브랜드별 상품 리스트 딕셔너리 반환"""
        log.info("  [수집] 카테고리: %s", category)
        items = self.client.search_products(category, display=100, sort="sim")
        # 최신순 추가 수집 (성장 브랜드 포착용)
        items += self.client.search_products(category, display=100, sort="date")

        brand_map: dict[str, list[dict]] = {}
        for item in items:
            brand = (item.get("brand") or item.get("mallName") or "Unknown").strip()
            if not brand or brand in ("", "Unknown"):
                continue
            brand_map.setdefault(brand, []).append(item)
        return brand_map

    # ── 2a. 프록시 성장 점수 (DataLab 미수집 폴백) ───────────────────────────
    @staticmethod
    def _calc_growth_proxy(products: list[dict]) -> float:
        """상품 수 + 리뷰 수 기반 로그 스케일 프록시 (0~1)"""
        review_counts = []
        for p in products:
            try:
                review_counts.append(int(p.get("reviewCount", 0) or 0))
            except ValueError:
                review_counts.append(0)
        total = sum(review_counts) + len(products) * 10
        return min(math.log1p(total) / math.log1p(25000), 1.0)

    # ── 2b. 성장 점수 (DataLab 실측 기반) ────────────────────────────────────
    @staticmethod
    def calc_growth_score_from_trend(trend: dict | None) -> tuple[float, float, float, float]:
        """
        DataLab 트렌드 데이터로 성장 점수 산출.
        growth_rate = (최근4주 평균 - 이전4주 평균) / 이전4주 평균

        growth_rate 해석:
          +1.0  → 검색량 2배 증가 (100% 성장)
           0.0  → 변화 없음
          -1.0  → 검색량 소멸

        원점수: sigmoid 변환으로 0~1 매핑
          score = 1 / (1 + exp(-2 * growth_rate))
          → growth_rate=0 → 0.5, +100% → ~0.73, +200% → ~0.88, -100% → ~0.27

        Returns: (growth_score_raw, recent_avg, prev_avg, growth_rate)
        """
        if not trend:
            return -1.0, 0.0, 0.0, 0.0   # DataLab 미수집 → 폴백 신호

        recent_avg  = trend.get("recent_avg",  0.0)
        prev_avg    = trend.get("prev_avg",    0.0)
        growth_rate = trend.get("growth_rate", 0.0)

        # 검색량 자체가 0에 가까우면 신뢰도 낮음 → 패널티
        if recent_avg < 1.0 and prev_avg < 1.0:
            return 0.3, recent_avg, prev_avg, growth_rate

        score = 1.0 / (1.0 + math.exp(-2.0 * growth_rate))
        return round(score, 4), recent_avg, prev_avg, growth_rate

    # ── 3. CS 문제 점수 ───────────────────────────────────────────────────────
    def calc_cs_score(self, products: list[dict]) -> tuple[float, int, int, str]:
        """
        상품 제목 + 데모 리뷰 텍스트에서 pain 키워드 검출
        Returns: (cs_score_raw, pain_count, total_sampled, top_keywords_str)
        """
        all_text: list[str] = []
        for p in products:
            all_text.append((p.get("title") or "").lower())
            all_text.append((p.get("_demo_review_text") or "").lower())

        keyword_hits: Counter = Counter()
        total_tokens = len(all_text)

        for text in all_text:
            for kw in SHIPPING_PAIN_KEYWORDS:
                if kw in text:
                    keyword_hits[kw] += 1

        pain_count = sum(keyword_hits.values())
        top_kws = ", ".join(f"{kw}({cnt})" for kw, cnt in keyword_hits.most_common(5))
        ratio = pain_count / max(total_tokens, 1)
        cs_raw = min(ratio * 10, 1.0)   # 10% 이상이면 만점
        return cs_raw, pain_count, total_tokens, top_kws

    # ── 4. SKU 복잡도 점수 ────────────────────────────────────────────────────
    def calc_sku_score(self, products: list[dict]) -> float:
        """
        - 가격대 폭 (hprice - lprice) / avg → 옵션 다양성 프록시
        - 제목 내 SKU 신호 키워드 비중
        """
        prices_low, prices_high, sku_signal_count = [], [], 0

        for p in products:
            try:
                lp = int(p.get("lprice", 0) or 0)
                hp = int(p.get("hprice", 0) or 0)
                if lp > 0:
                    prices_low.append(lp)
                if hp > 0:
                    prices_high.append(hp)
            except ValueError:
                pass

            title = (p.get("title") or "").lower()
            if any(sig in title for sig in SKU_COMPLEXITY_SIGNALS):
                sku_signal_count += 1

        # 가격 폭 점수
        if prices_low and prices_high:
            avg_low  = sum(prices_low)  / len(prices_low)
            avg_high = sum(prices_high) / len(prices_high)
            price_spread = (avg_high - avg_low) / max(avg_low, 1)
            price_score  = min(price_spread / 3.0, 1.0)   # 3배 이상이면 만점
        else:
            price_score = 0.0

        # SKU 키워드 비중
        sku_keyword_ratio = sku_signal_count / max(len(products), 1)
        sku_raw = 0.5 * price_score + 0.5 * min(sku_keyword_ratio / 0.6, 1.0)
        return sku_raw

    # ── 5. 브랜드 메트릭 통합 ─────────────────────────────────────────────────
    def build_metrics(
        self,
        brand: str,
        category: str,
        products: list[dict],
        trend: dict | None = None,
    ) -> BrandMetrics:
        m = BrandMetrics(brand=brand, category=category)
        m.total_products = len(products)

        # 성장 점수: DataLab 실측값 우선, 미수집 시 상품 기반 프록시 폴백
        growth_raw, recent_avg, prev_avg, growth_rate = \
            self.calc_growth_score_from_trend(trend)
        if growth_raw < 0:   # 폴백 신호
            growth_raw  = self._calc_growth_proxy(products)
            recent_avg  = 0.0
            prev_avg    = 0.0
            growth_rate = 0.0
        m.trend_recent_avg   = recent_avg
        m.trend_prev_avg     = prev_avg
        m.trend_growth_rate  = growth_rate
        m.datalab_available  = trend is not None

        cs_raw, pain_cnt, sampled, top_kws = self.calc_cs_score(products)
        sku_raw = self.calc_sku_score(products)

        m.growth_score_raw      = growth_raw
        m.cs_score_raw          = cs_raw
        m.sku_score_raw         = sku_raw
        m.pain_keyword_count    = pain_cnt
        m.total_reviews_sampled = sampled
        m.pain_keyword_ratio    = pain_cnt / max(sampled, 1)
        m.top_pain_keywords     = top_kws
        m.main_sellers          = self.collect_main_sellers(products)

        # 정규화는 전체 집합 기준으로 나중에 수행
        m.growth_score = growth_raw
        m.cs_score     = cs_raw
        m.sku_score    = sku_raw
        return m

    # ── 6. 판매 채널 집계 (mallName 기반) ────────────────────────────────────
    @staticmethod
    def collect_main_sellers(products: list[dict], top_n: int = 5) -> str:
        """mallName 필드를 집계해 상위 판매몰 문자열 반환 (예: '비비안스토어(4), 11번가(2)')"""
        counts: Counter = Counter()
        for p in products:
            mall = (p.get("mallName") or "").strip()
            if mall:
                counts[mall] += 1
        return ", ".join(f"{k}({v})" for k, v in counts.most_common(top_n))

    # ── 7. Pain Score 계산 ────────────────────────────────────────────────────
    @staticmethod
    def calc_pain_score(m: BrandMetrics) -> float:
        return round(
            0.4 * m.growth_score +
            0.4 * m.cs_score     +
            0.2 * m.sku_score,
            4,
        )


# ─────────────────────────────────────────────────────────────────────────────
# brand.naver.com 택배사 / 3PL 조회
# ─────────────────────────────────────────────────────────────────────────────
_BRAND_NAVER_LINK_RE = re.compile(
    r"https://brand\.naver\.com/[^/]+/products/(\d+)"
)


def _brand_product_ids_from_items(products: list[dict], max_n: int = 5) -> list[str]:
    """
    Shopping API 응답 items에서 brand.naver.com 상품 ID 추출.
    우선순위: link 필드의 brand.naver.com URL > productId 필드
    """
    ids: list[str] = []
    seen: set[str] = set()

    for p in products:
        # link 필드에서 brand.naver.com URL 파싱
        link = p.get("link") or p.get("mallProductUrl") or ""
        m = _BRAND_NAVER_LINK_RE.search(link)
        if m:
            pid = m.group(1)
            if pid not in seen:
                ids.append(pid)
                seen.add(pid)

        if len(ids) >= max_n:
            break

    # brand.naver.com URL이 없으면 productId 폴백
    if not ids:
        for p in products:
            pid = str(p.get("productId") or "").strip()
            if pid and pid not in seen:
                ids.append(pid)
                seen.add(pid)
            if len(ids) >= max_n:
                break

    return ids


def fetch_brand_delivery_info(product_id: str, nid_ses: str, nid_aut: str) -> dict:
    """
    brand.naver.com XHR API로 택배사·3PL 정보 추출 (curl subprocess 사용).

    Python requests는 TLS 핑거프린트(JA3)로 nfront에 차단되므로
    curl을 subprocess로 호출해 브라우저와 동일한 TLS 핸드셰이크를 사용.

    Endpoint:
      GET https://brand.naver.com/n/v1/group-products/{product_id}?channelServiceType=STOREFARM

    Response 매핑:
      products[0].productDeliveryInfo.deliveryCompany.name  → courier_company
      products[0].productLogistics.logisticsCompanyName     → threepl
    """
    url = BRAND_NAVER_PRODUCT_URL.format(product_id=product_id)
    cookie_str = f"NID_AUT={nid_aut}; NID_SES={nid_ses}"
    cmd = [
        "curl", "-s", "--max-time", "12",
        "-H", "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
        "-H", "Accept: application/json, text/plain, */*",
        "-H", "Accept-Language: ko-KR,ko;q=0.9",
        "-H", f"Referer: https://brand.naver.com/",
        "-H", "sec-fetch-dest: empty",
        "-H", "sec-fetch-mode: cors",
        "-H", "sec-fetch-site: same-origin",
        "-H", f"Cookie: {cookie_str}",
        "-w", "\n__STATUS__%{http_code}",
        url,
    ]
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
        raw = result.stdout
        # 마지막 줄에서 HTTP 상태코드 분리
        if "__STATUS__" in raw:
            body, status_str = raw.rsplit("__STATUS__", 1)
            status = int(status_str.strip())
        else:
            body, status = raw, 0

        if status == 200:
            d = json.loads(body)
            # 응답은 products 배열 형태
            first = d.get("products", [{}])[0] if d.get("products") else d
            courier = (
                first.get("productDeliveryInfo", {})
                     .get("deliveryCompany", {})
                     .get("name", "") or ""
            )
            threepl = (
                first.get("productLogistics", {})
                     .get("logisticsCompanyName", "") or ""
            )
            if courier or threepl:
                return {
                    "courier_company": courier or "미확인",
                    "threepl":         threepl or "미확인",
                }
        log.debug("fetch_brand_delivery_info: %s → HTTP %d", product_id, status)
    except (subprocess.TimeoutExpired, json.JSONDecodeError, Exception) as e:
        log.debug("fetch_brand_delivery_info 오류 (%s): %s", product_id, e)
    return {"courier_company": "미확인", "threepl": "미확인"}


_SMARTSTORE_LINK_RE = re.compile(
    r"https://smartstore\.naver\.com/[^/]+/products/(\d+)"
)
_SMARTSTORE_API_PAT = re.compile(r"/i/v2/channels/[^/]+/products/\d+")


def fetch_smartstore_delivery_playwright(
    product_link: str,
    nid_ses: str,
    nid_aut: str,
) -> dict:
    """
    Playwright(headless=False)로 SmartStore 상품 페이지를 로드해
    /i/v2/channels/.../products/... XHR 응답을 인터셉트, 택배사 추출.

    headless=False 이유:
      SmartStore nfront이 headless Chrome의 JS 지표를 탐지해 490(CAPTCHA)를 반환함.
      실제 창을 띄우면 탐지가 되지 않음.

    Returns:
      {"courier_company": str, "threepl": str}
    """
    try:
        from playwright.sync_api import sync_playwright  # 선택적 의존성
    except ImportError:
        log.warning("playwright 미설치 → pip install playwright && playwright install chromium")
        return {"courier_company": "미확인", "threepl": "미확인"}

    captured: dict = {}

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=False)
            ctx = browser.new_context(
                user_agent=(
                    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/124.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1280, "height": 800},
            )
            ctx.add_cookies([
                {"name": "NID_SES", "value": nid_ses, "domain": ".naver.com", "path": "/"},
                {"name": "NID_AUT", "value": nid_aut, "domain": ".naver.com", "path": "/"},
            ])
            page = ctx.new_page()

            def on_response(resp):
                if _SMARTSTORE_API_PAT.search(resp.url) and "withWindow=false" in resp.url:
                    if resp.status == 200:
                        try:
                            captured["data"] = resp.json()
                        except Exception:
                            pass

            page.on("response", on_response)
            try:
                page.goto(product_link, wait_until="networkidle", timeout=35000)
            except Exception:
                pass  # timeout 무시 — 응답 인터셉트는 이미 됐을 수 있음

            browser.close()
    except Exception as e:
        log.debug("fetch_smartstore_delivery_playwright 오류: %s", e)
        return {"courier_company": "미확인", "threepl": "미확인"}

    if "data" in captured:
        di = captured["data"].get("productDeliveryInfo") or {}
        company = di.get("deliveryCompany") or {}
        courier = company.get("name") or ""
        # SmartStore API는 3PL 필드 없음 — deliveryCompany.name 으로 통일
        if courier:
            return {"courier_company": courier, "threepl": "미확인"}

    return {"courier_company": "미확인", "threepl": "미확인"}


def enrich_courier_info(
    metrics_list: list["BrandMetrics"],
    brand_products: dict[str, list[dict]],
    nid_ses: str,
    nid_aut: str,
    max_tries: int = 5,
) -> None:
    """
    상위 브랜드의 택배사·3PL 정보 수집 (in-place).

    경로 1 — brand.naver.com 상품: curl subprocess (TLS 우회)
    경로 2 — SmartStore 상품     : Playwright headless=False (CAPTCHA 우회)
    """
    for m in tqdm(metrics_list, desc="택배사 정보 수집"):
        products = brand_products.get(m.brand, [])
        if not products:
            continue

        # ── 경로 1: brand.naver.com ──────────────────────────────────────────
        brand_ids = _brand_product_ids_from_items(products, max_n=max_tries)
        for pid in brand_ids:
            info = fetch_brand_delivery_info(pid, nid_ses, nid_aut)
            if info["courier_company"] != "미확인" or info["threepl"] != "미확인":
                m.courier_company = info["courier_company"]
                m.threepl         = info["threepl"]
                log.info("  [brand.naver] %s → 택배사=%s / 3PL=%s",
                         m.brand, m.courier_company, m.threepl)
                break
            time.sleep(0.4)

        if m.courier_company != "미확인":
            continue

        # ── 경로 2: SmartStore (Playwright) ──────────────────────────────────
        ss_links: list[str] = []
        seen_ss: set[str] = set()
        for p in products:
            link = p.get("link") or ""
            if _SMARTSTORE_LINK_RE.search(link) and link not in seen_ss:
                ss_links.append(link)
                seen_ss.add(link)
            if len(ss_links) >= max_tries:
                break

        for link in ss_links:
            info = fetch_smartstore_delivery_playwright(link, nid_ses, nid_aut)
            if info["courier_company"] != "미확인":
                m.courier_company = info["courier_company"]
                log.info("  [smartstore] %s → 택배사=%s",
                         m.brand, m.courier_company)
                break


# ─────────────────────────────────────────────────────────────────────────────
# 정규화 유틸
# ─────────────────────────────────────────────────────────────────────────────
def min_max_normalize(values: list[float]) -> list[float]:
    mn, mx = min(values), max(values)
    if mx == mn:
        return [0.5] * len(values)
    return [(v - mn) / (mx - mn) for v in values]


def normalize_metrics(records: list[BrandMetrics]) -> list[BrandMetrics]:
    """성장·CS·SKU 점수를 전체 브랜드 기준으로 min-max 정규화"""
    if not records:
        return records

    g_norm = min_max_normalize([r.growth_score_raw for r in records])
    c_norm = min_max_normalize([r.cs_score_raw     for r in records])
    s_norm = min_max_normalize([r.sku_score_raw    for r in records])

    for r, g, c, s in zip(records, g_norm, c_norm, s_norm):
        r.growth_score = round(g, 4)
        r.cs_score     = round(c, 4)
        r.sku_score    = round(s, 4)
    return records


# ─────────────────────────────────────────────────────────────────────────────
# 파이프라인
# ─────────────────────────────────────────────────────────────────────────────
def run_pipeline(
    categories: list[str] = TARGET_CATEGORIES,
    min_products: int = 3,
    top_n: int = 20,
    output_path: str = OUTPUT_CSV,
    nid_ses: str = "",
    nid_aut: str = "",
) -> pd.DataFrame:
    """전체 분석 파이프라인 실행 후 DataFrame 반환

    Args:
      nid_ses: 브라우저 NID_SES 쿠키 (택배사 정보 수집용, 선택사항)
      nid_aut: 브라우저 NID_AUT 쿠키 (택배사 정보 수집용, 선택사항)
    """
    client   = NaverShoppingClient(NAVER_CLIENT_ID, NAVER_CLIENT_SECRET)
    datalab  = NaverDataLabClient(NAVER_CLIENT_ID, NAVER_CLIENT_SECRET)
    analyzer = BrandAnalyzer(client, datalab)
    all_metrics: list[BrandMetrics] = []
    all_brand_products: dict[str, list[dict]] = {}   # 택배사 조회용 보관

    for category in tqdm(categories, desc="카테고리 분석"):
        brand_products = analyzer.collect_brand_products(category)

        # min_products 필터 먼저 적용
        qualified = {
            b: p for b, p in brand_products.items()
            if len(p) >= min_products
        }
        log.info("  → 브랜드 수: %d (필터 후: %d)", len(brand_products), len(qualified))

        if not qualified:
            continue

        # ── DataLab 배치 트렌드 조회 ──────────────────────────────────────────
        brand_list = list(qualified.keys())
        log.info("  [DataLab] %d개 브랜드 검색량 트렌드 수집 중...", len(brand_list))
        trend_map = datalab.get_trends_all(brand_list)
        hit  = sum(1 for b in brand_list if b in trend_map)
        miss = len(brand_list) - hit
        log.info("  [DataLab] 수집 완료: %d건 성공 / %d건 미수집(중립값 사용)", hit, miss)

        for brand, products in qualified.items():
            trend = trend_map.get(brand)   # None이면 중립값(0.5) 적용
            m = analyzer.build_metrics(brand, category, products, trend=trend)
            all_metrics.append(m)
            all_brand_products[brand] = products

    if not all_metrics:
        log.warning("분석 가능한 브랜드 데이터가 없습니다.")
        return pd.DataFrame()

    # 정규화
    all_metrics = normalize_metrics(all_metrics)

    # Pain Score 계산 후 정렬
    for m in all_metrics:
        m.pain_score = BrandAnalyzer.calc_pain_score(m)

    all_metrics.sort(key=lambda x: x.pain_score, reverse=True)
    top_brands = all_metrics[:top_n]

    # ── 택배사 / 3PL 정보 수집 (쿠키 제공 시) ────────────────────────────────
    if nid_ses and nid_aut:
        log.info("[배송정보] brand.naver.com API로 상위 %d개 브랜드 택배사 조회 시작", len(top_brands))
        enrich_courier_info(top_brands, all_brand_products, nid_ses, nid_aut)
    else:
        log.info(
            "[배송정보] NID_SES/NID_AUT 미제공 → courier_company/threepl = '미확인'\n"
            "  택배사 정보가 필요하면 --nid-ses, --nid-aut 옵션으로 브라우저 쿠키를 전달하세요."
        )

    # ── CSV 저장 ──────────────────────────────────────────────────────────────
    fieldnames = list(asdict(top_brands[0]).keys())
    with open(output_path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for m in top_brands:
            writer.writerow(asdict(m))

    log.info("✅ 결과 저장 완료: %s (%d개 브랜드)", output_path, len(top_brands))

    df = pd.DataFrame([asdict(m) for m in top_brands])
    return df


# ─────────────────────────────────────────────────────────────────────────────
# 결과 리포트 출력
# ─────────────────────────────────────────────────────────────────────────────
def print_report(df: pd.DataFrame) -> None:
    if df.empty:
        print("분석 결과가 없습니다.")
        return

    print("\n" + "═" * 70)
    print("  네이버 쇼핑 브랜드 Pain Score 리포트")
    print(f"  생성일시: {datetime.now().strftime('%Y-%m-%d %H:%M')}")
    print("═" * 70)
    print(f"{'순위':<4} {'브랜드':<16} {'카테고리':<14} {'성장':>6} {'CS':>6} {'SKU':>6} {'PAIN':>7}")
    print("─" * 70)

    for rank, (_, row) in enumerate(df.iterrows(), 1):
        print(
            f"{rank:<4} {row['brand']:<16} {row['category']:<14} "
            f"{row['growth_score']:>6.3f} {row['cs_score']:>6.3f} "
            f"{row['sku_score']:>6.3f} {row['pain_score']:>7.4f}"
        )

    print("─" * 70)
    print(f"\n Pain Score = 성장속도×0.4 + CS문제×0.4 + SKU복잡도×0.2")

    # 상위 3개 상세 출력
    print("\n[ Top 3 브랜드 상세 ]\n")
    for _, row in df.head(3).iterrows():
        datalab_tag = "(DataLab 실측)" if row.get("datalab_available") else "(중립값)"
        print(f"  브랜드: {row['brand']}  ({row['category']})")
        print(f"    Pain Score     : {row['pain_score']:.4f}")
        print(f"    성장 점수      : {row['growth_score']:.4f}  {datalab_tag}")
        print(f"      검색량 이전   : {row.get('trend_prev_avg', 0):.2f}")
        print(f"      검색량 최근   : {row.get('trend_recent_avg', 0):.2f}")
        print(f"      검색량 증가율 : {row.get('trend_growth_rate', 0):+.1%}")
        print(f"    CS 점수        : {row['cs_score']:.4f}")
        print(f"    SKU 점수       : {row['sku_score']:.4f}")
        print(f"    Pain 키워드    : {row['top_pain_keywords'] or '없음'}")
        print(f"    상품 수        : {row['total_products']}")
        print(f"    주요 판매몰    : {row.get('main_sellers') or '미확인'}")
        print(f"    택배사         : {row.get('courier_company', '미확인')}")
        print(f"    3PL            : {row.get('threepl', '미확인')}")
        print()
    print("═" * 70)


# ─────────────────────────────────────────────────────────────────────────────
# 엔트리포인트
# ─────────────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="네이버 쇼핑 브랜드 Pain Score 분석")
    parser.add_argument("--categories", nargs="*", default=TARGET_CATEGORIES,
                        help="분석할 카테고리 목록 (기본값: 7개 카테고리)")
    parser.add_argument("--top", type=int, default=20,
                        help="상위 N개 브랜드 출력 (기본값: 20)")
    parser.add_argument("--min-products", type=int, default=3,
                        help="최소 상품 수 필터 (기본값: 3)")
    parser.add_argument("--output", default=OUTPUT_CSV,
                        help=f"출력 CSV 경로 (기본값: {OUTPUT_CSV})")
    parser.add_argument("--nid-ses", default="",
                        help="브라우저 NID_SES 쿠키값 (택배사/3PL 조회용, 선택사항)")
    parser.add_argument("--nid-aut", default="",
                        help="브라우저 NID_AUT 쿠키값 (택배사/3PL 조회용, 선택사항)")
    args = parser.parse_args()

    df = run_pipeline(
        categories=args.categories,
        min_products=args.min_products,
        top_n=args.top,
        output_path=args.output,
        nid_ses=args.nid_ses,
        nid_aut=args.nid_aut,
    )
    print_report(df)
