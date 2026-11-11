# 성북 세이프패스 서버 기능 모음 (공용)
# - 내 PC: tools/로컬서버.py 가 이 파일의 respond() 를 부른다
# - Vercel: api/<이름>.py 가 같은 respond() 를 부른다
# 키는 환경변수(.env / Vercel Environment Variables)에서만 읽는다. 브라우저로는 카카오 JavaScript 키만 보낸다.
import json
import os
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import urlencode, quote
from urllib.request import Request, urlopen

API_DIR = Path(__file__).resolve().parent
ROOT = API_DIR.parent
KST = timezone(timedelta(hours=9))
UA = {"User-Agent": "SafePass-team3 (Hansung Univ. capstone)"}


def load_dotenv():
    """내 PC에서만: team3_project/.env 를 환경변수로 (이미 있는 값은 그대로)"""
    p = ROOT / ".env"
    if not p.exists():
        return
    for line in p.read_text(encoding="utf-8-sig").splitlines():
        s = line.strip()
        if s and not s.startswith("#") and "=" in s:
            k, v = s.split("=", 1)
            os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))


def env(name, default=""):
    return os.environ.get(name, default).strip()


# ---------- 작은 저장소 (같은 요청을 다시 부르지 않게) ----------
_cache = {}
_lock = threading.Lock()


def cached(key, ttl, fn):
    now = time.time()
    with _lock:
        hit = _cache.get(key)
        if hit and now - hit[0] < ttl:
            return hit[1]
    val = fn()
    if isinstance(val, dict) and val.get("ok"):
        with _lock:
            _cache[key] = (now, val)
    return val


def get_json(url, timeout=12):
    with urlopen(Request(url, headers=UA), timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


# ---------- 화면 설정 ----------
def config(q):
    return {"ok": True, "kakaoJsKey": env("javascriptKey"), "hasDataKey": bool(env("DATA_GO_KR_KEY")),
            "hasSeoulKey": bool(env("seoulOpenDataKey"))}


# ---------- 날씨: 기상청 단기예보 ----------
NX, NY = 60, 127   # 성북구 한성대입구역 · 성북동 일대 격자


def _kma_base(now):
    t = now - timedelta(minutes=15)
    for h in (23, 20, 17, 14, 11, 8, 5, 2):
        if t.hour >= h:
            return t.strftime("%Y%m%d"), f"{h:02d}00"
    return (t - timedelta(days=1)).strftime("%Y%m%d"), "2300"


def weather(q):
    key = env("DATA_GO_KR_KEY")
    if not key:
        return {"ok": False, "reason": ".env 에 DATA_GO_KR_KEY 가 없습니다"}

    def go():
        now = datetime.now(KST)
        bd, bt = _kma_base(now)
        base = env("kmaShortForecastApi", "https://apis.data.go.kr/1360000/VilageFcstInfoService_2.0/getVilageFcst")
        url = base + "?" + urlencode({"serviceKey": key, "pageNo": 1, "numOfRows": 1000, "dataType": "JSON",
                                       "base_date": bd, "base_time": bt, "nx": NX, "ny": NY})
        try:
            items = get_json(url)["response"]["body"]["items"]["item"]
        except Exception as e:
            return {"ok": False, "reason": f"기상청 호출 실패: {e}"}
        cur, hours = now.strftime("%Y%m%d%H"), {}
        for it in items:
            k = it["fcstDate"] + it["fcstTime"][:2]
            if k >= cur:
                hours.setdefault(k, {"h": int(it["fcstTime"][:2])})[it["category"]] = it["fcstValue"]
        out = []
        for k in sorted(hours)[:18]:
            v = hours[k]
            if "TMP" not in v:
                continue
            pcp = str(v.get("PCP", "강수없음"))
            out.append({"h": v["h"], "tmp": float(v["TMP"]), "sky": int(v.get("SKY", 1)), "pty": int(v.get("PTY", 0)),
                        "pop": int(v.get("POP", 0)), "pcp": 0 if "없음" in pcp else pcp})
        if not out:
            return {"ok": False, "reason": "예보 자료가 비어 있습니다"}
        return {"ok": True, "base": f"{bd} {bt}", "nx": NX, "ny": NY, "hours": out}
    return cached("weather", 1800, go)


# ---------- 미세먼지: 에어코리아 측정소별 실시간 측정정보 (측정소 「성북구」, 길음2동) ----------
def dust(q):
    key = env("DATA_GO_KR_KEY")
    if not key:
        return {"ok": False, "reason": ".env 에 DATA_GO_KR_KEY 가 없습니다"}

    def go():
        base = env("airKoreaApi", "https://apis.data.go.kr/B552584/ArpltnInforInqireSvc/getMsrstnAcctoRltmMesureDnsty")
        url = base + "?" + urlencode({"serviceKey": key, "returnType": "json", "numOfRows": 24, "pageNo": 1,
                                       "stationName": "성북구", "dataTerm": "DAILY", "ver": "1.0"})
        try:
            items = get_json(url)["response"]["body"]["items"]
        except Exception as e:
            return {"ok": False, "reason": f"에어코리아 호출 실패 (활용신청 승인 여부 확인): {e}"}
        num = lambda v: int(float(v)) if str(v).replace(".", "", 1).isdigit() else None
        hours = []
        for it in reversed(items):          # 오래된 것 → 최근
            t = str(it.get("dataTime", ""))
            p10, p25 = num(it.get("pm10Value")), num(it.get("pm25Value"))
            if p10 is None:
                continue
            hours.append({"t": t, "h": int(t[11:13]) if len(t) >= 13 else 0, "pm10": p10, "pm25": p25 if p25 is not None else 0})
        if not hours:
            return {"ok": False, "reason": "측정값이 비어 있습니다 (점검 중일 수 있음)"}
        return {"ok": True, "station": "성북구", "latest": hours[-1], "hours": hours[-18:], "src": "에어코리아 실시간 측정 (성북구 측정소)"}
    return cached("dust", 1800, go)


# ---------- 공공데이터포털 파일데이터 API (odcloud) ----------
SETS = {
    # 이름: (환경변수, 성북구만 고를 칸 이름에 들어간 글자, 남길 칸)
    "baengnyeon": ("baengnyeonShopApi", "주소", ["업체명", "업체주소"]),
    "center": ("sbCommunityCenterApi", None, ["주민센터명", "주소", "전화번호", "위도", "경도", "행정동"]),
    "bagshop": ("sbTrashBagShopApi", None, ["판매소명", "주소", "동이름"]),
    "festival": ("sbFestivalApi", None, ["행사명", "개최 예정일", "시작시간", "종료시간", "행정동명", "행사 주요 내용", "유무료 여부", "사전 신청 필요 여부"]),
}


def data(q):
    name = (q.get("set") or [""])[0]
    if name not in SETS:
        return {"ok": False, "reason": "set 은 " + ", ".join(SETS)}
    env_name, gu_col, keep = SETS[name]
    key, base = env("DATA_GO_KR_KEY"), env(env_name)
    if not key or not base.startswith("http"):
        return {"ok": False, "reason": f".env 에 DATA_GO_KR_KEY 와 {env_name}(서비스 주소)가 필요합니다"}

    def go():
        rows, page = [], 1
        try:
            while page <= 20:
                body = get_json(base + "?" + urlencode({"serviceKey": key, "page": page, "perPage": 1000, "returnType": "JSON"}))
                part = body.get("data", [])
                rows += part
                if not part or len(rows) >= body.get("totalCount", 0):
                    break
                page += 1
        except Exception as e:
            return {"ok": False, "reason": f"공공데이터포털 호출 실패: {e}"}
        if gu_col:
            rows = [r for r in rows if any("성북구" in str(v) for k, v in r.items() if gu_col in k)]
        rows = [{k: r.get(k) for k in keep if k in r} for r in rows]   # 개인정보가 섞일 수 있는 칸은 보내지 않음
        return {"ok": True, "set": name, "count": len(rows), "rows": rows, "src": f"공공데이터포털 {env_name}"}
    return cached("data:" + name, 12 * 3600, go)


# ---------- 서울시 문화행사 (서울 열린데이터광장) ----------
def events(q):
    key, svc = env("seoulOpenDataKey"), env("seoulCultureEventApi", "culturalEventInfo")
    if not key:
        return {"ok": False, "reason": ".env 에 seoulOpenDataKey 가 없습니다"}

    def page(a):
        url = f"http://openapi.seoul.go.kr:8088/{quote(key)}/json/{svc}/{a}/{a + 999}/"
        return get_json(url, timeout=20).get(svc, {})

    def go():
        try:
            first = page(1)
            total = int(first.get("list_total_count", 0))
            rows = list(first.get("row", []))
            starts = list(range(1001, total + 1, 1000))
            with ThreadPoolExecutor(max_workers=8) as ex:     # 약 2만 건을 1,000건씩 나눠 동시에 받음
                for part in ex.map(page, starts):
                    rows += part.get("row", [])
        except Exception as e:
            return {"ok": False, "reason": f"서울 열린데이터광장 호출 실패: {e}"}
        today = datetime.now(KST).strftime("%Y-%m-%d")
        soon = (datetime.now(KST) + timedelta(days=21)).strftime("%Y-%m-%d")
        out, seoul = [], []
        for r in rows:
            end = str(r.get("END_DATE", ""))[:10]
            start = str(r.get("STRTDATE", ""))[:10]
            # 서울 전체 축제: 분류가 「축제」이고 지금 ~ 3주 안에 열리는 것 (성북구 밖)
            if r.get("GUNAME") != "성북구" and "축제" in str(r.get("CODENAME", "")) and end >= today and start <= soon:
                try:
                    la, lo = float(r.get("LAT") or 0), float(r.get("LOT") or 0)
                except ValueError:
                    la = lo = 0
                seoul.append({"title": r.get("TITLE", ""), "cat": r.get("CODENAME", ""), "gu": r.get("GUNAME", ""), "start": start, "end": end,
                              "time": r.get("PRO_TIME", ""), "place": r.get("PLACE", ""), "fee": r.get("USE_FEE", ""), "free": r.get("IS_FREE", ""),
                              "url": r.get("HMPG_ADDR", ""), "lat": la if 37 < la < 38 else None, "lng": lo if 126 < lo < 128 else None})
            if r.get("GUNAME") != "성북구" or end < today:
                continue
            try:
                lat, lng = float(r.get("LAT") or 0), float(r.get("LOT") or 0)
            except ValueError:
                lat = lng = 0
            # 출연자 실명(PLAYER) · 문의 연락처(INQUIRY)는 보내지 않음
            out.append({"title": r.get("TITLE", ""), "cat": r.get("CODENAME", ""), "start": str(r.get("STRTDATE", ""))[:10], "end": end,
                        "time": r.get("PRO_TIME", ""), "place": r.get("PLACE", ""), "fee": r.get("USE_FEE", ""),
                        "free": r.get("IS_FREE", ""), "url": r.get("HMPG_ADDR", ""),
                        "lat": lat if 37 < lat < 38 else None, "lng": lng if 126 < lng < 128 else None})
        out.sort(key=lambda e: e["start"])
        seoul.sort(key=lambda e: (e["start"] > today, e["start"]))   # 진행 중 먼저, 그다음 가까운 날짜
        return {"ok": True, "count": len(out), "events": out, "seoul": seoul[:12], "src": "서울 열린데이터광장 서울시 문화행사 정보 (OA-15486)"}
    return cached("events", 6 * 3600, go)


# ---------- 한국관광공사 외국어 관광정보 (숙소 근처) ----------
KTO = {  # 화면 언어: (환경변수, 기본 주소, {콘텐츠 종류: 이름})
    "en": ("ktoEngTourApi", "https://apis.data.go.kr/B551011/EngService2", {"76": "spot", "78": "culture", "85": "festival", "82": "food", "79": "shop"}),
    "ja": ("ktoJpnTourApi", "https://apis.data.go.kr/B551011/JpnService2", {"76": "spot", "78": "culture", "85": "festival", "82": "food", "79": "shop"}),
    "zh": ("ktoChsTourApi", "https://apis.data.go.kr/B551011/ChsService2", {"76": "spot", "78": "culture", "85": "festival", "82": "food", "79": "shop"}),
    "ko": ("ktoKorTourApi", "https://apis.data.go.kr/B551011/KorService2", {"12": "spot", "14": "culture", "15": "festival", "39": "food", "38": "shop"}),
}


def tour(q):
    lang = (q.get("lang") or ["en"])[0]
    if lang not in KTO:
        lang = "en"
    try:
        lat, lng = float(q["lat"][0]), float(q["lng"][0])
    except Exception:
        return {"ok": False, "reason": "lat, lng 가 필요합니다"}
    key = env("DATA_GO_KR_KEY")
    env_name, default, kinds = KTO[lang]
    base = env(env_name) if env(env_name).startswith("http") else default
    if not key:
        return {"ok": False, "reason": ".env 에 DATA_GO_KR_KEY 가 없습니다"}

    def go():
        url = base + "/locationBasedList2?" + urlencode({
            "serviceKey": key, "MobileOS": "ETC", "MobileApp": "SafePass", "_type": "json",
            "mapX": f"{lng:.6f}", "mapY": f"{lat:.6f}", "radius": 2000, "arrange": "E", "numOfRows": 40, "pageNo": 1})
        try:
            body = get_json(url)
            items = body["response"]["body"]["items"]
            items = items.get("item", []) if isinstance(items, dict) else []
        except Exception as e:
            return {"ok": False, "reason": f"한국관광공사 호출 실패: {e}"}
        out = []
        for it in items if isinstance(items, list) else [items]:
            kind = kinds.get(str(it.get("contenttypeid")))
            if not kind:
                continue
            try:
                ilat, ilng = float(it.get("mapy")), float(it.get("mapx"))
            except (TypeError, ValueError):
                continue
            out.append({"id": it.get("contentid"), "kind": kind, "title": it.get("title", ""), "addr": it.get("addr1", ""),
                        "lat": ilat, "lng": ilng, "dist": float(it.get("dist") or 0), "img": it.get("firstimage", "")})
        return {"ok": True, "lang": lang, "count": len(out), "items": out, "src": f"한국관광공사 {env_name}"}
    return cached(f"tour:{lang}:{lat:.4f}:{lng:.4f}", 12 * 3600, go)


# ---------- AI 짧은 번역 (행사 이름 · 가게 이름 → 영 · 중 · 일) ----------
# 기획서 원칙: 이름 · 주소 · 날짜는 원래 데이터 그대로 두고, AI 번역은 옆에 「AI translation」으로만 붙인다.
_tr = {}
LANG_NAME = {"en": "English", "zh": "Simplified Chinese", "ja": "Japanese"}


def _post_json(url, payload, headers, timeout=20):
    req = Request(url, data=json.dumps(payload).encode("utf-8"), headers={**UA, "Content-Type": "application/json", **headers})
    with urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


_models = {}


def _pick_groq(k):
    """이 키로 쓸 수 있는 Groq 모델 중 하나 (모델 이름이 자주 바뀌어서 목록에서 고른다)"""
    if env("GROQ_MODEL"):
        return env("GROQ_MODEL")
    if "groq" not in _models:
        ids = [m["id"] for m in get_json_auth("https://api.groq.com/openai/v1/models", k).get("data", []) if m.get("active", True)]
        ids = [i for i in ids if not any(x in i for x in ("whisper", "tts", "guard", "embed", "playai", "orpheus"))]
        pref = ["llama-3.3-70b", "gpt-oss-120b", "llama-4", "qwen", "gpt-oss-20b", "llama"]
        _models["groq"] = next((i for p in pref for i in ids if p in i), ids[0] if ids else "")
    return _models["groq"]


def _pick_gemini(k):
    if env("GEMINI_MODEL"):
        return env("GEMINI_MODEL")
    if "gemini" not in _models:
        ms = get_json(f"https://generativelanguage.googleapis.com/v1beta/models?key={quote(k)}&pageSize=200").get("models", [])
        ids = [m["name"].split("/")[-1] for m in ms if "generateContent" in m.get("supportedGenerationMethods", [])]
        flash = [i for i in ids if "flash" in i and "lite" not in i and "image" not in i and "tts" not in i and "preview" not in i]
        _models["gemini"] = (flash or ids or [""])[0]
    return _models["gemini"]


def get_json_auth(url, k, timeout=12):
    with urlopen(Request(url, headers={**UA, "Authorization": f"Bearer {k}"}), timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def _ask_ai(prompt):
    """Groq(여러 키 차례로) → 안 되면 Gemini. 결과는 JSON 문자열"""
    errs = []
    for k in [x.strip() for x in env("GROQ_API_KEYS").split(",") if x.strip()]:
        try:
            model = _pick_groq(k)
            body = _post_json("https://api.groq.com/openai/v1/chat/completions", {
                "model": model, "temperature": 0, "response_format": {"type": "json_object"},
                "messages": [{"role": "user", "content": prompt}]}, {"Authorization": f"Bearer {k}"})
            return body["choices"][0]["message"]["content"]
        except Exception as e:
            _models.pop("groq", None)
            errs.append(f"groq({_models.get('groq', '?')}): {e}")
    for k in [x.strip() for x in env("GEMINI_API_KEYS").split(",") if x.strip()]:
        try:
            model = _pick_gemini(k)
            body = _post_json(f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={quote(k)}", {
                "contents": [{"parts": [{"text": prompt}]}],
                "generationConfig": {"temperature": 0, "responseMimeType": "application/json"}}, {})
            return body["candidates"][0]["content"]["parts"][0]["text"]
        except Exception as e:
            _models.pop("gemini", None)
            errs.append(f"gemini: {e}")
    raise RuntimeError("; ".join(errs) or "GROQ_API_KEYS · GEMINI_API_KEYS 가 없습니다")


def ai_models(q):
    """확인용: 지금 고른 모델 이름"""
    out = {"ok": True}
    g = [x.strip() for x in env("GROQ_API_KEYS").split(",") if x.strip()]
    m = [x.strip() for x in env("GEMINI_API_KEYS").split(",") if x.strip()]
    try:
        out["groq"] = _pick_groq(g[0]) if g else "(키 없음)"
    except Exception as e:
        out["groq"] = f"목록 실패: {e}"
    try:
        out["gemini"] = _pick_gemini(m[0]) if m else "(키 없음)"
    except Exception as e:
        out["gemini"] = f"목록 실패: {e}"
    return out


def translate(q):
    lang = (q.get("lang") or ["en"])[0]
    kind = (q.get("kind") or ["event"])[0]
    texts = [t[:150] for t in (q.get("t") or [])][:30]
    if lang not in LANG_NAME or not texts:
        return {"ok": False, "reason": "lang(en/zh/ja) 와 t 가 필요합니다"}
    todo = [t for t in dict.fromkeys(texts) if (lang, kind, t) not in _tr]
    if todo:
        what = ("names of long-running local shops and restaurants; give the romanized name followed by what it is in "
                "parentheses only when the Korean name clearly says it (e.g. 보리밥 = barley rice); never invent facts"
                if kind == "shop" else "titles of cultural events in Seoul; keep bracketed organizer names short")
        prompt = (f"Translate the Korean texts below into {LANG_NAME[lang]} for foreign tourists. They are {what}. "
                  f"Keep each under 14 words. Return JSON: {{\"items\": [ ...same order, same count... ]}}.\n"
                  + json.dumps(todo, ensure_ascii=False))
        try:
            items = json.loads(_ask_ai(prompt)).get("items", [])
        except Exception as e:
            return {"ok": False, "reason": f"AI 번역 실패: {e}"}
        if len(items) != len(todo):
            return {"ok": False, "reason": "AI 번역 개수가 맞지 않습니다"}
        for t, v in zip(todo, items):
            _tr[(lang, kind, t)] = str(v)[:200]
    return {"ok": True, "lang": lang, "items": {t: _tr.get((lang, kind, t), "") for t in texts}, "note": "AI translation"}


# ---------- 도보 경로: 틈길 엔진 → OpenStreetMap ----------
_engine = {"obj": None, "msg": "아직 불러오지 않음"}
_engine_lock = threading.Lock()
_routes = {}
FOOT_URL = "https://routing.openstreetmap.de/routed-foot/route/v1/foot/"


def engine():
    with _engine_lock:
        if _engine["obj"] is None and _engine["msg"] == "아직 불러오지 않음":
            graph = API_DIR / "_data" / "walk_graph_v10_2.json.gz"
            try:
                import sys
                sys.path.insert(0, str(API_DIR))
                from _walk_engine3 import WalkEngine
                _engine["obj"] = WalkEngine(graph)
                _engine["msg"] = "로드됨"
            except Exception as e:
                _engine["msg"] = f"없음 ({e})"
        return _engine["obj"]


def walk(q):
    try:
        a = [float(x) for x in q["from"][0].split(",")]
        b = [float(x) for x in q["to"][0].split(",")]
    except Exception:
        return {"ok": False, "reason": "좌표 형식이 잘못되었습니다"}
    for lat, lng in (a, b):
        if not (37.3 < lat < 37.8 and 126.7 < lng < 127.3):
            return {"ok": False, "reason": "서울 밖 좌표입니다"}
    ck = tuple(round(v, 5) for v in a + b)
    if ck in _routes:
        return _routes[ck]
    eng = engine()
    if eng is not None:
        try:
            with _engine_lock:
                r = eng.compare4(a[1], a[0], b[1], b[0])
            if "error" not in r and max(r.get("snap_m") or [0]) < 300:
                rt = r.get("accessible") or r.get("shortest")   # 틈길 '편한 길(최소시간)'
                out = {"ok": True, "src": "teumgil", "dist": round(rt["distance_m"]), "min": rt.get("minutes"),
                       "path": [[p[1], p[0]] for p in rt["path"]]}
                _routes[ck] = out
                return out
        except Exception:
            pass
    try:
        body = get_json(f"{FOOT_URL}{a[1]:.6f},{a[0]:.6f};{b[1]:.6f},{b[0]:.6f}?overview=full&geometries=geojson", timeout=8)
        rt = body["routes"][0]
        out = {"ok": True, "src": "osm", "dist": round(rt["distance"]), "path": [[c[1], c[0]] for c in rt["geometry"]["coordinates"]]}
    except Exception as e:
        return {"ok": False, "reason": f"도보 경로 호출 실패: {e}"}
    if len(_routes) > 300:
        _routes.clear()
    _routes[ck] = out
    return out


# ---------- 안전 시설 (SOS 패널): 약국 · 응급실 · AED · 민방위 대피시설 ----------
# 공공데이터포털 활용신청이 필요 (승인 전에는 ok:false → 화면이 카카오 장소검색 · 안내로 대신함)
NMC = "https://apis.data.go.kr/B552657"
SAFETY = {
    # 이름: (주소, 기본 파라미터)
    "pharm": (env("nmcPharmacyApi", NMC + "/ErmctInsttInfoInqireService/getParmacyListInfoInqire"), {"Q0": "서울특별시", "Q1": "성북구", "numOfRows": "500"}),
    "er": (env("nmcEmergencyApi", NMC + "/ErmctInfoInqireService/getEgytListInfoInqire"), {"Q0": "서울특별시", "numOfRows": "200"}),
    "aed": (env("nmcAedApi", NMC + "/AEDInfoInqireService/getEgytAedManageInfoInqire"), {"Q0": "서울특별시", "Q1": "성북구", "numOfRows": "1000"}),
    "shelter": (env("civilShelterApi", "https://apis.data.go.kr/1741000/civil_defense_shelter_info"), {"cond[ROAD_NM_WHOL_ADDR::LIKE]": "성북구", "numOfRows": "100", "returnType": "json"}),
}


def _items(body):
    """XML/JSON 어느 쪽이 와도 item 목록으로"""
    import xml.etree.ElementTree as ET
    body = body.strip()
    if body.startswith("{"):
        j = json.loads(body)
        # 흔한 모양: response.body.items.item / body.items / items
        for path in (("response", "body", "items", "item"), ("response", "body", "items"), ("body", "items", "item"), ("body", "items"), ("items",)):
            cur = j
            for k in path:
                cur = cur.get(k) if isinstance(cur, dict) else None
                if cur is None:
                    break
            if cur is not None:
                return cur if isinstance(cur, list) else [cur]
        return []
    root = ET.fromstring(body)
    code = root.findtext(".//resultCode") or root.findtext(".//returnReasonCode")
    if code and code not in ("00", "0", "0000"):
        raise RuntimeError(root.findtext(".//resultMsg") or root.findtext(".//returnAuthMsg") or code)
    return [{c.tag: (c.text or "").strip() for c in it} for it in root.iter("item")]


def _num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def safety(q):
    name = (q.get("set") or [""])[0]
    if name not in SAFETY:
        return {"ok": False, "reason": "set = pharm | er | aed | shelter"}
    key = env("DATA_GO_KR_KEY")
    if not key:
        return {"ok": False, "reason": ".env 에 DATA_GO_KR_KEY 가 없습니다"}
    url, params = SAFETY[name]

    def go():
        try:
            full = url + "?" + urlencode({"serviceKey": key, "pageNo": "1", **params})
            with urlopen(Request(full, headers=UA), timeout=5) as r:   # 5초 안에 안 오면 저장본 · 카카오로
                raw = r.read().decode("utf-8", "replace")
            items = _items(raw)
        except Exception as e:
            return {"ok": False, "reason": f"{name} 호출 실패 (활용신청 · 승인 확인): {e}"}
        out = []
        for it in items:
            lat = _num(it.get("wgs84Lat") or it.get("lat") or it.get("LAT"))
            lng = _num(it.get("wgs84Lon") or it.get("lon") or it.get("LOT") or it.get("lng"))
            row = {"name": it.get("dutyName") or it.get("org") or it.get("FCLT_NM") or "",
                   "addr": it.get("dutyAddr") or it.get("buildAddress") or it.get("ROAD_NM_WHOL_ADDR") or "",
                   "tel": it.get("dutyTel1") or it.get("clerkTel") or "",
                   "place": it.get("buildPlace") or it.get("FCLT_SE_NM") or "",
                   "lat": lat if lat and 37 < lat < 38 else None, "lng": lng if lng and 126 < lng < 128 else None}
            if name == "pharm":   # 요일별 영업시간 (1=월 … 7=일, 8=공휴일), 「0900」 모양
                row["hours"] = {str(d): [it.get(f"dutyTime{d}s", ""), it.get(f"dutyTime{d}c", "")] for d in range(1, 9) if it.get(f"dutyTime{d}s")}
            if name == "er" and "성북" not in row["addr"] and "종로" not in row["addr"]:
                continue
            if name == "shelter" and not row["lat"]:
                row["x"], row["y"] = _num(it.get("XCRD") or it.get("X")), _num(it.get("YCRD") or it.get("Y"))   # EPSG:5174 — 승인 뒤 필드 확인 필요
            out.append(row)
        return {"ok": True, "count": len(out), "rows": out, "src": {"pharm": "국립중앙의료원 전국 약국 정보", "er": "국립중앙의료원 전국 응급의료기관 정보",
                "aed": "국립중앙의료원 전국 자동심장충격기(AED) 정보", "shelter": "행정안전부 민방위대피시설"}[name]}

    return cached("safety:" + name, 6 * 3600, go)


ROUTES = {
    "safety": safety,"config": config, "weather": weather, "dust": dust, "translate": translate, "models": ai_models, "data": data, "events": events, "tour": tour, "walk": walk}


def respond(name, q):
    fn = ROUTES.get(name)
    if not fn:
        return 404, {"ok": False, "reason": "없는 기능입니다"}
    try:
        return 200, fn(q)
    except Exception as e:
        return 500, {"ok": False, "reason": f"서버 오류: {e}"}
