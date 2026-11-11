# 성북 세이프패스 · 공공데이터포털 · 서울 열린데이터광장 API 자료를 받아 docs/답변참고문서 에 .md 로 저장한다
# 실행: team3_project 폴더에서 C:\김경민\h_claude\세이프패스_v1\python\python.exe tools\공공데이터_받기.py
# 키: .env 의 DATA_GO_KR_KEY 또는 dataGoKrKey (공공데이터포털), seoulOpenDataKey (서울 열린데이터광장) — 키는 화면 · 파일에 적지 않는다
import json
import sys
from datetime import date
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "docs" / "답변참고문서"
TODAY = date.today().isoformat()

# (저장 파일 이름, 문서 제목, API 주소, 성북구만 고를 칸 이름 또는 None)
APIS = [
    ("소상공인시장진흥공단_백년가게성북구_2026", "백년가게 (성북구)",
     "https://api.odcloud.kr/api/15132695/v1/uddi:706576c0-3d19-4e32-96be-d446b2b76bab", "주소"),
    ("성북구_동주민센터현황_2023", "성북구 동주민센터",
     "https://api.odcloud.kr/api/15040310/v1/uddi:3c139e24-2658-4b04-b4bd-8a84a66b2b06", None),
    ("성북구_종량제봉투판매소_2023", "성북구 종량제 봉투 판매소",
     "https://api.odcloud.kr/api/15113116/v1/uddi:1076c507-c35f-481f-b33c-e7262fdfaefe", None),
    ("성북구_문화와축제현황_2026", "성북구 문화와 축제",
     "https://api.odcloud.kr/api/15162450/v1/uddi:ed84986b-7901-4625-aca9-a70e2c3d3e50", None),
    ("성북구_문화시설정보_2026", "성북구 문화시설",
     "https://api.odcloud.kr/api/15064749/v1/uddi:28b48288-89f0-4e02-95aa-e559a694f5b8", None),
    ("성북구_문화재현황_2021", "성북구 문화재",
     "https://api.odcloud.kr/api/15040337/v1/uddi:767cfb2d-4b13-404e-b230-9c3da73cef2e", None),
]


DROP_COLS = {"소유자", "관리자(단체)", "대표자", "대표자명"}


def load_env():
    env = ROOT / ".env"
    out = {}
    if env.exists():
        for line in env.read_text(encoding="utf-8-sig").splitlines():
            s = line.strip()
            if s and not s.startswith("#") and "=" in s:
                k, v = s.split("=", 1)
                out[k.strip()] = v.strip().strip('"').strip("'")
    return out


ENV = load_env()


def load_key():
    return ENV.get("DATA_GO_KR_KEY") or ENV.get("dataGoKrKey", "")


# ---------- 서울 열린데이터광장 (키 하나 + 서비스 이름) ----------
SEOUL = "http://openapi.seoul.go.kr:8088/{key}/json/{svc}/{a}/{b}/"
# 숙박 인허가 4종: 영업/정상만, 답변에 필요한 칸만 (전화번호 · 면적 · 종사자 수 등은 빼고)
LODGING = [
    ("seoulMinbakApi", "LOCALDATA_031104_SB", "외국인관광도시민박업"),
    ("seoulLodgingApi", "LOCALDATA_031103_SB", "숙박업"),
    ("seoulHanokApi", "LOCALDATA_031106_SB", "한옥체험업"),
    ("seoulTourHotelApi", "LOCALDATA_031101_SB", "관광숙박업"),
]
LODGING_COLS = [("BPLCNM", "사업장명"), ("ENGSTNTRNMNM", "영문상호명"), ("RDNWHLADDR", "도로명주소"), ("APVPERMYMD", "인허가일자")]
# 문화행사: 출연자 실명 · 문의 연락처 · 이미지는 뺀다
EVENT_COLS = [("CODENAME", "분류"), ("TITLE", "공연/행사명"), ("PLACE", "장소"), ("STRTDATE", "시작일"), ("END_DATE", "종료일"),
              ("PRO_TIME", "행사시간"), ("USE_TRGT", "이용대상"), ("IS_FREE", "유무료"), ("USE_FEE", "이용요금"),
              ("HMPG_ADDR", "문화포털상세URL")]


def seoul_all(key, svc):
    rows, a = [], 1
    while True:
        url = SEOUL.format(key=key, svc=svc, a=a, b=a + 999)
        with urlopen(Request(url, headers={"User-Agent": "SafePass-team3"}), timeout=30) as r:
            body = json.loads(r.read().decode("utf-8"))
        part = body.get(svc)
        if not part:
            raise RuntimeError(body.get("RESULT", body))
        rows += part.get("row", [])
        if len(rows) >= part.get("list_total_count", 0) or not part.get("row"):
            return rows
        a += 1000


def write_table(name, title, src, rows, cols):
    cell = lambda v: str("" if v is None else v).replace("|", "/").replace("\n", " ").strip()
    lines = [f"# {title}", "", f"- 출처: {src}", f"- 받은 날: {TODAY}", f"- 건수: {len(rows)}", "", "## 목록", "",
             "| " + " | ".join(k for _, k in cols) + " |", "|" + "---|" * len(cols)]
    lines += ["| " + " | ".join(cell(r.get(c)) for c, _ in cols) + " |" for r in rows]
    (OUT / f"{name}.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def seoul_main():
    key = ENV.get("seoulOpenDataKey", "")
    if not key:
        print("[건너뜀] 서울 열린데이터광장: .env 에 seoulOpenDataKey 가 없습니다")
        return
    try:
        ev = seoul_all(key, ENV.get("seoulCultureEventApi", "culturalEventInfo"))
        ev = [r for r in ev if r.get("GUNAME") == "성북구" and str(r.get("END_DATE", ""))[:10] >= TODAY]
        for r in ev:
            r["STRTDATE"], r["END_DATE"] = str(r.get("STRTDATE", ""))[:10], str(r.get("END_DATE", ""))[:10]
        ev.sort(key=lambda r: r["STRTDATE"])
        write_table("서울시_문화행사정보성북구_2026", "서울시 문화행사 (성북구 · 진행 중 · 예정)",
                    "서울 열린데이터광장 서울시 문화행사 정보 (OA-15486)", ev, EVENT_COLS)
        print(f"[완료] 문화행사 성북구: {len(ev)}건")
    except Exception as e:
        print(f"[실패] 문화행사: {e}")
    for env_name, svc, kind in LODGING:
        try:
            rows = [r for r in seoul_all(key, ENV.get(env_name, svc)) if r.get("TRDSTATENM") == "영업/정상"]
            write_table(f"성북구_{kind}인허가_2026", f"성북구 {kind} (영업 중)",
                        f"서울 열린데이터광장 서울시 성북구 {kind} 인허가 정보", rows, LODGING_COLS)
            print(f"[완료] {kind}: {len(rows)}건")
        except Exception as e:
            print(f"[실패] {kind}: {e}")


def fetch_all(url, key):
    rows, page = [], 1
    while True:
        q = urlencode({"serviceKey": key, "page": page, "perPage": 1000, "returnType": "JSON"})
        with urlopen(Request(f"{url}?{q}", headers={"User-Agent": "SafePass-team3"}), timeout=20) as r:
            body = json.loads(r.read().decode("utf-8"))
        data = body.get("data", [])
        rows += data
        if len(rows) >= body.get("totalCount", 0) or not data:
            return rows
        page += 1


def to_md(title, name, url, rows):
    cols = list(rows[0].keys()) if rows else []
    cell = lambda v: str("" if v is None else v).replace("|", "/").replace("\n", " ")
    lines = [f"# {title}", "",
             f"- 출처: 공공데이터포털 ({url.split('/api/')[1].split('/')[0]}번)",
             f"- 받은 날: {TODAY}", f"- 건수: {len(rows)}", "",
             "## 목록", "",
             "| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    lines += ["| " + " | ".join(cell(r.get(c)) for c in cols) + " |" for r in rows]
    (OUT / f"{name}.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main():
    seoul_main()
    key = load_key()
    if not key:
        print("[건너뜀] 공공데이터포털: .env 에 DATA_GO_KR_KEY (또는 dataGoKrKey) 가 없습니다")
        sys.exit(0)
    for name, title, url, gu_col in APIS:
        try:
            rows = fetch_all(url, key)
        except Exception as e:
            print(f"[실패] {title}: {e}  (활용신청이 승인됐는지 확인)")
            continue
        if gu_col:
            raw = rows
            # 주소 칸 이름이 데이터마다 달라서(주소 · 업체주소 등) '주소'가 들어간 칸을 모두 본다
            rows = [r for r in rows if any("성북구" in str(v) for k, v in r.items() if gu_col in k)]
            if raw and not rows:
                print(f"  [확인용] {title} 원본 {len(raw)}건 · 칸 이름: {list(raw[0].keys())}")
                print(f"  [확인용] 첫 줄: {raw[0]}")
        # 개인 실명이 들어 있는 칸은 뺀다 (문화재 소유자 · 관리자 등)
        rows = [{k: v for k, v in r.items() if k not in DROP_COLS} for r in rows]
        to_md(title, name, url, rows)
        print(f"[완료] {title}: {len(rows)}건 → docs/답변참고문서/{name}.md")


if __name__ == "__main__":
    main()
