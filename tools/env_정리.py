# .env 정리: 키 값은 그대로 옮기고, 중복을 없애고, 서비스 주소 · 이름을 채운다. 세이프패스 config.json 의 카카오 키도 모은다.
# 실행: team3_project 폴더에서  C:\김경민\h_claude\세이프패스_v1\python\python.exe tools\env_정리.py
# 원래 .env 는 .env.백업_날짜시각 으로 남긴다 (.gitignore 의 .env.* 에 걸려 깃허브에 안 올라감). 화면에는 키 값이 나오지 않는다.
import hashlib
import json
import shutil
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENV = ROOT / ".env"
SAFEPASS_CFG = Path(r"C:\김경민\h_claude\세이프패스_v3\config.json")


def read_env(p):
    out = {}
    for line in p.read_text(encoding="utf-8-sig").splitlines():
        s = line.strip()
        if s and not s.startswith("#") and "=" in s:
            k, v = s.split("=", 1)
            out.setdefault(k.strip(), v.strip().strip('"').strip("'"))   # 같은 이름이 두 번이면 첫 번째 값
    return out


def read_cfg(p):
    if not p.exists():
        return {}
    lines = p.read_text(encoding="utf-8-sig").splitlines()
    return json.loads("\n".join(l for l in lines if not l.strip().startswith(("#", "//"))))


def fp(v):
    return hashlib.sha256(v.encode()).hexdigest()[:6] if v else "(비어 있음)"


old = read_env(ENV)
cfg = read_cfg(SAFEPASS_CFG)

DATA_APIS = [  # 공공데이터포털 서비스 주소 (키 아님)
    ("기상청_단기예보 조회서비스", "kmaShortForecastApi", "https://apis.data.go.kr/1360000/VilageFcstInfoService_2.0/getVilageFcst"),
    ("서울특별시 성북구_문화와 축제 현황", "sbFestivalApi", "https://api.odcloud.kr/api/15162450/v1/uddi:ed84986b-7901-4625-aca9-a70e2c3d3e50"),
    ("서울특별시_성북구_문화재_현황", "sbHeritageApi", "https://api.odcloud.kr/api/15040337/v1/uddi:767cfb2d-4b13-404e-b230-9c3da73cef2e"),
    ("서울특별시 성북구_문화시설정보", "sbCultureFacilityApi", "https://api.odcloud.kr/api/15064749/v1/uddi:28b48288-89f0-4e02-95aa-e559a694f5b8"),
    ("서울관광재단_식당운영정보", "seoulRestaurantInfoApi", "https://api.odcloud.kr/api/15098046/v1/uddi:086910c1-c1eb-4a9a-98df-910ed0495f6b"),
    ("서울특별시 성북구_규격봉투 판매소 현황", "sbTrashBagShopApi", "https://api.odcloud.kr/api/15113116/v1/uddi:1076c507-c35f-481f-b33c-e7262fdfaefe"),
    ("서울특별시_성북구_동주민센터_현황", "sbCommunityCenterApi", "https://api.odcloud.kr/api/15040310/v1/uddi:3c139e24-2658-4b04-b4bd-8a84a66b2b06"),
    ("서울특별시 성북구_외국인지원시설현황", "sbForeignerSupportApi", "https://api.odcloud.kr/api/15067994/v1/uddi:9baf3013-5ea4-4d48-b75f-be137769947b"),
    ("소상공인시장진흥공단_전국 백년가게 지정리스트 현황 정보", "baengnyeonShopApi", "https://api.odcloud.kr/api/15132695/v1/uddi:706576c0-3d19-4e32-96be-d446b2b76bab"),
    ("한국관광공사_방한 외래관광객 상세 월별 집계", "foreignVisitorMonthlyApi", "https://api.odcloud.kr/api/15136774/v1/uddi:ef3ac703-f138-45ec-a09d-f1f57eade496"),
    ("한국관광공사_국문 관광정보 서비스_GW (15101578)", "ktoKorTourApi", "https://apis.data.go.kr/B551011/KorService2"),
    ("한국관광공사_영문 관광정보서비스_GW (15101753)", "ktoEngTourApi", "https://apis.data.go.kr/B551011/EngService2"),
    ("한국관광공사_일문 관광정보서비스_GW (15101760)", "ktoJpnTourApi", "https://apis.data.go.kr/B551011/JpnService2"),
    ("한국관광공사_중문 간체 관광정보서비스_GW", "ktoChsTourApi", "https://apis.data.go.kr/B551011/ChsService2"),
]
SEOUL_SVCS = [
    ("서울시 문화행사 정보 (OA-15486)", "seoulCultureEventApi", "culturalEventInfo"),
    ("서울시 성북구 외국인관광도시민박업 인허가 정보 (OA-17459)", "seoulMinbakApi", "LOCALDATA_031104_SB"),
    ("서울시 성북구 숙박업 인허가 정보 (OA-17434)", "seoulLodgingApi", "LOCALDATA_031103_SB"),
    ("서울시 성북구 한옥체험업 인허가 정보 (OA-17509)", "seoulHanokApi", "LOCALDATA_031106_SB"),
    ("서울시 성북구 관광숙박업 인허가 정보 (OA-17409)", "seoulTourHotelApi", "LOCALDATA_031101_SB"),
]

# 공공데이터포털 키: DATA_GO_KR_KEY → 없으면 예전에 API 이름 칸에 넣어 둔 값 → 세이프패스 config 의 dataGoKrKey
data_key = old.get("DATA_GO_KR_KEY") or old.get("dataGoKrKey") or next(
    (old[n] for _, n, _ in DATA_APIS if old.get(n) and not old[n].startswith("http")), "") or cfg.get("dataGoKrKey", "")
odd = [n for _, n, _ in DATA_APIS if old.get(n) and not old[n].startswith("http") and old[n] != data_key]

vals = {
    "GROQ_API_KEYS": old.get("GROQ_API_KEYS", ""),
    "GEMINI_API_KEYS": old.get("GEMINI_API_KEYS", ""),
    "DATA_GO_KR_KEY": data_key,
    "seoulOpenDataKey": old.get("seoulOpenDataKey", ""),
    "javascriptKey": old.get("javascriptKey") or cfg.get("javascriptKey", ""),
    "restApiKey": old.get("restApiKey") or cfg.get("restApiKey", ""),
    "tmapAppKey": old.get("tmapAppKey") or cfg.get("tmapAppKey", ""),
}

out = ["# 성북 세이프패스 · 키와 서비스 주소 (깃허브에 올리지 않는다)", f"# 정리: {datetime.now():%Y-%m-%d %H:%M} · tools/env_정리.py", "",
       "#AI 키 (팀원 키 여러 개, 쉼표로)", f"GROQ_API_KEYS={vals['GROQ_API_KEYS']}", f"GEMINI_API_KEYS={vals['GEMINI_API_KEYS']}", "",
       "#카카오 (세이프패스 지도 · 길찾기) — JavaScript 키는 화면에, REST 키는 서버에서만", f"javascriptKey={vals['javascriptKey']}", f"restApiKey={vals['restApiKey']}", "",
       "#TMAP (SK 오픈API) — 쓸 때만", f"tmapAppKey={vals['tmapAppKey']}", "",
       "#공공데이터포털 인증키 (Decoding) — 아래 API 전부 이 키 하나로", f"DATA_GO_KR_KEY={vals['DATA_GO_KR_KEY']}", "",
       "#공공데이터포털 서비스 주소 (키 아님)"]
for title, name, url in DATA_APIS:
    out += [f"#{title}", f"{name}={url}"]
out += ["", "#서울 열린데이터광장 인증키 (공용)", f"seoulOpenDataKey={vals['seoulOpenDataKey']}", "", "#서울 열린데이터광장 서비스 이름 (키 아님)"]
for title, name, svc in SEOUL_SVCS:
    out += [f"#{title}", f"{name}={svc}"]

# 위에서 다루지 않은 예전 항목은 지우지 않고 맨 아래에 그대로 둔다
known = set(vals) | {n for _, n, _ in DATA_APIS} | {n for _, n, _ in SEOUL_SVCS} | {"dataGoKrKey"}
extra = [k for k in old if k not in known]
if extra:
    out += ["", "#예전 .env 에 있던 그 밖의 항목 (그대로 옮김)"] + [f"{k}={old[k]}" for k in extra]

backup = ROOT / f".env.백업_{datetime.now():%Y%m%d_%H%M%S}"
shutil.copy2(ENV, backup)
ENV.write_text("\n".join(out) + "\n", encoding="utf-8")

print("정리 완료. 원래 파일:", backup.name)
print("-" * 50)
for k, v in vals.items():
    print(f"  {k:<20} {'있음' if v else '비어 있음':<8} 지문 {fp(v)}")
print(f"  서비스 주소 {len(DATA_APIS)}개 · 서울 서비스 이름 {len(SEOUL_SVCS)}개 채움")
if extra:
    print("  그 밖의 항목 그대로 옮김:", ", ".join(extra))
if odd:
    print("  [주의] DATA_GO_KR_KEY 와 값이 다른 API 칸이 있었음:", ", ".join(odd), "→ 백업 파일에서 확인하세요")
input("\n엔터를 누르면 닫힙니다.")
