# 깃허브 · Vercel 에 올리기 전 점검 (키 값은 화면에 절대 나오지 않음)
# 실행: team3_project 폴더에서  C:\김경민\h_claude\세이프패스_v1\python\python.exe tools\배포_점검.py
#  1) .gitignore 가 .env 를 막는지
#  2) 올라갈 파일 목록 · 큰 파일
#  3) 올라갈 파일 안에 .env 의 키 값이 그대로 들어 있지 않은지
#  4) Vercel Environment Variables 에 넣어야 할 이름이 .env 에 다 있는지
import fnmatch
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# 서버(api/_safepass.py)가 읽는 이름
NEED = [
    ("javascriptKey", "카카오 지도 (화면)"),
    ("DATA_GO_KR_KEY", "공공데이터포털: 날씨 · 미세먼지 · 관광공사 · 백년가게 · 주민센터 · 봉투 판매소"),
    ("seoulOpenDataKey", "서울 열린데이터광장: 문화행사"),
    ("baengnyeonShopApi", "백년가게 서비스 주소"),
    ("sbCommunityCenterApi", "주민센터 서비스 주소"),
    ("sbTrashBagShopApi", "종량제 봉투 판매소 서비스 주소"),
]
NEED_ONE = [("GROQ_API_KEYS", "GEMINI_API_KEYS")]   # 둘 중 하나는 있어야 AI 번역


def read_env(p):
    out = {}
    if p.exists():
        for line in p.read_text(encoding="utf-8-sig").splitlines():
            s = line.strip()
            if s and not s.startswith("#") and "=" in s:
                k, v = s.split("=", 1)
                out.setdefault(k.strip(), v.strip().strip('"').strip("'"))
    return out


def ignore_rules():
    p = ROOT / ".gitignore"
    if not p.exists():
        return []
    return [l.strip() for l in p.read_text(encoding="utf-8").splitlines() if l.strip() and not l.strip().startswith("#")]


def ignored(rel, rules):
    parts = rel.split("/")
    for r in rules:
        pat = r.rstrip("/")
        if "/" in pat:                       # 경로 규칙 (docs/기획서/ 등)
            if rel == pat or rel.startswith(pat + "/") or fnmatch.fnmatch(rel, pat):
                return True
        else:                                # 이름 규칙 (.env, *.pyc, __pycache__/ 등)
            if any(fnmatch.fnmatch(x, pat) for x in parts):
                return True
    return False


rules = ignore_rules()
envv = read_env(ROOT / ".env")
problems = 0

print("=" * 60)
print(" 세이프패스 배포 전 점검")
print("=" * 60)

# 1) .gitignore
if ignored(".env", rules):
    print("[통과] .gitignore 가 .env 를 막고 있음")
else:
    print("[위험] .gitignore 에 .env 줄이 없습니다 — 올리지 마세요")
    problems += 1

# 2) 올라갈 파일
files = []
for dp, dns, fns in os.walk(ROOT):
    rel_dir = Path(dp).relative_to(ROOT).as_posix()
    if rel_dir == ".git" or rel_dir.startswith(".git/"):
        dns[:] = []
        continue
    for f in fns:
        rel = f"{rel_dir}/{f}" if rel_dir != "." else f
        if not ignored(rel, rules):
            files.append(rel)
files.sort()
total = sum((ROOT / f).stat().st_size for f in files)
print(f"\n올라갈 파일 {len(files)}개 · 모두 {total / 1e6:.1f} MB")
for top in sorted({f.split('/')[0] for f in files}):
    sub = [f for f in files if f.split('/')[0] == top]
    size = sum((ROOT / f).stat().st_size for f in sub)
    print(f"  {top:<28} {len(sub):>4}개  {size / 1e6:6.1f} MB")
big = [f for f in files if (ROOT / f).stat().st_size > 50e6]
for f in big:
    print(f"[주의] 50MB 넘는 파일 (깃허브가 경고 · 100MB 넘으면 거부): {f}")

# 3) 키 값이 다른 파일에 들어갔는지
# 키 칸만 본다 (이름에 KEY · Key 가 들어간 것). 서비스 이름(culturalEventInfo, LOCALDATA_… 등)은 코드에 원래 들어 있어도 되는 값
secrets = [v for k, v in envv.items() if "key" in k.lower() and len(v) >= 12 and not v.startswith("http")]
secrets = [s for v in secrets for s in v.split(",") if len(s.strip()) >= 12]
leak = []
for f in files:
    p = ROOT / f
    if p.stat().st_size > 5e6:
        continue
    try:
        txt = p.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        continue
    if any(s.strip() in txt for s in secrets):
        leak.append(f)
if leak:
    problems += 1
    print("\n[위험] 아래 파일 안에 .env 의 키 값이 그대로 들어 있습니다 (값은 표시하지 않음):")
    for f in leak:
        print("   ", f)
else:
    print("\n[통과] 올라갈 파일 안에 .env 키 값 없음")

# 4) Vercel 에 넣을 이름
print("\nVercel Environment Variables (Import .env 로 한 번에 넣으면 됨)")
for name, why in NEED:
    ok = bool(envv.get(name))
    problems += 0 if ok else 1
    print(f"  {'있음' if ok else '없음'}  {name:<22} {why}")
for group in NEED_ONE:
    ok = any(envv.get(n) for n in group)
    problems += 0 if ok else 1
    print(f"  {'있음' if ok else '없음'}  {' 또는 '.join(group)}  AI 번역")

print("\n" + ("문제 없음 — 올려도 됩니다." if problems == 0 else f"확인할 것 {problems}개 — 위의 [위험] · 없음 을 먼저 고치세요."))
input("\n엔터를 누르면 닫힙니다.")
