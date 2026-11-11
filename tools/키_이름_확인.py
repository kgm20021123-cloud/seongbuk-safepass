# 키 이름 확인: .env 와 세이프패스 config.json 의 "이름"과 "상태"만 보여 준다. 키 값은 화면에 나오지 않는다.
# 실행: team3_project 폴더에서  C:\김경민\h_claude\세이프패스_v1\python\python.exe tools\키_이름_확인.py
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FILES = {
    "team3 .env": ROOT / ".env",
    "세이프패스 v3 config.json": Path(r"C:\김경민\h_claude\세이프패스_v3\config.json"),
}


def read_env(p):
    out = {}
    for line in p.read_text(encoding="utf-8-sig").splitlines():
        s = line.strip()
        if s and not s.startswith("#") and "=" in s:
            k, v = s.split("=", 1)
            out[k.strip()] = v.strip().strip('"').strip("'")
    return out


def read_json(p):
    lines = p.read_text(encoding="utf-8-sig").splitlines()
    text = "\n".join(l for l in lines if not l.strip().startswith(("#", "//")))
    data = json.loads(text)
    return {k: v for k, v in data.items() if isinstance(v, str)}


def tag(v):
    # 값 대신 짧은 지문만 (같은 값이면 같은 지문) — 원래 값은 알 수 없다
    return hashlib.sha256(v.encode()).hexdigest()[:6] if v else "------"


def kind(v):
    if not v:
        return "비어 있음"
    if v.startswith("http"):
        return "주소"
    if len(v) < 40 and all(c.isalnum() or c in "_-" for c in v) and not any(c.isdigit() for c in v[:3]) and "_" in v:
        return "이름 · 서비스명으로 보임"
    return f"키로 보임 ({len(v)}자)"


all_vals = {}
for label, p in FILES.items():
    print("=" * 60)
    print(label, "-", p)
    if not p.exists():
        print("  파일 없음")
        continue
    try:
        d = read_env(p) if p.suffix != ".json" else read_json(p)
    except Exception as e:
        print("  읽기 실패:", e)
        continue
    for k, v in d.items():
        if "," in v and not v.startswith("http"):
            n = len([x for x in v.split(",") if x.strip()])
            print(f"  {k:<28} 여러 개 ({n}개)          지문 {tag(v)}")
        else:
            print(f"  {k:<28} {kind(v):<22} 지문 {tag(v)}")
        all_vals.setdefault(tag(v), []).append(f"{label}:{k}")

print("=" * 60)
print("두 파일에서 값이 같은 키 (같은 지문):")
same = [v for t, v in all_vals.items() if len(v) > 1 and t != "------"]
for v in same:
    print("  " + "  =  ".join(v))
if not same:
    print("  없음")
print("\n이 화면을 캡처해서 보내 주세요. 키 값은 나오지 않습니다.")
input("엔터를 누르면 닫힙니다.")
