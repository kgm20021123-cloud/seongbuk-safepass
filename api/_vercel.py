# Vercel 서버 함수 공통 틀 — api/<이름>.py 는 이 틀에 이름만 넣는다
# 성공한 응답은 Vercel 의 CDN 이 잠시 저장해 두고 다시 쓴다 (공공데이터 API 호출 횟수 · 첫 응답 시간 줄이기)
import json
import sys
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import parse_qs, urlparse

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _safepass import respond  # noqa: E402

# 기능별 CDN 저장 시간(초) — 서버 안의 cached() 시간과 맞춤
CDN_TTL = {
    "config": 300,          # 키를 바꾸면 5분 안에 반영
    "weather": 1800,
    "dust": 1800,
    "events": 6 * 3600,
    "tour": 12 * 3600,
    "data": 12 * 3600,
    "translate": 7 * 86400,  # 같은 글은 같은 번역
    "walk": 7 * 86400,       # 같은 출발 · 도착은 같은 경로
    "safety": 3 * 3600,      # 약국 영업시간 등
    "wifi": 12 * 3600,
    "toilets": 12 * 3600,
}


class Base(BaseHTTPRequestHandler):
    NAME = ""

    def do_GET(self):
        status, body = respond(self.NAME, parse_qs(urlparse(self.path).query))
        data = json.dumps(body, ensure_ascii=False).encode("utf-8")
        ttl = CDN_TTL.get(self.NAME, 0)
        ok = status == 200 and isinstance(body, dict) and body.get("ok")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        # 실패한 응답은 저장하지 않음 → 다음 요청에서 바로 다시 시도
        self.send_header("Cache-Control", f"public, max-age=0, s-maxage={ttl}, stale-while-revalidate={ttl}" if ok and ttl else "no-store")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def log_message(self, fmt, *args):
        pass
