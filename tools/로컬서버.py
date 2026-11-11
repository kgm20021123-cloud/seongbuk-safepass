# 성북 세이프패스 · 내 PC에서 띄우는 서버 (Vercel 과 같은 구조)
#   화면: public/ 폴더   ·   서버 기능: /api/<이름>  → api/_safepass.py 의 respond()
#   키: team3_project/.env (브라우저로는 카카오 JavaScript 키만 보냄)
# 실행: 세이프패스_실행.bat 더블클릭
import json
import os
import socket
import sys
import threading
import webbrowser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

ROOT = Path(__file__).resolve().parent.parent
PUBLIC = ROOT / "public"
sys.path.insert(0, str(ROOT / "api"))
import _safepass as sp  # noqa: E402

sp.load_dotenv()
PORT = int(os.environ.get("PORT", "5173"))   # 카카오 개발자 콘솔에 등록된 http://localhost:5173


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        s.close()


class Server(ThreadingHTTPServer):
    # 윈도우는 기본 설정이면 같은 포트를 두 서버가 함께 잡아, 예전 서버가 계속 대답하는 일이 생긴다 → 막는다
    allow_reuse_address = False


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **kw):
        super().__init__(*a, directory=str(PUBLIC), **kw)   # public 폴더 밖(.env · docs · api)은 내보내지 않음

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self):
        u = urlparse(self.path)
        if u.path.startswith("/api/"):
            name = u.path[5:].strip("/").removesuffix(".py")
            if name == "info":   # 내 PC 전용: 휴대전화 QR 주소
                status, body = 200, {"ok": True, "lan": f"http://{lan_ip()}:{PORT}/"}
            else:
                status, body = sp.respond(name, parse_qs(u.query))
            data = json.dumps(body, ensure_ascii=False).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
            return
        return super().do_GET()

    def log_message(self, fmt, *args):
        pass


if __name__ == "__main__":
    print("=" * 58)
    print(" 성북 세이프패스 (team3_project · 시연용)")
    print("=" * 58)
    for label, name in [("카카오 지도 키", "javascriptKey"), ("공공데이터포털 키", "DATA_GO_KR_KEY"), ("서울 열린데이터광장 키", "seoulOpenDataKey")]:
        print(f" {label:<16}:", "로드됨" if sp.env(name) else "없음 (.env 확인)")
    print(" 틈길 경로 엔진   : 불러오는 중… (2초쯤)")
    threading.Thread(target=lambda: print(" 틈길 경로 엔진   :", "로드됨" if sp.engine() else sp._engine["msg"]), daemon=True).start()
    threading.Thread(target=lambda: sp.events({}), daemon=True).start()      # 문화행사는 미리 받아 둠 (약 2만 건)
    url = f"http://localhost:{PORT}/"
    print(" PC에서 보기      :", url)
    print(" 휴대전화(같은 와이파이):", f"http://{lan_ip()}:{PORT}/")
    print(" 종료하려면 이 창을 닫거나 Ctrl+C 를 누르세요.")
    threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        Server(("0.0.0.0", PORT), Handler).serve_forever()
    except OSError as e:
        print("\n서버를 열지 못했습니다:", e)
        print("5173 포트를 다른 서버가 쓰고 있습니다. 세이프패스 v1~v3 · 틈길 · 예전 세이프패스 창을 닫거나,")
        print("작업 관리자에서 python.exe 를 모두 「작업 끝내기」 한 뒤 다시 실행하세요.")
        input("엔터를 누르면 닫힙니다.")
