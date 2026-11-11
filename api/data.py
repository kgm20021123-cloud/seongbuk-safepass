# Vercel 서버 함수: /api/data  (실제 기능은 _safepass.py, 응답 틀은 _vercel.py)
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _vercel import Base  # noqa: E402


class handler(Base):
    NAME = "data"
