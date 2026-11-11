// 성북 세이프패스 서비스워커 — 인터넷이 끊겨도 앱 화면 · 저장본 데이터 · SOS · 보여 주기 카드가 열리게
// 화면 파일은 「먼저 네트워크, 안 되면 저장본」, /api/* 와 카카오 지도는 저장하지 않음 (실시간 · 키 보호)
const CACHE = "safepass-v1";
const SHELL = ["./", "index.html", "sp_data.json", "qrcode.js", "sp-manifest.json", "sp-icon-180.png", "sp-icon-192.png", "sp-icon-512.png",
  "stay/a1.jpg", "stay/a2.jpg", "stay/a3.jpg", "stay/a4.jpg", "stay/a5.jpg"];

self.addEventListener("install", e => {
  e.waitUntil(caches.open(CACHE).then(c => Promise.all(SHELL.map(u => c.add(u).catch(() => null)))).then(() => self.skipWaiting()));
});
self.addEventListener("activate", e => {
  e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener("fetch", e => {
  const u = new URL(e.request.url);
  if (e.request.method !== "GET" || u.origin !== location.origin || u.pathname.startsWith("/api/")) return;   // 외부 · API 는 그대로
  e.respondWith(fetch(e.request).then(r => {
    if (r.ok) { const copy = r.clone(); caches.open(CACHE).then(c => c.put(e.request, copy)); }
    return r;
  }).catch(() => caches.match(e.request, { ignoreSearch: true }).then(r => r || caches.match("index.html"))));
});
