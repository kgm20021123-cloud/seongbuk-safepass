# 숙소 A 사진 프롬프트 (5장) — 한성대입구역 근처 게스트하우스 (시연용 가상 숙소)

「내 숙소」 탭 맨 위 사진 칸에 들어가요. 화면에는 이미 자리가 있어서 파일만 넣으면 바로 보여요.

## 사용법

1. ChatGPT나 Gemini에서 **새 대화**를 열어요.
2. 「0. 공통 스타일」을 먼저 붙여 넣어요.
3. 같은 대화에서 1번부터 **한 장씩** 붙여 넣어요. 같은 대화여야 같은 건물, 같은 방처럼 보여요.
4. 마음에 들면 아래 표의 이름으로 저장해요. `.jpg`, `.png` 둘 다 돼요.
5. 저장한 사진을 `team3_project\public\stay\` 폴더에 넣어요. 폴더가 없으면 새로 만들어요.
6. 내 PC에서는 새로고침하면 바로 보여요. 배포본(vercel)에 넣으려면 `git add .` → `git commit -m "숙소 A 사진"` → `git push`를 해요.

| 번호 | 파일 이름 | 장면 | 화면 설명 (영어 기준) |
|---|---|---|---|
| 1 | `a1.jpg` | 골목의 건물 입구 (외부) | Building entrance on a quiet side street |
| 2 | `a2.jpg` | 객실 — 더블 침대와 책상 | Your room — double bed and desk |
| 3 | `a3.jpg` | 전용 욕실 | Private bathroom |
| 4 | `a4.jpg` | 공용 라운지 · 간이 주방 | Shared lounge & kitchenette |
| 5 | `a5.jpg` | 번호키 현관 (셀프 체크인) | Keypad door — self check-in |

- 사진이 없는 칸은 화면에 안 나와요. 몇 장만 먼저 넣어도 돼요.
- 화면에는 이미 「시연용 숙소 — 이름 · 사진 · 호스트 · 주소는 지어낸 값」이라고 적혀 있어요. AI 사진이라도 실제 숙소처럼 속이는 일은 없어요.
- 크기가 너무 크면(장당 1MB 넘음) 휴대전화에서 느려요. 저장할 때 가로 1600px 정도로 줄이면 좋아요.

---

## 0. 공통 스타일 (먼저 한 번만)

```
I will ask you for 5 photos, one at a time, of the same small guesthouse in Seoul, South Korea, for a travel app listing. Do not make an image yet — just remember this and reply "OK".

- Style: realistic interior/real-estate photography, natural daylight, bright and clean, slightly warm tones, shot at eye level with a wide-angle lens, no heavy filters. It must look like a real, modest, well-kept place — not luxury, not a 3D render.
- Landscape 4:3 (e.g. 1600×1200).
- The place: a small guesthouse on the 3rd floor of a typical 4-storey red-brick residential "villa" building in a quiet side street near Hansung University Station, Seongbuk-gu, Seoul. Modern simple interior: light oak wood floor, white walls, light grey bedding, a few green plants, one accent colour of deep celadon green (#2F6B5C) in small items (cushion, towel, mug).
- Keep the same building, the same room and the same furniture across all photos.
- No people, no faces. No readable text, no brand names, no logos, no signs with writing, no house numbers.
```

## 1. a1.jpg — 골목의 건물 입구 (외부)

```
Photo 1 of 5. Exterior: the entrance of the 4-storey red-brick villa building seen from the quiet narrow side street on a sunny afternoon. A glass front door with a simple metal frame, a small potted plant beside it, a few parked scooters or bicycles nearby, typical Seoul residential alley with power lines and other low buildings. No readable signs or numbers.
```

## 2. a2.jpg — 객실 (더블 침대와 책상)

```
Photo 2 of 5. The guest room: a neat double bed with light grey bedding and a celadon-green cushion, a small wooden desk with a chair and a lamp by the window, sheer white curtains, a wall-mounted air conditioner above, a small wardrobe. Compact but tidy, about 12 square metres. Daylight from the window.
```

## 3. a3.jpg — 전용 욕실

```
Photo 3 of 5. The private bathroom of the same room, typical Korean style: wet-room layout with a glass shower screen, rain shower head, white tiles, a sink with a mirror, a hair dryer on a hook, folded white towels with one celadon-green hand towel, small toiletry bottles without labels. Clean and bright.
```

## 4. a4.jpg — 공용 라운지 · 간이 주방

```
Photo 4 of 5. The shared lounge on the same floor: a small kitchenette along one wall with a microwave, electric kettle, compact fridge and a sink, a wooden dining table for four, a shelf with mugs and a small first-aid box, a fire extinguisher mounted near the door. Warm, simple, homely. Same wood floor and white walls.
```

## 5. a5.jpg — 번호키 현관 (셀프 체크인)

```
Photo 5 of 5. Close-up of the room's front door in the hallway: a modern digital keypad door lock (numeric touch pad, no brand logo) on a light grey door, soft hallway lighting, a small shoe area on the floor. Shot from a slight angle so the keypad is clearly visible but no numbers are readable.
```

## 틀렸을 때 고치는 말

- **글자 · 간판 · 번호가 생겼을 때:** `Remove all readable text, numbers and logos. Keep everything else the same.`
- **너무 고급스러울 때:** `Make it look like a modest, real small guesthouse — simpler furniture, smaller room.`
- **방이 바뀌었을 때:** `Keep exactly the same room, furniture and colours as the previous photo.`
