# Discord Voice Activity, Economy & PNG Profile Bot

Многофункциональный Discord-бот на **Python** (`discord.py`, `Pillow`, `numpy`, `sqlite3`) для геймификации серверов: учёт голосового онлайна, защита от AFK, серверная экономика, коллекционные карточки и генерация графических карточек профиля.

## Ключевые возможности

- **Трекер голосовой активности и AFK-роутинг:** фоновый тикер (`TICK_SECONDS = 15`) с защитой от лагов (`MAX_CREDIT = 60`), автоматическим перемещением неактивных участников (`AFK_TIMEOUT = 15 min`) и начислением серверных монет за время в голосе (`VOICE_COIN_INTERVAL = 5 min`).
- **Генерация PNG-карточек (Pillow + NumPy):** рендеринг персонализированных изображений профиля (`/profile`) поверх кастомных фонов и шрифтов (`background.png`, `top_background.png`, `font.ttf`).
- **Локальная БД SQLite (8 таблиц):** `voice_time`, `wallet`, `messages`, `levels`, `cards`, `marriages`, `warnings`, `bot_meta`.
- **Автобэкапы базы данных:** выгрузка резервной копии по команде или автоматически в назначенный канал Discord.

## Slash-команды (`app_commands`)

| Категория | Команды | Описание |
|---|---|---|
| **Профиль и топ** | `/profile`, `/balance`, `/top` | PNG-карточка профиля, баланс/XP/голос, таблица лидеров |
| **Социальные** | `/marry`, `/divorce` | Система пар (отображается в карточке `/profile`) |
| **Магазин карточек** | `/shop`, `/opencard`, `/collection`, `/showcard` | Покупка случайных карточек, шансы, коллекция игрока |
| **Модерация** | `/warns`, `/warn`, `/unwarn`, `/clearwarns` | Выдача, просмотр и снятие предупреждений |
| **Администрирование** | `/addcoins`, `/setvoice`, `/setmessages`, `/backup`, `/setbackupchannel` | Управление экономикой, статистикой и бэкапами БД |

## Установка и запуск

```bash
pip install -r requirements.txt
```

Укажите токен бота в переменной окружения `DISCORD_BOT_TOKEN` (или в файле `.env` для `python-dotenv`):

```bash
export DISCORD_BOT_TOKEN="your_discord_bot_token"
python main.py
```
