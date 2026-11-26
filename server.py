import base64, gzip, json, os, re, threading, urllib.parse, urllib.request, urllib.error, webbrowser, zlib, html, time, random, uuid
from datetime import datetime
from html.parser import HTMLParser
from concurrent.futures import ThreadPoolExecutor
from collections import Counter
from difflib import SequenceMatcher
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get('DATA_DIR', str(ROOT)))
DATA_DIR.mkdir(parents=True, exist_ok=True)
MAX = 3_000_000
MAX_MONITORS_PER_USER = 8


def decode_pob(s):
    s = s.strip().replace('\n', '').replace('\r', '')
    if s.startswith('<'):
        raw = s.encode('utf-8')
    else:
        if not re.fullmatch(r'[A-Za-z0-9_\-+/=]+', s):
            raise ValueError('匯出碼含有無效字元')
        raw = base64.urlsafe_b64decode(s + '=' * (-len(s) % 4))
        obj = zlib.decompressobj()
        raw = obj.decompress(raw, MAX + 1)
        if len(raw) > MAX or obj.unconsumed_tail:
            raise ValueError('解壓縮內容超過限制')
    if len(raw) > MAX:
        raise ValueError('XML 檔案過大')
    if b'<!DOCTYPE' in raw.upper() or b'<!ENTITY' in raw.upper():
        raise ValueError('不支援 XML 外部實體')
    root = ET.fromstring(raw)
    if root.tag != 'PathOfBuilding':
        raise ValueError('不是有效的 Path of Building XML')
    return root


ENCHANT_MOD_RE = re.compile(
    r'^(?:Allocates\s+|Adds\s+\d+\s+Passive\s+Skills|'
    r'\d+\s+Added\s+Passive\s+Skills?\s+(?:is|are)\s+a?\s*Jewel\s+Sockets?|'
    r'Added\s+Small\s+Passive\s+Skills\s+grant:|'
    r'Used\s+when\s+Charges\s+reach\s+full|'
    r'Quality\s+does\s+not\s+increase\s+|'
    r'Grants\s+\d+%\s+increased\s+.*per\s+\d+%\s+Quality)',
    re.I,
)


def parse_item(item):
    lines = [x.strip() for x in (item.text or '').splitlines() if x.strip()]
    if not lines or not lines[0].startswith('Rarity:'):
        return None
    rarity = lines[0].split(':', 1)[1].strip()
    name = lines[1] if len(lines) > 1 else ''
    base = (
        lines[2]
        if len(lines) > 2
        and not re.match(
            r'^(Unique ID|Item Level|Implicits|Quality|LevelReq|Sockets|Crafted):',
            lines[2],
        )
        else ''
    )
    if rarity == 'MAGIC' and not base:
        base = next((x for x in lines[2:] if x.endswith(' Flask')), '')
    ignore = (
        'Unique ID:', 'Item Level:', 'LevelReq:', 'Quality:', 'Sockets:', 'Implicits:',
        'Requirements:', 'Radius:', 'Limited to:', 'Cluster Jewel Skill:',
        'Cluster Jewel Node Count:', 'Variant:', 'Selected Variant:', 'Enchant:',
        'Catalyst:', 'CatalystQuality:', 'Armour:', 'Evasion:', 'Evasion Rating:',
        'Energy Shield:', 'Ward:', 'Chance to Block:',
        'Physical Damage:', 'Elemental Damage:', 'Critical Strike Chance:',
        'Attacks per Second:', 'Weapon Range:', 'Map Tier:', 'Stack Size:',
        'Rarity:', 'Level:', 'Dex:', 'Str:', 'Int:',
    )
    ignore_exact = {'Corrupted', 'Mirrored', 'Split', 'Fractured Item', 'Historic', 'Synthesised Item'}
    skill_grant_re = re.compile(
        r'^(?:Grants?\s+Level\s+\d+|Trigger\s+Level\s+\d+|Cast\s+Level\s+\d+|'
        r'授予\s*等級\s*\d+|觸發\s*等級\s*\d+|施放\s*等級\s*\d+|'
        r'產生\s*低階神殿|Grant\s+a\s+Level\s+\d+)',
        re.I,
    )
    mods = []
    mod_entries = []
    implicit_count = 0
    seen_implicits = False
    remaining_implicits = 0
    for raw_line in lines[2:]:
        if raw_line.startswith('Implicits:'):
            try:
                implicit_count = int(raw_line.split(':', 1)[1].strip())
            except ValueError:
                implicit_count = 0
            seen_implicits = True
            remaining_implicits = implicit_count
            continue
        if (
            raw_line == base
            or raw_line in ignore_exact
            or raw_line.startswith(ignore)
            or raw_line.startswith((
                'Has Influence:', 'Influence:', 'Tags:', 'ArmourBasePercentile:',
                'EvasionBasePercentile:', 'EnergyShieldBasePercentile:',
                'BasePercentile:', 'DefencePercentile:', 'CraftedMods:',
                'Prefix:', 'Suffix:', 'Sockets:',
            ))
            or (re.match(r'^[A-Za-z][A-Za-z0-9_ ]{1,30}:', raw_line) and not raw_line.lower().startswith('added small passive skills'))
        ):
            continue
        low_raw = raw_line.lower()
        tags = set(re.findall(r'\{([^}]+)\}', low_raw))
        clean_x = re.sub(r'^(?:\{[^}]*\})+', '', raw_line).strip()
        if not clean_x or clean_x.startswith(('Item ', 'Requires ')):
            continue
        is_imp_slot = False
        if seen_implicits and remaining_implicits > 0:
            is_imp_slot = True
            remaining_implicits -= 1
        if skill_grant_re.search(clean_x):
            continue
        if is_imp_slot:
            if 'enchant' in tags or ENCHANT_MOD_RE.search(clean_x):
                pref = 'enchant'
            else:
                pref = 'implicit'
        elif 'fractured' in tags:
            pref = 'fractured'
        elif 'crafted' in tags:
            pref = 'crafted'
        elif 'enchant' in tags:
            pref = 'enchant'
        elif 'implicit' in tags:
            pref = 'implicit'
        else:
            pref = 'explicit'
        mods.append(clean_x)
        mod_entries.append({'text': clean_x, 'preferred': pref})
    return {
        'rarity': rarity,
        'name': name,
        'base': base,
        'mods': mods,
        'mod_entries': mod_entries,
        'raw': '\n'.join(lines),
        'implicit_count': implicit_count,
    }


def parse_pob(s, source=''):
    root = decode_pob(s)
    b = root.find('Build')
    its = root.find('Items')
    if b is None or its is None:
        raise ValueError('缺少角色或裝備資料')
    items = {x.get('id'): parse_item(x) for x in its.findall('Item')}
    active = its.get('activeItemSet', '1')
    sets = its.findall('ItemSet')
    chosen = next((x for x in sets if x.get('id') == active), sets[0] if sets else None)
    slots = []
    if chosen is not None:
        for slot in chosen.findall('Slot'):
            name = slot.get('name', '')
            iid = slot.get('itemId', '0')
            if (
                iid == '0'
                or not items.get(iid)
                or ' Swap' in name
                or 'Abyssal Socket' in name
                or name in ('Head', 'Body', 'Arm', 'Leg')
            ):
                continue
            it = dict(items[iid])
            it['slot'] = name
            slots.append(it)
    tree = root.find('Tree')
    jewels = []
    if tree is not None:
        spec = next(
            (x for x in tree.findall('Spec') if x.get('active', 'false') == 'true'),
            tree.find('Spec'),
        )
        if spec is not None:
            for sock in spec.findall('.//Socket'):
                iid = sock.get('itemId', '0')
                if items.get(iid):
                    jewels.append(dict(items[iid], slot='珠寶'))
    skills = []
    sk = root.find('Skills')
    if sk is not None:
        skset = next(
            (x for x in sk.findall('SkillSet') if x.get('id') == sk.get('activeSkillSet', '1')),
            sk.find('SkillSet'),
        )
        if skset is not None:
            for group in skset.findall('Skill'):
                if group.get('enabled') == 'false' or 'Swap' in group.get('slot', ''):
                    continue
                # Skip skills granted by equipment (source="Item:..."), passive tree (source="Tree:..."), or explosions
                if group.get('source'):
                    continue
                for gem in group.findall('Gem'):
                    if not gem.get('gemId'):
                        continue
                    name = gem.get('nameSpec') or gem.get('gemId') or gem.get('skillId')
                    if name:
                        skills.append({
                            'name': name,
                            'slot': group.get('slot', ''),
                            'level': gem.get('level', ''),
                            'quality': gem.get('quality', ''),
                        })
    return {
        'id': source or 'pob-' + str(zlib.adler32(ET.tostring(root))),
        'source': source,
        'class': b.get('className', ''),
        'ascendancy': b.get('ascendClassName', ''),
        'level': b.get('level', ''),
        'items': slots + jewels,
        'skills': skills,
        'item_records': len(its.findall('Item')),
    }


def fetch_poedb(url):
    parsed = urllib.parse.urlparse(url)
    if (
        parsed.scheme != 'https'
        or parsed.hostname not in ('poedb.tw', 'www.poedb.tw')
        or not re.fullmatch(r'/[a-z]{2}(?:-[a-z]{2})?/pob/[A-Za-z0-9_-]+/?', parsed.path)
    ):
        raise ValueError('請輸入 https://poedb.tw/tw/pob/代碼 格式的網址')
    req = urllib.request.Request(
        url, headers={'User-Agent': 'Mozilla/5.0 POEStatsV2/1.0', 'Accept': 'text/html'}
    )
    with urllib.request.urlopen(req, timeout=12) as response:
        page_html = response.read(1_000_001).decode('utf-8', 'replace')
    patterns = [
        r'(?:pobCode|pob_code|buildCode|exportCode)["\']?\s*[:=]\s*["\']([A-Za-z0-9_-]{100,})',
        r'([A-Za-z0-9_-]{1500,})',
    ]
    for pattern in patterns:
        for match in re.finditer(pattern, page_html):
            try:
                return parse_pob(match.group(1), url)
            except (ValueError, ET.ParseError, zlib.error, base64.binascii.Error):
                pass
    raise ValueError(
        'PoEDB 網頁未提供可直接解析的 PoB 匯出碼。請從該頁複製 PoB 匯出碼貼入下方；此功能仍屬實驗性。'
    )


STAT_CACHE = {}
CATALOGUE_DIR = DATA_DIR / 'trade_catalogues'
CATALOGUE_DIR.mkdir(parents=True, exist_ok=True)
CATALOGUE_URLS = {
    'en': [
        'https://www.pathofexile.com/api/trade/data/stats',
        'https://pathofexile.com/api/trade/data/stats',
    ],
    'tw': [
        'https://pathofexile.tw/api/trade/data/stats',
    ],
}

STAT_KIND_LABELS = {
    'explicit': '外顯',
    'implicit': '固定屬性',
    'fractured': '破裂',
    'crafted': '工藝',
    'enchant': '附魔',
    'pseudo': '總和',
}

LOCAL_ADDED_DMG_RE = re.compile(r'^(附加\s*#\s*至\s*#\s*.+?傷害)$')


def is_local_added_dmg_zh(zh):
    return bool(re.match(r'^附加\s*#\s*至\s*#\s*.+?傷害\s*\(部分\)$', (zh or '').strip()))


def upgrade_to_local_damage(sid, zh, tw_by_text):
    if not zh:
        return sid, zh
    s = zh.strip()
    if s.endswith('(部分)'):
        return sid, s
    m = LOCAL_ADDED_DMG_RE.match(s)
    if not m:
        return sid, zh
    target_zh = m.group(1) + ' (部分)'
    cands = tw_by_text.get(normalize_stat(target_zh), [])
    if not cands:
        return sid, zh
    prefix = sid.split('.', 1)[0] + '.' if '.' in sid else ''
    same_kind = [c for c in cands if c['id'].startswith(prefix)]
    chosen = same_kind[0] if same_kind else cands[0]
    return chosen['id'], chosen['text']


def extract_rolls(s):
    return [float(v.replace(',', '')) for v in re.findall(r'(?<![\w#])[-+]?\d+(?:[.,]\d+)?', s)]


def normalize_stat(s):
    s = re.sub(r'\{[^}]+\}', '', s)
    s = re.sub(r'\((?:implicit|crafted|fractured|enchant|scourge|crucible)\)', '', s, flags=re.I)
    s = re.sub(r'\(\s*[-+]?\d+(?:[.,]\d+)?\s*[-–—]\s*[-+]?\d+(?:[.,]\d+)?\s*\)', '#', s)
    s = re.sub(r'(?<![\w#])[-+]?\d+(?:[.,]\d+)?', '#', s)
    s = s.replace('’', "'").replace('–', '-').replace('＋', '+')
    s = re.sub(r'\s*\((?:local|global)\)\s*', ' ', s, flags=re.I)
    s = re.sub(r'(?<!\w)\+(?=#)', '', s)
    s = re.sub(r'[,:;]', ' ', s)
    return re.sub(r'\s+', ' ', s).strip().lower()


PLURAL_MAP = {
    'charges': 'charge',
    'sockets': 'socket',
    'projectiles': 'projectile',
    'targets': 'target',
    'seconds': 'second',
    'times': 'time',
    'enemies': 'enemy',
    'skills': 'skill',
    'totems': 'totem',
    'minions': 'minion',
    'curses': 'curse',
    'ailments': 'ailment',
    'hits': 'hit',
    'kills': 'kill',
    'strikes': 'strike',
    'attacks': 'attack',
    'spells': 'spell',
    'flasks': 'flask',
    'jewels': 'jewel',
    'brands': 'brand',
    'traps': 'trap',
    'mines': 'mine',
    'allies': 'ally',
}


def canonical_stat(s):
    n = normalize_stat(s)
    n = re.sub(r'\b(?:an|a)\b(?=\s+[a-z])', '#', n)
    words = re.findall(r'[a-z0-9#]+', n)
    words = [PLURAL_MAP.get(w, w) for w in words]
    return ' '.join(words)


# --- 全站玩家共用詞綴手動修正庫 (custom_mod_overrides.json) ---
MOD_OVERRIDE_FILE = DATA_DIR / 'custom_mod_overrides.json'
BUNDLED_MOD_OVERRIDE_FILE = ROOT / 'custom_mod_overrides.json'
MOD_OVERRIDE_LOCK = threading.Lock()
MOD_OVERRIDES = {}


def load_mod_overrides():
    loaded = {}
    for path in (BUNDLED_MOD_OVERRIDE_FILE, MOD_OVERRIDE_FILE):
        if path.exists():
            try:
                raw = json.loads(path.read_text(encoding='utf-8'))
                src = raw.get('overrides') if isinstance(raw, dict) and isinstance(raw.get('overrides'), dict) else raw
                if isinstance(src, dict):
                    for k, v in src.items():
                        if isinstance(v, dict) and isinstance(v.get('id'), str) and isinstance(v.get('zh'), str):
                            loaded[k] = v
            except Exception:
                pass
    MOD_OVERRIDES.clear()
    MOD_OVERRIDES.update(loaded)


def save_mod_overrides_unlocked():
    payload = json.dumps({'version': 1, 'overrides': MOD_OVERRIDES}, ensure_ascii=False, indent=2)
    try:
        MOD_OVERRIDE_FILE.write_text(payload, encoding='utf-8')
    except Exception:
        pass
    if BUNDLED_MOD_OVERRIDE_FILE != MOD_OVERRIDE_FILE:
        try:
            BUNDLED_MOD_OVERRIDE_FILE.write_text(payload, encoding='utf-8')
        except Exception:
            pass


load_mod_overrides()


def save_mod_override(mod_text, stat_id, zh_text, en_text='', option=None):
    mod_text = str(mod_text or '').strip()
    stat_id = str(stat_id or '').strip()
    zh_text = str(zh_text or '').strip()
    en_text = str(en_text or '').strip()
    if not mod_text or len(mod_text) > 500:
        raise ValueError('原始詞綴文字無效')
    if not re.fullmatch(r'[a-z]{2,20}\.[a-z0-9_]{3,80}', stat_id):
        raise ValueError('官方詞綴編號格式不正確')
    if not zh_text or len(zh_text) > 240:
        raise ValueError('請提供有效的繁體中文詞綴名稱')
    opt_val = None
    if option is not None and option != '':
        if isinstance(option, (int, float)) and not isinstance(option, bool):
            opt_val = int(option)
        elif isinstance(option, str) and option.isdigit():
            opt_val = int(option)

    key = canonical_stat(mod_text) or normalize_stat(mod_text)
    if not key:
        raise ValueError('無法建立詞綴索引鍵')

    entry = {
        'key': key,
        'exampleMod': mod_text,
        'id': stat_id,
        'option': opt_val,
        'zh': zh_text,
        'en': en_text,
        'updatedAt': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
    }
    with MOD_OVERRIDE_LOCK:
        MOD_OVERRIDES[key] = entry
        save_mod_overrides_unlocked()
    return entry


def delete_mod_override(key_or_mod):
    raw = str(key_or_mod or '').strip()
    if not raw:
        raise ValueError('缺少要刪除的詞綴鍵值')
    canon = canonical_stat(raw)
    norm = normalize_stat(raw)
    with MOD_OVERRIDE_LOCK:
        removed = False
        for k in (raw, canon, norm):
            if k and k in MOD_OVERRIDES:
                del MOD_OVERRIDES[k]
                removed = True
        if removed:
            save_mod_overrides_unlocked()
        return len(MOD_OVERRIDES)


def import_mod_overrides(raw_data):
    if not isinstance(raw_data, dict):
        raise ValueError('無效的共用詞綴庫 JSON 格式')
    src = raw_data.get('overrides') if isinstance(raw_data.get('overrides'), dict) else raw_data
    if not isinstance(src, dict):
        raise ValueError('找不到 overrides 詞綴資料')
    imported = 0
    with MOD_OVERRIDE_LOCK:
        for k, v in src.items():
            if not isinstance(v, dict):
                continue
            sid = str(v.get('id', '')).strip()
            zh = str(v.get('zh', '')).strip()
            ex = str(v.get('exampleMod', k)).strip()
            key = canonical_stat(ex) or str(k).strip()
            if key and re.fullmatch(r'[a-z]{2,20}\.[a-z0-9_]{3,80}', sid) and zh:
                opt = v.get('option')
                opt_val = int(opt) if isinstance(opt, (int, float)) and not isinstance(opt, bool) else None
                MOD_OVERRIDES[key] = {
                    'key': key,
                    'exampleMod': ex,
                    'id': sid,
                    'option': opt_val,
                    'zh': zh,
                    'en': str(v.get('en', '')).strip(),
                    'updatedAt': str(v.get('updatedAt') or datetime.now().strftime('%Y-%m-%d %H:%M:%S')),
                }
                imported += 1
        save_mod_overrides_unlocked()
        total = len(MOD_OVERRIDES)
    return {'imported': imported, 'count': total}


def list_mod_overrides():
    with MOD_OVERRIDE_LOCK:
        items = list(MOD_OVERRIDES.values())
        raw_copy = dict(MOD_OVERRIDES)
    items.sort(key=lambda x: x.get('updatedAt', ''), reverse=True)
    return items, raw_copy


def parse_catalogue(data):
    if not isinstance(data, dict) or not isinstance(data.get('result'), list):
        raise ValueError('不是有效的交易詞綴 JSON（缺少 result）')
    entries = []
    for group in data['result']:
        if not isinstance(group, dict):
            continue
        for e in group.get('entries', []):
            if isinstance(e, dict) and isinstance(e.get('id'), str) and isinstance(e.get('text'), str):
                entry = {'id': e['id'], 'text': e['text'], 'type': group.get('id', '')}
                opt = e.get('option')
                if isinstance(opt, dict) and isinstance(opt.get('options'), list):
                    entry['options'] = [
                        {'id': o['id'], 'text': o['text']}
                        for o in opt['options']
                        if isinstance(o, dict) and 'id' in o and isinstance(o.get('text'), str)
                    ]
                entries.append(entry)
    if len(entries) < 100:
        raise ValueError('交易詞綴資料不足，請使用完整 /api/trade/data/stats JSON')
    return entries


def catalogue_file(lang):
    return CATALOGUE_DIR / (lang + '.json')


def fetch_catalogue(lang, refresh=False):
    file = catalogue_file(lang)
    if file.exists() and not refresh:
        try:
            return parse_catalogue(json.loads(file.read_text(encoding='utf-8'))), '本機快取'
        except Exception:
            pass
    last_err = None
    for url in CATALOGUE_URLS[lang]:
        req = urllib.request.Request(
            url,
            headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0 Safari/537.36',
                'Accept': 'application/json',
                'Accept-Language': 'en-US,en;q=0.9' if lang == 'en' else 'zh-TW,zh;q=0.9',
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as response:
                raw = response.read(12_000_000)
            data = json.loads(raw)
            entries = parse_catalogue(data)
            file.write_text(json.dumps(data, ensure_ascii=False), encoding='utf-8')
            return entries, '官方線上下載'
        except Exception as exc:
            last_err = exc
            continue
    if file.exists():
        return (
            parse_catalogue(json.loads(file.read_text(encoding='utf-8'))),
            '本機快取（線上更新失敗）',
        )
    raise last_err or ValueError('下載失敗')


def build_stat_indexes(en_entries, tw_entries, zh_by_id):
    allowed = ('explicit.', 'implicit.', 'enchant.', 'crafted.', 'pseudo.', 'fractured.', 'scourge.', 'crucible.', 'veiled.')
    stats = [e for e in en_entries if e['id'].startswith(allowed)]
    tw = [e for e in tw_entries if e['id'].startswith(allowed)]

    by_text = {}
    by_canonical = {}
    by_subline = {}
    token_index = {}
    lookup = {}
    expanded_entries = []

    tw_by_id_entry = {e['id']: e for e in tw}

    for entry in stats:
        sid = entry['id']
        txt = entry['text']
        lookup[sid] = entry

        key = normalize_stat(txt)
        by_text.setdefault(key, []).append(entry)

        ckey = canonical_stat(txt)
        by_canonical.setdefault(ckey, []).append(entry)

        if '\n' in txt:
            for sub in txt.splitlines():
                sub = sub.strip()
                if sub:
                    s_ckey = canonical_stat(sub)
                    if s_ckey:
                        by_subline.setdefault(s_ckey, []).append(entry)

        for token in stat_tokens(txt):
            token_index.setdefault(token, []).append(entry)

        if entry.get('options') and '#' in txt:
            tw_entry = tw_by_id_entry.get(sid)
            tw_opts = {}
            tw_tmpl = zh_by_id.get(sid, '')
            if tw_entry and tw_entry.get('options'):
                tw_opts = {o['id']: o['text'] for o in tw_entry['options']}
            for opt in entry['options']:
                opt_id = opt['id']
                opt_en = opt['text'].replace('\n', ' / ').strip()
                opt_zh = (tw_opts.get(opt_id) or opt_en).replace('\n', ' / ').strip()
                exp_en = txt.replace('#', opt_en, 1)
                exp_zh = tw_tmpl.replace('#', opt_zh, 1) if (tw_tmpl and '#' in tw_tmpl) else f"{tw_tmpl} {opt_zh}".strip()
                virt = {
                    'id': sid,
                    'text': exp_en,
                    'zh_override': exp_zh,
                    'option': opt_id,
                    'type': entry.get('type', ''),
                }
                expanded_entries.append(virt)
                v_key = normalize_stat(exp_en)
                by_text.setdefault(v_key, []).append(virt)
                v_ckey = canonical_stat(exp_en)
                by_canonical.setdefault(v_ckey, []).append(virt)

    tw_by_text = {}
    tw_by_canonical = {}
    for e in tw:
        tw_by_text.setdefault(normalize_stat(e['text']), []).append(e)
        tw_by_canonical.setdefault(canonical_stat(e['text']), []).append(e)

    return {
        'stats': stats,
        'tw': tw,
        'expanded': expanded_entries,
        'lookup': lookup,
        'by_text': by_text,
        'by_canonical': by_canonical,
        'by_subline': by_subline,
        'token_index': token_index,
        'tw_by_text': tw_by_text,
        'tw_by_canonical': tw_by_canonical,
    }


def fetch_trade_stats(refresh=False):
    now = time.time()
    if not refresh and STAT_CACHE.get('expires', 0) > now:
        return STAT_CACHE['entries'], STAT_CACHE['zh_by_id'], STAT_CACHE['meta']
    errors = {}
    bylang = {}
    sources = {}
    for lang in ('en', 'tw'):
        try:
            bylang[lang], sources[lang] = fetch_catalogue(lang, refresh=refresh)
        except Exception as exc:
            errors[lang] = str(exc)[:180]
    if not bylang:
        raise ValueError('無法讀取交易詞綴資料庫：' + str(errors))
    en = bylang.get('en', [])
    tw = bylang.get('tw', [])
    zh_by_id = {e['id']: e['text'] for e in tw if re.search(r'[\u3400-\u9fff]', e['text'])}
    en_by_id = {e['id']: e['text'] for e in en}
    idx = build_stat_indexes(en, tw, zh_by_id)
    meta = {
        'english_count': len(en),
        'taiwan_count': len(tw),
        'sources': sources,
        'errors': errors,
        'chinese_count': len(zh_by_id),
        'english_available': bool(en),
    }
    STAT_CACHE.update(
        entries=en,
        zh_by_id=zh_by_id,
        en_by_id=en_by_id,
        tw_entries=tw,
        tw_by_text=idx['tw_by_text'],
        idx=idx,
        meta=meta,
        expires=now + 86400,
    )
    return en, zh_by_id, meta


def search_trade_stats(query_str, kind_filter='all', limit=30):
    q = str(query_str or '').strip().lower()
    if not q:
        return []
    stats, zh_by_id, _ = fetch_trade_stats()
    en_by_id = STAT_CACHE.get('en_by_id', {})
    tw_entries = STAT_CACHE.get('tw_entries', [])
    tw_by_text = STAT_CACHE.get('tw_by_text', {})
    idx = STAT_CACHE.get('idx') or {}
    expanded = idx.get('expanded', [])
    allowed = ('explicit.', 'implicit.', 'enchant.', 'crafted.', 'pseudo.', 'fractured.', 'scourge.', 'crucible.', 'veiled.')
    kind_prio = {'explicit': 0, 'pseudo': 1, 'implicit': 2, 'fractured': 3, 'crafted': 4, 'enchant': 5}

    tokens = [t for t in re.split(r'\s+', q) if t]
    seen_sigs = set()
    scored = []

    def check_candidate(sid, zh_text, en_text, opt_val=None):
        if not sid.startswith(allowed):
            return
        if opt_val is None:
            sid, zh_text = upgrade_to_local_damage(sid, zh_text, tw_by_text)
        sig = (sid, opt_val)
        if sig in seen_sigs:
            return
        k = sid.split('.', 1)[0]
        if kind_filter and kind_filter != 'all' and k != kind_filter:
            return
        zh_low = (zh_text or '').lower()
        en_low = (en_text or '').lower()
        hay = zh_low + ' ' + en_low
        if not all(t in hay for t in tokens):
            return
        seen_sigs.add(sig)
        exact_boost = 0 if (q in zh_low or q in en_low) else 1
        prefix_boost = 0 if (zh_low.startswith(q) or en_low.startswith(q)) else 1
        local_bonus = 0 if is_local_added_dmg_zh(zh_text) else 1
        scored.append((
            exact_boost,
            prefix_boost,
            local_bonus,
            kind_prio.get(k, 9),
            len(zh_text or en_text),
            {
                'id': sid,
                'option': opt_val,
                'zh': zh_text or en_text,
                'en': en_text or '',
                'kind': k,
                'kindLabel': STAT_KIND_LABELS.get(k, k),
            },
        ))

    for e in tw_entries:
        sid = e['id']
        check_candidate(sid, e['text'], en_by_id.get(sid, ''), None)
    for e in stats:
        sid = e['id']
        check_candidate(sid, zh_by_id.get(sid, ''), e['text'], None)
    for v in expanded:
        check_candidate(v['id'], v.get('zh_override', ''), v.get('text', ''), v.get('option'))

    scored.sort(key=lambda x: (x[0], x[1], x[2], x[3], x[4]))
    return [x[5] for x in scored[:limit]]


def import_catalogue(lang, data):
    if lang not in ('en', 'tw'):
        raise ValueError('語言只能選 en 或 tw')
    entries = parse_catalogue(data)
    catalogue_file(lang).write_text(json.dumps(data, ensure_ascii=False), encoding='utf-8')
    STAT_CACHE.clear()
    return {'language': lang, 'count': len(entries)}


LIGHT_OF_MEANING_MODS = {
    'maximum life': '範圍內的天賦同時給予 +# 最大生命',
    'maximum mana': '範圍內的天賦同時給予 +# 最大魔力',
    'global critical strike chance': '範圍內的天賦同時增加 #% 全域暴擊機率',
    'all attributes': '範圍內的天賦同時給予 +# 全能力',
    'chaos resistance': '範圍內的天賦同時給予 +#% 混沌抗性',
    'physical damage': '範圍內的天賦同時增加 #% 物理傷害',
    'fire damage': '範圍內的天賦同時增加 #% 火焰傷害',
    'cold damage': '範圍內的天賦同時增加 #% 冰冷傷害',
    'lightning damage': '範圍內的天賦同時增加 #% 閃電傷害',
    'chaos damage': '範圍內的天賦同時增加 #% 混沌傷害',
    'armour': '範圍內的天賦同時增加 #% 護甲',
    'evasion rating': '範圍內的天賦同時增加 #% 閃避值',
    'energy shield': '範圍內的天賦同時增加 #% 能量護盾',
}


def known_mod_zh(mod):
    prefix = 'passive skills in radius also grant '
    if not mod.lower().startswith(prefix):
        return ''
    suffix = mod.lower()[len(prefix):]
    for key, zh in LIGHT_OF_MEANING_MODS.items():
        if suffix.endswith(key):
            return zh
    return ''


STOPWORDS = {
    'of', 'the', 'to', 'and', 'for', 'with', 'a', 'an', 'you', 'your', 'while',
    'affected', 'by', 'in', 'on', 'per', 'from', 'is', 'are', 'have', 'has',
    'as', 'at', 'against', 'enemy', 'enemies',
}


def stat_tokens(s):
    s = canonical_stat(s)
    return {t for t in re.findall(r'[a-z]+', s) if t not in STOPWORDS}


def stat_score(a, b):
    ca = canonical_stat(a)
    cb = canonical_stat(b)
    if ca == cb:
        return 1.0
    ta, tb = stat_tokens(a), stat_tokens(b)
    if not ta or not tb:
        return 0
    common = len(ta & tb)
    if common < 2:
        return 0
    jaccard = common / len(ta | tb)
    seq = SequenceMatcher(None, ca, cb).ratio()
    return round(0.67 * jaccard + 0.33 * seq, 4)


def watcher_zh_hint(mod):
    m = normalize_stat(mod)
    if 'while affected by zealotry' in m and 'penetrate' in m and 'elemental resistances' in m:
        return '受狂熱影響時，暴擊穿透 #% 敵人元素抗性'
    if 'while affected by discipline' in m and 'energy shield per enemy hit' in m:
        return '受紀律影響時，每擊中一個敵人獲得 # 能量護盾'
    for suffix, zh in [
        ('maximum energy shield', '增加 #% 最大能量護盾'),
        ('maximum life', '增加 #% 最大生命'),
        ('maximum mana', '增加 #% 最大魔力'),
    ]:
        if m.endswith(suffix) and 'increased' in m:
            return zh
    return ''


def entry_zh(entry, zh_by_id):
    return entry.get('zh_override') or zh_by_id.get(entry['id'], '')


def choose_exact_trade_stat(entries, zh_by_id, preferred='explicit'):
    priority = {'explicit': 0, 'fractured': 1, 'crafted': 2, 'implicit': 3, 'enchant': 4, 'pseudo': 5}

    def key(entry):
        kind = entry['id'].split('.', 1)[0]
        zh = entry_zh(entry, zh_by_id)
        local_bonus = 0 if is_local_added_dmg_zh(zh) else 1
        return (0 if kind == preferred else 1, local_bonus, priority.get(kind, 9), entry['id'])

    options = [x for x in entries if entry_zh(x, zh_by_id)]
    return sorted(options, key=key)[0] if options else None


def detect_mod_preferred_kind(mod):
    low = mod.lower()
    for tag in ('implicit', 'crafted', 'fractured', 'enchant'):
        if f'({tag})' in low:
            return tag
    return 'explicit'


def match_mods(mods):
    if not isinstance(mods, list) or len(mods) > 100:
        raise ValueError('詞綴資料格式不正確')
    try:
        stats, zh_by_id, meta = fetch_trade_stats()
        catalogue_error = ''
    except Exception as exc:
        stats = []
        zh_by_id = {}
        meta = {}
        catalogue_error = '無法取得交易詞綴資料：' + str(exc)[:180]

    idx = STAT_CACHE.get('idx') or build_stat_indexes(stats, STAT_CACHE.get('tw_entries', []), zh_by_id)
    by_text = idx['by_text']
    by_canonical = idx['by_canonical']
    by_subline = idx['by_subline']
    token_index = idx['token_index']
    lookup = idx['lookup']
    tw_by_text = idx['tw_by_text']
    tw_by_canonical = idx['tw_by_canonical']

    output = []
    for item_entry in mods:
        if isinstance(item_entry, dict):
            mod = item_entry.get('text', '')
            pref_kind = item_entry.get('preferred') or detect_mod_preferred_kind(mod)
        else:
            mod = item_entry
            pref_kind = detect_mod_preferred_kind(mod)
        if not isinstance(mod, str) or len(mod) > 500:
            continue
        norm = normalize_stat(mod)
        canon = canonical_stat(mod)
        override_key = canon or norm

        # 0. Check shared community modifier overrides first
        with MOD_OVERRIDE_LOCK:
            ov = MOD_OVERRIDES.get(canon) or MOD_OVERRIDES.get(norm)
        if ov:
            sid = ov['id']
            k = sid.split('.', 1)[0]
            output.append({
                'mod': mod,
                'status': 'matched',
                'id': sid,
                'option': ov.get('option'),
                'kind': k,
                'kindLabel': STAT_KIND_LABELS.get(k, k),
                'text': ov.get('en') or mod,
                'zh': ov['zh'],
                'rolls': extract_rolls(mod),
                'translation_status': 'override',
                'override': True,
                'overrideKey': ov.get('key') or override_key,
                'suggestions': [],
            })
            continue

        # 1. Exact normalized English match (including expanded options)
        choices = by_text.get(norm, [])
        # 2. Canonical English match (handles (10-20) ranges, singular/plural, a/an)
        if not choices:
            choices = by_canonical.get(canon, [])
        # 3. Direct Chinese match (for TW PoE client pasted mods)
        if not choices and re.search(r'[\u3400-\u9fff]', mod):
            choices = tw_by_text.get(norm, []) or tw_by_canonical.get(canon, [])
        # 4. Multi-line subline match (for split multi-line mods)
        if not choices:
            choices = by_subline.get(canon, [])

        known_zh = known_mod_zh(mod) or watcher_zh_hint(mod)
        suggestions = []

        # 5. Fuzzy token + sequence similarity match
        if not choices and idx['stats']:
            tokens = stat_tokens(mod)
            candidate_ids = Counter(e['id'] for t in tokens for e in token_index.get(t, []))
            scored = []
            for sid, overlap in candidate_ids.items():
                if overlap < 2 and len(tokens) >= 2:
                    continue
                e = lookup[sid]
                score = stat_score(mod, e['text'])
                if score >= 0.50:
                    scored.append((score, e))
            scored.sort(key=lambda z: -z[0])

            seen_sug = set()
            for score, e in scored:
                raw_zh = entry_zh(e, zh_by_id)
                if not raw_zh:
                    continue
                up_id, up_zh = upgrade_to_local_damage(e['id'], raw_zh, tw_by_text)
                if up_id in seen_sug:
                    continue
                seen_sug.add(up_id)
                suggestions.append({'id': up_id, 'text': e['text'], 'zh': up_zh, 'score': round(score * 100)})
                if len(suggestions) >= 8:
                    break

            if scored and scored[0][0] >= 0.82:
                top_score = scored[0][0]
                top_group = [e for sc, e in scored if top_score - sc <= 0.03 and entry_zh(e, zh_by_id)]
                top_canons = {canonical_stat(e['text']) for e in top_group}
                if len(top_canons) == 1:
                    choices = top_group

        if not choices and known_zh:
            choices = tw_by_text.get(normalize_stat(known_zh), [])

        ids = {(x['id'], x.get('option')) for x in choices}
        if len(ids) == 1:
            c0 = choices[0]
            sid = c0['id']
            opt_val = c0.get('option')
            zh = entry_zh(c0, zh_by_id) or known_zh
            if opt_val is None:
                sid, zh = upgrade_to_local_damage(sid, zh, tw_by_text)
            k = sid.split('.', 1)[0]
            output.append({
                'mod': mod,
                'status': 'matched',
                'id': sid,
                'option': opt_val,
                'kind': k,
                'kindLabel': STAT_KIND_LABELS.get(k, k),
                'text': c0['text'],
                'zh': zh,
                'rolls': extract_rolls(mod),
                'translation_status': 'verified' if zh else 'unavailable',
                'override': False,
                'overrideKey': override_key,
                'suggestions': suggestions,
            })
        elif choices:
            pick = choose_exact_trade_stat(choices, zh_by_id, preferred=pref_kind)
            opts = []
            seen_opt = set()
            for x in choices[:12]:
                x_zh = entry_zh(x, zh_by_id) or known_zh
                if x.get('option') is None:
                    ox_id, ox_zh = upgrade_to_local_damage(x['id'], x_zh, tw_by_text)
                else:
                    ox_id, ox_zh = x['id'], x_zh
                sig = (ox_id, x.get('option'))
                if sig in seen_opt:
                    continue
                seen_opt.add(sig)
                opts.append({'id': ox_id, 'option': x.get('option'), 'zh': ox_zh, 'text': x['text'], 'score': 100})
            if pick:
                p_zh = entry_zh(pick, zh_by_id)
                if pick.get('option') is None:
                    pid, pzh = upgrade_to_local_damage(pick['id'], p_zh, tw_by_text)
                else:
                    pid, pzh = pick['id'], p_zh
                k = pid.split('.', 1)[0]
                output.append({
                    'mod': mod,
                    'status': 'matched',
                    'id': pid,
                    'option': pick.get('option'),
                    'kind': k,
                    'kindLabel': STAT_KIND_LABELS.get(k, k),
                    'text': pick['text'],
                    'zh': pzh,
                    'rolls': extract_rolls(mod),
                    'translation_status': 'auto',
                    'override': False,
                    'overrideKey': override_key,
                    'reason': '多個相同文字的交易 ID，已優先選取對應詞綴；可自行更改',
                    'suggestions': opts,
                })
            else:
                output.append({
                    'mod': mod,
                    'status': 'ambiguous',
                    'reason': '同一模板存在多個 ID，但沒有可靠中文對照',
                    'zh': known_zh,
                    'rolls': extract_rolls(mod),
                    'override': False,
                    'overrideKey': override_key,
                    'suggestions': opts,
                })
        else:
            reason = catalogue_error or (
                '英文交易詞綴資料未載入，請先下載或匯入完整英文 JSON'
                if not idx['stats']
                else '官方詞綴模板無法唯一對應'
            )
            preview = suggestions[0]['zh'] if suggestions and suggestions[0]['score'] >= 60 else ''
            output.append({
                'mod': mod,
                'status': 'unmatched',
                'reason': reason,
                'zh': known_zh or preview,
                'translation_status': 'candidate' if preview and not known_zh else ('hint' if known_zh else 'unavailable'),
                'rolls': extract_rolls(mod),
                'override': False,
                'overrideKey': override_key,
                'suggestions': suggestions,
            })
    return output


def parse_pasted_item_text(raw_text):
    """Parse PoE Ctrl+C item text (EN or TW) or plain modifier lines."""
    raw_lines = [x.strip() for x in str(raw_text or '').splitlines() if x.strip()]
    if not raw_lines:
        raise ValueError('請貼上遊戲內 Ctrl+C 複製的物品文字或詞綴內容')
    if len(raw_lines) > 120:
        raise ValueError('貼上內容行數過多')

    kind = 'unique'
    name = ''
    base = ''
    has_header = False

    rarity_idx = next(
        (idx for idx, ln in enumerate(raw_lines) if ln.startswith(('Rarity:', '稀有度:'))),
        -1,
    )
    if rarity_idx >= 0:
        has_header = True
        r_val = raw_lines[rarity_idx].split(':', 1)[1].strip().lower()
        if r_val in ('unique', '傳奇'):
            kind = 'unique'
        elif r_val in ('gem', '技能寶石'):
            kind = 'gem'
        else:
            kind = 'rare'
        if rarity_idx + 1 < len(raw_lines) and not raw_lines[rarity_idx + 1].startswith('---'):
            name = raw_lines[rarity_idx + 1]
        if rarity_idx + 2 < len(raw_lines) and not raw_lines[rarity_idx + 2].startswith('---'):
            cand_base = raw_lines[rarity_idx + 2]
            if ':' not in cand_base:
                base = cand_base

    ignore_prefixes = (
        'Item Class:', '物品種類:', 'Rarity:', '稀有度:', 'Quality:', '品質:',
        'Sockets:', '插槽:', 'Item Level:', '物品等級:', 'LevelReq:', 'Requirements:',
        '需求:', 'Level:', '等級:', 'Str:', '力量:', 'Dex:', '敏捷:', 'Int:', '智慧:',
        'Armour:', '護甲:', 'Evasion Rating:', '閃避值:', 'Energy Shield:', '能量護盾:',
        'Chance to Block:', '格擋機率:', 'Physical Damage:', '物理傷害:',
        'Elemental Damage:', '元素傷害:', 'Critical Strike Chance:', '暴擊機率:',
        'Attacks per Second:', '每秒攻擊次數:', 'Weapon Range:', '武器範圍:',
        'Map Tier:', '地圖階級:', 'Stack Size:', '堆疊數量:', 'Radius:', '範圍:',
        'Limited to:', '僅限:', 'Note:', '備註:', 'Experience:', '經驗值:',
        'Catalyst:', 'CatalystQuality:', '催化劑:', 'Unique ID:', 'Implicits:', 'Variant:',
        'Selected Variant:', 'Cluster Jewel Skill:', 'Cluster Jewel Node Count:',
        'Armour:', 'Evasion:', 'Energy Shield:', 'Ward:',
        '~b/o', '~price',
    )
    ignore_exact = {
        'Corrupted', '已汙染', 'Mirrored', '已複製', 'Split', '已分化',
        'Fractured Item', '破裂物品', 'Synthesised Item', '追憶物品',
        'Unidentified', '未鑑定', 'Historic',
    }

    mod_lines = []
    start_idx = rarity_idx + 1 if has_header else 0
    for ln in raw_lines[start_idx:]:
        if ln.startswith('---') or ln in ignore_exact or ln.startswith(ignore_prefixes):
            continue
        if has_header and (ln == name or ln == base):
            continue
        if ln.startswith('{') and '}' in ln:
            ln = re.sub(r'^(?:\{[^}]*\})+', '', ln).strip()
        if ln and not re.match(r'^[A-Za-z][A-Za-z0-9_ ]{1,30}:', ln) and not re.search(r'(?:Grants?\s+Level\s+\d+|Trigger\s+Level\s+\d+|授予\s*等級\s*\d+|觸發\s*等級\s*\d+|產生\s*低階神殿)', ln, re.I):
            mod_lines.append(ln)

    if has_header and mod_lines and not re.search(r'[0-9+#%]', mod_lines[0]) and len(mod_lines[0]) <= 12:
        mod_lines = mod_lines[1:]

    resolved_zh = ''
    is_foulborn = False
    if kind == 'unique' and name:
        if name.lower().startswith('foulborn ') or name.startswith('穢生'):
            is_foulborn = True
        if re.search(r'[\u3400-\u9fff]', name):
            resolved_zh = name.strip()
        else:
            r = resolve_name(name, 'unique', allow_web=True)
            resolved_zh = r.get('zh') or name
    elif kind == 'gem' and name:
        if re.search(r'[\u3400-\u9fff]', name):
            resolved_zh = name
        else:
            r = resolve_name(name, 'gem', allow_web=True)
            resolved_zh = r.get('zh') or name
    elif kind == 'rare':
        target_base = base or name
        if target_base:
            if re.search(r'[\u3400-\u9fff]', target_base):
                resolved_zh = target_base
            else:
                r = resolve_name(target_base, 'base', allow_web=True)
                resolved_zh = r.get('zh') or target_base

    matched = match_mods(mod_lines)
    return {
        'kind': kind,
        'itemName': resolved_zh,
        'isFoulborn': is_foulborn,
        'rawName': name,
        'rawBase': base,
        'mods': matched,
    }


def sanitize_tw_unique_name(name):
    name = name.strip()
    name = re.sub(r'^穢生[．·\s]*', '', name).strip()
    maps = get_official_item_map()
    valid_uniques = maps.get('tw_unique_names') or set()
    valid_bases = maps.get('tw_base_names') or set()
    if valid_uniques and name in valid_uniques:
        return name
    if ' ' in name:
        head, tail = name.rsplit(' ', 1)
        if (valid_uniques and head in valid_uniques) or (valid_bases and tail in valid_bases):
            return head.strip()
        first_part = name.split(' ', 1)[0].strip()
        if valid_uniques and first_part in valid_uniques:
            return first_part
    if valid_uniques:
        compact = name.replace('．', '').replace('·', '').replace(' ', '')
        for vu in valid_uniques:
            if vu.replace('．', '').replace('·', '').replace(' ', '') == compact:
                return vu
    return name


SLOT_CATEGORY_MAP = {
    'helmet': 'armour.helmet',
    'body armour': 'armour.chest',
    'gloves': 'armour.gloves',
    'boots': 'armour.boots',
    'amulet': 'accessory.amulet',
    'ring 1': 'accessory.ring',
    'ring 2': 'accessory.ring',
    'ring': 'accessory.ring',
    'belt': 'accessory.belt',
}


def resolve_rare_category(slot='', base=''):
    b = str(base or '').lower()
    sl = str(slot or '').strip().lower()
    if 'cluster jewel' in b or '星團珠寶' in b:
        return 'jewel.cluster'
    if 'abyss' in b or 'eye jewel' in b or '深淵珠寶' in b or '之眼珠寶' in b:
        return 'jewel.abyss'
    if 'jewel' in b or '珠寶' in b or sl == '珠寶':
        return 'jewel'
    if sl in SLOT_CATEGORY_MAP:
        return SLOT_CATEGORY_MAP[sl]
    if 'quiver' in b or '箭袋' in b:
        return 'armour.quiver'
    if 'shield' in b or '盾' in b:
        return 'armour.shield'
    if sl in ('weapon 1', 'weapon 2', 'weapon'):
        return 'weapon'
    return ''


def build_trade_query(name, league, kind='unique', base='', stat_ids=None, stat_filters=None, status_option='securable', slot=''):
    if not isinstance(league, str) or not league.strip() or len(league) > 100:
        raise ValueError('請填入正確的台服聯盟名稱')
    if kind not in ('unique', 'gem', 'rare'):
        raise ValueError('不支援的物品類別')
    if kind in ('unique', 'gem') and (not isinstance(name, str) or not name.strip() or len(name) > 140):
        raise ValueError('請輸入或選擇有效的物品名稱')
    if status_option not in ('securable', 'available', 'online', 'onlineleague', 'any'):
        status_option = 'securable'
    query = {
        'status': {'option': status_option},
        'stats': [{'type': 'and', 'filters': []}],
        'filters': {
            'type_filters': {
                'filters': {
                    'rarity': {'option': 'rare' if kind == 'rare' else ('unique' if kind == 'unique' else 'gem')}
                }
            }
        },
    }
    if kind in ('unique', 'rare'):
        if kind == 'unique':
            clean_name = sanitize_tw_unique_name(name)
            query['name'] = clean_name
        else:
            cat = resolve_rare_category(slot, base)
            if cat:
                query['filters']['type_filters']['filters']['category'] = {'option': cat}
        if stat_ids:
            if (
                not isinstance(stat_ids, list)
                or len(stat_ids) > 12
                or any(
                    not isinstance(x, str)
                    or not re.fullmatch(r'[a-z]{2,20}\.[a-z0-9_]{3,80}', x)
                    for x in stat_ids
                )
            ):
                raise ValueError('詞綴搜尋條件格式不正確')
            if stat_filters is not None:
                if not isinstance(stat_filters, list) or len(stat_filters) > 12:
                    raise ValueError('詞綴數值條件格式不正確')
                parsed = []
                for f in stat_filters:
                    if not isinstance(f, dict) or f.get('id') not in stat_ids:
                        raise ValueError('詞綴數值條件無效')
                    obj = {'id': f['id'], 'disabled': False}
                    value = {}
                    for field in ('min', 'max', 'option'):
                        v = f.get(field)
                        if v is not None and v != '':
                            if (
                                not isinstance(v, (int, float))
                                or isinstance(v, bool)
                                or not -1000000000 <= v <= 1000000000
                            ):
                                raise ValueError('詞綴數值必須是有效數字')
                            value[field] = v
                    if value:
                        obj['value'] = value
                    parsed.append(obj)
                query['stats'] = [{'type': 'and', 'filters': parsed}]
            else:
                query['stats'] = [
                    {'type': 'and', 'filters': [{'id': x, 'disabled': False} for x in dict.fromkeys(stat_ids)]}
                ]
    else:
        query['type'] = name.strip()
        query['filters'] = {}
    return query


def build_direct_q_url(name, league, kind='unique', base='', stat_ids=None, stat_filters=None, status_option='securable', slot=''):
    query = build_trade_query(name, league, kind, base, stat_ids, stat_filters, status_option=status_option, slot=slot)
    q_json = json.dumps({'query': query, 'sort': {'price': 'asc'}}, ensure_ascii=False, separators=(',', ':'))
    return (
        'https://pathofexile.tw/trade/search/'
        + urllib.parse.quote(league.strip(), safe='')
        + '?q='
        + urllib.parse.quote(q_json, safe='')
    )


def execute_trade_search(name, league, kind='unique', base='', stat_ids=None, stat_filters=None, status_option='securable', slot=''):
    query = build_trade_query(name, league, kind, base, stat_ids, stat_filters, status_option=status_option, slot=slot)
    payload = json.dumps({'query': query, 'sort': {'price': 'asc'}}, ensure_ascii=False).encode('utf-8')
    url = 'https://pathofexile.tw/api/trade/search/' + urllib.parse.quote(league.strip(), safe='')
    req = urllib.request.Request(
        url,
        data=payload,
        headers={
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0 Safari/537.36',
            'Content-Type': 'application/json',
            'Accept': 'application/json',
            'Origin': 'https://pathofexile.tw',
            'Referer': 'https://pathofexile.tw/trade',
        },
        method='POST',
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as response:
            data = json.loads(response.read(500_000))
    except urllib.error.HTTPError as e:
        detail = e.read(1500).decode('utf-8', 'replace')
        if e.code == 403:
            raise ValueError('CLOUDFLARE_403')
        if 'Unknown item name' in detail:
            tried_name = query.get('name') or query.get('type') or name
            raise ValueError(
                f'台服市集無法辨識物品名稱「{tried_name}」（請確認輸入的是台服官方繁體中文名稱）'
            )
        raise ValueError(f'台服交易網站拒絕搜尋（HTTP {e.code}）：{detail[:250]}')
    except (urllib.error.URLError, TimeoutError) as e:
        raise ValueError(f'無法連線台服交易搜尋服務：{e}')
    search_id = data.get('id') if isinstance(data, dict) else None
    if not isinstance(search_id, str) or not re.fullmatch(r'[A-Za-z0-9_-]{4,4096}', search_id):
        raise ValueError('台服未回傳有效搜尋 ID：' + str(data)[:250])
    trade_url = 'https://pathofexile.tw/trade/search/' + urllib.parse.quote(league.strip(), safe='') + '/' + search_id
    return {
        'id': search_id,
        'url': trade_url,
        'result': data.get('result') or [],
        'total': data.get('total', 0),
    }


def trade_link(name, league, kind='unique', base='', stat_ids=None, stat_filters=None, status_option='securable', slot=''):
    try:
        return execute_trade_search(name, league, kind, base, stat_ids, stat_filters, status_option=status_option, slot=slot)['url']
    except ValueError as e:
        if str(e) == 'CLOUDFLARE_403':
            return build_direct_q_url(name, league, kind, base, stat_ids, stat_filters, status_option=status_option, slot=slot)
        raise


CURRENCY_ZH = {
    'divine': '神聖石',
    'chaos': '混沌石',
    'exalted': '崇高石',
    'mirror': '卡蘭德的魔鏡',
    'vaal': '瓦爾寶珠',
    'alchemy': '點金石',
    'alteration': '改造石',
    'chromatic': '幻色石',
    'jewellers': '工匠石',
    'fusing': '鏈結石',
    'scouring': '重鑄石',
    'regret': '後悔石',
    'gcp': '寶石匠的稜鏡',
    'chisel': '製圖釘',
    'blessed': '祝福石',
}


def fetch_trade_listings(item_ids, search_id):
    if not item_ids:
        return []
    batch = item_ids[:10]
    url = f"https://pathofexile.tw/api/trade/fetch/{','.join(batch)}?query={urllib.parse.quote(search_id, safe='')}"
    req = urllib.request.Request(
        url,
        headers={
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0 Safari/537.36',
            'Accept': 'application/json',
            'Origin': 'https://pathofexile.tw',
            'Referer': 'https://pathofexile.tw/trade',
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as r:
            data = json.loads(r.read(1_500_000))
    except Exception:
        return []
    out = []
    for entry in data.get('result', []) if isinstance(data, dict) else []:
        if not isinstance(entry, dict):
            continue
        listing = entry.get('listing') or {}
        price_obj = listing.get('price') or {}
        amount = price_obj.get('amount')
        curr = price_obj.get('currency', '')
        curr_zh = CURRENCY_ZH.get(curr, curr)
        price_str = f"{amount} {curr_zh}" if amount is not None and curr else '未標價'
        acc = listing.get('account') or {}
        ign = acc.get('lastCharacterName') or acc.get('name') or '未知賣家'
        it = entry.get('item') or {}
        it_name = ' '.join(x for x in [it.get('name', ''), it.get('typeLine', '')] if x).strip()
        mods = (
            (it.get('fracturedMods') or [])
            + (it.get('implicitMods') or [])
            + (it.get('explicitMods') or [])
            + (it.get('craftedMods') or [])
        )
        out.append({
            'itemId': entry.get('id', ''),
            'itemName': it_name,
            'price': price_str,
            'seller': ign,
            'mods': mods[:8],
            'whisper': listing.get('whisper', ''),
        })
    return out


# --- 多人隔離 10 分鐘自動監控系統 ---
MONITOR_FILE = DATA_DIR / 'monitors_multi.json'
LEGACY_MONITOR_FILE = ROOT / 'monitors.json'
MONITOR_LOCK = threading.Lock()
MONITOR_STATE = {
    'users': {},
}


def valid_client_id(raw):
    s = str(raw or '').strip()
    if re.fullmatch(r'[A-Za-z0-9_-]{6,64}', s):
        return s
    return 'default'


def get_user_bucket_unlocked(client_id):
    cid = valid_client_id(client_id)
    users = MONITOR_STATE.setdefault('users', {})
    if cid not in users:
        users[cid] = {
            'monitors': [],
            'alerts': [],
            'discordWebhook': '',
            'updatedAt': time.time(),
        }
    return users[cid]


def load_monitors():
    if MONITOR_FILE.exists():
        try:
            data = json.loads(MONITOR_FILE.read_text(encoding='utf-8'))
            if isinstance(data, dict) and isinstance(data.get('users'), dict):
                MONITOR_STATE['users'] = data['users']
                return
        except Exception:
            pass
    if LEGACY_MONITOR_FILE.exists():
        try:
            old = json.loads(LEGACY_MONITOR_FILE.read_text(encoding='utf-8'))
            if isinstance(old, dict):
                MONITOR_STATE['users']['default'] = {
                    'monitors': old.get('monitors', []),
                    'alerts': old.get('alerts', [])[:60],
                    'discordWebhook': old.get('discordWebhook', ''),
                    'updatedAt': time.time(),
                }
                save_monitors_unlocked()
        except Exception:
            pass


def save_monitors_unlocked():
    try:
        for u in MONITOR_STATE.get('users', {}).values():
            u['alerts'] = (u.get('alerts') or [])[:60]
        MONITOR_FILE.write_text(json.dumps(MONITOR_STATE, ensure_ascii=False, indent=2), encoding='utf-8')
    except Exception:
        pass


load_monitors()


def send_discord_notification(webhook_url, title, description, trade_url, fields=None):
    if not webhook_url or not webhook_url.startswith(('https://discord.com/api/webhooks/', 'https://discordapp.com/api/webhooks/')):
        return False
    embed = {
        'title': title[:250],
        'description': description[:2000],
        'url': trade_url,
        'color': 3912586,
        'timestamp': datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%SZ'),
        'footer': {'text': 'POE 裝備統計助手 · 每 10 分鐘自動監控'},
    }
    if fields:
        embed['fields'] = fields[:10]
    body = json.dumps({'username': 'POE 市集監控助手', 'embeds': [embed]}, ensure_ascii=False).encode('utf-8')
    req = urllib.request.Request(
        webhook_url,
        data=body,
        headers={
            'User-Agent': 'Mozilla/5.0 POEStatsMonitor/1.0',
            'Content-Type': 'application/json',
        },
        method='POST',
    )
    with urllib.request.urlopen(req, timeout=10) as r:
        return r.status in (200, 204)


def run_single_monitor_check(client_id, monitor_id, is_initial=False):
    with MONITOR_LOCK:
        bucket = get_user_bucket_unlocked(client_id)
        mon = next((m for m in bucket['monitors'] if m['id'] == monitor_id), None)
        if not mon:
            return None
        params = {
            'name': mon['queryName'],
            'league': mon['league'],
            'kind': mon['kind'],
            'base': mon.get('base', ''),
            'stat_ids': mon.get('statIds', []),
            'stat_filters': mon.get('statFilters', []),
            'status_option': mon.get('statusOption', 'securable'),
            'slot': mon.get('slot', ''),
        }
        seen_set = set(mon.get('seenIds', []))
        display_name = mon['displayName']
        cond_summary = mon.get('condSummary', '')

    now_ts = time.time()
    try:
        res = execute_trade_search(**params)
        result_ids = res['result']
        new_ids = [iid for iid in result_ids if iid not in seen_set]
        listings = []
        if new_ids and not is_initial:
            listings = fetch_trade_listings(new_ids[:10], res['id'])

        with MONITOR_LOCK:
            bucket = get_user_bucket_unlocked(client_id)
            mon = next((m for m in bucket['monitors'] if m['id'] == monitor_id), None)
            if not mon:
                return None
            merged_seen = list(dict.fromkeys(result_ids + mon.get('seenIds', [])))[:500]
            mon['seenIds'] = merged_seen
            mon['lastChecked'] = now_ts
            mon['nextCheck'] = now_ts + mon.get('intervalSec', 600)
            mon['lastTotal'] = res['total']
            mon['lastUrl'] = res['url']
            mon['lastError'] = ''
            webhook_url = bucket.get('discordWebhook', '').strip()

            created_alerts = []
            if new_ids and not is_initial:
                if listings:
                    for item in listings:
                        alert = {
                            'id': uuid.uuid4().hex[:12],
                            'monitorId': monitor_id,
                            'displayName': display_name,
                            'league': params['league'],
                            'price': item['price'],
                            'seller': item['seller'],
                            'mods': item['mods'],
                            'url': res['url'],
                            'time': datetime.now().strftime('%H:%M:%S'),
                            'timestamp': now_ts,
                            'browserNotified': False,
                        }
                        created_alerts.append(alert)
                else:
                    alert = {
                        'id': uuid.uuid4().hex[:12],
                        'monitorId': monitor_id,
                        'displayName': display_name,
                        'league': params['league'],
                        'price': f'新增 {len(new_ids)} 筆上架',
                        'seller': '點擊前往賣場查看',
                        'mods': [],
                        'url': res['url'],
                        'time': datetime.now().strftime('%H:%M:%S'),
                        'timestamp': now_ts,
                        'browserNotified': False,
                    }
                    created_alerts.append(alert)

                bucket['alerts'] = (created_alerts + bucket.get('alerts', []))[:60]

            save_monitors_unlocked()

        if created_alerts and webhook_url:
            for al in created_alerts[:5]:
                fields = [
                    {'name': '聯盟', 'value': al['league'], 'inline': True},
                    {'name': '標價', 'value': al['price'], 'inline': True},
                    {'name': '賣家', 'value': al['seller'], 'inline': True},
                ]
                if cond_summary:
                    fields.append({'name': '監控條件', 'value': cond_summary, 'inline': False})
                if al['mods']:
                    fields.append({'name': '物品詞綴', 'value': '\n'.join(al['mods'][:6]), 'inline': False})
                try:
                    send_discord_notification(
                        webhook_url,
                        f"🔔 POE 市集新商品：{al['displayName']}",
                        f"在 **{al['league']}** 發現符合條件的新商品！點擊標題直接開啟台服交易頁面。",
                        al['url'],
                        fields=fields,
                    )
                except Exception:
                    pass

        return {'total': res['total'], 'newCount': 0 if is_initial else len(new_ids), 'url': res['url']}
    except Exception as exc:
        err_msg = '雲端伺服器 IP 遭台服 Cloudflare 阻擋（請改用本機執行或自架主機）' if str(exc) == 'CLOUDFLARE_403' else str(exc)[:200]
        with MONITOR_LOCK:
            bucket = get_user_bucket_unlocked(client_id)
            mon = next((m for m in bucket['monitors'] if m['id'] == monitor_id), None)
            if mon:
                mon['lastChecked'] = now_ts
                mon['nextCheck'] = now_ts + mon.get('intervalSec', 600)
                mon['lastError'] = err_msg
                save_monitors_unlocked()
        if is_initial:
            raise ValueError(err_msg)
        return {'error': err_msg}


def monitor_worker_loop():
    while True:
        time.sleep(15)
        now = time.time()
        due_tasks = []
        with MONITOR_LOCK:
            for cid, bucket in list(MONITOR_STATE.get('users', {}).items()):
                for m in bucket.get('monitors', []):
                    if m.get('enabled', True) and now >= m.get('nextCheck', 0):
                        due_tasks.append((cid, m['id']))
                        if len(due_tasks) >= 12:
                            break
                if len(due_tasks) >= 12:
                    break
        for cid, mid in due_tasks:
            run_single_monitor_check(cid, mid, is_initial=False)
            time.sleep(random.uniform(2.5, 4.5))


threading.Thread(target=monitor_worker_loop, daemon=True).start()


# --- 官方 Trade API 物品資料庫 ---
ITEM_CACHE = {}
ITEM_CACHE_LOCK = threading.Lock()
ITEM_URLS = {
    'en': [
        'https://www.pathofexile.com/api/trade/data/items',
        'https://pathofexile.com/api/trade/data/items',
    ],
    'tw': [
        'https://pathofexile.tw/api/trade/data/items',
    ],
}


def item_catalogue_file(lang):
    return CATALOGUE_DIR / f'items_{lang}.json'


def fetch_raw_items(lang, refresh=False):
    file = item_catalogue_file(lang)
    if file.exists() and not refresh:
        try:
            return json.loads(file.read_text(encoding='utf-8'))
        except Exception:
            pass
    for url in ITEM_URLS[lang]:
        req = urllib.request.Request(
            url,
            headers={
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0 Safari/537.36',
                'Accept': 'application/json',
                'Accept-Language': 'en-US,en;q=0.9' if lang == 'en' else 'zh-TW,zh;q=0.9',
            },
        )
        try:
            with urllib.request.urlopen(req, timeout=15) as r:
                data = json.loads(r.read(15_000_000))
            if isinstance(data, dict) and isinstance(data.get('result'), list):
                file.write_text(json.dumps(data, ensure_ascii=False), encoding='utf-8')
                return data
        except Exception:
            continue
    if file.exists():
        try:
            return json.loads(file.read_text(encoding='utf-8'))
        except Exception:
            pass
    return None


def norm_item_key(s):
    return re.sub(r'\s+', ' ', s.replace('’', "'").strip()).lower()


def get_official_item_map(refresh=False):
    with ITEM_CACHE_LOCK:
        now = time.time()
        if not refresh and ITEM_CACHE.get('expires', 0) > now:
            return ITEM_CACHE['maps']
        maps = {
            'unique': {},
            'gem': {},
            'base': {},
            'tw_unique_names': set(),
            'tw_base_names': set(),
            'tw_gem_names': set(),
            'search_items': [],
        }
        en_data = fetch_raw_items('en', refresh=refresh)
        tw_data = fetch_raw_items('tw', refresh=refresh)

        if tw_data:
            for g in tw_data.get('result', []):
                if not isinstance(g, dict):
                    continue
                gid = g.get('id')
                for e in g.get('entries', []):
                    if not isinstance(e, dict):
                        continue
                    flags = e.get('flags') or {}
                    t_name = e.get('name', '').strip()
                    t_type = e.get('type', '').strip()
                    if flags.get('unique') and t_name:
                        maps['tw_unique_names'].add(t_name)
                    if gid == 'gems' and t_type:
                        maps['tw_gem_names'].add(t_type)
                    elif t_type and gid != 'gems':
                        maps['tw_base_names'].add(t_type)

        if en_data and tw_data:
            en_groups = {
                g.get('id'): g.get('entries', [])
                for g in en_data.get('result', [])
                if isinstance(g, dict)
            }
            tw_groups = {
                g.get('id'): g.get('entries', [])
                for g in tw_data.get('result', [])
                if isinstance(g, dict)
            }
            for gid, en_entries in en_groups.items():
                tw_entries = tw_groups.get(gid)
                if not tw_entries:
                    continue

                if len(en_entries) == len(tw_entries):
                    for en_e, tw_e in zip(en_entries, tw_entries):
                        en_flags = en_e.get('flags') or {}
                        tw_flags = tw_e.get('flags') or {}
                        if en_flags.get('unique') != tw_flags.get('unique'):
                            continue
                        en_name, tw_name = en_e.get('name', ''), tw_e.get('name', '')
                        en_type, tw_type = en_e.get('type', ''), tw_e.get('type', '')
                        if en_flags.get('unique') and en_name and tw_name:
                            maps['unique'][norm_item_key(en_name)] = tw_name
                        if gid == 'gems' and en_type and tw_type:
                            maps['gem'][norm_item_key(en_type)] = tw_type
                        if en_type and tw_type and gid != 'gems':
                            maps['base'][norm_item_key(en_type)] = tw_type
                else:
                    en_non_u = [e for e in en_entries if not (e.get('flags') or {}).get('unique')]
                    tw_non_u = [e for e in tw_entries if not (e.get('flags') or {}).get('unique')]
                    local_base_map = {}
                    if len(en_non_u) == len(tw_non_u):
                        for en_e, tw_e in zip(en_non_u, tw_non_u):
                            et, tt = en_e.get('type', ''), tw_e.get('type', '')
                            if et and tt:
                                local_base_map[et] = tt
                                if gid == 'gems':
                                    maps['gem'][norm_item_key(et)] = tt
                                else:
                                    maps['base'][norm_item_key(et)] = tt

                    en_u_by_key = {}
                    for e in en_entries:
                        if (e.get('flags') or {}).get('unique') and e.get('name'):
                            k = (e.get('type', ''), e.get('disc', ''))
                            en_u_by_key.setdefault(k, []).append(e)

                    tw_u_by_key = {}
                    for e in tw_entries:
                        if (e.get('flags') or {}).get('unique') and e.get('name'):
                            k = (e.get('type', ''), e.get('disc', ''))
                            tw_u_by_key.setdefault(k, []).append(e)

                    for (en_b, disc), en_list in en_u_by_key.items():
                        tw_b = local_base_map.get(en_b)
                        if not tw_b:
                            continue
                        tw_list = tw_u_by_key.get((tw_b, disc), [])
                        if len(en_list) == len(tw_list):
                            for en_e, tw_e in zip(en_list, tw_list):
                                maps['unique'][norm_item_key(en_e['name'])] = tw_e['name']

        rev_unique = {tw_v: en_k for en_k, tw_v in maps['unique'].items()}
        rev_base = {tw_v: en_k for en_k, tw_v in maps['base'].items()}
        rev_gem = {tw_v: en_k for en_k, tw_v in maps['gem'].items()}
        s_items = []
        for zh_n in sorted(maps['tw_unique_names']):
            s_items.append({'kind': 'unique', 'zh': zh_n, 'en': rev_unique.get(zh_n, '')})
        for zh_b in sorted(maps['tw_base_names']):
            s_items.append({'kind': 'rare', 'zh': zh_b, 'en': rev_base.get(zh_b, '')})
        for zh_g in sorted(maps['tw_gem_names']):
            s_items.append({'kind': 'gem', 'zh': zh_g, 'en': rev_gem.get(zh_g, '')})
        maps['search_items'] = s_items

        ITEM_CACHE.update(maps=maps, expires=now + 86400)
        return maps


def search_official_items(query_str, kind_filter='all', limit=25):
    q = str(query_str or '').strip().lower()
    if not q:
        return []
    maps = get_official_item_map()
    s_items = maps.get('search_items', [])
    tokens = [t for t in re.split(r'\s+', q) if t]
    scored = []
    for it in s_items:
        if kind_filter and kind_filter != 'all' and it['kind'] != kind_filter:
            continue
        zh_low = it['zh'].lower()
        en_low = it['en'].lower()
        hay = zh_low + ' ' + en_low
        if not all(t in hay for t in tokens):
            continue
        exact_boost = 0 if (q == zh_low or q == en_low) else 1
        prefix_boost = 0 if (zh_low.startswith(q) or en_low.startswith(q)) else 1
        scored.append((exact_boost, prefix_boost, len(it['zh']), it))
    scored.sort(key=lambda x: (x[0], x[1], x[2]))
    return [x[3] for x in scored[:limit]]


VERIFIED_NAMES = {
    ('unique', 'Crown of the Inward Eye'): ('暗眼之冠', 'Crown_of_the_Inward_Eye'),
    ('unique', "Replica Dragonfang's Flight"): ('贗品．龍牙翱翔', 'Replica_Dragonfangs_Flight'),
    ('unique', 'Bottled Faith'): ('瓶中信仰', 'Bottled_Faith'),
    ('unique', "Rumi's Concoction"): ('魯米的靈藥', 'Rumis_Concoction'),
    ('unique', 'The Red Dream'): ('赤影夢境', 'The_Red_Dream'),
    ('unique', 'Militant Faith'): ('激進的信仰', 'Militant_Faith'),
    ('unique', "Watcher's Eye"): ('看守之眼', 'Watchers_Eye'),
    ('unique', 'The Light of Meaning'): ('意涵之光', 'The_Light_of_Meaning'),
    ('unique', 'Stormshroud'): ('風暴籠罩', 'Stormshroud'),
    ('gem', 'Greater Multiple Projectiles'): ('高階多重投射輔助', 'Greater_Multiple_Projectiles_Support'),
    ('gem', 'Returning Projectiles'): ('投射物返回輔助', 'Returning_Projectiles_Support'),
    ('gem', 'Frostblink of Wintry Blast'): ('霜漣之瞬．寒風', 'Frostblink_of_Wintry_Blast'),
}


class TitleReader(HTMLParser):
    def __init__(self):
        super().__init__()
        self.in_title = False
        self.title = []

    def handle_starttag(self, tag, attrs):
        if tag == 'title':
            self.in_title = True

    def handle_endtag(self, tag):
        if tag == 'title':
            self.in_title = False

    def handle_data(self, data):
        if self.in_title:
            self.title.append(data)


CACHE = {}
CACHE_LOCK = threading.Lock()


def name_candidates(name, kind):
    clean = re.sub(r"[',’:.]", '', name).strip()
    stem = re.sub(r'\s+', '_', clean)
    out = [stem]
    if kind == 'gem' and not stem.endswith('_Support'):
        out.insert(0, stem + '_Support')
    if kind == 'gem' and stem.endswith('_Support'):
        out.append(stem[:-8])
    return list(dict.fromkeys(out))


UNIQUE_PREFIXES = (
    ('foulborn ', '穢生'),
    ('replica ', '贗品．'),
)
BASE_STRIP_PREFIXES = (
    'superior ', 'synthesised ', 'fractured ', 'mirrored ', 'split ', 'foulborn ',
)


def lookup_official_item(name, kind):
    maps = get_official_item_map()
    bucket = maps.get(kind, {})
    k = norm_item_key(name)
    if k in bucket:
        return bucket[k]
    if kind == 'unique':
        for en_pre, zh_pre in UNIQUE_PREFIXES:
            if k.startswith(en_pre):
                inner = k[len(en_pre):].strip()
                if inner in bucket:
                    return zh_pre + bucket[inner]
    if kind == 'base':
        cleaned = k
        changed = True
        while changed:
            changed = False
            for pre in BASE_STRIP_PREFIXES:
                if cleaned.startswith(pre):
                    cleaned = cleaned[len(pre):].strip()
                    changed = True
        if cleaned in bucket:
            return bucket[cleaned]
    if kind == 'gem':
        if not k.endswith(' support') and (k + ' support') in bucket:
            return bucket[k + ' support']
        if k.endswith(' support') and k[:-8] in bucket:
            return bucket[k[:-8]]
    return None


def resolve_name(name, kind, allow_web=True):
    name = name.strip()
    if kind not in ('unique', 'gem', 'base') or not name or len(name) > 140:
        return {'en': name, 'zh': None, 'status': 'unverified', 'source': None}
    seed = VERIFIED_NAMES.get((kind, name))
    if seed:
        return {'en': name, 'zh': seed[0], 'status': 'verified', 'source': 'https://poedb.tw/tw/' + seed[1]}
    official_zh = lookup_official_item(name, kind)
    if official_zh:
        return {'en': name, 'zh': official_zh, 'status': 'verified', 'source': 'https://pathofexile.tw/trade'}
    if not allow_web:
        return {'en': name, 'zh': None, 'status': 'unverified', 'source': None}
    if kind == 'unique':
        low = norm_item_key(name)
        for en_pre, zh_pre in UNIQUE_PREFIXES:
            if low.startswith(en_pre):
                inner_res = resolve_name(name[len(en_pre):].strip(), 'unique', allow_web=True)
                if inner_res.get('status') == 'verified' and inner_res.get('zh'):
                    inner_clean = sanitize_tw_unique_name(inner_res['zh'])
                    return {'en': name, 'zh': zh_pre + inner_clean, 'status': 'verified', 'source': inner_res.get('source')}

    key = (kind, name)
    with CACHE_LOCK:
        prev = CACHE.get(key)
        if prev and (prev['status'] == 'verified' or time.time() - prev['at'] < 900):
            return prev['value']

    result = {'en': name, 'zh': None, 'status': 'unverified', 'source': None}
    for slug in name_candidates(name, kind):
        url = 'https://poedb.tw/tw/' + urllib.parse.quote(slug, safe='_')
        try:
            req = urllib.request.Request(
                url,
                headers={
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/130.0 Safari/537.36',
                    'Accept-Language': 'zh-TW,zh;q=0.9',
                },
            )
            with urllib.request.urlopen(req, timeout=7) as r:
                final = urllib.parse.urlparse(r.geturl())
                if final.hostname not in ('poedb.tw', 'www.poedb.tw') or not final.path.startswith('/tw/'):
                    continue
                body = r.read(400_000).decode('utf-8', 'replace')
            reader = TitleReader()
            reader.feed(body)
            title = html.unescape(''.join(reader.title)).strip()
            zh = re.split(r'\s*[-–|]\s*(?:流亡編年史|Path of Exile)', title)[0].strip()
            if not zh or not re.search(r'[\u3400-\u9fff]', zh) or len(zh) > 75 or '404' in title or 'Not Found' in title:
                continue
            if kind == 'unique':
                m = re.search(r'<h1\b[^>]*>(.*?)</h1>', body, re.S | re.I)
                if m:
                    h1_inner = m.group(1)
                    first_a = re.search(r'<a\b[^>]*>(.*?)</a>', h1_inner, re.S | re.I)
                    if first_a:
                        heading = html.unescape(re.sub(r'<[^>]*>', '', first_a.group(1))).strip()
                    else:
                        heading = html.unescape(re.sub(r'<[^>]*>', '', h1_inner)).strip()
                    if heading and re.search(r'[\u3400-\u9fff]', heading) and len(heading) < 65:
                        zh = sanitize_tw_unique_name(heading)
                else:
                    zh = sanitize_tw_unique_name(zh.split()[0])
            result = {'en': name, 'zh': zh, 'status': 'verified', 'source': r.geturl()}
            break
        except Exception:
            continue
    with CACHE_LOCK:
        CACHE[key] = {'value': result, 'status': result['status'], 'at': time.time()}
    return result


def resolve_batch(entries, seed_only=False):
    if not isinstance(entries, list) or len(entries) > 100:
        raise ValueError('每次最多查詢 100 個名稱')
    clean = []
    for x in entries:
        if not isinstance(x, dict):
            continue
        n, k = x.get('name', ''), x.get('kind', '')
        if isinstance(n, str) and len(n) <= 140 and k in ('unique', 'gem', 'base'):
            clean.append((n, k))
    get_official_item_map()
    with ThreadPoolExecutor(max_workers=5) as pool:
        results = list(pool.map(lambda x: resolve_name(x[0], x[1], allow_web=not seed_only), clean))
    return results


class Handler(BaseHTTPRequestHandler):
    def get_client_id(self):
        parsed = urllib.parse.urlparse(self.path)
        qs = urllib.parse.parse_qs(parsed.query)
        raw = self.headers.get('X-Client-Id') or (qs.get('cid') or [''])[0]
        return valid_client_id(raw)

    def reply(self, obj, status=200):
        body = json.dumps(obj, ensure_ascii=False).encode()
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        route = parsed.path
        qs = urllib.parse.parse_qs(parsed.query)
        if route == '/health':
            self.reply({'ok': True, 'version': '2.35-web'})
            return
        if route == '/api/catalogue-status':
            try:
                en, zh, meta = fetch_trade_stats()
                self.reply({'ok': True, 'meta': meta})
            except Exception as e:
                self.reply({'ok': False, 'error': str(e)})
            return
        if route == '/api/items/search':
            q = (qs.get('q') or [''])[0]
            k = (qs.get('kind') or ['all'])[0]
            self.reply({'ok': True, 'items': search_official_items(q, k)})
            return
        if route == '/api/stats/search':
            q = (qs.get('q') or [''])[0]
            k = (qs.get('kind') or ['all'])[0]
            try:
                self.reply({'ok': True, 'stats': search_trade_stats(q, k)})
            except Exception as e:
                self.reply({'ok': False, 'error': str(e)}, 400)
            return
        if route == '/api/mod-overrides':
            items, raw_copy = list_mod_overrides()
            self.reply({'ok': True, 'count': len(items), 'overrides': items, 'raw': raw_copy})
            return
        if route == '/api/monitors':
            cid = self.get_client_id()
            with MONITOR_LOCK:
                bucket = get_user_bucket_unlocked(cid)
                safe_mons = [{k: v for k, v in m.items() if k != 'seenIds'} for m in bucket['monitors']]
                self.reply({
                    'ok': True,
                    'clientId': cid,
                    'monitors': safe_mons,
                    'alerts': bucket['alerts'],
                    'discordWebhook': bucket['discordWebhook'],
                })
            return
        if route not in ('/', '/index.html'):
            self.send_error(404)
            return
        body = (ROOT / 'index.html').read_bytes()
        self.send_response(200)
        self.send_header('Content-Type', 'text/html; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        route = parsed.path
        allowed_paths = (
            '/api/parse', '/api/parse-item-text', '/api/poedb', '/api/trade-link', '/api/names',
            '/api/match-mods', '/api/catalogue-import', '/api/catalogue-refresh',
            '/api/mod-overrides/save', '/api/mod-overrides/delete', '/api/mod-overrides/import',
            '/api/monitors/add', '/api/monitors/toggle', '/api/monitors/delete', '/api/monitors/set-all-status',
            '/api/monitors/check', '/api/monitors/settings', '/api/monitors/test-discord',
            '/api/monitors/ack', '/api/monitors/clear-alerts',
        )
        if route not in allowed_paths:
            self.send_error(404)
            return
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if size < 1 or size > MAX * 2:
                raise ValueError('輸入資料過大或空白')
            data = json.loads(self.rfile.read(size))
            cid = self.get_client_id()

            if route == '/api/catalogue-import':
                self.reply({'ok': True, 'imported': import_catalogue(data.get('lang'), data.get('catalogue'))})
                return
            elif route == '/api/catalogue-refresh':
                en, zh, meta = fetch_trade_stats(refresh=True)
                get_official_item_map(refresh=True)
                self.reply({'ok': True, 'meta': meta})
                return
            elif route == '/api/mod-overrides/save':
                entry = save_mod_override(
                    data.get('mod', ''),
                    data.get('id', ''),
                    data.get('zh', ''),
                    data.get('en', ''),
                    data.get('option'),
                )
                self.reply({'ok': True, 'entry': entry, 'count': len(MOD_OVERRIDES)})
                return
            elif route == '/api/mod-overrides/delete':
                cnt = delete_mod_override(data.get('key') or data.get('mod') or '')
                self.reply({'ok': True, 'count': cnt})
                return
            elif route == '/api/mod-overrides/import':
                res = import_mod_overrides(data.get('data'))
                self.reply({'ok': True, **res})
                return
            elif route == '/api/parse':
                result = parse_pob(data.get('code', ''), data.get('source', ''))
            elif route == '/api/parse-item-text':
                self.reply({'ok': True, 'parsed': parse_pasted_item_text(data.get('text', ''))})
                return
            elif route == '/api/poedb':
                result = fetch_poedb(data.get('url', ''))
            elif route == '/api/match-mods':
                self.reply({'ok': True, 'mods': match_mods(data.get('mods', []))})
                return
            elif route == '/api/names':
                self.reply({'ok': True, 'names': resolve_batch(data.get('entries', []), data.get('seedOnly', False))})
                return
            elif route == '/api/trade-link':
                q_name = str(data.get('name', '')).strip()
                kind = data.get('kind', 'unique')
                base = str(data.get('base', '')).strip()
                status_opt = data.get('statusOption', 'securable')
                if kind in ('unique', 'gem') and q_name and not re.search(r'[\u3400-\u9fff]', q_name):
                    r = resolve_name(q_name, kind, allow_web=True)
                    if r.get('zh'):
                        q_name = r['zh']
                if kind == 'rare' and base and not re.search(r'[\u3400-\u9fff]', base):
                    r = resolve_name(base, 'base', allow_web=True)
                    if r.get('zh'):
                        base = r['zh']
                self.reply({
                    'ok': True,
                    'url': trade_link(
                        q_name,
                        data.get('league', ''),
                        kind,
                        base,
                        data.get('statIds', []),
                        data.get('statFilters'),
                        status_option=status_opt,
                        slot=str(data.get('slot', '')).strip(),
                    ),
                })
                return
            elif route == '/api/monitors/add':
                q_name = str(data.get('name', '')).strip()
                d_name = str(data.get('displayName', q_name)).strip()
                league = str(data.get('league', '')).strip()
                kind = data.get('kind', 'unique')
                base = str(data.get('base', '')).strip()
                stat_ids = data.get('statIds') or []
                stat_filters = data.get('statFilters') or []
                cond_summary = str(data.get('condSummary', '')).strip()
                status_opt = data.get('statusOption', 'securable')
                if kind in ('unique', 'gem') and q_name and not re.search(r'[\u3400-\u9fff]', q_name):
                    r = resolve_name(q_name, kind, allow_web=True)
                    if r.get('zh'):
                        q_name = r['zh']
                        if not d_name:
                            d_name = r['zh']
                if kind == 'rare' and base and not re.search(r'[\u3400-\u9fff]', base):
                    r = resolve_name(base, 'base', allow_web=True)
                    if r.get('zh'):
                        base = r['zh']
                        if not d_name or d_name == data.get('base'):
                            d_name = r['zh']
                if kind == 'unique':
                    q_name = sanitize_tw_unique_name(q_name)
                if kind == 'rare' and not d_name:
                    d_name = base or '自訂稀有裝備'
                slot_val = str(data.get('slot', '')).strip()
                build_trade_query(q_name, league, kind, base, stat_ids, stat_filters, status_option=status_opt, slot=slot_val)
                mid = uuid.uuid4().hex[:10]
                now_ts = time.time()
                mon_obj = {
                    'id': mid,
                    'displayName': d_name,
                    'queryName': q_name,
                    'league': league,
                    'kind': kind,
                    'base': base,
                    'slot': slot_val,
                    'statIds': stat_ids,
                    'statFilters': stat_filters,
                    'condSummary': cond_summary,
                    'statusOption': status_opt,
                    'intervalSec': 600,
                    'enabled': True,
                    'createdAt': now_ts,
                    'lastChecked': 0,
                    'nextCheck': now_ts + 600,
                    'lastTotal': 0,
                    'lastUrl': '',
                    'lastError': '',
                    'seenIds': [],
                }
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    if len(bucket['monitors']) >= MAX_MONITORS_PER_USER:
                        raise ValueError(f'每位使用者最多可同時建立 {MAX_MONITORS_PER_USER} 項自動監控，請先刪除舊項目')
                    bucket['monitors'].insert(0, mon_obj)
                    save_monitors_unlocked()
                try:
                    init_res = run_single_monitor_check(cid, mid, is_initial=True)
                except Exception as exc:
                    with MONITOR_LOCK:
                        bucket = get_user_bucket_unlocked(cid)
                        bucket['monitors'] = [m for m in bucket['monitors'] if m['id'] != mid]
                        save_monitors_unlocked()
                    raise ValueError(f'建立監控失敗：{exc}')
                self.reply({'ok': True, 'monitorId': mid, 'initial': init_res})
                return
            elif route == '/api/monitors/toggle':
                mid = data.get('id')
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    mon = next((m for m in bucket['monitors'] if m['id'] == mid), None)
                    if not mon:
                        raise ValueError('找不到指定的監控項目')
                    mon['enabled'] = not mon.get('enabled', True)
                    if mon['enabled']:
                        mon['nextCheck'] = time.time() + mon.get('intervalSec', 600)
                    save_monitors_unlocked()
                self.reply({'ok': True})
                return
            elif route == '/api/monitors/delete':
                mid = data.get('id')
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    bucket['monitors'] = [m for m in bucket['monitors'] if m['id'] != mid]
                    save_monitors_unlocked()
                self.reply({'ok': True})
                return
            elif route == '/api/monitors/set-all-status':
                target_status = data.get('statusOption', 'securable')
                if target_status not in ('securable', 'available', 'online', 'onlineleague', 'any'):
                    target_status = 'securable'
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    ids = []
                    for m in bucket['monitors']:
                        m['statusOption'] = target_status
                        m['seenIds'] = []
                        if m.get('enabled', True):
                            ids.append(m['id'])
                    save_monitors_unlocked()
                for i in ids:
                    run_single_monitor_check(cid, i, is_initial=True)
                    time.sleep(0.8)
                self.reply({'ok': True, 'updated': len(ids)})
                return
            elif route == '/api/monitors/check':
                mid = data.get('id')
                if mid:
                    res = run_single_monitor_check(cid, mid, is_initial=False)
                    self.reply({'ok': True, 'result': res})
                else:
                    with MONITOR_LOCK:
                        bucket = get_user_bucket_unlocked(cid)
                        ids = [m['id'] for m in bucket['monitors'] if m.get('enabled', True)]
                    total_new = 0
                    for i in ids:
                        r = run_single_monitor_check(cid, i, is_initial=False)
                        if r and not r.get('error'):
                            total_new += r.get('newCount', 0)
                        time.sleep(1.2)
                    self.reply({'ok': True, 'checked': len(ids), 'newCount': total_new})
                return
            elif route == '/api/monitors/settings':
                wh = str(data.get('discordWebhook', '')).strip()
                if wh and not wh.startswith(('https://discord.com/api/webhooks/', 'https://discordapp.com/api/webhooks/')):
                    raise ValueError('Discord Webhook 網址格式不正確（應為 https://discord.com/api/webhooks/...）')
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    bucket['discordWebhook'] = wh
                    save_monitors_unlocked()
                self.reply({'ok': True})
                return
            elif route == '/api/monitors/test-discord':
                with MONITOR_LOCK:
                    saved_wh = get_user_bucket_unlocked(cid).get('discordWebhook', '')
                wh = str(data.get('discordWebhook', '')).strip() or saved_wh
                if not wh:
                    raise ValueError('請先輸入 Discord Webhook 網址')
                ok = send_discord_notification(
                    wh,
                    '✅ POE 市集監控測試通知',
                    '連線設定成功！當監控的裝備有新商品上架時，將會自動發送通知到此頻道。',
                    'https://pathofexile.tw/trade',
                )
                if not ok:
                    raise ValueError('Discord Webhook 發送失敗，請確認網址是否有效')
                self.reply({'ok': True})
                return
            elif route == '/api/monitors/ack':
                ack_ids = set(data.get('ids') or [])
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    for al in bucket['alerts']:
                        if al['id'] in ack_ids:
                            al['browserNotified'] = True
                    save_monitors_unlocked()
                self.reply({'ok': True})
                return
            elif route == '/api/monitors/clear-alerts':
                with MONITOR_LOCK:
                    bucket = get_user_bucket_unlocked(cid)
                    bucket['alerts'] = []
                    save_monitors_unlocked()
                self.reply({'ok': True})
                return

            self.reply({'ok': True, 'character': result})
        except Exception as e:
            self.reply({'ok': False, 'error': str(e)}, 400)

    def log_message(self, *args):
        pass


if __name__ == '__main__':
    host = '0.0.0.0'
    port = int(os.environ.get('PORT', '8766'))
    httpd = ThreadingHTTPServer((host, port), Handler)
    print(f'POE 裝備統計 V2.35 (過濾裝備自帶技能 + 精準抓取固定屬性 implicit + 稀有裝備獨立列出且同部位純詞綴搜尋): http://{host}:{port}/')
    is_cloud = any(os.environ.get(k) for k in ('PORT', 'RENDER', 'ZEABUR', 'RAILWAY_ENVIRONMENT', 'FLY_APP_NAME'))
    if not is_cloud:
        threading.Timer(0.8, lambda: webbrowser.open(f'http://127.0.0.1:{port}/')).start()
    httpd.serve_forever()
