"""
APLIKASI PENJUALAN SPG (online)
================================
Role:
  master      : kelola semua, superadmin
  kepala_depo : view dashboard/penjualan/laporan/absensi wilayahnya saja, bisa request tambah data
  spg         : absen harian, input penjualan, input stok masuk di toko yang ditugaskan (mobile-friendly)

Fitur v1.3: tampilan master/depo baru (sidebar, grafik tren 14 hari), tombol lihat password,
            perketat keamanan (anti-spoof IP, cek Origin, validasi input, koneksi DB selalu ditutup)
Fitur v1.2:
  - Absen harian SPG (masuk/pulang/izin/sakit), rekap untuk master & kepala depo
  - Nama sales (opsional) di toko & SPG; SPG otomatis memakai sales dari toko tempatnya bertugas
  - Stok awal per toko (hanya master), stok masuk diinput SPG di menu khusus

Keamanan:
  - password di-hash dengan scrypt + salt acak
  - sesi disimpan sebagai hash di database, cookie HttpOnly + SameSite=Strict (+Secure di HTTPS)
  - proteksi CSRF, rate limit & penguncian akun saat brute force
  - 2FA (Google Authenticator) opsional, wajib untuk master bila diaktifkan
  - CSP dengan nonce, HSTS, pemaksaan HTTPS
  - semua aktivitas tercatat di audit log
  - auto logout 30 menit idle untuk SPG & kepala_depo
"""
import base64, hashlib, hmac, io, json, os, re, secrets, sqlite3, struct, sys
import ipaddress, math, threading, time, unicodedata, uuid
from datetime import date, datetime, timedelta, timezone
from contextlib import contextmanager
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

APP_NAME    = "Penjualan SPG"
APP_VERSION = "1.3"
BASE_DIR    = Path(__file__).resolve().parent
DATA_DIR    = Path(os.environ.get("SPG_DATA_DIR", BASE_DIR / "data"))
DB_PATH     = DATA_DIR / "spg.db"
BACKUP_DIR  = DATA_DIR / "backup"

HOST          = os.environ.get("SPG_HOST", "127.0.0.1")
PORT          = int(os.environ.get("SPG_PORT", "8090"))
TRUST_PROXY   = os.environ.get("SPG_TRUST_PROXY", "0") == "1"
PROXY_HOPS    = max(1, int(os.environ.get("SPG_PROXY_HOPS", "1")))   # jumlah proxy tepercaya di depan aplikasi
REQUIRE_HTTPS = os.environ.get("SPG_REQUIRE_HTTPS", "1") == "1"
DEV_MODE      = os.environ.get("SPG_DEV", "0") == "1"
TZ_OFFSET     = int(os.environ.get("SPG_TZ_OFFSET", "7"))
EDIT_WINDOW_MIN = int(os.environ.get("SPG_EDIT_MENIT", "60"))
SATUAN = ("BOTOL", "DUS")
JENIS  = ("JUAL", "SAMPLE")

# Idle timeout per role (menit) — master tidak ada timeout
IDLE_TIMEOUT = {"spg": 30, "kepala_depo": 30, "master": 480}

TZ = timezone(timedelta(hours=TZ_OFFSET))
def now():       return datetime.now(TZ)
def now_iso():   return now().isoformat(timespec="seconds")
def today_str(): return now().date().isoformat()
def new_uid():   return uuid.uuid4().hex

# =====================================================================
# DATABASE
# =====================================================================
SCHEMA = """
PRAGMA journal_mode=WAL;
CREATE TABLE IF NOT EXISTS setting (key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS pengguna (
    uid TEXT PRIMARY KEY,
    username TEXT NOT NULL UNIQUE COLLATE NOCASE,
    nama TEXT NOT NULL,
    role TEXT NOT NULL,
    wilayah TEXT DEFAULT '',
    pw_hash TEXT NOT NULL, pw_salt TEXT NOT NULL,
    harus_ganti INTEGER DEFAULT 1,
    totp TEXT DEFAULT '', totp_aktif INTEGER DEFAULT 0,
    aktif INTEGER DEFAULT 1,
    telepon TEXT DEFAULT '', catatan TEXT DEFAULT '',
    gagal INTEGER DEFAULT 0, kunci_sampai TEXT DEFAULT '',
    terakhir_login TEXT DEFAULT '', dibuat TEXT NOT NULL, diubah TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS toko (
    uid TEXT PRIMARY KEY, nama TEXT NOT NULL, wilayah TEXT DEFAULT '', alamat TEXT DEFAULT '',
    catatan TEXT DEFAULT '', aktif INTEGER DEFAULT 1, dibuat TEXT NOT NULL, diubah TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS produk (
    uid TEXT PRIMARY KEY, kode TEXT NOT NULL, nama TEXT NOT NULL,
    harga_botol REAL DEFAULT 0, harga_dus REAL DEFAULT 0, isi_dus INTEGER DEFAULT 12,
    aktif INTEGER DEFAULT 1, urut INTEGER DEFAULT 0, dibuat TEXT NOT NULL, diubah TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS spg_toko (
    spg_uid TEXT NOT NULL, toko_uid TEXT NOT NULL, dibuat TEXT NOT NULL,
    PRIMARY KEY (spg_uid, toko_uid));
CREATE TABLE IF NOT EXISTS penjualan (
    uid TEXT PRIMARY KEY,
    waktu TEXT NOT NULL,
    tanggal TEXT NOT NULL,
    spg_uid TEXT NOT NULL, toko_uid TEXT NOT NULL, produk_uid TEXT NOT NULL,
    jenis TEXT NOT NULL,
    satuan TEXT NOT NULL,
    qty REAL NOT NULL,
    isi_dus INTEGER DEFAULT 1,
    harga REAL DEFAULT 0,
    total REAL DEFAULT 0,
    botol_setara REAL DEFAULT 0,
    catatan TEXT DEFAULT '',
    ip TEXT DEFAULT '', perangkat TEXT DEFAULT '',
    dihapus INTEGER DEFAULT 0, diubah TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS permintaan (
    uid TEXT PRIMARY KEY,
    waktu TEXT NOT NULL,
    peminta_uid TEXT NOT NULL,
    tipe TEXT NOT NULL,
    data TEXT NOT NULL,
    status TEXT DEFAULT 'pending',
    catatan_master TEXT DEFAULT '',
    diproses_waktu TEXT DEFAULT '');
CREATE TABLE IF NOT EXISTS sesi (
    id TEXT PRIMARY KEY,
    pengguna_uid TEXT NOT NULL, csrf TEXT NOT NULL,
    dibuat TEXT NOT NULL, terakhir TEXT NOT NULL, kedaluwarsa TEXT NOT NULL,
    ip TEXT DEFAULT '', perangkat TEXT DEFAULT '');
CREATE TABLE IF NOT EXISTS log (
    uid TEXT PRIMARY KEY, waktu TEXT NOT NULL, pengguna_uid TEXT DEFAULT '',
    username TEXT DEFAULT '', role TEXT DEFAULT '', aksi TEXT NOT NULL,
    detail TEXT DEFAULT '', ip TEXT DEFAULT '', perangkat TEXT DEFAULT '');
-- v1.2: absensi harian SPG (1 baris per SPG per hari)
CREATE TABLE IF NOT EXISTS absensi (
    uid TEXT PRIMARY KEY,
    tanggal TEXT NOT NULL,
    spg_uid TEXT NOT NULL,
    toko_uid TEXT DEFAULT '',
    status TEXT NOT NULL,
    jam_masuk TEXT DEFAULT '',
    jam_pulang TEXT DEFAULT '',
    catatan TEXT DEFAULT '',
    ip TEXT DEFAULT '', perangkat TEXT DEFAULT '',
    diubah TEXT NOT NULL,
    UNIQUE (spg_uid, tanggal));
-- v1.2: stok awal per toko per produk (dalam botol) — hanya master
CREATE TABLE IF NOT EXISTS stok_awal (
    toko_uid TEXT NOT NULL, produk_uid TEXT NOT NULL,
    qty_botol REAL DEFAULT 0,
    tanggal TEXT NOT NULL,
    diubah TEXT NOT NULL,
    PRIMARY KEY (toko_uid, produk_uid));
-- v1.2: stok masuk, diinput SPG
CREATE TABLE IF NOT EXISTS stok_masuk (
    uid TEXT PRIMARY KEY,
    waktu TEXT NOT NULL,
    tanggal TEXT NOT NULL,
    spg_uid TEXT NOT NULL, toko_uid TEXT NOT NULL, produk_uid TEXT NOT NULL,
    satuan TEXT NOT NULL,
    qty REAL NOT NULL,
    isi_dus INTEGER DEFAULT 1,
    botol_setara REAL DEFAULT 0,
    catatan TEXT DEFAULT '',
    ip TEXT DEFAULT '', perangkat TEXT DEFAULT '',
    dihapus INTEGER DEFAULT 0, diubah TEXT NOT NULL);
CREATE INDEX IF NOT EXISTS ix_jual_tgl  ON penjualan(tanggal);
CREATE INDEX IF NOT EXISTS ix_jual_spg  ON penjualan(spg_uid);
CREATE INDEX IF NOT EXISTS ix_jual_toko ON penjualan(toko_uid);
CREATE INDEX IF NOT EXISTS ix_log_waktu ON log(waktu);
CREATE INDEX IF NOT EXISTS ix_sesi_user ON sesi(pengguna_uid);
CREATE INDEX IF NOT EXISTS ix_absen_tgl ON absensi(tanggal);
CREATE INDEX IF NOT EXISTS ix_stokm_toko ON stok_masuk(toko_uid, produk_uid);
CREATE INDEX IF NOT EXISTS ix_stokm_tgl ON stok_masuk(tanggal);
"""

LOCK = threading.RLock()
@contextmanager
def db():
    """Koneksi SQLite: commit bila sukses, rollback bila error, dan SELALU ditutup (tidak bocor)."""
    conn = sqlite3.connect(DB_PATH, timeout=20)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys=ON")
    try:
        yield conn
        conn.commit()
    except BaseException:
        conn.rollback()
        raise
    finally:
        conn.close()
def rows(cur): return [dict(r) for r in cur.fetchall()]
def one(cur):  r = cur.fetchone(); return dict(r) if r else None

def migrasi(conn):
    """Aman dijalankan berulang: membuat tabel baru & menambah kolom sales pada database lama."""
    conn.executescript(SCHEMA)
    for tabel, kolom in (("toko", "sales"), ("pengguna", "sales")):
        ada = {r[1] for r in conn.execute(f"PRAGMA table_info({tabel})")}
        if kolom not in ada:
            conn.execute(f"ALTER TABLE {tabel} ADD COLUMN {kolom} TEXT DEFAULT ''")

class ApiError(Exception):
    def __init__(self, status, message, extra=None):
        super().__init__(message)
        self.status, self.message, self.extra = status, message, extra or {}

# =====================================================================
# PASSWORD & TOTP
# =====================================================================
SCRYPT = dict(n=2**15, r=8, p=1, dklen=32, maxmem=64*1024*1024)
PW_UMUM = {"password","12345678","123456789","qwerty123","admin123","spg12345",
           "password1","rahasia123","indonesia","11223344","abcd1234"}

def hash_pw(password, salt=None):
    salt = salt or secrets.token_hex(16)
    h = hashlib.scrypt(password.encode(), salt=bytes.fromhex(salt), **SCRYPT)
    return h.hex(), salt

def cek_pw(password, pw_hash, salt):
    try: h, _ = hash_pw(password, salt)
    except ValueError: return False
    return hmac.compare_digest(h, pw_hash)

def cek_kekuatan_pw(pw, username="", nama=""):
    if len(pw) < 10: raise ApiError(400, "Password minimal 10 karakter.")
    if len(pw) > 128: raise ApiError(400, "Password terlalu panjang.")
    if not re.search(r"[A-Za-z]", pw) or not re.search(r"\d", pw):
        raise ApiError(400, "Password harus berisi huruf dan angka.")
    low = pw.lower()
    if low in PW_UMUM: raise ApiError(400, "Password terlalu umum.")
    if username and username.lower() in low: raise ApiError(400, "Password tidak boleh memuat username.")
    for bagian in (nama or "").lower().split():
        if len(bagian) >= 4 and bagian in low: raise ApiError(400, "Password tidak boleh memuat nama Anda.")
    return True

def password_acak(n=12):
    huruf = "abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ"
    angka = "23456789"
    pool = huruf + angka
    while True:
        pw = "".join(secrets.choice(pool) for _ in range(n))
        if re.search(r"[A-Za-z]", pw) and re.search(r"\d", pw): return pw

def totp_secret(): return base64.b32encode(secrets.token_bytes(20)).decode().rstrip("=")

def totp_cek(secret, kode, window=1):
    kode = re.sub(r"\D", "", kode or "")
    if len(kode) != 6 or not secret: return False
    key = base64.b32decode(secret + "=" * (-len(secret) % 8))
    counter = int(time.time()) // 30
    for delta in range(-window, window+1):
        msg = struct.pack(">Q", counter+delta)
        h = hmac.new(key, msg, hashlib.sha1).digest()
        off = h[-1] & 0x0F
        val = (struct.unpack(">I", h[off:off+4])[0] & 0x7FFFFFFF) % 1_000_000
        if hmac.compare_digest(f"{val:06d}", kode): return True
    return False

# =====================================================================
# SETTING, LOG, SESI
# =====================================================================
def get_set(conn, key, default=None):
    r = conn.execute("SELECT value FROM setting WHERE key=?", (key,)).fetchone()
    return r[0] if r else default

def set_set(conn, key, value):
    conn.execute("INSERT OR REPLACE INTO setting VALUES (?,?)", (key, str(value)))

def catat(conn, user, aksi, detail="", ip="", perangkat=""):
    conn.execute("INSERT INTO log VALUES (?,?,?,?,?,?,?,?,?)",
        (new_uid(), now_iso(), (user or {}).get("uid",""), (user or {}).get("username",""),
         (user or {}).get("role",""), aksi, detail, ip, (perangkat or "")[:200]))

def buat_sesi(conn, user, ip, perangkat):
    token = secrets.token_urlsafe(32)
    sid   = hashlib.sha256(token.encode()).hexdigest()
    csrf  = secrets.token_urlsafe(24)
    jam   = 8 if user["role"] == "master" else 12
    conn.execute("INSERT INTO sesi VALUES (?,?,?,?,?,?,?,?)",
        (sid, user["uid"], csrf, now_iso(), now_iso(),
         (now()+timedelta(hours=jam)).isoformat(timespec="seconds"), ip, (perangkat or "")[:200]))
    conn.execute("DELETE FROM sesi WHERE kedaluwarsa < ?", (now_iso(),))
    # maksimal 5 sesi aktif per akun (yang terlama otomatis keluar)
    conn.execute("""DELETE FROM sesi WHERE pengguna_uid=? AND id NOT IN
                    (SELECT id FROM sesi WHERE pengguna_uid=? ORDER BY terakhir DESC LIMIT 5)""",
                 (user["uid"], user["uid"]))
    return token, csrf

def ambil_sesi(conn, token):
    if not token: return None
    sid = hashlib.sha256(token.encode()).hexdigest()
    s = one(conn.execute(
        """SELECT s.*, p.username, p.nama, p.role, p.wilayah, p.aktif, p.harus_ganti, p.totp_aktif
           FROM sesi s JOIN pengguna p ON p.uid=s.pengguna_uid WHERE s.id=?""", (sid,)))
    if not s: return None
    if s["kedaluwarsa"] < now_iso() or not s["aktif"]:
        conn.execute("DELETE FROM sesi WHERE id=?", (sid,)); return None
    # idle timeout per role
    idle = IDLE_TIMEOUT.get(s["role"], 30)
    if datetime.fromisoformat(s["terakhir"]) < now() - timedelta(minutes=idle):
        conn.execute("DELETE FROM sesi WHERE id=?", (sid,)); return None
    conn.execute("UPDATE sesi SET terakhir=? WHERE id=?", (now_iso(), sid))
    s["uid"] = s["pengguna_uid"]
    return s

# =====================================================================
# RATE LIMIT
# =====================================================================
_hits = {}
_hits_lock = threading.Lock()

def rate_limit(ip, bucket, batas, detik):
    kunci = (ip, bucket)
    sekarang = time.time()
    with _hits_lock:
        arr = [t for t in _hits.get(kunci, []) if sekarang-t < detik]
        if len(arr) >= batas:
            arr.append(sekarang); _hits[kunci] = arr
            sisa = int(detik-(sekarang-arr[0]))
            raise ApiError(429, f"Terlalu banyak percobaan. Coba lagi dalam {max(sisa,1)} detik.")
        arr.append(sekarang); _hits[kunci] = arr
        if len(_hits) > 5000:
            for k in [k for k,v in _hits.items() if not v or sekarang-v[-1]>3600]: _hits.pop(k,None)

# =====================================================================
# HELPER
# =====================================================================
def bersih(v): return " ".join(str(v or "").split())
def upper(v):  return bersih(v).upper()
def angka(v, nama="Angka"):
    if v is None or v == "": return 0.0
    if isinstance(v, bool) or isinstance(v, (list, dict)):
        raise ApiError(400, f"{nama} tidak valid.")
    if isinstance(v, (int,float)):
        x = float(v)
    else:
        s = str(v).strip().replace(" ","").replace("Rp","")
        if re.fullmatch(r"-?\d{1,3}([.,]\d{3})+", s): s = re.sub(r"[.,]","",s)
        elif "," in s and "." in s: s = s.replace(".","").replace(",",".")
        else: s = s.replace(",",".")
        try: x = float(s)
        except ValueError: raise ApiError(400, f"{nama} tidak valid: {str(v)[:30]}")
    # tolak NaN / Infinity / angka tak masuk akal (NaN merusak JSON & tampilan)
    if not math.isfinite(x) or abs(x) > 1e12:
        raise ApiError(400, f"{nama} tidak valid.")
    return x

def tanggal(v, nama="Tanggal"):
    if not v: return None
    s = str(v).strip()
    for f in ("%Y-%m-%d","%d/%m/%Y","%d-%m-%Y"):
        try: return datetime.strptime(s,f).date().isoformat()
        except ValueError: pass
    raise ApiError(400, f"{nama} tidak valid: {v}")

def q1(q, k, d=""): return (q.get(k) or [d])[0].strip()
def slug_user(v):
    v = unicodedata.normalize("NFKD",bersih(v)).encode("ascii","ignore").decode().lower()
    return re.sub(r"[^a-z0-9._-]","",v.replace(" ",".")[:32])

def _list_str(v, maks=5000):
    """Daftar uid dari klien: harus list berisi string (cegah tipe aneh -> error 500)."""
    if v is None: return []
    if not isinstance(v, list): raise ApiError(400, "Format daftar tidak valid.")
    return [x for x in v if isinstance(x, str)][:maks]

def init_db():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    try: os.chmod(DATA_DIR, 0o700)
    except OSError: pass
    with db() as conn:
        migrasi(conn)
        if not conn.execute("SELECT 1 FROM pengguna WHERE role='master'").fetchone():
            pw = os.environ.get("SPG_ADMIN_PASSWORD") or password_acak(14)
            h, salt = hash_pw(pw)
            conn.execute("""INSERT INTO pengguna (uid,username,nama,role,wilayah,pw_hash,pw_salt,
                harus_ganti,dibuat,diubah) VALUES (?,?,?,?,?,?,?,1,?,?)""",
                (new_uid(),"master","Master","master","",h,salt,now_iso(),now_iso()))
            (DATA_DIR/"PASSWORD_AWAL.txt").write_text(
                f"Username : master\nPassword : {pw}\n\nSegera login dan ganti password.\n", encoding="utf-8")
            print("="*64); print("  AKUN MASTER DIBUAT")
            print(f"  username : master"); print(f"  password : {pw}"); print("="*64)
        if not get_set(conn, "nama_perusahaan"):
            set_set(conn, "nama_perusahaan", os.environ.get("SPG_NAMA","Penjualan SPG"))

def backup_harian():
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    target = BACKUP_DIR / f"spg_{today_str()}.db"
    if DB_PATH.exists() and not target.exists():
        src, dst = sqlite3.connect(DB_PATH), sqlite3.connect(target)
        src.backup(dst); dst.close(); src.close()
    for f in sorted(BACKUP_DIR.glob("spg_*.db"))[:-30]: f.unlink(missing_ok=True)

# =====================================================================
# LOGIN / AKUN
# =====================================================================
ROLE_VALID = ("master","kepala_depo","spg")

def _gagal_login(conn, u, alasan, ip, perangkat):
    """Catat percobaan gagal, kunci akun 15 menit setelah 5 kali. Mengembalikan ApiError bila terkunci."""
    gagal = u["gagal"]+1
    kunci = (now()+timedelta(minutes=15)).isoformat(timespec="seconds") if gagal>=5 else ""
    conn.execute("UPDATE pengguna SET gagal=?,kunci_sampai=? WHERE uid=?",
        (0 if kunci else gagal, kunci, u["uid"]))
    catat(conn, u, "LOGIN_GAGAL", f"{alasan} (ke-{gagal})", ip, perangkat)
    conn.commit()
    return ApiError(429,"Gagal 5 kali. Akun dikunci 15 menit.") if kunci else None

def login(body, ip, perangkat):
    rate_limit(ip, "login", 10, 300)
    username = bersih(body.get("username")).lower()
    password = str(body.get("password") or "")
    kode     = bersih(body.get("kode"))
    if not username or not password: raise ApiError(400, "Username dan password wajib diisi.")
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT * FROM pengguna WHERE username=? COLLATE NOCASE",(username,)))
        gagal_umum = ApiError(401, "Username atau password salah.")
        if not u:
            hash_pw(password, "00"*16)          # samakan waktu respons agar username tak bisa ditebak
            catat(conn, None, "LOGIN_GAGAL", f"username tidak ada: {username[:40]}", ip, perangkat)
            conn.commit(); raise gagal_umum
        if not u["aktif"]:
            catat(conn, u, "LOGIN_GAGAL", "akun nonaktif", ip, perangkat); conn.commit()
            raise ApiError(403, "Akun dinonaktifkan. Hubungi master.")
        if u["kunci_sampai"] and u["kunci_sampai"] > now_iso():
            sisa = int((datetime.fromisoformat(u["kunci_sampai"])-now()).total_seconds()/60)+1
            raise ApiError(429, f"Akun terkunci. Coba lagi {sisa} menit lagi.")
        if not cek_pw(password, u["pw_hash"], u["pw_salt"]):
            raise _gagal_login(conn, u, "password salah", ip, perangkat) or gagal_umum
        if u["totp_aktif"]:
            if not kode: raise ApiError(401,"Masukkan kode 6 angka dari Authenticator.",{"butuh_kode":True})
            if not totp_cek(u["totp"], kode):
                raise _gagal_login(conn, u, "kode 2FA salah", ip, perangkat) or ApiError(401,"Kode 2FA salah.",{"butuh_kode":True})
        token, csrf = buat_sesi(conn, u, ip, perangkat)
        conn.execute("UPDATE pengguna SET gagal=0,kunci_sampai='',terakhir_login=? WHERE uid=?",(now_iso(),u["uid"]))
        catat(conn, u, "LOGIN", "berhasil masuk", ip, perangkat)
    idle = IDLE_TIMEOUT.get(u["role"], 30)
    return token, {"uid":u["uid"],"username":u["username"],"nama":u["nama"],"role":u["role"],
                   "wilayah":u["wilayah"],"harus_ganti":bool(u["harus_ganti"]),"csrf":csrf,
                   "totp_aktif":bool(u["totp_aktif"]),"idle_menit":idle}

def logout(user, token, ip):
    with LOCK, db() as conn:
        if token: conn.execute("DELETE FROM sesi WHERE id=?",(hashlib.sha256(token.encode()).hexdigest(),))
        catat(conn, user, "LOGOUT","",ip)
    return {"ok":True}

def ganti_password(user, body, ip):
    lama, baru = str(body.get("lama") or ""), str(body.get("baru") or "")
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT * FROM pengguna WHERE uid=?",(user["uid"],)))
        if not cek_pw(lama, u["pw_hash"], u["pw_salt"]):
            rate_limit(ip,"gantipw",10,600); raise ApiError(400,"Password lama salah.")
        if lama == baru: raise ApiError(400,"Password baru harus berbeda.")
        cek_kekuatan_pw(baru, u["username"], u["nama"])
        h, salt = hash_pw(baru)
        conn.execute("UPDATE pengguna SET pw_hash=?,pw_salt=?,harus_ganti=0,diubah=? WHERE uid=?",
            (h,salt,now_iso(),u["uid"]))
        conn.execute("DELETE FROM sesi WHERE pengguna_uid=? AND id!=?",
            (u["uid"],hashlib.sha256((body.get("_token") or "").encode()).hexdigest()))
        catat(conn, user,"GANTI_PASSWORD","password diganti sendiri",ip)
        try: (DATA_DIR/"PASSWORD_AWAL.txt").unlink(missing_ok=True)   # hapus file password awal
        except OSError: pass
    return {"ok":True}

def totp_siapkan(user):
    secret = totp_secret()
    with LOCK, db() as conn:
        conn.execute("UPDATE pengguna SET totp=?,totp_aktif=0 WHERE uid=?",(secret,user["uid"]))
        nama = get_set(conn,"nama_perusahaan",APP_NAME)
    uri = f"otpauth://totp/{nama}:{user['username']}?secret={secret}&issuer={nama}&digits=6&period=30"
    return {"secret":secret,"uri":uri}

def totp_aktifkan(user, body, ip):
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT totp FROM pengguna WHERE uid=?",(user["uid"],)))
        if not u["totp"] or not totp_cek(u["totp"],body.get("kode")):
            raise ApiError(400,"Kode salah.")
        conn.execute("UPDATE pengguna SET totp_aktif=1,diubah=? WHERE uid=?",(now_iso(),user["uid"]))
        catat(conn, user,"2FA_AKTIF","verifikasi 2 langkah diaktifkan",ip)
    return {"ok":True}

def totp_matikan(user, body, ip):
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT * FROM pengguna WHERE uid=?",(user["uid"],)))
        if not cek_pw(str(body.get("password") or ""),u["pw_hash"],u["pw_salt"]):
            rate_limit(ip,"2fa",10,600); raise ApiError(400,"Password salah.")
        conn.execute("UPDATE pengguna SET totp='',totp_aktif=0,diubah=? WHERE uid=?",(now_iso(),user["uid"]))
        catat(conn, user,"2FA_MATI","verifikasi 2 langkah dimatikan",ip)
    return {"ok":True}

def sesi_saya(user):
    with db() as conn:
        return rows(conn.execute(
            "SELECT dibuat,terakhir,kedaluwarsa,ip,perangkat FROM sesi WHERE pengguna_uid=? ORDER BY terakhir DESC",
            (user["uid"],)))

# =====================================================================
# PERMINTAAN (kepala_depo → master)
# =====================================================================
def permintaan_kirim(user, body, ip):
    tipe = bersih(body.get("tipe"))
    data = body.get("data") or {}
    if tipe not in ("tambah_toko","tambah_produk","tambah_spg"):
        raise ApiError(400,"Tipe permintaan tidak valid.")
    with LOCK, db() as conn:
        uid = new_uid()
        conn.execute("INSERT INTO permintaan VALUES (?,?,?,?,?,?,?,?)",
            (uid, now_iso(), user["uid"], tipe, json.dumps(data,ensure_ascii=False),
             "pending","",""))
        catat(conn, user,"KIRIM_PERMINTAAN",f"{tipe} dari {user['username']}",ip)
    return {"ok":True,"uid":uid}

def permintaan_list(user):
    with db() as conn:
        if user["role"] == "master":
            return rows(conn.execute(
                """SELECT r.*,p.nama AS peminta_nama,p.username AS peminta_user,p.wilayah AS peminta_wilayah
                   FROM permintaan r JOIN pengguna p ON p.uid=r.peminta_uid
                   ORDER BY r.waktu DESC LIMIT 200"""))
        return rows(conn.execute(
            "SELECT * FROM permintaan WHERE peminta_uid=? ORDER BY waktu DESC LIMIT 50",(user["uid"],)))

def permintaan_proses(user, uid, body, ip):
    status = body.get("status")
    if status not in ("approved","rejected"): raise ApiError(400,"Status tidak valid.")
    with LOCK, db() as conn:
        r = one(conn.execute("SELECT * FROM permintaan WHERE uid=?",(uid,)))
        if not r: raise ApiError(404,"Permintaan tidak ditemukan.")
        if r["status"] != "pending": raise ApiError(400,"Permintaan sudah diproses.")
        conn.execute("UPDATE permintaan SET status=?,catatan_master=?,diproses_waktu=? WHERE uid=?",
            (status, bersih(body.get("catatan","")), now_iso(), uid))
        catat(conn, user,"PROSES_PERMINTAAN",f"{r['tipe']} → {status}",ip)
    return {"ok":True}

# =====================================================================
# MASTER: PENGGUNA
# =====================================================================
def user_list():
    with db() as conn:
        data = rows(conn.execute(
            """SELECT p.uid,p.username,p.nama,p.role,p.wilayah,p.sales,p.aktif,p.telepon,p.catatan,
                      p.harus_ganti,p.totp_aktif,p.terakhir_login,p.kunci_sampai,p.dibuat,
                      (SELECT COUNT(*) FROM spg_toko st WHERE st.spg_uid=p.uid) AS jumlah_toko,
                      (SELECT COUNT(*) FROM penjualan j WHERE j.spg_uid=p.uid AND j.dihapus=0) AS jumlah_entri
               FROM pengguna p ORDER BY p.role DESC,p.nama"""))
        toko = {}
        for r in conn.execute(
                """SELECT st.spg_uid,t.uid,t.nama,t.sales FROM spg_toko st JOIN toko t ON t.uid=st.toko_uid
                   WHERE t.aktif=1 ORDER BY t.nama"""):
            toko.setdefault(r["spg_uid"],[]).append({"uid":r["uid"],"nama":r["nama"],"sales":r["sales"] or ""})
    for u in data:
        u["toko"] = toko.get(u["uid"],[])
        # sales otomatis = gabungan sales dari toko tempat SPG bertugas; bila sales SPG diisi manual, itu yang dipakai
        oto = []
        for t in u["toko"]:
            s = (t.get("sales") or "").strip()
            if s and s not in oto: oto.append(s)
        u["sales_otomatis"] = ", ".join(oto)
        u["sales_efektif"]  = (u.get("sales") or "").strip() or u["sales_otomatis"]
    return data

def user_simpan(user, body, uid=None, ip=""):
    nama  = bersih(body.get("nama"))
    role  = body.get("role") if body.get("role") in ROLE_VALID else "spg"
    if not nama: raise ApiError(400,"Nama wajib diisi.")
    username = slug_user(body.get("username") or nama)
    if len(username) < 3: raise ApiError(400,"Username minimal 3 karakter.")
    sales = upper(body.get("sales", ""))
    hasil = {}
    with LOCK, db() as conn:
        if conn.execute("SELECT 1 FROM pengguna WHERE username=? COLLATE NOCASE AND uid!=?",
                (username, uid or "")).fetchone():
            raise ApiError(409,f"Username '{username}' sudah dipakai.")
        if uid:
            u = one(conn.execute("SELECT * FROM pengguna WHERE uid=?",(uid,)))
            if not u: raise ApiError(404,"Pengguna tidak ditemukan.")
            aktif = 1 if body.get("aktif",True) else 0
            if u["role"]=="master" and (role!="master" or not aktif):
                sisa = conn.execute("SELECT COUNT(*) FROM pengguna WHERE role='master' AND aktif=1 AND uid!=?",(uid,)).fetchone()[0]
                if not sisa: raise ApiError(400,"Minimal harus ada satu master aktif.")
            conn.execute("""UPDATE pengguna SET username=?,nama=?,role=?,wilayah=?,sales=?,aktif=?,telepon=?,catatan=?,diubah=?
                            WHERE uid=?""",
                (username,nama,role,upper(body.get("wilayah","")),sales,aktif,
                 bersih(body.get("telepon")),bersih(body.get("catatan")),now_iso(),uid))
            if not aktif: conn.execute("DELETE FROM sesi WHERE pengguna_uid=?",(uid,))
            catat(conn,user,"UBAH_PENGGUNA",f"{username} ({role})",ip)
        else:
            uid = new_uid(); pw = password_acak()
            h, salt = hash_pw(pw)
            conn.execute("""INSERT INTO pengguna (uid,username,nama,role,wilayah,sales,pw_hash,pw_salt,harus_ganti,aktif,
                            telepon,catatan,dibuat,diubah) VALUES (?,?,?,?,?,?,?,?,1,1,?,?,?,?)""",
                (uid,username,nama,role,upper(body.get("wilayah","")),sales,h,salt,
                 bersih(body.get("telepon")),bersih(body.get("catatan")),now_iso(),now_iso()))
            hasil["password"] = pw
            catat(conn,user,"TAMBAH_PENGGUNA",f"{username} ({role})",ip)
        if "toko_uids" in body: _set_toko(conn, uid, body.get("toko_uids") or [])
    hasil["uid"] = uid; hasil["username"] = username
    return hasil

def _set_toko(conn, spg_uid, uids):
    uids = _list_str(uids)
    conn.execute("DELETE FROM spg_toko WHERE spg_uid=?",(spg_uid,))
    for t in uids:
        if conn.execute("SELECT 1 FROM toko WHERE uid=?",(t,)).fetchone():
            conn.execute("INSERT OR IGNORE INTO spg_toko VALUES (?,?,?)",(spg_uid,t,now_iso()))

def user_toko(user, uid, body, ip):
    with LOCK, db() as conn:
        if not conn.execute("SELECT 1 FROM pengguna WHERE uid=?",(uid,)).fetchone():
            raise ApiError(404,"Pengguna tidak ditemukan.")
        _set_toko(conn, uid, body.get("toko_uids") or [])
        n  = conn.execute("SELECT COUNT(*) FROM spg_toko WHERE spg_uid=?",(uid,)).fetchone()[0]
        nm = one(conn.execute("SELECT username FROM pengguna WHERE uid=?",(uid,)))["username"]
        catat(conn,user,"SET_TOKO_SPG",f"{nm}: {n} toko",ip)
    return {"ok":True,"jumlah":n}

def user_reset_pw(user, uid, ip):
    pw = password_acak(); h, salt = hash_pw(pw)
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT username FROM pengguna WHERE uid=?",(uid,)))
        if not u: raise ApiError(404,"Pengguna tidak ditemukan.")
        conn.execute("UPDATE pengguna SET pw_hash=?,pw_salt=?,harus_ganti=1,gagal=0,kunci_sampai='',diubah=? WHERE uid=?",
            (h,salt,now_iso(),uid))
        conn.execute("DELETE FROM sesi WHERE pengguna_uid=?",(uid,))
        catat(conn,user,"RESET_PASSWORD",f"password {u['username']} direset",ip)
    return {"password":pw,"username":u["username"]}

def user_buka_kunci(user, uid, ip):
    with LOCK, db() as conn:
        conn.execute("UPDATE pengguna SET gagal=0,kunci_sampai='' WHERE uid=?",(uid,))
        catat(conn,user,"BUKA_KUNCI",uid,ip)
    return {"ok":True}

def user_hapus(user, uid, ip):
    with LOCK, db() as conn:
        u = one(conn.execute("SELECT * FROM pengguna WHERE uid=?",(uid,)))
        if not u: raise ApiError(404,"Pengguna tidak ditemukan.")
        if u["role"]=="master" and conn.execute(
                "SELECT COUNT(*) FROM pengguna WHERE role='master' AND aktif=1 AND uid!=?",(uid,)).fetchone()[0]==0:
            raise ApiError(400,"Minimal harus ada satu master aktif.")
        n = conn.execute("SELECT COUNT(*) FROM penjualan WHERE spg_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM absensi WHERE spg_uid=?",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM stok_masuk WHERE spg_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        if n:
            conn.execute("UPDATE pengguna SET aktif=0,diubah=? WHERE uid=?",(now_iso(),uid))
            conn.execute("DELETE FROM sesi WHERE pengguna_uid=?",(uid,))
            catat(conn,user,"NONAKTIF_PENGGUNA",f"{u['username']} punya {n} entri",ip)
            return {"ok":True,"dinonaktifkan":True,"entri":n}
        conn.execute("DELETE FROM spg_toko WHERE spg_uid=?",(uid,))
        conn.execute("DELETE FROM sesi WHERE pengguna_uid=?",(uid,))
        conn.execute("DELETE FROM pengguna WHERE uid=?",(uid,))
        catat(conn,user,"HAPUS_PENGGUNA",u["username"],ip)
    return {"ok":True}

# =====================================================================
# TOKO & PRODUK
# =====================================================================
def toko_list(q=None, wilayah_paksa=None, spg_uid=None):
    q = q or {}
    where, args = [], []
    if wilayah_paksa: where.append("t.wilayah=?"); args.append(wilayah_paksa)
    if spg_uid: where.append("t.uid IN (SELECT toko_uid FROM spg_toko WHERE spg_uid=?)"); args.append(spg_uid)
    if q1(q,"aktif","1") == "1": where.append("t.aktif=1")
    if q1(q,"wilayah"): where.append("t.wilayah=?"); args.append(q1(q,"wilayah"))
    if q1(q,"q"):
        where.append("(t.nama LIKE ? OR t.wilayah LIKE ? OR t.sales LIKE ?)"); args += [f"%{q1(q,'q')}%"]*3
    w = (" WHERE "+" AND ".join(where)) if where else ""
    with db() as conn:
        return rows(conn.execute(
            f"""SELECT t.*,(SELECT COUNT(*) FROM spg_toko st WHERE st.toko_uid=t.uid) AS jumlah_spg,
                       (SELECT COUNT(*) FROM penjualan j WHERE j.toko_uid=t.uid AND j.dihapus=0) AS jumlah_entri,
                       (SELECT group_concat(p.nama,', ') FROM spg_toko st JOIN pengguna p ON p.uid=st.spg_uid
                        WHERE st.toko_uid=t.uid) AS spg
                FROM toko t {w} ORDER BY t.nama""", args))

def _set_spg_toko(conn, toko_uid, spg_uids):
    spg_uids = _list_str(spg_uids)
    conn.execute("DELETE FROM spg_toko WHERE toko_uid=?", (toko_uid,))
    for sid in spg_uids:
        if conn.execute("SELECT 1 FROM pengguna WHERE uid=? AND role='spg'", (sid,)).fetchone():
            conn.execute("INSERT OR IGNORE INTO spg_toko VALUES (?,?,?)", (sid, toko_uid, now_iso()))

def toko_simpan(user, body, uid=None, ip=""):
    nama = upper(body.get("nama"))
    if not nama: raise ApiError(400,"Nama toko wajib diisi.")
    data = (nama,upper(body.get("wilayah")),bersih(body.get("alamat")),upper(body.get("sales")),
            bersih(body.get("catatan")),1 if body.get("aktif",True) else 0,now_iso())
    with LOCK, db() as conn:
        if conn.execute("SELECT 1 FROM toko WHERE nama=? COLLATE NOCASE AND uid!=?",(nama,uid or "")).fetchone():
            raise ApiError(409,f"Toko '{nama}' sudah ada.")
        if uid:
            conn.execute("UPDATE toko SET nama=?,wilayah=?,alamat=?,sales=?,catatan=?,aktif=?,diubah=? WHERE uid=?",(*data,uid))
            catat(conn,user,"UBAH_TOKO",nama,ip)
        else:
            uid = new_uid()
            conn.execute("INSERT INTO toko (uid,nama,wilayah,alamat,sales,catatan,aktif,diubah,dibuat) VALUES (?,?,?,?,?,?,?,?,?)",
                (uid,*data,now_iso()))
            catat(conn,user,"TAMBAH_TOKO",nama,ip)
        if "spg_uids" in body:
            _set_spg_toko(conn, uid, body.get("spg_uids") or [])
            catat(conn,user,"SET_SPG_TOKO",f"{nama}: {len(body.get('spg_uids') or [])} SPG",ip)
    return {"uid":uid,"nama":nama}

def toko_hapus(user, uid, ip):
    with LOCK, db() as conn:
        t = one(conn.execute("SELECT * FROM toko WHERE uid=?",(uid,)))
        if not t: raise ApiError(404,"Toko tidak ditemukan.")
        n = conn.execute("SELECT COUNT(*) FROM penjualan WHERE toko_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM stok_masuk WHERE toko_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM stok_awal WHERE toko_uid=?",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM absensi WHERE toko_uid=?",(uid,)).fetchone()[0]
        if n:
            conn.execute("UPDATE toko SET aktif=0,diubah=? WHERE uid=?",(now_iso(),uid))
            catat(conn,user,"NONAKTIF_TOKO",f"{t['nama']} ({n} entri)",ip)
            return {"ok":True,"dinonaktifkan":True,"entri":n}
        conn.execute("DELETE FROM spg_toko WHERE toko_uid=?",(uid,))
        conn.execute("DELETE FROM toko WHERE uid=?",(uid,))
        catat(conn,user,"HAPUS_TOKO",t["nama"],ip)
    return {"ok":True}

def produk_list(aktif_saja=True):
    with db() as conn:
        return rows(conn.execute(
            f"""SELECT p.*,(SELECT COUNT(*) FROM penjualan j WHERE j.produk_uid=p.uid AND j.dihapus=0) AS jumlah_entri
                FROM produk p {'WHERE p.aktif=1' if aktif_saja else ''} ORDER BY p.urut,p.nama"""))

def produk_simpan(user, body, uid=None, ip=""):
    kode, nama = upper(body.get("kode")), bersih(body.get("nama"))
    if not kode or not nama: raise ApiError(400,"Kode dan nama produk wajib diisi.")
    hb, hd = angka(body.get("harga_botol"),"Harga botol"), angka(body.get("harga_dus"),"Harga dus")
    isi = int(angka(body.get("isi_dus"),"Isi per dus") or 12)
    if isi < 1: raise ApiError(400,"Isi per dus minimal 1.")
    if not hd and hb: hd = hb*isi
    with LOCK, db() as conn:
        if conn.execute("SELECT 1 FROM produk WHERE kode=? COLLATE NOCASE AND uid!=?",(kode,uid or "")).fetchone():
            raise ApiError(409,f"Kode produk '{kode}' sudah ada.")
        vals = (kode,nama,hb,hd,isi,1 if body.get("aktif",True) else 0,int(angka(body.get("urut"))),now_iso())
        if uid:
            conn.execute("""UPDATE produk SET kode=?,nama=?,harga_botol=?,harga_dus=?,isi_dus=?,aktif=?,urut=?,diubah=?
                            WHERE uid=?""",(*vals,uid))
            catat(conn,user,"UBAH_PRODUK",f"{kode} {nama}",ip)
        else:
            uid = new_uid()
            conn.execute("""INSERT INTO produk (uid,kode,nama,harga_botol,harga_dus,isi_dus,aktif,urut,diubah,dibuat)
                            VALUES (?,?,?,?,?,?,?,?,?,?)""",(uid,*vals,now_iso()))
            catat(conn,user,"TAMBAH_PRODUK",f"{kode} {nama}",ip)
    return {"uid":uid}

def produk_hapus(user, uid, ip):
    with LOCK, db() as conn:
        p = one(conn.execute("SELECT * FROM produk WHERE uid=?",(uid,)))
        if not p: raise ApiError(404,"Produk tidak ditemukan.")
        n = conn.execute("SELECT COUNT(*) FROM penjualan WHERE produk_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM stok_masuk WHERE produk_uid=? AND dihapus=0",(uid,)).fetchone()[0]
        n += conn.execute("SELECT COUNT(*) FROM stok_awal WHERE produk_uid=?",(uid,)).fetchone()[0]
        if n:
            conn.execute("UPDATE produk SET aktif=0,diubah=? WHERE uid=?",(now_iso(),uid))
            catat(conn,user,"NONAKTIF_PRODUK",f"{p['kode']} ({n} entri)",ip)
            return {"ok":True,"dinonaktifkan":True,"entri":n}
        conn.execute("DELETE FROM produk WHERE uid=?",(uid,))
        catat(conn,user,"HAPUS_PRODUK",p["kode"],ip)
    return {"ok":True}

# =====================================================================
# ABSENSI HARIAN SPG
# =====================================================================
ABSEN_FROM = """FROM absensi a JOIN pengguna p ON p.uid=a.spg_uid LEFT JOIN toko t ON t.uid=a.toko_uid"""
ABSEN_SQL = """SELECT a.uid,a.tanggal,a.spg_uid,a.toko_uid,a.status,a.jam_masuk,a.jam_pulang,a.catatan,
       p.nama AS spg,p.wilayah AS wilayah_spg,COALESCE(t.nama,'') AS toko,COALESCE(t.sales,'') AS sales """ + ABSEN_FROM
STATUS_ABSEN = ("HADIR", "IZIN", "SAKIT")

def absen_hari(conn, spg_uid):
    return one(conn.execute(ABSEN_SQL+" WHERE a.spg_uid=? AND a.tanggal=?",(spg_uid,today_str())))

def absen_masuk(user, body, ip, perangkat):
    status  = upper(body.get("status") or "HADIR")
    catatan = bersih(body.get("catatan"))[:200]
    if status not in STATUS_ABSEN: raise ApiError(400,"Status absen tidak valid.")
    if status != "HADIR" and not catatan: raise ApiError(400,"Isi alasan untuk izin / sakit.")
    with LOCK, db() as conn:
        toko_uid = ""
        if status == "HADIR":
            toko = one(conn.execute("SELECT * FROM toko WHERE uid=? AND aktif=1",(body.get("toko_uid"),)))
            if not toko: raise ApiError(400,"Pilih toko tempat Anda bertugas hari ini.")
            if not conn.execute("SELECT 1 FROM spg_toko WHERE spg_uid=? AND toko_uid=?",
                    (user["uid"],toko["uid"])).fetchone():
                raise ApiError(403,"Toko ini bukan toko Anda.")
            toko_uid = toko["uid"]
        lama = absen_hari(conn, user["uid"])
        if lama and lama["status"] == "HADIR":
            raise ApiError(400,"Anda sudah absen masuk hari ini.")
        jam_masuk = now_iso() if status == "HADIR" else ""
        if lama:
            conn.execute("""UPDATE absensi SET toko_uid=?,status=?,jam_masuk=?,jam_pulang='',catatan=?,ip=?,perangkat=?,diubah=?
                            WHERE uid=?""",
                (toko_uid,status,jam_masuk,catatan,ip,(perangkat or "")[:200],now_iso(),lama["uid"]))
        else:
            conn.execute("""INSERT INTO absensi (uid,tanggal,spg_uid,toko_uid,status,jam_masuk,jam_pulang,catatan,ip,perangkat,diubah)
                            VALUES (?,?,?,?,?,?,'',?,?,?,?)""",
                (new_uid(),today_str(),user["uid"],toko_uid,status,jam_masuk,catatan,ip,(perangkat or "")[:200],now_iso()))
        catat(conn,user,"ABSEN_MASUK" if status=="HADIR" else "ABSEN_"+status,catatan or "",ip,perangkat)
        return absen_hari(conn, user["uid"])

def absen_pulang(user, ip, perangkat):
    with LOCK, db() as conn:
        a = absen_hari(conn, user["uid"])
        if not a or a["status"] != "HADIR": raise ApiError(400,"Anda belum absen masuk hari ini.")
        if a["jam_pulang"]: raise ApiError(400,"Anda sudah absen pulang hari ini.")
        conn.execute("UPDATE absensi SET jam_pulang=?,diubah=? WHERE uid=?",(now_iso(),now_iso(),a["uid"]))
        catat(conn,user,"ABSEN_PULANG","",ip,perangkat)
        return absen_hari(conn, user["uid"])

def absen_list(user, q):
    wp = wilayah_depo(user)
    where, args = [], []
    dari, sampai = q1(q,"dari"), q1(q,"sampai")
    if dari:   where.append("a.tanggal >= ?"); args.append(dari)
    if sampai: where.append("a.tanggal <= ?"); args.append(sampai)
    if user["role"] == "spg":
        where.append("a.spg_uid = ?"); args.append(user["uid"])
    elif q1(q,"spg_uid"):
        where.append("a.spg_uid = ?"); args.append(q1(q,"spg_uid"))
    if q1(q,"status") in STATUS_ABSEN:
        where.append("a.status = ?"); args.append(q1(q,"status"))
    if wp:
        where.append("(p.wilayah = ? OR t.wilayah = ?)"); args += [wp, wp]
    w = (" WHERE "+" AND ".join(where)) if where else ""
    with db() as conn:
        data = rows(conn.execute(ABSEN_SQL+w+" ORDER BY a.tanggal DESC,a.jam_masuk DESC,p.nama LIMIT 2000",args))
        rekap = rows(conn.execute(
            f"""SELECT p.nama AS spg,
                       SUM(CASE WHEN a.status='HADIR' THEN 1 ELSE 0 END) AS hadir,
                       SUM(CASE WHEN a.status='IZIN'  THEN 1 ELSE 0 END) AS izin,
                       SUM(CASE WHEN a.status='SAKIT' THEN 1 ELSE 0 END) AS sakit,
                       COUNT(*) AS hari
                {ABSEN_FROM}{w} GROUP BY p.uid ORDER BY p.nama""",args))
        belum = None
        if user["role"] != "spg" and dari and dari == sampai:
            cond, a2 = "", [dari]
            if wp:
                cond = (" AND (p.wilayah=? OR EXISTS (SELECT 1 FROM spg_toko s3 JOIN toko t3 ON t3.uid=s3.toko_uid "
                        "WHERE s3.spg_uid=p.uid AND t3.wilayah=?))")
                a2 += [wp, wp]
            belum = rows(conn.execute(
                f"""SELECT p.nama,p.wilayah,
                           (SELECT group_concat(t2.nama,', ') FROM spg_toko s2 JOIN toko t2 ON t2.uid=s2.toko_uid
                            WHERE s2.spg_uid=p.uid AND t2.aktif=1) AS toko
                    FROM pengguna p WHERE p.role='spg' AND p.aktif=1
                      AND NOT EXISTS (SELECT 1 FROM absensi a WHERE a.spg_uid=p.uid AND a.tanggal=?){cond}
                    ORDER BY p.nama""",a2))
    ringkas = {"jumlah":len(data),
               "hadir":sum(1 for r in data if r["status"]=="HADIR"),
               "izin": sum(1 for r in data if r["status"]=="IZIN"),
               "sakit":sum(1 for r in data if r["status"]=="SAKIT")}
    return {"rows":data,"ringkas":ringkas,"rekap":rekap,"belum":belum}

def absen_hapus(user, uid, ip):
    with LOCK, db() as conn:
        a = one(conn.execute(ABSEN_SQL+" WHERE a.uid=?",(uid,)))
        if not a: raise ApiError(404,"Data absen tidak ditemukan.")
        conn.execute("DELETE FROM absensi WHERE uid=?",(uid,))
        catat(conn,user,"HAPUS_ABSEN",f"{a['spg']} {a['tanggal']} {a['status']}",ip)
    return {"ok":True}

# =====================================================================
# STOK (stok awal: master saja | stok masuk: diinput SPG)
# =====================================================================
_STOK_SQL = """
SELECT m.uid,m.waktu,m.tanggal,m.satuan,m.qty,m.isi_dus,m.botol_setara,m.catatan,
       m.spg_uid,m.toko_uid,m.produk_uid,
       p.nama AS spg,t.nama AS toko,t.wilayah,pr.kode,pr.nama AS produk
FROM stok_masuk m
JOIN pengguna p ON p.uid=m.spg_uid
JOIN toko t ON t.uid=m.toko_uid
JOIN produk pr ON pr.uid=m.produk_uid
"""

def stok_masuk_simpan(user, body, ip, perangkat):
    satuan = upper(body.get("satuan") or "BOTOL")
    if satuan not in SATUAN: raise ApiError(400,"Satuan tidak valid.")
    qty = angka(body.get("qty"),"Jumlah")
    if qty <= 0:     raise ApiError(400,"Jumlah harus lebih dari 0.")
    if qty > 100000: raise ApiError(400,"Jumlah terlalu besar.")
    catatan = bersih(body.get("catatan"))[:200]
    with LOCK, db() as conn:
        toko   = one(conn.execute("SELECT * FROM toko WHERE uid=? AND aktif=1",(body.get("toko_uid"),)))
        produk = one(conn.execute("SELECT * FROM produk WHERE uid=? AND aktif=1",(body.get("produk_uid"),)))
        if not toko:   raise ApiError(400,"Toko belum dipilih atau tidak aktif.")
        if not produk: raise ApiError(400,"Produk belum dipilih atau tidak aktif.")
        if user["role"] == "spg" and not conn.execute(
                "SELECT 1 FROM spg_toko WHERE spg_uid=? AND toko_uid=?",(user["uid"],toko["uid"])).fetchone():
            raise ApiError(403,"Toko ini bukan toko Anda.")
        isi   = int(produk["isi_dus"] or 1)
        botol = qty*(isi if satuan=="DUS" else 1)
        uid, w = new_uid(), now()
        conn.execute("""INSERT INTO stok_masuk (uid,waktu,tanggal,spg_uid,toko_uid,produk_uid,satuan,qty,isi_dus,
                        botol_setara,catatan,ip,perangkat,dihapus,diubah)
                        VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,0,?)""",
            (uid,w.isoformat(timespec="seconds"),w.date().isoformat(),user["uid"],toko["uid"],produk["uid"],
             satuan,qty,isi,botol,catatan,ip,(perangkat or "")[:200],now_iso()))
        catat(conn,user,"INPUT_STOK_MASUK",f"{toko['nama']}|{produk['kode']}|{qty:g} {satuan}",ip,perangkat)
        return one(conn.execute(_STOK_SQL+" WHERE m.uid=?",(uid,)))

def stok_masuk_hapus(user, uid, ip):
    with LOCK, db() as conn:
        e = one(conn.execute(_STOK_SQL+" WHERE m.uid=? AND m.dihapus=0",(uid,)))
        _cek_boleh_ubah(user, e)
        conn.execute("UPDATE stok_masuk SET dihapus=1,diubah=? WHERE uid=?",(now_iso(),uid))
        catat(conn,user,"HAPUS_STOK_MASUK",f"{e['toko']}|{e['kode']}|{e['qty']:g} {e['satuan']}",ip)
    return {"ok":True}

def stok_masuk_list(user, q):
    where, args = ["m.dihapus=0"], []
    for key,kolom in (("dari","m.tanggal >= ?"),("sampai","m.tanggal <= ?"),
                      ("toko_uid","m.toko_uid = ?"),("produk_uid","m.produk_uid = ?")):
        v = q1(q,key)
        if v: where.append(kolom); args.append(v)
    if user["role"] == "spg":
        where.append("m.spg_uid = ?"); args.append(user["uid"])
    elif q1(q,"spg_uid"):
        where.append("m.spg_uid = ?"); args.append(q1(q,"spg_uid"))
    w = " WHERE "+" AND ".join(where)
    with db() as conn:
        data = rows(conn.execute(_STOK_SQL+w+" ORDER BY m.waktu DESC LIMIT 1000",args))
    return {"rows":data,"ringkas":{"jumlah":len(data),"botol":sum(r["botol_setara"] for r in data)}}

def stok_list(q):
    """Posisi stok per toko x produk. Hanya dipanggil master."""
    tuid = q1(q,"toko_uid")
    w    = " AND t.uid=?" if tuid else ""
    args = (tuid,) if tuid else ()
    with db() as conn:
        data = rows(conn.execute(
            f"""SELECT t.uid AS toko_uid,t.nama AS toko,t.wilayah,t.sales,
                       pr.uid AS produk_uid,pr.kode,pr.nama AS produk,pr.isi_dus,
                       sa.qty_botol AS awal,sa.tanggal AS tgl_awal,
                       COALESCE((SELECT SUM(m.botol_setara) FROM stok_masuk m
                                 WHERE m.toko_uid=t.uid AND m.produk_uid=pr.uid AND m.dihapus=0
                                   AND m.tanggal >= COALESCE(sa.tanggal,'')),0) AS masuk,
                       COALESCE((SELECT SUM(j.botol_setara) FROM penjualan j
                                 WHERE j.toko_uid=t.uid AND j.produk_uid=pr.uid AND j.dihapus=0 AND j.jenis='JUAL'
                                   AND j.tanggal >= COALESCE(sa.tanggal,'')),0) AS terjual,
                       COALESCE((SELECT SUM(j.botol_setara) FROM penjualan j
                                 WHERE j.toko_uid=t.uid AND j.produk_uid=pr.uid AND j.dihapus=0 AND j.jenis='SAMPLE'
                                   AND j.tanggal >= COALESCE(sa.tanggal,'')),0) AS sample
                FROM toko t CROSS JOIN produk pr
                LEFT JOIN stok_awal sa ON sa.toko_uid=t.uid AND sa.produk_uid=pr.uid
                WHERE t.aktif=1 AND pr.aktif=1{w}
                ORDER BY t.nama,pr.urut,pr.nama""",args))
    for r in data:
        r["diatur"] = r["awal"] is not None
        r["awal"]   = r["awal"] or 0
        r["sisa"]   = r["awal"] + r["masuk"] - r["terjual"] - r["sample"]
    return {"rows":data}

def stok_awal_simpan(user, body, ip):
    tgl = tanggal(body.get("tanggal")) or today_str()
    items = body.get("items") or []
    if not isinstance(items, list): raise ApiError(400,"Format daftar tidak valid.")
    with LOCK, db() as conn:
        toko = one(conn.execute("SELECT * FROM toko WHERE uid=?",(body.get("toko_uid"),)))
        if not toko: raise ApiError(404,"Toko tidak ditemukan.")
        n = 0
        for it in items:
            if not isinstance(it, dict): continue
            if it.get("qty") in (None, ""): continue      # kosong = tidak diubah
            produk = one(conn.execute("SELECT * FROM produk WHERE uid=?",(it.get("produk_uid"),)))
            if not produk: continue
            qty = angka(it.get("qty"),"Stok awal")
            if qty < 0: raise ApiError(400,"Stok awal tidak boleh minus.")
            if qty > 10_000_000: raise ApiError(400,"Stok awal terlalu besar.")
            satuan = upper(it.get("satuan") or "BOTOL")
            if satuan not in SATUAN: raise ApiError(400,"Satuan tidak valid.")
            botol = qty*(int(produk["isi_dus"] or 1) if satuan=="DUS" else 1)
            conn.execute("INSERT OR REPLACE INTO stok_awal VALUES (?,?,?,?,?)",
                (toko["uid"],produk["uid"],botol,tgl,now_iso()))
            n += 1
        catat(conn,user,"SET_STOK_AWAL",f"{toko['nama']}: {n} produk (per {tgl})",ip)
    return {"ok":True,"jumlah":n}

# =====================================================================
# PENJUALAN
# =====================================================================
def spg_awal(user):
    with db() as conn:
        toko = rows(conn.execute(
            """SELECT t.uid,t.nama,t.wilayah FROM spg_toko st JOIN toko t ON t.uid=st.toko_uid
               WHERE st.spg_uid=? AND t.aktif=1 ORDER BY t.nama""",(user["uid"],)))
        produk = rows(conn.execute(
            "SELECT uid,kode,nama,harga_botol,harga_dus,isi_dus FROM produk WHERE aktif=1 ORDER BY urut,nama"))
        hari_ini = _entri_list(conn,{"spg_uid":[user["uid"]],"dari":[today_str()],"sampai":[today_str()]})
        terakhir = one(conn.execute(
            "SELECT toko_uid FROM penjualan WHERE spg_uid=? AND dihapus=0 ORDER BY waktu DESC LIMIT 1",(user["uid"],)))
        absen = absen_hari(conn, user["uid"])
    return {"toko":toko,"produk":produk,"hari_ini":hari_ini,
            "toko_terakhir":(terakhir or {}).get("toko_uid"),"edit_menit":EDIT_WINDOW_MIN,
            "nama":user["nama"],"jam_server":now_iso(),"absen":absen}

def _hitung(produk, satuan, qty, harga, jenis):
    isi = int(produk["isi_dus"] or 1)
    botol = qty*(isi if satuan=="DUS" else 1)
    total = 0 if jenis=="SAMPLE" else round(qty*harga,2)
    return isi, botol, total

def entri_simpan(user, body, ip, perangkat, uid=None):
    jenis  = upper(body.get("jenis") or "JUAL")
    satuan = upper(body.get("satuan") or "BOTOL")
    if jenis not in JENIS:  raise ApiError(400,"Jenis tidak valid.")
    if satuan not in SATUAN: raise ApiError(400,"Satuan tidak valid.")
    qty = angka(body.get("qty"),"Jumlah")
    if qty <= 0:    raise ApiError(400,"Jumlah harus lebih dari 0.")
    if qty > 100000: raise ApiError(400,"Jumlah terlalu besar.")
    harga  = angka(body.get("harga"),"Harga")
    if harga < 0: raise ApiError(400,"Harga tidak boleh minus.")
    catatan = bersih(body.get("catatan"))[:200]
    with LOCK, db() as conn:
        toko   = one(conn.execute("SELECT * FROM toko WHERE uid=? AND aktif=1",(body.get("toko_uid"),)))
        produk = one(conn.execute("SELECT * FROM produk WHERE uid=? AND aktif=1",(body.get("produk_uid"),)))
        if not toko:   raise ApiError(400,"Toko belum dipilih atau tidak aktif.")
        if not produk: raise ApiError(400,"Produk belum dipilih atau tidak aktif.")
        if user["role"] == "spg":
            if not conn.execute("SELECT 1 FROM spg_toko WHERE spg_uid=? AND toko_uid=?",
                    (user["uid"],toko["uid"])).fetchone():
                raise ApiError(403,"Toko ini bukan toko Anda.")
        if jenis=="SAMPLE": harga = 0.0
        elif not harga: harga = produk["harga_dus"] if satuan=="DUS" else produk["harga_botol"]
        isi, botol, total = _hitung(produk,satuan,qty,harga,jenis)
        if uid:
            lama = one(conn.execute(_ENTRI_SQL+" WHERE j.uid=?",(uid,)))
            _cek_boleh_ubah(user, lama)
            conn.execute("""UPDATE penjualan SET toko_uid=?,produk_uid=?,jenis=?,satuan=?,qty=?,isi_dus=?,harga=?,
                            total=?,botol_setara=?,catatan=?,diubah=? WHERE uid=?""",
                (toko["uid"],produk["uid"],jenis,satuan,qty,isi,harga,total,botol,catatan,now_iso(),uid))
            catat(conn,user,"UBAH_PENJUALAN",f"{toko['nama']}|{produk['kode']}|{qty:g} {satuan}|{jenis}",ip,perangkat)
        else:
            uid = new_uid(); w = now()
            conn.execute("""INSERT INTO penjualan (uid,waktu,tanggal,spg_uid,toko_uid,produk_uid,jenis,satuan,
                            qty,isi_dus,harga,total,botol_setara,catatan,ip,perangkat,dihapus,diubah)
                            VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?)""",
                (uid,w.isoformat(timespec="seconds"),w.date().isoformat(),user["uid"],toko["uid"],
                 produk["uid"],jenis,satuan,qty,isi,harga,total,botol,catatan,ip,(perangkat or "")[:200],now_iso()))
            catat(conn,user,"INPUT_PENJUALAN",f"{toko['nama']}|{produk['kode']}|{qty:g} {satuan}|{jenis}",ip,perangkat)
        hasil = one(conn.execute(_ENTRI_SQL+" WHERE j.uid=?",(uid,)))
    return hasil

def _cek_boleh_ubah(user, entri):
    if not entri or entri.get("dihapus"): raise ApiError(404,"Data tidak ditemukan.")
    if user["role"] == "master": return
    if entri["spg_uid"] != user["uid"]: raise ApiError(403,"Ini bukan data Anda.")
    batas = datetime.fromisoformat(entri["waktu"])+timedelta(minutes=EDIT_WINDOW_MIN)
    if now() > batas: raise ApiError(403,f"Data sudah lewat {EDIT_WINDOW_MIN} menit, tidak bisa diubah.")

def entri_hapus(user, uid, ip):
    with LOCK, db() as conn:
        e = one(conn.execute(_ENTRI_SQL+" WHERE j.uid=?",(uid,)))
        _cek_boleh_ubah(user, e)
        conn.execute("UPDATE penjualan SET dihapus=1,diubah=? WHERE uid=?",(now_iso(),uid))
        catat(conn,user,"HAPUS_PENJUALAN",f"{e['toko']}|{e['kode']}|{e['qty']:g} {e['satuan']}",ip)
    return {"ok":True}

_ENTRI_SQL = """
SELECT j.uid,j.waktu,j.tanggal,j.jenis,j.satuan,j.qty,j.isi_dus,j.harga,j.total,j.botol_setara,
       j.catatan,j.spg_uid,j.toko_uid,j.produk_uid,j.dihapus,
       p.nama AS spg,p.username AS spg_user,t.nama AS toko,t.wilayah,t.sales AS sales,
       pr.kode,pr.nama AS produk
FROM penjualan j
JOIN pengguna p ON p.uid=j.spg_uid
JOIN toko t ON t.uid=j.toko_uid
JOIN produk pr ON pr.uid=j.produk_uid
"""

def _filter(q, wilayah_paksa=None):
    where, args = ["j.dihapus=0"], []
    for key,kolom in (("dari","j.tanggal >= ?"),("sampai","j.tanggal <= ?"),("spg_uid","j.spg_uid = ?"),
                      ("toko_uid","j.toko_uid = ?"),("produk_uid","j.produk_uid = ?"),
                      ("jenis","j.jenis = ?"),("satuan","j.satuan = ?"),("wilayah","t.wilayah = ?")):
        v = q1(q,key)
        if key=="wilayah" and wilayah_paksa: continue
        if v: where.append(kolom); args.append(v)
    if wilayah_paksa:
        where.append("t.wilayah = ?"); args.append(wilayah_paksa)
    if q1(q,"q"):
        where.append("(t.nama LIKE ? OR pr.nama LIKE ? OR pr.kode LIKE ? OR p.nama LIKE ? OR j.catatan LIKE ? OR t.sales LIKE ?)")
        args += [f"%{q1(q,'q')}%"]*6
    return " WHERE "+" AND ".join(where), args

def _entri_list(conn, q, limit=2000, wilayah_paksa=None):
    w, args = _filter(q, wilayah_paksa)
    data = rows(conn.execute(_ENTRI_SQL+w+" ORDER BY j.waktu DESC LIMIT ?",(*args,limit)))
    r = one(conn.execute(
        f"""SELECT COUNT(*) AS jumlah,COALESCE(SUM(j.total),0) AS total,
                   COALESCE(SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara ELSE 0 END),0) AS botol_jual,
                   COALESCE(SUM(CASE WHEN j.jenis='SAMPLE' THEN j.botol_setara ELSE 0 END),0) AS botol_sample,
                   COUNT(DISTINCT j.toko_uid) AS toko,COUNT(DISTINCT j.spg_uid) AS spg
            FROM penjualan j JOIN pengguna p ON p.uid=j.spg_uid JOIN toko t ON t.uid=j.toko_uid
            JOIN produk pr ON pr.uid=j.produk_uid {w}""",args))
    return {"rows":data,"ringkas":r}

def entri_list(user, q):
    wp = wilayah_depo(user)
    if user["role"]=="spg": q = {**q,"spg_uid":[user["uid"]]}
    with db() as conn:
        return _entri_list(conn, q, wilayah_paksa=wp)

def laporan(q, wilayah_paksa=None):
    w, args = _filter(q, wilayah_paksa)
    with db() as conn:
        hasil = _entri_list(conn, q, limit=int(q1(q,"limit","1000")), wilayah_paksa=wilayah_paksa)
        grup = {}
        for nama,kolom in (("spg","p.nama"),("toko","t.nama"),("sales","COALESCE(NULLIF(t.sales,''),'(tanpa sales)')"),
                           ("produk","pr.kode || ' - ' || pr.nama"),
                           ("tanggal","j.tanggal"),("wilayah","COALESCE(NULLIF(t.wilayah,''),'(tanpa wilayah)')")):
            grup[nama] = rows(conn.execute(
                f"""SELECT {kolom} AS label,COUNT(*) AS entri,
                           SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara ELSE 0 END) AS botol_jual,
                           SUM(CASE WHEN j.jenis='SAMPLE' THEN j.botol_setara ELSE 0 END) AS botol_sample,
                           SUM(j.total) AS total
                    FROM penjualan j JOIN pengguna p ON p.uid=j.spg_uid JOIN toko t ON t.uid=j.toko_uid
                    JOIN produk pr ON pr.uid=j.produk_uid {w}
                    GROUP BY label ORDER BY total DESC,botol_jual DESC""",args))
    hasil["grup"] = grup
    return hasil

def dashboard(wilayah_paksa=None):
    hari = today_str(); bulan = hari[:8]+"01"
    wh = " AND t.wilayah=?" if wilayah_paksa else ""
    wa = (wilayah_paksa,) if wilayah_paksa else ()
    with db() as conn:
        f = lambda sql,*a: one(conn.execute(sql,a))
        hari_ini = f(f"""SELECT COUNT(*) AS entri,COALESCE(SUM(j.total),0) AS total,
                                COALESCE(SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara END),0) AS botol,
                                COALESCE(SUM(CASE WHEN j.jenis='SAMPLE' THEN j.botol_setara END),0) AS sample,
                                COUNT(DISTINCT j.spg_uid) AS spg,COUNT(DISTINCT j.toko_uid) AS toko
                         FROM penjualan j JOIN toko t ON t.uid=j.toko_uid
                         WHERE j.dihapus=0 AND j.tanggal=?{wh}""",hari,*wa)
        bulan_ini = f(f"""SELECT COUNT(*) AS entri,COALESCE(SUM(j.total),0) AS total,
                                 COALESCE(SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara END),0) AS botol,
                                 COALESCE(SUM(CASE WHEN j.jenis='SAMPLE' THEN j.botol_setara END),0) AS sample
                          FROM penjualan j JOIN toko t ON t.uid=j.toko_uid
                          WHERE j.dihapus=0 AND j.tanggal>=?{wh}""",bulan,*wa)
        terbaru = rows(conn.execute(
            _ENTRI_SQL+f" WHERE j.dihapus=0{wh} ORDER BY j.waktu DESC LIMIT 25",wa))
        per_spg = rows(conn.execute(
            f"""SELECT p.nama AS spg,p.uid,
                       COALESCE(SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara END),0) AS botol,
                       COALESCE(SUM(CASE WHEN j.jenis='SAMPLE' THEN j.botol_setara END),0) AS sample,
                       COALESCE(SUM(j.total),0) AS total,COUNT(j.uid) AS entri,MAX(j.waktu) AS terakhir
               FROM pengguna p LEFT JOIN penjualan j ON j.spg_uid=p.uid AND j.dihapus=0 AND j.tanggal=?
               LEFT JOIN toko t ON t.uid=j.toko_uid
               WHERE p.role='spg' AND p.aktif=1 {('AND t.wilayah=?' if wilayah_paksa else '')}
               GROUP BY p.uid ORDER BY total DESC,p.nama""",
            (hari, wilayah_paksa) if wilayah_paksa else (hari,)))
        belum = rows(conn.execute(
            f"""SELECT t.nama,t.wilayah FROM toko t WHERE t.aktif=1{wh}
               AND NOT EXISTS (SELECT 1 FROM penjualan j WHERE j.toko_uid=t.uid AND j.dihapus=0 AND j.tanggal=?)
               ORDER BY t.nama LIMIT 50""",(*wa,hari)))
        mulai = (now().date()-timedelta(days=13)).isoformat()
        tren = rows(conn.execute(
            f"""SELECT j.tanggal AS tanggal,COALESCE(SUM(j.total),0) AS total,
                       COALESCE(SUM(CASE WHEN j.jenis='JUAL' THEN j.botol_setara END),0) AS botol
                FROM penjualan j JOIN toko t ON t.uid=j.toko_uid
                WHERE j.dihapus=0 AND j.tanggal>=?{wh} GROUP BY j.tanggal ORDER BY j.tanggal""",(mulai,*wa)))
        cond, ar = "", [hari]
        if wilayah_paksa:
            cond = " AND (p.wilayah=? OR t.wilayah=?)"; ar += [wilayah_paksa, wilayah_paksa]
        ab = one(conn.execute(
            f"""SELECT COALESCE(SUM(CASE WHEN a.status='HADIR' THEN 1 ELSE 0 END),0) AS hadir,
                       COALESCE(SUM(CASE WHEN a.status IN ('IZIN','SAKIT') THEN 1 ELSE 0 END),0) AS izin
                {ABSEN_FROM} WHERE a.tanggal=?{cond}""",ar))
        if wilayah_paksa:
            total_spg = conn.execute(
                """SELECT COUNT(*) FROM pengguna p WHERE p.role='spg' AND p.aktif=1 AND (p.wilayah=? OR EXISTS
                   (SELECT 1 FROM spg_toko s3 JOIN toko t3 ON t3.uid=s3.toko_uid WHERE s3.spg_uid=p.uid AND t3.wilayah=?))""",
                (wilayah_paksa,wilayah_paksa)).fetchone()[0]
        else:
            total_spg = conn.execute("SELECT COUNT(*) FROM pengguna WHERE role='spg' AND aktif=1").fetchone()[0]
        absen = {"hadir":ab["hadir"],"izin":ab["izin"],"total":total_spg}
    return {"hari_ini":hari_ini,"bulan_ini":bulan_ini,"terbaru":terbaru,"per_spg":per_spg,
            "toko_belum_isi":belum,"tren":tren,"absen":absen,"jam":now_iso()}

def log_list(q):
    where, args = [], []
    if q1(q,"dari"): where.append("waktu >= ?"); args.append(q1(q,"dari"))
    if q1(q,"sampai"): where.append("waktu < ?"); args.append((date.fromisoformat(q1(q,"sampai"))+timedelta(days=1)).isoformat())
    if q1(q,"aksi"): where.append("aksi = ?"); args.append(q1(q,"aksi"))
    if q1(q,"q"): where.append("(detail LIKE ? OR username LIKE ? OR ip LIKE ?)"); args += [f"%{q1(q,'q')}%"]*3
    w = (" WHERE "+" AND ".join(where)) if where else ""
    with db() as conn:
        return {"rows":rows(conn.execute(f"SELECT * FROM log {w} ORDER BY waktu DESC LIMIT 1000",args)),
                "aksi":[r[0] for r in conn.execute("SELECT DISTINCT aksi FROM log ORDER BY aksi")]}

# =====================================================================
# BACKUP & PEMULIHAN (master)
# =====================================================================
def backup_bytes():
    tmp = DATA_DIR / f"tmp_{new_uid()}.db"
    try:
        src, dst = sqlite3.connect(DB_PATH), sqlite3.connect(tmp)
        src.backup(dst); dst.close(); src.close()
        return tmp.read_bytes()
    finally:
        tmp.unlink(missing_ok=True)

def restore_db(user, data, password, ip):
    if len(data) < 1024 or not data.startswith(b"SQLite format 3\x00"):
        raise ApiError(400, "File bukan database SPG yang valid.")
    with LOCK:
        with db() as conn:
            u = one(conn.execute("SELECT * FROM pengguna WHERE uid=?", (user["uid"],)))
        if not cek_pw(password, u["pw_hash"], u["pw_salt"]):
            rate_limit(ip, "restore", 5, 600); raise ApiError(400, "Password salah.")
        tmp = DATA_DIR / f"restore_{new_uid()}.db"
        tmp.write_bytes(data)
        try:
            t = sqlite3.connect(tmp)
            try:
                ok = t.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
                tabel = {r[0] for r in t.execute("SELECT name FROM sqlite_master WHERE type='table'")}
                if not ok or not {"pengguna","toko","produk","penjualan"} <= tabel:
                    raise ApiError(400, "Isi file bukan database aplikasi ini atau rusak.")
                if not t.execute("SELECT 1 FROM pengguna WHERE role='master' AND aktif=1").fetchone():
                    raise ApiError(400, "Backup ini tidak punya akun master aktif, pemulihan dibatalkan.")
                BACKUP_DIR.mkdir(parents=True, exist_ok=True)
                aman = BACKUP_DIR / f"sebelum_restore_{now():%Y%m%d_%H%M%S}.db"
                a, b = sqlite3.connect(DB_PATH), sqlite3.connect(aman)
                a.backup(b); b.close(); a.close()
                cur = sqlite3.connect(DB_PATH); t.backup(cur); cur.close()
            finally:
                t.close()
        finally:
            tmp.unlink(missing_ok=True)
        try:
            # backup lama (sebelum v1.2) belum punya tabel absensi/stok & kolom sales -> lengkapi otomatis
            with db() as conn:
                migrasi(conn)
                catat(conn, user, "RESTORE", "database dipulihkan dari file", ip)
        except Exception as e:
            print("migrasi setelah restore gagal:", e)
    return {"ok": True}

def backup_daftar():
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    return [{"nama": f.name, "ukuran": f.stat().st_size, "waktu": datetime.fromtimestamp(f.stat().st_mtime, TZ).isoformat(timespec="seconds")}
            for f in sorted(BACKUP_DIR.glob("*.db"), reverse=True)][:40]

# =====================================================================
# EXPORT
# =====================================================================
try:
    from openpyxl import Workbook
    from openpyxl.styles import Alignment, Font, PatternFill
    from openpyxl.utils import get_column_letter
    ADA_EXCEL = True
except ImportError:
    ADA_EXCEL = False

KOLOM = ["TANGGAL","JAM","SPG","TOKO","WILAYAH","KODE","PRODUK","JENIS","SATUAN","QTY",
         "ISI/DUS","BOTOL SETARA","HARGA","TOTAL","CATATAN","SALES"]

def _baris_export(r):
    return [r["tanggal"],r["waktu"][11:16],r["spg"],r["toko"],r["wilayah"],r["kode"],r["produk"],
            r["jenis"],r["satuan"],r["qty"],r["isi_dus"],r["botol_setara"],r["harga"],r["total"],r["catatan"],
            r.get("sales") or ""]

def export_penjualan(user, q, ip):
    wp = wilayah_depo(user)
    if user["role"]=="spg": q = {**q,"spg_uid":[user["uid"]]}
    with db() as conn:
        data = _entri_list(conn, q, limit=100000, wilayah_paksa=wp)
        catat(conn,user,"EXPORT",f"{len(data['rows'])} baris",ip)
    rows_ = list(reversed(data["rows"]))
    nama  = f"PENJUALAN_SPG_{now():%Y%m%d_%H%M}"
    if not ADA_EXCEL:
        buf = io.StringIO()
        buf.write(";".join(KOLOM)+"\n")
        for r in rows_: buf.write(";".join(str(x).replace(";",",") for x in _baris_export(r))+"\n")
        return buf.getvalue().encode("utf-8-sig"), nama+".csv", "text/csv; charset=utf-8"
    wb = Workbook(); ws = wb.active; ws.title = "PENJUALAN"
    ws.append(KOLOM)
    for c in range(1,len(KOLOM)+1):
        cell = ws.cell(1,c)
        cell.font = Font(bold=True,color="FFFFFF")
        cell.fill = PatternFill("solid",fgColor="1F3D73")
        cell.alignment = Alignment(horizontal="center")
    for r in rows_: ws.append(_baris_export(r))
    n = ws.max_row
    for c in (10,12,13,14):
        for rr in range(2,n+1): ws.cell(rr,c).number_format = "#,##0"
    if n >= 2:
        ws.append([]); ws.cell(n+2,9,"TOTAL")
        for c,f in ((10,f"=SUM(J2:J{n})"),(12,f"=SUM(L2:L{n})"),(14,f"=SUM(N2:N{n})")):
            ws.cell(n+2,c,f); ws.cell(n+2,c).font=Font(bold=True); ws.cell(n+2,c).number_format="#,##0"
    for i,w in enumerate([11,7,18,28,14,10,24,9,8,8,8,12,12,14,24,16],1):
        ws.column_dimensions[get_column_letter(i)].width = w
    ws.freeze_panes = "A2"; ws.auto_filter.ref = f"A1:P{max(n,1)}"; wb.calculation.fullCalcOnLoad=True
    bio = io.BytesIO(); wb.save(bio)
    return bio.getvalue(), nama+".xlsx","application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"

# =====================================================================
# HTTP ROUTING
# =====================================================================
def wilayah_depo(user):
    if user["role"] != "kepala_depo": return None
    return user.get("wilayah") or "__TANPA_WILAYAH__"

MASTER = ("master",)
DEPO   = ("master","kepala_depo")
SEMUA  = ("master","kepala_depo","spg")
VIEW   = ("master","kepala_depo")
INPUT  = ("master","spg")
ROUTES = []

def route(method, pattern, roles):
    def deco(fn):
        ROUTES.append((method, re.compile(pattern), roles, fn))
        return fn
    return deco

class Handler(BaseHTTPRequestHandler):
    server_version = "spg"; sys_version = ""; protocol_version = "HTTP/1.1"
    timeout = 30            # putus koneksi yang menggantung (cegah slowloris)
    def log_message(self,*a): pass

    @property
    def ip(self):
        if TRUST_PROXY:
            # ambil alamat dari sisi KANAN (ditambahkan proxy tepercaya); sisi kiri bisa dipalsukan klien
            bagian = [x.strip() for x in self.headers.get("X-Forwarded-For","").split(",") if x.strip()]
            if bagian:
                cand = bagian[-min(PROXY_HOPS, len(bagian))]
                try: return str(ipaddress.ip_address(cand))
                except ValueError: pass
        return self.client_address[0]

    @property
    def perangkat(self): return self.headers.get("User-Agent","")[:200]

    @property
    def https(self):
        if TRUST_PROXY: return self.headers.get("X-Forwarded-Proto","").lower()=="https"
        return False

    def kirim(self, status, body, ctype, extra=None, nonce=""):
        if isinstance(body,str): body = body.encode()
        self.send_response(status)
        self.send_header("Content-Type",ctype)
        self.send_header("Content-Length",str(len(body)))
        self.send_header("Cache-Control","no-store")
        self.send_header("X-Content-Type-Options","nosniff")
        self.send_header("X-Frame-Options","DENY")
        self.send_header("Referrer-Policy","same-origin")
        self.send_header("Cross-Origin-Opener-Policy","same-origin")
        self.send_header("Cross-Origin-Resource-Policy","same-origin")
        self.send_header("X-Permitted-Cross-Domain-Policies","none")
        self.send_header("Permissions-Policy","geolocation=(),microphone=(),camera=(),interest-cohort=()")
        self.send_header("Content-Security-Policy",
            "default-src 'self'; base-uri 'none'; form-action 'none'; frame-ancestors 'none'; "
            "object-src 'none'; img-src 'self' data:; connect-src 'self'; "
            f"style-src 'self' 'nonce-{nonce}'; script-src 'self' 'nonce-{nonce}'")
        if self.https: self.send_header("Strict-Transport-Security","max-age=31536000; includeSubDomains")
        for k,v in (extra or {}).items(): self.send_header(k,v)
        self.end_headers()
        if self.command != "HEAD": self.wfile.write(body)

    def json(self, obj, status=200, extra=None):
        self.kirim(status, json.dumps(obj,ensure_ascii=False,default=str), "application/json; charset=utf-8", extra)

    def file(self, data, nama, ctype):
        self.kirim(200,data,ctype,{"Content-Disposition":f'attachment; filename="{nama}"'})

    def raw(self, maks=1_000_000):
        try: n = int(self.headers.get("Content-Length") or 0)
        except ValueError: raise ApiError(400,"Permintaan tidak valid.")
        if n < 0: raise ApiError(400,"Permintaan tidak valid.")
        if n > maks: raise ApiError(413,"Data terlalu besar.")
        return self.rfile.read(n) if n else b""

    def body(self):
        b = self.raw()
        try: data = json.loads(b.decode()) if b else {}
        except (ValueError,UnicodeDecodeError,RecursionError): raise ApiError(400,"Format data tidak valid.")
        if not isinstance(data, dict): raise ApiError(400,"Format data tidak valid.")
        return data

    def token(self):
        for bagian in (self.headers.get("Cookie") or "").split(";"):
            k,_,v = bagian.strip().partition("=")
            if k == "sid": return v
        return ""

    def set_cookie(self, token, hapus=False):
        bagian = [f"sid={'' if hapus else token}","HttpOnly","SameSite=Strict","Path=/"]
        if hapus: bagian.append("Max-Age=0")
        if self.https: bagian.append("Secure")
        return {"Set-Cookie":"; ".join(bagian)}

    def do_GET(self):  self.jalan("GET")
    def do_POST(self): self.jalan("POST")
    def do_PUT(self):  self.jalan("PUT")
    def do_DELETE(self): self.jalan("DELETE")

    def jalan(self, method):
        url  = urlparse(self.path)
        path = url.path.rstrip("/") or "/"
        q    = parse_qs(url.query)
        try:
            if path == "/healthz": return self.kirim(200,"ok","text/plain")
            if REQUIRE_HTTPS and not DEV_MODE and TRUST_PROXY and not self.https:
                host = self.headers.get("Host","")
                if method=="GET" and host:
                    return self.kirim(308,b"","text/plain",{"Location":f"https://{host}{self.path}"})
                raise ApiError(400,"Koneksi harus HTTPS.")
            # perlindungan CSRF tambahan: permintaan tulis dari situs lain ditolak
            origin = self.headers.get("Origin")
            if method != "GET" and origin:
                sah = {self.headers.get("Host","").lower()}
                if TRUST_PROXY:
                    sah |= {x.strip().lower() for x in self.headers.get("X-Forwarded-Host","").split(",") if x.strip()}
                if urlparse(origin).netloc.lower() not in sah:
                    raise ApiError(403,"Asal permintaan tidak dikenali.")
            rate_limit(self.ip,"umum",600,60)
            user = None
            with db() as conn:
                sesi = ambil_sesi(conn, self.token())
            if sesi:
                user = {k:sesi[k] for k in ("uid","username","nama","role","wilayah","csrf","harus_ganti","totp_aktif")}
                user["pengguna_uid"] = sesi["pengguna_uid"]
            for m,pat,roles,fn in ROUTES:
                if m != method: continue
                cocok = pat.fullmatch(path)
                if not cocok: continue
                if roles is not None:
                    if not user: raise ApiError(401,"Sesi berakhir. Silakan masuk lagi.")
                    if user["role"] not in roles: raise ApiError(403,"Menu ini tidak tersedia untuk akun Anda.")
                    if method != "GET":
                        if not hmac.compare_digest(self.headers.get("X-CSRF-Token",""),user["csrf"]):
                            raise ApiError(403,"Permintaan ditolak (token tidak cocok). Muat ulang halaman.")
                        if user["harus_ganti"] and not path.startswith("/api/password"):
                            raise ApiError(403,"Ganti password dulu sebelum memakai aplikasi.")
                return fn(self,q,user,*cocok.groups())
            raise ApiError(404,"Halaman tidak ditemukan.")
        except ApiError as e: self.json({"error":e.message,**e.extra},e.status)
        except (ValueError,KeyError,TypeError,AttributeError,RecursionError):
            import traceback; traceback.print_exc()
            self.json({"error":"Data tidak valid."},400)
        except BrokenPipeError: pass
        except Exception as e:
            import traceback; traceback.print_exc()
            self.json({"error":"Terjadi kesalahan di server."},500)

# =====================================================================
# ROUTES
# =====================================================================
@route("GET",r"/",None)
def r_index(h,q,user):
    nonce = secrets.token_urlsafe(16)
    with db() as conn: nama = get_set(conn,"nama_perusahaan",APP_NAME)
    html = INDEX_HTML.replace("__NONCE__",nonce).replace("__APPNAME__",nama)
    h.kirim(200,html,"text/html; charset=utf-8",nonce=nonce)

@route("POST",r"/api/login",None)
def r_login(h,q,user):
    token, info = login(h.body(),h.ip,h.perangkat)
    h.json(info,extra=h.set_cookie(token))

@route("POST",r"/api/logout",SEMUA)
def r_logout(h,q,user):
    logout(user,h.token(),h.ip); h.json({"ok":True},extra=h.set_cookie("",hapus=True))

@route("GET",r"/api/me",None)
def r_me(h,q,user):
    if not user: return h.json({"login":False})
    idle = IDLE_TIMEOUT.get(user["role"],30)
    h.json({"login":True,**{k:user[k] for k in ("uid","username","nama","role","wilayah","csrf","harus_ganti","totp_aktif")},"idle_menit":idle})

@route("POST",r"/api/password",SEMUA)
def r_password(h,q,user): h.json(ganti_password(user,{**h.body(),"_token":h.token()},h.ip))

@route("POST",r"/api/2fa/siapkan",SEMUA)
def r_2fa1(h,q,user): h.json(totp_siapkan(user))

@route("POST",r"/api/2fa/aktifkan",SEMUA)
def r_2fa2(h,q,user): h.json(totp_aktifkan(user,h.body(),h.ip))

@route("POST",r"/api/2fa/matikan",SEMUA)
def r_2fa3(h,q,user): h.json(totp_matikan(user,h.body(),h.ip))

@route("GET",r"/api/sesi",SEMUA)
def r_sesi(h,q,user): h.json(sesi_saya(user))

# permintaan
@route("GET",r"/api/permintaan",("master","kepala_depo"))
def r_perm_list(h,q,user): h.json(permintaan_list(user))

@route("POST",r"/api/permintaan",("kepala_depo",))
def r_perm_kirim(h,q,user): h.json(permintaan_kirim(user,h.body(),h.ip))

@route("PUT",r"/api/permintaan/(\w+)",MASTER)
def r_perm_proses(h,q,user,uid): h.json(permintaan_proses(user,uid,h.body(),h.ip))

# spg
@route("GET",r"/api/spg/awal",("spg",))
def r_spg_awal(h,q,user): h.json(spg_awal(user))

# absensi
@route("GET",r"/api/absen",SEMUA)
def r_absen_list(h,q,user): h.json(absen_list(user,q))

@route("POST",r"/api/absen/masuk",("spg",))
def r_absen_masuk(h,q,user): h.json(absen_masuk(user,h.body(),h.ip,h.perangkat))

@route("POST",r"/api/absen/pulang",("spg",))
def r_absen_pulang(h,q,user): h.json(absen_pulang(user,h.ip,h.perangkat))

@route("DELETE",r"/api/absen/(\w+)",MASTER)
def r_absen_hapus(h,q,user,uid): h.json(absen_hapus(user,uid,h.ip))

# stok
@route("GET",r"/api/stok",MASTER)
def r_stok_list(h,q,user): h.json(stok_list(q))

@route("PUT",r"/api/stok/awal",MASTER)
def r_stok_awal(h,q,user): h.json(stok_awal_simpan(user,h.body(),h.ip))

@route("GET",r"/api/stok/masuk",INPUT)
def r_stokm_list(h,q,user): h.json(stok_masuk_list(user,q))

@route("POST",r"/api/stok/masuk",INPUT)
def r_stokm_baru(h,q,user): h.json(stok_masuk_simpan(user,h.body(),h.ip,h.perangkat))

@route("DELETE",r"/api/stok/masuk/(\w+)",INPUT)
def r_stokm_hapus(h,q,user,uid): h.json(stok_masuk_hapus(user,uid,h.ip))

@route("POST",r"/api/penjualan",INPUT)
def r_jual_baru(h,q,user): h.json(entri_simpan(user,h.body(),h.ip,h.perangkat))

@route("PUT",r"/api/penjualan/(\w+)",INPUT)
def r_jual_ubah(h,q,user,uid): h.json(entri_simpan(user,h.body(),h.ip,h.perangkat,uid))

@route("DELETE",r"/api/penjualan/(\w+)",SEMUA)
def r_jual_hapus(h,q,user,uid): h.json(entri_hapus(user,uid,h.ip))

@route("GET",r"/api/penjualan",SEMUA)
def r_jual_list(h,q,user): h.json(entri_list(user,q))

@route("GET",r"/export/backup",MASTER)
def r_backup(h,q,user):
    with db() as conn: catat(conn,user,"BACKUP_UNDUH","unduh database",h.ip)
    h.file(backup_bytes(), f"SPG_BACKUP_{now():%Y%m%d_%H%M}.db", "application/octet-stream")

@route("GET",r"/api/backup",MASTER)
def r_backup_list(h,q,user): h.json(backup_daftar())

@route("POST",r"/api/restore",MASTER)
def r_restore(h,q,user):
    from urllib.parse import unquote
    h.json(restore_db(user, h.raw(100_000_000), unquote(h.headers.get("X-Password","")), h.ip))

@route("GET",r"/export/penjualan",SEMUA)
def r_export(h,q,user):
    data,nama,ctype = export_penjualan(user,q,h.ip); h.file(data,nama,ctype)

# master & depo
@route("GET",r"/api/dashboard",SEMUA)
def r_dash(h,q,user):
    wp = wilayah_depo(user)
    h.json(dashboard(wp))

@route("GET",r"/api/laporan",VIEW)
def r_laporan(h,q,user):
    wp = wilayah_depo(user)
    h.json(laporan(q,wp))

@route("GET",r"/api/pengguna",MASTER)
def r_user_list(h,q,user): h.json(user_list())

@route("POST",r"/api/pengguna",MASTER)
def r_user_baru(h,q,user): h.json(user_simpan(user,h.body(),None,h.ip))

@route("PUT",r"/api/pengguna/(\w+)",MASTER)
def r_user_ubah(h,q,user,uid): h.json(user_simpan(user,h.body(),uid,h.ip))

@route("DELETE",r"/api/pengguna/(\w+)",MASTER)
def r_user_hapus(h,q,user,uid): h.json(user_hapus(user,uid,h.ip))

@route("PUT",r"/api/pengguna/(\w+)/toko",MASTER)
def r_user_toko(h,q,user,uid): h.json(user_toko(user,uid,h.body(),h.ip))

@route("POST",r"/api/pengguna/(\w+)/reset",MASTER)
def r_user_reset(h,q,user,uid): h.json(user_reset_pw(user,uid,h.ip))

@route("POST",r"/api/pengguna/(\w+)/buka",MASTER)
def r_user_buka(h,q,user,uid): h.json(user_buka_kunci(user,uid,h.ip))

@route("GET",r"/api/toko",SEMUA)
def r_toko_list(h,q,user):
    h.json(toko_list(q, wilayah_depo(user), user["uid"] if user["role"]=="spg" else None))

@route("POST",r"/api/toko",MASTER)
def r_toko_baru(h,q,user): h.json(toko_simpan(user,h.body(),None,h.ip))

@route("PUT",r"/api/toko/(\w+)",MASTER)
def r_toko_ubah(h,q,user,uid): h.json(toko_simpan(user,h.body(),uid,h.ip))

@route("DELETE",r"/api/toko/(\w+)",MASTER)
def r_toko_hapus(h,q,user,uid): h.json(toko_hapus(user,uid,h.ip))

@route("GET",r"/api/produk",SEMUA)
def r_produk(h,q,user): h.json(produk_list(q1(q,"semua")!="1" or user["role"]!="master"))

@route("POST",r"/api/produk",MASTER)
def r_produk_baru(h,q,user): h.json(produk_simpan(user,h.body(),None,h.ip))

@route("PUT",r"/api/produk/(\w+)",MASTER)
def r_produk_ubah(h,q,user,uid): h.json(produk_simpan(user,h.body(),uid,h.ip))

@route("DELETE",r"/api/produk/(\w+)",MASTER)
def r_produk_hapus(h,q,user,uid): h.json(produk_hapus(user,uid,h.ip))

@route("GET",r"/api/log",MASTER)
def r_log(h,q,user): h.json(log_list(q))


INDEX_HTML = r'''<!DOCTYPE html>
<html lang="id">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#0f766e">
<title>__APPNAME__</title>
<style nonce="__NONCE__">
:root{
  --ink:#0f172a;--ink2:#334155;--muted:#64748b;--line:#e6ebf2;--bg:#f4f7fb;--card:#fff;
  --brand:#0d9488;--brand2:#0f766e;--brand3:#14b8a6;--soft:#ccfbf1;--soft2:#f0fdfa;
  --ok:#15803d;--ok-s:#dcfce7;--warn:#a16207;--warn-s:#fef3c7;
  --err:#b91c1c;--err-s:#fee2e2;--ind:#4338ca;--ind-s:#e0e7ff;
  --side:#0b1324;--side2:#12203d;
  --sh1:0 1px 2px rgba(15,23,42,.04),0 6px 22px rgba(15,23,42,.06);
  --sh2:0 18px 50px rgba(15,23,42,.22);
  --sab:env(safe-area-inset-bottom,0px);--sat:env(safe-area-inset-top,0px);
}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;min-height:100%}
body{font-family:Inter,"Segoe UI",Roboto,system-ui,-apple-system,Arial,sans-serif;font-size:16px;color:var(--ink);
     background:var(--bg);letter-spacing:.003em;-webkit-font-smoothing:antialiased}
button,input,select,textarea{font:inherit;color:inherit}
input,select,textarea{border:1px solid #d5dde8;border-radius:12px;padding:12px 14px;background:#fff;width:100%;transition:border-color .15s,box-shadow .15s}
input:focus,select:focus,textarea:focus{outline:0;border-color:var(--brand);box-shadow:0 0 0 4px rgba(13,148,136,.15)}
input::placeholder,textarea::placeholder{color:#a3b0c2}
select{appearance:none;background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='16' height='16' viewBox='0 0 24 24' fill='none' stroke='%2364748b' stroke-width='2.2' stroke-linecap='round' stroke-linejoin='round'%3E%3Cpath d='M6 9l6 6 6-6'/%3E%3C/svg%3E");background-repeat:no-repeat;background-position:right 12px center;padding-right:38px}
::-webkit-scrollbar{width:10px;height:10px}::-webkit-scrollbar-thumb{background:#cbd5e1;border-radius:10px;border:2px solid transparent;background-clip:content-box}

/* ---------- tombol ---------- */
.btn{border:1px solid #d5dde8;background:#fff;border-radius:12px;padding:11px 16px;cursor:pointer;font-weight:600;display:inline-flex;
     align-items:center;justify-content:center;gap:6px;text-decoration:none;color:var(--ink2);transition:transform .12s,box-shadow .15s,background .15s,border-color .15s}
.btn:hover{border-color:#b9c4d3;box-shadow:0 2px 8px rgba(15,23,42,.08)}
.btn:active{transform:scale(.97)}
.btn.primary{background:linear-gradient(135deg,#14b8a6,#0d9488);border-color:#0d9488;color:#fff;box-shadow:0 4px 14px rgba(13,148,136,.32)}
.btn.primary:hover{box-shadow:0 6px 18px rgba(13,148,136,.45)}
.btn.ok{background:linear-gradient(135deg,#22c55e,#15803d);border-color:#15803d;color:#fff;box-shadow:0 4px 14px rgba(21,128,61,.3)}
.btn.danger{color:var(--err);border-color:#f0c4c4;background:#fff}
.btn.danger:hover{background:var(--err-s)}
.btn.block{width:100%}
.btn.sm{padding:6px 11px;font-size:13.5px;border-radius:9px}
.btn.big{padding:17px;font-size:18px;border-radius:15px}
.btn:disabled{opacity:.5;pointer-events:none}
.row .btn{flex:0 0 auto}

/* ---------- komponen umum ---------- */
.card{background:var(--card);border:1px solid #edf1f6;border-radius:20px;padding:20px;margin-bottom:16px;box-shadow:var(--sh1)}
.card.compact{margin-bottom:10px;padding:14px}
.card h2{font-size:15px;margin:0 0 14px;color:var(--ink);font-weight:700;letter-spacing:-.005em}
.card-head{display:flex;justify-content:space-between;align-items:baseline;gap:10px;margin-bottom:6px}
.card-head h2{margin:0}
label.f{display:block;font-size:12.5px;color:var(--muted);margin:0 0 6px;font-weight:600}
.muted{color:var(--muted)}
.dim{color:#94a3b8;font-weight:600;font-size:.7em}
.row{display:flex;gap:10px;flex-wrap:wrap;align-items:center}
.row>*{min-width:0}
.row>h2,.row>.flex1,.row>.spacer{flex:1}
.row>h2{margin:0}
.row>input,.row>select{flex:1 1 200px}
.row>.block{flex:1 1 100%}
.spacer{flex:1}
.badge{display:inline-block;border-radius:999px;padding:3px 11px;font-size:12px;font-weight:700;letter-spacing:.01em}
.b-jual{background:var(--soft);color:var(--brand2)}
.b-sample{background:var(--warn-s);color:var(--warn)}
.b-ok{background:var(--ok-s);color:var(--ok)}
.b-err{background:var(--err-s);color:var(--err)}
.b-depo{background:var(--ind-s);color:var(--ind)}
.note{padding:12px 14px;border-radius:12px;margin:10px 0;font-size:14px;line-height:1.55}
.note.ok{background:var(--ok-s);color:var(--ok)}
.note.warn{background:var(--warn-s);color:var(--warn)}
.note.err{background:var(--err-s);color:var(--err)}
.note.info{background:var(--soft2);color:var(--brand2);border:1px solid #b7efe8}
code{background:#eef2f7;padding:2px 7px;border-radius:7px;font-size:13.5px}

/* ---------- utilitas (pengganti style="" yang diblokir CSP) ---------- */
.hide{display:none}
.mt10{margin-top:10px}.mt6{margin:6px 0 0}.ml8{margin-left:8px}
.flex1{flex:1;min-width:0}.noflex{flex:none}.nobr{white-space:nowrap}
.rsz{resize:vertical}.fr{float:right;text-transform:none}.fs15{font-size:15px}
.max220{max-width:220px}.row-acts{display:flex;gap:6px;flex:none}
.kode-lg{font-size:18px}.kode-md{font-size:16px;letter-spacing:2px}
.ol-ak{padding-left:20px;line-height:1.8}
.gap{height:12px}.gap-s{height:8px}.kecil{font-size:13px}
.lebar{max-width:260px}

/* ---------- LOGIN ---------- */
#login{min-height:100vh;display:flex;align-items:center;justify-content:center;padding:18px;
  background:radial-gradient(900px 500px at 15% 10%,rgba(45,212,191,.35),transparent 60%),
             radial-gradient(800px 500px at 90% 90%,rgba(99,102,241,.28),transparent 60%),
             linear-gradient(160deg,#0b1324,#12304a 60%,#0f766e)}
#login .card{width:min(420px,100%);margin:0;padding:30px 26px;border:0;box-shadow:var(--sh2);border-radius:24px}
#login h1{font-size:23px;margin:14px 0 4px;letter-spacing:-.02em}
#login p.sub{margin:0 0 20px;color:var(--muted);font-size:14px}
.logo{width:38px;height:38px;border-radius:12px;display:grid;place-items:center;flex:none;
  background:linear-gradient(135deg,#2dd4bf,#0d9488);color:#fff;box-shadow:0 6px 16px rgba(13,148,136,.4)}
.logo svg{width:21px;height:21px}
.logo.lg{width:56px;height:56px;border-radius:17px}.logo.lg svg{width:30px;height:30px}

/* ---------- KERANGKA APLIKASI ---------- */
#app{display:none;min-height:100vh;flex-direction:column}
header.topbar{display:flex;align-items:center;gap:12px;padding:12px 16px;padding-top:calc(12px + var(--sat));
  background:linear-gradient(135deg,#0f766e,#0d9488);color:#fff;box-shadow:0 2px 12px rgba(15,118,110,.25);position:relative;z-index:30}
.brand{display:none;align-items:center;gap:11px;font-weight:800;font-size:17px;letter-spacing:-.02em}
.grow{flex:1}
.who{display:flex;align-items:center;gap:10px;min-width:0}
.avatar{width:38px;height:38px;border-radius:50%;display:grid;place-items:center;background:rgba(255,255,255,.22);font-weight:800;flex:none}
.who-t{min-width:0}
.who-t b{display:block;font-size:15px;line-height:1.2;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.who-t small{font-size:12px;opacity:.85}
header .btn.ghost{background:rgba(255,255,255,.14);border-color:rgba(255,255,255,.3);color:#fff;padding:8px 13px;font-size:14px;box-shadow:none}
header .btn.ghost:hover{background:rgba(255,255,255,.24)}
.shell{display:flex;flex-direction:column;flex:1;min-width:0}
.content{flex:1;min-width:0}
main{max-width:1500px;width:100%;margin:0 auto;padding:14px;padding-bottom:calc(28px + var(--sab))}
main>*{animation:naik .35s ease both}
@keyframes naik{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
@media(prefers-reduced-motion:reduce){main>*{animation:none}}

nav.tabs{display:flex;gap:6px;overflow-x:auto;padding:10px 14px 0;background:linear-gradient(135deg,#0f766e,#0d9488);
  position:sticky;top:0;z-index:25;scrollbar-width:none}
nav.tabs::-webkit-scrollbar{display:none}
nav.tabs button{background:rgba(255,255,255,.12);border:0;color:#e8fffb;padding:8px 16px;border-radius:999px;margin-bottom:10px;
  cursor:pointer;white-space:nowrap;font-weight:600;font-size:14px;transition:.15s}
nav.tabs button.active{background:#fff;color:var(--brand2);box-shadow:0 2px 8px rgba(0,0,0,.14)}
nav.tabs svg,.nav-label{display:none}

.page-head{display:none;align-items:flex-end;justify-content:space-between;gap:12px;padding:18px 14px 0;max-width:1500px;margin:0 auto}
.page-head h1{margin:0;font-size:23px;font-weight:800;letter-spacing:-.025em}
.page-head p{margin:3px 0 0;color:var(--muted);font-size:14px}
.head-date{background:#fff;border:1px solid var(--line);border-radius:999px;padding:7px 14px;font-size:13px;font-weight:600;color:var(--ink2);box-shadow:var(--sh1);white-space:nowrap}

/* tampilan master & kepala depo: sidebar gelap di layar lebar */
@media(min-width:960px){
  body.side header.topbar{background:#fff;color:var(--ink);box-shadow:0 1px 0 var(--line);position:sticky;top:0;height:68px;padding:0 24px}
  body.side .brand{display:flex}
  body.side .brand .logo{width:38px;height:38px}
  body.side .who{order:2}
  body.side .grow{order:1}
  body.side header .btn{order:3}
  body.side .avatar{background:linear-gradient(135deg,#2dd4bf,#0d9488);color:#fff}
  body.side header .btn.ghost{background:#fff;border-color:var(--line);color:var(--ink2)}
  body.side header .btn.ghost:hover{background:#f8fafc}
  body.side .shell{flex-direction:row;align-items:flex-start}
  body.side nav.tabs{flex-direction:column;flex:none;width:256px;height:calc(100vh - 68px);position:sticky;top:68px;overflow-y:auto;
    padding:18px 14px 24px;gap:3px;background:linear-gradient(180deg,var(--side),var(--side2))}
  body.side nav.tabs button{display:flex;align-items:center;gap:12px;width:100%;text-align:left;padding:11px 14px;border-radius:12px;margin:0;
    background:transparent;color:#aab6cc;font-size:14.5px;box-shadow:none}
  body.side nav.tabs button:hover{background:rgba(255,255,255,.07);color:#fff}
  body.side nav.tabs button.active{background:linear-gradient(135deg,#14b8a6,#0d9488);color:#fff;box-shadow:0 8px 20px rgba(20,184,166,.35)}
  body.side nav.tabs svg{display:block;width:19px;height:19px;flex:none}
  body.side .nav-label{display:block;color:#5d6d8a;font-size:11px;font-weight:700;letter-spacing:.12em;text-transform:uppercase;padding:16px 14px 6px}
  body.side .page-head{padding:30px 34px 0}
  body.side main{padding:20px 34px 40px}
}

/* ---------- SPG (mobile) ---------- */
.spg-wrap{max-width:540px;margin:0 auto;counter-reset:langkah}
.spg-step{background:var(--card);border:1px solid #edf1f6;border-radius:20px;padding:18px;margin-bottom:14px;box-shadow:var(--sh1)}
.spg-step h2{font-size:15px;margin:0 0 12px;color:var(--ink);font-weight:700}
.spg-step h2::before{counter-increment:langkah;content:counter(langkah);display:inline-grid;place-items:center;
  width:26px;height:26px;margin-right:8px;border-radius:50%;background:var(--brand);color:#fff;font-size:13px}
.spg-step:last-child h2::before{display:none}
.seg{display:flex;gap:8px}
.seg button{flex:1;padding:14px 10px;border:2px solid var(--line);background:#fff;border-radius:13px;font-weight:700;cursor:pointer;font-size:15px}
.seg button.aktif{border-color:var(--brand);background:var(--soft2);color:var(--brand2)}
.qty-row{display:flex;gap:10px;align-items:center;margin-top:12px}
.qty-row button{width:56px;height:56px;font-size:26px;font-weight:700;border-radius:13px;border:2px solid var(--line);background:#fff;cursor:pointer;flex:none}
.qty-row input{text-align:center;font-size:22px;font-weight:700;height:56px;border-radius:13px}
.sample-toggle{display:flex;align-items:center;gap:12px;padding:14px;border:2px solid var(--line);border-radius:13px;background:#fff;cursor:pointer;margin-top:12px;user-select:none}
.sample-toggle.aktif{border-color:var(--warn);background:var(--warn-s)}
.sample-toggle input[type=checkbox]{width:22px;height:22px;flex:none;accent-color:var(--warn)}
.total-box{display:flex;align-items:baseline;justify-content:space-between;padding:14px 0 0;flex-wrap:nowrap;gap:10px}
.total-val{font-size:28px;font-weight:800;color:var(--brand2)}
.entri{display:flex;gap:10px;align-items:flex-start;padding:12px 0;border-bottom:1px solid var(--line)}
.entri:last-child{border-bottom:0}
.entri .jam{font-variant-numeric:tabular-nums;font-weight:700;width:46px;flex:none;padding-top:2px;font-size:14px}
.entri .isi{flex:1;min-width:0}
.entri .isi b{display:block;font-size:15px;line-height:1.3}
.entri .isi small{color:var(--muted);font-size:13px}
.entri .nilai{font-weight:700;white-space:nowrap;font-size:15px;text-align:right}

/* ---------- kartu statistik ---------- */
.ring{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:14px;margin-bottom:16px}
.ring div{--acc:#14b8a6;position:relative;overflow:hidden;background:var(--card);border:1px solid #edf1f6;border-radius:18px;padding:16px 18px;box-shadow:var(--sh1)}
.ring div::after{content:"";position:absolute;right:-22px;top:-22px;width:92px;height:92px;border-radius:50%;background:var(--acc);opacity:.13}
.ring div::before{content:"";position:absolute;left:0;top:18px;bottom:18px;width:4px;border-radius:0 4px 4px 0;background:var(--acc)}
.ring div:nth-child(6n+2){--acc:#6366f1}
.ring div:nth-child(6n+3){--acc:#f59e0b}
.ring div:nth-child(6n+4){--acc:#10b981}
.ring div:nth-child(6n+5){--acc:#0ea5e9}
.ring div:nth-child(6n+6){--acc:#f43f5e}
.ring b{display:block;font-size:22px;font-weight:800;letter-spacing:-.02em;font-variant-numeric:tabular-nums;overflow-wrap:anywhere;line-height:1.25}
.ring span{font-size:12.5px;color:var(--muted);font-weight:500}
.spg-wrap .ring{grid-template-columns:repeat(2,1fr)}
.spg-wrap .ring b{font-size:18px}

/* ---------- grafik ---------- */
.grafik{width:100%;height:auto;display:block}
.grafik .bar{fill:url(#gbar)}
.grafik .bar.hari{fill:#0f766e}
.grafik .axis{fill:#94a3b8;font-size:11px;font-weight:600}
.grafik .gl{stroke:#e8edf3;stroke-dasharray:3 5}
.grafik .val{fill:#64748b;font-size:10.5px;font-weight:600}

/* ---------- tabel ---------- */
.tbl{overflow:auto;border:1px solid #edf1f6;border-radius:18px;background:#fff;max-height:70vh;box-shadow:var(--sh1);margin-bottom:16px}
.tbl.pendek{max-height:330px}
.card>.tbl{box-shadow:none}
table{border-collapse:separate;border-spacing:0;width:100%;font-size:14px}
th,td{padding:12px 14px;border-bottom:1px solid #f0f3f8;white-space:nowrap;text-align:left}
th{background:#f8fafc;color:#64748b;position:sticky;top:0;z-index:1;font-size:11.5px;text-transform:uppercase;letter-spacing:.07em;font-weight:700;border-bottom:1px solid var(--line)}
tbody tr{transition:background .12s}
tbody tr:hover{background:#f6fffd}
tbody tr:last-child td{border-bottom:0}
td.n{text-align:right;font-variant-numeric:tabular-nums}
tr.grup-toko td{background:#ecfdf9;font-weight:700;color:var(--brand2)}
td.minus{color:var(--err);font-weight:700}
.tbl input.qa{min-width:90px}
.empty{padding:36px;text-align:center;color:var(--muted);font-size:15px}
.empty::before{content:"📭";display:block;font-size:34px;margin-bottom:6px}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(340px,1fr));gap:16px}
.form{display:grid;grid-template-columns:repeat(auto-fit,minmax(160px,1fr));gap:14px}
.form .full{grid-column:1/-1}
.chips{display:flex;flex-wrap:wrap;gap:6px}
.chip{background:var(--soft2);border:1px solid #b7efe8;color:var(--brand2);border-radius:999px;padding:4px 12px;font-size:12.5px;font-weight:600}
.checklist{max-height:260px;overflow:auto;border:1px solid var(--line);border-radius:12px;padding:6px}
.checklist label{display:flex;gap:10px;align-items:center;padding:9px 8px;border-radius:8px;cursor:pointer}
.checklist label:hover{background:#f6fffd}
.checklist input{width:20px;height:20px;flex:none;accent-color:var(--brand)}

/* ---------- modal, toast ---------- */
dialog{border:0;border-radius:22px;padding:0;width:min(660px,94vw);box-shadow:var(--sh2);animation:naik .25s ease}
dialog::backdrop{background:rgba(8,15,30,.55);backdrop-filter:blur(3px)}
dialog .h{padding:16px 20px;border-bottom:1px solid var(--line);display:flex;align-items:center;gap:10px}
dialog .h h3{margin:0;font-size:17px;flex:1;letter-spacing:-.01em}
dialog .b{padding:20px;max-height:72vh;overflow:auto}
dialog .f{padding:14px 20px;border-top:1px solid var(--line);display:flex;gap:8px;justify-content:flex-end;flex-wrap:wrap;background:#fafcfe;border-radius:0 0 22px 22px}
#toast{position:fixed;left:50%;bottom:calc(22px + var(--sab));transform:translateX(-50%);background:#0f172a;color:#fff;padding:13px 22px;
  border-radius:999px;display:none;z-index:100;max-width:92vw;font-weight:600;text-align:center;font-size:14.5px;box-shadow:var(--sh2)}
#toast.err{background:var(--err)}
#toast.ok{background:var(--ok)}
#idle-bar{position:fixed;bottom:0;left:0;right:0;background:var(--warn-s);color:var(--warn);font-size:13px;font-weight:600;
  padding:8px 16px;padding-bottom:calc(8px + var(--sab));text-align:center;display:none;z-index:99}

/* ---------- lihat / sembunyikan password ---------- */
input::-ms-reveal,input::-ms-clear{display:none}
input::-webkit-credentials-auto-fill-button{visibility:hidden}
.pw-wrap{position:relative;display:block;width:100%}
.pw-wrap input{padding-right:48px}
.pw-mata{position:absolute;right:4px;top:50%;transform:translateY(-50%);width:40px;height:40px;border:0;background:transparent;
  cursor:pointer;display:grid;place-items:center;color:var(--muted);border-radius:10px}
.pw-mata:hover{color:var(--brand2);background:var(--soft2)}
.pw-mata svg{width:22px;height:22px;pointer-events:none}

@media(max-width:600px){
  main{padding:10px}
  .ring{grid-template-columns:repeat(2,1fr);gap:10px}
  .ring b{font-size:17px}
  .total-val{font-size:22px}
  nav.tabs button{font-size:13px;padding:7px 13px}
  header.topbar{padding:10px 14px;padding-top:calc(10px + var(--sat))}
  .card{padding:16px;border-radius:18px}
  .page-head h1{font-size:20px}
}
</style>
</head>
<body>

<section id="login">
  <div class="card">
    <div class="logo lg"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 2L3 6v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V6l-3-4z"/><path d="M3 6h18"/><path d="M16 10a4 4 0 0 1-8 0"/></svg></div>
    <h1>__APPNAME__</h1>
    <p class="sub">Masuk untuk mulai mencatat penjualan</p>
    <label class="f" for="u">Username</label>
    <input id="u" autocomplete="username" autocapitalize="none" spellcheck="false">
    <div class="gap"></div>
    <label class="f" for="p">Password</label>
    <input id="p" type="password" autocomplete="current-password">
    <div id="kode-wrap" class="hide">
      <div class="gap"></div>
      <label class="f" for="k">Kode 6 angka (Authenticator)</label>
      <input id="k" inputmode="numeric" maxlength="6" autocomplete="one-time-code">
    </div>
    <div id="login-err"></div>
    <div class="gap"></div>
    <button class="btn primary big block" id="masuk">Masuk</button>
  </div>
</section>

<section id="app">
  <header class="topbar">
    <div class="brand"><span class="logo"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M6 2L3 6v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2V6l-3-4z"/><path d="M3 6h18"/><path d="M16 10a4 4 0 0 1-8 0"/></svg></span><span>__APPNAME__</span></div>
    <div class="who"><span class="avatar" id="h-av">-</span><div class="who-t"><b id="h-nama">-</b><small id="h-info">-</small></div></div>
    <span class="grow"></span>
    <button class="btn ghost" id="h-akun">Akun</button>
    <button class="btn ghost" id="h-keluar">Keluar</button>
  </header>
  <div class="shell">
    <nav class="tabs" id="tabs"></nav>
    <div class="content">
      <div class="page-head" id="page-head"><div><h1 id="pj"></h1><p id="pp"></p></div><span class="head-date" id="pd"></span></div>
      <main id="isi"></main>
    </div>
  </div>
</section>

<div id="idle-bar">⏱ Sesi akan berakhir dalam <span id="idle-sisa"></span> menit. Sentuh layar untuk tetap aktif.</div>
<dialog id="modal">
  <div class="h"><h3 id="m-judul"></h3><button class="btn sm" id="m-tutup">✕</button></div>
  <div class="b" id="m-isi"></div>
  <div class="f" id="m-aksi"></div>
</dialog>
<div id="toast" role="status" aria-live="polite"></div>

<script nonce="__NONCE__">
const $ = (s,el=document) => el.querySelector(s);
const $$ = (s,el=document) => [...el.querySelectorAll(s)];
const esc = s => String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const num = n => Number(n||0).toLocaleString('id-ID',{maximumFractionDigits:2});
const rp  = n => 'Rp '+Math.round(n||0).toLocaleString('id-ID');
const BLN = ['Jan','Feb','Mar','Apr','Mei','Jun','Jul','Agu','Sep','Okt','Nov','Des'];
const tgl = s => {if(!s)return'-';const[y,m,d]=s.slice(0,10).split('-');return`${+d} ${BLN[m-1]} ${y}`;};
const jam = s => s?s.slice(11,16):'';
const qs  = o => new URLSearchParams(Object.entries(o).filter(([,v])=>v!==''&&v!=null)).toString();
const hariIni   = () => {const d=new Date();return new Date(d-d.getTimezoneOffset()*6e4).toISOString().slice(0,10);};
const awalBulan = () => hariIni().slice(0,8)+'01';
const tglMundur = n => {const d=new Date();d.setDate(d.getDate()-n);return new Date(d-d.getTimezoneOffset()*6e4).toISOString().slice(0,10);};
let ME=null,TIMER=null;

// ---- IDLE TIMER ----
let _idleTimer=null,_idleSisa=0;
function resetIdle(){
  if(!ME||ME.role==='master')return;
  clearTimeout(_idleTimer);
  const menit=ME.idle_menit||30;
  _idleSisa=menit;
  const bar=$('#idle-bar');
  bar.style.display='none';
  const tick=()=>{
    _idleSisa--;
    if(_idleSisa<=5){bar.style.display='block';$('#idle-sisa').textContent=_idleSisa;}
    if(_idleSisa<=0){
      bar.style.display='none';
      api('/api/logout',{method:'POST',body:{}}).catch(()=>{});
      ME=null;tampilLogin('Sesi berakhir karena tidak aktif selama '+menit+' menit.');
    } else _idleTimer=setTimeout(tick,60000);
  };
  _idleTimer=setTimeout(tick,60000);
}
['click','touchstart','keydown','scroll'].forEach(ev=>document.addEventListener(ev,resetIdle,{passive:true}));

// ---- API ----
async function api(url,opt={}){
  const init={method:opt.method||'GET',headers:{},credentials:'same-origin'};
  if(opt.body!==undefined){init.body=JSON.stringify(opt.body);init.headers['Content-Type']='application/json';}
  if(init.method!=='GET')init.headers['X-CSRF-Token']=ME?.csrf||'';
  const res=await fetch(url,init);
  let data=null;try{data=await res.json();}catch{}
  if(res.status===401&&ME){ME=null;tampilLogin('Sesi berakhir, silakan masuk lagi.');throw new Error('Sesi berakhir.');}
  if(!res.ok){const e=new Error(data?.error||`Gagal (${res.status})`);e.status=res.status;e.data=data||{};throw e;}
  return data;
}
let tOut;
function toast(pesan,tipe='ok'){
  const t=$('#toast');t.textContent=pesan;t.className=tipe;t.style.display='block';
  clearTimeout(tOut);tOut=setTimeout(()=>t.style.display='none',tipe==='err'?6000:2600);
}
const jaga=fn=>async(...a)=>{try{return await fn(...a);}catch(e){toast(e.message,'err');}};
const resetEl=el=>{const n=el.cloneNode(false);el.replaceWith(n);return n;};
function unduh(url){const a=document.createElement('a');a.href=url;document.body.append(a);a.click();a.remove();}

// ---- MODAL ----
const modal=$('#modal');
function buka(judul,isi,aksi=[]){
  $('#m-judul').textContent=judul;
  const b=$('#m-isi');b.innerHTML='';
  typeof isi==='string'?(b.innerHTML=isi):b.append(isi);
  const f=$('#m-aksi');f.innerHTML='';
  aksi.forEach(a=>{
    const el=document.createElement('button');
    el.className='btn '+(a.cls||'');el.textContent=a.teks;
    el.onclick=jaga(async()=>{if(await a.klik?.()!==false)tutup();});
    f.append(el);
  });
  f.style.display=aksi.length?'':'none';
  if(!modal.open)modal.showModal();
}
const tutup=()=>modal.open&&modal.close();
$('#m-tutup').onclick=tutup;
function konfirmasi(judul,teks,ok='Ya',bahaya=true){
  return new Promise(res=>{
    let done=false;
    buka(judul,`<p>${teks}</p>`,[
      {teks:'Batal',klik:()=>{done=true;res(false);}},
      {teks:ok,cls:bahaya?'danger':'primary',klik:()=>{done=true;res(true);}}]);
    modal.addEventListener('close',()=>{if(!done)res(false);},{once:true});
  });
}

// ---- LOGIN ----
function tampilLogin(pesan){
  clearInterval(TIMER);clearTimeout(_idleTimer);
  document.body.classList.remove('side');
  $('#app').style.display='none';$('#login').style.display='flex';
  $('#login-err').innerHTML=pesan?`<div class="note err">${esc(pesan)}</div>`:'';
  $('#p').value='';$('#k').value='';$('#kode-wrap').style.display='none';
  setTimeout(()=>($('#u').value?$('#p'):$('#u')).focus(),60);
}
const masuk=async()=>{
  const btn=$('#masuk');btn.disabled=true;$('#login-err').innerHTML='';
  try{
    ME=await api('/api/login',{method:'POST',body:{username:$('#u').value,password:$('#p').value,kode:$('#k').value}});
    await mulai();
  }catch(e){
    if(e.data?.butuh_kode){$('#kode-wrap').style.display='block';setTimeout(()=>$('#k').focus(),50);}
    $('#login-err').innerHTML=`<div class="note err">${esc(e.message)}</div>`;
  }finally{btn.disabled=false;}
};
$('#masuk').onclick=masuk;
['u','p','k'].forEach(id=>$('#'+id).addEventListener('keydown',e=>e.key==='Enter'&&masuk()));
$('#h-keluar').onclick=jaga(async()=>{
  if(!await konfirmasi('Keluar','Keluar dari aplikasi?','Keluar'))return;
  await api('/api/logout',{method:'POST',body:{}}).catch(()=>{});
  ME=null;tampilLogin();
});
$('#h-akun').onclick=()=>halamanAkun();

async function mulai(){
  $('#login').style.display='none';$('#app').style.display='flex';
  $('#h-nama').textContent=ME.nama;
  $('#h-av').textContent=(ME.nama||'?').trim().charAt(0).toUpperCase();
  const roleLabel={master:'Master',kepala_depo:'Kepala Depo',spg:'SPG'}[ME.role]||ME.role;
  $('#h-info').textContent=roleLabel+' · '+ME.username+(ME.wilayah?' · '+ME.wilayah:'');
  resetIdle();
  if(ME.harus_ganti)return gantiPassword(true);
  if(ME.role==='master')masterUI();
  else if(ME.role==='kepala_depo')depoUI();
  else spgUI();
}

// ---- GANTI PASSWORD ----
function gantiPassword(wajib){
  const w=document.createElement('div');
  w.innerHTML=`${wajib?'<div class="note warn">Ganti password bawaan Anda sebelum memakai aplikasi.</div>':''}
    <label class="f">Password sekarang</label><input type="password" id="pw-lama" autocomplete="current-password">
    <div class="gap-s"></div><label class="f">Password baru</label><input type="password" id="pw-baru" autocomplete="new-password">
    <div class="gap-s"></div><label class="f">Ulangi password baru</label><input type="password" id="pw-baru2" autocomplete="new-password">
    <p class="muted kecil">Minimal 10 karakter, ada huruf dan angka.</p>`;
  buka('Ganti Password',w,[
    ...(wajib?[]:[{teks:'Batal'}]),
    {teks:'Simpan',cls:'primary',klik:async()=>{
      if($('#pw-baru',w).value!==$('#pw-baru2',w).value){toast('Password baru tidak sama','err');return false;}
      await api('/api/password',{method:'POST',body:{lama:$('#pw-lama',w).value,baru:$('#pw-baru',w).value}});
      toast('Password berhasil diganti');ME.harus_ganti=false;
      if(ME.role==='master')masterUI();else if(ME.role==='kepala_depo')depoUI();else spgUI();
    }}]);
  if(wajib)modal.addEventListener('cancel',e=>e.preventDefault(),{once:true});
}

function halamanAkun(){
  const w=document.createElement('div');
  w.innerHTML=`<div class="row"><button class="btn block" id="a-pw">Ganti password</button></div>
    <div class="gap"></div>
    <div class="note ${ME.totp_aktif?'ok':'warn'}">Verifikasi 2 langkah: <b>${ME.totp_aktif?'AKTIF':'belum aktif'}</b>.</div>
    <button class="btn block ${ME.totp_aktif?'danger':'primary'}" id="a-2fa">${ME.totp_aktif?'Matikan 2FA':'Aktifkan 2FA'}</button>`;
  buka('Akun Saya',w,[]);
  $('#a-pw',w).onclick=()=>gantiPassword(false);
  $('#a-2fa',w).onclick=()=>ME.totp_aktif?matikan2fa():aktifkan2fa();
}
const aktifkan2fa=jaga(async()=>{
  const d=await api('/api/2fa/siapkan',{method:'POST',body:{}});
  const w=document.createElement('div');
  w.innerHTML=`<ol class="ol-ak">
    <li>Buka <b>Google Authenticator</b> di HP</li>
    <li>Tambah akun → Masukkan kunci setup</li>
    <li>Kunci: <code class="kode-md">${esc(d.secret)}</code></li>
    <li>Masukkan 6 angka yang muncul di bawah</li></ol>
    <input id="kode2fa" inputmode="numeric" maxlength="6" placeholder="123456">`;
  buka('Aktifkan 2FA',w,[{teks:'Batal'},{teks:'Aktifkan',cls:'primary',klik:async()=>{
    await api('/api/2fa/aktifkan',{method:'POST',body:{kode:$('#kode2fa',w).value}});
    ME.totp_aktif=true;toast('2FA aktif');
  }}]);
});
const matikan2fa=()=>{
  const w=document.createElement('div');
  w.innerHTML=`<div class="note warn">Keamanan akun akan berkurang.</div>
    <label class="f">Password Anda</label><input type="password" id="pw2fa">`;
  buka('Matikan 2FA',w,[{teks:'Batal'},{teks:'Matikan',cls:'danger',klik:async()=>{
    await api('/api/2fa/matikan',{method:'POST',body:{password:$('#pw2fa',w).value}});
    ME.totp_aktif=false;toast('2FA dimatikan');
  }}]);
};

// ================================================================
// SPG UI — MOBILE FRIENDLY (menu: Penjualan | Absen | Stok Masuk)
// ================================================================
const TAB_SPG=[['penjualan','Penjualan'],['absen','Absen'],['stok','Stok Masuk']];
let tabSpg='penjualan';
function spgUI(){
  document.body.classList.remove('side');
  buatNav(TAB_SPG,tabSpg,gantiTabSpg);
  gantiTabSpg(tabSpg);
}
function gantiTabSpg(t){
  tabSpg=t;setHalaman(t);
  $$('#tabs button').forEach(b=>b.classList.toggle('active',b.dataset.t===t));
  clearInterval(TIMER);
  $('#isi').innerHTML='<div class="spg-wrap"><div class="spg-step">Memuat…</div></div>';
  jaga(({penjualan:spgPenjualan,absen:spgAbsen,stok:spgStok})[t])();
}

// ---- SPG: PENJUALAN ----
async function spgPenjualan(){
  const isi=$('#isi');
  const d=await api('/api/spg/awal');
  let toko=d.toko.find(t=>t.uid===d.toko_terakhir)||null;
  let produk=null,satuan='BOTOL',sample=false,qty=1;
  const belumAbsen=!d.absen;

  isi.innerHTML=`<div class="spg-wrap">
    ${belumAbsen?`<div class="note warn">Anda belum absen hari ini. <button class="btn sm primary" id="s-ke-absen">Absen sekarang</button></div>`:''}
    <div class="ring" id="s-ring"></div>

    <div class="spg-step">
      <h2>Pilih Toko <button class="btn sm fr" id="s-muat">↻ Muat ulang</button></h2>
      ${d.toko.length===0?'<div class="note warn">Belum ada toko yang ditugaskan. Hubungi master.</div>':''}
      <select id="s-toko-sel">
        <option value="">— Pilih toko —</option>
        ${d.toko.map(t=>`<option value="${t.uid}">${esc(t.nama)}${t.wilayah?' ('+esc(t.wilayah)+')':''}</option>`).join('')}
      </select>
    </div>

    <div class="spg-step">
      <h2>Pilih Produk</h2>
      <select id="s-produk-sel">
        <option value="">— Pilih produk —</option>
        ${d.produk.map(p=>`<option value="${p.uid}">${esc(p.nama)} · ${esc(p.kode)}</option>`).join('')}
      </select>
      <div id="s-produk-info" class="note info hide mt10"></div>
    </div>

    <div class="spg-step">
      <h2>Jumlah & Satuan</h2>
      <div class="seg">
        <button class="aktif" data-s="BOTOL">BOTOL</button>
        <button data-s="DUS">DUS</button>
      </div>
      <div class="qty-row">
        <button id="s-kurang" aria-label="Kurangi">−</button>
        <input id="s-qty" inputmode="decimal" value="1">
        <button id="s-tambah" aria-label="Tambah">+</button>
      </div>
      <div class="sample-toggle" id="s-sample">
        <input type="checkbox" id="s-sample-cb">
        <div><b>Sample gratis</b><br><small class="muted">harga otomatis jadi 0</small></div>
      </div>
    </div>

    <div class="spg-step" id="s-harga-step">
      <h2>Harga <span id="s-sat-label">per Botol</span></h2>
      <input id="s-harga" inputmode="numeric" placeholder="0">
      <p class="muted kecil mt6">Harga muncul otomatis, bisa diubah bila ada perubahan.</p>
    </div>

    <div class="spg-step">
      <h2>Catatan (opsional)</h2>
      <input id="s-catatan" placeholder="contoh: promo akhir bulan, minta nota">
    </div>

    <div class="spg-step">
      <div class="total-box"><span class="muted fs15">TOTAL</span><div class="total-val" id="s-total">Rp 0</div></div>
      <div class="gap"></div>
      <button class="btn ok big block" id="s-kirim">KIRIM PENJUALAN</button>
    </div>

    <div class="spg-step">
      <h2>Sudah dikirim hari ini</h2>
      <div id="s-daftar"></div>
    </div>
  </div>`;

  if(belumAbsen)$('#s-ke-absen').onclick=()=>gantiTabSpg('absen');

  // toko dropdown
  const selToko=$('#s-toko-sel');
  $('#s-muat').onclick=()=>gantiTabSpg('penjualan');
  if(toko)selToko.value=toko.uid;
  selToko.onchange=()=>{
    toko=d.toko.find(t=>t.uid===selToko.value)||null;
    hitung();
  };

  // produk dropdown
  const selProduk=$('#s-produk-sel');
  const infoProduk=$('#s-produk-info');
  selProduk.onchange=()=>{
    produk=d.produk.find(p=>p.uid===selProduk.value)||null;
    if(produk){
      infoProduk.style.display='block';
      infoProduk.innerHTML=`<b>${esc(produk.nama)}</b> · ${esc(produk.kode)}<br>
        Harga botol: <b>${rp(produk.harga_botol)}</b> &nbsp;|&nbsp; Harga dus: <b>${rp(produk.harga_dus)}</b> (${produk.isi_dus} botol/dus)`;
    }else{infoProduk.style.display='none';}
    isiHarga();hitung();
  };

  document.querySelector('.seg').addEventListener('click',e=>{
    const b=e.target.closest('[data-s]');if(!b)return;
    satuan=b.dataset.s;
    $$('.seg button').forEach(x=>x.classList.toggle('aktif',x===b));
    isiHarga();hitung();
  });

  const hargaDefault=()=>!produk?0:(satuan==='DUS'?produk.harga_dus:produk.harga_botol);
  const isiHarga=()=>{$('#s-harga').value=hargaDefault()?Math.round(hargaDefault()):''};
  const hitung=()=>{
    const h=sample?0:(parseFloat($('#s-harga').value)||0);
    $('#s-total').textContent=rp(qty*h);
    $('#s-sat-label').textContent=satuan==='DUS'?'per Dus':'per Botol';
    $('#s-harga-step').style.display=sample?'none':'';
    $('#s-sample').classList.toggle('aktif',sample);
    $('#s-kirim').textContent=sample?'KIRIM SAMPLE GRATIS':'KIRIM PENJUALAN';
    $('#s-kirim').className='btn big block '+(sample?'primary':'ok');
  };

  const setQty=v=>{qty=Math.max(0,Math.round(v*100)/100);$('#s-qty').value=qty;hitung();};
  $('#s-kurang').onclick=()=>setQty(qty-1);
  $('#s-tambah').onclick=()=>setQty(qty+1);
  $('#s-qty').oninput=()=>{qty=parseFloat($('#s-qty').value)||0;hitung();};
  $('#s-harga').oninput=hitung;
  $('#s-sample').onclick=e=>{
    if(e.target.id!=='s-sample-cb')$('#s-sample-cb').checked=!$('#s-sample-cb').checked;
    sample=$('#s-sample-cb').checked;hitung();
  };

  const gambarDaftar=data=>{
    const r=data.ringkas;
    $('#s-ring').innerHTML=`
      <div><b>${num(r.botol_jual)}</b><span>botol terjual</span></div>
      <div><b>${num(r.botol_sample)}</b><span>botol sample</span></div>
      <div><b>${rp(r.total)}</b><span>total rupiah</span></div>
      <div><b>${num(r.jumlah)}</b><span>entri hari ini</span></div>`;
    $('#s-daftar').innerHTML=data.rows.length?data.rows.map(e=>{
      const bolehHapus=(Date.now()-new Date(e.waktu).getTime())/60000<d.edit_menit;
      return`<div class="entri"><div class="jam">${jam(e.waktu)}</div>
        <div class="isi"><b>${esc(e.produk)} · ${num(e.qty)} ${e.satuan}</b>
          <small>${esc(e.toko)} ${e.jenis==='SAMPLE'?'<span class="badge b-sample">SAMPLE</span>':''}${e.catatan?' · '+esc(e.catatan):''}</small></div>
        <div class="nilai">${e.jenis==='SAMPLE'?'-':rp(e.total)}</div>
        ${bolehHapus?`<button class="btn sm danger noflex" data-hapus="${e.uid}">Hapus</button>`:''}</div>`;
    }).join(''):'<div class="empty">Belum ada. Isi form di atas lalu tekan KIRIM.</div>';
  };
  gambarDaftar(d.hari_ini);

  $('#s-daftar').onclick=jaga(async e=>{
    const b=e.target.closest('[data-hapus]');if(!b)return;
    if(!await konfirmasi('Hapus','Hapus data ini?','Hapus'))return;
    await api('/api/penjualan/'+b.dataset.hapus,{method:'DELETE'});
    toast('Data dihapus');segarkan();
  });
  const segarkan=jaga(async()=>{
    const baru=await api('/api/penjualan?'+qs({dari:hariIni(),sampai:hariIni()}));
    gambarDaftar(baru);
  });

  $('#s-kirim').onclick=jaga(async()=>{
    if(!toko)return toast('Pilih toko dulu','err');
    if(!produk)return toast('Pilih produk dulu','err');
    if(!qty)return toast('Isi jumlahnya dulu','err');
    const btn=$('#s-kirim');btn.disabled=true;
    try{
      await api('/api/penjualan',{method:'POST',body:{
        toko_uid:toko.uid,produk_uid:produk.uid,jenis:sample?'SAMPLE':'JUAL',satuan,
        qty,harga:sample?0:$('#s-harga').value,catatan:$('#s-catatan').value}});
      toast(sample?'Sample tercatat':'Penjualan tercatat','ok');
      $('#s-catatan').value='';setQty(1);
      $('#s-sample-cb').checked=false;sample=false;isiHarga();hitung();
      segarkan();
    }finally{btn.disabled=false;}
  });

  clearInterval(TIMER);
  TIMER=setInterval(segarkan,60000);
}

// ---- SPG: ABSEN ----
const LABEL_ABSEN={HADIR:'Hadir',IZIN:'Izin',SAKIT:'Sakit'};
const badgeAbsen=s=>`<span class="badge ${s==='HADIR'?'b-ok':s==='SAKIT'?'b-err':'b-sample'}">${LABEL_ABSEN[s]||esc(s)}</span>`;

async function spgAbsen(){
  const isi=$('#isi');
  const [d,riw]=await Promise.all([api('/api/spg/awal'),api('/api/absen?'+qs({dari:tglMundur(13),sampai:hariIni()}))]);
  const a=d.absen,sudahMasuk=a&&a.status==='HADIR';
  const pilihToko=`<label class="f" for="ab-toko">Toko tempat bertugas hari ini</label>
    <select id="ab-toko"><option value="">— Pilih toko —</option>
      ${d.toko.map(t=>`<option value="${t.uid}" ${(d.toko.length===1||t.uid===d.toko_terakhir)?'selected':''}>${esc(t.nama)}${t.wilayah?' ('+esc(t.wilayah)+')':''}</option>`).join('')}
    </select>`;
  let kartuUtama;
  if(sudahMasuk){
    kartuUtama=`<div class="note ok">✅ Absen masuk pukul <b>${jam(a.jam_masuk)}</b> di <b>${esc(a.toko)}</b>.
        ${a.jam_pulang?` Pulang pukul <b>${jam(a.jam_pulang)}</b>.`:''}</div>
      ${a.jam_pulang?'<div class="note info">Absen hari ini sudah lengkap. Terima kasih!</div>'
        :'<button class="btn primary big block" id="ab-pulang">ABSEN PULANG</button>'}`;
  }else{
    kartuUtama=`${a?`<div class="note warn">Status hari ini: ${badgeAbsen(a.status)} ${esc(a.catatan||'')}<br>Jika ternyata Anda masuk, silakan absen masuk di bawah.</div>`:''}
      ${d.toko.length===0?'<div class="note warn">Belum ada toko yang ditugaskan. Hubungi master.</div>':''}
      ${pilihToko}<div class="gap"></div>
      <button class="btn ok big block" id="ab-masuk">ABSEN MASUK</button>`;
  }
  isi.innerHTML=`<div class="spg-wrap">
    <div class="card"><h2>Absen hari ini · ${tgl(hariIni())}</h2>${kartuUtama}</div>
    ${sudahMasuk?'':`<div class="card"><h2>Tidak bisa masuk?</h2>
      <label class="f" for="ab-status">Keterangan</label>
      <select id="ab-status"><option value="IZIN">Izin</option><option value="SAKIT">Sakit</option></select>
      <div class="gap-s"></div>
      <label class="f" for="ab-alasan">Alasan</label>
      <input id="ab-alasan" placeholder="contoh: acara keluarga / demam">
      <div class="gap"></div>
      <button class="btn block" id="ab-izin">Kirim izin / sakit</button></div>`}
    <div class="card"><h2>Riwayat 14 hari terakhir</h2><div id="ab-riw">
      ${riw.rows.length?riw.rows.map(r=>`<div class="entri">
        <div class="isi"><b>${tgl(r.tanggal)}</b>
          <small>${r.status==='HADIR'?esc(r.toko)+' · '+jam(r.jam_masuk)+' – '+(r.jam_pulang?jam(r.jam_pulang):'belum pulang'):esc(r.catatan||'')}</small></div>
        <div>${badgeAbsen(r.status)}</div></div>`).join('')
        :'<div class="empty">Belum ada riwayat absen.</div>'}
    </div></div></div>`;

  const kirim=(body,pesan)=>jaga(async()=>{
    await api('/api/absen/masuk',{method:'POST',body});
    toast(pesan);spgAbsen();
  })();
  if($('#ab-masuk'))$('#ab-masuk').onclick=()=>{
    const toko_uid=$('#ab-toko').value;
    if(!toko_uid)return toast('Pilih toko dulu','err');
    kirim({status:'HADIR',toko_uid},'Absen masuk tercatat');
  };
  if($('#ab-izin'))$('#ab-izin').onclick=()=>{
    const alasan=$('#ab-alasan').value.trim();
    if(!alasan)return toast('Isi alasannya dulu','err');
    kirim({status:$('#ab-status').value,catatan:alasan},'Keterangan tercatat');
  };
  if($('#ab-pulang'))$('#ab-pulang').onclick=jaga(async()=>{
    if(!await konfirmasi('Absen pulang','Absen pulang sekarang?','Ya, pulang',false))return;
    await api('/api/absen/pulang',{method:'POST',body:{}});
    toast('Absen pulang tercatat');spgAbsen();
  });
}

// ---- SPG: STOK MASUK ----
async function spgStok(){
  const isi=$('#isi');
  const [d,riw]=await Promise.all([api('/api/spg/awal'),
    api('/api/stok/masuk?'+qs({dari:tglMundur(6),sampai:hariIni()}))]);
  let satuan='BOTOL',qty=1;
  isi.innerHTML=`<div class="spg-wrap">
    <div class="note info">Menu ini untuk mencatat <b>barang/stok yang masuk ke toko</b> (kiriman). Penjualan harian tetap diisi di menu Penjualan.</div>
    <div class="spg-step"><h2>Pilih Toko</h2>
      ${d.toko.length===0?'<div class="note warn">Belum ada toko yang ditugaskan. Hubungi master.</div>':''}
      <select id="k-toko"><option value="">— Pilih toko —</option>
        ${d.toko.map(t=>`<option value="${t.uid}" ${(d.toko.length===1||t.uid===d.toko_terakhir)?'selected':''}>${esc(t.nama)}</option>`).join('')}</select></div>
    <div class="spg-step"><h2>Pilih Produk</h2>
      <select id="k-produk"><option value="">— Pilih produk —</option>
        ${d.produk.map(p=>`<option value="${p.uid}">${esc(p.nama)} · ${esc(p.kode)}</option>`).join('')}</select>
      <div id="k-info" class="note info hide mt10"></div></div>
    <div class="spg-step"><h2>Jumlah Masuk</h2>
      <div class="seg"><button class="aktif" data-s="BOTOL">BOTOL</button><button data-s="DUS">DUS</button></div>
      <div class="qty-row"><button id="k-kurang" aria-label="Kurangi">−</button>
        <input id="k-qty" inputmode="decimal" value="1">
        <button id="k-tambah" aria-label="Tambah">+</button></div></div>
    <div class="spg-step"><h2>Catatan (opsional)</h2>
      <input id="k-catatan" placeholder="contoh: kiriman dari gudang, no. surat jalan"></div>
    <div class="spg-step"><button class="btn primary big block" id="k-kirim">KIRIM STOK MASUK</button></div>
    <div class="spg-step"><h2>Stok masuk 7 hari terakhir</h2><div id="k-daftar"></div></div></div>`;

  const produkAktif=()=>d.produk.find(p=>p.uid===$('#k-produk').value)||null;
  const setQty=v=>{qty=Math.max(0,Math.round(v*100)/100);$('#k-qty').value=qty;infoBotol();};
  const infoBotol=()=>{
    const p=produkAktif(),el=$('#k-info');
    if(!p){el.style.display='none';return;}
    el.style.display='block';
    el.innerHTML=satuan==='DUS'?`${num(qty)} dus = <b>${num(qty*p.isi_dus)} botol</b> (${p.isi_dus} botol/dus)`:`<b>${num(qty)} botol</b>`;
  };
  $('#k-produk').onchange=infoBotol;
  document.querySelector('.seg').addEventListener('click',e=>{
    const b=e.target.closest('[data-s]');if(!b)return;
    satuan=b.dataset.s;$$('.seg button').forEach(x=>x.classList.toggle('aktif',x===b));infoBotol();
  });
  $('#k-kurang').onclick=()=>setQty(qty-1);
  $('#k-tambah').onclick=()=>setQty(qty+1);
  $('#k-qty').oninput=()=>{qty=parseFloat($('#k-qty').value)||0;infoBotol();};

  const gambar=data=>{
    $('#k-daftar').innerHTML=data.rows.length?data.rows.map(e=>{
      const bolehHapus=(Date.now()-new Date(e.waktu).getTime())/60000<d.edit_menit;
      return`<div class="entri"><div class="jam">${jam(e.waktu)}</div>
        <div class="isi"><b>${esc(e.produk)} · ${num(e.qty)} ${e.satuan}</b>
          <small>${tgl(e.tanggal)} · ${esc(e.toko)}${e.satuan==='DUS'?' · '+num(e.botol_setara)+' botol':''}${e.catatan?' · '+esc(e.catatan):''}</small></div>
        ${bolehHapus?`<button class="btn sm danger" data-hapus="${e.uid}">Hapus</button>`:''}</div>`;
    }).join(''):'<div class="empty">Belum ada stok masuk.</div>';
  };
  gambar(riw);
  $('#k-daftar').onclick=jaga(async e=>{
    const b=e.target.closest('[data-hapus]');if(!b)return;
    if(!await konfirmasi('Hapus','Hapus data stok masuk ini?','Hapus'))return;
    await api('/api/stok/masuk/'+b.dataset.hapus,{method:'DELETE'});
    toast('Data dihapus');
    gambar(await api('/api/stok/masuk?'+qs({dari:tglMundur(6),sampai:hariIni()})));
  });
  $('#k-kirim').onclick=jaga(async()=>{
    const toko_uid=$('#k-toko').value,produk_uid=$('#k-produk').value;
    if(!toko_uid)return toast('Pilih toko dulu','err');
    if(!produk_uid)return toast('Pilih produk dulu','err');
    if(!qty)return toast('Isi jumlahnya dulu','err');
    const btn=$('#k-kirim');btn.disabled=true;
    try{
      await api('/api/stok/masuk',{method:'POST',body:{toko_uid,produk_uid,satuan,qty,catatan:$('#k-catatan').value}});
      toast('Stok masuk tercatat');
      $('#k-catatan').value='';setQty(1);
      gambar(await api('/api/stok/masuk?'+qs({dari:tglMundur(6),sampai:hariIni()})));
    }finally{btn.disabled=false;}
  });
}

// ================================================================
// KEPALA DEPO UI
// ================================================================
const TAB_DEPO=[['dashboard','Dashboard','Ringkasan'],['penjualan','Penjualan'],['laporan','Laporan'],
                ['absen','Absensi','Tim'],['permintaan','Permintaan']];
let tabDepo='dashboard';
function depoUI(){
  document.body.classList.add('side');
  buatNav(TAB_DEPO,tabDepo,gantiTabDepo);
  gantiTabDepo(tabDepo);
}
function gantiTabDepo(t){
  tabDepo=t;setHalaman(t);
  $$('#tabs button').forEach(b=>b.classList.toggle('active',b.dataset.t===t));
  clearInterval(TIMER);
  $('#isi').innerHTML='<div class="card">Memuat…</div>';
  ({dashboard:mDashboard,penjualan:mPenjualan,laporan:mLaporan,absen:mAbsensi,permintaan:mPermintaanDepo}[t])($('#isi'));
}

async function mPermintaanDepo(el){
  el=resetEl(el);
  el.innerHTML=`<div class="card">
    <div class="row"><h2>Permintaan ke Master</h2>
    <button class="btn primary" id="pr-baru">+ Kirim Permintaan</button></div></div>
    <div id="pr-list" class="card">Memuat…</div>`;
  const muat=jaga(async()=>{
    const list=await api('/api/permintaan');
    $('#pr-list').innerHTML=list.length?list.map(r=>`<div class="entri">
      <div class="isi"><b>${esc({tambah_toko:'Tambah Toko',tambah_produk:'Tambah Produk',tambah_spg:'Tambah SPG'}[r.tipe]||r.tipe)}</b>
        <small>${tgl(r.waktu)} · ${esc(JSON.parse(r.data||'{}').keterangan||'')}</small>
        ${r.catatan_master?`<small class="muted">Catatan master: ${esc(r.catatan_master)}</small>`:''}</div>
      <div><span class="badge ${r.status==='approved'?'b-ok':r.status==='rejected'?'b-err':'b-sample'}">${r.status}</span></div>
    </div>`).join(''):'<div class="empty">Belum ada permintaan.</div>';
  });
  muat();
  $('#pr-baru').onclick=()=>{
    const w=document.createElement('div');
    w.innerHTML=`<label class="f">Jenis permintaan</label>
      <select id="pr-tipe">
        <option value="tambah_toko">Tambah Toko</option>
        <option value="tambah_produk">Tambah Produk</option>
        <option value="tambah_spg">Tambah SPG</option>
      </select>
      <div class="gap"></div>
      <label class="f">Detail / keterangan</label>
      <textarea id="pr-detail" rows="4" placeholder="Nama toko, alamat, atau info lainnya…" class="rsz"></textarea>`;
    buka('Kirim Permintaan ke Master',w,[{teks:'Batal'},{teks:'Kirim',cls:'primary',klik:async()=>{
      const tipe=$('#pr-tipe',w).value;
      const detail=$('#pr-detail',w).value;
      if(!detail.trim()){toast('Isi keterangannya dulu','err');return false;}
      await api('/api/permintaan',{method:'POST',body:{tipe,data:{keterangan:detail,wilayah:ME.wilayah}}});
      toast('Permintaan terkirim ke master');muat();
    }}]);
  };
}

// ================================================================
// MASTER UI
// ================================================================
const TAB_MASTER=[['dashboard','Dashboard','Ringkasan'],['penjualan','Penjualan'],['laporan','Laporan'],
                  ['absen','Absensi','Operasional'],['stok','Stok'],
                  ['spg','Akun Pengguna','Data Master'],['toko','Toko'],['produk','Produk'],['permintaan','Permintaan'],
                  ['backup','Backup Data','Sistem'],['log','Log Keamanan']];
let tabMaster='dashboard';
function masterUI(){
  document.body.classList.add('side');
  buatNav(TAB_MASTER,tabMaster,gantiTabMaster);
  gantiTabMaster(tabMaster);
}
function gantiTabMaster(t){
  tabMaster=t;setHalaman(t);
  $$('#tabs button').forEach(b=>b.classList.toggle('active',b.dataset.t===t));
  clearInterval(TIMER);
  $('#isi').innerHTML='<div class="card">Memuat…</div>';
  ({dashboard:mDashboard,penjualan:mPenjualan,laporan:mLaporan,absen:mAbsensi,stok:mStok,
    spg:mSpg,toko:mToko,produk:mProduk,permintaan:mPermintaanMaster,backup:mBackup,log:mLog}[t])($('#isi'));
}

// ---- DASHBOARD (shared master & depo) ----
async function mDashboard(el){
  el=resetEl(el);
  const gambar=d=>{
    const h=d.hari_ini,b=d.bulan_ini,ab=d.absen||{hadir:0,izin:0,total:0};
    const total14=(d.tren||[]).reduce((t,x)=>t+(x.total||0),0);
    el.innerHTML=`
      <div class="ring">
        <div><b>${rp(h.total)}</b><span>penjualan hari ini</span></div>
        <div><b>${num(h.botol)}</b><span>botol terjual hari ini</span></div>
        <div><b>${num(h.sample)}</b><span>botol sample hari ini</span></div>
        <div><b>${num(ab.hadir)} <span class="dim">/ ${num(ab.total)}</span></b><span>SPG hadir${ab.izin?` · ${num(ab.izin)} izin/sakit`:''}</span></div>
        <div><b>${num(h.toko)}</b><span>toko terisi hari ini</span></div>
        <div><b>${rp(b.total)}</b><span>penjualan bulan ini</span></div>
      </div>
      <div class="card"><div class="card-head"><h2>Penjualan 14 hari terakhir</h2><span class="muted kecil">total ${rp(total14)}</span></div>
        ${grafikTren(d.tren)}</div>
      <div class="grid2">
        <div class="card"><h2>Masuk terbaru</h2><div id="d-live"></div></div>
        <div>
          <div class="card"><h2>Per SPG hari ini</h2><div class="tbl pendek"><table>
            <thead><tr><th>SPG</th><th>Entri</th><th>Botol</th><th>Sample</th><th>Total</th><th>Terakhir</th></tr></thead>
            <tbody>${d.per_spg.map(s=>`<tr><td>${esc(s.spg)}</td><td class="n">${s.entri}</td>
              <td class="n">${num(s.botol)}</td><td class="n">${num(s.sample)}</td>
              <td class="n">${num(s.total)}</td><td>${s.terakhir?jam(s.terakhir):'-'}</td></tr>`).join('')}</tbody>
          </table></div></div>
          <div class="card"><h2>Toko belum input hari ini (${d.toko_belum_isi.length})</h2>
            <div class="chips">${d.toko_belum_isi.map(t=>`<span class="chip">${esc(t.nama)}</span>`).join('')||'<span class="muted">Semua toko sudah input.</span>'}</div></div>
        </div>
      </div>`;
    $('#d-live').innerHTML=d.terbaru.length?d.terbaru.map(e=>`<div class="entri">
      <div class="jam">${jam(e.waktu)}</div>
      <div class="isi"><b>${esc(e.produk)} · ${num(e.qty)} ${e.satuan}</b>
        <small>${esc(e.toko)} · ${esc(e.spg)} ${e.jenis==='SAMPLE'?'<span class="badge b-sample">SAMPLE</span>':''}</small></div>
      <div class="nilai">${e.jenis==='SAMPLE'?'-':rp(e.total)}</div></div>`).join('')
    :'<div class="empty">Belum ada input hari ini.</div>';
  };
  gambar(await api('/api/dashboard'));
  TIMER=setInterval(jaga(async()=>{if((ME.role==='master'?tabMaster:tabDepo)==='dashboard')gambar(await api('/api/dashboard'));}),20000);
}

// ---- FILTER BAR ----
function filterBar(id,opsi,extra=''){
  return`<div class="card"><div class="form">
    <div><label class="f">Dari</label><input type="date" id="${id}-dari" value="${awalBulan()}"></div>
    <div><label class="f">Sampai</label><input type="date" id="${id}-sampai" value="${hariIni()}"></div>
    <div><label class="f">SPG</label><select id="${id}-spg"><option value="">Semua</option>${opsi.spg}</select></div>
    <div><label class="f">Toko</label><select id="${id}-toko"><option value="">Semua</option>${opsi.toko}</select></div>
    <div><label class="f">Produk</label><select id="${id}-produk"><option value="">Semua</option>${opsi.produk}</select></div>
    <div><label class="f">Jenis</label><select id="${id}-jenis"><option value="">Semua</option>
      <option value="JUAL">Jual</option><option value="SAMPLE">Sample</option></select></div>
    <div><label class="f">Cari</label><input id="${id}-q" placeholder="toko / produk / sales / catatan"></div>
    <div class="full row">
      <button class="btn primary" id="${id}-go">Tampilkan</button>
      <button class="btn" data-cepat="hari">Hari ini</button>
      <button class="btn" data-cepat="kemarin">Kemarin</button>
      <button class="btn" data-cepat="bulan">Bulan ini</button>
      <span class="spacer"></span>${extra}
    </div></div></div>`;
}
const nilaiFilter=id=>({dari:$(`#${id}-dari`).value,sampai:$(`#${id}-sampai`).value,
  spg_uid:$(`#${id}-spg`).value,toko_uid:$(`#${id}-toko`).value,
  produk_uid:$(`#${id}-produk`).value,jenis:$(`#${id}-jenis`).value,q:$(`#${id}-q`).value});
function pasangCepat(el,id,load){
  el.addEventListener('click',e=>{
    const b=e.target.closest('[data-cepat]');if(!b)return;
    const d=new Date(),pad=n=>String(n).padStart(2,'0');
    const f=x=>`${x.getFullYear()}-${pad(x.getMonth()+1)}-${pad(x.getDate())}`;
    let a,c;
    if(b.dataset.cepat==='hari')a=c=f(d);
    else if(b.dataset.cepat==='kemarin'){const y=new Date(d-864e5);a=c=f(y);}
    else{a=awalBulan();c=hariIni();}
    $(`#${id}-dari`).value=a;$(`#${id}-sampai`).value=c;load();
  });
}
async function opsiFilter(){
  const [spg,toko,produk]=await Promise.all([
    ME.role==='master'?api('/api/pengguna'):Promise.resolve([]),
    api('/api/toko'),api('/api/produk?semua=1')]);
  return{
    spg:spg.filter(u=>u.role==='spg').map(u=>`<option value="${u.uid}">${esc(u.nama)}</option>`).join(''),
    toko:toko.map(t=>`<option value="${t.uid}">${esc(t.nama)}</option>`).join(''),
    produk:produk.map(p=>`<option value="${p.uid}">${esc(p.nama)}</option>`).join(''),
    _spg:spg,_toko:toko,_produk:produk};
}

async function mPenjualan(el){
  el=resetEl(el);
  const opsi=await opsiFilter();
  const xtra=ME.role==='master'?'<button class="btn" id="f-xls">Export Excel</button>':'';
  el.innerHTML=filterBar('f',opsi,xtra)+
    '<div class="ring" id="f-ring"></div><div class="tbl" id="f-tabel"></div>';
  const load=jaga(async()=>{
    const d=await api('/api/penjualan?'+qs(nilaiFilter('f')));
    const r=d.ringkas;
    $('#f-ring').innerHTML=`<div><b>${num(r.jumlah)}</b><span>entri</span></div>
      <div><b>${num(r.botol_jual)}</b><span>botol terjual</span></div>
      <div><b>${num(r.botol_sample)}</b><span>botol sample</span></div>
      <div><b>${rp(r.total)}</b><span>total rupiah</span></div>
      <div><b>${num(r.toko)}</b><span>toko</span></div><div><b>${num(r.spg)}</b><span>SPG</span></div>`;
    $('#f-tabel').innerHTML=d.rows.length?`<table><thead><tr><th>Tanggal</th><th>Jam</th><th>SPG</th>
      <th>Toko</th><th>Sales</th><th>Produk</th><th>Jenis</th><th>Qty</th><th>Satuan</th>
      <th>Botol</th><th>Harga</th><th>Total</th><th>Catatan</th>
      ${ME.role==='master'?'<th></th>':''}</tr></thead>
      <tbody>${d.rows.map(e=>`<tr><td>${tgl(e.tanggal)}</td><td>${jam(e.waktu)}</td><td>${esc(e.spg)}</td>
        <td>${esc(e.toko)}</td><td>${esc(e.sales||'-')}</td><td>${esc(e.produk)}</td>
        <td>${e.jenis==='SAMPLE'?'<span class="badge b-sample">SAMPLE</span>':'<span class="badge b-jual">JUAL</span>'}</td>
        <td class="n">${num(e.qty)}</td><td>${e.satuan}</td><td class="n">${num(e.botol_setara)}</td>
        <td class="n">${num(e.harga)}</td><td class="n">${num(e.total)}</td><td>${esc(e.catatan)}</td>
        ${ME.role==='master'?`<td><button class="btn sm danger" data-hapus="${e.uid}">Hapus</button></td>`:''}</tr>`).join('')}</tbody></table>`
    :'<div class="empty">Tidak ada data.</div>';
  });
  $('#f-go').onclick=load;
  $('#f-q').addEventListener('keydown',e=>e.key==='Enter'&&load());
  ['spg','toko','produk','jenis'].forEach(k=>$(`#f-${k}`)&&($(`#f-${k}`).onchange=load));
  if(ME.role==='master')$('#f-xls').onclick=()=>{unduh('/export/penjualan?'+qs(nilaiFilter('f')));toast('Menyiapkan file…');};
  pasangCepat(el,'f',load);
  el.addEventListener('click',jaga(async e=>{
    const b=e.target.closest('[data-hapus]');if(!b)return;
    if(!await konfirmasi('Hapus data','Hapus entri ini?','Hapus'))return;
    await api('/api/penjualan/'+b.dataset.hapus,{method:'DELETE'});toast('Dihapus');load();
  }));
  load();
}

async function mLaporan(el){
  el=resetEl(el);
  const opsi=await opsiFilter();
  const xtra=`<button class="btn" id="l-xls">Export Excel</button>`;
  el.innerHTML=filterBar('l',opsi,xtra)+
    '<div class="ring" id="l-ring"></div><div class="grid2" id="l-grup"></div>';
  const judul={spg:'Per SPG',toko:'Per Toko',sales:'Per Sales',produk:'Per Produk',tanggal:'Per Tanggal',wilayah:'Per Wilayah'};
  const load=jaga(async()=>{
    const d=await api('/api/laporan?'+qs({...nilaiFilter('l'),limit:1}));
    const r=d.ringkas;
    $('#l-ring').innerHTML=`<div><b>${num(r.jumlah)}</b><span>entri</span></div>
      <div><b>${num(r.botol_jual)}</b><span>botol terjual</span></div>
      <div><b>${num(r.botol_sample)}</b><span>botol sample</span></div>
      <div><b>${rp(r.total)}</b><span>total rupiah</span></div>`;
    $('#l-grup').innerHTML=Object.entries(d.grup).map(([k,arr])=>`<div class="card"><h2>${judul[k]||k}</h2>
      <div class="tbl pendek"><table><thead><tr>
        <th>${(judul[k]||k).replace('Per ','')}</th><th>Entri</th><th>Botol</th><th>Sample</th><th>Total</th></tr></thead>
      <tbody>${arr.map(x=>`<tr><td>${esc(k==='tanggal'?tgl(x.label):x.label)}</td>
        <td class="n">${x.entri}</td><td class="n">${num(x.botol_jual)}</td>
        <td class="n">${num(x.botol_sample)}</td><td class="n">${num(x.total)}</td></tr>`).join('')
      ||'<tr><td colspan="5" class="empty">Tidak ada data</td></tr>'}</tbody></table></div></div>`).join('');
  });
  $('#l-go').onclick=load;
  ['spg','toko','produk','jenis'].forEach(k=>$(`#l-${k}`)&&($(`#l-${k}`).onchange=load));
  $('#l-xls').onclick=()=>unduh('/export/penjualan?'+qs(nilaiFilter('l')));
  pasangCepat(el,'l',load);
  load();
}

// ---- ABSENSI (master & kepala depo) ----
async function mAbsensi(el){
  el=resetEl(el);
  const spg=ME.role==='master'?(await api('/api/pengguna')).filter(u=>u.role==='spg'&&u.aktif):[];
  el.innerHTML=`<div class="card"><div class="form">
    <div><label class="f">Dari</label><input type="date" id="a-dari" value="${hariIni()}"></div>
    <div><label class="f">Sampai</label><input type="date" id="a-sampai" value="${hariIni()}"></div>
    ${ME.role==='master'?`<div><label class="f">SPG</label><select id="a-spg"><option value="">Semua</option>
      ${spg.map(u=>`<option value="${u.uid}">${esc(u.nama)}</option>`).join('')}</select></div>`:''}
    <div><label class="f">Status</label><select id="a-status"><option value="">Semua</option>
      <option value="HADIR">Hadir</option><option value="IZIN">Izin</option><option value="SAKIT">Sakit</option></select></div>
    <div class="full row">
      <button class="btn primary" id="a-go">Tampilkan</button>
      <button class="btn" data-cepat="hari">Hari ini</button>
      <button class="btn" data-cepat="kemarin">Kemarin</button>
      <button class="btn" data-cepat="bulan">Bulan ini</button>
    </div></div></div>
    <div class="ring" id="a-ring"></div>
    <div id="a-belum"></div>
    <div class="card"><h2>Detail absen</h2><div class="tbl" id="a-tabel"></div></div>
    <div class="card"><h2>Rekap per SPG (sesuai periode)</h2><div class="tbl pendek" id="a-rekap"></div></div>`;
  const load=jaga(async()=>{
    const d=await api('/api/absen?'+qs({dari:$('#a-dari').value,sampai:$('#a-sampai').value,
      spg_uid:$('#a-spg')?.value||'',status:$('#a-status').value}));
    const r=d.ringkas;
    $('#a-ring').innerHTML=`<div><b>${num(r.hadir)}</b><span>hadir</span></div>
      <div><b>${num(r.izin)}</b><span>izin</span></div><div><b>${num(r.sakit)}</b><span>sakit</span></div>
      <div><b>${num(r.jumlah)}</b><span>total catatan</span></div>`;
    $('#a-belum').innerHTML=d.belum?`<div class="card"><h2>Belum absen pada ${tgl($('#a-dari').value)} (${d.belum.length})</h2>
      <div class="chips">${d.belum.map(b=>`<span class="chip">${esc(b.nama)}${b.toko?' · '+esc(b.toko):''}</span>`).join('')
        ||'<span class="muted">Semua SPG sudah absen.</span>'}</div></div>`:'';
    $('#a-tabel').innerHTML=d.rows.length?`<table><thead><tr><th>Tanggal</th><th>SPG</th><th>Status</th>
      <th>Toko</th><th>Sales</th><th>Masuk</th><th>Pulang</th><th>Keterangan</th>${ME.role==='master'?'<th></th>':''}</tr></thead>
      <tbody>${d.rows.map(x=>`<tr><td>${tgl(x.tanggal)}</td><td>${esc(x.spg)}</td><td>${badgeAbsen(x.status)}</td>
        <td>${esc(x.toko||'-')}</td><td>${esc(x.sales||'-')}</td><td>${jam(x.jam_masuk)||'-'}</td>
        <td>${jam(x.jam_pulang)||'-'}</td><td>${esc(x.catatan||'')}</td>
        ${ME.role==='master'?`<td><button class="btn sm danger" data-hapus="${x.uid}">Hapus</button></td>`:''}</tr>`).join('')}</tbody></table>`
      :'<div class="empty">Belum ada data absen.</div>';
    $('#a-rekap').innerHTML=d.rekap.length?`<table><thead><tr><th>SPG</th><th>Hadir</th><th>Izin</th><th>Sakit</th><th>Total hari</th></tr></thead>
      <tbody>${d.rekap.map(x=>`<tr><td>${esc(x.spg)}</td><td class="n">${x.hadir}</td><td class="n">${x.izin}</td>
        <td class="n">${x.sakit}</td><td class="n">${x.hari}</td></tr>`).join('')}</tbody></table>`
      :'<div class="empty">Tidak ada data.</div>';
  });
  $('#a-go').onclick=load;
  ['a-status','a-spg'].forEach(id=>$('#'+id)&&($('#'+id).onchange=load));
  pasangCepat(el,'a',load);
  el.addEventListener('click',jaga(async e=>{
    const b=e.target.closest('[data-hapus]');if(!b)return;
    if(!await konfirmasi('Hapus absen','Hapus data absen ini? SPG bisa absen ulang.','Hapus'))return;
    await api('/api/absen/'+b.dataset.hapus,{method:'DELETE'});toast('Dihapus');load();
  }));
  load();
}

// ---- STOK (master) ----
async function mStok(el){
  el=resetEl(el);
  const toko=await api('/api/toko');
  el.innerHTML=`<div class="card"><div class="row">
    <h2 class="judul">Stok per toko</h2>
    <select id="st-toko" class="lebar"><option value="">Semua toko</option>
      ${toko.map(t=>`<option value="${t.uid}">${esc(t.nama)}</option>`).join('')}</select></div>
    <p class="muted kecil">Stok awal <b>hanya terlihat oleh master</b>. Stok masuk diinput SPG lewat menu <b>Stok Masuk</b>.
      Sisa = stok awal + masuk − terjual − sample, dihitung sejak tanggal stok awal toko tersebut.</p></div>
    <div class="tbl" id="st-tabel"></div>
    <div class="card"><h2>Riwayat stok masuk (30 hari terakhir)</h2><div class="tbl pendek" id="st-riw"></div></div>`;
  let data=[];
  const muat=jaga(async()=>{
    const tuid=$('#st-toko').value;
    const [s,m]=await Promise.all([api('/api/stok?'+qs({toko_uid:tuid})),
      api('/api/stok/masuk?'+qs({dari:tglMundur(29),sampai:hariIni(),toko_uid:tuid}))]);
    data=s.rows;
    let html='',terakhir='';
    data.forEach(r=>{
      if(r.toko_uid!==terakhir){
        terakhir=r.toko_uid;
        html+=`<tr class="grup-toko"><td colspan="7">${esc(r.toko)}${r.sales?' · Sales: '+esc(r.sales):''}
          &nbsp;<button class="btn sm" data-atur="${r.toko_uid}">Atur stok awal</button></td></tr>`;
      }
      html+=`<tr><td>${esc(r.produk)} <span class="muted">${esc(r.kode)}</span></td>
        <td class="n">${r.diatur?num(r.awal):'<span class="muted">belum diatur</span>'}</td>
        <td>${r.diatur?tgl(r.tgl_awal):'-'}</td>
        <td class="n">${num(r.masuk)}</td><td class="n">${num(r.terjual)}</td><td class="n">${num(r.sample)}</td>
        <td class="n ${r.sisa<0?'minus':''}">${num(r.sisa)}</td></tr>`;
    });
    $('#st-tabel').innerHTML=data.length?`<table><thead><tr><th>Produk</th><th>Stok awal (botol)</th><th>Per tanggal</th>
      <th>Masuk</th><th>Terjual</th><th>Sample</th><th>Sisa (botol)</th></tr></thead><tbody>${html}</tbody></table>`
      :'<div class="empty">Belum ada toko / produk aktif.</div>';
    $('#st-riw').innerHTML=m.rows.length?`<table><thead><tr><th>Tanggal</th><th>Jam</th><th>Toko</th><th>Produk</th>
      <th>Qty</th><th>Satuan</th><th>Botol</th><th>Diinput</th><th>Catatan</th><th></th></tr></thead>
      <tbody>${m.rows.map(e=>`<tr><td>${tgl(e.tanggal)}</td><td>${jam(e.waktu)}</td><td>${esc(e.toko)}</td>
        <td>${esc(e.produk)}</td><td class="n">${num(e.qty)}</td><td>${e.satuan}</td><td class="n">${num(e.botol_setara)}</td>
        <td>${esc(e.spg)}</td><td>${esc(e.catatan||'')}</td>
        <td><button class="btn sm danger" data-hapusm="${e.uid}">Hapus</button></td></tr>`).join('')}</tbody></table>`
      :'<div class="empty">Belum ada stok masuk.</div>';
  });
  const atur=tuid=>{
    const baris=data.filter(r=>r.toko_uid===tuid);
    if(!baris.length)return;
    const tglAwal=baris.find(r=>r.diatur)?.tgl_awal||hariIni();
    const w=document.createElement('div');
    w.innerHTML=`<div class="note info">Isi jumlah stok awal tiap produk di <b>${esc(baris[0].toko)}</b>.
      Kosongkan baris yang tidak ingin diubah. Penjualan &amp; stok masuk mulai tanggal di bawah ikut dihitung ke sisa stok.</div>
      <label class="f">Tanggal stok awal</label><input type="date" id="sa-tgl" value="${tglAwal}">
      <div class="gap"></div>
      <div class="tbl"><table><thead><tr><th>Produk</th><th>Jumlah</th><th>Satuan</th></tr></thead>
      <tbody>${baris.map(r=>`<tr data-p="${r.produk_uid}"><td>${esc(r.produk)}</td>
        <td><input class="qa" inputmode="decimal" value="${r.diatur?r.awal:''}" placeholder="0"></td>
        <td><select class="sa"><option value="BOTOL">BOTOL</option><option value="DUS">DUS</option></select></td></tr>`).join('')}</tbody></table></div>`;
    buka('Atur Stok Awal',w,[{teks:'Batal'},{teks:'Simpan',cls:'primary',klik:async()=>{
      const items=$$('tr[data-p]',w).map(tr=>({produk_uid:tr.dataset.p,qty:$('.qa',tr).value,satuan:$('.sa',tr).value}));
      const r=await api('/api/stok/awal',{method:'PUT',body:{toko_uid:tuid,tanggal:$('#sa-tgl',w).value,items}});
      toast(r.jumlah+' produk tersimpan');muat();
    }}]);
  };
  $('#st-toko').onchange=muat;
  el.addEventListener('click',jaga(async e=>{
    const a=e.target.closest('[data-atur]');
    if(a)return atur(a.dataset.atur);
    const h=e.target.closest('[data-hapusm]');
    if(h){
      if(!await konfirmasi('Hapus stok masuk','Hapus data stok masuk ini?','Hapus'))return;
      await api('/api/stok/masuk/'+h.dataset.hapusm,{method:'DELETE'});toast('Dihapus');muat();
    }
  }));
  muat();
}

async function mPermintaanMaster(el){
  el=resetEl(el);
  el.innerHTML=`<div class="card"><h2>Permintaan dari Kepala Depo</h2></div><div id="pm-list" class="card">Memuat…</div>`;
  const muat=jaga(async()=>{
    const list=await api('/api/permintaan');
    $('#pm-list').innerHTML=list.length?list.map(r=>{
      const data=JSON.parse(r.data||'{}');
      return`<div class="card compact">
        <div class="row">
          <div class="flex1">
            <b>${esc({tambah_toko:'Tambah Toko',tambah_produk:'Tambah Produk',tambah_spg:'Tambah SPG'}[r.tipe]||r.tipe)}</b>
            <span class="badge ${r.status==='approved'?'b-ok':r.status==='rejected'?'b-err':'b-sample'} ml8">${r.status}</span><br>
            <small class="muted">${esc(r.peminta_nama||'')} (${esc(r.peminta_wilayah||'')}) · ${tgl(r.waktu)}</small><br>
            <small>${esc(data.keterangan||'')}</small>
            ${r.catatan_master?`<br><small class="muted">Catatan: ${esc(r.catatan_master)}</small>`:''}
          </div>
          ${r.status==='pending'?`<div class="row-acts">
            <button class="btn sm ok" data-apr="${r.uid}">Setujui</button>
            <button class="btn sm danger" data-rej="${r.uid}">Tolak</button>
          </div>`:''}
        </div></div>`;
    }).join(''):'<div class="empty">Tidak ada permintaan.</div>';
  });
  muat();
  el.addEventListener('click',jaga(async e=>{
    const apr=e.target.closest('[data-apr]');
    const rej=e.target.closest('[data-rej]');
    if(apr){
      const w=document.createElement('div');
      w.innerHTML=`<label class="f">Catatan (opsional)</label><textarea id="cat-apr" rows="3" class="rsz"></textarea>`;
      buka('Setujui Permintaan',w,[{teks:'Batal'},{teks:'Setujui',cls:'ok',klik:async()=>{
        await api('/api/permintaan/'+apr.dataset.apr,{method:'PUT',body:{status:'approved',catatan:$('#cat-apr',w).value}});
        toast('Permintaan disetujui');muat();
      }}]);
    }
    if(rej){
      const w=document.createElement('div');
      w.innerHTML=`<label class="f">Alasan penolakan</label><textarea id="cat-rej" rows="3" class="rsz"></textarea>`;
      buka('Tolak Permintaan',w,[{teks:'Batal'},{teks:'Tolak',cls:'danger',klik:async()=>{
        await api('/api/permintaan/'+rej.dataset.rej,{method:'PUT',body:{status:'rejected',catatan:$('#cat-rej',w).value}});
        toast('Permintaan ditolak');muat();
      }}]);
    }
  }));
}

async function mSpg(el){
  el=resetEl(el);
  const [users,toko]=await Promise.all([api('/api/pengguna'),api('/api/toko')]);
  el.innerHTML=`<div class="card"><div class="row">
    <h2>Akun pengguna</h2>
    <button class="btn primary" id="u-baru">+ Akun baru</button></div></div>
    <div class="tbl"><table><thead><tr><th>Nama</th><th>Username</th><th>Role</th><th>Wilayah</th>
      <th>Sales</th><th>Toko</th><th>Entri</th><th>Status</th><th>Terakhir</th><th>Aksi</th></tr></thead>
    <tbody>${users.map(u=>`<tr>
      <td><b>${esc(u.nama)}</b></td><td><code>${esc(u.username)}</code></td>
      <td>${u.role==='master'?'<span class="badge b-jual">MASTER</span>':u.role==='kepala_depo'?'<span class="badge b-depo">KEPALA DEPO</span>':'SPG'}</td>
      <td>${esc(u.wilayah||'-')}</td>
      <td>${u.role==='spg'?(esc(u.sales_efektif||'-')+(!u.sales&&u.sales_otomatis?' <span class="badge b-jual">otomatis</span>':'')):'-'}</td>
      <td>${u.role==='spg'?`<button class="btn sm" data-toko="${u.uid}">${u.jumlah_toko} toko</button>`:'-'}</td>
      <td class="n">${num(u.jumlah_entri)}</td>
      <td>${!u.aktif?'<span class="badge b-err">nonaktif</span>':u.kunci_sampai>new Date().toISOString()?'<span class="badge b-err">terkunci</span>':'<span class="badge b-ok">aktif</span>'}
          ${u.totp_aktif?' <span class="badge b-ok">2FA</span>':''}${u.harus_ganti?' <span class="badge b-sample">pw baru</span>':''}</td>
      <td>${u.terakhir_login?tgl(u.terakhir_login)+' '+jam(u.terakhir_login):'-'}</td>
      <td class="nobr">
        <button class="btn sm" data-ubah="${u.uid}">Ubah</button>
        <button class="btn sm" data-reset="${u.uid}">Reset pw</button>
        ${u.kunci_sampai>new Date().toISOString()?`<button class="btn sm" data-buka="${u.uid}">Buka</button>`:''}
        <button class="btn sm danger" data-hapus="${u.uid}">Hapus</button>
      </td></tr>`).join('')}</tbody></table></div>`;

  const form=(u=null)=>{
    const w=document.createElement('div');
    w.innerHTML=`<div class="form">
      <div class="full"><label class="f">Nama lengkap *</label><input name="nama" value="${esc(u?.nama||'')}"></div>
      <div><label class="f">Username</label><input name="username" value="${esc(u?.username||'')}" placeholder="otomatis dari nama"></div>
      <div><label class="f">Role</label><select name="role">
        <option value="spg" ${u?.role!=='master'&&u?.role!=='kepala_depo'?'selected':''}>SPG</option>
        <option value="kepala_depo" ${u?.role==='kepala_depo'?'selected':''}>Kepala Depo</option>
        <option value="master" ${u?.role==='master'?'selected':''}>Master</option></select></div>
      <div><label class="f">Wilayah</label><input name="wilayah" value="${esc(u?.wilayah||'')}" placeholder="nama wilayah / depo"></div>
      <div><label class="f">Nama sales (opsional)</label><input name="sales" value="${esc(u?.sales||'')}" placeholder="kosong = otomatis dari toko"></div>
      <div><label class="f">Telepon</label><input name="telepon" value="${esc(u?.telepon||'')}"></div>
      <div><label class="f">Status</label><select name="aktif">
        <option value="1" ${u?.aktif!==0?'selected':''}>Aktif</option>
        <option value="0" ${u?.aktif===0?'selected':''}>Nonaktif</option></select></div>
      <div class="full"><label class="f">Catatan</label><input name="catatan" value="${esc(u?.catatan||'')}"></div>
      <div class="full"><label class="f">Toko yang ditugaskan (untuk SPG)</label>
        <div class="checklist">${toko.map(t=>`<label><input type="checkbox" value="${t.uid}"
          ${u?.toko?.some(x=>x.uid===t.uid)?'checked':''}>${esc(t.nama)} <span class="muted">${esc(t.wilayah||'')}${t.sales?' · sales '+esc(t.sales):''}</span></label>`).join('')}</div>
        <p class="muted kecil">Bila kolom sales dikosongkan, nama sales SPG otomatis mengikuti sales dari toko yang dipilih.</p></div>
    </div>`;
    buka(u?'Ubah Akun':'Akun Baru',w,[{teks:'Batal'},{teks:'Simpan',cls:'primary',klik:async()=>{
      const body=Object.fromEntries($$('[name]',w).map(i=>[i.name,i.value]));
      body.aktif=body.aktif==='1';
      body.toko_uids=$$('.checklist input:checked',w).map(i=>i.value);
      const r=u?await api('/api/pengguna/'+u.uid,{method:'PUT',body}):await api('/api/pengguna',{method:'POST',body});
      if(r.password){
        buka('Akun dibuat',`<div class="note ok">Catat & berikan ke pengguna. Hanya ditampilkan sekali.</div>
          <p>Username: <code>${esc(r.username)}</code></p><p>Password: <code class="kode-lg">${esc(r.password)}</code></p>`,
          [{teks:'Sudah dicatat',cls:'primary'}]);
      }else toast('Tersimpan');
      mSpg(el);return!r.password;
    }}]);
  };
  $('#u-baru').onclick=()=>form();
  el.addEventListener('click',jaga(async e=>{
    const b=e.target.closest('button');if(!b)return;
    const u=users.find(x=>x.uid===(b.dataset.ubah||b.dataset.reset||b.dataset.hapus||b.dataset.buka||b.dataset.toko));
    if(b.dataset.ubah||b.dataset.toko)form(u);
    if(b.dataset.buka){await api(`/api/pengguna/${u.uid}/buka`,{method:'POST',body:{}});toast('Kunci dibuka');mSpg(el);}
    if(b.dataset.reset){
      if(!await konfirmasi('Reset password',`Reset password <b>${esc(u.nama)}</b>?`,'Reset',false))return;
      const r=await api(`/api/pengguna/${u.uid}/reset`,{method:'POST',body:{}});
      buka('Password baru',`<div class="note ok">Berikan ke ${esc(u.nama)}.</div>
        <p>Username: <code>${esc(r.username)}</code></p><p>Password: <code class="kode-lg">${esc(r.password)}</code></p>`,
        [{teks:'Sudah dicatat',cls:'primary'}]);
      mSpg(el);
    }
    if(b.dataset.hapus){
      if(!await konfirmasi('Hapus akun',`Hapus akun <b>${esc(u.nama)}</b>?`,'Hapus'))return;
      const r=await api('/api/pengguna/'+u.uid,{method:'DELETE'});
      toast(r.dinonaktifkan?'Akun dinonaktifkan':'Akun dihapus');mSpg(el);
    }
  }));
}

async function mToko(el){
  el=resetEl(el);
  const [toko,users]=await Promise.all([api('/api/toko?aktif=0'),api('/api/pengguna')]);
  const spg=users.filter(u=>u.role==='spg');
  el.innerHTML=`<div class="card"><div class="row">
    <h2>Daftar toko</h2>
    <input id="t-cari" placeholder="Cari toko / sales…" class="max220">
    <button class="btn primary" id="t-baru">+ Toko baru</button></div></div>
    <div class="tbl" id="t-tabel"></div>`;
  const gambar=()=>{
    const q=$('#t-cari').value.trim().toUpperCase();
    const list=toko.filter(t=>!q||(t.nama+' '+(t.wilayah||'')+' '+(t.sales||'')).toUpperCase().includes(q));
    $('#t-tabel').innerHTML=`<table><thead><tr><th>Nama</th><th>Wilayah</th><th>Alamat</th><th>Sales</th>
      <th>SPG</th><th>Entri</th><th>Status</th><th></th></tr></thead>
      <tbody>${list.map(t=>`<tr><td><b>${esc(t.nama)}</b></td><td>${esc(t.wilayah||'')}</td>
        <td>${esc(t.alamat||'')}</td><td>${esc(t.sales||'-')}</td><td>${esc(t.spg||'-')}</td><td class="n">${num(t.jumlah_entri)}</td>
        <td>${t.aktif?'<span class="badge b-ok">aktif</span>':'<span class="badge b-err">nonaktif</span>'}</td>
        <td><button class="btn sm" data-ubah="${t.uid}">Ubah</button>
            <button class="btn sm danger" data-hapus="${t.uid}">Hapus</button></td></tr>`).join('')
        ||'<tr><td colspan="8" class="empty">Belum ada toko.</td></tr>'}</tbody></table>`;
  };
  const form=(t=null)=>{
    const w=document.createElement('div');
    w.innerHTML=`<div class="form">
      <div class="full"><label class="f">Nama toko *</label><input name="nama" value="${esc(t?.nama||'')}"></div>
      <div><label class="f">Wilayah</label><input name="wilayah" value="${esc(t?.wilayah||'')}"></div>
      <div><label class="f">Status</label><select name="aktif">
        <option value="1" ${t?.aktif!==0?'selected':''}>Aktif</option>
        <option value="0" ${t?.aktif===0?'selected':''}>Nonaktif</option></select></div>
      <div class="full"><label class="f">Alamat</label><input name="alamat" value="${esc(t?.alamat||'')}"></div>
      <div class="full"><label class="f">Nama sales (opsional)</label><input name="sales" value="${esc(t?.sales||'')}" placeholder="boleh dikosongkan">
        <p class="muted kecil">SPG yang ditempatkan di toko ini otomatis menampilkan nama sales ini.</p></div>
      <div class="full"><label class="f">Catatan</label><input name="catatan" value="${esc(t?.catatan||'')}"></div>
      <div class="full"><label class="f">SPG yang bertugas</label><div class="checklist">
        ${spg.map(u=>`<label><input type="checkbox" value="${u.uid}"
          ${u.toko?.some(x=>x.uid===t?.uid)?'checked':''}>${esc(u.nama)}</label>`).join('')
          ||'<span class="muted">Belum ada akun SPG.</span>'}</div></div></div>`;
    buka(t?'Ubah Toko':'Toko Baru',w,[{teks:'Batal'},{teks:'Simpan',cls:'primary',klik:async()=>{
      const body=Object.fromEntries($$('[name]',w).map(i=>[i.name,i.value]));
      body.aktif=body.aktif==='1';
      body.spg_uids=$$('.checklist input:checked',w).map(i=>i.value);
      t?await api('/api/toko/'+t.uid,{method:'PUT',body}):await api('/api/toko',{method:'POST',body});
      toast('Tersimpan');mToko(el);
    }}]);
  };
  $('#t-baru').onclick=()=>form();
  $('#t-cari').oninput=gambar;
  el.addEventListener('click',jaga(async e=>{
    const b=e.target.closest('button');if(!b)return;
    const t=toko.find(x=>x.uid===(b.dataset.ubah||b.dataset.hapus));
    if(b.dataset.ubah)form(t);
    if(b.dataset.hapus){
      if(!await konfirmasi('Hapus toko',`Hapus <b>${esc(t.nama)}</b>?`,'Hapus'))return;
      const r=await api('/api/toko/'+t.uid,{method:'DELETE'});
      toast(r.dinonaktifkan?'Toko dinonaktifkan':'Toko dihapus');mToko(el);
    }
  }));
  gambar();
}

async function mProduk(el){
  el=resetEl(el);
  const produk=await api('/api/produk?semua=1');
  el.innerHTML=`<div class="card"><div class="row">
    <h2>Daftar produk & harga</h2>
    <button class="btn primary" id="p-baru">+ Produk baru</button></div></div>
    <div class="tbl"><table><thead><tr><th>Urut</th><th>Kode</th><th>Nama</th>
      <th>Harga/botol</th><th>Harga/dus</th><th>Isi/dus</th><th>Entri</th><th>Status</th><th></th></tr></thead>
      <tbody>${produk.map(p=>`<tr><td class="n">${p.urut}</td><td><code>${esc(p.kode)}</code></td>
        <td><b>${esc(p.nama)}</b></td><td class="n">${num(p.harga_botol)}</td>
        <td class="n">${num(p.harga_dus)}</td><td class="n">${p.isi_dus}</td>
        <td class="n">${num(p.jumlah_entri)}</td>
        <td>${p.aktif?'<span class="badge b-ok">aktif</span>':'<span class="badge b-err">nonaktif</span>'}</td>
        <td><button class="btn sm" data-ubah="${p.uid}">Ubah</button>
            <button class="btn sm danger" data-hapus="${p.uid}">Hapus</button></td></tr>`).join('')
      ||'<tr><td colspan="9" class="empty">Belum ada produk.</td></tr>'}</tbody></table></div>`;
  const form=(p=null)=>{
    const w=document.createElement('div');
    w.innerHTML=`<div class="form">
      <div><label class="f">Kode *</label><input name="kode" value="${esc(p?.kode||'')}"></div>
      <div class="full"><label class="f">Nama produk *</label><input name="nama" value="${esc(p?.nama||'')}"></div>
      <div><label class="f">Harga per botol</label><input name="harga_botol" inputmode="numeric" value="${p?.harga_botol||''}"></div>
      <div><label class="f">Harga per dus</label><input name="harga_dus" inputmode="numeric" value="${p?.harga_dus||''}"></div>
      <div><label class="f">Isi per dus</label><input name="isi_dus" inputmode="numeric" value="${p?.isi_dus??12}"></div>
      <div><label class="f">Urutan</label><input name="urut" inputmode="numeric" value="${p?.urut??0}"></div>
      <div><label class="f">Status</label><select name="aktif">
        <option value="1" ${p?.aktif!==0?'selected':''}>Aktif</option>
        <option value="0" ${p?.aktif===0?'selected':''}>Nonaktif</option></select></div></div>`;
    buka(p?'Ubah Produk':'Produk Baru',w,[{teks:'Batal'},{teks:'Simpan',cls:'primary',klik:async()=>{
      const body=Object.fromEntries($$('[name]',w).map(i=>[i.name,i.value]));
      body.aktif=body.aktif==='1';
      p?await api('/api/produk/'+p.uid,{method:'PUT',body}):await api('/api/produk',{method:'POST',body});
      toast('Tersimpan');mProduk(el);
    }}]);
  };
  $('#p-baru').onclick=()=>form();
  el.addEventListener('click',jaga(async e=>{
    const b=e.target.closest('button');if(!b)return;
    const p=produk.find(x=>x.uid===(b.dataset.ubah||b.dataset.hapus));
    if(b.dataset.ubah)form(p);
    if(b.dataset.hapus){
      if(!await konfirmasi('Hapus produk',`Hapus <b>${esc(p.nama)}</b>?`,'Hapus'))return;
      const r=await api('/api/produk/'+p.uid,{method:'DELETE'});
      toast(r.dinonaktifkan?'Produk dinonaktifkan':'Produk dihapus');mProduk(el);
    }
  }));
}

async function mBackup(el){
  el=resetEl(el);
  const daftar=await api('/api/backup');
  el.innerHTML=`<div class="card"><h2>Simpan salinan data (disarankan tiap hari)</h2>
    <div class="note info">File backup berisi <b>semua data</b> (akun, toko, penjualan, absensi, stok). Simpan di Google Drive / flashdisk, jangan dibagikan ke orang lain.</div>
    <button class="btn primary big block" id="b-unduh">⬇ Download Backup Database</button></div>
    <div class="card"><h2>Pulihkan dari file backup</h2>
    <div class="note warn">Semua data sekarang akan DIGANTI dengan isi file backup. Sistem otomatis membuat salinan pengaman dulu. Setelah berhasil, semua pengguna perlu login ulang.</div>
    <label class="f">Pilih file backup (.db)</label><input type="file" id="b-file" accept=".db">
    <div class="gap-s"></div><label class="f">Password Anda (konfirmasi)</label><input type="password" id="b-pw" autocomplete="current-password">
    <div class="gap"></div><button class="btn danger block" id="b-pulih">Pulihkan Data</button></div>
    <div class="card"><h2>Salinan otomatis di server (30 hari terakhir)</h2><div class="tbl pendek"><table>
      <thead><tr><th>File</th><th>Waktu</th><th>Ukuran</th></tr></thead><tbody>${daftar.map(f=>`<tr><td>${esc(f.nama)}</td>
      <td>${tgl(f.waktu)} ${jam(f.waktu)}</td><td class="n">${num(f.ukuran/1024)} KB</td></tr>`).join('')||'<tr><td colspan="3" class="empty">Belum ada.</td></tr>'}</tbody></table></div>
      <p class="muted kecil">Salinan ini ada di server yang sama. Tetap download backup ke komputer Anda secara rutin.</p></div>`;
  $('#b-unduh').onclick=()=>{unduh('/export/backup');toast('Menyiapkan file backup…');};
  $('#b-pulih').onclick=jaga(async()=>{
    const f=$('#b-file').files[0];
    if(!f)return toast('Pilih file backup dulu','err');
    if(!$('#b-pw').value)return toast('Isi password dulu','err');
    if(!await konfirmasi('Pulihkan data',`Ganti semua data dengan isi <b>${esc(f.name)}</b>?`,'Ya, pulihkan'))return;
    const res=await fetch('/api/restore',{method:'POST',credentials:'same-origin',body:f,
      headers:{'X-CSRF-Token':ME.csrf,'X-Password':encodeURIComponent($('#b-pw').value),'Content-Type':'application/octet-stream'}});
    const d=await res.json().catch(()=>({}));
    if(!res.ok)return toast(d.error||'Gagal memulihkan','err');
    ME=null;tampilLogin('Data berhasil dipulihkan. Silakan masuk lagi.');
  });
}

async function mLog(el){
  el=resetEl(el);
  el.innerHTML=`<div class="card"><div class="form">
    <div><label class="f">Dari</label><input type="date" id="g-dari"></div>
    <div><label class="f">Sampai</label><input type="date" id="g-sampai"></div>
    <div><label class="f">Aktivitas</label><select id="g-aksi"><option value="">Semua</option></select></div>
    <div><label class="f">Cari</label><input id="g-q" placeholder="username / IP / detail"></div>
    <div class="full"><button class="btn primary" id="g-go">Tampilkan</button></div></div></div>
    <div class="tbl" id="g-tabel"></div>`;
  let pertama=true;
  const load=jaga(async()=>{
    const d=await api('/api/log?'+qs({dari:$('#g-dari').value,sampai:$('#g-sampai').value,aksi:$('#g-aksi').value,q:$('#g-q').value}));
    if(pertama){$('#g-aksi').innerHTML+= d.aksi.map(a=>`<option value="${a}">${a}</option>`).join('');pertama=false;}
    $('#g-tabel').innerHTML=d.rows.length?`<table><thead><tr><th>Waktu</th><th>Pengguna</th><th>Role</th>
      <th>Aktivitas</th><th>Detail</th><th>IP</th><th>Perangkat</th></tr></thead>
      <tbody>${d.rows.map(l=>`<tr><td>${tgl(l.waktu)} ${jam(l.waktu)}</td><td>${esc(l.username)}</td>
        <td>${esc(l.role)}</td><td><span class="badge ${/GAGAL|HAPUS|KUNCI/.test(l.aksi)?'b-err':'b-jual'}">${esc(l.aksi)}</span></td>
        <td>${esc(l.detail)}</td><td>${esc(l.ip)}</td><td>${esc((l.perangkat||'').slice(0,45))}</td></tr>`).join('')}</tbody></table>`
    :'<div class="empty">Tidak ada log.</div>';
  });
  $('#g-go').onclick=load;$('#g-q').addEventListener('keydown',e=>e.key==='Enter'&&load());
  $('#g-aksi').onchange=load;load();
}

// ---- IKON, NAVIGASI & JUDUL HALAMAN ----
const IKON={
  dashboard:'<path d="M3 3h7v9H3zM14 3h7v5h-7zM14 12h7v9h-7zM3 16h7v5H3z"/>',
  penjualan:'<circle cx="9" cy="21" r="1"/><circle cx="20" cy="21" r="1"/><path d="M1 1h4l2.7 13.4a2 2 0 0 0 2 1.6h9.7a2 2 0 0 0 2-1.6L23 6H6"/>',
  laporan:'<path d="M18 20V10M12 20V4M6 20v-6"/>',
  absen:'<rect x="3" y="4" width="18" height="18" rx="2"/><path d="M16 2v4M8 2v4M3 10h18M9 16l2 2 4-4"/>',
  stok:'<path d="M21 16V8a2 2 0 0 0-1-1.7l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.7l7 4a2 2 0 0 0 2 0l7-4a2 2 0 0 0 1-1.7z"/><path d="M3.3 7L12 12l8.7-5M12 22V12"/>',
  spg:'<path d="M17 21v-2a4 4 0 0 0-4-4H5a4 4 0 0 0-4 4v2"/><circle cx="9" cy="7" r="4"/><path d="M23 21v-2a4 4 0 0 0-3-3.9M16 3.1a4 4 0 0 1 0 7.8"/>',
  toko:'<path d="M3 9l1-5h16l1 5M3 9a3 3 0 0 0 6 0 3 3 0 0 0 6 0 3 3 0 0 0 6 0M5 21V12m14 9V12M3 21h18"/>',
  produk:'<path d="M20.6 13.4l-7.2 7.2a2 2 0 0 1-2.8 0L2 12V2h10l8.6 8.6a2 2 0 0 1 0 2.8z"/><circle cx="7" cy="7" r="1.5"/>',
  permintaan:'<path d="M22 12h-6l-2 3h-4l-2-3H2"/><path d="M5.5 5.1L2 12v6a2 2 0 0 0 2 2h16a2 2 0 0 0 2-2v-6l-3.5-6.9A2 2 0 0 0 16.8 4H7.2a2 2 0 0 0-1.7 1.1z"/>',
  backup:'<ellipse cx="12" cy="5" rx="9" ry="3"/><path d="M21 12c0 1.7-4 3-9 3s-9-1.3-9-3M3 5v14c0 1.7 4 3 9 3s9-1.3 9-3V5"/>',
  log:'<path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/>'};
const svgIkon=k=>`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${IKON[k]||''}</svg>`;
function buatNav(tabs,aktif,onPilih){
  const nav=$('#tabs');nav.style.display='flex';
  nav.innerHTML=tabs.map(([k,l,g])=>(g?`<div class="nav-label">${esc(g)}</div>`:'')+
    `<button data-t="${k}" class="${k===aktif?'active':''}">${svgIkon(k)}<span>${esc(l)}</span></button>`).join('');
  nav.onclick=e=>{const b=e.target.closest('[data-t]');if(b)onPilih(b.dataset.t);};
}
const HALAMAN={
  dashboard:['Dashboard','Ringkasan penjualan dan aktivitas hari ini'],
  penjualan:['Penjualan','Semua entri penjualan dari SPG'],
  laporan:['Laporan','Rekap per SPG, toko, sales, produk dan tanggal'],
  absen:['Absensi','Kehadiran harian SPG'],
  stok:['Stok','Stok awal, stok masuk dan sisa per toko'],
  spg:['Akun Pengguna','Master, kepala depo dan SPG'],
  toko:['Toko','Daftar toko, sales dan penugasan SPG'],
  produk:['Produk & Harga','Harga botol, harga dus dan isi per dus'],
  permintaan:['Permintaan','Permintaan tambah data ke master'],
  backup:['Backup Data','Simpan dan pulihkan database'],
  log:['Log Keamanan','Jejak aktivitas semua pengguna']};
function setHalaman(t){
  const ph=$('#page-head');
  if(!document.body.classList.contains('side')){ph.style.display='none';return;}
  const [j,p]=HALAMAN[t]||[t,''];
  $('#pj').textContent=j;$('#pp').textContent=p;$('#pd').textContent=tgl(hariIni());
  ph.style.display='flex';
}
function grafikTren(tren){
  const peta=Object.fromEntries((tren||[]).map(t=>[t.tanggal,t]));
  const data=[];for(let i=13;i>=0;i--){const h=tglMundur(i);data.push({h,total:peta[h]?.total||0,botol:peta[h]?.botol||0});}
  const maks=Math.max(1,...data.map(d=>d.total));
  const W=720,H=190,kiri=8,atas=22,bawah=28,tinggi=H-atas-bawah,bw=(W-kiri*2)/data.length;
  const garis=[0,.5,1].map(f=>{const y=atas+tinggi*(1-f);return`<line class="gl" x1="${kiri}" x2="${W-kiri}" y1="${y}" y2="${y}"/>`;}).join('');
  const batang=data.map((d,i)=>{
    const hgt=Math.max(Math.round(tinggi*d.total/maks),d.total?3:2),x=kiri+i*bw+bw*.18,y=atas+tinggi-hgt,w=bw*.64;
    const nilai=d.total?`<text class="val" x="${(x+w/2).toFixed(1)}" y="${y-5}" text-anchor="middle">${d.total>=1e6?(d.total/1e6).toFixed(1).replace('.0','')+'jt':d.total>=1e3?Math.round(d.total/1e3)+'rb':d.total}</text>`:'';
    return`<g><title>${tgl(d.h)}: ${rp(d.total)} · ${num(d.botol)} botol</title>
      <rect class="bar${d.h===hariIni()?' hari':''}" x="${x.toFixed(1)}" y="${y}" width="${w.toFixed(1)}" height="${hgt}" rx="6"/>${nilai}
      <text class="axis" x="${(x+w/2).toFixed(1)}" y="${H-8}" text-anchor="middle">${+d.h.slice(8)}</text></g>`;}).join('');
  return`<svg class="grafik" viewBox="0 0 ${W} ${H}" role="img" aria-label="Grafik penjualan 14 hari terakhir">
    <defs><linearGradient id="gbar" x1="0" y1="0" x2="0" y2="1"><stop offset="0" stop-color="#2dd4bf"/><stop offset="1" stop-color="#0d9488"/></linearGradient></defs>
    ${garis}${batang}</svg>`;
}

// ---- LIHAT / SEMBUNYIKAN PASSWORD (otomatis untuk semua kolom password) ----
const IKON_MATA=`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"/><circle cx="12" cy="12" r="3"/></svg>`;
const IKON_MATA_CORET=`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24"/><line x1="1" y1="1" x2="23" y2="23"/></svg>`;
function pasangMata(inp){
  if(inp.dataset.mata)return;
  inp.dataset.mata='1';
  const wrap=document.createElement('div');wrap.className='pw-wrap';
  inp.replaceWith(wrap);wrap.append(inp);
  const b=document.createElement('button');
  b.type='button';b.className='pw-mata';b.tabIndex=-1;
  b.setAttribute('aria-label','Tampilkan password');b.innerHTML=IKON_MATA;
  // mousedown dicegah supaya kolom tidak kehilangan fokus saat tombol diklik
  b.addEventListener('mousedown',e=>e.preventDefault());
  b.onclick=()=>{
    const sembunyi=inp.type==='password';
    inp.type=sembunyi?'text':'password';
    b.innerHTML=sembunyi?IKON_MATA_CORET:IKON_MATA;
    b.setAttribute('aria-label',sembunyi?'Sembunyikan password':'Tampilkan password');
    inp.focus();
  };
  wrap.append(b);
}
const cariPassword=()=>$$('input[type=password]').forEach(pasangMata);
new MutationObserver(cariPassword).observe(document.body,{childList:true,subtree:true});
cariPassword();

// ---- START ----
(async()=>{
  try{
    const me=await api('/api/me');
    if(me.login){ME=me;await mulai();}else tampilLogin();
  }catch{tampilLogin();}
})();
</script>
</body>
</html>
'''

def restore_dari_file():
    """Bila ada file RESTORE.db di folder data, database dipulihkan dari file itu saat aplikasi start.
    Berguna bila web tidak bisa dibuka: upload RESTORE.db lewat Railway CLI lalu restart."""
    f = DATA_DIR / "RESTORE.db"
    if not f.exists(): return
    try:
        t = sqlite3.connect(f)
        try:
            ok = t.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
            tabel = {r[0] for r in t.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            if (not ok or not {"pengguna","toko","produk","penjualan"} <= tabel
                    or not t.execute("SELECT 1 FROM pengguna WHERE role='master' AND aktif=1").fetchone()):
                print("RESTORE.db TIDAK VALID - diabaikan"); t.close()
                f.replace(DATA_DIR / "RESTORE_GAGAL.db"); return
            BACKUP_DIR.mkdir(parents=True, exist_ok=True)
            if DB_PATH.exists():
                a_, b_ = sqlite3.connect(DB_PATH), sqlite3.connect(BACKUP_DIR / f"sebelum_restore_{now():%Y%m%d_%H%M%S}.db")
                a_.backup(b_); b_.close(); a_.close()
            cur = sqlite3.connect(DB_PATH); t.backup(cur); cur.close()
        finally:
            try: t.close()
            except Exception: pass
        f.replace(DATA_DIR / f"RESTORE_selesai_{now():%Y%m%d_%H%M%S}.db")
        print("DATABASE DIPULIHKAN dari RESTORE.db")
    except Exception as e:
        print("Gagal restore dari RESTORE.db:", e)

def _loop_backup():
    while True:
        time.sleep(3600)
        try: backup_harian()
        except Exception as e: print("backup gagal:", e)
        try:
            with db() as conn:     # rapikan log lama & sesi kedaluwarsa
                conn.execute("DELETE FROM log WHERE waktu < ?",((now()-timedelta(days=400)).isoformat(timespec="seconds"),))
                conn.execute("DELETE FROM sesi WHERE kedaluwarsa < ?",(now_iso(),))
        except Exception as e: print("rapikan gagal:", e)

def main():
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    restore_dari_file()
    init_db()
    try: os.chmod(DB_PATH, 0o600)
    except OSError: pass
    backup_harian()
    threading.Thread(target=_loop_backup, daemon=True).start()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    server.daemon_threads = True
    print("="*64)
    print(f"  {APP_NAME} v{APP_VERSION}")
    print(f"  Alamat : http://{HOST}:{PORT}")
    print(f"  Data   : {DB_PATH}")
    print(f"  Mode   : {'DEV' if DEV_MODE else 'PRODUKSI'}{' | proxy' if TRUST_PROXY else ''}")
    print("="*64)
    try: server.serve_forever()
    except KeyboardInterrupt: print("\nBerhenti.")
    finally: server.server_close()

if __name__ == "__main__":
    main()
