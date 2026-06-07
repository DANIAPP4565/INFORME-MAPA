#!/usr/bin/env python3
"""
MAPA Informe Médico – App Streamlit
Dr. Ricardo Daniel Olano | Cardiólogo – IPENSA La Plata
Versión 6.0 – 2026
"""

# ─────────────────────────────────────────────────────────────────────────────
# IMPORTS
# ─────────────────────────────────────────────────────────────────────────────
import streamlit as st
import pandas as pd
import numpy as np
import pdfplumber
import io, base64, os, re, warnings, hashlib
from datetime import datetime
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from scipy import stats as sp_stats

from reportlab.lib.pagesizes import A4
from reportlab.lib import colors
from reportlab.lib.units import cm, mm
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle,
    Image as RLImage, PageBreak, HRFlowable, KeepTogether, KeepInFrame
)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_CENTER, TA_LEFT, TA_RIGHT, TA_JUSTIFY
from reportlab.pdfgen import canvas as rl_canvas
from reportlab.platypus.flowables import Flowable

warnings.filterwarnings('ignore')

# ─────────────────────────────────────────────────────────────────────────────
# PAGE CONFIG
# ─────────────────────────────────────────────────────────────────────────────
st.set_page_config(
    page_title="MAPA Informe | Dr. Olano",
    page_icon="🫀",
    layout="wide",
    initial_sidebar_state="expanded",
)

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTES
# ─────────────────────────────────────────────────────────────────────────────
THRESHOLDS = {
    '24h':      {'sys': 130, 'dia': 80},
    'diurno':   {'sys': 135, 'dia': 85},
    'nocturno': {'sys': 120, 'dia': 70},
}

OUTLIER = {'PAD_min': 40, 'PAD_max': 130, 'PAS_max': 230, 'PP_max': 80, 'PP_min': 20}

DOCTOR_NAME     = "Ricardo Daniel Olano"
DOCTOR_TITLE    = "Especialista Universitario en Cardiología"
DOCTOR_SUBTITLE = "Cardiólogo Especialista en Hipertensión Arterial y Mecánica Vascular"
DOCTOR_SPEC     = "(Cardiografía de Impedancia, Velocidad de Onda del Pulso, Medición de Presión Central)"
DOCTOR_MP       = "MP: 110957"
INSTITUTION     = "IPENSA – Instituto Privado Clínico Quirúrgico de Diagnóstico y Tratamiento"
INSTITUTION_ADDR = "Calle 59 Nº 434/36 – La Plata (1900)"

PAGE_W, PAGE_H   = A4
MAR_L = MAR_R    = 2 * cm
MAR_T            = 1.5 * cm
MAR_B            = 2 * cm
CONTENT_W        = PAGE_W - MAR_L - MAR_R

# Pediatric thresholds 95th pct (AAP 2017 / ESH 2016) – approximate midpoints
PED_THR = {
    1:(98,54), 2:(101,58), 3:(104,63), 4:(107,66), 5:(108,69),
    6:(111,72), 7:(114,74), 8:(116,76), 9:(119,78), 10:(122,79),
    11:(124,80), 12:(127,82), 13:(130,84), 14:(134,85), 15:(136,86), 16:(138,87),
}

# ─────────────────────────────────────────────────────────────────────────────
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def safe(v, decimals=1, suffix=''):
    if v is None or (isinstance(v, float) and np.isnan(v)):
        return "No disponible"
    try:
        return f"{round(float(v), int(decimals))}{suffix}"
    except Exception:
        return str(v)

def ped_thr(age, sex='M', height_cm=None):
    a = min(max(int(age), 1), 16)
    s, d = PED_THR.get(a, (130, 80))
    if height_cm:
        if height_cm > 170: s += 3; d += 2
        elif height_cm < 130: s -= 3; d -= 2
    if sex == 'F': s -= 2; d -= 1
    return s, d

def time_to_minutes(hora_str):
    try:
        parts = str(hora_str).strip().split(':')
        return int(parts[0]) % 24 * 60 + int(parts[1])
    except:
        return None

def img_to_bytes(path_or_bytesio):
    if path_or_bytesio is None:
        return None
    if isinstance(path_or_bytesio, bytes):
        return path_or_bytesio
    if hasattr(path_or_bytesio, 'read'):
        path_or_bytesio.seek(0)
        return path_or_bytesio.read()
    if isinstance(path_or_bytesio, str) and os.path.exists(path_or_bytesio):
        with open(path_or_bytesio, 'rb') as f:
            return f.read()
    return None

# ─────────────────────────────────────────────────────────────────────────────
# PDF PARSER – multi-strategy (robust)
# ─────────────────────────────────────────────────────────────────────────────
COL_MAP = {
    # Systolic
    'SIS':'PAS','SISTOLICA':'PAS','SISTÓLICA':'PAS','SYS':'PAS','PAS':'PAS',
    'SISTOL':'PAS','SIST':'PAS','S.A.':'PAS','SAP':'PAS','SYSTOLIC':'PAS',
    # Diastolic
    'DIA':'PAD','DIASTOLICA':'PAD','DIASTÓLICA':'PAD','PAD':'PAD','DIAST':'PAD',
    'D.A.':'PAD','DAP':'PAD','DIASTOLIC':'PAD',
    # HR
    'FC':'FC','FREC':'FC','PULSO':'FC','HR':'FC','LPM':'FC','FREQ':'FC',
    'HEART RATE':'FC','FRECUENCIA':'FC','PUL':'FC','BPM':'FC',
    # Time
    'HORA':'hora','TIME':'hora','TIEMPO':'hora','HORAS':'hora','HOUR':'hora',
    # Date
    'FECHA':'fecha','DATE':'fecha',
    # MAP
    'PAM':'PAM','MAP':'PAM','MEAN':'PAM','MEDIA':'PAM',
    # PP
    'PP':'PP','PULSE':'PP','PRESION DE PULSO':'PP','P.P.':'PP',
    # Period
    'PERIODO':'Período','PERIOD':'Período','TIPO':'Período','PER':'Período',
    # Misc
    'COMENTARIO':'motivo','COMMENT':'motivo','NOTAS':'motivo','OBS':'motivo',
    'ESTADO':'motivo','STATUS':'motivo','FLAG':'motivo',
}

def _map_col(col_str):
    u = str(col_str).upper().strip()
    for k, v in COL_MAP.items():
        if u == k or u.startswith(k):
            return v
    for k, v in COL_MAP.items():
        if k in u:
            return v
    return col_str

def _standardize(df):
    df = df.rename(columns={c: _map_col(c) for c in df.columns})
    seen = {}
    rename_dup = {}
    for c in df.columns:
        if c in seen:
            rename_dup[c] = f'{c}_dup{seen[c]}'
            seen[c] += 1
        else:
            seen[c] = 1
    df = df.rename(columns=rename_dup)

    if 'PAS' not in df.columns or 'PAD' not in df.columns:
        return None
    for c in ['PAS','PAD','FC','PAM','PP']:
        if c in df.columns:
            df[c] = pd.to_numeric(df[c], errors='coerce')
    if 'hora' not in df.columns:
        for c in df.columns:
            sample = df[c].dropna().head(5).astype(str)
            if sample.str.match(r'^\d{1,2}:\d{2}').any():
                df = df.rename(columns={c: 'hora'})
                break
    df = df.dropna(subset=['PAS','PAD'])
    df = df[df['PAS'].between(50,280) & df['PAD'].between(20,160)]
    return df if len(df) > 3 else None


def _is_generated_report(text):
    """
    Detecta si el PDF cargado parece ser un informe ya generado por esta app
    y no el PDF original del equipo MAPA.
    """
    if not text:
        return False
    t = text.lower()
    señales_app = [
        "monitoreo ambulatorio de presión arterial (m.a.p.a.)",
        "ricardo daniel olano",
        "conclusión ejecutiva",
        "conclusión médica ampliada",
        "comparación con guías",
    ]
    señales_equipo = [
        "medicaldb",
        "tabla completa",
        "promedios horarios",
        "representación gráfica de presiones",
        "graficas de distribuciones",
        "gráficas de distribuciones",
    ]
    score_app = sum(s in t for s in señales_app)
    score_equipo = sum(s in t for s in señales_equipo)
    return score_app >= 2 and score_equipo == 0


@st.cache_data(show_spinner=False, ttl=3600, max_entries=8)
def parse_mapa_pdf_cached(file_bytes, cache_version="v6.1-cache-ocr"):
    """
    Versión cacheada del parser pesado. Evita re-ejecutar OCR y parsers
    en cada rerun de Streamlit. El cache se invalida automáticamente si
    cambian los bytes del PDF o cache_version.
    """
    return parse_mapa_pdf(io.BytesIO(file_bytes))


def parse_mapa_pdf(pdf_file):
    """
    Importación AUTOMÁTICA desde PDF original del equipo MAPA.
    Lee datos filiatorios, datos del estudio y TODA la tabla completa.
    Nunca usa los promedios/resúmenes del PDF para calcular: solo lecturas crudas.
    """
    raw_text = ""
    ocr_text = ""
    all_tables = []
    diagnostics = []

    # 1) Texto/tablas digitales, si existen
    try:
        pdf_file.seek(0)
        with pdfplumber.open(pdf_file) as pdf:
            pages_text = []
            for p in pdf.pages:
                t = p.extract_text(x_tolerance=2, y_tolerance=3) or ""
                if t:
                    pages_text.append(t)
                for ts in [
                    {},
                    {'vertical_strategy':'lines','horizontal_strategy':'lines'},
                    {'vertical_strategy':'text','horizontal_strategy':'text'},
                ]:
                    try:
                        tbls = p.extract_tables(ts) if ts else p.extract_tables()
                        if tbls:
                            all_tables.extend(tbls)
                            break
                    except Exception:
                        pass
            raw_text = "\n".join(pages_text)
            diagnostics.append(f"Texto digital: {len(raw_text)} caracteres; tablas: {len(all_tables)}")
    except Exception as e:
        diagnostics.append(f"pdfplumber no pudo leer texto/tablas: {e}")

    # 2) OCR automático. Se ejecuta siempre que el texto digital sea insuficiente
    # o cuando no aparezca Tabla Completa.
    need_ocr = (len(raw_text) < 1500) or ("tabla completa" not in raw_text.lower())
    if need_ocr:
        try:
            pdf_file.seek(0)
            ocr_text = _ocr_pdf_pages(pdf_file)
            diagnostics.append(f"OCR: {len(ocr_text)} caracteres")
        except Exception as e:
            diagnostics.append(f"OCR no disponible o falló: {e}")
            ocr_text = ""

    full_text = "\n".join([raw_text, ocr_text]).strip()

    # 3) Prioridad máxima: Tabla Completa del MedicalDB, no promedios horarios ni informe generado.
    # Primero intentar OCR por layout/celdas; luego OCR lineal.
    df = None
    try:
        pdf_file.seek(0)
        df_layout = _ocr_medicaldb_table_layout(pdf_file)
        if df_layout is not None:
            df = df_layout
            diagnostics.append(f"OCR por celdas: {len(df_layout)} lecturas")
    except Exception as e:
        diagnostics.append(f"OCR por celdas no disponible o falló: {e}")

    if df is None or len(df) < 20:
        df = _parse_medicaldb_table_text(full_text)

    # 3.5) Parser ZLogic/MedicalDB 17.7 – formato celdas | y [ con OCR ruidoso
    if df is None or len(df) < 20:
        df_zl = _parse_zlogic_table(full_text)
        if df_zl is not None and len(df_zl) > (len(df) if df is not None else 0):
            df = df_zl
            diagnostics.append(f"ZLogic parser: {len(df_zl)} lecturas")

    # 4) Segunda opción: tablas digitales del PDF original
    if df is None or len(df) < 20:
        df_tbl = _parse_from_tables(all_tables)
        if df_tbl is not None and len(df_tbl) > (len(df) if df is not None else 0):
            df = df_tbl

    # 5) Parser agresivo de texto
    if (df is None or len(df) < 20) and ("resultados – promedios" not in full_text.lower()):
        df2 = _parse_from_text_v2(full_text)
        if df2 is not None and len(df2) > (len(df) if df is not None else 0):
            df = df2

    # 6) _parse_fixed_width – columnas de ancho fijo (faltaba en el pipeline)
    if df is None or len(df) < 20:
        df_fw = _parse_fixed_width(full_text)
        if df_fw is not None and len(df_fw) > (len(df) if df is not None else 0):
            df = df_fw

    # 7) Último recurso: extracción numérica pura, tolera OCR muy ruidoso
    if df is None or len(df) < 10:
        df_np = _parse_numeric_pairs(full_text)
        if df_np is not None and len(df_np) > (len(df) if df is not None else 0):
            df = df_np

    meta = _extract_meta(full_text)

    if df is None or len(df) < 10:
        if _is_generated_report(full_text):
            pac = full_text.split("Paciente:")[1].split("\n")[0].strip() if "Paciente:" in full_text else "no identificado"
            msg = (
                "⚠️ El PDF cargado es un INFORME YA GENERADO por esta app, no el PDF original del equipo MAPA. "
                "Para procesar un nuevo informe, suba el PDF ORIGINAL del equipo MedicalDB 17.7 "
                "(el que contiene la Tabla Completa con las lecturas individuales de presión arterial). "
                f"Paciente detectado en el informe: {pac}"
            )
        else:
            msg = (
                "No se pudo importar una TABLA COMPLETA válida desde el PDF original. "
                "El archivo no contiene lecturas crudas suficientes. "
                "Verifique en Diagnóstico técnico que el OCR contiene filas con hora y valores numéricos. "
                + " | ".join(diagnostics)
            )
        return None, msg, full_text

    # Ordenar por número de fila si existe; si no, preservar orden de lectura.
    if 'nro' in df.columns:
        df = df.sort_values('nro').drop_duplicates('nro', keep='first')
    df = df.reset_index(drop=True)

    # Fecha/hora combinada para gráficos cronológicos
    df = _ensure_datetime_sequence(df, meta)

    return df, meta, full_text


def _ocr_pdf_pages(pdf_file, dpi=200, first_pages=2, last_pages=3):
    """OCR de todas las páginas del PDF con PyMuPDF + Tesseract."""
    try:
        import fitz
        import pytesseract
        from PIL import Image, ImageOps, ImageFilter, ImageEnhance
    except Exception as e:
        raise RuntimeError(
            "Faltan dependencias OCR. En requirements.txt deben estar pymupdf, pillow y pytesseract; "
            "en packages.txt debe estar tesseract-ocr. Error: " + str(e)
        )

    pdf_file.seek(0)
    data = pdf_file.read()
    doc = fitz.open(stream=data, filetype="pdf")
    texts = []
    zoom = dpi / 72.0
    mat = fitz.Matrix(zoom, zoom)

    n_pages = len(doc)
    if first_pages is None and last_pages is None:
        page_indices = list(range(n_pages))
    else:
        page_indices = sorted(set(list(range(min(first_pages or 0, n_pages))) +
                                  list(range(max(0, n_pages - (last_pages or 0)), n_pages))))

    for i in page_indices:
        page = doc[i]
        pix = page.get_pixmap(matrix=mat, alpha=False)
        img = Image.open(io.BytesIO(pix.tobytes("png"))).convert("L")
        img = ImageOps.autocontrast(img, cutoff=2)
        # Mejorar contraste y nitidez para tablas escaneadas.
        img = ImageEnhance.Sharpness(img).enhance(2.0)
        img = ImageEnhance.Contrast(img).enhance(1.5)
        # Probar PSM 6/4/11; elegir el que extraiga más dígitos.
        best_txt = ""
        best_score = -1
        for psm in [6, 4, 11]:
            config = f"--oem 3 --psm {psm}"
            try:
                try:
                    txt = pytesseract.image_to_string(img, lang="spa+eng", config=config)
                except Exception:
                    txt = pytesseract.image_to_string(img, lang="eng", config=config)
                score = len(re.findall(r'\d', txt))
                if score > best_score:
                    best_score = score
                    best_txt = txt
            except Exception:
                pass
        texts.append(f"\n--- OCR_PAGE_{i+1} ---\n{best_txt}")

    return "\n".join(texts)


def _num_clean_token(tok):
    """Corrige errores OCR frecuentes en tokens numéricos."""
    if tok is None:
        return ""
    s = str(tok)
    s = s.replace("↑", "").replace("]", "").replace("[", "").replace("|", "")
    s = s.replace("l", "1").replace("I", "1").replace("O", "0").replace("o", "0")
    s = s.replace("S", "5").replace("s", "5").replace("B", "8").replace("G", "6")
    s = s.replace("z", "2").replace("Z", "2")
    s = re.sub(r"[^0-9/:.-]", "", s)
    return s


def _normalize_date_token(s, reference_year=None, prefer_birth=False):
    """
    Normaliza fechas OCR y corrige errores frecuentes:
    - 26052026 -> 26/05/2026
    - 03/05/1054 -> 03/05/1954 (año de nacimiento)
    - años 2006/1056 en estudios con fecha de portada 2026 -> se corrigen usando reference_year
    """
    s0 = _num_clean_token(s)
    s0 = s0.replace("-", "/").replace(".", "/")
    digits = re.sub(r"\D", "", s0)

    seqs = []
    if len(digits) >= 8:
        # buscar ventanas ddmmaaaa válidas
        for i in range(0, len(digits)-7):
            seqs.append(digits[i:i+8])
    elif len(digits) == 6:
        seqs.append(digits)
    else:
        m = re.search(r"(\d{1,2})/(\d{1,2})/(\d{2,4})", s0)
        if m:
            d, mo, y = m.groups()
            seqs.append(f"{int(d):02d}{int(mo):02d}{int(y):0{len(y)}d}")

    for seq in seqs:
        try:
            if len(seq) == 8:
                d, mo, y = int(seq[:2]), int(seq[2:4]), int(seq[4:])
            elif len(seq) == 6:
                d, mo, y = int(seq[:2]), int(seq[2:4]), 2000 + int(seq[4:])
            else:
                continue
        except Exception:
            continue
        if not (1 <= d <= 31 and 1 <= mo <= 12):
            continue

        # Correcciones de año
        if y < 100:
            y = 2000 + y
        if 1000 <= y <= 1099:
            # error clásico OCR: 1954 -> 1054
            y = 1900 + (y % 100)
        if prefer_birth and y > datetime.now().year:
            y -= 100
        if reference_year is not None:
            try:
                ry = int(reference_year)
                # En MedicalDB OCR suele leer 2026 como 2006 o 1056.
                if 2000 <= y <= 2015 and ry >= 2020:
                    y = ry
                if 1000 <= y <= 1099 and ry >= 2020 and not prefer_birth:
                    y = ry
            except Exception:
                pass
        return f"{d:02d}/{mo:02d}/{y:04d}"
    return None


def _normalize_time_token(s):
    s0 = _num_clean_token(s).replace("-", ":").replace(".", ":").replace("/", ":")
    m = re.search(r"(\d{1,2}):(\d{2})(?::(\d{2}))?", s0)
    if m:
        h = int(m.group(1)) % 24
        mi = int(m.group(2))
        ss = int(m.group(3) or 0)
        if mi < 60 and ss < 60:
            return f"{h:02d}:{mi:02d}"
    digits = re.sub(r"\D", "", s0)
    # 164500 -> 16:45 ; 071500 -> 07:15
    if len(digits) >= 4:
        if len(digits) >= 6:
            h, mi = int(digits[-6:-4]), int(digits[-4:-2])
        else:
            h, mi = int(digits[:-2]), int(digits[-2:])
        if 0 <= h <= 23 and 0 <= mi <= 59:
            return f"{h:02d}:{mi:02d}"
    return None


def _study_reference_year(text):
    """Año de estudio confiable desde portada: 'Fecha: dd/mm/aaaa'."""
    if not text:
        return None
    m = re.search(r"Paciente:.*?Fecha[:\s]+(\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4})", text, re.I | re.S)
    if not m:
        m = re.search(r"\bFecha[:\s]+(\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4})", text, re.I)
    if m:
        f = _normalize_date_token(m.group(1))
        if f:
            try:
                return datetime.strptime(f, "%d/%m/%Y").year
            except Exception:
                return None
    return None


def _merge_positions(vals, tol=10):
    out = []
    for v in sorted([int(x) for x in vals]):
        if not out or abs(v - out[-1]) > tol:
            out.append(v)
        else:
            out[-1] = int((out[-1] + v) / 2)
    return out


def _numeric_candidates_from_cell(txt, low, high):
    """Devuelve candidatos numéricos desde una celda OCR con flechas/ruido."""
    cands = set()
    s = _num_clean_token(txt)
    for seq in re.findall(r"\d+", s):
        vals = set()
        if 1 <= len(seq) <= 3:
            vals.add(int(seq))
        # substrings 2-3 dígitos y eliminación de un dígito para casos tipo 1545 -> 155/154/145
        for L in (2, 3):
            for i in range(0, max(0, len(seq)-L+1)):
                vals.add(int(seq[i:i+L]))
        if len(seq) >= 4:
            for i in range(len(seq)):
                ss = seq[:i] + seq[i+1:]
                for L in (2, 3):
                    for j in range(0, max(0, len(ss)-L+1)):
                        vals.add(int(ss[j:j+L]))
        for v in vals:
            if low <= v <= high:
                cands.add(v)
    return sorted(cands)


def _choose_plausible_row_from_cells(cells, reference_year=None):
    """Interpreta una fila de Tabla Completa leída por layout OCR."""
    if len(cells) < 7:
        return None
    fecha = _normalize_date_token(cells[1], reference_year=reference_year)
    hora = _normalize_time_token(cells[2])
    if not fecha or not hora:
        return None

    pas_c = _numeric_candidates_from_cell(cells[3], 60, 260)
    pad_c = _numeric_candidates_from_cell(cells[4], 25, 150)
    fc_c  = _numeric_candidates_from_cell(cells[5], 30, 180)
    # A veces OCR une PAM y PP; mirar también celdas vecinas.
    pam_c = _numeric_candidates_from_cell(cells[6], 40, 180)
    pp_c  = _numeric_candidates_from_cell(cells[7] if len(cells)>7 else "", 10, 180)
    if not pp_c and len(cells) > 6:
        pp_c = _numeric_candidates_from_cell(" ".join(cells[6:8]), 10, 180)

    best = None
    for pas in pas_c[:12]:
        for pad in pad_c[:12]:
            if pas <= pad:
                continue
            for fc in (fc_c[:10] or [np.nan]):
                for pam in (pam_c[:10] or [round(pad + (pas-pad)/3)]):
                    for pp in (pp_c[:10] or [pas-pad]):
                        score = abs(pp - (pas-pad))*3 + abs(pam - (pad + (pas-pad)/3))*2
                        # penalizar imposibles sin descartar: después se depuran por criterios MAPA
                        if pp < 10 or pp > 160:
                            score += 100
                        if pas > 230 or pad > 130:
                            score += 15
                        cand = (score, pas, pad, fc, pam, pp)
                        if best is None or cand < best:
                            best = cand
    if best is None or best[0] > 140:
        return None
    _, pas, pad, fc, pam, pp = best
    return {
        "fecha": fecha, "hora": hora, "PAS": pas, "PAD": pad,
        "FC": fc, "PAM": pam, "PP": pp,
        "Período": "Nocturno" if re.search(r"noche|noct", " ".join(cells), re.I) else "",
        "motivo": " ".join(cells)
    }


def _ocr_medicaldb_table_layout(pdf_file, dpi=220):
    """
    OCR por layout de la 'Tabla Completa' de MedicalDB.
    Usa detección de grilla para evitar leer promedios horarios o estadísticas.
    Es más robusto que OCR lineal cuando la tabla está escaneada.
    """
    try:
        import fitz
        import cv2
        import pytesseract
        from pytesseract import Output
        import numpy as _np
    except Exception as e:
        raise RuntimeError(f"OCR de tabla por celdas no disponible: {e}")

    pdf_file.seek(0)
    data = pdf_file.read()
    doc = fitz.open(stream=data, filetype="pdf")
    zoom = dpi / 72.0
    mat = fitz.Matrix(zoom, zoom)

    # texto liviano para año de referencia
    try:
        ref_text = _ocr_pdf_pages(io.BytesIO(data), dpi=150)
    except Exception:
        ref_text = ""
    ref_year = _study_reference_year(ref_text)

    all_rows = []
    for pno, page in enumerate(doc):
        # MedicalDB suele tener tablas completas en las últimas páginas, pero no asumimos.
        pix = page.get_pixmap(matrix=mat, alpha=False)
        img = _np.frombuffer(pix.samples, dtype=_np.uint8).reshape(pix.height, pix.width, pix.n)
        if pix.n == 4:
            img = cv2.cvtColor(img, cv2.COLOR_RGBA2RGB)

        gray = cv2.cvtColor(img, cv2.COLOR_RGB2GRAY)
        h, w = gray.shape

        # detectar líneas de grilla
        bin_img = cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_MEAN_C,
                                        cv2.THRESH_BINARY_INV, 31, 15)
        v_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (1, max(20, h//85)))
        h_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (max(20, w//85), 1))
        vert = cv2.morphologyEx(bin_img, cv2.MORPH_OPEN, v_kernel, iterations=1)
        hor  = cv2.morphologyEx(bin_img, cv2.MORPH_OPEN, h_kernel, iterations=1)

        xs, ys = [], []
        contours, _ = cv2.findContours(vert, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        for c in contours:
            x, y, ww, hh = cv2.boundingRect(c)
            if hh > h*0.18 and ww < 25:
                xs.append(x + ww//2)
        contours, _ = cv2.findContours(hor, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        for c in contours:
            x, y, ww, hh = cv2.boundingRect(c)
            if ww > w*0.50 and hh < 25:
                ys.append(y + hh//2)

        xs = _merge_positions(xs, max(8, int(w*0.006)))
        ys = _merge_positions(ys, max(8, int(h*0.004)))
        if len(xs) < 8 or len(ys) < 8:
            continue

        # OCR de página a data frame de palabras con coordenadas
        try:
            data_ocr = pytesseract.image_to_data(gray, lang="spa+eng", config="--oem 3 --psm 6", output_type=Output.DICT)
        except Exception:
            data_ocr = pytesseract.image_to_data(gray, lang="eng", config="--oem 3 --psm 6", output_type=Output.DICT)

        cells = [[[] for _ in range(len(xs)-1)] for __ in range(len(ys)-1)]
        for i, word in enumerate(data_ocr.get("text", [])):
            word = str(word).strip()
            if not word:
                continue
            try:
                if float(data_ocr.get("conf", [0])[i]) < 0:
                    continue
            except Exception:
                pass
            cx = data_ocr["left"][i] + data_ocr["width"][i] / 2
            cy = data_ocr["top"][i] + data_ocr["height"][i] / 2
            ci = next((j for j in range(len(xs)-1) if xs[j] <= cx <= xs[j+1]), None)
            ri = next((j for j in range(len(ys)-1) if ys[j] <= cy <= ys[j+1]), None)
            if ci is not None and ri is not None:
                cells[ri][ci].append(word)

        cell_text = [[" ".join(x) for x in row] for row in cells]

        # encontrar fila encabezado
        header_i = None
        for i, row in enumerate(cell_text):
            joined = " ".join(row[:10]).lower()
            if ("fecha" in joined and "hora" in joined) or ("sis" in joined and "dia" in joined):
                header_i = i
                break
        if header_i is None:
            continue

        page_rows = []
        for row in cell_text[header_i+1:]:
            parsed = _choose_plausible_row_from_cells(row, reference_year=ref_year)
            if parsed:
                parsed["nro"] = len(all_rows) + len(page_rows) + 1
                page_rows.append(parsed)

        if len(page_rows) >= 2:
            all_rows.extend(page_rows)

    if not all_rows:
        return None
    df = pd.DataFrame(all_rows)
    df = df.drop_duplicates(subset=["fecha","hora","PAS","PAD"], keep="first")
    for c in ["PAS","PAD","FC","PAM","PP"]:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    df = df.dropna(subset=["PAS","PAD"])
    return df if len(df) >= 10 else None


def _extract_ints_after(text):
    vals = []
    for tok in re.findall(r"[A-Za-z0-9/:.-]+", text):
        c = _num_clean_token(tok)
        if re.fullmatch(r"\d{1,3}", c):
            try:
                vals.append(int(c))
            except Exception:
                pass
    return vals


def _plausible_reading(pas, pad, fc=None, pam=None, pp=None):
    if pas is None or pad is None:
        return False
    if not (60 <= pas <= 260 and 25 <= pad <= 150 and pas > pad):
        return False
    if fc is not None and not (30 <= fc <= 180):
        return False
    if pp is not None and abs((pas - pad) - pp) > 40:
        # Puede haber OCR imperfecto, pero no aceptar absurdos.
        return False
    return True


def _parse_medicaldb_table_text(text):
    """
    Parser dedicado a páginas 'Tabla Completa' de MedicalDB.
    Extrae: nro, fecha, hora, PAS/SIS, PAD/DIA, FC, PAM, PP, período, tipo/comentario.
    """
    if not text:
        return None

    # Tomar preferentemente el texto desde Tabla Completa en adelante.
    low = text.lower()
    chunks = []
    for m in re.finditer(r"tabla\s+completa", low):
        chunks.append(text[m.start(): m.start() + 9000])
    if not chunks:
        # No rechazar: algunos OCR pierden el título.
        chunks = [text]

    ref_year = _study_reference_year(text)
    rows = []
    row_regex = re.compile(
        r"(?P<nro>\d{1,3})\D+"
        r"(?P<fecha>(?:\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}|\d{6,8}))\D+"
        r"(?P<hora>(?:\d{1,2}[:\-]\d{2}(?:[:\-]\d{2})?|\d{4,6}))"
        r"(?P<rest>.*?)(?=(?:\n|\r).{0,20}\d{1,3}\D+(?:\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}|\d{6,8})|$)",
        re.IGNORECASE | re.DOTALL
    )

    for chunk in chunks:
        # Reducir salto de línea dentro de una misma fila, pero preservar separadores principales.
        chunk2 = re.sub(r"[ \t]+", " ", chunk)
        for mm in row_regex.finditer(chunk2):
            nro_raw = _num_clean_token(mm.group("nro"))
            fecha = _normalize_date_token(mm.group("fecha"), reference_year=ref_year)
            hora = _normalize_time_token(mm.group("hora"))
            rest = mm.group("rest")[:220]
            nums = _extract_ints_after(rest)

            # Filtrar tokens que suelen ser parte de hora/fecha repetida.
            candidates = [x for x in nums if 0 <= x <= 260]
            # Buscar ventana PAS PAD FC PAM PP plausible.
            best = None
            for i in range(0, max(1, len(candidates)-4)):
                win = candidates[i:i+5]
                if len(win) < 5:
                    continue
                pas, pad, fc, pam, pp = win[:5]
                if _plausible_reading(pas, pad, fc, pam, pp):
                    best = (pas, pad, fc, pam, pp)
                    break
            if best is None and len(candidates) >= 2:
                # Último intento: primera dupla PAS/PAD plausible y completar.
                for i in range(0, len(candidates)-1):
                    pas, pad = candidates[i], candidates[i+1]
                    if _plausible_reading(pas, pad):
                        fc = candidates[i+2] if i+2 < len(candidates) else np.nan
                        pam = candidates[i+3] if i+3 < len(candidates) else np.nan
                        pp = candidates[i+4] if i+4 < len(candidates) else pas-pad
                        best = (pas, pad, fc, pam, pp)
                        break

            if fecha and hora and best:
                pas, pad, fc, pam, pp = best
                periodo = "Nocturno" if re.search(r"noche|noct", rest, re.I) else ""
                rows.append({
                    "nro": int(nro_raw) if nro_raw.isdigit() else len(rows)+1,
                    "fecha": fecha, "hora": hora,
                    "PAS": pas, "PAD": pad, "FC": fc, "PAM": pam, "PP": pp,
                    "Período": periodo,
                    "motivo": rest.strip()
                })

    if len(rows) < 10:
        # Parser línea por línea, menos estricto, para OCR con filas intactas.
        for line in text.splitlines():
            if not re.search(r"\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}|\d{6,8}", line):
                continue
            if not re.search(r"\d{1,2}[:\-]\d{2}|\d{4,6}", line):
                continue
            tokens = line.split()
            fecha = None; hora = None
            for tok in tokens:
                if fecha is None:
                    fecha = _normalize_date_token(tok, reference_year=ref_year)
                    if fecha: 
                        continue
                if fecha and hora is None:
                    hora = _normalize_time_token(tok)
                    if hora:
                        break
            nums = _extract_ints_after(line)
            # quitar nro/fecha/hora aproximados: buscar ventana plausible
            best = None
            for i in range(0, max(1, len(nums)-4)):
                win = nums[i:i+5]
                if len(win) == 5 and _plausible_reading(*win[:5]):
                    best = win[:5]; break
            if fecha and hora and best:
                pas, pad, fc, pam, pp = best
                rows.append({
                    "nro": len(rows)+1, "fecha": fecha, "hora": hora,
                    "PAS": pas, "PAD": pad, "FC": fc, "PAM": pam, "PP": pp,
                    "Período": "Nocturno" if re.search(r"noche|noct", line, re.I) else "",
                    "motivo": line.strip()
                })

    if not rows:
        return None

    df = pd.DataFrame(rows)
    df = df.drop_duplicates(subset=["fecha","hora","PAS","PAD"], keep="first")
    for c in ["PAS","PAD","FC","PAM","PP"]:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    df = df.dropna(subset=["PAS","PAD"])
    return df if len(df) >= 10 else None

def _ensure_datetime_sequence(df, meta=None):
    df = df.copy()
    # datetime real si hay fecha
    if "fecha" in df.columns:
        dt = pd.to_datetime(df["fecha"].astype(str) + " " + df["hora"].astype(str),
                            dayfirst=True, errors="coerce")
    else:
        dt = pd.Series([pd.NaT]*len(df))
    if dt.notna().sum() >= max(5, len(df)//2):
        df["dt"] = dt
        df = df.sort_values("dt").reset_index(drop=True)
        base = df["dt"].dropna().iloc[0]
        df["tplot"] = (df["dt"] - base).dt.total_seconds() / 60.0
        df["hora_label"] = df["dt"].dt.strftime("%H:%M")
    else:
        # Usar orden de fila y corregir cruce de medianoche.
        mins = df["hora"].apply(time_to_minutes).astype(float)
        corrected = []
        offset = 0
        prev = None
        for m in mins:
            if pd.isna(m):
                corrected.append(np.nan); continue
            if prev is not None and (m + offset) < prev - 360:
                offset += 1440
            corrected.append(m + offset)
            prev = m + offset
        df["tplot"] = corrected
        df["hora_label"] = df["hora"].astype(str).str.slice(0,5)
    return df

def _parse_from_tables(tables):
    best = None
    for tbl in tables:
        if not tbl or len(tbl) < 4:
            continue
        # Try every row as potential header
        for i, row in enumerate(tbl):
            if not row:
                continue
            row_s = ' '.join(str(x).upper() for x in row if x)
            has_sys = any(k in row_s for k in ['SIS','DIA','PAS','PAD','SIST','SYS'])
            has_time = any(k in row_s for k in ['HORA','TIME','HH:','FECHA'])
            if has_sys:
                headers = [str(x).strip() if x else f'C{j}' for j, x in enumerate(row)]
                data = tbl[i+1:]
                if len(data) < 3:
                    continue
                df = pd.DataFrame(data, columns=headers)
                result = _standardize(df)
                if result is not None and (best is None or len(result) > len(best)):
                    best = result
    return best

def _parse_from_text_v2(text):
    """Multi-pattern text parser."""
    readings = []

    # Pattern A: date+time then numbers  (dd/mm/yyyy hh:mm  SYS  DIA  HR)
    pat_a = re.compile(
        r'\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}\s+'
        r'(\d{1,2}:\d{2})\s+'
        r'(\d{2,3})\s+(\d{2,3})\s+(\d{2,3})'
    )
    # Pattern B: time then 3+ numbers  (hh:mm  SYS  DIA  HR)
    pat_b = re.compile(r'(\d{1,2}:\d{2})\s+(\d{2,3})\s+(\d{2,3})\s+(\d{2,3})')
    # Pattern C: time then 2 numbers  (hh:mm  SYS  DIA)
    pat_c = re.compile(r'(\d{1,2}:\d{2})\s+(\d{2,3})\s+(\d{2,3})')
    # Pattern D: number  time  SYS  DIA  HR  (row number first)
    pat_d = re.compile(r'^\s*\d+\s+(\d{1,2}:\d{2})\s+(\d{2,3})\s+(\d{2,3})\s+(\d{2,3})', re.MULTILINE)
    # Pattern E: MedicalDB style: No Hora Sis Dia Pul (columns with spaces)
    pat_e = re.compile(r'(\d{1,2}:\d{2})\D{0,5}(\d{2,3})\D{1,5}(\d{2,3})\D{1,5}(\d{2,3})')

    for pat, groups in [(pat_a,(1,2,3,4)), (pat_d,(1,2,3,4)),
                         (pat_b,(1,2,3,4)), (pat_e,(1,2,3,4)), (pat_c,(1,2,3,None))]:
        matches = list(pat.finditer(text))
        if len(matches) >= 5:
            local_readings = []
            for match in matches:
                try:
                    hora = match.group(groups[0])
                    v1   = int(match.group(groups[1]))
                    v2   = int(match.group(groups[2]))
                    v3   = int(match.group(groups[3])) if groups[3] else None
                    # Auto-detect SYS/DIA/HR order: SYS > DIA, both plausible
                    if 50 <= v1 <= 250 and 30 <= v2 <= 150:
                        r = {'hora': hora, 'PAS': v1, 'PAD': v2}
                        if v3 and 30 <= v3 <= 200:
                            r['FC'] = v3
                        local_readings.append(r)
                except:
                    pass
            if len(local_readings) > len(readings):
                readings = local_readings

    if len(readings) >= 5:
        df = pd.DataFrame(readings)
        df = df[df['PAS'].between(50,280) & df['PAD'].between(20,160)]
        if 'FC' in df.columns:
            df = df[df['FC'].between(30,200) | df['FC'].isna()]
        return df if len(df) >= 5 else None
    return None

def _parse_fixed_width(text):
    """Parse fixed-width column data common in ABPM reports."""
    lines = [l for l in text.split('\n') if l.strip()]
    readings = []
    # Look for lines that are mostly numbers
    num_pat = re.compile(r'^[\s\d:/\-\.DdNn]+$')
    time_pat = re.compile(r'\d{1,2}:\d{2}')
    num_only = re.compile(r'\d+')

    for line in lines:
        if not time_pat.search(line):
            continue
        nums = num_only.findall(line)
        time_m = time_pat.search(line)
        if not time_m or len(nums) < 2:
            continue
        try:
            hora = time_m.group()
            # Remove time digits from nums list
            h, mn = hora.split(':')
            remaining = [int(n) for n in nums
                         if n not in [h, mn, h.lstrip('0') or '0']]
            # Find SYS and DIA among remaining numbers
            candidates = [n for n in remaining if 50 <= n <= 250]
            if len(candidates) >= 2:
                pas, pad = candidates[0], candidates[1]
                if pas > pad:
                    r = {'hora': hora, 'PAS': pas, 'PAD': pad}
                    fc_cands = [n for n in remaining if 30 <= n <= 200 and n != pas and n != pad]
                    if fc_cands:
                        r['FC'] = fc_cands[0]
                    readings.append(r)
        except:
            pass

    if len(readings) >= 5:
        df = pd.DataFrame(readings)
        return df if len(df) >= 5 else None
    return None

def _parse_from_text(text):
    # Legacy wrapper
    return _parse_from_text_v2(text)

def _parse_from_text_v2_old(text):
    lines = text.split('\n')
    readings = []
    pat = re.compile(r'(\d{1,2}:\d{2})\s+(\d{2,3})\s+(\d{2,3})(?:\s+(\d{2,3}))?')
    for line in lines:
        m = pat.search(line)
        if m:
            try:
                hora = m.group(1)
                n1, n2 = int(m.group(2)), int(m.group(3))
                n3 = int(m.group(4)) if m.group(4) else None
                if 60 <= n1 <= 230 and 30 <= n2 <= 130:
                    r = {'hora': hora, 'PAS': n1, 'PAD': n2}
                    if n3 and 30 <= n3 <= 160:
                        r['FC'] = n3
                    readings.append(r)
            except:
                pass
    if len(readings) > 5:
        return pd.DataFrame(readings)
    return None


def _parse_numeric_pairs(text):
    """
    Parser de último recurso para texto OCR con formato irregular.
    Busca hora hh:mm + par numérico PAS/PAD plausible en cada línea.
    Aplica _num_clean_token para recuperar dígitos de strings mixtos
    como '11s'→115, 'ss'→55, 'iio'→110 (ZLogic/MedicalDB).
    """
    readings = []
    for line in text.splitlines():
        hora_m = re.search(r'\b(\d{1,2}):(\d{2})\b', line)
        if not hora_m:
            continue
        h, mi = int(hora_m.group(1)), int(hora_m.group(2))
        if h > 23 or mi > 59:
            continue
        hora = f"{h:02d}:{mi:02d}"
        # Aplicar _num_clean_token a cada token separado por espacios/separadores
        # antes de buscar números, para recuperar dígitos en strings mixtos.
        clean_tokens = []
        for tok in re.split(r'[\s|\[\]{}]+', line):
            if not tok:
                continue
            c = _num_clean_token(tok)
            # Extraer secuencias de 2-3 dígitos del token limpio
            for m in re.finditer(r'\d{2,3}', c):
                v = int(m.group())
                if 30 <= v <= 260:
                    clean_tokens.append(v)
        nums = clean_tokens
        for i in range(len(nums) - 1):
            pas, pad = nums[i], nums[i + 1]
            if 80 <= pas <= 220 and 40 <= pad <= 130 and pas > pad + 10:
                r = {'hora': hora, 'PAS': pas, 'PAD': pad}
                if i + 2 < len(nums) and 30 <= nums[i + 2] <= 180:
                    r['FC'] = nums[i + 2]
                readings.append(r)
                break
    if len(readings) < 5:
        return None
    df = pd.DataFrame(readings)
    df = df.drop_duplicates(subset=['hora', 'PAS', 'PAD'], keep='first')
    df = df[df['PAS'].between(80, 220) & df['PAD'].between(40, 130)]
    return df if len(df) >= 5 else None



def _parse_zlogic_table(text):
    """
    Parser dedicado para PDFs del equipo ZLogic / MedicalDB 17.7.
    Maneja la 'Tabla Completa' con celdas separadas por | y [ con OCR ruidoso.
    Detecta la hora en múltiples formatos OCR:
      • HH:MM[:SS]   → dos puntos estándar
      • HHMM.SS      → punto como separador de segundos (ej. 1845.00)
      • HH-MM        → guión como separador (ej. 05-4500)
      • HHMMSS       → 6 dígitos consecutivos aislados (ej. 174500)
      • igual en versión OCR-limpia (ej. oo4s00 → 004500)
    """
    if not text:
        return None

    # Tomar texto desde "Tabla Completa" en adelante (puede haber 2 secciones).
    low = text.lower()
    chunks = []
    for m in re.finditer(r"tabla\s+completa", low):
        chunks.append(text[m.start(): m.start() + 12000])
    if not chunks:
        chunks = [text]

    ref_year = _study_reference_year(text) or datetime.now().year
    rows = []

    def _find_time(line):
        """Detecta HH:MM en línea OCR ZLogic con múltiples formatos. Retorna (hora, end_pos)."""
        # Prioridad 1: HH:MM[:SS] con dos puntos estándar
        m = re.search(r'(?<![/\d])(\d{1,2}):(\d{2})(?::\d{2})?', line)
        if m:
            h, mi = int(m.group(1)), int(m.group(2))
            if h <= 23 and mi <= 59:
                return f"{h:02d}:{mi:02d}", m.end()

        # Prioridad 2: HHMM.SS (ej. 1845.00, 0415.00, 0745.00)
        m = re.search(r'(?<!\d)(\d{2})(\d{2})\.(\d{2})(?!\d)', line)
        if m:
            h, mi = int(m.group(1)), int(m.group(2))
            if h <= 23 and mi <= 59:
                return f"{h:02d}:{mi:02d}", m.end()

        # Prioridad 3: HH-MM (guión, ej. 05-4500, 06-0000)
        m = re.search(r'(?<![/\d])(\d{2})-(\d{2})', line)
        if m:
            h, mi = int(m.group(1)), int(m.group(2))
            if h <= 23 and mi <= 59:
                return f"{h:02d}:{mi:02d}", m.end()

        # Prioridad 4: HHMMSS exactos (6 dígitos aislados, ej. 174500, 211600)
        for m in re.finditer(r'(?<!\d)(\d{2})(\d{2})(\d{2})(?!\d)', line):
            h, mi, ss = int(m.group(1)), int(m.group(2)), int(m.group(3))
            if h <= 23 and mi <= 59 and ss <= 59:
                return f"{h:02d}:{mi:02d}", m.end()

        # Prioridad 5: igual con sustituciones OCR (ej. oo4s00→004500, o14s00→014500)
        lc = re.sub(r'[oO]', '0', line)
        lc = re.sub(r'[lI]', '1', lc)
        lc = re.sub(r'[sS]', '5', lc)
        if lc != line:
            m = re.search(r'(?<!\d)(\d{2})(\d{2})\.(\d{2})(?!\d)', lc)
            if m:
                h, mi = int(m.group(1)), int(m.group(2))
                if h <= 23 and mi <= 59:
                    return f"{h:02d}:{mi:02d}", m.end()
            for m in re.finditer(r'(?<!\d)(\d{2})(\d{2})(\d{2})(?!\d)', lc):
                h, mi, ss = int(m.group(1)), int(m.group(2)), int(m.group(3))
                if h <= 23 and mi <= 59 and ss <= 59:
                    return f"{h:02d}:{mi:02d}", m.end()

        return None, -1

    for chunk in chunks:
        for line in chunk.splitlines():
            if len(line) < 10:
                continue

            hora, time_end = _find_time(line)
            if hora is None:
                continue

            # Buscar fecha en la línea completa
            fecha = None
            for tok in re.split(r'[|\[\]{}]', line):
                tok = tok.strip()
                if not tok:
                    continue
                c = _num_clean_token(tok)
                fecha = _normalize_date_token(c, reference_year=ref_year)
                if fecha:
                    break
            if not fecha:
                fecha = _normalize_date_token(_num_clean_token(line), reference_year=ref_year)

            # Extraer números de los tokens POST-hora
            # Para tokens cortos (≤5 chars) se aplican sustituciones ZLogic agresivas
            # (i→1, a→4) sin afectar palabras largas como "Automatica"/"Repeticion".
            post_line = line[time_end:]
            nums = []
            for tok in re.split(r'[|\[\]{}\s]+', post_line)[:12]:
                if not tok:
                    continue
                c = _num_clean_token(tok)
                # Sustituciones extra sólo para tokens cortos (valor numérico con OCR)
                if len(tok.strip()) <= 5:
                    c2 = tok.strip()
                    c2 = c2.replace("i","1").replace("a","4")
                    c2 = c2.replace("l","1").replace("I","1")
                    c2 = c2.replace("o","0").replace("O","0")
                    c2 = c2.replace("s","5").replace("S","5")
                    c2 = c2.replace("z","2").replace("G","6")
                    c2 = re.sub(r"[^0-9]", "", c2)
                    if len(c2) > len(re.sub(r"[^0-9]", "", c)):
                        c = c2
                for m2 in re.finditer(r'\d{2,3}', c):
                    v = int(m2.group())
                    if 20 <= v <= 260:
                        nums.append(v)

            if len(nums) < 2:
                continue

            # Buscar par PAS/PAD plausible
            # Umbral inferior: 60 para PAS (lecturas nocturnas pueden ser 65-79)
            # y 30 para PAD (clean_data filtra después con PAD_min=40)
            best = None
            for i in range(len(nums) - 1):
                pas, pad = nums[i], nums[i + 1]
                if 60 <= pas <= 220 and 30 <= pad <= 130 and pas > pad + 10:
                    fc  = nums[i+2] if i+2 < len(nums) and 30 <= nums[i+2] <= 180 else np.nan
                    pam = nums[i+3] if i+3 < len(nums) else round(pad + (pas - pad) / 3)
                    pp  = nums[i+4] if i+4 < len(nums) else pas - pad
                    best = (pas, pad, fc, pam, pp)
                    break

            if best is None:
                continue

            pas, pad, fc, pam, pp = best
            periodo = "Nocturno" if re.search(r'noche|noct', line, re.I) else ""
            rows.append({
                "nro": len(rows) + 1,
                "fecha": fecha or "",
                "hora": hora,
                "PAS": pas, "PAD": pad, "FC": fc, "PAM": pam, "PP": pp,
                "Período": periodo,
                "motivo": line.strip()
            })

    if not rows:
        return None

    df = pd.DataFrame(rows)
    df = df.drop_duplicates(subset=["hora", "PAS", "PAD"], keep="first")
    for c in ["PAS", "PAD", "FC", "PAM", "PP"]:
        df[c] = pd.to_numeric(df[c], errors="coerce")
    df = df.dropna(subset=["PAS", "PAD"])
    return df if len(df) >= 10 else None

def _extract_meta(text):
    """Extrae filiatorios automáticamente desde PDF/OCR del equipo MedicalDB."""
    meta = {}
    if not text:
        return meta

    # Normalizaciones OCR mínimas para etiquetas, no para valores.
    t = re.sub(r"[ \t]+", " ", text)
    t_label = (t.replace("Macimiento", "Nacimiento")
                 .replace("Mocimiento", "Nacimiento")
                 .replace("Múmero", "Número")
                 .replace("Glorla", "GLORIA")
                 .replace("GLOETA", "GLORIA"))

    ref_year = _study_reference_year(t_label)

    # Paciente / Apellido y Nombre
    pats = [
        r"Apellido\s*y\s*Nombre[:\s]+([A-ZÁÉÍÓÚÑa-záéíóúñ ]+?)(?:\*|Documento|Domicilio|\n)",
        r"Paciente[:\s]+([A-ZÁÉÍÓÚÑa-záéíóúñ ]+?)(?:\*|Fecha|Documento|Domicilio|\n)",
    ]
    for pat in pats:
        m = re.search(pat, t_label, re.IGNORECASE)
        if m:
            nombre = re.sub(r"[^A-Za-zÁÉÍÓÚÑáéíóúñ ]", " ", m.group(1))
            nombre = re.sub(r"\s+", " ", nombre).strip().upper()
            if len(nombre) >= 5 and "MONITOREO" not in nombre:
                meta["paciente"] = nombre
                break

    # Documento
    m = re.search(r"Documento[:\s]+(\d{6,10})", t_label, re.I)
    if m:
        meta["documento"] = m.group(1)

    # Fecha de nacimiento y edad calculada
    m = re.search(r"Fecha\s+de\s+Nacimiento[:\s]+(\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4})", t_label, re.I)
    if m:
        fnac = _normalize_date_token(m.group(1), prefer_birth=True)
        meta["fecha_nacimiento"] = fnac

    # Sexo: permitir OCR parcial; si no figura M/F, dejar no especificado.
    m = re.search(r"Sexo[:\s]+([MF])\b", t_label, re.I)
    if m:
        meta["sexo"] = "Femenino" if m.group(1).upper() == "F" else "Masculino"

    # Obra social
    m = re.search(r"Obra\s+Social[:\s]+([A-ZÁÉÍÓÚÑa-záéíóúñ0-9 ._-]+?)(?:Número|Numero|Múmero|Datos del estudio|\n)", t_label, re.I)
    if m:
        osoc = re.sub(r"[^A-ZÁÉÍÓÚÑa-záéíóúñ0-9 ._-]", "", m.group(1)).strip().upper()
        osoc = re.sub(r"\s+", " ", osoc).strip(" -—")
        if osoc:
            meta["obra_social"] = osoc

    # Inicio / Fin; corregir año por portada si OCR lee 2006 en lugar de 2026.
    m = re.search(
        r"Inicio[:\s]+(\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4})\s+(\d{1,2}:\d{2}(?::\d{2})?)\s+Fin[:\s]+(\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4})\s+(\d{1,2}:\d{2}(?::\d{2})?)",
        t_label, re.I)
    if m:
        meta["fecha_inicio"] = _normalize_date_token(m.group(1), reference_year=ref_year)
        meta["hora_inicio"] = _normalize_time_token(m.group(2))
        meta["fecha_fin"] = _normalize_date_token(m.group(3), reference_year=ref_year)
        meta["hora_fin"] = _normalize_time_token(m.group(4))
    else:
        # Portada o datos de estudio.
        dates = re.findall(r"\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}", t_label)
        if dates:
            # preferir la fecha de portada si aparece luego de "Paciente"
            meta["fecha_inicio"] = _normalize_date_token(dates[0], reference_year=ref_year)

    if meta.get("fecha_inicio") and not meta.get("fecha_fin") and meta.get("hora_fin"):
        meta["fecha_fin"] = meta["fecha_inicio"]

    # Edad desde fecha nacimiento y fecha del estudio.
    try:
        if meta.get("fecha_nacimiento") and meta.get("fecha_inicio"):
            fn = datetime.strptime(meta["fecha_nacimiento"], "%d/%m/%Y")
            fe = datetime.strptime(meta["fecha_inicio"], "%d/%m/%Y")
            edad = fe.year - fn.year - ((fe.month, fe.day) < (fn.month, fn.day))
            if 0 <= edad <= 120:
                meta["edad"] = edad
    except Exception:
        pass

    # Dispositivo
    for dev in ["MedicalDB 17.7", "MedicalDB", "SpaceLabs", "Microlife", "OMRON", "Schiller", "Welch Allyn", "A&D"]:
        if dev.lower() in t_label.lower():
            meta["dispositivo"] = dev
            break

    # Solicitante y motivo
    m = re.search(r"Solicitado\s+por[:\s]+(.+?)(?:Motivo|\n)", t_label, re.I)
    if m:
        val = re.sub(r"\s+", " ", m.group(1)).strip().upper()
        if val:
            meta["solicitante"] = val
    m = re.search(r"Motivo[:\s]+(.+?)(?:Informe|\n)", t_label, re.I)
    if m:
        val = re.sub(r"\s+", " ", m.group(1)).strip().upper()
        if val:
            meta["motivo"] = val

    # Duración si figura
    m = re.search(r"Tiempo\s+de\s+estudio[:\s]+(.+?)(?:L[ií]mites|Total|\n)", t_label, re.I)
    if m:
        meta["duracion"] = re.sub(r"\s+", " ", m.group(1)).strip()

    return meta


def assign_periods(df, noc_start=23, noc_end=7):
    df = df.copy()
    def _period_from_time(h):
        mins = time_to_minutes(h)
        if mins is None:
            return 'Diurno'
        hr = mins // 60
        return 'Nocturno' if (hr >= noc_start or hr < noc_end) else 'Diurno'

    if 'Período' not in df.columns:
        df['Período'] = df['hora'].apply(_period_from_time)
        df['periodo_asumido'] = True
    else:
        def norm_period(row):
            val = str(row.get('Período', '')).lower()
            if 'noch' in val or 'noct' in val:
                return 'Nocturno'
            if 'dia' in val or 'diur' in val:
                return 'Diurno'
            return _period_from_time(row.get('hora'))
        df['Período'] = df.apply(norm_period, axis=1)
        df['periodo_asumido'] = False
    return df

def clean_data(df):
    orig = len(df)
    df = df.copy()
    if 'PP' not in df.columns or df['PP'].isna().all():
        df['PP'] = df['PAS'] - df['PAD']
    if 'PAM' not in df.columns or df['PAM'].isna().all():
        df['PAM'] = (df['PAD'] + (df['PAS'] - df['PAD']) / 3).round(1)
    mask = (
        df['PAD'].between(OUTLIER['PAD_min'], OUTLIER['PAD_max']) &
        (df['PAS'] <= OUTLIER['PAS_max']) &
        df['PP'].between(OUTLIER['PP_min'], OUTLIER['PP_max'])
    )
    return df[mask].copy(), orig - mask.sum(), orig

# ─────────────────────────────────────────────────────────────────────────────
# METRICS CALCULATION
# ─────────────────────────────────────────────────────────────────────────────
def calculate_metrics(df, age=None, is_ped=False, sex='M', height=None):
    m = {}
    thr = THRESHOLDS
    if is_ped and age:
        ps, pd_ = ped_thr(age, sex, height)
        thr = {
            '24h':      {'sys': ps,    'dia': pd_},
            'diurno':   {'sys': ps,    'dia': pd_},
            'nocturno': {'sys': ps-10, 'dia': pd_-10},
        }
        m['ped_thr_sys'] = ps
        m['ped_thr_dia'] = pd_
    m['thresholds'] = thr

    day = df[df['Período']=='Diurno']
    noc = df[df['Período']=='Nocturno']

    m.update({'n_total':len(df),'n_diurno':len(day),'n_nocturno':len(noc)})

    for pname, pdf in [('24h',df),('diurno',day),('nocturno',noc)]:
        for col in ['PAS','PAD','PAM','PP','FC']:
            key = f'{col}_{pname}'
            if col in pdf.columns and len(pdf) > 0 and not pdf[col].isna().all():
                m[key] = round(pdf[col].mean(), 1)
            else:
                m[key] = None

    # DE, CV, var^0.5
    for pname, pdf in [('24h',df),('diurno',day),('nocturno',noc)]:
        for col in ['PAS','PAD']:
            if col in pdf.columns and len(pdf) > 1:
                de = pdf[col].std()
                mn = pdf[col].mean()
                m[f'{col}_DE_{pname}'] = round(de, 1)
                m[f'{col}_CV_{pname}'] = round(de/mn*100, 1) if mn else None
            else:
                m[f'{col}_DE_{pname}'] = None; m[f'{col}_CV_{pname}'] = None

    for col in ['PAS','PAD']:
        if col in df.columns and len(df) > 1:
            m[f'{col}_var05'] = round(float(df[col].var())**0.5, 2)
        else:
            m[f'{col}_var05'] = None

    # Cargas
    for pname, pdf in [('24h',df),('diurno',day),('nocturno',noc)]:
        n = len(pdf)
        if n > 0:
            ts, td = thr[pname]['sys'], thr[pname]['dia']
            m[f'carga_sys_{pname}']   = round((pdf['PAS'] > ts).sum()/n*100, 1)
            m[f'carga_dia_{pname}']   = round((pdf['PAD'] > td).sum()/n*100, 1)
            m[f'carga_total_{pname}'] = round(((pdf['PAS']>ts)|(pdf['PAD']>td)).sum()/n*100, 1)
        else:
            for k in [f'carga_sys_{pname}',f'carga_dia_{pname}',f'carga_total_{pname}']:
                m[k] = None

    # Nocturnal dip
    s_d, s_n = m.get('PAS_diurno'), m.get('PAS_nocturno')
    d_d, d_n = m.get('PAD_diurno'), m.get('PAD_nocturno')
    if s_d and s_n and s_d > 0:
        dip_s = 100*(s_d-s_n)/s_d
        dip_d = 100*(d_d-d_n)/d_d if (d_d and d_d > 0) else dip_s
        m['dip_sys'] = round(dip_s,1)
        m['dip_dia'] = round(dip_d,1)
        avg = (dip_s+dip_d)/2
        if avg >= 20:    m['dip_pattern'] = 'EXTREME DIPPER'
        elif avg >= 10:  m['dip_pattern'] = 'DIPPER'
        elif avg >= 0:   m['dip_pattern'] = 'NON-DIPPER'
        else:            m['dip_pattern'] = 'REVERSE DIPPER'
    else:
        m['dip_sys']=m['dip_dia']=None; m['dip_pattern']='NO DISPONIBLE'

    # AASI
    try:
        if len(df) >= 10:
            slope, *_ = sp_stats.linregress(df['PAS'], df['PAD'])
            aasi = round(float(1-slope), 2)
            m['aasi'] = aasi
            if aasi <= 0.40:   m['aasi_interp'] = 'Normal (≤0.40)'
            elif aasi <= 0.50: m['aasi_interp'] = 'Límite (0.41–0.50)'
            else:              m['aasi_interp'] = 'Elevado (>0.50)'
        else:
            m['aasi'] = None; m['aasi_interp'] = 'No disponible (n insuficiente)'
    except:
        m['aasi'] = None; m['aasi_interp'] = 'No disponible'

    # PP interpretation
    pp = m.get('PP_24h')
    m['pp_interp'] = 'NORMAL (<60 mmHg)' if (pp and pp < 60) else ('ELEVADA (≥60 mmHg)' if pp else 'No disponible')

    # Morning surge
    ms = _morning_surge(df)
    m['morning_surge'] = ms
    m['morning_surge_method'] = 'estimado (ventana 06–09 h vs 02–04 h)' if ms is not None else 'no disponible (registro insuficiente)'

    # DE elevated flag
    for col in ['PAS','PAD']:
        de = m.get(f'{col}_DE_24h')
        mn = m.get(f'{col}_24h')
        m[f'{col}_DE_elevated'] = bool(de and mn and (de/mn*100) > 15)

    return m

def _morning_surge(df):
    if 'hora' not in df.columns: return None
    try:
        df = df.copy()
        df['hmin'] = df['hora'].apply(time_to_minutes)
        df = df.dropna(subset=['hmin'])
        morning   = df[df['hmin'].apply(lambda x: 6*60 <= x <= 9*60+59)]
        pre_wake  = df[df['hmin'].apply(lambda x: 2*60 <= x <= 3*60+59)]
        if len(morning) >= 2 and len(pre_wake) >= 1:
            return round(morning['PAS'].mean() - pre_wake['PAS'].mean(), 1)
    except:
        pass
    return None

# ─────────────────────────────────────────────────────────────────────────────
# PHENOTYPE CLASSIFIER
# ─────────────────────────────────────────────────────────────────────────────
def classify_phenotype(m):
    thr = m.get('thresholds', THRESHOLDS)
    vals = {
        's24': m.get('PAS_24h',0) or 0,  'd24': m.get('PAD_24h',0) or 0,
        'sD':  m.get('PAS_diurno',0) or 0,'dD':  m.get('PAD_diurno',0) or 0,
        'sN':  m.get('PAS_nocturno',0) or 0,'dN': m.get('PAD_nocturno',0) or 0,
    }
    f = {
        'h24s': vals['s24'] >= thr['24h']['sys'],
        'h24d': vals['d24'] >= thr['24h']['dia'],
        'hDs':  vals['sD']  >= thr['diurno']['sys'],
        'hDd':  vals['dD']  >= thr['diurno']['dia'],
        'hNs':  vals['sN']  >= thr['nocturno']['sys'],
        'hNd':  vals['dN']  >= thr['nocturno']['dia'],
    }

    if f['h24s'] and f['h24d']:
        if f['hDs'] and f['hDd'] and not f['hNs'] and not f['hNd']:
            return "HTA SISTODIASTÓLICA DIURNA AISLADA"
        if f['hNs'] and f['hNd'] and not f['hDs'] and not f['hDd']:
            return "HTA SISTODIASTÓLICA NOCTURNA AISLADA"
        return "HTA SISTODIASTÓLICA SOSTENIDA"

    if f['h24s'] and not f['h24d']:
        if f['hDs'] and not f['hNs']: return "HTA SISTÓLICA AISLADA DIURNA"
        if f['hNs'] and not f['hDs']: return "HTA SISTÓLICA AISLADA NOCTURNA"
        return "HTA SISTÓLICA AISLADA"

    if f['h24d'] and not f['h24s']:
        if f['hDd'] and not f['hNd']: return "HTA DIASTÓLICA AISLADA DIURNA"
        if f['hNd'] and not f['hDd']: return "HTA DIASTÓLICA AISLADA NOCTURNA"
        return "HTA DIASTÓLICA AISLADA"

    # Check isolated day/night even if 24h averages normal
    if f['hDs'] and f['hDd']: return "HTA SISTODIASTÓLICA DIURNA AISLADA"
    if f['hDs'] and not f['hDd']: return "HTA SISTÓLICA AISLADA DIURNA"
    if f['hDd'] and not f['hDs']: return "HTA DIASTÓLICA AISLADA DIURNA"
    if f['hNs'] and f['hNd']: return "HTA SISTODIASTÓLICA NOCTURNA AISLADA"
    if f['hNs'] and not f['hNd']: return "HTA SISTÓLICA AISLADA NOCTURNA"
    if f['hNd'] and not f['hNs']: return "HTA DIASTÓLICA AISLADA NOCTURNA"

    return "NORMOTENSIÓN AMBULATORIA"

# ─────────────────────────────────────────────────────────────────────────────
# CHART GENERATION
# ─────────────────────────────────────────────────────────────────────────────

def generate_chart(df, m):
    df = df.copy()
    # Eje X cronológico real: NO ordenar por hora del día porque rompe el cruce de medianoche.
    if 'tplot' not in df.columns:
        df = _ensure_datetime_sequence(df, {})
    df = df.sort_values('tplot').reset_index(drop=True)

    thr = m['thresholds']
    fig, axes = plt.subplots(2, 1, figsize=(14, 8), dpi=110,
                              gridspec_kw={'hspace': 0.42})

    # Franja nocturna azul real por segmentos cronológicos
    segs = _noc_segments_plot(df)
    for ax in axes:
        for s, e in segs:
            ax.axvspan(s, e, alpha=0.14, color='#4472C4', zorder=0)

    # Umbrales por período como líneas escalonadas/segmentadas
    xs = df['tplot'].astype(float).to_numpy()
    periods = df['Período'].astype(str).to_numpy()
    sys_thr = np.array([thr['nocturno']['sys'] if p == 'Nocturno' else thr['diurno']['sys'] for p in periods])
    dia_thr = np.array([thr['nocturno']['dia'] if p == 'Nocturno' else thr['diurno']['dia'] for p in periods])

    ax = axes[0]
    ax.plot(xs, df['PAS'], color='#C00000', lw=1.8, marker='o', ms=3, label='PAS', zorder=3)
    ax.plot(xs, df['PAD'], color='#0070C0', lw=1.8, marker='s', ms=3, label='PAD', zorder=3)
    ax.step(xs, sys_thr, where='mid', color='#C00000', ls='--', lw=1.1, alpha=0.75,
            label='Umbral sistólico según período')
    ax.step(xs, dia_thr, where='mid', color='#0070C0', ls='--', lw=1.1, alpha=0.75,
            label='Umbral diastólico según período')

    noc_patch = mpatches.Patch(color='#4472C4', alpha=0.25, label='Período nocturno')
    handles, labels = ax.get_legend_handles_labels()
    ax.legend(handles+[noc_patch], labels+['Período nocturno'], loc='upper right',
              fontsize=7, ncol=3, framealpha=0.85)
    ax.set_ylabel('Presión arterial (mmHg)', fontsize=9)
    ax.set_title('Monitoreo Ambulatorio de Presión Arterial – lecturas válidas depuradas', fontsize=11, fontweight='bold')
    ymin = max(30, min(df['PAD'].min() - 15, 50))
    ymax = min(250, max(df['PAS'].max() + 20, 170))
    ax.set_ylim(ymin, ymax)
    ax.grid(True, alpha=0.28)
    _fmt_x(ax, df)

    ax2 = axes[1]
    if 'FC' in df.columns and not df['FC'].isna().all():
        ax2.plot(xs, df['FC'], color='#00A651', lw=1.8, marker='^', ms=3, label='FC (lpm)', zorder=3)
        ax2.set_ylabel('Frecuencia cardíaca (lpm)', fontsize=9)
        ax2.set_title('Frecuencia cardíaca – 24 h', fontsize=11, fontweight='bold')
        ax2.legend(loc='upper right', fontsize=8)
        ymin2 = max(25, min(df['FC'].dropna().min() - 15, 40))
        ymax2 = min(180, max(df['FC'].dropna().max() + 20, 120))
        ax2.set_ylim(ymin2, ymax2)
        ax2.grid(True, alpha=0.28)
        _fmt_x(ax2, df)
    else:
        ax2.text(0.5, 0.5, 'Frecuencia cardíaca no disponible', ha='center', va='center', transform=ax2.transAxes)
        ax2.set_axis_off()

    fig.patch.set_facecolor('white')
    buf = io.BytesIO()
    fig.savefig(buf, format='PNG', dpi=110)
    buf.seek(0)
    plt.close(fig)
    return buf


def _noc_segments_plot(df):
    segs, in_noc, start, last = [], False, None, None
    for _, row in df.iterrows():
        x = float(row['tplot'])
        if row['Período'] == 'Nocturno':
            if not in_noc:
                start = x
                in_noc = True
        else:
            if in_noc:
                end = last if last is not None else x
                segs.append((start, end))
                in_noc = False
        last = x
    if in_noc and start is not None:
        segs.append((start, float(df['tplot'].max())))
    return segs


def _fmt_x(ax, df):
    if 'tplot' not in df.columns:
        return
    x = df['tplot'].astype(float)
    mn, mx = float(x.min()), float(x.max())
    if mx <= mn:
        return
    # ticks cada 2 h, con hora real del registro más cercana
    step = 120
    ticks = list(np.arange(0, mx + step, step))
    labels = []
    for t in ticks:
        idx = (x - t).abs().idxmin()
        lab = str(df.loc[idx, 'hora_label'] if 'hora_label' in df.columns else df.loc[idx, 'hora'])
        labels.append(lab[:5])
    ax.set_xlim(mn - 10, mx + 10)
    ax.set_xticks(ticks)
    ax.set_xticklabels(labels, rotation=45, fontsize=7)
    ax.set_xlabel('Hora del registro', fontsize=9)

class HorizontalRule(Flowable):
    def __init__(self, width, thickness=0.5, color=colors.HexColor('#1F3864')):
        self.width = width; self.thickness = thickness; self.line_color = color
    def draw(self):
        self.canv.setStrokeColor(self.line_color)
        self.canv.setLineWidth(self.thickness)
        self.canv.line(0, 0, self.width, 0)
    def wrap(self, *args):
        return (self.width, self.thickness + 2)

def _styles():
    base_font = 'Helvetica'
    bold_font = 'Helvetica-Bold'
    s = {}
    s['title'] = ParagraphStyle('T', fontName=bold_font, fontSize=13, leading=18,
                                  alignment=TA_CENTER, spaceAfter=2, textColor=colors.HexColor('#1F3864'))
    s['subtitle'] = ParagraphStyle('Sub', fontName=base_font, fontSize=9, leading=12,
                                    alignment=TA_CENTER, spaceAfter=1, textColor=colors.HexColor('#2F5496'))
    s['heading'] = ParagraphStyle('H', fontName=bold_font, fontSize=10, leading=14,
                                   spaceBefore=8, spaceAfter=3, textColor=colors.HexColor('#1F3864'))
    s['body'] = ParagraphStyle('B', fontName=base_font, fontSize=10, leading=14,
                                alignment=TA_JUSTIFY)
    s['bold_body'] = ParagraphStyle('BB', fontName=bold_font, fontSize=10, leading=14,
                                     alignment=TA_JUSTIFY)
    s['conclusion'] = ParagraphStyle('C', fontName=bold_font, fontSize=10, leading=15,
                                      alignment=TA_JUSTIFY, spaceBefore=4, spaceAfter=4,
                                      textColor=colors.black)
    s['small'] = ParagraphStyle('Sm', fontName=base_font, fontSize=8, leading=11,
                                  alignment=TA_JUSTIFY, textColor=colors.HexColor('#444444'))
    s['center'] = ParagraphStyle('Cn', fontName=base_font, fontSize=10, leading=14,
                                   alignment=TA_CENTER)
    s['tbl_hdr'] = ParagraphStyle('TH', fontName=bold_font, fontSize=9, leading=11,
                                   alignment=TA_CENTER)
    s['tbl_cell'] = ParagraphStyle('TC', fontName=base_font, fontSize=9, leading=11,
                                    alignment=TA_CENTER)
    return s

def _tbl_style_base(has_header=True):
    cmd = [
        ('GRID',       (0,0),(-1,-1), 0.4, colors.HexColor('#CCCCCC')),
        ('FONT',       (0,0),(-1,-1), 'Helvetica', 9),
        ('ROWBACKGROUNDS',(0,0),(-1,-1),[colors.white, colors.HexColor('#F5F8FF')]),
        ('ALIGN',      (0,0),(-1,-1), 'CENTER'),
        ('VALIGN',     (0,0),(-1,-1), 'MIDDLE'),
        ('LEFTPADDING',(0,0),(-1,-1), 4),
        ('RIGHTPADDING',(0,0),(-1,-1), 4),
        ('TOPPADDING', (0,0),(-1,-1), 3),
        ('BOTTOMPADDING',(0,0),(-1,-1), 3),
    ]
    if has_header:
        cmd += [
            ('BACKGROUND',(0,0),(-1,0), colors.HexColor('#1F3864')),
            ('TEXTCOLOR', (0,0),(-1,0), colors.white),
            ('FONT',      (0,0),(-1,0), 'Helvetica-Bold', 9),
        ]
    return TableStyle(cmd)

def _page_template(canv, doc):
    """Footer for all pages."""
    canv.saveState()
    canv.setFont('Helvetica', 7)
    canv.setFillColor(colors.HexColor('#888888'))
    canv.drawCentredString(PAGE_W/2, 12*mm,
        f"{INSTITUTION}  ·  {INSTITUTION_ADDR}  ·  Tel: (0221) 427-1190")
    canv.drawRightString(PAGE_W - MAR_R, 12*mm, f"Página {doc.page}")
    canv.restoreState()

def generate_pdf(df, m, pat, stu, phenotype, logo_bytes, firma_bytes, excluded):
    buf = io.BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=A4,
                             leftMargin=MAR_L, rightMargin=MAR_R,
                             topMargin=MAR_T, bottomMargin=MAR_B,
                             title=f"MAPA – {pat.get('nombre','Paciente')}",
                             author=DOCTOR_NAME)
    s = _styles()
    story = []

    # ── PAGE 1 ──────────────────────────────────────────────────────────────
    story += _page1(m, pat, stu, phenotype, logo_bytes, firma_bytes, excluded, s)
    story.append(PageBreak())

    # ── PAGE 2+ ─────────────────────────────────────────────────────────────
    story += _page2plus(df, m, pat, phenotype, s)

    doc.build(story, onFirstPage=_page_template, onLaterPages=_page_template)
    buf.seek(0)
    return buf

# ─── PAGE 1 ──────────────────────────────────────────────────────────────────
def _page1(m, pat, stu, phenotype, logo_bytes, firma_bytes, excluded, s):
    story = []

    # ─ Logo + Header ─
    logo_w = 3.5*cm
    logo_h = 2.0*cm

    if logo_bytes:
        logo_img = RLImage(io.BytesIO(logo_bytes), width=logo_w, height=logo_h)
    else:
        logo_img = Spacer(logo_w, logo_h)

    header_text = [
        Paragraph("MONITOREO AMBULATORIO DE PRESIÓN ARTERIAL (M.A.P.A.)", s['title']),
        Paragraph(f"<b>{DOCTOR_NAME}</b> – {DOCTOR_SUBTITLE}", s['subtitle']),
        Paragraph(DOCTOR_SPEC, s['small']),
    ]

    header_tbl = Table(
        [[logo_img, header_text]],
        colWidths=[logo_w + 0.3*cm, CONTENT_W - logo_w - 0.3*cm],
        style=TableStyle([
            ('VALIGN', (0,0),(-1,-1), 'MIDDLE'),
            ('LEFTPADDING', (0,0),(0,0), 0),
            ('RIGHTPADDING',(0,0),(0,0), 6),
            ('TOPPADDING',  (0,0),(-1,-1), 0),
            ('BOTTOMPADDING',(0,0),(-1,-1), 0),
        ])
    )
    story.append(header_tbl)
    story.append(Spacer(1, 4))
    story.append(HorizontalRule(CONTENT_W, thickness=1.2))
    story.append(Spacer(1, 6))

    # ─ Datos personales y del estudio (lado a lado) ─
    is_ped = pat.get('is_pediatric', False)
    edad_str = f"{pat.get('edad','–')} años"
    if is_ped:
        edad_str += " (POBLACIÓN PEDIÁTRICA)"

    personal = [
        ['DATOS PERSONALES', ''],
        ['Paciente:',  pat.get('nombre','–')],
        ['Edad / Sexo:', f"{edad_str} / {pat.get('sexo','–')}"],
        ['Obra Social:',  pat.get('obra_social','–')],
        ['Motivo:',       pat.get('motivo','–')],
        ['Solicitante:',  pat.get('solicitante','–')],
    ]
    estudio = [
        ['DATOS DEL ESTUDIO', ''],
        ['Fecha:',          stu.get('fecha','–')],
        ['Inicio / Fin:',   f"{stu.get('inicio','–')} / {stu.get('fin','–')}"],
        ['Duración efectiva:', stu.get('duracion','–')],
        ['Dispositivo:',    stu.get('dispositivo','–')],
        ['Manguito:',       stu.get('manguito','–')],
        ['Lecturas válidas:', f"{m.get('n_total',0)} ({stu.get('pct_validas','–')}% válidas)"],
    ]
    if excluded > 0:
        estudio.append(['Lecturas excluidas:', str(excluded)])

    def _data_tbl(data):
        ts = TableStyle([
            ('SPAN',        (0,0),(1,0)),
            ('BACKGROUND',  (0,0),(1,0), colors.HexColor('#1F3864')),
            ('TEXTCOLOR',   (0,0),(1,0), colors.white),
            ('FONT',        (0,0),(1,0), 'Helvetica-Bold', 9),
            ('FONT',        (0,1),(-1,-1), 'Helvetica', 9),
            ('FONT',        (0,1),(0,-1), 'Helvetica-Bold', 9),
            ('GRID',        (0,0),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
            ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white, colors.HexColor('#F5F8FF')]),
            ('ALIGN',       (0,0),(-1,-1), 'LEFT'),
            ('VALIGN',      (0,0),(-1,-1), 'MIDDLE'),
            ('LEFTPADDING', (0,0),(-1,-1), 4),
            ('RIGHTPADDING',(0,0),(-1,-1), 4),
            ('TOPPADDING',  (0,0),(-1,-1), 2),
            ('BOTTOMPADDING',(0,0),(-1,-1), 2),
            ('ALIGN',       (0,0),(1,0), 'CENTER'),
        ])
        return Table(data, colWidths=[3.5*cm, None], style=ts)

    half = (CONTENT_W - 0.4*cm) / 2
    dual = Table(
        [[_data_tbl(personal), _data_tbl(estudio)]],
        colWidths=[half, half],
        style=TableStyle([
            ('VALIGN',(0,0),(-1,-1),'TOP'),
            ('LEFTPADDING',(0,0),(0,0),0),
            ('RIGHTPADDING',(0,0),(0,0),5),
            ('LEFTPADDING',(1,0),(1,0),5),
            ('RIGHTPADDING',(1,0),(1,0),0),
        ])
    )
    story.append(dual)
    story.append(Spacer(1, 8))

    # ─ Tabla de promedios ─
    story.append(Paragraph("RESULTADOS – PROMEDIOS", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.5))
    story.append(Spacer(1, 4))

    # Pediatric thresholds note
    if is_ped:
        ps = m.get('ped_thr_sys','–'); pd_ = m.get('ped_thr_dia','–')
        story.append(Paragraph(
            f"<b>Nota:</b> Población pediátrica – umbrales de HTA: PAS ≥{ps} / PAD ≥{pd_} mmHg "
            f"(ajustados por edad/sexo/talla según guías ESH 2016 / AAP 2017).", s['small']))
        story.append(Spacer(1, 3))

    avg_data = [
        ['Parámetro', '24 horas', 'Diurno', 'Nocturno'],
    ]
    thr = m.get('thresholds', THRESHOLDS)
    for param, col in [('PAS (mmHg)','PAS'),('PAD (mmHg)','PAD'),
                        ('PAM (mmHg)','PAM'),('PP (mmHg)','PP'),('FC (lpm)','FC')]:
        row = [param]
        for p in ['24h','diurno','nocturno']:
            v = m.get(f'{col}_{p}')
            row.append(safe(v,1,' mmHg' if col!='FC' else ' lpm'))
        avg_data.append(row)

    # Add DE/CV
    avg_data.append(['DE PAS/PAD (24h)',
                      f"{safe(m.get('PAS_DE_24h'))} / {safe(m.get('PAD_DE_24h'))} mmHg", '', ''])
    avg_data.append(['CV PAS/PAD (24h)',
                      f"{safe(m.get('PAS_CV_24h'))} / {safe(m.get('PAD_CV_24h'))} %", '', ''])

    avg_tbl = Table(avg_data, colWidths=[4.5*cm, None, None, None])
    avg_ts = _tbl_style_base()
    avg_ts.add('SPAN',(1,-2),(3,-2)); avg_ts.add('SPAN',(1,-1),(3,-1))
    avg_tbl.setStyle(avg_ts)
    story.append(avg_tbl)
    story.append(Spacer(1, 8))

    # ─ Conclusión ejecutiva (bold, mayúsculas, justificado, Arial 10) ─
    story.append(HorizontalRule(CONTENT_W, thickness=1.2))
    story.append(Spacer(1, 4))
    story.append(Paragraph("CONCLUSIÓN EJECUTIVA", s['heading']))

    dip_txt = m.get('dip_pattern','NO DISPONIBLE').upper()
    aasi_v  = m.get('aasi')
    aasi_i  = m.get('aasi_interp','NO DISPONIBLE').upper()
    pp_i    = m.get('pp_interp','NO DISPONIBLE').upper()
    ms_v    = m.get('morning_surge')
    ms_m    = m.get('morning_surge_method','')

    # Main conclusion paragraph (bold, uppercase, justified)
    conc_lines = []
    conc_lines.append(f"FENOTIPO HIPERTENSIVO: {phenotype.upper()}.")
    conc_lines.append(f"PATRÓN DE DESCENSO NOCTURNO: {dip_txt}"
                      f" (PAS: {safe(m.get('dip_sys'),'1','%')} / PAD: {safe(m.get('dip_dia'),'1','%')}).")
    conc_lines.append(f"PRESIÓN DE PULSO (PP) PROMEDIO 24 H: {safe(m.get('PP_24h'),'1')} MMHG – {pp_i}.")
    conc_lines.append(f"ÍNDICE DE RIGIDEZ ARTERIAL AMBULATORIO (AASI): "
                      f"{safe(aasi_v,'2')} – {aasi_i}.")
    ms_str = f"{safe(ms_v,'1')} MMHG ({ms_m.upper()})" if ms_v is not None else ms_m.upper()
    conc_lines.append(f"MORNING SURGE: {ms_str}.")

    for line in conc_lines:
        story.append(Paragraph(line, s['conclusion']))

    story.append(Spacer(1, 6))

    # ─ Descripción de métricas (valores numéricos en negrita) ─
    story.append(Paragraph("CARGAS TENSIONALES", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.5))
    story.append(Spacer(1, 3))

    # Cargas table
    carg_data = [
        ['Indicador', 'Sistólica', 'Diastólica', 'Total'],
        ['Carga 24 h (%)',
         safe(m.get('carga_sys_24h'),'1','%'),
         safe(m.get('carga_dia_24h'),'1','%'),
         safe(m.get('carga_total_24h'),'1','%')],
        ['Carga Diurna (%)',
         safe(m.get('carga_sys_diurno'),'1','%'),
         safe(m.get('carga_dia_diurno'),'1','%'),
         safe(m.get('carga_total_diurno'),'1','%')],
        ['Carga Nocturna (%)',
         safe(m.get('carga_sys_nocturno'),'1','%'),
         safe(m.get('carga_dia_nocturno'),'1','%'),
         safe(m.get('carga_total_nocturno'),'1','%')],
    ]
    carg_tbl = Table(carg_data, colWidths=[5*cm, None, None, None])
    carg_tbl.setStyle(_tbl_style_base())
    story.append(carg_tbl)
    story.append(Spacer(1, 4))

    # Thresholds note
    t = thr
    story.append(Paragraph(
        f"<i>Umbrales: 24 h ≥{t['24h']['sys']}/{t['24h']['dia']} mmHg · "
        f"Diurno ≥{t['diurno']['sys']}/{t['diurno']['dia']} mmHg · "
        f"Nocturno ≥{t['nocturno']['sys']}/{t['nocturno']['dia']} mmHg</i>",
        s['small']))
    story.append(Spacer(1, 8))

    # Variability
    story.append(Paragraph("VARIABILIDAD", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.5))
    story.append(Spacer(1, 3))

    de_s = m.get('PAS_DE_24h'); de_d = m.get('PAD_DE_24h')
    cv_s = m.get('PAS_CV_24h'); cv_d = m.get('PAD_CV_24h')
    flag_s = " <b>[ELEVADA &gt;15%]</b>" if m.get('PAS_DE_elevated') else ""
    flag_d = " <b>[ELEVADA &gt;15%]</b>" if m.get('PAD_DE_elevated') else ""

    story.append(Paragraph(
        f"Desvío estándar PAS 24 h: <b>{safe(de_s,'1')} mmHg</b>{flag_s}   "
        f"| Desvío estándar PAD 24 h: <b>{safe(de_d,'1')} mmHg</b>{flag_d}",
        s['body']))
    story.append(Paragraph(
        f"Coeficiente de variación PAS 24 h: <b>{safe(cv_s,'1')} %</b>   "
        f"| Coeficiente de variación PAD 24 h: <b>{safe(cv_d,'1')} %</b>",
        s['body']))
    story.append(Paragraph(
        f"Varianza^0.5 PAS: <b>{safe(m.get('PAS_var05'),'2')}</b>   "
        f"| Varianza^0.5 PAD: <b>{safe(m.get('PAD_var05'),'2')}</b>",
        s['body']))
    story.append(Spacer(1, 8))

    # ─ Firma ─
    if firma_bytes:
        firma_img = RLImage(io.BytesIO(firma_bytes), width=5*cm, height=3*cm,
                            kind='proportional')
        firma_tbl = Table([[firma_img]], colWidths=[CONTENT_W],
                          style=TableStyle([('ALIGN',(0,0),(-1,-1),'RIGHT'),
                                            ('RIGHTPADDING',(0,0),(-1,-1),0)]))
        story.append(firma_tbl)
    else:
        story.append(Spacer(1, 28))
        story.append(Paragraph(
            f"<b>Dr. {DOCTOR_NAME}</b><br/>{DOCTOR_TITLE}<br/>"
            f"Especialista Universitario en Cardiología<br/>{DOCTOR_MP}",
            ParagraphStyle('firma', fontName='Helvetica', fontSize=9, alignment=TA_RIGHT)))

    return story

# ─── PAGE 2+ ─────────────────────────────────────────────────────────────────
def _page2plus(df, m, pat, phenotype, s):
    story = []

    # Chart
    story.append(Paragraph("REPRESENTACIÓN GRÁFICA – PRESIÓN ARTERIAL Y FC (24 H)", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.5))
    story.append(Spacer(1, 4))
    try:
        chart_buf = generate_chart(df, m)
        chart_img = RLImage(chart_buf, width=CONTENT_W, height=CONTENT_W*0.58)
        story.append(chart_img)
    except Exception as e:
        story.append(Paragraph(f"[Gráfico no disponible: {e}]", s['small']))
    story.append(Spacer(1, 10))

    # ─ Comparación con guías ─
    story.append(Paragraph("COMPARACIÓN CON GUÍAS INTERNACIONALES", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.8))
    story.append(Spacer(1, 4))

    thr = m.get('thresholds', THRESHOLDS)
    s24  = m.get('PAS_24h','–');   d24  = m.get('PAD_24h','–')
    sDiu = m.get('PAS_diurno','–');dDiu = m.get('PAD_diurno','–')
    sNoc = m.get('PAS_nocturno','–');dNoc = m.get('PAD_nocturno','–')

    def _dx(s_val, d_val, ts, td):
        if s_val is None or d_val is None: return "No disponible"
        if s_val >= ts and d_val >= td: return "HTA SISTODIASTÓLICA"
        if s_val >= ts: return "HTA SISTÓLICA AISLADA"
        if d_val >= td: return "HTA DIASTÓLICA AISLADA"
        return "NORMOTENSIÓN"

    guide_data = [
        ['Guía', 'Umbral 24h', 'Resultado 24h', 'Umbral Diurno', 'Resultado Diurno', 'Umbral Nocturno', 'Resultado Nocturno'],
    ]
    for guide_name in ['ESC/ESH 2024', 'ACC/AHA 2025', 'Consenso Arg. FAC-SAHA-SAC 2025']:
        row = [guide_name,
               f"≥{thr['24h']['sys']}/{thr['24h']['dia']}",
               _dx(s24, d24, thr['24h']['sys'], thr['24h']['dia']),
               f"≥{thr['diurno']['sys']}/{thr['diurno']['dia']}",
               _dx(sDiu, dDiu, thr['diurno']['sys'], thr['diurno']['dia']),
               f"≥{thr['nocturno']['sys']}/{thr['nocturno']['dia']}",
               _dx(sNoc, dNoc, thr['nocturno']['sys'], thr['nocturno']['dia']),
        ]
        guide_data.append(row)

    guide_tbl = Table(guide_data,
                       colWidths=[3.2*cm, 2*cm, 3*cm, 2*cm, 3*cm, 2*cm, 3*cm])
    guide_tbl.setStyle(_tbl_style_base())
    story.append(guide_tbl)
    story.append(Spacer(1, 10))

    # ─ Conclusión médica ampliada ─
    story.append(Paragraph("CONCLUSIÓN MÉDICA AMPLIADA", s['heading']))
    story.append(HorizontalRule(CONTENT_W, thickness=0.8))
    story.append(Spacer(1, 4))

    dip = m.get('dip_pattern','NO DISPONIBLE')
    aasi = m.get('aasi')
    aasi_i = m.get('aasi_interp','')
    pp_24 = m.get('PP_24h')
    is_ped = pat.get('is_pediatric', False)

    # Build clinical interpretation
    nombre = pat.get('nombre','el/la paciente')
    edad = pat.get('edad','')
    sexo = pat.get('sexo','')

    interp_parts = []

    # 1. General
    interp_parts.append(
        f"El estudio MAPA de 24 h realizado al/a la paciente <b>{nombre}</b> "
        f"({edad} años, sexo {sexo}) es técnicamente válido, con "
        f"<b>{m.get('n_total','–')}</b> lecturas válidas y período de registro efectivo de "
        f"{pat.get('duracion_str', 'no especificado')}."
    )

    # 2. Phenotype
    norm = phenotype == "NORMOTENSIÓN AMBULATORIA"
    if norm:
        interp_parts.append(
            f"Los promedios tensionales se encuentran dentro de rangos normales según las guías internacionales vigentes "
            f"(PAS 24 h: <b>{safe(s24)} mmHg</b> / PAD 24 h: <b>{safe(d24)} mmHg</b>). "
            f"No se documenta hipertensión arterial sostenida en ningún período del registro."
        )
    else:
        interp_parts.append(
            f"Se documenta el fenotipo <b>{phenotype}</b> con promedios: "
            f"PAS/PAD 24 h: <b>{safe(s24)}/{safe(d24)} mmHg</b>, "
            f"diurno: <b>{safe(sDiu)}/{safe(dDiu)} mmHg</b>, "
            f"nocturno: <b>{safe(sNoc)}/{safe(dNoc)} mmHg</b>."
        )

    # 3. Circadian pattern
    if dip in ['EXTREME DIPPER']:
        circ = (f"El patrón circadiano es <b>{dip}</b> "
                f"(descenso nocturno PAS: <b>{safe(m.get('dip_sys'),'1')}%</b>), "
                f"lo que puede asociarse a mayor riesgo de eventos isquémicos nocturnos y debe correlacionarse con el contexto clínico.")
    elif dip in ['DIPPER']:
        circ = (f"El patrón circadiano es <b>{dip}</b> "
                f"(descenso nocturno PAS: <b>{safe(m.get('dip_sys'),'1')}%</b>), "
                f"hallazgo fisiológicamente normal, asociado a menor riesgo cardiovascular relativo.")
    elif dip in ['NON-DIPPER']:
        circ = (f"El patrón circadiano es <b>{dip}</b> "
                f"(descenso nocturno PAS: <b>{safe(m.get('dip_sys'),'1')}%</b>), "
                f"asociado a mayor riesgo cardiovascular, daño de órgano blanco y síndrome de apnea obstructiva del sueño. "
                f"Se recomienda evaluación clínica dirigida.")
    elif dip in ['REVERSE DIPPER']:
        circ = (f"El patrón circadiano es <b>{dip}</b> "
                f"(la presión nocturna supera la diurna: PAS nocturna <b>{safe(sNoc)} mmHg</b> vs. diurna <b>{safe(sDiu)} mmHg</b>). "
                f"Este patrón tiene implicancia pronóstica adversa significativa y requiere evaluación cardiológica ampliada.")
    else:
        circ = f"Patrón circadiano: <b>{dip}</b>."
    interp_parts.append(circ)

    # 4. AASI
    if aasi is not None:
        if aasi > 0.50:
            aasi_txt = (f"El índice de rigidez arterial ambulatorio (AASI) es <b>{safe(aasi,'2')}</b> ({aasi_i}), "
                        f"indicando disminución de la distensibilidad arterial con posibles cambios estructurales vasculares. "
                        f"Este hallazgo tiene valor pronóstico cardiovascular independiente.")
        elif aasi > 0.40:
            aasi_txt = (f"El AASI es <b>{safe(aasi,'2')}</b> ({aasi_i}), en zona límite. "
                        f"Se recomienda seguimiento y correlación con otros indicadores de rigidez.")
        else:
            aasi_txt = (f"El AASI es <b>{safe(aasi,'2')}</b> ({aasi_i}), dentro de rango normal.")
        interp_parts.append(aasi_txt)

    # 5. PP
    if pp_24 is not None:
        if pp_24 >= 60:
            pp_txt = (f"La presión de pulso (PP) promedio de 24 h es <b>{safe(pp_24,'1')} mmHg</b> "
                      f"(ELEVADA ≥60 mmHg), marcador de rigidez arterial y riesgo cardiovascular aumentado, "
                      f"especialmente en población mayor de 55 años.")
        else:
            pp_txt = (f"La presión de pulso (PP) promedio de 24 h es <b>{safe(pp_24,'1')} mmHg</b> "
                      f"(dentro de rango esperado <60 mmHg).")
        interp_parts.append(pp_txt)

    # 6. Variability
    de_s = m.get('PAS_DE_24h'); cv_s = m.get('PAS_CV_24h')
    if de_s and m.get('PAS_DE_elevated'):
        interp_parts.append(
            f"Se evidencia variabilidad tensional aumentada (DE PAS 24 h: <b>{safe(de_s,'1')} mmHg</b>, "
            f"CV: <b>{safe(cv_s,'1')}%</b>), con implicancias pronósticas independientes del nivel tensional promedio.")

    # 7. Suggested additional studies
    sugg = []
    if aasi and aasi > 0.40:
        sugg.append("Velocidad de Onda del Pulso (VOP) para cuantificación de rigidez arterial")
    if aasi and aasi > 0.40 or (pp_24 and pp_24 >= 60):
        sugg.append("Medición de Presión Central (presión aórtica) para valoración de post-carga central")
    if not norm or dip in ['NON-DIPPER', 'REVERSE DIPPER']:
        sugg.append("Cardiografía de Impedancia (evaluación hemodinámica no invasiva) para fenotipado hemodinámico")
    if sugg:
        sugg_str = "; ".join(sugg)
        interp_parts.append(
            f"<b>Estudios complementarios sugeridos:</b> Se sugiere complementar la evaluación con: {sugg_str}.")

    # 8. Pediatric note
    if is_ped:
        interp_parts.append(
            f"<b>Nota pediátrica:</b> La interpretación se realizó conforme a los umbrales por percentiles "
            f"de presión arterial para edad, sexo y talla según las guías ESH 2016 y AAP 2017.")

    for part in interp_parts:
        story.append(Paragraph(part, s['body']))
        story.append(Spacer(1, 4))

    story.append(Spacer(1, 12))
    story.append(Paragraph(
        "<b>REFERENCIAS:</b> ESC/ESH Guidelines for the management of arterial hypertension 2024 · "
        "ACC/AHA Hypertension Guidelines 2025 · Consenso Argentino FAC-SAHA-SAC 2025 · "
        "ESH 2016 Pediatric Hypertension Guidelines · AAP 2017 Pediatric Blood Pressure Guidelines",
        s['small']))

    return story



def _try_import_ocr_stack():
    """Carga dependencias OCR sólo cuando son necesarias."""
    try:
        import fitz  # PyMuPDF
        from PIL import Image
        import pytesseract
        return fitz, Image, pytesseract, None
    except Exception as e:
        return None, None, None, str(e)

# ─────────────────────────────────────────────────────────────────────────────
# STREAMLIT UI
# ─────────────────────────────────────────────────────────────────────────────

def main():
    # CSS
    st.markdown("""
    <style>
    .stApp { background-color: #f8f9fc; }
    .block-container { padding-top: 1.5rem; }
    h1 { color: #1F3864; }
    h2, h3 { color: #2F5496; }
    .metric-box {
        background: white;
        border-radius: 8px;
        padding: 12px 16px;
        border-left: 4px solid #1F3864;
        margin-bottom: 8px;
        box-shadow: 0 1px 3px rgba(0,0,0,0.08);
    }
    .stButton>button {
        background: #1F3864;
        color: white;
        border-radius: 6px;
        border: none;
        padding: 0.5rem 2rem;
        font-weight: bold;
        font-size: 1rem;
    }
    .stButton>button:hover { background: #2F5496; }
    </style>
    """, unsafe_allow_html=True)

    with st.sidebar:
        st.markdown("## ⚙️ Configuración automática")
        st.markdown("La carga de datos filiatorios, estudio y lecturas se realiza **desde el PDF original**.")
        st.markdown("---")
        st.markdown("**Logo institucional**")
        logo_file = st.file_uploader("Subir logo (PNG/JPG)", type=['png','jpg','jpeg'],
                                      key='logo', label_visibility='collapsed')
        st.markdown("**Firma / sello médico**")
        firma_file = st.file_uploader("Subir firma (PNG/JPG)", type=['png','jpg','jpeg'],
                                       key='firma', label_visibility='collapsed')
        st.markdown("---")
        st.markdown("**Período nocturno para filas sin etiqueta**")
        noc_start = st.number_input("Inicio nocturno (hs)", 20, 24, 23, 1)
        noc_end   = st.number_input("Fin nocturno (hs)", 4, 10, 7, 1)
        st.markdown("---")

        if st.button("♻️ Reprocesar PDF / limpiar caché", use_container_width=True):
            for k in [
                "mapa_file_hash", "df_raw", "meta", "raw_text_debug",
                "parse_error", "generated_pdf_bytes", "generated_csv_bytes",
                "generated_base_name", "generated_audio_msg", "generated_summary"
            ]:
                st.session_state.pop(k, None)
            parse_mapa_pdf_cached.clear()
            st.rerun()

        st.markdown("---")
        st.markdown(f"<small>**{DOCTOR_NAME}**<br/>{DOCTOR_TITLE}<br/>{DOCTOR_MP}</small>",
                    unsafe_allow_html=True)

        st.markdown("---")
        with st.expander("Estado OCR", expanded=False):
            fitz_mod, pil_mod, tess_mod, ocr_err = _try_import_ocr_stack()
            if ocr_err:
                st.error("OCR no disponible")
                st.code("pip install PyMuPDF Pillow pytesseract")
                st.caption(f"Detalle: {ocr_err}")
            else:
                st.success("OCR disponible")

    st.title("🫀 MAPA – Informe Médico Ambulatorio")
    st.markdown(f"*{DOCTOR_SUBTITLE}*")
    st.markdown("---")

    st.subheader("1. Cargar PDF original del equipo MAPA")
    pdf_file = st.file_uploader("Subir PDF del dispositivo MAPA", type=['pdf'], key='mapa_pdf')

    if not pdf_file:
        st.info("Subí el PDF original del MAPA. La app importará automáticamente datos filiatorios, datos del estudio y lecturas.")
        return

    file_bytes = pdf_file.getvalue()
    file_hash = hashlib.sha256(file_bytes).hexdigest()

    # Parse automático, pero sólo si cambió el archivo. Evita reruns lentos.
    if st.session_state.get("mapa_file_hash") != file_hash:
        for k in [
            "df_raw", "meta", "raw_text_debug", "parse_error",
            "generated_pdf_bytes", "generated_csv_bytes",
            "generated_base_name", "generated_audio_msg", "generated_summary"
        ]:
            st.session_state.pop(k, None)

        with st.spinner("Importando automáticamente datos del PDF original. El primer procesamiento puede tardar por OCR..."):
            df_raw, meta_or_err, raw_text_debug = parse_mapa_pdf_cached(file_bytes)

        st.session_state["mapa_file_hash"] = file_hash
        st.session_state["raw_text_debug"] = raw_text_debug

        if df_raw is None:
            st.session_state["parse_error"] = meta_or_err
        else:
            st.session_state["df_raw"] = df_raw
            st.session_state["meta"] = meta_or_err if isinstance(meta_or_err, dict) else {}
            st.session_state["parse_error"] = None

    # Manejo de errores de importación
    if st.session_state.get("parse_error"):
        meta_or_err = st.session_state.get("parse_error")
        raw_text_debug = st.session_state.get("raw_text_debug", "")
        is_gen = "⚠️ El PDF cargado es un INFORME YA GENERADO" in str(meta_or_err)
        if is_gen:
            st.warning(meta_or_err)
            st.info(
                "**¿Qué PDF necesita la app?** El PDF ORIGINAL del equipo MAPA (MedicalDB 17.7 u otro). "
                "Es el archivo que genera el propio monitor de presión, antes de ser procesado. "
                "Contiene la Tabla Completa con cada lectura individual hora a hora."
            )
        else:
            st.error("No se pudo importar automáticamente el PDF.")
            st.warning(meta_or_err)
            with st.expander("Diagnóstico técnico"):
                st.text_area("Texto/OCR obtenido", raw_text_debug[:6000] if raw_text_debug else "", height=250)
                st.markdown("""
                Para PDFs escaneados se requiere OCR instalado.  
                **Local:** `pip install PyMuPDF Pillow pytesseract` y Tesseract OCR instalado en el sistema.  
                **Streamlit Cloud:** subir `requirements.txt` y `packages.txt` junto con la app.
                """)
        return

    df_raw = st.session_state.get("df_raw")
    meta = st.session_state.get("meta", {})

    if df_raw is None or len(df_raw) == 0:
        st.error("No hay lecturas importadas.")
        return

    st.success(f"✅ Importación automática completa: {len(df_raw)} lecturas crudas detectadas desde la Tabla Completa.")

    # Autocompletar datos filiatorios / estudio
    nombre_default = meta.get("paciente", "NO ESPECIFICADO")
    try:
        edad_default = int(meta.get("edad", 50))
    except Exception:
        edad_default = 50
    if edad_default < 0 or edad_default > 120:
        edad_default = 50

    sexo_default = meta.get("sexo", "No especificado")
    obra_social_default = meta.get("obra_social", "")
    solicitante_default = meta.get("solicitante", "–")
    motivo_default = meta.get("motivo", "–")
    fecha_default = meta.get("fecha_inicio", datetime.now().strftime("%d/%m/%Y"))
    hora_inicio_default = meta.get("hora_inicio", df_raw["hora"].iloc[0] if "hora" in df_raw.columns else "–")
    hora_fin_default = meta.get("hora_fin", df_raw["hora"].iloc[-1] if "hora" in df_raw.columns else "–")
    dispositivo_default = meta.get("dispositivo", "No especificado")
    manguito_default = meta.get("manguito", "No especificado")
    dur_str_default = meta.get("duracion_str", meta.get("duracion", "No especificado"))

    st.subheader("2. Datos importados automáticamente")
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Paciente", nombre_default[:28])
    c2.metric("Edad / sexo", f"{edad_default} / {sexo_default}")
    c3.metric("Obra social", obra_social_default[:24])
    c4.metric("Fecha", fecha_default)

    c5, c6, c7, c8 = st.columns(4)
    c5.metric("Inicio", hora_inicio_default)
    c6.metric("Fin", hora_fin_default)
    c7.metric("Duración", dur_str_default)
    c8.metric("Dispositivo", dispositivo_default[:24])

    with st.expander("Vista previa de lecturas importadas", expanded=False):
        st.dataframe(df_raw, use_container_width=True)

    _faltan_datos = (sexo_default == "No especificado" or not str(obra_social_default).strip())
    if _faltan_datos:
        st.warning("⚠️ Sexo y/u obra social no figuran en el PDF — completar manualmente antes de generar.")

    st.markdown("---")
    st.subheader("3. Completar/corregir y generar")

    # Formulario: evita reruns en cada edición de campo.
    with st.form("form_generar_mapa", clear_on_submit=False):
        st.caption("Los cambios en estos campos no reprocesan el PDF hasta presionar el botón de generación.")
        nombre = st.text_input("Nombre y apellido", value=nombre_default)
        cc1, cc2, cc3 = st.columns(3)
        edad_val = cc1.number_input("Edad", min_value=0, max_value=120, value=int(edad_default), step=1)
        sexo = cc2.selectbox(
            "Sexo",
            ["Masculino", "Femenino", "No especificado"],
            index=(0 if sexo_default == "Masculino" else 1 if sexo_default == "Femenino" else 2)
        )
        obra_social = cc3.text_input("Obra social", value=obra_social_default)
        solicitante = st.text_input("Solicitante", value=solicitante_default)
        motivo = st.text_input("Motivo", value=motivo_default)
        f1, f2, f3 = st.columns(3)
        fecha_estudio = f1.text_input("Fecha estudio", value=fecha_default)
        hora_inicio = f2.text_input("Hora inicio", value=hora_inicio_default)
        hora_fin = f3.text_input("Hora fin", value=hora_fin_default)
        d1, d2 = st.columns(2)
        dispositivo = d1.text_input("Dispositivo", value=dispositivo_default)
        manguito = d2.text_input("Manguito", value=manguito_default)

        generate = st.form_submit_button("⚕️ Calcular todo y generar informe PDF", use_container_width=True)

    if generate:
        with st.spinner("Depurando lecturas, recalculando métricas y generando informe..."):
            df_work = df_raw.copy()

            # Si el parser trae períodos desde la tabla, se respetan; si faltan, se asignan por horario.
            if "Período" not in df_work.columns or df_work["Período"].isna().all():
                df_work = assign_periods(df_work, noc_start=int(noc_start), noc_end=int(noc_end))
            else:
                tmp = assign_periods(df_work.drop(columns=["Período"], errors="ignore"),
                                     noc_start=int(noc_start), noc_end=int(noc_end))
                df_work["Período"] = df_work["Período"].fillna(tmp["Período"])
                df_work["Período"] = df_work["Período"].replace("", np.nan).fillna(tmp["Período"])
                df_work["periodo_asumido"] = False

            df_clean, excluded, n_orig = clean_data(df_work)

            if len(df_clean) < 20:
                st.error(f"Quedan sólo {len(df_clean)} lecturas válidas tras depuración. Revisar OCR/tabla. No se genera informe con una tabla incompleta.")
                return

            if meta.get("pct_validas_pdf"):
                pct_val = meta.get("pct_validas_pdf")
            else:
                pct_val = round(len(df_clean) / n_orig * 100, 1) if n_orig else "–"

            is_ped = int(edad_val) < 17
            sex_code = "F" if "Fem" in sexo else "M"
            m = calculate_metrics(df_clean, age=edad_val if is_ped else None,
                                  is_ped=is_ped, sex=sex_code, height=None)
            phenotype = classify_phenotype(m)

            pat_info = {
                "nombre": nombre,
                "edad": str(int(edad_val)),
                "sexo": sexo,
                "obra_social": obra_social,
                "solicitante": solicitante or "–",
                "motivo": motivo or "–",
                "is_pediatric": is_ped,
                "duracion_str": dur_str_default,
            }
            stu_info = {
                "fecha": fecha_estudio,
                "inicio": hora_inicio,
                "fin": hora_fin,
                "duracion": dur_str_default,
                "dispositivo": dispositivo,
                "manguito": manguito,
                "pct_validas": str(pct_val),
            }

            logo_bytes = img_to_bytes(logo_file) if logo_file else img_to_bytes("/mnt/data/logo IPENSA.png")
            firma_bytes = img_to_bytes(firma_file) if firma_file else img_to_bytes("/mnt/data/FIRMA PNG.png")

            pdf_buf = generate_pdf(df_clean, m, pat_info, stu_info, phenotype,
                                   logo_bytes, firma_bytes, excluded)

            nombre_clean = re.sub(r"[^A-Za-z0-9]", "_", (nombre or "Paciente").upper())
            fecha_clean = str(fecha_estudio).replace("/", "-")
            os_clean = re.sub(r"[^A-Za-z0-9]", "_", (obra_social or "SinOS").upper())
            base_name = f"{nombre_clean}_{fecha_clean}_MAPA_{os_clean}"

            csv_io = io.StringIO()
            df_clean.to_csv(csv_io, index=False, encoding="utf-8-sig")

            audio_msg = f"ESTUDIO MAPA INFORMADO DE {(nombre or 'PACIENTE').upper()}, {fecha_estudio}, {(obra_social or 'SIN OBRA SOCIAL').upper()}"

            st.session_state["generated_pdf_bytes"] = pdf_buf.getvalue()
            st.session_state["generated_csv_bytes"] = csv_io.getvalue().encode("utf-8-sig")
            st.session_state["generated_base_name"] = base_name
            st.session_state["generated_audio_msg"] = audio_msg
            st.session_state["generated_summary"] = {
                "phenotype": phenotype,
                "dip_pattern": m.get("dip_pattern", "-"),
                "aasi": safe(m.get("aasi"), "2") + " - " + str(m.get("aasi_interp", "-")),
                "pp24": f"{safe(m.get('PP_24h'), '1')} mmHg",
                "pas24": f"{safe(m.get('PAS_24h'), '1')}/{safe(m.get('PAD_24h'), '1')} mmHg",
                "pas_day": f"{safe(m.get('PAS_diurno'), '1')}/{safe(m.get('PAD_diurno'), '1')} mmHg",
                "pas_night": f"{safe(m.get('PAS_nocturno'), '1')}/{safe(m.get('PAD_nocturno'), '1')} mmHg",
                "used": f"{len(df_clean)} / {n_orig}",
                "excluded": excluded,
            }

    # Mostrar resultado persistente tras generar.
    if st.session_state.get("generated_pdf_bytes"):
        summary = st.session_state.get("generated_summary", {})
        st.markdown("---")
        st.subheader("📊 Resumen recalculado desde lecturas del PDF")

        col_a, col_b, col_c, col_d = st.columns(4)
        col_a.metric("Fenotipo", summary.get("phenotype", "-")[:25])
        col_b.metric("Patrón circadiano", summary.get("dip_pattern", "-"))
        col_c.metric("AASI", summary.get("aasi", "-")[:25])
        col_d.metric("PP 24h", summary.get("pp24", "-"))

        col_e, col_f, col_g, col_h = st.columns(4)
        col_e.metric("PAS/PAD 24h", summary.get("pas24", "-"))
        col_f.metric("PAS/PAD Diurno", summary.get("pas_day", "-"))
        col_g.metric("PAS/PAD Nocturno", summary.get("pas_night", "-"))
        col_h.metric("Lecturas usadas", summary.get("used", "-"))

        if summary.get("excluded", 0) > 0:
            st.info(f"{summary.get('excluded')} medición(es) fueron excluidas durante la depuración de datos.")

        base_name = st.session_state["generated_base_name"]
        st.download_button(
            label="Descargar informe PDF",
            data=st.session_state["generated_pdf_bytes"],
            file_name=f"{base_name}.pdf",
            mime="application/pdf",
            use_container_width=True
        )
        st.download_button(
            label="Descargar lecturas depuradas CSV",
            data=st.session_state["generated_csv_bytes"],
            file_name=f"{base_name}_lecturas_depuradas.csv",
            mime="text/csv",
            use_container_width=True
        )

        audio_msg = st.session_state["generated_audio_msg"]
        st.markdown(f"""
        <div style="margin-top:1rem;padding:0.8rem 1rem;background:#e8f0fe;border-radius:8px;
                    border-left:4px solid #1F3864;font-family:Arial;font-size:1rem;font-weight:bold;">
            {audio_msg}
        </div>
        <script>
        setTimeout(function(){{
            if('speechSynthesis' in window){{
                var msg=new SpeechSynthesisUtterance("{audio_msg}");
                msg.lang='es-AR'; msg.rate=0.9; msg.volume=1;
                window.speechSynthesis.speak(msg);
            }}
        }},1200);
        </script>
        """, unsafe_allow_html=True)
        st.success(f"Informe generado: {base_name}.pdf")
        st.caption(audio_msg)

if __name__ == '__main__':
    main()
