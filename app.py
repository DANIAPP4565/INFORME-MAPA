#!/usr/bin/env python3
"""
MAPA Informe Médico – App Streamlit
Dr. Ricardo Daniel Olano | Cardiólogo – IPENSA La Plata
Versión 2.0 – 2026
"""

# ─────────────────────────────────────────────────────────────────────────────
# IMPORTS
# ─────────────────────────────────────────────────────────────────────────────
import streamlit as st
import pandas as pd
import numpy as np
import pdfplumber
import io, base64, os, re, warnings
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

def parse_mapa_pdf(pdf_file):
    """Returns (df, metadata_dict, raw_text) or (None, error_str, raw_text)."""
    raw_text = ""
    try:
        with pdfplumber.open(pdf_file) as pdf:
            pages_text = []
            all_tables = []
            # Extract with different settings for each page
            for p in pdf.pages:
                # Try standard extraction
                t = p.extract_text()
                if t:
                    pages_text.append(t)
                # Try with x_tolerance adjustments
                if not t or len(t) < 50:
                    t2 = p.extract_text(x_tolerance=5, y_tolerance=5)
                    if t2:
                        pages_text.append(t2)
                # Tables
                for ts in [
                    {},
                    {'vertical_strategy':'lines','horizontal_strategy':'lines'},
                    {'vertical_strategy':'text','horizontal_strategy':'text'},
                    {'vertical_strategy':'explicit','horizontal_strategy':'explicit',
                     'explicit_vertical_lines':[],'explicit_horizontal_lines':[]},
                ]:
                    try:
                        tbls = p.extract_tables(ts) if ts else p.extract_tables()
                        if tbls:
                            all_tables.extend(tbls)
                            break
                    except:
                        pass

            raw_text = "\n".join(pages_text)

        # IMPORTANTE: para el informe se ignoran los datos/resúmenes del PDF original.
        # Sólo se usan lecturas crudas de la tabla completa o lecturas válidas.
        raw_readings_text = _isolate_lecturas_validas_text(raw_text)

        # Strategy 1: aggressive text parsing sobre la tabla de lecturas crudas
        df = _parse_from_text_v2(raw_readings_text)
        # Strategy 2: column-based extraction (fixed-width) sobre lecturas crudas
        if df is None or len(df) < 5:
            df3 = _parse_fixed_width(raw_readings_text)
            if df3 is not None and len(df3) > (len(df) if df is not None else 0):
                df = df3
        # Strategy 3: table extraction como respaldo, sin usar estadísticas/promedios
        if df is None or len(df) < 5:
            df_tbl = _parse_from_tables(all_tables)
            if df_tbl is not None and len(df_tbl) > (len(df) if df is not None else 0):
                df = df_tbl

        if df is None or len(df) < 3:
            return None, "No se pudieron extraer lecturas del PDF.", raw_text

        meta = _extract_meta(raw_text)
        return df, meta, raw_text

    except Exception as e:
        return None, f"Error al procesar PDF: {e}", raw_text

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

def _extract_meta(text):
    meta = {}
    for pat in [r'Paciente[:\s]+([A-ZÁÉÍÓÚÑa-záéíóúñ\s,]+)',
                r'Nombre[:\s]+([A-ZÁÉÍÓÚÑa-záéíóúñ\s,]+)']:
        m = re.search(pat, text, re.IGNORECASE)
        if m:
            meta['paciente'] = m.group(1).strip()[:60].title()
            break
    dates = re.findall(r'\d{1,2}[/\-]\d{1,2}[/\-]\d{2,4}', text)
    if dates: meta['fecha_inicio'] = dates[0]
    if len(dates) > 1: meta['fecha_fin'] = dates[1]
    for dev in ['SpaceLabs','MedicalDB','Microlife','OMRON','Schiller','Welch Allyn','A&D']:
        if dev.upper() in text.upper():
            meta['dispositivo'] = dev; break
    for sz in ['Adulto grande','Adulto estándar','Adulto pequeño','Pediátrico']:
        if sz.lower() in text.lower():
            meta['manguito'] = sz; break
    return meta


def _isolate_lecturas_validas_text(text):
    """
    Prioriza la sección de lecturas crudas/tabla completa y descarta portadas,
    estadísticas, promedios horarios y resúmenes del PDF original. Esto evita
    que el informe use promedios ya calculados por el software del equipo.
    """
    if not isinstance(text, str) or not text.strip():
        return text
    upper = text.upper()
    anchors = [
        'TABLA COMPLETA',
        'LECTURAS VÁLIDAS',
        'LECTURAS VALIDAS',
        'MEDICIONES VÁLIDAS',
        'MEDICIONES VALIDAS',
        'HORA SIS DIA',
        'FECHA HORA SIS DIA',
    ]
    positions = [upper.find(a) for a in anchors if upper.find(a) >= 0]
    if positions:
        return text[min(positions):]
    return text

# ─────────────────────────────────────────────────────────────────────────────
# DATA PROCESSING
# ─────────────────────────────────────────────────────────────────────────────
def assign_periods(df, noc_start=23, noc_end=7):
    if 'Período' not in df.columns:
        def _period(h):
            mins = time_to_minutes(h)
            if mins is None: return 'Diurno'
            hr = mins // 60
            return 'Nocturno' if (hr >= noc_start or hr < noc_end) else 'Diurno'
        df = df.copy()
        df['Período'] = df['hora'].apply(_period)
        df['periodo_asumido'] = True
    else:
        df = df.copy()
        df['Período'] = df['Período'].apply(
            lambda x: 'Nocturno' if 'noct' in str(x).lower() else 'Diurno')
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
    df['tmin'] = df['hora'].apply(time_to_minutes)
    df = df.dropna(subset=['tmin']).sort_values('tmin')

    thr = m['thresholds']
    fig, axes = plt.subplots(2, 1, figsize=(15, 9), dpi=150,
                              gridspec_kw={'hspace': 0.45})

    # ─ Nocturnal bands ─
    segs = _noc_segments(df)

    for ax in axes:
        for s, e in segs:
            ax.axvspan(s, e, alpha=0.13, color='#4472C4', zorder=0)

    # ─ Plot 1: PAS / PAD ─
    ax = axes[0]
    ax.plot(df['tmin'], df['PAS'], color='#C00000', lw=1.8,
            marker='o', ms=3, label='PAS', zorder=3)
    ax.plot(df['tmin'], df['PAD'], color='#0070C0', lw=1.8,
            marker='s', ms=3, label='PAD', zorder=3)

    # Threshold lines
    ax.axhline(thr['diurno']['sys'],  color='#C00000', ls='--', lw=1.1, alpha=0.75,
               label=f"Umbral SYS diurno ({thr['diurno']['sys']} mmHg)")
    ax.axhline(thr['diurno']['dia'],  color='#0070C0', ls='--', lw=1.1, alpha=0.75,
               label=f"Umbral DIA diurno ({thr['diurno']['dia']} mmHg)")
    ax.axhline(thr['nocturno']['sys'],color='#C00000', ls=':',  lw=1.0, alpha=0.65,
               label=f"Umbral SYS nocturno ({thr['nocturno']['sys']} mmHg)")
    ax.axhline(thr['nocturno']['dia'],color='#0070C0', ls=':',  lw=1.0, alpha=0.65,
               label=f"Umbral DIA nocturno ({thr['nocturno']['dia']} mmHg)")

    noc_patch = mpatches.Patch(color='#4472C4', alpha=0.25, label='Período nocturno')
    handles, labels = ax.get_legend_handles_labels()
    ax.legend(handles+[noc_patch], labels+['Período nocturno'],
              loc='upper right', fontsize=7, ncol=3, framealpha=0.8)

    ax.set_ylabel('Presión Arterial (mmHg)', fontsize=9)
    ax.set_title('Monitoreo Ambulatorio de Presión Arterial – 24 h', fontsize=11, fontweight='bold')
    ax.set_ylim(40, 220); ax.grid(True, alpha=0.3)
    _fmt_x(ax, df)

    # ─ Plot 2: FC ─
    ax2 = axes[1]
    if 'FC' in df.columns and not df['FC'].isna().all():
        ax2.plot(df['tmin'], df['FC'], color='#00B050', lw=1.8,
                 marker='^', ms=3, label='FC (lpm)', zorder=3)
        ax2.set_ylabel('Frecuencia Cardíaca (lpm)', fontsize=9)
        ax2.set_title('Frecuencia Cardíaca – 24 h', fontsize=11, fontweight='bold')
        ax2.legend(loc='upper right', fontsize=8)
        ax2.set_ylim(30, 150); ax2.grid(True, alpha=0.3)
        _fmt_x(ax2, df)
    else:
        ax2.set_visible(False)

    fig.patch.set_facecolor('white')
    buf = io.BytesIO()
    fig.savefig(buf, format='PNG', dpi=150, bbox_inches='tight')
    buf.seek(0); plt.close(fig)
    return buf

def _noc_segments(df):
    segs, in_noc, start = [], False, None
    for _, row in df.iterrows():
        if row['Período'] == 'Nocturno':
            if not in_noc: start = row['tmin']; in_noc = True
        else:
            if in_noc: segs.append((start, row['tmin'])); in_noc = False
    if in_noc and start is not None:
        segs.append((start, df['tmin'].max()))
    return segs

def _fmt_x(ax, df):
    mn, mx = df['tmin'].min(), df['tmin'].max()
    ticks = list(range(int(mn//60)*60, int(mx//60+2)*60, 60))
    ticks = [t for t in ticks if mn <= t <= mx]
    ax.set_xticks(ticks)
    ax.set_xticklabels([f"{(t//60)%24:02d}:00" for t in ticks], rotation=45, fontsize=7)
    ax.set_xlabel('Hora del día', fontsize=9)

# ─────────────────────────────────────────────────────────────────────────────
# PDF REPORT GENERATION
# ─────────────────────────────────────────────────────────────────────────────
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

    # ─ Sidebar ─
    with st.sidebar:
        st.image("https://i.imgur.com/8X8X8X8.png", width=60) if False else None
        st.markdown("## ⚙️ Configuración")
        st.markdown("---")

        st.markdown("**Logo institucional**")
        logo_file = st.file_uploader("Subir logo (PNG/JPG)", type=['png','jpg','jpeg'],
                                      key='logo', label_visibility='collapsed')

        st.markdown("**Firma / sello médico**")
        firma_file = st.file_uploader("Subir firma (PNG/JPG)", type=['png','jpg','jpeg'],
                                       key='firma', label_visibility='collapsed')

        st.markdown("---")
        st.markdown("**Período nocturno asumido**")
        noc_start = st.number_input("Inicio nocturno (hs)", 20, 24, 23, 1)
        noc_end   = st.number_input("Fin nocturno (hs)", 4, 10, 7, 1)

        st.markdown("---")
        ignore_pdf_original = st.checkbox(
            "Ignorar datos/resúmenes del PDF original",
            value=True,
            help="Usar el PDF sólo para extraer la tabla de lecturas crudas; los datos del paciente/estudio se toman del formulario y los promedios se recalculan."
        )

        st.markdown("---")
        st.markdown(f"<small>**{DOCTOR_NAME}**<br/>{DOCTOR_TITLE}<br/>{DOCTOR_MP}</small>",
                    unsafe_allow_html=True)

    # ─ Main ─
    st.title("🫀 MAPA – Informe Médico Ambulatorio")
    st.markdown(f"*{DOCTOR_SUBTITLE}*")
    st.markdown("---")

    col_upload, col_manual = st.columns([1, 1])

    # ─ 1. PDF upload ─
    with col_upload:
        st.subheader("1. Cargar PDF del equipo MAPA")
        pdf_file = st.file_uploader("Subir PDF del dispositivo MAPA",
                                     type=['pdf'], key='mapa_pdf')

        # ── Diagnóstico inmediato al subir PDF ──────────────────────────────
        if pdf_file is not None:
            with st.spinner("Analizando PDF..."):
                try:
                    import pdfplumber as _plb
                    pdf_file.seek(0)
                    with _plb.open(pdf_file) as _pdf:
                        _pages_text = []
                        _all_tables = []
                        for _p in _pdf.pages:
                            _t = _p.extract_text() or ''
                            _pages_text.append(_t)
                            for _ts in [{},
                                {'vertical_strategy':'lines','horizontal_strategy':'lines'},
                                {'vertical_strategy':'text','horizontal_strategy':'text'}]:
                                try:
                                    _tbls = _p.extract_tables(_ts)
                                    if _tbls:
                                        _all_tables.extend(_tbls); break
                                except: pass
                        _raw = "\n".join(_pages_text)
                    _raw_lecturas = _isolate_lecturas_validas_text(_raw)
                    pdf_file.seek(0)  # reset for later use

                    # Try to parse immediately. No usa estadísticas ni promedios del PDF.
                    _df_preview = _parse_from_text_v2(_raw_lecturas)
                    if _df_preview is None:
                        _df_preview = _parse_fixed_width(_raw_lecturas)
                    if _df_preview is None:
                        _df_preview = _parse_from_tables(_all_tables)

                    if _df_preview is not None and len(_df_preview) >= 3:
                        st.success(f"✅ {len(_df_preview)} lecturas detectadas automáticamente")
                        with st.expander("👁️ Vista previa (primeras 8 filas)", expanded=False):
                            st.dataframe(_df_preview.head(8), use_container_width=True)
                    else:
                        st.warning("⚠️ No se detectaron lecturas automáticamente.")
                        st.markdown("**Texto extraído del PDF** (copialo para carga manual):")
                        st.text_area("Texto del PDF:", _raw[:4000], height=220,
                                     key='pdf_raw_text',
                                     help="Copiá las filas con hora/PAS/PAD y pegálas abajo en carga manual")
                        if _all_tables:
                            with st.expander(f"Tablas detectadas ({len(_all_tables)})", expanded=False):
                                for i, tbl in enumerate(_all_tables[:3]):
                                    st.write(f"Tabla {i+1}:")
                                    st.write(pd.DataFrame(tbl).head(10))
                except Exception as _e:
                    st.error(f"Error al leer PDF: {_e}")

    # ─ 2. Patient data ─
    with col_manual:
        st.subheader("2. Datos del paciente")

        nombre     = st.text_input("Nombre y apellido", placeholder="APELLIDO, Nombre")
        c1, c2, c3 = st.columns(3)
        edad_val   = c1.number_input("Edad (años)", 0, 120, 50, 1)
        sexo       = c2.selectbox("Sexo", ["Masculino","Femenino","No especificado"])
        altura_cm  = c3.number_input("Talla (cm)", 0, 220, 0, 1,
                                      help="Opcional – para cálculo pediátrico (dejar en 0 si no aplica)")

        obra_social = st.text_input("Obra social")
        solicitante = st.text_input("Médico solicitante")
        motivo      = st.text_input("Motivo del estudio")

    st.markdown("---")

    # ─ 3. Study data ─
    st.subheader("3. Datos del estudio")
    cs1, cs2, cs3, cs4, cs5 = st.columns(5)
    fecha_estudio = cs1.text_input("Fecha (dd/mm/aaaa)", datetime.now().strftime("%d/%m/%Y"))
    hora_inicio   = cs2.text_input("Hora inicio", "08:00")
    hora_fin      = cs3.text_input("Hora fin", "08:00")
    dispositivo   = cs4.text_input("Dispositivo", "No especificado")
    manguito      = cs5.selectbox("Manguito", ["Adulto estándar","Adulto grande","Adulto pequeño","Pediátrico"])
    lecturas_tot  = st.number_input("Total de lecturas tomadas", 0, 500, 0, 1)

    st.markdown("---")

    # ─ 4. Manual reading entry (fallback) ─
    with st.expander("📋 Carga manual de lecturas (si el PDF no parsea correctamente)", expanded=False):
        st.markdown("""
        Pegá las lecturas en formato CSV con columnas:
        `hora,PAS,PAD,FC` (una lectura por línea).
        Ejemplo: `08:15,145,92,72`
        """)
        manual_csv = st.text_area("Lecturas (hora,PAS,PAD,FC)", height=200,
                                   placeholder="08:15,145,92,72\n09:00,138,88,68\n...")
        st.markdown("También podés pegar directamente desde una planilla de cálculo (Tab-separado o CSV).")

    # ─ Generate ─
    st.markdown("---")
    gen_col, _ = st.columns([1, 2])
    generate = gen_col.button("⚕️ Generar Informe PDF", use_container_width=True)

    if not generate:
        st.info("Completá los datos del paciente y cargá el PDF del equipo, luego presioná **Generar Informe PDF**.")
        return

    # ─ PROCESSING ─
    with st.spinner("Procesando estudio MAPA..."):

        df_raw = None
        meta = {}
        parse_error = None
        raw_text_debug = ""

        # Try PDF first
        if pdf_file:
            result = parse_mapa_pdf(pdf_file)
            # parse_mapa_pdf returns (df, meta, raw_text) or (None, err_str, raw_text)
            if len(result) == 3:
                df_raw, meta_or_err, raw_text_debug = result
            else:
                df_raw, meta_or_err = result[:2]
                raw_text_debug = ""

            if df_raw is None:
                parse_error = meta_or_err
                st.warning(f"⚠️ {parse_error}")
                # Show raw text excerpt so user can diagnose / copy-paste manually
                if raw_text_debug:
                    with st.expander("🔍 Texto extraído del PDF (para diagnóstico)", expanded=True):
                        st.text_area("Primeros 3000 caracteres del PDF:",
                                     raw_text_debug[:3000], height=200)
                        st.caption("Si ves las lecturas aquí, copiálas y pegálas en la carga manual.")
            else:
                meta = meta_or_err if isinstance(meta_or_err, dict) else {}
                st.success(f"✅ PDF procesado: **{len(df_raw)} lecturas** extraídas.")
                # Preview extracted data
                with st.expander("👁️ Vista previa de datos extraídos", expanded=False):
                    st.dataframe(df_raw.head(10), use_container_width=True)
                    if len(df_raw) > 10:
                        st.caption(f"... y {len(df_raw)-10} lecturas más")

        # Try manual CSV
        if df_raw is None and manual_csv.strip():
            try:
                lines = [l.strip() for l in manual_csv.strip().split('\n') if l.strip()]
                rows = []
                for line in lines:
                    parts = re.split(r'[\t,;]', line)
                    if len(parts) >= 3:
                        r = {'hora': parts[0].strip(),
                             'PAS': float(parts[1]), 'PAD': float(parts[2])}
                        if len(parts) >= 4:
                            r['FC'] = float(parts[3])
                        rows.append(r)
                if rows:
                    df_raw = pd.DataFrame(rows)
                    st.success(f"✅ Datos manuales cargados: {len(df_raw)} lecturas.")
            except Exception as e:
                st.error(f"Error al parsear datos manuales: {e}")

        if df_raw is None:
            st.error("❌ No hay datos para procesar. "
                     "Cargá el PDF del equipo o ingresá las lecturas manualmente.")
            return

        # Detect pediatric
        is_ped = int(edad_val) < 17
        altura = int(altura_cm) if altura_cm > 0 else None
        sex_code = 'F' if 'Fem' in sexo else 'M'

        # Assign periods
        df_raw = assign_periods(df_raw, noc_start=int(noc_start), noc_end=int(noc_end))

        # Clean
        df_clean, excluded, n_orig = clean_data(df_raw)

        if len(df_clean) < 5:
            st.error(f"❌ Quedan sólo {len(df_clean)} lecturas válidas tras la depuración. "
                     "Revisá los datos.")
            return

        # Lecturas válidas %
        lect_tot = lecturas_tot if lecturas_tot > 0 else n_orig
        pct_val = round(len(df_clean)/lect_tot*100, 1) if lect_tot > 0 else '–'

        # Metrics
        m = calculate_metrics(df_clean, age=edad_val if is_ped else None,
                               is_ped=is_ped, sex=sex_code, height=altura)

        # Phenotype
        phenotype = classify_phenotype(m)

        # Duration
        try:
            h_ini = datetime.strptime(hora_inicio, "%H:%M")
            h_fin = datetime.strptime(hora_fin, "%H:%M")
            dur_h = (h_fin - h_ini).seconds // 3600 if h_fin > h_ini else (
                (h_fin - h_ini).seconds + 86400) // 3600
            dur_str = f"{dur_h} horas"
        except:
            dur_str = "No especificado"

        # Build patient/study dicts
        pat_info = {
            'nombre': nombre or 'No especificado',
            'edad': str(int(edad_val)),
            'sexo': sexo,
            'obra_social': obra_social or 'No especificada',
            'solicitante': solicitante or '–',
            'motivo': motivo or '–',
            'is_pediatric': is_ped,
            'duracion_str': dur_str,
        }
        stu_info = {
            'fecha': fecha_estudio,
            'inicio': hora_inicio,
            'fin': hora_fin,
            'duracion': dur_str,
            # Por defecto no se toman datos del encabezado/resumen del PDF original.
            # El PDF se usa sólo como fuente de lecturas crudas; estos campos salen del formulario.
            'dispositivo': dispositivo if ignore_pdf_original else meta.get('dispositivo', dispositivo),
            'manguito': manguito if ignore_pdf_original else meta.get('manguito', manguito),
            'pct_validas': str(pct_val),
        }

        # Assets
        logo_bytes  = img_to_bytes(logo_file) if logo_file else None
        firma_bytes = img_to_bytes(firma_file) if firma_file else None

        # Generate PDF
        pdf_buf = generate_pdf(df_clean, m, pat_info, stu_info, phenotype,
                                logo_bytes, firma_bytes, excluded)

    # Results summary
    st.markdown("---")
    st.subheader("\U0001f4ca Resumen del informe")

    col_a, col_b, col_c, col_d = st.columns(4)
    col_a.metric("Fenotipo", phenotype if len(phenotype) < 25 else phenotype[:24]+'...')
    col_b.metric('Patron circadiano', m.get('dip_pattern','-'))
    dip_lbl = safe(m.get('aasi'),'2') + ' - ' + str(m.get('aasi_interp','-'))
    col_c.metric('AASI', dip_lbl[:25])
    col_d.metric("PP 24h", f"{safe(m.get('PP_24h'),'1')} mmHg")

    col_e, col_f, col_g, col_h = st.columns(4)
    col_e.metric("PAS/PAD 24h", f"{safe(m.get('PAS_24h'),'1')}/{safe(m.get('PAD_24h'),'1')} mmHg")
    col_f.metric("PAS/PAD Diurno", f"{safe(m.get('PAS_diurno'),'1')}/{safe(m.get('PAD_diurno'),'1')} mmHg")
    col_g.metric("PAS/PAD Nocturno", f"{safe(m.get('PAS_nocturno'),'1')}/{safe(m.get('PAD_nocturno'),'1')} mmHg")
    col_h.metric("Lecturas válidas", f"{len(df_clean)} ({pct_val}%)")

    if excluded > 0:
        st.info(f"ℹ️ {excluded} medición(es) fueron excluidas durante la depuración de datos.")

    # Download section
    nombre_clean = re.sub(r'[^A-Za-z0-9]', '_', (nombre or 'Paciente').upper())
    fecha_clean  = fecha_estudio.replace('/','')
    os_clean     = re.sub(r'[^A-Za-z0-9]', '_', (obra_social or 'SinOS').upper())
    base_name    = f"MAPA_{nombre_clean}_{fecha_clean}_{os_clean}"

    # 1. PDF
    pdf_bytes = pdf_buf.getvalue()

    # 2. CSV lecturas
    df_export = df_clean.copy()
    for col in ['PAS','PAD','PAM','PP','FC']:
        if col in df_export.columns:
            df_export[col] = df_export[col].round(1)
    csv_io = io.StringIO()
    df_export.to_csv(csv_io, index=False, encoding='utf-8-sig')
    csv_bytes = csv_io.getvalue().encode('utf-8-sig')

    # 3. Chart PNG
    try:
        chart_buf2 = generate_chart(df_clean, m)
        chart_bytes = chart_buf2.getvalue()
    except Exception:
        chart_bytes = None

    # 4. Metrics TXT
    lines_txt = [
        "MAPA - RESUMEN DE METRICAS",
        f"Paciente : {nombre}",
        f"Fecha    : {fecha_estudio}  |  Obra social: {obra_social}",
        f"Fenotipo : {phenotype}",
        "",
        "PROMEDIOS",
        f"  PAS/PAD 24h     : {safe(m.get('PAS_24h'),1)}/{safe(m.get('PAD_24h'),1)} mmHg",
        f"  PAS/PAD Diurno  : {safe(m.get('PAS_diurno'),1)}/{safe(m.get('PAD_diurno'),1)} mmHg",
        f"  PAS/PAD Nocturno: {safe(m.get('PAS_nocturno'),1)}/{safe(m.get('PAD_nocturno'),1)} mmHg",
        f"  FC 24h          : {safe(m.get('FC_24h'),1)} lpm",
        f"  PP 24h          : {safe(m.get('PP_24h'),1)} mmHg  ({m.get('pp_interp','')})",
        "",
        "CARGAS TENSIONALES",
        f"  Carga SYS  24h   : {safe(m.get('carga_sys_24h'),1)}%  Diurno: {safe(m.get('carga_sys_diurno'),1)}%  Nocturno: {safe(m.get('carga_sys_nocturno'),1)}%",
        f"  Carga DIA  24h   : {safe(m.get('carga_dia_24h'),1)}%  Diurno: {safe(m.get('carga_dia_diurno'),1)}%  Nocturno: {safe(m.get('carga_dia_nocturno'),1)}%",
        "",
        "RITMO CIRCADIANO",
        f"  Patron    : {m.get('dip_pattern','')}",
        f"  Descenso PAS: {safe(m.get('dip_sys'),1)}%  PAD: {safe(m.get('dip_dia'),1)}%",
        "",
        "RIGIDEZ Y VARIABILIDAD",
        f"  AASI      : {safe(m.get('aasi'),2)}  ({m.get('aasi_interp','')})",
        f"  DE PAS 24h: {safe(m.get('PAS_DE_24h'),1)} mmHg  CV: {safe(m.get('PAS_CV_24h'),1)}%",
        f"  DE PAD 24h: {safe(m.get('PAD_DE_24h'),1)} mmHg  CV: {safe(m.get('PAD_CV_24h'),1)}%",
        f"  Morning surge: {safe(m.get('morning_surge'),1)} mmHg ({m.get('morning_surge_method','')})",
        "",
        "CALIDAD",
        f"  Lecturas validas : {len(df_clean)}  ({pct_val}%)",
        f"  Lecturas excluidas: {excluded}",
        "",
        f"Generado por: Dr. {DOCTOR_NAME}  |  {DOCTOR_MP}",
        INSTITUTION,
    ]
    txt_bytes = "\n".join(lines_txt).encode('utf-8')

    st.markdown("---")
    st.subheader("Descargar archivos")

    dcol1, dcol2, dcol3, dcol4 = st.columns(4)
    dcol1.download_button(label="Informe PDF", data=pdf_bytes,
        file_name=f"{base_name}.pdf", mime='application/pdf',
        use_container_width=True)
    dcol2.download_button(label="Lecturas CSV", data=csv_bytes,
        file_name=f"{base_name}_lecturas.csv", mime='text/csv',
        use_container_width=True)
    if chart_bytes:
        dcol3.download_button(label="Grafico PNG", data=chart_bytes,
            file_name=f"{base_name}_grafico.png", mime='image/png',
            use_container_width=True)
    else:
        dcol3.button("Grafico PNG", disabled=True, use_container_width=True)
    dcol4.download_button(label="Metricas TXT", data=txt_bytes,
        file_name=f"{base_name}_metricas.txt", mime='text/plain',
        use_container_width=True)

    audio_msg = (f"ESTUDIO MAPA INFORMADO DE {(nombre or 'PACIENTE').upper()}, "
                 f"{fecha_estudio}, {(obra_social or 'SIN OBRA SOCIAL').upper()}")
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