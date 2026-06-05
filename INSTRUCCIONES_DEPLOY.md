# MAPA Informe Médico – Guía de Despliegue
**Dr. Ricardo Daniel Olano | Cardiólogo – IPENSA La Plata**

---

## Archivos del proyecto

```
app.py               ← Aplicación Streamlit principal
requirements.txt     ← Dependencias Python
INSTRUCCIONES.md     ← Este archivo
assets/
  firma.png          ← (Opcional) Imagen de firma/sello médico
  logo_ipensa.png    ← (Opcional) Logo institucional IPENSA
```

---

## Opción 1 – Streamlit Cloud (recomendado)

1. Creá un repositorio en GitHub (puede ser privado).
2. Subí `app.py` y `requirements.txt` al repositorio.
3. Ingresá a [share.streamlit.io](https://share.streamlit.io) con tu cuenta de GitHub.
4. Clic en **New app** → seleccioná tu repositorio → rama `main` → archivo `app.py`.
5. Clic en **Deploy** → en 2–3 minutos la app estará disponible en una URL pública.

**Agregar logo y firma al repositorio:**
- Creá una carpeta `assets/` en el repositorio.
- Subí `firma.png` y `logo_ipensa.png` a esa carpeta.
- En el sidebar de la app, usá el uploader para cargarlos en cada sesión,
  o modificá `app.py` para leerlos automáticamente desde `assets/`.

---

## Opción 2 – Ejecución local

### Requisitos
- Python 3.10 o superior
- pip

### Instalación

```bash
# Clonar o copiar los archivos
cd /ruta/a/la/carpeta

# Instalar dependencias
pip install -r requirements.txt

# Ejecutar
streamlit run app.py
```

La app se abre automáticamente en el navegador en `http://localhost:8501`.

---

## Uso de la app

### Paso a paso

1. **Sidebar:** subí el logo institucional y la imagen de firma/sello.
2. **Cargar PDF:** subí el PDF exportado desde el equipo MAPA (MedicalDB, SpaceLabs, etc.).
3. **Completar datos del paciente:** nombre, edad, sexo, obra social, solicitante, motivo.
4. **Completar datos del estudio:** fecha, horario, dispositivo, manguito, lecturas totales.
5. **Carga manual (si el PDF no parsea):** pegá las lecturas en formato CSV
   (`hora,PAS,PAD,FC`) en el expander inferior.
6. **Generar Informe PDF** → descargá el archivo con el botón de descarga.

### Dispositivos MAPA soportados (parseo automático)
- MedicalDB (Argentina)
- SpaceLabs
- Microlife
- OMRON
- Schiller
- Welch Allyn
- A&D
- Cualquier PDF con tabla en formato hora/SIS/DIA/FC

### Si el PDF no parsea correctamente
Pegá las lecturas manualmente en el expander **"Carga manual de lecturas"**:
```
08:15,145,92,72
09:00,138,88,68
...
```
Formato: `hora (hh:mm), PAS, PAD, FC` — una lectura por línea.
También podés copiar y pegar desde Excel (acepta Tab-separado).

---

## Estructura del informe PDF generado

**Página 1**
- Logo institucional (esquina superior izquierda)
- Título: MONITOREO AMBULATORIO DE PRESIÓN ARTERIAL (M.A.P.A.)
- Datos personales y del estudio
- Tabla de promedios (24 h / Diurno / Nocturno)
- **Conclusión ejecutiva** (negrita, mayúsculas, justificado)
  - Fenotipo hipertensivo
  - Patrón de descenso nocturno
  - PP, AASI, Morning surge
- Cargas tensionales y variabilidad
- Firma/sello médico

**Página 2+**
- Gráfico PAS/PAD con umbrales y franja nocturna azul
- Gráfico FC
- Comparación con guías: ESC/ESH 2024, ACC/AHA 2025, Consenso Arg. FAC-SAHA-SAC 2025
- Conclusión médica ampliada con recomendación de estudios complementarios

---

## Nombre del archivo PDF generado

El archivo se nombra automáticamente:
```
MAPA_{APELLIDO_NOMBRE}_{FECHADDMMAAAA}_{OBRA_SOCIAL}.pdf
```
Ejemplo: `MAPA_GAGGERO_MARIA_CRISTINA_27102025_IOMA.pdf`

---

## Aviso de audio

Al finalizar la generación, la app emite por voz (Web Speech API del navegador):
> *ESTUDIO MAPA INFORMADO DE [NOMBRE], [FECHA], [OBRA SOCIAL]*

Requiere navegador con soporte de síntesis de voz (Chrome/Edge/Firefox modernos).

---

## Notas técnicas

- **Depuración automática:** se excluyen lecturas con PAD <40, PAD >130,
  PAS >230, PP >80, PP <20 mmHg.
- **Período nocturno:** configurable en el sidebar (por defecto 23:00–07:00).
- **Población pediátrica:** detección automática si edad <17 años;
  umbrales por percentiles ESH 2016 / AAP 2017.
- **AASI:** calculado por regresión lineal PAD vs PAS (requiere ≥10 lecturas).
- **Morning surge:** estimado (ventana 06:00–09:00 vs 02:00–04:00).

---

## Soporte

Dr. Ricardo Daniel Olano | MP: 110957  
IPENSA – Calle 59 Nº 434/36, La Plata  
Tel: (0221) 427-1190
