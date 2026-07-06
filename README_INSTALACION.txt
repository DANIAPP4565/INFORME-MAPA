MAPA Informe Médico – v6.6

ARCHIVOS
- app.py: aplicación completa e integrada.
- requirements.txt: dependencias Python.
- packages.txt: paquetes del sistema para Streamlit Cloud, incluido Tesseract OCR.

STREAMLIT CLOUD
1. Subir estos tres archivos a la raíz del repositorio.
2. Configurar app.py como archivo principal.
3. Reiniciar / Reboot app tras actualizar packages.txt.

LOCAL
Python:
    pip install -r requirements.txt

Ubuntu/Debian:
    sudo apt update
    sudo apt install tesseract-ocr tesseract-ocr-spa tesseract-ocr-eng

Windows:
- Instalar Tesseract OCR como programa del sistema.
- La app detecta automáticamente:
  C:\Program Files\Tesseract-OCR\tesseract.exe
  C:\Program Files (x86)\Tesseract-OCR\tesseract.exe
- También puede definirse la variable de entorno TESSERACT_CMD.

EJECUCIÓN
    streamlit run app.py

CAMBIOS PRINCIPALES v6.6
- Detección y validación real del ejecutable Tesseract.
- Soporte Linux/Streamlit Cloud, Windows, macOS/Homebrew y TESSERACT_CMD.
- Estado OCR en barra lateral con ruta, versión e idiomas detectados.
- Los métodos OCR fallan con diagnóstico explícito si sólo existe pytesseract pero falta Tesseract.
- Conserva corrección nocturna por hora real de reloj y precisión HH:MM.
- Conserva controles de integridad y mínimo nocturno.
