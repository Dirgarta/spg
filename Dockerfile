FROM python:3.12-slim
ENV PYTHONUNBUFFERED=1 PYTHONDONTWRITEBYTECODE=1
RUN useradd -m -u 10001 spg
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY app_spg.py .
RUN mkdir -p /data && chown -R spg:spg /data /app
USER spg
ENV SPG_DATA_DIR=/data SPG_HOST=0.0.0.0 SPG_PORT=8090 SPG_TRUST_PROXY=1
EXPOSE 8090
HEALTHCHECK --interval=30s --timeout=5s CMD python -c "import urllib.request;urllib.request.urlopen('http://127.0.0.1:8090/healthz').read()"
CMD ["python", "app_spg.py"]
