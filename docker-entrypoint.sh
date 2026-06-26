#!/bin/bash
# Re-run configure when the workspace is bind-mounted (host code replaces the
# baked copy).  Skip if Makefile.config already has ARCH set (baked image).
set -e

if [ ! -s /workspace/CompCert/configure ]; then
    echo "[entrypoint] CompCert submodule not found in mounted workspace."
    echo "  Run on host: git submodule update --init --recursive"
    exit 1
fi

if ! grep -q '^ARCH=.\+' /workspace/Makefile.config 2>/dev/null; then
    echo "[entrypoint] Running ./configure -clightgen x86_64-linux ..."
    cd /workspace && ./configure -clightgen x86_64-linux
fi

exec "$@"
