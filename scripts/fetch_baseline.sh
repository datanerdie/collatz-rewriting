#!/usr/bin/env bash
# Fetch the code that accompanies Yolcu, Aaronson & Heule, "An Automated Approach to the
# Collatz Conjecture" (J. Automated Reasoning, 2023) at a pinned commit.
# The upstream repository carries no licence file, so it is fetched, not vendored.
set -euo pipefail
PIN=8a4dfda60f97a6d33ff0a24fdfa7a172d4bec340
DEST="$(cd "$(dirname "$0")/.." && pwd)/third_party/rewriting-collatz"
if [ ! -d "$DEST/.git" ]; then
  mkdir -p "$(dirname "$DEST")"
  git clone -q https://github.com/emreyolcu/rewriting-collatz.git "$DEST"
fi
git -C "$DEST" checkout -q "$PIN"
echo "baseline at $DEST ($(git -C "$DEST" rev-parse --short HEAD))"
