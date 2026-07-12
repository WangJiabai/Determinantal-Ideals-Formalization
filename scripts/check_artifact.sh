#!/usr/bin/env bash
set -euo pipefail

skip_build=0
python_bin=python3
if ! command -v "$python_bin" >/dev/null 2>&1; then
  python_bin=python
fi
if (($# > 1)); then
  echo "Usage: $0 [--skip-build]" >&2
  exit 2
fi
if (($# == 1)); then
  if [[ $1 == --skip-build ]]; then
    skip_build=1
  else
    echo "Unknown option: $1" >&2
    exit 2
  fi
fi

echo "==> Checking tracked Lean sources"
bash scripts/check_sources.sh

if ((skip_build)); then
  echo "==> Skipping lake build"
else
  echo "==> Building the Lean project"
  lake build
fi

echo "==> Compiling paper-facing signatures"
lake env lean PaperAudit.lean

echo "==> Enforcing the axiom allowlist"
"$python_bin" scripts/check_axioms.py

echo "==> Locating paper-facing declarations"
"$python_bin" scripts/paper_links.py --check-only

echo "==> Generating current artifact metadata"
"$python_bin" scripts/artifact_metadata.py --format markdown

echo "==> Artifact checks completed successfully"
