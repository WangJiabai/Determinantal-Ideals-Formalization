#!/usr/bin/env bash
set -euo pipefail

mapfile -d '' lean_files < <(git ls-files -z '*.lean')
if ((${#lean_files[@]} == 0)); then
  echo "No tracked Lean files found." >&2
  exit 1
fi

failed=0
check_pattern() {
  local pattern=$1
  local message=$2
  local status
  set +e
  rg -n --pcre2 "$pattern" "${lean_files[@]}"
  status=$?
  set -e
  if ((status == 0)); then
    echo "$message" >&2
    failed=1
  elif ((status != 1)); then
    echo "Source scan failed while checking pattern: $pattern" >&2
    exit "$status"
  fi
}

check_pattern '\b(sorry|admit)\b' "Found sorry or admit in tracked Lean sources."
check_pattern '^\s*axiom\b' "Found a project axiom declaration in tracked Lean sources."
check_pattern '^\s*unsafe\b' "Found an unsafe declaration in tracked Lean sources."
if ((failed)); then
  exit 1
fi

printf 'Checked %d tracked Lean files:\n' "${#lean_files[@]}"
echo "- no sorry/admit"
echo "- no project axiom declarations"
echo "- no unsafe declarations"
