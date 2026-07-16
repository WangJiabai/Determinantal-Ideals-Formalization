#!/usr/bin/env bash
set -euo pipefail

mapfile -d '' lean_files < <(git ls-files -z '*.lean')
if ((${#lean_files[@]} == 0)); then
  echo "No tracked Lean files found." >&2
  exit 1
fi

failed=0
if command -v rg >/dev/null 2>&1; then
  scan_backend=rg
else
  scan_backend=git-grep
fi

check_pattern() {
  local pattern=$1
  local message=$2
  local status
  set +e
  if [[ $scan_backend == rg ]]; then
    rg -n --pcre2 "$pattern" "${lean_files[@]}"
  else
    git grep -n -P -e "$pattern" -- "${lean_files[@]}"
  fi
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

check_pattern '\b(sorry|admit|sorryAx)\b' \
  "Found sorry, admit, or sorryAx in tracked Lean sources."
check_pattern '^\s*(?:(?:private|protected)\s+)?axiom\b' \
  "Found a project axiom declaration in tracked Lean sources."
check_pattern '^\s*(?:(?:private|protected)\s+)?unsafe\b' \
  "Found an unsafe declaration in tracked Lean sources."
if ((failed)); then
  exit 1
fi

printf 'Checked %d tracked Lean files:\n' "${#lean_files[@]}"
echo "- scan backend: $scan_backend"
echo "- no sorry/admit/sorryAx"
echo "- no project axiom declarations (including private/protected)"
echo "- no unsafe declarations (including private/protected)"
