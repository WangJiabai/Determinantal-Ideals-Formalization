#!/usr/bin/env python3
"""Run Audit.lean and enforce its exact foundational-axiom allowlist."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "Audit.lean"
ALLOWLIST = ROOT / "audit" / "axiom_allowlist.txt"


def declarations() -> list[str]:
    pattern = re.compile(r"^\s*#print\s+axioms\s+(\S+)\s*$")
    result = [
        match.group(1)
        for line in AUDIT.read_text(encoding="utf-8").splitlines()
        if (match := pattern.match(line))
    ]
    if not result:
        raise RuntimeError("Audit.lean contains no '#print axioms' commands")
    if len(result) != len(set(result)):
        raise RuntimeError("Audit.lean contains duplicate audited declarations")
    return result


def allowed_axioms() -> set[str]:
    allowed = {
        line.strip()
        for line in ALLOWLIST.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    }
    if not allowed:
        raise RuntimeError("axiom allowlist is empty")
    return allowed


def parse_report(report: str) -> dict[str, set[str]]:
    parsed: dict[str, set[str]] = {}
    depends = re.compile(
        r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL
    )
    for match in depends.finditer(report):
        name = match.group(1)
        axioms = {item.strip() for item in match.group(2).split(",") if item.strip()}
        parsed[name] = axioms
    no_axioms = re.compile(r"'([^']+)' does not depend on any axioms")
    for match in no_axioms.finditer(report):
        parsed[match.group(1)] = set()
    return parsed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output", type=Path, help="also write the complete Lean report to PATH"
    )
    args = parser.parse_args()

    try:
        expected = declarations()
        allowed = allowed_axioms()
    except (OSError, RuntimeError) as error:
        print(f"axiom audit configuration error: {error}", file=sys.stderr)
        return 2

    process = subprocess.run(
        ["lake", "env", "lean", "Audit.lean"],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    report = process.stdout + process.stderr
    sys.stdout.write(process.stdout)
    sys.stderr.write(process.stderr)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(report, encoding="utf-8")
    if process.returncode != 0:
        print(f"Audit.lean failed with exit code {process.returncode}", file=sys.stderr)
        return process.returncode
    if "sorryAx" in report:
        print("axiom audit failed: output contains sorryAx", file=sys.stderr)
        return 1

    parsed = parse_report(report)
    missing = [name for name in expected if name not in parsed]
    extra = sorted(set(parsed) - set(expected))
    failures: list[tuple[str, str]] = []
    for name in expected:
        for axiom in sorted(parsed.get(name, set()) - allowed):
            failures.append((name, axiom))

    if missing:
        print("axiom audit failed: no parsed report for:", file=sys.stderr)
        for name in missing:
            print(f"  - {name}", file=sys.stderr)
    if extra:
        print("axiom audit failed: parsed unexpected declarations:", file=sys.stderr)
        for name in extra:
            print(f"  - {name}", file=sys.stderr)
    if failures:
        print("axiom audit failed: unexpected axioms:", file=sys.stderr)
        for name, axiom in failures:
            print(f"  - declaration: {name}", file=sys.stderr)
            print(f"    unexpected axiom: {axiom}", file=sys.stderr)
        print(f"  allowed set: {sorted(allowed)}", file=sys.stderr)
    if missing or extra or failures:
        return 1

    print(
        f"Axiom allowlist passed for {len(expected)} declarations; "
        f"allowed set: {sorted(allowed)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
