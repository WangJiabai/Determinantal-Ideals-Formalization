#!/usr/bin/env python3
"""Locate paper-facing declarations and emit immutable GitHub permalinks."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DECLARATIONS = [
    ("Determinantal.theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.antidiagExp_le_permExp_imp_minorIndex_eq", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.theorem1_normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.degree_minor_eq_antidiagExp", "MyProject/Determinantalideals/DiagonalOrder.lean"),
    ("Determinantal.straightening_law_exists_filtered", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.straightening_law", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.exists_standardBitableau_basis_determinantalRing", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.KRS.krsEquiv", "MyProject/Determinantalideals/KRScorrespondence.lean"),
    ("Determinantal.exists_krsEquiv_of_degree_widthLE", "MyProject/Determinantalideals/KRScorrespondence.lean"),
]


def run(*args: str) -> str:
    process = subprocess.run(
        args, cwd=ROOT, text=True, encoding="utf-8", errors="replace",
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False
    )
    if process.returncode != 0:
        raise RuntimeError(process.stderr.strip() or f"{' '.join(args)} failed")
    return process.stdout.strip()


def github_slug(remote: str) -> str:
    patterns = (
        r"^https?://github\.com/([^/]+/[^/]+?)(?:\.git)?$",
        r"^git@github\.com:([^/]+/[^/]+?)(?:\.git)?$",
        r"^ssh://git@github\.com/([^/]+/[^/]+?)(?:\.git)?$",
    )
    for pattern in patterns:
        if match := re.match(pattern, remote):
            return match.group(1)
    raise RuntimeError(f"cannot derive a GitHub repository slug from origin: {remote}")


def locate(qualified: str, relative: str) -> int:
    name = qualified.rsplit(".", 1)[-1]
    pattern = re.compile(
        rf"^\s*(?:(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev))\s+{re.escape(name)}\b"
    )
    lines = (ROOT / relative).read_text(encoding="utf-8").splitlines()
    matches = [index for index, line in enumerate(lines, start=1) if pattern.match(line)]
    if len(matches) != 1:
        raise RuntimeError(
            f"{qualified} must occur exactly once in {relative}; found {len(matches)}"
        )
    return matches[0]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--format", choices=("markdown",), default="markdown")
    parser.add_argument("--repository", help="override GitHub slug, e.g. owner/repo")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    try:
        located = [(name, path, locate(name, path)) for name, path in DECLARATIONS]
        if args.check_only:
            print(f"Located {len(located)} paper-facing declarations exactly once.")
            return 0
        if run("git", "status", "--porcelain"):
            raise RuntimeError(
                "working tree is dirty; commit and freeze the revision before generating publishable permalinks"
            )
        sha = run("git", "rev-parse", "HEAD")
        slug = args.repository or github_slug(run("git", "remote", "get-url", "origin"))
    except (OSError, RuntimeError) as error:
        print(f"paper links error: {error}", file=sys.stderr)
        return 1

    print("| Lean declaration | Module | Fixed permalink |")
    print("| --- | --- | --- |")
    for name, path, line in located:
        url = f"https://github.com/{slug}/blob/{sha}/{path}#L{line}"
        print(f"| `{name}` | `{path}` | [source]({url}) |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
