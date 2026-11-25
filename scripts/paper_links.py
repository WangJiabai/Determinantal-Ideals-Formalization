#!/usr/bin/env python3
"""Check documentation source links and generate paper-facing permalinks."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "WangJiabai/Determinantal-Ideals-Formalization"
INLINE_LINK = re.compile(r'\[([^\]\n]+)\]\(<?([^\s>)]+)>?(?:[ \t]+"[^"]*")?\)')
LINE_ANCHOR = re.compile(r"L([0-9]+)(?:-L([0-9]+))?")
DECLARATIONS = [
    ("Determinantal.exists_krsEquiv", "MyProject/Determinantalideals/KRScorrespondence.lean"),
    ("Determinantal.KRS.krsEquiv", "MyProject/Determinantalideals/KRScorrespondence.lean"),
    ("Determinantal.straightening_law_exists_filtered", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.straightening_law", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.exists_standardBitableau_basis_determinantalRing", "MyProject/Determinantalideals/StraighteningLaw.lean"),
    ("Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.monomial_mem_initGrPlusOne_iff_width", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.degree_minor_eq_antidiagExp", "MyProject/Determinantalideals/DiagonalOrder.lean"),
    ("Determinantal.leadingCoeff_minor_eq_revPermCoeff", "MyProject/Determinantalideals/DiagonalOrder.lean"),
    ("Determinantal.leadingTerm_minor_eq_antidiagMonomial_coeff", "MyProject/Determinantalideals/DiagonalOrder.lean"),
    ("Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex", "MyProject/Determinantalideals/Groebner.lean"),
    ("Determinantal.antidiagExp_le_permExp_imp_minorIndex_eq", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGenericMinor", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.support_normalizedGenericMinor", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.leadingCoeff_normalizedGenericMinor", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex", "MyProject/Determinantalideals/ReducedGroebner.lean"),
    ("Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex", "MyProject/Determinantalideals/ReducedGroebner.lean"),
]


def run(*args: str) -> str:
    process = subprocess.run(
        args, cwd=ROOT, text=True, encoding="utf-8", errors="replace",
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False
    )
    if process.returncode != 0:
        raise RuntimeError(process.stderr.strip() or f"{' '.join(args)} failed")
    return process.stdout


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


def declaration_pattern(qualified: str) -> re.Pattern[str]:
    name = qualified.rsplit(".", 1)[-1]
    return re.compile(
        rf"^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+"
        rf"{re.escape(name)}(?![\w'.])"
    )


def locate(qualified: str, relative: str) -> int:
    pattern = declaration_pattern(qualified)
    lines = (ROOT / relative).read_text(encoding="utf-8").splitlines()
    matches = [index for index, line in enumerate(lines, start=1) if pattern.match(line)]
    if len(matches) != 1:
        raise RuntimeError(
            f"{qualified} must occur exactly once in {relative}; found {len(matches)}"
        )
    return matches[0]


def check_source_links() -> tuple[int, int]:
    """Check inline links to local Lean sources and this repository's GitHub blobs."""
    docs = ["README.md", "REPRODUCIBILITY.md"]
    tracked_docs = run("git", "ls-files", "-z", "--", "docs").split("\0")
    docs.extend(path for path in tracked_docs if path.endswith(".md"))
    declarations = dict(DECLARATIONS)
    blob_prefix = f"/{REPOSITORY}/blob/"
    checked = mapped = 0

    for doc in map(Path, docs):
        markdown = (ROOT / doc).read_text(encoding="utf-8")
        for link in INLINE_LINK.finditer(markdown):
            label, target = link.groups()
            url = urlsplit(target)
            source = unquote(url.path)
            if not source.endswith(".lean"):
                continue
            revision = "main"
            if url.scheme or url.netloc:
                if url.hostname != "github.com" or not source.lower().startswith(blob_prefix.lower()):
                    continue
                revision, _, source = source[len(blob_prefix):].partition("/")
            else:
                source = (doc.parent / source).as_posix()

            line_number = markdown.count("\n", 0, link.start()) + 1
            location = f"{doc.as_posix()}:{line_number}"
            try:
                path = (ROOT / source).resolve().relative_to(ROOT)
                if revision == "main":
                    lines = (ROOT / path).read_text(encoding="utf-8").splitlines()
                else:
                    lines = run(
                        "git", "show", "--end-of-options", f"{revision}:{path.as_posix()}"
                    ).splitlines()

                name = label.strip().strip("`")
                if url.fragment or name in declarations:
                    anchor = LINE_ANCHOR.fullmatch(url.fragment)
                    if not anchor:
                        raise ValueError("expected a #L<number> or #L<start>-L<end> anchor")
                    first = int(anchor[1])
                    last = int(anchor[2] or anchor[1])
                    if not 1 <= first <= last <= len(lines):
                        raise ValueError(
                            f"expected 1 ≤ start ≤ end ≤ {len(lines)}, got {first}–{last}"
                        )
                    if name in declarations:
                        expected = declarations[name]
                        if (path.as_posix() != expected
                                or not declaration_pattern(name).match(lines[first - 1])):
                            raise ValueError(
                                f"anchor must start at the declaration of {name} in {expected}"
                            )
                        mapped += 1
                checked += 1
            except (OSError, RuntimeError, ValueError) as error:
                raise RuntimeError(f"{location}: {target}: {error}") from error

    return checked, mapped


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--format", choices=("markdown",), default="markdown")
    parser.add_argument("--repository", help="override GitHub slug, e.g. owner/repo")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    try:
        located = [(name, path, locate(name, path)) for name, path in DECLARATIONS]
        if args.check_only:
            checked, mapped = check_source_links()
            print(f"Located {len(located)} paper-facing declarations exactly once.")
            print(f"Checked {checked} documentation source links ({mapped} declaration anchors).")
            return 0
        if run("git", "status", "--porcelain"):
            raise RuntimeError(
                "working tree is dirty; commit and freeze the revision before generating publishable permalinks"
            )
        sha = run("git", "rev-parse", "HEAD").strip()
        slug = args.repository or github_slug(run("git", "remote", "get-url", "origin").strip())
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
