#!/usr/bin/env python3
"""Check that the manuscript-facing interfaces remain synchronized."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import artifact_metadata  # type: ignore[import-not-found]  # noqa: E402
import paper_links  # type: ignore[import-not-found]  # noqa: E402


PRINCIPAL_IMPORT = "MyProject.Determinantalideals.ReducedGroebner"
SIGNATURE_DECLARATIONS = (
    "Determinantal.exists_krsEquiv",
    "Determinantal.straightening_law_exists_filtered",
    "Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le",
    "Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder",
    "Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder",
    "Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder",
)
EXPECTED_LINK_DECLARATIONS = (
    "Determinantal.exists_krsEquiv",
    "Determinantal.KRS.krsEquiv",
    "Determinantal.straightening_law_exists_filtered",
    "Determinantal.straightening_law",
    "Determinantal.exists_standardBitableau_basis_determinantalRing",
    "Determinantal.hilbertFunction_detRing_eq_card_monomialExp_width_le",
    "Determinantal.monomial_mem_initGrPlusOne_iff_width",
    "Determinantal.lemma6_monomial_mem_initGrPlusOne_iff_width",
    "Determinantal.degree_minor_eq_antidiagExp",
    "Determinantal.leadingCoeff_minor_eq_revPermCoeff",
    "Determinantal.leadingTerm_minor_eq_antidiagMonomial_coeff",
    "Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder",
    "Determinantal.GrPlusOne_isGroebnerBasis_antiDiagonalLex",
    "Determinantal.antidiagExp_le_permExp_imp_minorIndex_eq",
    "Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder",
    "Determinantal.normalizedGenericMinor",
    "Determinantal.support_normalizedGenericMinor",
    "Determinantal.leadingCoeff_normalizedGenericMinor",
    "Determinantal.normalizedGrPlusOne",
    "Determinantal.normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder",
    "Determinantal.normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder",
    "Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder",
    "Determinantal.normalizedGrPlusOne_isReduced_antiDiagonalLex",
    "Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex",
)
EXPECTED_METADATA = {
    "principal_import": PRINCIPAL_IMPORT,
    "main_raw_groebner_theorem": (
        "Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder"
    ),
    "main_interreduction_theorem": (
        "Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder"
    ),
    "main_normalized_reduced_theorem": (
        "Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder"
    ),
    "concrete_order": "Determinantal.antiDiagonalLex",
}
REQUIRED_METADATA_KEYS = frozenset(
    {
        "principal_import",
        "main_raw_groebner_theorem",
        "main_interreduction_theorem",
        "main_normalized_reduced_theorem",
        "concrete_order",
        "lean_toolchain",
        "lean_version",
        "requested_mathlib_revision",
        "resolved_mathlib_commit",
        "requested_groebner_revision",
        "resolved_groebner_commit",
        "license",
        "head_sha",
        "working_tree",
        "ci_workflow_path",
        "package_version",
    }
)
OBSOLETE_PHRASES = (
    "does not formalize reducedness",
    "reducedness is future work",
    "reducedness is not part of the artifact",
)


def read(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def declaration_line(keyword: str, declaration: str) -> re.Pattern[str]:
    return re.compile(
        rf"^\s*{re.escape(keyword)}\s+{re.escape(declaration)}"
        rf"(?![A-Za-z0-9_'])",
        re.MULTILINE,
    )


def main() -> int:
    errors: list[str] = []
    paper_audit = read("PaperAudit.lean")
    axiom_audit = read("Audit.lean")

    import_pattern = re.compile(
        rf"^\s*import\s+{re.escape(PRINCIPAL_IMPORT)}\s*$", re.MULTILINE
    )
    if not import_pattern.search(paper_audit):
        errors.append(f"PaperAudit.lean must import {PRINCIPAL_IMPORT}")

    for declaration in SIGNATURE_DECLARATIONS:
        if not declaration_line("#check", declaration).search(paper_audit):
            errors.append(f"PaperAudit.lean does not #check {declaration}")
        if not declaration_line("exact", declaration).search(paper_audit):
            errors.append(
                f"PaperAudit.lean does not lock {declaration} with an exact example"
            )

    reduced_theorem = EXPECTED_METADATA["main_normalized_reduced_theorem"]
    if not declaration_line("#print axioms", reduced_theorem).search(axiom_audit):
        errors.append(f"Audit.lean does not audit {reduced_theorem}")

    link_names = tuple(name for name, _path in paper_links.DECLARATIONS)
    if len(link_names) != len(set(link_names)):
        errors.append("paper_links.py contains duplicate declaration names")
    if link_names != EXPECTED_LINK_DECLARATIONS:
        missing = sorted(set(EXPECTED_LINK_DECLARATIONS) - set(link_names))
        unexpected = sorted(set(link_names) - set(EXPECTED_LINK_DECLARATIONS))
        if missing:
            errors.append("paper_links.py is missing: " + ", ".join(missing))
        if unexpected:
            errors.append(
                "paper_links.py has unexpected entries: " + ", ".join(unexpected)
            )
        if not missing and not unexpected:
            errors.append("paper_links.py declarations are not in manuscript proof-chain order")

    if not REQUIRED_METADATA_KEYS.issubset(artifact_metadata.REQUIRED_METADATA_KEYS):
        missing = REQUIRED_METADATA_KEYS - artifact_metadata.REQUIRED_METADATA_KEYS
        errors.append(
            "artifact metadata schema is missing: " + ", ".join(sorted(missing))
        )
    for key, expected in EXPECTED_METADATA.items():
        if artifact_metadata.PAPER_METADATA.get(key) != expected:
            errors.append(
                f"artifact metadata {key!r} must be {expected!r}; "
                f"found {artifact_metadata.PAPER_METADATA.get(key)!r}"
            )

    prose_paths = (
        "README.md",
        "REPRODUCIBILITY.md",
        "docs/statement_correspondence.md",
    )
    prose = {path: read(path) for path in prose_paths}
    for path, text in prose.items():
        lowered = text.casefold()
        for phrase in OBSOLETE_PHRASES:
            if phrase in lowered:
                errors.append(f"{path} contains obsolete claim: {phrase!r}")

    combined = "\n".join(prose.values())
    semantic_claims = {
        "the original minors are interreduced": (
            r"(?:original|unnormalized).{0,160}minors?.{0,160}interreduc"
        ),
        "the normalized minors form a reduced Groebner basis": (
            r"(?:normalizedGrPlusOne|normalized\s+minors?|coefficient-normalized)"
            r".{0,1000}reduced.{0,40}Gr(?:ö|o)ebner.{0,20}basis"
        ),
        "rank-variety geometry is not formalized": (
            r"(?:does\s+not\s+formalize|not\s+formalized).{0,300}"
            r"(?:rank[- ]variety|geometr(?:y|ic)|vanishing\s+ideal)"
        ),
    }
    for description, pattern in semantic_claims.items():
        if not re.search(pattern, combined, re.IGNORECASE | re.DOTALL):
            errors.append(f"documentation does not state that {description}")

    if errors:
        print("Paper contract check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print(
        "Paper contract checks passed: six exact interfaces, "
        "24 fixed-link declarations, metadata, audits, and scope claims agree."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
