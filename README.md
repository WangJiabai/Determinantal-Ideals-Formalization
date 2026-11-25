# Determinantal Ideals in Lean 4

[![Lean](https://github.com/WangJiabai/Determinantal-Ideals-Formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/WangJiabai/Determinantal-Ideals-Formalization/actions/workflows/lean.yml)

This project formalizes the Gröbner-basis part of Sturmfels’s theorem for
determinantal ideals. Over an arbitrary field `k`, the fixed-size minors of a
generic `m × n` matrix form a Gröbner basis of the ideal they generate in
`MvPolynomial (Fin m × Fin n) k` for every anti-diagonal monomial order.

## Main results

| Result | Lean declaration |
| --- | --- |
| The leading monomials of the `(r + 1) × (r + 1)` minors generate the initial ideal | [`Determinantal.GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder`](MyProject/Determinantalideals/Groebner.lean#L1204) |
| The original minors are interreduced | [`Determinantal.GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder`](MyProject/Determinantalideals/ReducedGroebner.lean#L137) |
| The normalized minors form a reduced Gröbner basis of the same ideal | [`Determinantal.normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder`](MyProject/Determinantalideals/ReducedGroebner.lean#L227) |

Each normalized generator is scaled by the inverse of its leading coefficient
to make it monic. The project also verifies the concrete order
`antiDiagonalLex`, used in [`Examples/PaperExamples.lean`](Examples/PaperExamples.lean).

The formalized ideal `Jr` is defined by its minor generators. The Hilbert
function is stated in total degree. See the
[statement correspondence](docs/statement_correspondence.md) for how the Lean
results relate to the classical statements.

## Proof structure

1. [`DeterminantalIdeal.lean`](MyProject/Determinantalideals/DeterminantalIdeal.lean)
   defines generic minors and their generated ideals.
   [`DiagonalOrder.lean`](MyProject/Determinantalideals/DiagonalOrder.lean)
   identifies the leading terms under anti-diagonal orders.
2. [`KRScorrespondence.lean`](MyProject/Determinantalideals/KRScorrespondence.lean)
   establishes the degree-preserving Knuth–Robinson–Schensted (KRS)
   correspondence and relates monomial width to bitableau shape.
   [`StraighteningLaw.lean`](MyProject/Determinantalideals/StraighteningLaw.lean)
   proves the straightening law and constructs a standard-bitableau basis of
   the determinantal quotient.
3. [`Groebner.lean`](MyProject/Determinantalideals/Groebner.lean) uses KRS to
   count those basis elements in each degree and compares that count with the
   Hilbert function of the quotient by the leading monomials of the minors.
   Equality in each degree proves the Gröbner-basis theorem.
   [`ReducedGroebner.lean`](MyProject/Determinantalideals/ReducedGroebner.lean)
   proves interreduction and the monic reduced refinement.

The [proof outline](docs/proof_outline.md) and [design notes](docs/design_choices.md)
give the declaration-level proof dependencies and representation choices.

## Mathlib Integration

The foundational API was merged upstream through [Mathlib PR #40266](https://github.com/leanprover-community/mathlib4/pull/40266).
It includes `Matrix.mvPolynomialMinor`, `MvPolynomial.determinantalMinors`, and
`MvPolynomial.determinantalIdeal`, with membership, coefficient-map, and
finite-generation lemmas. This repository’s pinned build uses its local
foundational definitions and provides the KRS correspondence, straightening
law, Hilbert-function argument, and Gröbner-basis theorems.

## Repository layout

| Path | Contents |
| --- | --- |
| [`MyProject.lean`](MyProject.lean) and [`MyProject/Determinantalideals/`](MyProject/Determinantalideals/) | Lean library and project import |
| [`Examples/`](Examples/) | Examples using the public theorems |
| [`PaperAudit.lean`](PaperAudit.lean) and [`Audit.lean`](Audit.lean) | Declaration signatures and transitive axiom reports |
| [`scripts/`](scripts/), [`audit/`](audit/), and [`.github/workflows/`](.github/workflows/) | Automated verification, axiom allowlist, and CI |
| [`docs/`](docs/) | Proof outline, statement correspondence, and design notes |

## Requirements and build

Install Git and [elan](https://lean-lang.org/install/manual/). The project uses
Lean 4.28.0, Mathlib v4.28.0, and the `groebner` package v4.28.0. The toolchain
and dependency revisions are recorded in [`lean-toolchain`](lean-toolchain),
[`lakefile.toml`](lakefile.toml), and [`lake-manifest.json`](lake-manifest.json).

```bash
git clone https://github.com/WangJiabai/Determinantal-Ideals-Formalization.git
cd Determinantal-Ideals-Formalization
lake exe cache get
lake build
```

## Verification

Lean elaborates the proofs and checks the resulting terms in its kernel. The
audit compiles the public signatures and examples, scans tracked Lean sources
for unfinished proofs and disallowed declarations, and checks the transitive
axiom dependencies of selected theorems. Run it after the build with Bash and
Python 3.11 or later.

```bash
bash scripts/check_artifact.sh --skip-build
```

See the [reproducibility guide](REPRODUCIBILITY.md) for clean checkout
instructions, individual checks, and how to interpret the axiom reports.

## Related work

- Bernd Sturmfels, “Gröbner Bases and Stanley Decompositions of Determinantal
  Rings,” *Mathematische Zeitschrift* 205 (1990), 137–144.
  [Author’s publication list](https://math.berkeley.edu/~bernd/articles.html)
- Peter Doubilet, Gian-Carlo Rota, and Joel Stein, “On the Foundations of
  Combinatorial Theory IX. Combinatorial Methods in Invariant Theory,”
  *Studies in Applied Mathematics* 53 (1974), 185–216.
  [Publisher](https://doi.org/10.1002/sapm1974533185)
- Richard G. Swan, “On the Straightening Law for Minors of a Matrix.”
  [arXiv:1605.06696](https://arxiv.org/abs/1605.06696)

## Citation and license

Cite Jiabai Wang, *Determinantal Ideals in Lean 4*, the repository URL, and the
full Git commit SHA used. Machine-readable citation metadata is available in
[`CITATION.cff`](CITATION.cff). The project is licensed under
[Apache-2.0](LICENSE).
