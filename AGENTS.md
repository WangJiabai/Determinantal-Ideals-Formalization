# AGENTS.md

## Project

This is a Lean 4/mathlib project formalizing determinantal ideals, standard bitableaux, and the KRS correspondence.

Main file currently under active development:
- `MyProject/Determinantalideals/Sturmfels.lean`

Related files:
- `MyProject/Determinantalideals/Sturmfels_lemma.lean`
- `MyProject/Determinantalideals/Basic.lean`
- `MyProject/Determinantalideals/MinorTerms.lean`
- `MyProject/Determinantalideals/Ideal.lean`
- `MyProject/Determinantalideals/DiagonalOrder.lean`

## Lean workflow

After every nontrivial edit, run the smallest relevant Lean build command first.
Prefer checking only the edited file if possible. If not possible, run the full Lake build.

Do not leave new syntax errors, unresolved names, or type errors.

If a proof is hard, introduce a small mathematically meaningful lemma rather than making a huge fragile proof term.

## Proof style

Do not change theorem statements unless explicitly asked.
Do not weaken definitions or theorem statements to make proofs easier.
Do not encode the desired theorem as a field of a structure.
Do not introduce axioms.
Do not use `admit`.
Do not add new `sorry` unless the task explicitly allows it.
If a task allows temporary `sorry`, clearly report every remaining `sorry`.

Prefer direct proofs inside the current theorem unless a lemma is genuinely reusable.

## KRS formalization strategy

The KRS route should follow this structure:

1. monomial exponent vector ↔ sorted generalized permutation / biword;
2. KRS insertion and reverse KRS between biwords and same-shape semistandard tableau pairs;
3. tableau pair ↔ standard Young bitableau by reading columns as minors;
4. degree preservation via number of boxes;
5. width preservation via Schensted: LDS of lower word equals first-column height.

Use Mathlib `YoungDiagram` and `SemistandardYoungTableau`.
Use the local wrapper:

- `BoundedSSYT μ N`
- `TableauPair m n`

Do not reintroduce a custom independent `Shape` or custom independent `SemistandardTableau`.

## Current priority order

Work in this order unless the user says otherwise:

1. complete local row insertion infrastructure:
   - `replaceTableau`
   - `RowBumpStepResult`
   - `RowAppendStepResult`
   - `RowInsertionTrace`
2. define and prove existence of row insertion traces;
3. implement `rowInsert`;
4. implement `reverseRowInsert`;
5. prove `reverseRowInsert_inverse`;
6. define `krsTableauPair` and `reverseKrsBiword`;
7. prove `reverse_krs_krs` and `krs_reverse_krs`;
8. prove `krs_shape_numBoxes`;
9. prove `schensted_lds_eq_firstColumnHeight`.

Do not attempt Schensted before row insertion and KRS inverse are stable.

## Reporting

At the end of each run, report:

- which declarations were completed;
- which declarations still have `sorry`;
- whether any definitions/theorem statements were changed;
- the exact build/check command used;
- the next recommended target.