# Determinantal Ideals Formalization

This repository is a Lean 4 formalization project for determinantal ideals and
the algebraic infrastructure around minors of generic matrices. Its long-term
goal is to support a proof that the set of `t x t` minors of the generic matrix
forms a Groebner basis under a diagonal term order.

The project is research-oriented and proof-focused. It develops definitions and
lemmas for generic matrices, minor indices, determinantal ideals, diagonal
orders, leading terms, base change, and paper-guided Groebner basis arguments.

## Project Structure

- `MyProject.lean` imports the main formalization modules.
- `MyProject/Determinantalideals/Basic.lean` defines generic matrices, minor
  indices, generic minors, and the set of minors.
- `MyProject/Determinantalideals/Ideal.lean` develops determinantal ideal
  definitions and related ideal-level API.
- `MyProject/Determinantalideals/MinorTerms.lean` and
  `MyProject/Determinantalideals/MinorLeadingTerm.lean` contain results about
  terms and leading terms of minors.
- `MyProject/Determinantalideals/DiagonalOrder.lean` contains diagonal term
  order infrastructure.
- `MyProject/Determinantalideals/BaseChange.lean`,
  `Eval.lean`, and `ConcreteMatrix.lean` provide supporting algebraic
  constructions.
- `MyProject/Determinantalideals/PaperWay.lean` follows a paper-style proof
  route toward the Groebner basis theorem.

## Dependencies

The project uses:

- Lean `v4.28.0`
- Mathlib `v4.28.0`
- the external `groebner` package from
  `https://github.com/WuProver/groebner_proj.git`

The exact versions are recorded in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

## Building

To build the project, run:

```bash
lake build
```

For focused checking of a single file, use:

```bash
lake env lean MyProject/Determinantalideals/Basic.lean
```

## Development Notes

This is not a general-purpose Lean playground. Changes should preserve the
mathematical statements and align with the existing determinantal-ideal and
Groebner APIs. Prefer small local lemmas and proof-oriented changes over broad
refactors.
