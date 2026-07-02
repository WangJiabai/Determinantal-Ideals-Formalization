# Design Choices

## Generic Matrix API

The formalization uses Mathlib's existing

```lean
Matrix.mvPolynomialX
```

for the generic matrix. The older project-level name
`Determinantal.genericMatrix` is kept as a compatibility abbreviation.

## Minor Indices

Minors are indexed by ordered embeddings

```lean
Fin t ↪o Fin m
Fin t ↪o Fin n
```

packaged as `Matrix.MinorIndex m n t`. This representation makes the row and
column order part of the data and avoids repeatedly carrying sorted-list
invariants through determinant statements.

## Compatibility Layer

The file `Basic.lean` keeps the original names such as `genericMinor`,
`minorSet`, and `detIdeal`. The Mathlib-style candidate API lives in
`DeterminantalIdeal.lean` under `Matrix` and `MvPolynomial`.

This lets the proof retain stable paper-oriented names while keeping the basic
generic-minor layer close to Mathlib conventions.

## Separation of Main Components

The formerly monolithic Sturmfels development is split into:

| File | Component |
| --- | --- |
| `Bitableaux.lean` | Bitableaux, standardness, generalized permutations, width, and determinantal quotient notation. |
| `KRScorrespondence.lean` | Forward and reverse KRS algorithms and their equivalence. |
| `StraighteningLaw.lean` | Swan straightening and standard-bitableau basis results. |
| `Groebner.lean` | Hilbert-function comparison and final Grobner-basis theorem. |

The split keeps the final theorem file focused on the Hilbert-function and
Grobner-basis argument rather than the internal mechanics of row insertion and
straightening.

## Package Name

The Lake package is still named `MyProject`. Renaming it would require changing
all imports and likely downstream scripts. That change is intentionally left
out of this cleanup because it is mechanical but high-churn.

## External Grobner Dependency

The final Grobner-basis statements depend on the external `Groebner` package.
The generic-minor and determinantal-ideal foundation is kept separate so that
the reusable algebraic API can be reviewed independently from the final
Sturmfels theorem.
