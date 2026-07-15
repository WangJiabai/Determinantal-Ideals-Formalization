# Design Choices

This document records formalization cases, not a reconstruction of development
history. Each direct alternative is hypothetical unless repository history
explicitly establishes otherwise.

## Design case: Generic matrix and minor indices

### Mathematical requirement

A generic `m × n` matrix needs one algebraically independent variable at each
matrix position, and a minor needs increasing row and column selections.

### Direct alternative

One could use custom variables plus lists or finsets carrying cardinality,
distinctness, sortedness, and range side conditions.

### Formalization cost or failure mode

Those invariants would recur in every determinant, deletion, and content lemma;
finsets would also erase the order used to present a determinant.

### Chosen representation or API

`Matrix.mvPolynomialX` uses positions `Fin m × Fin n` directly as variable
indices. `Matrix.MinorIndex m n t` stores ordered embeddings
`Fin t ↪o Fin m` and `Fin t ↪o Fin n`, whose types package strict increase
and bounds.

### Downstream payoff

Submatrices have the correct shape by construction, and generic-minor,
evaluation, content, and term-order lemmas share one index type.

### Reusable lesson

Encode monotonicity and bounds in structural data when they are invariants of
nearly every later theorem.

## Design case: Compatibility layer

### Mathematical requirement

The proof needs concise paper-facing names while the reusable algebraic layer
should follow Mathlib namespace and naming conventions.

### Direct alternative

All proof files could use the lower-level `Matrix` and `MvPolynomial` names, or
the reusable API could adopt only project-specific notation.

### Formalization cost or failure mode

The first choice obscures the paper correspondence; the second makes the
generic-minor foundation harder to reuse and review.

### Chosen representation or API

`DeterminantalIdeal.lean` provides a project-local API following Mathlib
namespace and naming conventions. `Basic.lean` retains compatibility names
such as `genericMinor`, `minorSet`, and `detIdeal`, including the older
`genericMatrix` abbreviation.

### Downstream payoff

The main proof remains stable and readable while foundational declarations can
be used without paper notation.

### Reusable lesson

A thin, explicit compatibility layer is preferable to duplicating definitions
or forcing one naming audience onto every module.

## Design case: KRS representation pipeline

### Mathematical requirement

KRS must relate monomial multiplicities to standard bitableaux while preserving
content, total degree, and width and admitting a proved inverse.

### Direct alternative

An exponent vector could be treated informally as if it were already a
generalized permutation or tableau pair.

### Formalization cost or failure mode

An exponent vector is a multiplicity function, whereas insertion consumes an
ordered word. Identifying them directly hides sorting, repeated entries, shape
bounds, and inverse-correctness obligations.

### Chosen representation or API

The pipeline is

```text
exponent vector
→ sorted biword/generalized permutation
→ same-shape bounded tableau pair
→ standard Young bitableau.
```

Each interface proves the relevant multiplicity/content equality, degree and
width theorem, and left/right inverse statement. The composition is
`KRS.krsEquiv`.

### Downstream payoff

`KRS.krs_degree` and `KRS.krs_width` become stable public consequences, and
degree/width filtered types can be counted by restricting an actual
equivalence.

### Reusable lesson

Make changes of representation explicit when the intermediate ordering or
invariants carry the content of the proof.

## Design case: Abstract anti-diagonal predicate

### Mathematical requirement

The final argument needs only that the reverse-permutation exponent wins in
every generic minor.

### Direct alternative

The complete development could be tied directly to one constructed
lexicographic order.

### Formalization cost or failure mode

Order construction details would leak into leading-term and Hilbert-function
lemmas, preventing reuse for another order with the same mathematical
property.

### Chosen representation or API

`IsAntidiagonalTermOrder ord` states the required comparisons abstractly.
`antiDiagonalLex` is constructed separately and proved to satisfy it.

### Downstream payoff

All composition lemmas and the main theorem quantify an arbitrary satisfying
order; the concrete theorem is a one-line specialization.

### Reusable lesson

Abstract the exact semantic property consumed downstream, then prove concrete
constructions are instances.

## Design case: Coefficient-sensitive leading terms

### Mathematical requirement

The paper’s anti-diagonal initial monomial must be connected to Lean’s
coefficient-carrying leading term.

### Direct alternative

One could refer everywhere to a “leading monomial” without fixing whether that
means an exponent, a coefficient-one polynomial, or a signed term.

### Formalization cost or failure mode

For an anti-diagonal minor the reverse permutation contributes
`sign(Fin.revPerm)`, so the coefficient need not be literally `1`. Conflation
would make equalities false or conceal a required unit argument.

### Chosen representation or API

The source separately proves the exponent theorem (`ord.degree`), leading
coefficient theorem, and signed `leadingTerm` theorem. Over a field, the sign
is normalized as a unit to show that signed terms and coefficient-one
anti-diagonal monomials generate the same ideal.

### Downstream payoff

The combinatorial width ideal can be used without misstating the actual
`leadingTerm`, and the missing reducedness refinement is visible rather than
silently assumed.

### Reusable lesson

At every Gröbner interface, specify whether a claim is exponent-level,
monomial-level, coefficient-level, or term-level.

## Design case: Filtered straightening and independent uniqueness

### Mathematical requirement

The quotient proof needs spanning with total-degree and largest-minor support,
then linear independence and a basis.

### Direct alternative

An unfiltered spanning theorem could be called the straightening law, with
uniqueness treated as implicit.

### Formalization cost or failure mode

Spanning alone does not control which terms vanish modulo `Jr`, does not yield
a quotient basis, and cannot justify a Hilbert-function cardinality. Assuming
unique coefficients during the existence proof would be circular.

### Chosen representation or API

The Doubilet–Rota–Stein straightening law is developed via Swan’s
Laplace-product proof. Filtered existence records equal degree and output
length at least input length. Polynomial linear independence is proved
independently; uniqueness is then derived, followed separately by quotient
spanning, quotient independence, and the basis.

### Downstream payoff

The filtration proves large-minor vanishing survives straightening, while the
independent uniqueness argument licenses coefficient comparison and exact
dimension counts.

### Reusable lesson

Separate constructive spanning, support control, and independence before
packaging a unique normal form.

## Design case: Degree-wise Hilbert-function contradiction

### Mathematical requirement

Failure of the proposed Gröbner basis must contradict equality of Hilbert
functions.

### Direct alternative

The paper-level sentence “strict initial-ideal containment changes the Hilbert
function” could be used as one opaque lemma.

### Formalization cost or failure mode

Lean must expose the degree in which strictness occurs and connect ideal
membership, quotient subspaces, finite dimension, and counted monomials.

### Chosen representation or API

The proof decomposes the argument into failed initial-ideal inclusion, a
coefficient-one monomial witness, its total degree, homogeneous components, a
proper-subspace/strict-finrank inequality, normal-monomial counting, and the
contradiction with the determinantal quotient Hilbert function.

### Downstream payoff

Each bridge can be inspected and reused in other structural Gröbner-basis
proofs whose final step is a graded dimension comparison.

### Reusable lesson

Turn an existential graded contradiction into an explicit homogeneous witness
and small linear-algebra interfaces.

## Design case: Dependency separation

### Mathematical requirement

Reusable generic-minor algebra, combinatorial normal forms, and the final
Gröbner theorem have different dependencies and review surfaces.

### Direct alternative

A top-level aggregate import or one large proof file could define what counts
as “core”.

### Formalization cost or failure mode

Aggregation hides the real dependency graph and can make unrelated reusable
APIs appear necessary for the final theorem.

### Chosen representation or API

The core path is the generic-minor/determinantal-ideal foundation, followed by
`Bitableaux.lean`, `KRScorrespondence.lean`, `StraighteningLaw.lean`, and
`Groebner.lean`. The submitted Lean sources are restricted to this transitive
dependency closure. The external `Groebner` package enters at the final layer.

### Downstream payoff

Reviewers can separate algebraic API, KRS/straightening combinatorics, and the
final Hilbert-function theorem without reviewing unrelated auxiliary modules.

### Reusable lesson

Scope the submitted artifact to the target module’s transitive imports together
with its reviewer-facing documentation, audits, and build infrastructure.

## Design case: Current package name

### Mathematical requirement

Imports require a stable root name, but artifact documentation should not
present a placeholder as a mathematical design choice.

### Direct alternative

The Lake package, library, source directory, root module, and every import
could be renamed in this documentation-focused change.

### Formalization cost or failure mode

That is a compatibility-breaking, high-churn operation affecting downstream
users and CI, unrelated to the mathematical corrections here.

### Chosen representation or API

The current import prefix remains `MyProject`. A repository-wide rename is
intentionally deferred to a separate compatibility-breaking refactor.

### Downstream payoff

This revision changes documentation and audits without import churn or public
API breakage.

### Reusable lesson

Isolate namespace migrations from factual documentation corrections so each
change has a reviewable compatibility boundary.

## Design case: Paper-facing artifact synchronization

### Mathematical requirement

The manuscript’s declarations, signatures, commit, dependency versions, and
source links must agree with the frozen artifact revision.

### Direct alternative

Theorem names, SHA values, line numbers, and dependency hashes could be copied
manually into the manuscript.

### Formalization cost or failure mode

Manual data drifts after source or documentation changes: a theorem block can
retain an old type, or a link can silently point to a mutable or obsolete
revision.

### Chosen representation or API

`PaperAudit.lean` compiles manuscript-facing names and types; `Audit.lean` and
`scripts/check_axioms.py` report and allowlist logical dependencies;
`scripts/artifact_metadata.py` reads revision/package metadata; and
`scripts/paper_links.py` locates declarations at the current commit. CI runs
the non-publishing checks.

### Downstream payoff

The theorem map, artifact metadata, and fixed permalinks can be generated or
checked mechanically from the same revision.

### Reusable lesson

Treat the manuscript-facing interface as an audited API rather than a manually
maintained theorem list. These tools verify names, types, dependencies, and
version synchronization; they do not validate the manuscript’s mathematical
prose by themselves.
