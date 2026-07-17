# Design Choices

This document records design cases in the formalization; it does not
reconstruct the project’s development history. Every option described under
“Direct alternative” is hypothetical unless the repository history explicitly
shows otherwise.

## Design case: Generic matrix and minor indices

### Mathematical requirement

A generic `m × n` matrix needs one algebraically independent variable at each
matrix position, and a minor needs increasing row and column selections.

### Direct alternative

One could use custom variables together with lists or finsets and carry
separate proofs of cardinality, distinctness, sortedness, and range
constraints.

### Formalization cost or failure mode

Proof obligations for these invariants would recur in every lemma about
determinants, deletion, or content; finsets would also discard the ordering
used to write a determinant.

### Chosen representation or API

`Matrix.mvPolynomialX` uses matrix positions `Fin m × Fin n` directly as
variable indices. `Matrix.MinorIndex m n t` stores the row and column
selections as order embeddings `Fin t ↪o Fin m` and `Fin t ↪o Fin n`; these
types encode strict monotonicity and bounds.

### Downstream payoff

Submatrices have the correct shape by construction, and lemmas about generic
minors, evaluation, content, and term orders all use the same index type.

### Reusable lesson

Encode monotonicity and bounds in structural data when they are invariants of
nearly every later theorem.

## Design case: Compatibility layer

### Mathematical requirement

The proof needs concise names aligned with the paper, while the reusable
algebraic layer should follow Mathlib namespace and naming conventions.

### Direct alternative

All proof files could use the lower-level `Matrix` and `MvPolynomial` names, or
the reusable API could adopt only project-specific notation.

### Formalization cost or failure mode

The first choice would make the correspondence with the paper harder to
follow; the second would make the generic-minor foundation harder to reuse and
review.

### Chosen representation or API

`DeterminantalIdeal.lean` provides a project-local foundational API that
follows Mathlib namespace and naming conventions. `Basic.lean` retains the
compatibility names `genericMatrix`, `genericMinor`, and `minorSet`, while
`Ideal.lean` provides `detIdeal`.

### Downstream payoff

The main proof retains concise, paper-facing notation, while the foundational
declarations remain usable through Mathlib-style names.

### Reusable lesson

A thin, explicit compatibility layer is preferable to duplicating definitions
or imposing a single naming convention on every module.

## Design case: KRS representation pipeline

### Mathematical requirement

KRS must relate monomial multiplicities to standard Young bitableaux, preserve
content, total degree, and width, and provide a proved inverse.

### Direct alternative

An exponent vector could be treated informally as if it were already a
generalized permutation or tableau pair.

### Formalization cost or failure mode

An exponent vector is a multiplicity function, whereas insertion consumes an
ordered word. Treating these representations as identical would obscure
sorting, repeated entries, shape bounds, and the proof obligations for the
inverse.

### Chosen representation or API

The pipeline is

```text
exponent vector
→ sorted biword/generalized permutation
→ same-shape bounded tableau pair
→ standard Young bitableau.
```

At each interface, the development proves the relevant multiplicity and
content equalities, degree and width properties, and left- and right-inverse
statements. Their composition is `KRS.krsEquiv`.

### Downstream payoff

`KRS.krs_degree` and `KRS.krs_width` provide the public degree and width
statements, and the equivalence can be restricted to count degree- and
width-filtered subtypes.

### Reusable lesson

Make changes of representation explicit whenever the intermediate ordering or
invariants carry essential mathematical content.

## Design case: Abstract anti-diagonal predicate

### Mathematical requirement

The final argument requires only that, in every generic minor, the
reverse-permutation exponent is strictly greater than every other permutation
exponent.

### Direct alternative

The entire development could be tied directly to a single concrete
lexicographic order.

### Formalization cost or failure mode

Details of the order construction would then appear throughout the
leading-term and Hilbert-function lemmas, preventing their reuse for another
order with the same mathematical property.

### Chosen representation or API

`IsAntidiagonalTermOrder ord` states the required comparisons abstractly.
`antiDiagonalLex` is constructed separately and proved to satisfy it.

### Downstream payoff

The general leading-data lemmas and the main theorem quantify over an arbitrary
order satisfying the predicate; the concrete theorem follows by direct
specialization.

### Reusable lesson

Abstract the exact semantic property used downstream, and then prove that
concrete constructions satisfy it.

## Design case: Coefficient-sensitive leading terms

### Mathematical requirement

The paper’s anti-diagonal initial monomial must be connected to Lean’s
coefficient-carrying leading term.

### Direct alternative

One could refer everywhere to a “leading monomial” without fixing whether that
means an exponent, a coefficient-one polynomial, or a signed term.

### Formalization cost or failure mode

For a minor under an anti-diagonal term order, the reverse permutation
contributes the coefficient-ring image of its sign, which need not be literally
`1`. Conflating these notions would make some equalities false or conceal the
required unit argument.

### Chosen representation or API

The Lean development proves separate theorems for the leading exponent
(`ord.degree`), the leading coefficient, and the signed `leadingTerm`. Over a
field, the leading coefficient is a unit, so the signed leading terms and
coefficient-one anti-diagonal monomials generate the same ideal.
`normalizedGenericMinor` makes multiplication by the inverse coefficient
explicit when a monic representative is required.

### Downstream payoff

The combinatorial width ideal can be used without misstating the actual
`leadingTerm`, while the later reducedness theorem can distinguish the
interreduced original family from its monic normalization.

### Reusable lesson

At every Gröbner interface, specify whether a claim is exponent-level,
monomial-level, coefficient-level, or term-level.

## Design case: Interreduction and monic normalization

### Mathematical requirement

The library’s definition of reducedness requires both monicity and the absence
of terms divisible by the leading monomials of other generators. The
determinant family satisfies the second condition before coefficient
normalization.

### Direct alternative

One could treat the original, unnormalized minors as reduced up to units, or
prove reducedness for the normalized set only, in a single combined argument.

### Formalization cost or failure mode

The first choice is false under a definition that requires the leading
coefficient to be literally `1`; a reverse-permutation coefficient can be
`-1`. The second would hide the stronger structural fact that normalization
changes neither the support nor the divisibility relations and is needed only
to obtain monicity.

### Chosen representation or API

`GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder` states the remainder
condition for the original minors. The rigidity lemma
`antidiagExp_le_permExp_imp_minorIndex_eq` proves that if the anti-diagonal
exponent of one minor divides a permutation-term exponent of another, then the
two minor indices are equal. `normalizedGenericMinor` and
`normalizedGrPlusOne` apply the inverse of the common anti-diagonal
coefficient. The lemmas `support_normalizedGenericMinor` and
`leadingCoeff_normalizedGenericMinor` state, respectively, that the support is
unchanged and that, under an anti-diagonal term order, the new leading
coefficient is `1`. The existing Gröbner-basis result is transferred through
unit scalar multiplication, after which reducedness is proved separately.

### Downstream payoff

Users can work with the original family when only Gröbner-basis or
interreduction facts are needed, and with the normalized family when a reduced
Gröbner basis under the library’s monic definition is required. This
separation makes clear that coefficient normalization is the additional step
needed to pass from the interreduced original family to the normalized reduced
family.

### Reusable lesson

When a normal-form API fixes canonical coefficients, separate combinatorial
interreduction from unit normalization instead of hiding the scalar convention.

## Design case: Filtered straightening, independence, and uniqueness

### Mathematical requirement

The quotient proof requires a spanning theorem that controls total degree and
largest-minor size, followed by linear independence and a basis construction.

### Direct alternative

An unfiltered spanning theorem could be called the straightening law, with
uniqueness treated as implicit.

### Formalization cost or failure mode

Spanning alone neither controls which terms vanish modulo `Jr` nor yields a
quotient basis, and it cannot justify a Hilbert-function cardinality formula.
Assuming coefficient uniqueness in the existence proof would be circular.

### Chosen representation or API

The Doubilet–Rota–Stein straightening law is developed via Swan’s
Laplace-product proof. Filtered existence records that every nonzero output
term has the same degree as the input and length at least that of the input.
Polynomial-level linear independence is established by a separate argument,
from which uniqueness follows. The development then proves quotient spanning
and quotient-level linear independence before assembling the basis.

### Downstream payoff

The filtration ensures that the large-minor vanishing condition survives
straightening, while the separate linear-independence argument justifies
coefficient comparison and exact dimension counts.

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

Lean must identify the degree in which strictness occurs and relate ideal
membership, homogeneous subspaces, finite-dimensional quotients, and monomial
counts.

### Chosen representation or API

The proof first turns the failure of the inclusion of the leading-term ideal of
`Jr` in the ideal generated by the leading terms of `GrPlusOne` into a
coefficient-one monomial witness of a fixed total degree. It then shows that
the degree-wise component generated by the leading terms of `GrPlusOne` is a
proper subspace of the corresponding component of the leading-term ideal of
`Jr`, derives a strict finrank inequality, counts normal monomials, and
contradicts the determinantal quotient Hilbert function.

### Downstream payoff

Each intermediate result is explicit and can be reused in other structural
Gröbner-basis proofs whose final step is a graded dimension comparison.

### Reusable lesson

Reduce an existential graded contradiction to an explicit homogeneous witness
and a sequence of focused linear-algebra lemmas.

## Design case: Dependency separation

### Mathematical requirement

Reusable generic-minor algebra, combinatorial normal forms, and the final
Gröbner theorem have distinct dependency requirements and should be reviewable
separately.

### Direct alternative

A top-level aggregate import or one large proof file could define what counts
as “core”.

### Formalization cost or failure mode

Aggregation hides the real dependency graph and can make unrelated reusable
APIs appear necessary for the final theorem.

### Chosen representation or API

The core path begins with the generic-minor, determinantal-ideal, and term-order
foundation, then proceeds through `Bitableaux.lean`,
`KRScorrespondence.lean`, `StraighteningLaw.lean`, and `Groebner.lean`.
`ReducedGroebner.lean` is the final refinement layer: it reuses the
Gröbner-basis theorem and adds interreduction and coefficient normalization.
The theorem-development modules under `MyProject/` are restricted to this
transitive import closure. The external `Groebner` package is imported only at
the final Gröbner-basis and reducedness layers.

### Downstream payoff

Reviewers can assess the algebraic API, the KRS and straightening
combinatorics, and the final Hilbert-function argument as distinct layers.

### Reusable lesson

Scope the submitted artifact to the target module’s transitive imports together
with its reviewer-facing documentation, audits, and build infrastructure.

## Design case: Current package name

### Mathematical requirement

Imports require a stable root name, but artifact documentation should not
present a placeholder as a mathematical design choice.

### Direct alternative

A repository-wide migration could rename the Lake package, library, source
directory, root module, and every import.

### Formalization cost or failure mode

Such a rename would be a high-churn, compatibility-breaking change affecting
downstream users and CI, with no bearing on the mathematical content.

### Chosen representation or API

The current import prefix remains `MyProject`. A repository-wide rename is
intentionally deferred to a separate compatibility-breaking refactor.

### Downstream payoff

Documentation corrections can therefore be reviewed without an unrelated
import migration or public API breakage.

### Reusable lesson

Separate namespace migrations from factual documentation corrections so that
each change has a clear, reviewable compatibility boundary.

## Design case: Paper-facing artifact synchronization

### Mathematical requirement

The Lean declarations and signatures cited in the manuscript, together with
the artifact commit, dependency versions, and source links, must agree with
the frozen artifact revision.

### Direct alternative

Theorem names, SHA values, line numbers, and dependency hashes could be copied
manually into the manuscript.

### Formalization cost or failure mode

Manually maintained data can drift after source or documentation changes: a
theorem block may retain an outdated type, or a link may silently point to a
mutable or obsolete revision.

### Chosen representation or API

`PaperAudit.lean` checks manuscript-facing declaration names and signatures at
compile time. `Audit.lean` reports transitive axiom dependencies, and
`scripts/check_axioms.py` enforces their allowlist.
`scripts/artifact_metadata.py` collects revision and package metadata, while
`scripts/paper_links.py` locates declarations at the current commit. CI runs
the non-publishing checks.

### Downstream payoff

The declaration map, artifact metadata, and fixed permalinks can therefore be
generated or checked mechanically from the same revision.

### Reusable lesson

Treat the manuscript-facing interface as an audited API rather than a manually
maintained theorem list. These tools check declaration names, signatures, and
axiom dependencies, and they generate revision metadata and fixed source links
from the current revision. They support artifact synchronization but do not
validate the manuscript’s mathematical prose.
