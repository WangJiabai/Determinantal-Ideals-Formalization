# Proof Outline

The formalization uses standard Young bitableaux to prove the Gröbner-basis
component of Sturmfels’s theorem. It then makes explicit the coefficient
normalization required by the library’s definition of reducedness. Each stage
below explains its mathematical role, its Lean representation, and its
connection to the next stage.

## 1. Generic minors and generated ideals

The proof begins with minors of a generic `m × n` matrix.
`Matrix.mvPolynomialX` supplies the matrix, while `Matrix.MinorIndex m n t`
stores the row and column selections for a `t × t` minor as strictly increasing
embeddings. `Determinantal.genericMinor`, `minorSet`, and `detIdeal` are
compatibility interfaces built on this generic-minor API. In particular,
`Jr m n r k := detIdeal m n (r + 1) k`; Lean defines `Jr` as the ideal generated
by these minors and does not identify it with the rank-variety vanishing ideal.
This layer provides the generators whose leading data are analyzed next.

## 2. Leading exponents, coefficients, and terms

The term-order layer distinguishes four objects that are often conflated in
informal mathematical exposition: `ord.degree p` is the leading exponent,
`MvPolynomial.monomial (ord.degree p) 1` is the corresponding coefficient-one
monomial, `ord.leadingCoeff p` is the leading coefficient, and
`ord.leadingTerm p` combines that monomial with the coefficient. Under
`IsAntidiagonalTermOrder ord`, a minor has the anti-diagonal leading exponent,
while its leading coefficient is
`permCoeff k (Fin.revPerm : Equiv.Perm (Fin t))`, the image of the reverse
permutation’s sign in the coefficient ring. Consequently, its `leadingTerm` is
the anti-diagonal monomial with this coefficient. Over a field, the coefficient
is a unit, so the signed leading terms and coefficient-one anti-diagonal
monomials generate the same ideal.

The abstract theorems apply to every `ord` satisfying
`IsAntidiagonalTermOrder`; `antiDiagonalLex` is a concrete order proved to
satisfy this predicate. This coefficient-sensitive link allows the
combinatorial width ideal to be compared with Lean’s leading-term ideal.

## 3. Young bitableaux, degree, and length

Young bitableaux represent finite products of minors. The field `B.v` records the
number of minor factors. By contrast,

```lean
YoungBitableau.length B := Finset.univ.sup B.size
```

records the largest minor size. For a nonempty bitableau, it equals the size of
the first factor because `shape_antitone` makes the shape weakly decreasing;
the empty bitableau has length `0`. `YoungBitableau.degree B` is the sum of the
factor sizes and therefore the total degree of the associated polynomial.

The auxiliary representation used in straightening, `MinorWord`, makes the
same distinction: `MinorWord.factorCount` is the list length, whereas
`MinorWord.length` is the maximum factor size. The development keeps these
statistics separate because the degree and largest-minor filtrations, rather
than the factor count, govern the quotient by `Jr`.

## 4. KRS correspondence

Forward and reverse insertion are assembled into the equivalence

```lean
KRS.krsEquiv m n :
  ((Fin m × Fin n) →₀ ℕ) ≃ StandardYoungBitableau m n
```

The construction passes from an exponent vector to a sorted generalized
permutation, then to a pair of tableaux of the same shape, and finally to a
standard Young bitableau. `KRS.krs_degree` preserves total degree, while
`KRS.krs_width` identifies monomial width with the length of the corresponding
standard Young bitableau rather than with its factor count. Together, these
results yield the cardinality comparisons used first to prove linear
independence and later to compute the quotient Hilbert function.

## 5. Filtered straightening, independence, and uniqueness

The development formalizes the Doubilet–Rota–Stein straightening law via
Swan’s Laplace-product proof. `straightening_law_exists_filtered` gives an
expansion into standard Young bitableaux. For every term `S` appearing with a
nonzero coefficient,

```lean
YoungBitableau.degree S.1 = YoungBitableau.degree B
YoungBitableau.length B ≤ YoungBitableau.length S.1
```

Thus every nonzero output term has the same total degree as the input and
length at least that of the input. This inequality ensures that an input
containing a minor larger than `r` expands only into standard Young bitableaux
that also vanish modulo `Jr`.

Polynomial-level linear independence is established separately in
`straightening_law_standardBitableau_linearIndependent`, using degree-wise
spanning and the KRS cardinality comparison. Combining filtered existence with
this separately proved linear independence yields
`straightening_law_polynomial_exists_unique`; the public `straightening_law`
then packages the unique expansion together with both support properties. This
separation avoids circularity: the existence argument does not assume
uniqueness.

## 6. Quotient basis of standard Young bitableaux

By determinantal-ideal nesting (`genericMinor_mem_detIdeal_of_le`), every minor
of size greater than `r` belongs to `Jr` and hence vanishes in the quotient.
The length inequality from the previous step supplies quotient spanning.
Polynomial-level independence underpins the coefficient-vanishing theorem for
elements of `Jr`, which in turn establishes linear independence in the
quotient. `exists_standardBitableau_basis_determinantalRing` assembles these
results into a basis indexed by standard Young bitableaux of length at most
`r`. The next step can therefore compute each homogeneous component by
counting the corresponding basis indices.

## 7. Degree-wise Hilbert-function comparison

Using the quotient basis and KRS,
`hilbertFunction_detRing_eq_card_monomialExp_width_le` identifies the degree-`d`
Hilbert function of the determinantal quotient with the number of exponent
vectors of total degree `d` and width at most `r`. On the initial-ideal side,
`lemma6_monomial_mem_initGrPlusOne_iff_width` proves that a coefficient-one
monomial belongs to `initGrPlusOne` exactly when its width is at least `r + 1`.
Equivalently, the normal monomials are precisely those of width at most `r`.
Thus the determinantal quotient and the monomial quotient defined by
`initGrPlusOne` have the same degree-wise count. This equality is the numerical
statement contradicted in the final step.

## 8. Gröbner-basis conclusion

Suppose the leading terms of `GrPlusOne` fail to generate the leading-term
ideal of `Jr`. The proof extracts a coefficient-one monomial that belongs to
the latter ideal but not to the ideal generated by the former terms, and lets
`d` be its total degree. In degree `d`, the component generated by the leading
terms of `GrPlusOne` is a proper subspace of the corresponding component of the
leading-term ideal of `Jr`, so its finrank is strictly smaller. Passing to the
complementary normal-monomial counts shows that the determinantal quotient
Hilbert function is strictly smaller than the width-at-most-`r` count. This
contradicts the equality from Step 7.

`GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder` states the result for
every monomial order satisfying `IsAntidiagonalTermOrder`;
`GrPlusOne_isGroebnerBasis_antiDiagonalLex` specializes it to the concrete
order. These theorems apply to the original, unnormalized minors and supply the
Gröbner-basis input for the coefficient-normalized refinement.

## 9. Coefficient normalization and reducedness

The original minors already satisfy the nondivisibility condition in the
library’s definition of reducedness. More precisely,
`GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder` proves that every minor
is an `IsRemainder` of itself with respect to all the other minors. The key
rigidity statement is
`antidiagExp_le_permExp_imp_minorIndex_eq`: if the anti-diagonal exponent of
one `(r + 1) × (r + 1)` minor divides a permutation-term exponent of another
minor of the same size, then their row and column ranges, and hence their
`MinorIndex` values, are equal. Therefore, the leading exponent of one minor
cannot divide any supported term of a different minor.

Interreduction alone does not make the original family reduced under the
library’s definition, because a reverse-permutation leading coefficient may be
`-1` rather than literally `1`. For each fixed minor size,
`normalizedGenericMinor` multiplies a minor by the inverse of this common
nonzero coefficient, and `normalizedGrPlusOne` collects the normalized minors.
This unit rescaling preserves the support, as stated by
`support_normalizedGenericMinor`, and therefore also preserves the leading
exponent; the normalized family generates the same ideal `Jr`. Under an
anti-diagonal term order, `leadingCoeff_normalizedGenericMinor` states that the
new leading coefficient is `1`. `MonomialOrder.IsGroebnerBasis.smul` then
transfers the Gröbner-basis theorem across the unit rescaling.

`normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder` combines monicity
with the same rigidity argument to prove the library’s `.IsReduced` condition.
`normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder`
packages the existence of a Gröbner-basis proof satisfying this reducedness
condition, while
`theorem1_normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder`
is the paper-numbered alias for this normalized refinement. The
`antiDiagonalLex` corollaries specialize the result to the concrete order;
`normalizedGrPlusOne_isReducedGroebnerBasis_antiDiagonalLex` provides the
corresponding existential wrapper. A geometric gap relative to the source
statement remains: Lean defines `Jr` as the minor-generated ideal and does not
formalize its identification with the rank-variety vanishing ideal.
