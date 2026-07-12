# Proof Outline

The formalization follows the standard-bitableau route to the Gröbner-basis
part of Sturmfels’s theorem. Each stage below states its mathematical role, its
Lean representation, and why the next stage needs it.

## 1. Generic minors and generated ideals

Mathematically, the proof starts with minors of a generic `m × n` matrix.
`Matrix.mvPolynomialX` supplies that matrix, while `Matrix.MinorIndex m n t`
stores strictly increasing row and column embeddings for a `t × t` minor.
`Determinantal.genericMinor`, `minorSet`, and `detIdeal` are compatibility
interfaces over this generic-minor API. In particular,
`Jr m n r k := detIdeal m n (r + 1) k`; it is a generated ideal, not a
formalized rank-variety vanishing ideal. This layer supplies the generators
whose leading objects are studied next.

## 2. Leading exponents, coefficients, and terms

The term-order layer distinguishes four objects that paper prose can easily
conflate: `ord.degree p` is the leading exponent, the corresponding
coefficient-one monomial is `MvPolynomial.monomial (ord.degree p) 1`,
`ord.leadingCoeff p` is the coefficient, and `ord.leadingTerm p` combines the
last two. Under `IsAntidiagonalTermOrder ord`, a minor has anti-diagonal leading
exponent and leading coefficient `Equiv.Perm.sign (Fin.revPerm _)`. Thus its
`leadingTerm` is signed. Because this sign is a unit over a field, the signed
terms and coefficient-one anti-diagonal monomials generate the same ideal.

The abstract theorems apply to every `ord` satisfying
`IsAntidiagonalTermOrder`; `antiDiagonalLex` is a proved concrete instance.
This coefficient-aware bridge is needed before the combinatorial width ideal
can be compared with Lean’s leading-term ideal.

## 3. Young bitableaux, degree, and length

Young bitableaux encode finite products of minors. The field `B.v` records the
number of minor factors. By contrast,

```lean
YoungBitableau.length B := Finset.univ.sup B.size
```

is the largest minor size. For a nonempty bitableau it equals the first
factor’s size because `shape_antitone` makes the shape weakly decreasing; the
empty bitableau has length `0`. `YoungBitableau.degree B` is the sum of all
factor sizes and hence the usual total polynomial degree.

The local straightening representation `MinorWord` makes the same distinction:
`MinorWord.factorCount` is the list length, whereas `MinorWord.length` is the
maximum factor size. These statistics are kept separate because degree and
largest-minor filtrations, rather than factor count, control the quotient by
`Jr`.

## 4. KRS correspondence

Forward insertion and reverse insertion are packaged as

```lean
KRS.krsEquiv m n :
  ((Fin m × Fin n) →₀ ℕ) ≃ StandardYoungBitableau m n
```

The construction passes from an exponent vector to a sorted generalized
permutation, then to a same-shape tableau pair, and finally to a standard Young
bitableau. `KRS.krs_degree` preserves total degree, while `KRS.krs_width`
identifies monomial width with standard-bitableau length—not with factor count.
This gives the cardinality statement needed to prove independence and later to
compute the quotient Hilbert function.

## 5. Filtered straightening and independent uniqueness

The development formalizes the Doubilet–Rota–Stein straightening law through
Swan’s Laplace-product proof. `straightening_law_exists_filtered` first gives
an expansion into standard bitableaux. For every term `S` with nonzero
coefficient,

```lean
YoungBitableau.degree S.1 = YoungBitableau.degree B
YoungBitableau.length B ≤ YoungBitableau.length S.1
```

Thus every output has the same total degree and no smaller length. This is the
direction required to ensure that an input containing a minor larger than `r`
expands only into standard bitableaux that also vanish modulo `Jr`.

Polynomial-level linear independence is proved separately in
`straightening_law_standardBitableau_linearIndependent`, using degree-wise
spanning and the KRS cardinality. Existence plus this independent result yields
`straightening_law_polynomial_exists_unique`; the public
`straightening_law` then packages unique expansion and both support
properties. Keeping independence separate avoids a circular proof that assumes
uniqueness inside the existence argument.

## 6. Standard-bitableau quotient basis

Determinantal-ideal nesting (`genericMinor_mem_detIdeal_of_le`) makes every
minor of size greater than `r` vanish modulo `Jr`. The filtered direction from
the previous step supplies quotient spanning. Polynomial independence and the
coefficient-vanishing theorem for elements of `Jr` supply quotient-level
linear independence independently. These are assembled by
`exists_standardBitableau_basis_determinantalRing` into a basis indexed by
standard bitableaux of length at most `r`. The next step can therefore compute
each homogeneous component by counting basis indices.

## 7. Degree-wise Hilbert-function comparison

`hilbertFunction_detRing_eq_card_monomialExp_width_le` identifies the degree
`d` Hilbert function of the determinantal quotient with exponent vectors of
total degree `d` and width at most `r`, via the quotient basis and KRS. On the
initial-ideal side, `lemma6_monomial_mem_initGrPlusOne_iff_width` turns the same
width bound into normal-monomial membership. Consequently both quotients have
the same degree-wise count. This equality supplies the contradiction invariant
for the last step.

## 8. Gröbner-basis conclusion

Assume the leading terms of `GrPlusOne` fail to generate the leading-term
ideal of `Jr`. Lean extracts a coefficient-one monomial witness, places it in
its total-degree homogeneous component, and derives a proper-subspace (hence
strict finrank) inequality between the corresponding quotient components.
Normal-monomial counting converts that inequality to a strict inequality of
the width-bounded count, contradicting the determinantal quotient Hilbert
function from Step 7.

`GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder` states the result for
an arbitrary anti-diagonal term order;
`GrPlusOne_isGroebnerBasis_antiDiagonalLex` is its concrete specialization.
Neither theorem asserts reducedness.
