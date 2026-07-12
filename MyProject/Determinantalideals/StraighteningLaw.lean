/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.KRScorrespondence

namespace Determinantal

attribute [local instance] MvPolynomial.gradedAlgebra

/-!
## Doubilet–Rota–Stein straightening via Swan’s proof

This module develops the straightening law using Swan’s Laplace-product
argument, then proves polynomial linear independence and the quotient-basis
statements needed by the Gröbner-basis theorem.
-/

/-- One summand in Swan's local two-minor straightening relation.

This is the direct formal output expected from Swan Theorem 4.1 plus
Remark 4.4: a replacement pair of minors, standardly ordered, with strictly
smaller first factor and preserved row/column content. -/
structure SwanTwoMinorTerm
    {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) where
  F : MinorFactor m n
  G : MinorFactor m n
  pairLE : MinorIndex.PairLE F.idx G.idx
  firstLT : MinorIndex.PairLT F.idx I
  row_content :
    MinorWord.rowContent ⟨[F, G]⟩ =
      MinorIndex.rowContent I + MinorIndex.rowContent J
  col_content :
    MinorWord.colContent ⟨[F, G]⟩ =
      MinorIndex.colContent I + MinorIndex.colContent J

namespace SwanTwoMinorTerm

private def finiteCode {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) : MinorFactor m n × MinorFactor m n :=
  (T.F, T.G)

private lemma finiteCode_injective {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} :
    Function.Injective (@finiteCode m n p q I J) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

instance instFinite {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} :
    Finite (SwanTwoMinorTerm I J) := by
  classical
  exact Finite.of_injective (@finiteCode m n p q I J) finiteCode_injective

def toWord {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) : MinorWord m n :=
  ⟨[T.F, T.G]⟩

@[simp] lemma toWord_factors {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    T.toWord.factors = [T.F, T.G] := by
  rfl

lemma pairwisePairLE_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    MinorWord.PairwisePairLE T.toWord := by
  simp [MinorWord.PairwisePairLE, SwanTwoMinorTerm.toWord, T.pairLE]

lemma toPolynomial_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {k : Type*} [CommRing k]
    (T : SwanTwoMinorTerm I J) :
    MinorWord.toPolynomial k T.toWord =
      genericMinor k T.F.idx * genericMinor k T.G.idx := by
  simp [SwanTwoMinorTerm.toWord, MinorFactor.toPolynomial]

lemma rowContent_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    MinorWord.rowContent T.toWord =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  simpa [SwanTwoMinorTerm.toWord] using T.row_content

lemma colContent_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    MinorWord.colContent T.toWord =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  simpa [SwanTwoMinorTerm.toWord] using T.col_content

lemma first_size_nondec {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    p ≤ T.F.t :=
  MinorIndex.PairLE.size_le T.firstLT.pairLE

lemma length_nondec_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    p ≤ MinorWord.length T.toWord := by
  have hpF : p ≤ T.F.t := T.first_size_nondec
  simp only [MinorWord.length, MinorFactor.length, toWord, List.foldr_cons, List.foldr_nil, zero_le,
    sup_of_le_left, le_sup_iff]
  exact Or.inl hpF

lemma degree_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    MinorWord.degree T.toWord = p + q := by
  have hsum :
      (∑ i : Fin m, MinorWord.rowContent T.toWord i) =
        ∑ i : Fin m, (MinorIndex.rowContent I + MinorIndex.rowContent J) i := by
    exact congrArg (fun f : Fin m →₀ ℕ => ∑ i : Fin m, f i) T.rowContent_toWord
  simpa [MinorWord.rowContent_total, Finset.sum_add_distrib,
    MinorIndex.rowContent_total] using hsum

lemma support_data {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanTwoMinorTerm I J) :
    ∃ F G : MinorFactor m n,
      T.toWord.factors = [F, G]
      ∧ MinorIndex.PairLE F.idx G.idx
      ∧ MinorIndex.PairLT F.idx I
      ∧ MinorWord.rowContent T.toWord =
          MinorIndex.rowContent I + MinorIndex.rowContent J
      ∧ MinorWord.colContent T.toWord =
          MinorIndex.colContent I + MinorIndex.colContent J := by
  exact ⟨T.F, T.G, rfl, T.pairLE, T.firstLT, T.row_content, T.col_content⟩

end SwanTwoMinorTerm

/-- One term in Swan's Laplace-product straightening before the strict
first-factor improvement is attached.

The adjective "good" in Swan's Theorem 3.1 is represented here by
`pairLE : F ≤ G`: the produced two-minor product is locally standard.  The
separate weak comparison `firstLE : F ≤ I` is the direct non-strict improvement
from the Laplace-product theorem.  The strict comparison `F < I` used in
Theorem 4.1 is supplied later by Swan Lemma 4.3, not baked into this primitive
Laplace term. -/
structure SwanLaplaceProductTerm
    {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) where
  F : MinorFactor m n
  G : MinorFactor m n
  pairLE : MinorIndex.PairLE F.idx G.idx
  firstLE : MinorIndex.PairLE F.idx I
  row_content :
    MinorWord.rowContent ⟨[F, G]⟩ =
      MinorIndex.rowContent I + MinorIndex.rowContent J
  col_content :
    MinorWord.colContent ⟨[F, G]⟩ =
      MinorIndex.colContent I + MinorIndex.colContent J

namespace SwanLaplaceProductTerm

private def finiteCode {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) : MinorFactor m n × MinorFactor m n :=
  (T.F, T.G)

private lemma finiteCode_injective {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} :
    Function.Injective (@finiteCode m n p q I J) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

instance instFinite {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} :
    Finite (SwanLaplaceProductTerm I J) := by
  classical
  exact Finite.of_injective (@finiteCode m n p q I J) finiteCode_injective

def toWord {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) : MinorWord m n :=
  ⟨[T.F, T.G]⟩

@[simp] lemma toWord_factors {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    T.toWord.factors = [T.F, T.G] := by
  rfl

lemma pairwisePairLE_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    MinorWord.PairwisePairLE T.toWord := by
  simp [MinorWord.PairwisePairLE, SwanLaplaceProductTerm.toWord, T.pairLE]

lemma rowContent_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    MinorWord.rowContent T.toWord =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  simpa [SwanLaplaceProductTerm.toWord] using T.row_content

lemma colContent_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    MinorWord.colContent T.toWord =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  simpa [SwanLaplaceProductTerm.toWord] using T.col_content

lemma degree_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    MinorWord.degree T.toWord = p + q := by
  have hsum :
      (∑ i : Fin m, MinorWord.rowContent T.toWord i) =
        ∑ i : Fin m, (MinorIndex.rowContent I + MinorIndex.rowContent J) i := by
    exact congrArg (fun f : Fin m →₀ ℕ => ∑ i : Fin m, f i) T.rowContent_toWord
  simpa [MinorWord.rowContent_total, Finset.sum_add_distrib,
    MinorIndex.rowContent_total] using hsum

lemma toPolynomial_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {k : Type*} [CommRing k]
    (T : SwanLaplaceProductTerm I J) :
    MinorWord.toPolynomial k T.toWord =
      genericMinor k T.F.idx * genericMinor k T.G.idx := by
  simp [SwanLaplaceProductTerm.toWord, MinorFactor.toPolynomial]

lemma first_size_nondec {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    p ≤ T.F.t :=
  MinorIndex.PairLE.size_le T.firstLE

lemma length_nondec_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    p ≤ MinorWord.length T.toWord := by
  have hpF : p ≤ T.F.t := T.first_size_nondec
  simp only [MinorWord.length, MinorFactor.length, toWord, List.foldr_cons, List.foldr_nil, zero_le,
    sup_of_le_left, le_sup_iff]
  exact Or.inl hpF

lemma support_data {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J) :
    ∃ F G : MinorFactor m n,
      T.toWord.factors = [F, G]
      ∧ MinorIndex.PairLE F.idx G.idx
      ∧ MinorIndex.PairLE F.idx I
      ∧ MinorWord.rowContent T.toWord =
          MinorIndex.rowContent I + MinorIndex.rowContent J
      ∧ MinorWord.colContent T.toWord =
          MinorIndex.colContent I + MinorIndex.colContent J := by
  exact ⟨T.F, T.G, rfl, T.pairLE, T.firstLE, T.rowContent_toWord, T.colContent_toWord⟩

lemma firstLT_of_not_original_le_first {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J)
    (hnot : ¬ MinorIndex.PairLE I T.F.idx) :
    MinorIndex.PairLT T.F.idx I :=
  MinorIndex.PairLT.of_pairLE_not_symm T.firstLE hnot

/-- Attach the strict first-factor decrease supplied by Swan Lemma 4.3 to a
Laplace-product term, obtaining the local term used by Theorem 4.1. -/
def toSwanTwoMinorTerm {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J)
    (hstrict : MinorIndex.PairLT T.F.idx I) :
    SwanTwoMinorTerm I J where
  F := T.F
  G := T.G
  pairLE := T.pairLE
  firstLT := hstrict
  row_content := T.row_content
  col_content := T.col_content

@[simp] lemma toSwanTwoMinorTerm_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanLaplaceProductTerm I J)
    (hstrict : MinorIndex.PairLT T.F.idx I) :
    (T.toSwanTwoMinorTerm hstrict).toWord = T.toWord := by
  rfl

end SwanLaplaceProductTerm

/-- Swan's Laplace-product straightening data before Lemma 4.3 upgrades the
first factor from weakly improved to strictly improved.

This is the finite-sum object corresponding to Swan Theorem 3.1 in the local
two-minor setting. -/
structure SwanLaplaceProductExpansion
    (k : Type*) [Field k]
    {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) where
  ι : Type
  instFintype : Fintype ι
  coeff : ι → k
  term : ι → SwanLaplaceProductTerm I J
  poly_eq :
    genericMinor k I * genericMinor k J =
      ∑ x : ι,
        MvPolynomial.C (coeff x) *
          MinorWord.toPolynomial k
            (SwanLaplaceProductTerm.toWord (term x))

attribute [instance] SwanLaplaceProductExpansion.instFintype

/-- A finite local Swan expansion, before it is converted to a finsupp.

This mirrors the displayed finite sum in Swan Theorem 4.1: the index type
enumerates the nonzero replacement pairs, `coeff` gives their signed
coefficients, and `term` carries the ordered/content-preserving replacement
data. -/
structure SwanTwoMinorExpansion
    (k : Type*) [Field k]
    {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) where
  ι : Type
  instFintype : Fintype ι
  coeff : ι → k
  term : ι → SwanTwoMinorTerm I J
  poly_eq :
    genericMinor k I * genericMinor k J =
      ∑ x : ι,
        MvPolynomial.C (coeff x) *
          MinorWord.toPolynomial k
            (SwanTwoMinorTerm.toWord (term x))

attribute [instance] SwanTwoMinorExpansion.instFintype

/-- A product that is already good is its own one-term Laplace-product
expansion. -/
lemma swan_laplace_product_expansion_of_pairLE
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hIJ : MinorIndex.PairLE I J) :
    Nonempty (SwanLaplaceProductExpansion k I J) := by
  classical
  let F : MinorFactor m n := { t := p, idx := I }
  let G : MinorFactor m n := { t := q, idx := J }
  let T : SwanLaplaceProductTerm I J :=
    { F := F
      G := G
      pairLE := hIJ
      firstLE := MinorIndex.PairLE.refl I
      row_content := by
        simp [F, G, MinorFactor.rowContent]
      col_content := by
        simp [F, G, MinorFactor.colContent] }
  refine ⟨
    { ι := PUnit
      instFintype := inferInstance
      coeff := fun _ => (1 : k)
      term := fun _ => T
      poly_eq := ?_ }⟩
  simp [T, SwanLaplaceProductTerm.toWord, F, G, MinorFactor.toPolynomial]

/-- A raw two-factor Laplace product during Swan's reduction process.

Unlike `SwanLaplaceProductTerm`, this does not assume the two factors are
already good/ordered.  Corollary 2.7 reduces a bad raw term to a finite sum of
raw terms of smaller rank; Corollary 2.8 is the separate termination statement
which iterates that reduction until only good terms remain. -/
structure SwanRawLaplaceProductTerm
    {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) where
  F : MinorFactor m n
  G : MinorFactor m n
  firstLE : MinorIndex.PairLE F.idx I
  row_content :
    MinorWord.rowContent ⟨[F, G]⟩ =
      MinorIndex.rowContent I + MinorIndex.rowContent J
  col_content :
    MinorWord.colContent ⟨[F, G]⟩ =
      MinorIndex.colContent I + MinorIndex.colContent J

namespace SwanRawLaplaceProductTerm

def toWord {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) : MinorWord m n :=
  ⟨[T.F, T.G]⟩

def toRawPair {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) : RawMinorPair m n where
  p := T.F.t
  q := T.G.t
  left := RawMinorIndex.ofMinorIndex T.F.idx
  right := RawMinorIndex.ofMinorIndex T.G.idx

@[simp] lemma toRawPair_p {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    T.toRawPair.p = T.F.t := rfl

@[simp] lemma toRawPair_q {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    T.toRawPair.q = T.G.t := rfl

lemma toRawPair_toPolynomial {m n p q : ℕ}
    {k : Type*} [CommRing k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.toPolynomial k T.toRawPair =
      MinorWord.toPolynomial k T.toWord := by
  simp [SwanRawLaplaceProductTerm.toRawPair, SwanRawLaplaceProductTerm.toWord,
    RawMinorPair.toPolynomial, MinorFactor.toPolynomial]

lemma toRawPair_rowContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.rowContent T.toRawPair =
      MinorWord.rowContent T.toWord := by
  simp [SwanRawLaplaceProductTerm.toRawPair, SwanRawLaplaceProductTerm.toWord,
    RawMinorPair.rowContent, MinorFactor.rowContent]

lemma toRawPair_colContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.colContent T.toRawPair =
      MinorWord.colContent T.toWord := by
  simp [SwanRawLaplaceProductTerm.toRawPair, SwanRawLaplaceProductTerm.toWord,
    RawMinorPair.colContent, MinorFactor.colContent]

lemma toRawPair_laplacePolynomial {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [CommRing k]
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.laplacePolynomial k T.toRawPair =
      MvPolynomial.C (RawMinorPair.laplaceCoeff k T.toRawPair) *
        MinorWord.toPolynomial k T.toWord := by
  simp [RawMinorPair.laplacePolynomial, T.toRawPair_toPolynomial]

/-- Promote a raw two-minor pair to a raw Swan Laplace-product term once the
two raw factors are honest increasing minors and the first factor has the
required weak improvement. -/
def ofRawPairOfStrictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col)
    (hfirst :
      MinorIndex.PairLE (P.left.toMinorIndexOfStrictMono hLrow hLcol) I)
    (hrow :
      RawMinorPair.rowContent P =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      RawMinorPair.colContent P =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    SwanRawLaplaceProductTerm I J where
  F := P.leftFactorOfStrictMono hLrow hLcol
  G := P.rightFactorOfStrictMono hRrow hRcol
  firstLE := hfirst
  row_content := by
    rw [← hrow]
    exact RawMinorPair.rowContent_toMinorWordOfStrictMono P hLrow hLcol hRrow hRcol
  col_content := by
    rw [← hcol]
    exact RawMinorPair.colContent_toMinorWordOfStrictMono P hLrow hLcol hRrow hRcol

@[simp] lemma ofRawPairOfStrictMono_F {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col)
    (hfirst :
      MinorIndex.PairLE (P.left.toMinorIndexOfStrictMono hLrow hLcol) I)
    (hrow :
      RawMinorPair.rowContent P =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      RawMinorPair.colContent P =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    (ofRawPairOfStrictMono P hLrow hLcol hRrow hRcol hfirst hrow hcol).F =
      P.leftFactorOfStrictMono hLrow hLcol := rfl

@[simp] lemma ofRawPairOfStrictMono_G {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col)
    (hfirst :
      MinorIndex.PairLE (P.left.toMinorIndexOfStrictMono hLrow hLcol) I)
    (hrow :
      RawMinorPair.rowContent P =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      RawMinorPair.colContent P =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    (ofRawPairOfStrictMono P hLrow hLcol hRrow hRcol hfirst hrow hcol).G =
      P.rightFactorOfStrictMono hRrow hRcol := rfl

lemma ofRawPairOfStrictMono_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (P : RawMinorPair m n)
    (hLrow : StrictMono P.left.row) (hLcol : StrictMono P.left.col)
    (hRrow : StrictMono P.right.row) (hRcol : StrictMono P.right.col)
    (hfirst :
      MinorIndex.PairLE (P.left.toMinorIndexOfStrictMono hLrow hLcol) I)
    (hrow :
      RawMinorPair.rowContent P =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      RawMinorPair.colContent P =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    (ofRawPairOfStrictMono P hLrow hLcol hRrow hRcol hfirst hrow hcol).toWord =
      P.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol := by
  rfl

lemma toRawPair_left_row_strictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    StrictMono T.toRawPair.left.row := by
  simpa [SwanRawLaplaceProductTerm.toRawPair] using T.F.idx.row.strictMono

lemma toRawPair_left_col_strictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    StrictMono T.toRawPair.left.col := by
  simpa [SwanRawLaplaceProductTerm.toRawPair] using T.F.idx.col.strictMono

lemma toRawPair_right_row_strictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    StrictMono T.toRawPair.right.row := by
  simpa [SwanRawLaplaceProductTerm.toRawPair] using T.G.idx.row.strictMono

lemma toRawPair_right_col_strictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    StrictMono T.toRawPair.right.col := by
  simpa [SwanRawLaplaceProductTerm.toRawPair] using T.G.idx.col.strictMono

lemma reshuffle_toRawPair_rowContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.Reshuffle T.toRawPair) :
    RawMinorPair.rowContent E.toPair =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  rw [RawMinorPair.Reshuffle.rowContent_toPair,
    T.toRawPair_rowContent]
  simpa [SwanRawLaplaceProductTerm.toWord] using T.row_content

lemma reshuffle_toRawPair_colContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.Reshuffle T.toRawPair) :
    RawMinorPair.colContent E.toPair =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  rw [RawMinorPair.Reshuffle.colContent_toPair,
    T.toRawPair_colContent]
  simpa [SwanRawLaplaceProductTerm.toWord] using T.col_content

lemma biReshuffle_toRawPair_rowContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) :
    RawMinorPair.rowContent E.toPair =
      MinorIndex.rowContent I + MinorIndex.rowContent J := by
  rw [RawMinorPair.BiReshuffle.rowContent_toPair,
    T.toRawPair_rowContent]
  simpa [SwanRawLaplaceProductTerm.toWord] using T.row_content

lemma biReshuffle_toRawPair_colContent {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) :
    RawMinorPair.colContent E.toPair =
      MinorIndex.colContent I + MinorIndex.colContent J := by
  rw [RawMinorPair.BiReshuffle.colContent_toPair,
    T.toRawPair_colContent]
  simpa [SwanRawLaplaceProductTerm.toWord] using T.col_content

/-- Turn a nonzero bi-reshuffle term from Swan's Laplace relation into the raw
term type used by the reduction.  The hypotheses that the reshuffled factors
are strictly increasing are exactly the nonzero determinant conditions. -/
def ofBiReshuffleOfStrictMono {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col)
    (hfirst :
      MinorIndex.PairLE
        (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I) :
    SwanRawLaplaceProductTerm I J :=
  ofRawPairOfStrictMono E.toPair hLrow hLcol hRrow hRcol hfirst
    (T.biReshuffle_toRawPair_rowContent E)
    (T.biReshuffle_toRawPair_colContent E)

lemma ofBiReshuffleOfStrictMono_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col)
    (hfirst :
      MinorIndex.PairLE
        (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I) :
    (T.ofBiReshuffleOfStrictMono E hLrow hLcol hRrow hRcol hfirst).toWord =
      E.toPair.toMinorWordOfStrictMono hLrow hLcol hRrow hRcol := by
  rfl

lemma ofBiReshuffleOfStrictMono_laplacePolynomial {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [CommRing k]
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col)
    (hfirst :
      MinorIndex.PairLE
        (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I) :
    RawMinorPair.laplacePolynomial k E.toPair =
      MvPolynomial.C (RawMinorPair.laplaceCoeff k T.toRawPair) *
        MinorWord.toPolynomial k
          (T.ofBiReshuffleOfStrictMono E hLrow hLcol hRrow hRcol hfirst).toWord := by
  rw [RawMinorPair.BiReshuffle.laplacePolynomial_toPair]
  rw [T.ofBiReshuffleOfStrictMono_toWord E hLrow hLcol hRrow hRcol hfirst]
  rw [RawMinorPair.toPolynomial_toMinorWordOfStrictMono k]

def IsGood {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) : Prop :=
  MinorIndex.PairLE T.F.idx T.G.idx

/-- The concrete obstruction witnessing that a raw Laplace product is bad. -/
inductive BadWitness {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) : Prop
  | size : T.F.t < T.G.t → BadWitness T
  | component :
      (hsize : T.G.t ≤ T.F.t) →
      (j : Fin T.G.t) →
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j) →
      BadWitness T

lemma bad_cases {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) (hbad : ¬ T.IsGood) :
    T.F.t < T.G.t ∨
      ∃ (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t),
        ¬
          (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
           T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j) := by
  exact MinorIndex.not_pairLE_or_violation hbad

noncomputable def badWitness {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) (hbad : ¬ T.IsGood) :
    BadWitness T := by
  classical
  rcases T.bad_cases hbad with hsize | hviol
  · exact BadWitness.size hsize
  · rcases hviol with ⟨hsize, j, hj⟩
    exact BadWitness.component hsize j hj

lemma exists_violation_of_bad_of_size_le {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) (hbad : ¬ T.IsGood) :
    ∃ j : Fin T.G.t,
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j) := by
  exact MinorIndex.exists_violation_of_not_pairLE_of_size_le hsize hbad

/-- A component defect witnessed in the rows at position `j`. -/
def RowBadAt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t) : Prop :=
  T.G.idx.row j <
    T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩

/-- A component defect witnessed in the columns at position `j`. -/
def ColBadAt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t) : Prop :=
  T.G.idx.col j <
    T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩

lemma rowBad_or_colBad_of_component_violation {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t)
    (hj :
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j)) :
    RowBadAt T hsize j ∨ ColBadAt T hsize j := by
  classical
  by_cases hrow :
      T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j
  · right
    have hcol :
        ¬ T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤
            T.G.idx.col j := by
      intro hcol
      exact hj ⟨hrow, hcol⟩
    exact not_le.mp hcol
  · left
    exact not_le.mp hrow

noncomputable def rowBadFinset {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) : Finset (Fin T.G.t) :=
  by
    classical
    exact Finset.univ.filter fun j => RowBadAt T hsize j

noncomputable def colBadFinset {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) : Finset (Fin T.G.t) :=
  by
    classical
    exact Finset.univ.filter fun j => ColBadAt T hsize j

/-- The first row component where the old first factor is too large. -/
noncomputable def minimalRowBadIndex {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (rowBadFinset T hsize).Nonempty) : Fin T.G.t :=
  (rowBadFinset T hsize).min' hne

/-- The first column component where the old first factor is too large. -/
noncomputable def minimalColBadIndex {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (colBadFinset T hsize).Nonempty) : Fin T.G.t :=
  (colBadFinset T hsize).min' hne

lemma minimalRowBadIndex_bad {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (rowBadFinset T hsize).Nonempty) :
    RowBadAt T hsize (minimalRowBadIndex T hsize hne) := by
  classical
  have hmem := Finset.min'_mem (rowBadFinset T hsize) hne
  simpa [minimalRowBadIndex, rowBadFinset] using hmem

lemma minimalColBadIndex_bad {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (colBadFinset T hsize).Nonempty) :
    ColBadAt T hsize (minimalColBadIndex T hsize hne) := by
  classical
  have hmem := Finset.min'_mem (colBadFinset T hsize) hne
  simpa [minimalColBadIndex, colBadFinset] using hmem

lemma row_le_before_minimalRowBadIndex {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (rowBadFinset T hsize).Nonempty)
    (μ : Fin T.G.t) (hμ : μ < minimalRowBadIndex T hsize hne) :
    T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
      T.G.idx.row μ := by
  classical
  have hnot : ¬ RowBadAt T hsize μ := by
    intro hbad
    have hmem : μ ∈ rowBadFinset T hsize := by
      simp [rowBadFinset, hbad]
    have hle :
        minimalRowBadIndex T hsize hne ≤ μ := by
      simpa [minimalRowBadIndex] using
        Finset.min'_le (rowBadFinset T hsize) μ hmem
    exact not_lt_of_ge hle hμ
  exact not_lt.mp hnot

lemma col_le_before_minimalColBadIndex {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (hne : (colBadFinset T hsize).Nonempty)
    (μ : Fin T.G.t) (hμ : μ < minimalColBadIndex T hsize hne) :
    T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
      T.G.idx.col μ := by
  classical
  have hnot : ¬ ColBadAt T hsize μ := by
    intro hbad
    have hmem : μ ∈ colBadFinset T hsize := by
      simp [colBadFinset, hbad]
    have hle :
        minimalColBadIndex T hsize hne ≤ μ := by
      simpa [minimalColBadIndex] using
        Finset.min'_le (colBadFinset T hsize) μ hmem
    exact not_lt_of_ge hle hμ
  exact not_lt.mp hnot

/-- Swan's raw reduction order: a product is smaller when its first factor is
strictly smaller in the minor-pair order. -/
def LT {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (A B : SwanRawLaplaceProductTerm I J) : Prop :=
  MinorFactor.PairLT A.F B.F

lemma ofBiReshuffleOfStrictMono_LT {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : StrictMono E.toPair.left.row)
    (hLcol : StrictMono E.toPair.left.col)
    (hRrow : StrictMono E.toPair.right.row)
    (hRcol : StrictMono E.toPair.right.col)
    (hfirst :
      MinorIndex.PairLE
        (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I)
    (hlt :
      MinorIndex.PairLT
        (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) T.F.idx) :
    LT (T.ofBiReshuffleOfStrictMono E hLrow hLcol hRrow hRcol hfirst) T := by
  simpa [LT, MinorFactor.PairLT,
    SwanRawLaplaceProductTerm.ofBiReshuffleOfStrictMono,
    SwanRawLaplaceProductTerm.ofRawPairOfStrictMono,
    RawMinorPair.leftFactorOfStrictMono] using hlt

/-- A bi-reshuffle term that survives the zero filtering in the size branch of
Swan's Laplace relation and is already promotable to the raw reduction term
type. -/
structure BiReshuffleSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) where
  E : RawMinorPair.BiReshuffle T.toRawPair
  hLrow : StrictMono E.toPair.left.row
  hLcol : StrictMono E.toPair.left.col
  hRrow : StrictMono E.toPair.right.row
  hRcol : StrictMono E.toPair.right.col
  firstLE :
    MinorIndex.PairLE
      (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I
  firstLT :
    MinorIndex.PairLT
      (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) T.F.idx

namespace BiReshuffleSupport

private def finiteCode {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (S : BiReshuffleSupport T) :
    RawMinorPair.BiReshuffle T.toRawPair :=
  S.E

private lemma finiteCode_injective {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Function.Injective (@finiteCode m n p q I J T) := by
  intro S S' h
  cases S
  cases S'
  cases h
  rfl

instance instFinite {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Finite (BiReshuffleSupport T) := by
  classical
  exact Finite.of_injective (@finiteCode m n p q I J T) finiteCode_injective

noncomputable instance instFintype {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Fintype (BiReshuffleSupport T) := by
  classical
  exact Fintype.ofFinite (BiReshuffleSupport T)

def toRawTerm {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (S : BiReshuffleSupport T) :
    SwanRawLaplaceProductTerm I J :=
  T.ofBiReshuffleOfStrictMono S.E S.hLrow S.hLcol S.hRrow S.hRcol S.firstLE

lemma toRawTerm_LT {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (S : BiReshuffleSupport T) :
    LT S.toRawTerm T :=
  T.ofBiReshuffleOfStrictMono_LT S.E S.hLrow S.hLcol S.hRrow S.hRcol
    S.firstLE S.firstLT

@[simp] lemma toRawTerm_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (S : BiReshuffleSupport T) :
    S.toRawTerm.toWord =
      S.E.toPair.toMinorWordOfStrictMono S.hLrow S.hLcol S.hRrow S.hRcol := by
  rfl

lemma ext_E {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {S S' : BiReshuffleSupport T}
    (hE : S.E = S'.E) :
    S = S' := by
  cases S
  cases S'
  simp only at hE
  cases hE
  rfl

lemma E_injective {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Function.Injective (fun S : BiReshuffleSupport T => S.E) := by
  intro S S' hE
  exact ext_E hE

/-- A raw bi-reshuffle term survives the determinant filtering precisely when
all four raw factors are strictly increasing and Swan's size-branch comparison
promotes the first factor to a smaller first factor. -/
def IsPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ hLrow : StrictMono E.toPair.left.row,
  ∃ hLcol : StrictMono E.toPair.left.col,
  ∃ _hRrow : StrictMono E.toPair.right.row,
  ∃ _hRcol : StrictMono E.toPair.right.col,
  ∃ _firstLE :
    MinorIndex.PairLE
      (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) I,
    MinorIndex.PairLT
      (E.toPair.left.toMinorIndexOfStrictMono hLrow hLcol) T.F.idx

noncomputable def toPromotableSubtype {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (S : BiReshuffleSupport T) :
    { E : RawMinorPair.BiReshuffle T.toRawPair // IsPromotable T E } :=
  ⟨S.E, S.hLrow, S.hLcol, S.hRrow, S.hRcol, S.firstLE, S.firstLT⟩

noncomputable def ofSortedInjective {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : Function.Injective E.toPair.left.row)
    (hLcol : Function.Injective E.toPair.left.col)
    (hRrow : Function.Injective E.toPair.right.row)
    (hRcol : Function.Injective E.toPair.right.col)
    (firstLE :
      MinorIndex.PairLE
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) I)
    (firstLT :
      MinorIndex.PairLT
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) T.F.idx) :
    BiReshuffleSupport T where
  E := E.sorted
  hLrow := E.sorted_toPair_left_row_strictMono_of_injective hLrow
  hLcol := E.sorted_toPair_left_col_strictMono_of_injective hLcol
  hRrow := E.sorted_toPair_right_row_strictMono_of_injective hRrow
  hRcol := E.sorted_toPair_right_col_strictMono_of_injective hRcol
  firstLE := firstLE
  firstLT := firstLT

@[simp] lemma ofSortedInjective_E {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : Function.Injective E.toPair.left.row)
    (hLcol : Function.Injective E.toPair.left.col)
    (hRrow : Function.Injective E.toPair.right.row)
    (hRcol : Function.Injective E.toPair.right.col)
    (firstLE :
      MinorIndex.PairLE
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) I)
    (firstLT :
      MinorIndex.PairLT
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) T.F.idx) :
    (ofSortedInjective E hLrow hLcol hRrow hRcol firstLE firstLT).E =
      E.sorted := rfl

lemma ofSortedInjective_laplacePolynomial {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {k : Type*} [CommRing k]
    {T : SwanRawLaplaceProductTerm I J}
    (E : RawMinorPair.BiReshuffle T.toRawPair)
    (hLrow : Function.Injective E.toPair.left.row)
    (hLcol : Function.Injective E.toPair.left.col)
    (hRrow : Function.Injective E.toPair.right.row)
    (hRcol : Function.Injective E.toPair.right.col)
    (firstLE :
      MinorIndex.PairLE
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) I)
    (firstLT :
      MinorIndex.PairLT
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hLrow)
          (E.sorted_toPair_left_col_strictMono_of_injective hLcol)) T.F.idx) :
    RawMinorPair.laplacePolynomial k
        (ofSortedInjective E hLrow hLcol hRrow hRcol firstLE firstLT).E.toPair =
      RawMinorPair.sortSign k E.toPair *
        RawMinorPair.laplacePolynomial k E.toPair := by
  simpa [ofSortedInjective] using
    RawMinorPair.BiReshuffle.laplacePolynomial_sorted_toPair k E

def IsSortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ hE : E.AllInjective,
  ∃ _firstLE :
    MinorIndex.PairLE
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
      (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
      (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) I,
    MinorIndex.PairLT
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx

/-- Raw support predicate for the column-side Hodge component branch.

It records the non-pivot `HodgeColSplit` terms whose associated raw
bi-reshuffle survives determinant-zero filtering.  The order-theoretic
promotion to `IsSortedPromotable` is intentionally kept as a separate lemma. -/
def IsComponentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp,
    S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp ∧
      RawMinorPair.BiReshuffle.HodgeColSplit.toBiReshuffle S = E ∧
        E.AllInjective

/-- Raw support predicate for the row-side Hodge component branch. -/
def IsComponentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp,
    S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp ∧
      RawMinorPair.BiReshuffle.HodgeRowSplit.toBiReshuffle S = E ∧
        E.AllInjective

lemma allInjective_of_componentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsComponentColLaplaceSupport T ν hνp E) :
    E.AllInjective := by
  rcases h with ⟨_S, _hne, _hE, hsurvives⟩
  exact hsurvives

lemma allInjective_of_componentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsComponentRowLaplaceSupport T ν hνp E) :
    E.AllInjective := by
  rcases h with ⟨_S, _hne, _hE, hsurvives⟩
  exact hsurvives

noncomputable instance instFintypeComponentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t} :
    Fintype { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsComponentColLaplaceSupport T ν hνp E } := by
  classical
  exact Fintype.ofFinite _

noncomputable instance instFintypeComponentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t} :
    Fintype { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsComponentRowLaplaceSupport T ν hνp E } := by
  classical
  exact Fintype.ofFinite _

/-- The survivor condition for Swan's size-defect branch before collecting
terms into `BiReshuffleSupport`.

In the case `|A| < n / 2`, Corollary 2.8 sums over supersets `U ⊇ A` and
`W ⊇ B`.  After deleting determinant-zero raw terms and sorting the four raw
minors, every non-pivot survivor has a first factor of strictly larger size
than the original first factor, while still lying below it in Swan's
minor-pair order.  This predicate records exactly that local support
condition; the next lemma converts it to the existing `IsSortedPromotable`
interface used downstream. -/
def IsSizeBranchSurvivor {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ hE : E.AllInjective,
  ∃ _firstLEOld :
    MinorIndex.PairLE
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx,
    T.F.t < E.r

/-- Row-slot containment `U ⊇ A` in Swan's size branch: every old left row
slot of `T.toRawPair` is selected among the new left row slots of `E`. -/
def ContainsOriginalLeftRows {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∀ i : Fin T.F.t, ∃ a : Fin E.r, E.rowEquiv (Sum.inl a) = Sum.inl i

/-- Column-slot containment `W ⊇ B` in Swan's size branch: every old left
column slot of `T.toRawPair` is selected among the new left column slots of
`E`. -/
def ContainsOriginalLeftCols {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∀ i : Fin T.F.t, ∃ a : Fin E.r, E.colEquiv (Sum.inl a) = Sum.inl i

lemma containsOriginalLeftRows_id {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    ContainsOriginalLeftRows T (RawMinorPair.BiReshuffle.id T.toRawPair) := by
  intro i
  exact ⟨i, rfl⟩

lemma containsOriginalLeftCols_id {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    ContainsOriginalLeftCols T (RawMinorPair.BiReshuffle.id T.toRawPair) := by
  intro i
  exact ⟨i, rfl⟩

lemma containsOriginalLeftRows_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair) :
    ContainsOriginalLeftRows T S.toBiReshuffle := by
  intro i
  exact S.exists_rowEquiv_inl_eq_inl i

lemma containsOriginalLeftCols_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair) :
    ContainsOriginalLeftCols T S.toBiReshuffle := by
  intro i
  exact S.exists_colEquiv_inl_eq_inl i

lemma containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp) :
    ContainsOriginalLeftRows T S.toBiReshuffle := by
  classical
  intro i
  let x : S.rowSlots := ⟨Fin.castAdd T.toRawPair.q i,
    S.leftRows (RawMinorPair.BiReshuffle.mem_leftSlotFinset_castAdd T.toRawPair i)⟩
  let a : Fin S.rowSlots.card := (S.rowSlots.orderIsoOfFin rfl).symm x
  refine ⟨a, ?_⟩
  simp only [RawMinorPair.BiReshuffle.HodgeColSplit.toBiReshuffle,
    RawMinorPair.BiReshuffle.ofFinsets_rowEquiv_inl]
  have ha :
      S.rowSlots.orderEmbOfFin rfl a = Fin.castAdd T.toRawPair.q i := by
    exact congrArg Subtype.val ((S.rowSlots.orderIsoOfFin rfl).apply_symm_apply x)
  rw [ha, finSumFinEquiv_symm_apply_castAdd]

lemma containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp) :
    ContainsOriginalLeftCols T S.toBiReshuffle := by
  classical
  intro i
  let x : S.colSlots := ⟨Fin.castAdd T.toRawPair.q i,
    S.leftCols (RawMinorPair.BiReshuffle.mem_leftSlotFinset_castAdd T.toRawPair i)⟩
  let a : Fin S.colSlots.card := (S.colSlots.orderIsoOfFin rfl).symm x
  refine ⟨Fin.cast S.card_eq.symm a, ?_⟩
  simp only [RawMinorPair.BiReshuffle.HodgeRowSplit.toBiReshuffle,
    RawMinorPair.BiReshuffle.ofFinsets_colEquiv_inl]
  have ha :
      S.colSlots.orderEmbOfFin S.card_eq.symm (Fin.cast S.card_eq.symm a) =
        Fin.castAdd T.toRawPair.q i := by
    exact congrArg Subtype.val ((S.colSlots.orderIsoOfFin rfl).apply_symm_apply x)
  change
    finSumFinEquiv.symm
        (S.colSlots.orderEmbOfFin S.card_eq.symm (Fin.cast S.card_eq.symm a)) =
      Sum.inl i
  rw [ha, finSumFinEquiv_symm_apply_castAdd]

lemma left_row_image_subset_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair) :
    Finset.univ.image T.toRawPair.left.row ⊆
      Finset.univ.image S.toBiReshuffle.toPair.left.row := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  rcases S.exists_rowEquiv_inl_eq_inl i with ⟨a, ha⟩
  refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
  change T.toRawPair.slotRow (S.toBiReshuffle.rowEquiv (Sum.inl a)) =
    T.toRawPair.left.row i
  rw [ha]
  rfl

lemma left_col_image_subset_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair) :
    Finset.univ.image T.toRawPair.left.col ⊆
      Finset.univ.image S.toBiReshuffle.toPair.left.col := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  rcases S.exists_colEquiv_inl_eq_inl i with ⟨a, ha⟩
  refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
  change T.toRawPair.slotCol (S.toBiReshuffle.colEquiv (Sum.inl a)) =
    T.toRawPair.left.col i
  rw [ha]
  rfl

lemma left_row_image_subset_toBiReshuffle_of_hodgeColSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp) :
    Finset.univ.image T.toRawPair.left.row ⊆
      Finset.univ.image S.toBiReshuffle.toPair.left.row := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  rcases containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S i with
    ⟨a, ha⟩
  refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
  change T.toRawPair.slotRow (S.toBiReshuffle.rowEquiv (Sum.inl a)) =
    T.toRawPair.left.row i
  rw [ha]
  rfl

lemma left_col_image_subset_toBiReshuffle_of_hodgeRowSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp) :
    Finset.univ.image T.toRawPair.left.col ⊆
      Finset.univ.image S.toBiReshuffle.toPair.left.col := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _hi, rfl⟩
  rcases containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S i with
    ⟨a, ha⟩
  refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
  change T.toRawPair.slotCol (S.toBiReshuffle.colEquiv (Sum.inl a)) =
    T.toRawPair.left.col i
  rw [ha]
  rfl

lemma size_le_of_containsOriginalLeftRows {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hrows : ContainsOriginalLeftRows T E) :
    T.F.t ≤ E.r := by
  classical
  let pre : Fin T.F.t → Fin E.r := fun i => Classical.choose (hrows i)
  have hpre :
      ∀ i : Fin T.F.t, E.rowEquiv (Sum.inl (pre i)) = Sum.inl i := by
    intro i
    exact Classical.choose_spec (hrows i)
  have hinj : Function.Injective pre := by
    intro i j hij
    have hsum :
        (Sum.inl i : Sum (Fin T.F.t) (Fin T.G.t)) = Sum.inl j := by
      calc
      Sum.inl i = E.rowEquiv (Sum.inl (pre i)) := (hpre i).symm
      _ = E.rowEquiv (Sum.inl (pre j)) := by rw [hij]
      _ = Sum.inl j := hpre j
    injection hsum
  simpa using Fintype.card_le_of_injective pre hinj

lemma size_lt_of_containsOriginalLeftRows_of_ne {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hrows : ContainsOriginalLeftRows T E)
    (hne : E.r ≠ T.F.t) :
    T.F.t < E.r := by
  exact lt_of_le_of_ne (size_le_of_containsOriginalLeftRows hrows) (Ne.symm hne)

lemma size_le_of_containsOriginalLeftCols {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hcols : ContainsOriginalLeftCols T E) :
    T.F.t ≤ E.r := by
  classical
  let pre : Fin T.F.t → Fin E.r := fun i => Classical.choose (hcols i)
  have hpre :
      ∀ i : Fin T.F.t, E.colEquiv (Sum.inl (pre i)) = Sum.inl i := by
    intro i
    exact Classical.choose_spec (hcols i)
  have hinj : Function.Injective pre := by
    intro i j hij
    have hsum :
        (Sum.inl i : Sum (Fin T.F.t) (Fin T.G.t)) = Sum.inl j := by
      calc
        Sum.inl i = E.colEquiv (Sum.inl (pre i)) := (hpre i).symm
        _ = E.colEquiv (Sum.inl (pre j)) := by rw [hij]
        _ = Sum.inl j := hpre j
    injection hsum
  simpa using Fintype.card_le_of_injective pre hinj

lemma size_lt_of_containsOriginalLeftCols_of_ne {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hcols : ContainsOriginalLeftCols T E)
    (hne : E.r ≠ T.F.t) :
    T.F.t < E.r := by
  exact lt_of_le_of_ne (size_le_of_containsOriginalLeftCols hcols) (Ne.symm hne)

lemma firstLEOld_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair)
    (hE : S.toBiReshuffle.AllInjective) :
    MinorIndex.PairLE
      (S.toBiReshuffle.sorted.toPair.left.toMinorIndexOfStrictMono
        (S.toBiReshuffle.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (S.toBiReshuffle.sorted_toPair_left_col_strictMono_of_injective hE.2.1))
      T.F.idx := by
  let E := S.toBiReshuffle
  have hsize : T.F.t ≤ E.r :=
    size_le_of_containsOriginalLeftRows
      (containsOriginalLeftRows_toBiReshuffle_of_containingSplit T S)
  refine ⟨hsize, ?_⟩
  intro i
  constructor
  · have h := RawMinorIndex.sorted_row_le_of_image_subset
      T.toRawPair.left E.toPair.left T.F.idx.row.injective hE.1
      (left_row_image_subset_toBiReshuffle_of_containingSplit T S) i
    change E.toPair.left.sorted.row
      ⟨i, lt_of_lt_of_le i.isLt hsize⟩ ≤ T.F.idx.row i
    have hsort :
        Tuple.sort (RawMinorIndex.ofMinorIndex T.F.idx).row = Equiv.refl _ :=
      Tuple.sort_eq_refl_iff_monotone.mpr T.F.idx.row.monotone
    simpa [E, SwanRawLaplaceProductTerm.toRawPair,
      RawMinorIndex.sorted, RawMinorIndex.permute, hsort] using h
  · have h := RawMinorIndex.sorted_col_le_of_image_subset
      T.toRawPair.left E.toPair.left T.F.idx.col.injective hE.2.1
      (left_col_image_subset_toBiReshuffle_of_containingSplit T S) i
    change E.toPair.left.sorted.col
      ⟨i, lt_of_lt_of_le i.isLt hsize⟩ ≤ T.F.idx.col i
    have hsort :
        Tuple.sort (RawMinorIndex.ofMinorIndex T.F.idx).col = Equiv.refl _ :=
      Tuple.sort_eq_refl_iff_monotone.mpr T.F.idx.col.monotone
    simpa [E, SwanRawLaplaceProductTerm.toRawPair,
      RawMinorIndex.sorted, RawMinorIndex.permute, hsort] using h

/-- In the column-side Hodge branch, row slots still contain the old left row
slots, so the sorted new first rows are componentwise no larger than the old
first rows. -/
lemma sorted_left_row_le_original_of_hodgeColSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (hE : S.toBiReshuffle.AllInjective)
    (i : Fin T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.row
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftRows
            (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ ≤
      T.F.idx.row i := by
  let E := S.toBiReshuffle
  have h := RawMinorIndex.sorted_row_le_of_image_subset
    T.toRawPair.left E.toPair.left T.F.idx.row.injective hE.1
    (left_row_image_subset_toBiReshuffle_of_hodgeColSplit T S) i
  change E.toPair.left.sorted.row
      ⟨i, lt_of_lt_of_le i.isLt
        (size_le_of_containsOriginalLeftRows
          (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ ≤
    T.F.idx.row i
  have hsort :
      Tuple.sort (RawMinorIndex.ofMinorIndex T.F.idx).row = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr T.F.idx.row.monotone
  simpa [E, SwanRawLaplaceProductTerm.toRawPair,
    RawMinorIndex.sorted, RawMinorIndex.permute, hsort] using h

/-- In the row-side Hodge branch, column slots still contain the old left
column slots, so the sorted new first columns are componentwise no larger than
the old first columns. -/
lemma sorted_left_col_le_original_of_hodgeRowSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (hE : S.toBiReshuffle.AllInjective)
    (i : Fin T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.col
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftCols
            (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ ≤
      T.F.idx.col i := by
  let E := S.toBiReshuffle
  have h := RawMinorIndex.sorted_col_le_of_image_subset
    T.toRawPair.left E.toPair.left T.F.idx.col.injective hE.2.1
    (left_col_image_subset_toBiReshuffle_of_hodgeRowSplit T S) i
  change E.toPair.left.sorted.col
      ⟨i, lt_of_lt_of_le i.isLt
        (size_le_of_containsOriginalLeftCols
          (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ ≤
    T.F.idx.col i
  have hsort :
      Tuple.sort (RawMinorIndex.ofMinorIndex T.F.idx).col = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr T.F.idx.col.monotone
  simpa [E, SwanRawLaplaceProductTerm.toRawPair,
    RawMinorIndex.sorted, RawMinorIndex.permute, hsort] using h

lemma hodgeColSplit_leftPrefix_subset_colSlots_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    RawMinorPair.BiReshuffle.Hodge.leftPrefix T.toRawPair i ⊆ S.colSlots := by
  classical
  intro x hx
  rw [RawMinorPair.BiReshuffle.HodgeColSplit.colSlots]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact RawMinorPair.BiReshuffle.Hodge.leftPrefix_subset_hodgeD
      T.toRawPair ν i hx
  · intro hxW
    have hxC := S.W_subset hxW
    rcases Finset.mem_union.mp hxC with hxright | hxsuf
    · have hdis :=
        RawMinorPair.BiReshuffle.Hodge.leftPrefix_disjoint_rightPrefix
          T.toRawPair ν i
      rw [Finset.disjoint_left] at hdis
      exact hdis hx hxright
    · rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
      rcases Finset.mem_map.mp hxsuf with ⟨b, hb, hbx⟩
      have hai : a ≤ i := (Finset.mem_filter.mp ha).2
      have hνb : ν.val ≤ b.val := (Finset.mem_filter.mp hb).2
      have hab : a.val = b.val := by
        have hfin :
            Fin.castAdd T.toRawPair.q a = Fin.castAdd T.toRawPair.q b := by
          exact hax.trans hbx.symm
        simpa [Fin.castAdd] using congrArg Fin.val hfin
      have hai' : a.val ≤ i.val := by
        exact_mod_cast hai
      have hνi : ν.val ≤ i.val := by omega
      exact (not_le_of_gt hiν) hνi

lemma hodgeColSplit_leftPrefix_subset_good_colSlots_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    RawMinorPair.BiReshuffle.Hodge.leftPrefix T.toRawPair i ⊆
      S.colSlots.filter (fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i) := by
  classical
  intro x hx
  rw [Finset.mem_filter]
  refine ⟨hodgeColSplit_leftPrefix_subset_colSlots_of_lt T S i hiν hx, ?_⟩
  rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
  have hai : a ≤ i := (Finset.mem_filter.mp ha).2
  have hslot :
      T.toRawPair.slotCol (finSumFinEquiv.symm x) = T.F.idx.col a := by
    rw [← hax]
    have hsum :
        finSumFinEquiv.symm ((Fin.castAddEmb T.toRawPair.q) a) = Sum.inl a := by
      change finSumFinEquiv.symm (Fin.castAdd T.toRawPair.q a) = Sum.inl a
      simp
    rw [hsum]
    rfl
  rw [hslot]
  exact T.F.idx.col.monotone hai

lemma hodgeColSplit_colSlots_good_card_gt_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    (i : ℕ) <
      (S.colSlots.filter fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i).card := by
  classical
  have hcard := Finset.card_le_card
    (hodgeColSplit_leftPrefix_subset_good_colSlots_of_lt T S i hiν)
  rw [RawMinorPair.BiReshuffle.Hodge.card_leftPrefix] at hcard
  omega

lemma hodgeColSplit_bad_colSlots_subset_leftAfter_of_colBad
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hνi : ν.val ≤ i.val) :
    S.colSlots.filter (fun y =>
        ¬ T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i) ⊆
      RawMinorPair.BiReshuffle.Hodge.leftAfter T.toRawPair i := by
  classical
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxcol, hxnot⟩
  rw [RawMinorPair.BiReshuffle.HodgeColSplit.colSlots] at hxcol
  rcases Finset.mem_sdiff.mp hxcol with ⟨hxD, _hxW⟩
  rcases Finset.mem_union.mp hxD with hxleft | hxright
  · rcases Finset.mem_map.mp hxleft with ⟨a, _ha, hax⟩
    have hslot :
        T.toRawPair.slotCol (finSumFinEquiv.symm x) = T.F.idx.col a := by
      rw [← hax]
      have hsum :
          finSumFinEquiv.symm ((Fin.castAddEmb T.toRawPair.q) a) = Sum.inl a := by
        change finSumFinEquiv.symm (Fin.castAdd T.toRawPair.q a) = Sum.inl a
        simp
      rw [hsum]
      rfl
    have hia : i < a := by
      by_contra hnotlt
      have hai : a ≤ i := le_of_not_gt hnotlt
      exact hxnot (by
        rw [hslot]
        exact T.F.idx.col.monotone hai)
    refine Finset.mem_map.mpr ⟨a, ?_, hax⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hia⟩
  · rcases Finset.mem_map.mp hxright with ⟨μ, hμ, hμx⟩
    have hμν : μ ≤ ν := (Finset.mem_filter.mp hμ).2
    have hbad' :
        T.G.idx.col ν < T.F.idx.col ⟨ν.val, hνp⟩ := by
      simpa [ColBadAt] using hbad
    have hνiFin : (⟨ν.val, hνp⟩ : Fin T.F.t) ≤ i := by
      simpa [Fin.le_def] using hνi
    have hslot :
        T.toRawPair.slotCol (finSumFinEquiv.symm x) = T.G.idx.col μ := by
      rw [← hμx]
      have hsum :
          finSumFinEquiv.symm ((Fin.natAddEmb T.toRawPair.p) μ) = Sum.inr μ := by
        simp [Fin.natAddEmb]
      rw [hsum]
      rfl
    have hle :
        T.toRawPair.slotCol (finSumFinEquiv.symm x) ≤ T.F.idx.col i := by
      rw [hslot]
      exact le_trans (T.G.idx.col.monotone hμν)
        (le_trans (le_of_lt hbad') (T.F.idx.col.monotone hνiFin))
    exact False.elim (hxnot hle)

lemma hodgeColSplit_colSlots_good_card_gt_of_ge
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hνi : ν.val ≤ i.val) :
    (i : ℕ) <
      (S.colSlots.filter fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i).card := by
  classical
  let good : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) :=
    S.colSlots.filter fun y =>
      T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i
  let bad : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) :=
    S.colSlots.filter fun y =>
      ¬ T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i
  have hsplit : good.card + bad.card = S.colSlots.card := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := S.colSlots)
        (p := fun y =>
          T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i))
  have hbadcard :
      bad.card ≤
        (RawMinorPair.BiReshuffle.Hodge.leftAfter T.toRawPair i).card :=
    Finset.card_le_card
      (by
        simpa [bad] using
          hodgeColSplit_bad_colSlots_subset_leftAfter_of_colBad
            T hsize hbad S i hνi)
  rw [RawMinorPair.BiReshuffle.Hodge.card_leftAfter] at hbadcard
  change bad.card ≤ T.F.t - (i.val + 1) at hbadcard
  have hrowSize :
      T.F.t ≤ S.toBiReshuffle.r :=
    size_le_of_containsOriginalLeftRows
      (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S)
  have hcolSize : T.F.t ≤ S.colSlots.card := by
    have hrowSize' : T.F.t ≤ S.rowSlots.card := by
      simpa using hrowSize
    simpa [S.card_eq] using hrowSize'
  have hgood :
      (S.colSlots.filter fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i).card =
        good.card := rfl
  rw [hgood]
  omega

lemma hodgeColSplit_colSlots_good_card_gt_of_colBad
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) :
    (i : ℕ) <
      (S.colSlots.filter fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) ≤ T.F.idx.col i).card := by
  by_cases hiν : i.val < ν.val
  · exact hodgeColSplit_colSlots_good_card_gt_of_lt T S i hiν
  · have hνi : ν.val ≤ i.val := by omega
    exact hodgeColSplit_colSlots_good_card_gt_of_ge
      T hsize hbad S i hνi

lemma sorted_left_col_le_original_of_hodgeColSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.col
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftRows
            (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ ≤
      T.F.idx.col i := by
  let E := S.toBiReshuffle
  have hidx :
      (⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftRows
            (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ :
        Fin S.rowSlots.card) =
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftRows
            (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ := rfl
  have hcount :=
    hodgeColSplit_colSlots_good_card_gt_of_colBad
      T hsize hbad S i
  simpa [E, RawMinorPair.BiReshuffle.HodgeColSplit.toBiReshuffle, hidx] using
    RawMinorPair.BiReshuffle.ofFinsets_sorted_left_col_le_of_slot_count
      T.toRawPair S.rowSlots S.colSlots S.card_eq
      (⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftRows
            (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S))⟩ :
        Fin S.rowSlots.card)
      (T.F.idx.col i) hcount

lemma hodgeRowSplit_leftPrefix_subset_rowSlots_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    RawMinorPair.BiReshuffle.Hodge.leftPrefix T.toRawPair i ⊆ S.rowSlots := by
  classical
  intro x hx
  rw [RawMinorPair.BiReshuffle.HodgeRowSplit.rowSlots]
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · exact RawMinorPair.BiReshuffle.Hodge.leftPrefix_subset_hodgeD
      T.toRawPair ν i hx
  · intro hxW
    have hxC := S.W_subset hxW
    rcases Finset.mem_union.mp hxC with hxright | hxsuf
    · have hdis :=
        RawMinorPair.BiReshuffle.Hodge.leftPrefix_disjoint_rightPrefix
          T.toRawPair ν i
      rw [Finset.disjoint_left] at hdis
      exact hdis hx hxright
    · rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
      rcases Finset.mem_map.mp hxsuf with ⟨b, hb, hbx⟩
      have hai : a ≤ i := (Finset.mem_filter.mp ha).2
      have hνb : ν.val ≤ b.val := (Finset.mem_filter.mp hb).2
      have hab : a.val = b.val := by
        have hfin :
            Fin.castAdd T.toRawPair.q a = Fin.castAdd T.toRawPair.q b := by
          exact hax.trans hbx.symm
        simpa [Fin.castAdd] using congrArg Fin.val hfin
      have hai' : a.val ≤ i.val := by
        exact_mod_cast hai
      have hνi : ν.val ≤ i.val := by omega
      exact (not_le_of_gt hiν) hνi

lemma hodgeRowSplit_leftPrefix_subset_good_rowSlots_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    RawMinorPair.BiReshuffle.Hodge.leftPrefix T.toRawPair i ⊆
      S.rowSlots.filter (fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i) := by
  classical
  intro x hx
  rw [Finset.mem_filter]
  refine ⟨hodgeRowSplit_leftPrefix_subset_rowSlots_of_lt T S i hiν hx, ?_⟩
  rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
  have hai : a ≤ i := (Finset.mem_filter.mp ha).2
  have hslot :
      T.toRawPair.slotRow (finSumFinEquiv.symm x) = T.F.idx.row a := by
    rw [← hax]
    have hsum :
        finSumFinEquiv.symm ((Fin.castAddEmb T.toRawPair.q) a) = Sum.inl a := by
      change finSumFinEquiv.symm (Fin.castAdd T.toRawPair.q a) = Sum.inl a
      simp
    rw [hsum]
    rfl
  rw [hslot]
  exact T.F.idx.row.monotone hai

lemma hodgeRowSplit_rowSlots_good_card_gt_of_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hiν : i.val < ν.val) :
    (i : ℕ) <
      (S.rowSlots.filter fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i).card := by
  classical
  have hcard := Finset.card_le_card
    (hodgeRowSplit_leftPrefix_subset_good_rowSlots_of_lt T S i hiν)
  rw [RawMinorPair.BiReshuffle.Hodge.card_leftPrefix] at hcard
  omega

lemma hodgeRowSplit_bad_rowSlots_subset_leftAfter_of_rowBad
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hνi : ν.val ≤ i.val) :
    S.rowSlots.filter (fun y =>
        ¬ T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i) ⊆
      RawMinorPair.BiReshuffle.Hodge.leftAfter T.toRawPair i := by
  classical
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxrow, hxnot⟩
  rw [RawMinorPair.BiReshuffle.HodgeRowSplit.rowSlots] at hxrow
  rcases Finset.mem_sdiff.mp hxrow with ⟨hxD, _hxW⟩
  rcases Finset.mem_union.mp hxD with hxleft | hxright
  · rcases Finset.mem_map.mp hxleft with ⟨a, _ha, hax⟩
    have hslot :
        T.toRawPair.slotRow (finSumFinEquiv.symm x) = T.F.idx.row a := by
      rw [← hax]
      have hsum :
          finSumFinEquiv.symm ((Fin.castAddEmb T.toRawPair.q) a) = Sum.inl a := by
        change finSumFinEquiv.symm (Fin.castAdd T.toRawPair.q a) = Sum.inl a
        simp
      rw [hsum]
      rfl
    have hia : i < a := by
      by_contra hnotlt
      have hai : a ≤ i := le_of_not_gt hnotlt
      exact hxnot (by
        rw [hslot]
        exact T.F.idx.row.monotone hai)
    refine Finset.mem_map.mpr ⟨a, ?_, hax⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hia⟩
  · rcases Finset.mem_map.mp hxright with ⟨μ, hμ, hμx⟩
    have hμν : μ ≤ ν := (Finset.mem_filter.mp hμ).2
    have hbad' :
        T.G.idx.row ν < T.F.idx.row ⟨ν.val, hνp⟩ := by
      simpa [RowBadAt] using hbad
    have hνiFin : (⟨ν.val, hνp⟩ : Fin T.F.t) ≤ i := by
      simpa [Fin.le_def] using hνi
    have hslot :
        T.toRawPair.slotRow (finSumFinEquiv.symm x) = T.G.idx.row μ := by
      rw [← hμx]
      have hsum :
          finSumFinEquiv.symm ((Fin.natAddEmb T.toRawPair.p) μ) = Sum.inr μ := by
        simp [Fin.natAddEmb]
      rw [hsum]
      rfl
    have hle :
        T.toRawPair.slotRow (finSumFinEquiv.symm x) ≤ T.F.idx.row i := by
      rw [hslot]
      exact le_trans (T.G.idx.row.monotone hμν)
        (le_trans (le_of_lt hbad') (T.F.idx.row.monotone hνiFin))
    exact False.elim (hxnot hle)

lemma hodgeRowSplit_rowSlots_good_card_gt_of_ge
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) (hνi : ν.val ≤ i.val) :
    (i : ℕ) <
      (S.rowSlots.filter fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i).card := by
  classical
  let good : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) :=
    S.rowSlots.filter fun y =>
      T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i
  let bad : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) :=
    S.rowSlots.filter fun y =>
      ¬ T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i
  have hsplit : good.card + bad.card = S.rowSlots.card := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := S.rowSlots)
        (p := fun y =>
          T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i))
  have hbadcard :
      bad.card ≤
        (RawMinorPair.BiReshuffle.Hodge.leftAfter T.toRawPair i).card :=
    Finset.card_le_card
      (by
        simpa [bad] using
          hodgeRowSplit_bad_rowSlots_subset_leftAfter_of_rowBad
            T hsize hbad S i hνi)
  rw [RawMinorPair.BiReshuffle.Hodge.card_leftAfter] at hbadcard
  change bad.card ≤ T.F.t - (i.val + 1) at hbadcard
  have hrowSize :
      T.F.t ≤ S.toBiReshuffle.r :=
    size_le_of_containsOriginalLeftCols
      (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S)
  have hgood :
      (S.rowSlots.filter fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i).card =
        good.card := rfl
  rw [hgood]
  have hrowSize' : T.F.t ≤ S.rowSlots.card := by
    simpa using hrowSize
  omega

lemma hodgeRowSplit_rowSlots_good_card_gt_of_rowBad
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) :
    (i : ℕ) <
      (S.rowSlots.filter fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) ≤ T.F.idx.row i).card := by
  by_cases hiν : i.val < ν.val
  · exact hodgeRowSplit_rowSlots_good_card_gt_of_lt T S i hiν
  · have hνi : ν.val ≤ i.val := by omega
    exact hodgeRowSplit_rowSlots_good_card_gt_of_ge
      T hsize hbad S i hνi

lemma sorted_left_row_le_original_of_hodgeRowSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (i : Fin T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.row
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftCols
            (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ ≤
      T.F.idx.row i := by
  let E := S.toBiReshuffle
  have hidx :
      (⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftCols
            (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ :
        Fin S.rowSlots.card) =
        ⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftCols
            (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ := rfl
  have hcount :=
    hodgeRowSplit_rowSlots_good_card_gt_of_rowBad
      T hsize hbad S i
  simpa [E, RawMinorPair.BiReshuffle.HodgeRowSplit.toBiReshuffle, hidx] using
    RawMinorPair.BiReshuffle.ofFinsets_sorted_left_row_le_of_slot_count
      T.toRawPair S.rowSlots S.colSlots S.card_eq
      (⟨i.val, lt_of_lt_of_le i.isLt
          (size_le_of_containsOriginalLeftCols
            (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S))⟩ :
        Fin S.rowSlots.card)
      (T.F.idx.row i) hcount

lemma hodgeColSplit_colSlots_bad_position_lt_card_gt_of_ne_pivot_of_rowSlots_card_eq
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (hne :
      S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp)
    (hcard : S.rowSlots.card = T.F.t) :
    (ν : ℕ) <
      (S.colSlots.filter fun y =>
        T.toRawPair.slotCol (finSumFinEquiv.symm y) <
          T.F.idx.col ⟨ν.val, hνp⟩).card := by
  classical
  obtain ⟨x, hx⟩ :=
RawMinorPair.BiReshuffle.HodgeColSplit.rightPrefix_sdiff_W_nonempty_of_ne_pivot_of_rowSlots_card_eq
      S hne hcard
  rcases Finset.mem_sdiff.mp hx with ⟨hxright, hxW⟩
  let base := RawMinorPair.BiReshuffle.Hodge.leftBefore T.toRawPair ν
  have hsubset :
      insert x base ⊆
        S.colSlots.filter fun y =>
          T.toRawPair.slotCol (finSumFinEquiv.symm y) <
            T.F.idx.col ⟨ν.val, hνp⟩ := by
    intro y hy
    rw [Finset.mem_filter]
    rcases Finset.mem_insert.mp hy with hyx | hybase
    · subst y
      constructor
      · rw [RawMinorPair.BiReshuffle.HodgeColSplit.colSlots]
        exact Finset.mem_sdiff.mpr
          ⟨RawMinorPair.BiReshuffle.Hodge.rightPrefix_subset_hodgeD
              T.toRawPair ν hxright, hxW⟩
      · rcases Finset.mem_map.mp hxright with ⟨μ, hμ, hμx⟩
        have hμν : μ ≤ ν := (Finset.mem_filter.mp hμ).2
        have hslot :
            T.toRawPair.slotCol (finSumFinEquiv.symm x) =
              T.G.idx.col μ := by
          rw [← hμx]
          have hsum :
              finSumFinEquiv.symm
                  ((Fin.natAddEmb T.toRawPair.p) μ) =
                Sum.inr μ := by
            simp [Fin.natAddEmb]
          rw [hsum]
          rfl
        have hbad' :
            T.G.idx.col ν < T.F.idx.col ⟨ν.val, hνp⟩ := by
          simpa [ColBadAt] using hbad
        rw [hslot]
        exact lt_of_le_of_lt (T.G.idx.col.monotone hμν) hbad'
    · constructor
      · simpa [base, RawMinorPair.BiReshuffle.HodgeColSplit.colSlots] using
          RawMinorPair.BiReshuffle.Hodge.leftBefore_subset_hodgeD_sdiff_W
            T.toRawPair ν hνp S.W_subset hybase
      · simpa [base, SwanRawLaplaceProductTerm.toRawPair] using
          RawMinorPair.BiReshuffle.Hodge.slotCol_lt_of_mem_leftBefore
            T.toRawPair T.toRawPair_left_col_strictMono hνp hybase
  have hxnot : x ∉ base := by
    intro hxbase
    have hdis :=
      RawMinorPair.BiReshuffle.Hodge.leftBefore_disjoint_rightPrefix
        T.toRawPair ν
    rw [Finset.disjoint_left] at hdis
    exact hdis hxbase hxright
  have hcard_insert : (insert x base).card = ν.val + 1 := by
    rw [Finset.card_insert_of_notMem hxnot]
    rw [show base = RawMinorPair.BiReshuffle.Hodge.leftBefore T.toRawPair ν from rfl]
    rw [RawMinorPair.BiReshuffle.Hodge.card_leftBefore T.toRawPair ν hνp]
  have hcard_le := Finset.card_le_card hsubset
  rw [hcard_insert] at hcard_le
  omega

lemma sorted_left_col_lt_original_of_hodgeColSplit_ne_pivot_of_rowSlots_card_eq
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : ColBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp)
    (hne :
      S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp)
    (hcard : S.rowSlots.card = T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.col
        (⟨ν.val, by rw [hcard]; exact hνp⟩ : Fin S.rowSlots.card) <
      T.F.idx.col ⟨ν.val, hνp⟩ := by
  let E := S.toBiReshuffle
  have hcount :=
    hodgeColSplit_colSlots_bad_position_lt_card_gt_of_ne_pivot_of_rowSlots_card_eq
      T hsize hbad S hne hcard
  simpa [E, RawMinorPair.BiReshuffle.HodgeColSplit.toBiReshuffle] using
    RawMinorPair.BiReshuffle.ofFinsets_sorted_left_col_lt_of_slot_count
      T.toRawPair S.rowSlots S.colSlots S.card_eq
      (⟨ν.val, by rw [hcard]; exact hνp⟩ : Fin S.rowSlots.card)
      (T.F.idx.col ⟨ν.val, hνp⟩) hcount

lemma hodgeRowSplit_rowSlots_bad_position_lt_card_gt_of_ne_pivot_of_rowSlots_card_eq
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (hne :
      S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp)
    (hcard : S.rowSlots.card = T.F.t) :
    (ν : ℕ) <
      (S.rowSlots.filter fun y =>
        T.toRawPair.slotRow (finSumFinEquiv.symm y) <
          T.F.idx.row ⟨ν.val, hνp⟩).card := by
  classical
  obtain ⟨x, hx⟩ :=
RawMinorPair.BiReshuffle.HodgeRowSplit.rightPrefix_sdiff_W_nonempty_of_ne_pivot_of_rowSlots_card_eq
      S hne hcard
  rcases Finset.mem_sdiff.mp hx with ⟨hxright, hxW⟩
  let base := RawMinorPair.BiReshuffle.Hodge.leftBefore T.toRawPair ν
  have hsubset :
      insert x base ⊆
        S.rowSlots.filter fun y =>
          T.toRawPair.slotRow (finSumFinEquiv.symm y) <
            T.F.idx.row ⟨ν.val, hνp⟩ := by
    intro y hy
    rw [Finset.mem_filter]
    rcases Finset.mem_insert.mp hy with hyx | hybase
    · subst y
      constructor
      · rw [RawMinorPair.BiReshuffle.HodgeRowSplit.rowSlots]
        exact Finset.mem_sdiff.mpr
          ⟨RawMinorPair.BiReshuffle.Hodge.rightPrefix_subset_hodgeD
              T.toRawPair ν hxright, hxW⟩
      · rcases Finset.mem_map.mp hxright with ⟨μ, hμ, hμx⟩
        have hμν : μ ≤ ν := (Finset.mem_filter.mp hμ).2
        have hslot :
            T.toRawPair.slotRow (finSumFinEquiv.symm x) =
              T.G.idx.row μ := by
          rw [← hμx]
          have hsum :
              finSumFinEquiv.symm
                  ((Fin.natAddEmb T.toRawPair.p) μ) =
                Sum.inr μ := by
            simp [Fin.natAddEmb]
          rw [hsum]
          rfl
        have hbad' :
            T.G.idx.row ν < T.F.idx.row ⟨ν.val, hνp⟩ := by
          simpa [RowBadAt] using hbad
        rw [hslot]
        exact lt_of_le_of_lt (T.G.idx.row.monotone hμν) hbad'
    · constructor
      · simpa [base, RawMinorPair.BiReshuffle.HodgeRowSplit.rowSlots] using
          RawMinorPair.BiReshuffle.Hodge.leftBefore_subset_hodgeD_sdiff_W
            T.toRawPair ν hνp S.W_subset hybase
      · simpa [base, SwanRawLaplaceProductTerm.toRawPair] using
          RawMinorPair.BiReshuffle.Hodge.slotRow_lt_of_mem_leftBefore
            T.toRawPair T.toRawPair_left_row_strictMono hνp hybase
  have hxnot : x ∉ base := by
    intro hxbase
    have hdis :=
      RawMinorPair.BiReshuffle.Hodge.leftBefore_disjoint_rightPrefix
        T.toRawPair ν
    rw [Finset.disjoint_left] at hdis
    exact hdis hxbase hxright
  have hcard_insert : (insert x base).card = ν.val + 1 := by
    rw [Finset.card_insert_of_notMem hxnot]
    rw [show base = RawMinorPair.BiReshuffle.Hodge.leftBefore T.toRawPair ν from rfl]
    rw [RawMinorPair.BiReshuffle.Hodge.card_leftBefore T.toRawPair ν hνp]
  have hcard_le := Finset.card_le_card hsubset
  rw [hcard_insert] at hcard_le
  omega

lemma sorted_left_row_lt_original_of_hodgeRowSplit_ne_pivot_of_rowSlots_card_eq
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hbad : RowBadAt T hsize ν)
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp)
    (hne :
      S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp)
    (hcard : S.rowSlots.card = T.F.t) :
    S.toBiReshuffle.toPair.left.sorted.row
        (⟨ν.val, by rw [hcard]; exact hνp⟩ : Fin S.rowSlots.card) <
      T.F.idx.row ⟨ν.val, hνp⟩ := by
  let E := S.toBiReshuffle
  have hcount :=
    hodgeRowSplit_rowSlots_bad_position_lt_card_gt_of_ne_pivot_of_rowSlots_card_eq
      T hsize hbad S hne hcard
  simpa [E, RawMinorPair.BiReshuffle.HodgeRowSplit.toBiReshuffle] using
    RawMinorPair.BiReshuffle.ofFinsets_sorted_left_row_lt_of_slot_count
      T.toRawPair S.rowSlots S.colSlots S.card_eq
      (⟨ν.val, by rw [hcard]; exact hνp⟩ : Fin S.rowSlots.card)
      (T.F.idx.row ⟨ν.val, hνp⟩) hcount

/-- Raw support predicate for the non-pivot terms in Swan Corollary 2.8,
size-defect branch.

The determinant identity itself supplies coefficients on this support.  The
predicate separates the paper's combinatorics from later algebra:
`ContainsOriginalLeftRows` and `ContainsOriginalLeftCols` encode
`U ⊇ A`, `W ⊇ B`; `hne` removes the distinguished original term; and
`firstLEOld` is the sorted-subset comparison that makes the new first factor
weakly smaller than the old first factor. -/
def IsSizeBranchLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (E : RawMinorPair.BiReshuffle T.toRawPair) : Prop :=
  ∃ hE : E.AllInjective,
  ∃ _hrows : ContainsOriginalLeftRows T E,
  ∃ _hcols : ContainsOriginalLeftCols T E,
  ∃ _hne : E.r ≠ T.F.t,
    MinorIndex.PairLE
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx

lemma isSizeBranchLaplaceSupport_toBiReshuffle_of_containingSplit
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair)
    (hE : S.toBiReshuffle.AllInjective)
    (hne : S.toBiReshuffle.r ≠ T.F.t) :
    IsSizeBranchLaplaceSupport T S.toBiReshuffle := by
  exact ⟨hE,
    containsOriginalLeftRows_toBiReshuffle_of_containingSplit T S,
    containsOriginalLeftCols_toBiReshuffle_of_containingSplit T S,
    hne,
    firstLEOld_toBiReshuffle_of_containingSplit T S hE⟩

lemma not_sizeBranchLaplaceSupport_id {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    ¬ IsSizeBranchLaplaceSupport T (RawMinorPair.BiReshuffle.id T.toRawPair) := by
  intro h
  rcases h with ⟨_hE, _hrows, _hcols, hne, _hfirstLEOld⟩
  exact hne rfl

noncomputable instance instFintypeSizeBranchLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Fintype { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSizeBranchLaplaceSupport T E } := by
  classical
  exact Fintype.ofFinite _

lemma sizeBranchSurvivor_of_laplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsSizeBranchLaplaceSupport T E) :
    IsSizeBranchSurvivor T E := by
  rcases h with ⟨hE, hrows, _hcols, hne, hfirstLEOld⟩
  exact ⟨hE, hfirstLEOld, size_lt_of_containsOriginalLeftRows_of_ne hrows hne⟩

lemma size_lt_of_sizeBranchLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsSizeBranchLaplaceSupport T E) :
    T.F.t < E.r := by
  rcases h with ⟨_hE, hrows, _hcols, hne, _hfirstLEOld⟩
  exact size_lt_of_containsOriginalLeftRows_of_ne hrows hne

noncomputable instance instFintypeSortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Fintype { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E } := by
  classical
  exact Fintype.ofFinite _

noncomputable instance instFintypeSizeBranchSurvivor {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J} :
    Fintype { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSizeBranchSurvivor T E } := by
  classical
  exact Fintype.ofFinite _

lemma isSortedPromotable_of_sizeBranchSurvivor {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsSizeBranchSurvivor T E) :
    IsSortedPromotable T E := by
  rcases h with ⟨hE, hfirstLEOld, hsize⟩
  refine ⟨hE, MinorIndex.PairLE.trans hfirstLEOld T.firstLE, ?_⟩
  exact MinorIndex.PairLT.of_pairLE_not_symm hfirstLEOld
    (MinorIndex.not_pairLE_of_size_lt hsize)

lemma isSortedPromotable_of_sizeBranchLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsSizeBranchLaplaceSupport T E) :
    IsSortedPromotable T E :=
  isSortedPromotable_of_sizeBranchSurvivor
    (sizeBranchSurvivor_of_laplaceSupport h)

lemma exists_coeff_sortedPromotable_sum_of_sizeBranchSurvivor
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSizeBranchSurvivor T E } → k) :
    ∃ coeff' : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSizeBranchSurvivor T E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair) =
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            IsSortedPromotable T E },
          MvPolynomial.C (coeff' E) *
            RawMinorPair.laplacePolynomial k E.1.toPair := by
  classical
  let toSortedPromotable :
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSizeBranchSurvivor T E } →
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } :=
    fun E => ⟨E.1, isSortedPromotable_of_sizeBranchSurvivor E.2⟩
  exact exists_fintype_coeff_pushforward_polynomial_sum
    toSortedPromotable coeff
    (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } =>
      RawMinorPair.laplacePolynomial k E.1.toPair)

lemma exists_coeff_sortedPromotable_sum_of_sizeBranchLaplaceSupport
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSizeBranchLaplaceSupport T E } → k) :
    ∃ coeff' : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSizeBranchLaplaceSupport T E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair) =
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            IsSortedPromotable T E },
          MvPolynomial.C (coeff' E) *
            RawMinorPair.laplacePolynomial k E.1.toPair := by
  classical
  let toSortedPromotable :
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSizeBranchLaplaceSupport T E } →
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } :=
    fun E => ⟨E.1, isSortedPromotable_of_sizeBranchLaplaceSupport E.2⟩
  exact exists_fintype_coeff_pushforward_polynomial_sum
    toSortedPromotable coeff
    (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } =>
      RawMinorPair.laplacePolynomial k E.1.toPair)

lemma exists_coeff_sortedPromotable_sum_of_componentColLaplaceSupport
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        IsComponentColLaplaceSupport T ν hνp E → IsSortedPromotable T E)
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsComponentColLaplaceSupport T ν hνp E } → k) :
    ∃ coeff' : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsComponentColLaplaceSupport T ν hνp E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair) =
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            IsSortedPromotable T E },
          MvPolynomial.C (coeff' E) *
            RawMinorPair.laplacePolynomial k E.1.toPair := by
  classical
  let toSortedPromotable :
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsComponentColLaplaceSupport T ν hνp E } →
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } :=
    fun E => ⟨E.1, hprom E.2⟩
  exact exists_fintype_coeff_pushforward_polynomial_sum
    toSortedPromotable coeff
    (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } =>
      RawMinorPair.laplacePolynomial k E.1.toPair)

lemma exists_coeff_sortedPromotable_sum_of_componentRowLaplaceSupport
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        IsComponentRowLaplaceSupport T ν hνp E → IsSortedPromotable T E)
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsComponentRowLaplaceSupport T ν hνp E } → k) :
    ∃ coeff' : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsComponentRowLaplaceSupport T ν hνp E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair) =
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            IsSortedPromotable T E },
          MvPolynomial.C (coeff' E) *
            RawMinorPair.laplacePolynomial k E.1.toPair := by
  classical
  let toSortedPromotable :
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsComponentRowLaplaceSupport T ν hνp E } →
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } :=
    fun E => ⟨E.1, hprom E.2⟩
  exact exists_fintype_coeff_pushforward_polynomial_sum
    toSortedPromotable coeff
    (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } =>
      RawMinorPair.laplacePolynomial k E.1.toPair)

noncomputable def toSupportOfSortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (E : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E }) :
    BiReshuffleSupport T := by
  classical
  let hE : E.1.AllInjective := Classical.choose E.2
  let hrest := Classical.choose_spec E.2
  let firstLE := Classical.choose hrest
  let firstLT := Classical.choose_spec hrest
  exact ofSortedInjective E.1 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 firstLE firstLT

lemma laplacePolynomial_toSupportOfSortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [CommRing k]
    {T : SwanRawLaplaceProductTerm I J}
    (E : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E }) :
    RawMinorPair.laplacePolynomial k E.1.toPair =
      RawMinorPair.sortSign k E.1.toPair *
        RawMinorPair.laplacePolynomial k
          (toSupportOfSortedPromotable E).E.toPair := by
  classical
  rw [RawMinorPair.laplacePolynomial_eq_sortSign_mul_sorted]
  rw [← E.1.toPair_sorted]
  simp [toSupportOfSortedPromotable, ofSortedInjective]

lemma exists_coeff_support_sum_of_sortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E } → k) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSortedPromotable T E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k
            (toSupportOfSortedPromotable E).E.toPair) =
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair := by
  classical
  exact exists_fintype_coeff_pushforward_polynomial_sum
    (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E } => toSupportOfSortedPromotable E)
    coeff
    (fun S : BiReshuffleSupport T =>
      RawMinorPair.laplacePolynomial k S.E.toPair)

lemma exists_coeff_support_sum_raw_sortedPromotable {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (k : Type*) [Field k]
    {T : SwanRawLaplaceProductTerm I J}
    (coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
      IsSortedPromotable T E } → k) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSortedPromotable T E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair) =
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair := by
  classical
  let coeff' :
      { E : RawMinorPair.BiReshuffle T.toRawPair //
        IsSortedPromotable T E } → k :=
    fun E => coeff E * RawMinorPair.sortSignCoeff k E.1.toPair
  rcases exists_coeff_support_sum_of_sortedPromotable
      k (T := T) coeff' with ⟨coeffRest, hsum⟩
  refine ⟨coeffRest, ?_⟩
  calc
    (∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSortedPromotable T E },
        MvPolynomial.C (coeff E) *
          RawMinorPair.laplacePolynomial k E.1.toPair)
        =
      ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          IsSortedPromotable T E },
        MvPolynomial.C (coeff' E) *
          RawMinorPair.laplacePolynomial k
            (toSupportOfSortedPromotable E).E.toPair := by
        apply Finset.sum_congr rfl
        intro E _hE
        rw [laplacePolynomial_toSupportOfSortedPromotable k E,
          RawMinorPair.sortSign_eq_C]
        simp [coeff', MvPolynomial.C_mul]
        ring
    _ =
      ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair := hsum

lemma firstLEOld_of_componentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hνbad : ColBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hE : E.AllInjective)
    (h : IsComponentColLaplaceSupport T ν hνp E) :
    MinorIndex.PairLE
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx := by
  classical
  rcases h with ⟨S, _hne, rfl, _hSurvives⟩
  let E := S.toBiReshuffle
  have hsizeRows : T.F.t ≤ E.r :=
    size_le_of_containsOriginalLeftRows
      (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S)
  refine MinorIndex.PairLE.of_components hsizeRows ?_
  intro i
  constructor
  · change E.toPair.left.sorted.row
        ⟨i.val, lt_of_lt_of_le i.isLt hsizeRows⟩ ≤ T.F.idx.row i
    exact sorted_left_row_le_original_of_hodgeColSplit T S hE i
  · change E.toPair.left.sorted.col
        ⟨i.val, lt_of_lt_of_le i.isLt hsizeRows⟩ ≤ T.F.idx.col i
    exact sorted_left_col_le_original_of_hodgeColSplit T hsize hνbad S i

lemma firstLT_of_componentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (_hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.col μ)
    (hνbad : ColBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hE : E.AllInjective)
    (h : IsComponentColLaplaceSupport T ν hνp E) :
    MinorIndex.PairLT
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx := by
  classical
  -- Promote the weak comparison with the old first factor: non-pivot Hodge
  -- column terms force a strict drop at the first bad column.
  have hfirstLEOld :
      MinorIndex.PairLE
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
          (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx :=
    firstLEOld_of_componentColLaplaceSupport T hsize hνbad hE h
  refine MinorIndex.PairLT.of_pairLE_not_symm hfirstLEOld ?_
  rcases h with ⟨S, hne, rfl, _hSurvives⟩
  let E := S.toBiReshuffle
  have hsizeRows : T.F.t ≤ E.r :=
    size_le_of_containsOriginalLeftRows
      (containsOriginalLeftRows_toBiReshuffle_of_hodgeColSplit T S)
  by_cases hEq : E.r = T.F.t
  · have hcard : S.rowSlots.card = T.F.t := by
      simpa [E] using hEq
    have hlt :=
      sorted_left_col_lt_original_of_hodgeColSplit_ne_pivot_of_rowSlots_card_eq
        T hsize hνbad S hne hcard
    have hpq :
        S.toBiReshuffle.sorted.toPair.p ≤ T.F.t := by
      change E.r ≤ T.F.t
      exact le_of_eq hEq
    refine MinorIndex.not_pairLE_of_violation
      (I := T.F.idx)
      (J := S.toBiReshuffle.sorted.toPair.left.toMinorIndexOfStrictMono
        (S.toBiReshuffle.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (S.toBiReshuffle.sorted_toPair_left_col_strictMono_of_injective hE.2.1))
      hpq
      (⟨ν.val, by rw [hEq]; exact hνp⟩ : Fin E.r) ?_
    intro hcomp
    exact not_lt_of_ge (by simpa [E, hcard] using hcomp.2) hlt
  · have hgt : T.F.t < E.r :=
      lt_of_le_of_ne hsizeRows (Ne.symm hEq)
    exact MinorIndex.not_pairLE_of_size_lt
      (I := T.F.idx)
      (J := S.toBiReshuffle.sorted.toPair.left.toMinorIndexOfStrictMono
        (S.toBiReshuffle.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (S.toBiReshuffle.sorted_toPair_left_col_strictMono_of_injective hE.2.1))
      hgt

lemma isSortedPromotable_of_componentColLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.col μ)
    (hνbad : ColBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsComponentColLaplaceSupport T ν hνp E) :
    IsSortedPromotable T E := by
  classical
  let hE : E.AllInjective := allInjective_of_componentColLaplaceSupport h
  refine ⟨hE, ?_, ?_⟩
  · exact MinorIndex.PairLE.trans
      (firstLEOld_of_componentColLaplaceSupport T hsize hνbad hE h)
      T.firstLE
  · exact firstLT_of_componentColLaplaceSupport
      T hsize ν hνp hνmin hνbad hE h

lemma firstLEOld_of_componentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    {ν : Fin T.G.t} {hνp : ν.val < T.F.t}
    (hνbad : RowBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hE : E.AllInjective)
    (h : IsComponentRowLaplaceSupport T ν hνp E) :
    MinorIndex.PairLE
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx := by
  classical
  rcases h with ⟨S, _hne, rfl, _hSurvives⟩
  let E := S.toBiReshuffle
  have hsizeRows : T.F.t ≤ E.r :=
    size_le_of_containsOriginalLeftCols
      (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S)
  refine MinorIndex.PairLE.of_components hsizeRows ?_
  intro i
  constructor
  · change E.toPair.left.sorted.row
        ⟨i.val, lt_of_lt_of_le i.isLt hsizeRows⟩ ≤ T.F.idx.row i
    exact sorted_left_row_le_original_of_hodgeRowSplit T hsize hνbad S i
  · change E.toPair.left.sorted.col
        ⟨i.val, lt_of_lt_of_le i.isLt hsizeRows⟩ ≤ T.F.idx.col i
    exact sorted_left_col_le_original_of_hodgeRowSplit T S hE i

lemma firstLT_of_componentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (_hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.row μ)
    (hνbad : RowBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (hE : E.AllInjective)
    (h : IsComponentRowLaplaceSupport T ν hνp E) :
    MinorIndex.PairLT
      (E.sorted.toPair.left.toMinorIndexOfStrictMono
        (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx := by
  classical
  have hfirstLEOld :
      MinorIndex.PairLE
        (E.sorted.toPair.left.toMinorIndexOfStrictMono
          (E.sorted_toPair_left_row_strictMono_of_injective hE.1)
          (E.sorted_toPair_left_col_strictMono_of_injective hE.2.1)) T.F.idx :=
    firstLEOld_of_componentRowLaplaceSupport T hsize hνbad hE h
  refine MinorIndex.PairLT.of_pairLE_not_symm hfirstLEOld ?_
  rcases h with ⟨S, hne, rfl, _hSurvives⟩
  let E := S.toBiReshuffle
  have hsizeRows : T.F.t ≤ E.r :=
    size_le_of_containsOriginalLeftCols
      (containsOriginalLeftCols_toBiReshuffle_of_hodgeRowSplit T S)
  by_cases hEq : E.r = T.F.t
  · have hcard : S.rowSlots.card = T.F.t := by
      simpa [E] using hEq
    have hlt :=
      sorted_left_row_lt_original_of_hodgeRowSplit_ne_pivot_of_rowSlots_card_eq
        T hsize hνbad S hne hcard
    have hpq :
        S.toBiReshuffle.sorted.toPair.p ≤ T.F.t := by
      change E.r ≤ T.F.t
      exact le_of_eq hEq
    refine MinorIndex.not_pairLE_of_violation
      (I := T.F.idx)
      (J := S.toBiReshuffle.sorted.toPair.left.toMinorIndexOfStrictMono
        (S.toBiReshuffle.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (S.toBiReshuffle.sorted_toPair_left_col_strictMono_of_injective hE.2.1))
      hpq
      (⟨ν.val, by rw [hEq]; exact hνp⟩ : Fin E.r) ?_
    intro hcomp
    exact not_lt_of_ge (by simpa [E, hcard] using hcomp.1) hlt
  · have hgt : T.F.t < E.r :=
      lt_of_le_of_ne hsizeRows (Ne.symm hEq)
    exact MinorIndex.not_pairLE_of_size_lt
      (I := T.F.idx)
      (J := S.toBiReshuffle.sorted.toPair.left.toMinorIndexOfStrictMono
        (S.toBiReshuffle.sorted_toPair_left_row_strictMono_of_injective hE.1)
        (S.toBiReshuffle.sorted_toPair_left_col_strictMono_of_injective hE.2.1))
      hgt

lemma isSortedPromotable_of_componentRowLaplaceSupport {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.row μ)
    (hνbad : RowBadAt T hsize ν)
    {E : RawMinorPair.BiReshuffle T.toRawPair}
    (h : IsComponentRowLaplaceSupport T ν hνp E) :
    IsSortedPromotable T E := by
  classical
  let hE : E.AllInjective := allInjective_of_componentRowLaplaceSupport h
  refine ⟨hE, ?_, ?_⟩
  · exact MinorIndex.PairLE.trans
      (firstLEOld_of_componentRowLaplaceSupport T hsize hνbad hE h)
      T.firstLE
  · exact firstLT_of_componentRowLaplaceSupport
      T hsize ν hνp hνmin hνbad hE h

end BiReshuffleSupport

lemma exists_coeff_componentColLaplaceSupport_of_hodgeColSplit_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (h :
      ∃ coeff :
          { S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp } → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S :
              { S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp //
                S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp },
            MvPolynomial.C (coeff S) *
              RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0) :
    ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
        BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E } → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E },
          MvPolynomial.C (coeff E) *
            RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
  classical
  rcases h with ⟨coeff, hsum⟩
  let Source :=
    { S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp //
      S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp }
  let SupportedSource :=
    { S : Source //
      BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp
        S.1.toBiReshuffle }
  let term : Source → MvPolynomial (Fin m × Fin n) k :=
    fun S => RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair
  have hzero :
      ∀ S : Source,
        S ∉ Set.range (fun U : SupportedSource => U.1) →
          MvPolynomial.C (coeff S) * term S = 0 := by
    intro S hS
    by_cases hE : S.1.toBiReshuffle.AllInjective
    · have hsupp :
          BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp
            S.1.toBiReshuffle := by
        exact ⟨S.1, S.2, rfl, hE⟩
      exact False.elim (hS ⟨⟨S, hsupp⟩, rfl⟩)
    · simp [term,
        RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_not_allInjective
          k S.1.toBiReshuffle hE]
  have hrestrict :
      (∑ S : Source, MvPolynomial.C (coeff S) * term S) =
        ∑ S : SupportedSource, MvPolynomial.C (coeff S.1) * term S.1 := by
    exact fintype_sum_eq_sum_of_injective_support
      (fun U : SupportedSource => U.1) Subtype.val_injective
      (fun S : Source => MvPolynomial.C (coeff S) * term S) hzero
  let toSupport :
      SupportedSource →
        { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E } :=
    fun S => ⟨S.1.1.toBiReshuffle, S.2⟩
  rcases exists_fintype_coeff_pushforward_polynomial_sum
      toSupport (fun S : SupportedSource => coeff S.1)
      (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E } =>
        RawMinorPair.laplacePolynomial k E.1.toPair) with
    ⟨coeff', hpush⟩
  refine ⟨coeff', ?_⟩
  rw [← hpush, ← hrestrict]
  simpa [Source, term] using hsum

lemma exists_coeff_componentRowLaplaceSupport_of_hodgeRowSplit_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (h :
      ∃ coeff :
          { S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp } → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S :
              { S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp //
                S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp },
            MvPolynomial.C (coeff S) *
              RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0) :
    ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
        BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E } → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E },
          MvPolynomial.C (coeff E) *
            RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
  classical
  rcases h with ⟨coeff, hsum⟩
  let Source :=
    { S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp //
      S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp }
  let SupportedSource :=
    { S : Source //
      BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp
        S.1.toBiReshuffle }
  let term : Source → MvPolynomial (Fin m × Fin n) k :=
    fun S => RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair
  have hzero :
      ∀ S : Source,
        S ∉ Set.range (fun U : SupportedSource => U.1) →
          MvPolynomial.C (coeff S) * term S = 0 := by
    intro S hS
    by_cases hE : S.1.toBiReshuffle.AllInjective
    · have hsupp :
          BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp
            S.1.toBiReshuffle := by
        exact ⟨S.1, S.2, rfl, hE⟩
      exact False.elim (hS ⟨⟨S, hsupp⟩, rfl⟩)
    · simp [term,
        RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_not_allInjective
          k S.1.toBiReshuffle hE]
  have hrestrict :
      (∑ S : Source, MvPolynomial.C (coeff S) * term S) =
        ∑ S : SupportedSource, MvPolynomial.C (coeff S.1) * term S.1 := by
    exact fintype_sum_eq_sum_of_injective_support
      (fun U : SupportedSource => U.1) Subtype.val_injective
      (fun S : Source => MvPolynomial.C (coeff S) * term S) hzero
  let toSupport :
      SupportedSource →
        { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E } :=
    fun S => ⟨S.1.1.toBiReshuffle, S.2⟩
  rcases exists_fintype_coeff_pushforward_polynomial_sum
      toSupport (fun S : SupportedSource => coeff S.1)
      (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E } =>
        RawMinorPair.laplacePolynomial k E.1.toPair) with
    ⟨coeff', hpush⟩
  refine ⟨coeff', ?_⟩
  rw [← hpush, ← hrestrict]
  simpa [Source, term] using hsum

lemma exists_coeff_ne_pivot_of_total_sum_eq_zero
    {α σ k : Type*} [Fintype α] [DecidableEq α]
    [Field k]
    (pivot : α)
    (coeff : α → k)
    (term : α → MvPolynomial σ k)
    (pivotTerm : MvPolynomial σ k)
    (hpivot_coeff : coeff pivot = (-1 : k))
    (hpivot_term : term pivot = pivotTerm)
    (hsum : (∑ a : α, MvPolynomial.C (coeff a) * term a) = 0) :
    ∃ coeffRest : { a : α // a ≠ pivot } → k,
      - pivotTerm +
        ∑ a : { a : α // a ≠ pivot },
          MvPolynomial.C (coeffRest a) * term a.1 = 0 := by
  classical
  have h :
      ∃ coeffSupport : { a : α // a ≠ pivot } → k,
        - term pivot +
          ∑ a : { a : α // a ≠ pivot },
            MvPolynomial.C (coeffSupport a) * term a.1 = 0 := by
    refine signed_subtype_sum_eq_zero_of_total_sum_eq_zero
      (α := α) (σ := σ) k
      (support := fun a => a ≠ pivot)
      pivot (by simp) coeff term ?_ ?_ hsum
    · exact hpivot_coeff
    · intro a hne hnot
      exact False.elim (hnot hne)
  rcases h with ⟨coeffRest, hrest⟩
  refine ⟨coeffRest, ?_⟩
  simpa [hpivot_term] using hrest

lemma exists_coeff_hodgeColSplit_identity_of_total_laplace_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p)
    (coeff : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp) =
        (-1 : k))
    (hpivot_laplace :
      RawMinorPair.laplacePolynomial k
          (RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp).toBiReshuffle.toPair =
        RawMinorPair.laplacePolynomial k P)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffRest :
        { S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp //
          S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp } → k,
      - RawMinorPair.laplacePolynomial k P +
        ∑ S :
          { S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp },
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0 := by
  classical
  let pivot := RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp
  let term : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp →
      MvPolynomial (Fin m × Fin n) k :=
    fun S => RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair
  have h :
      ∃ coeffSupport :
          { S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp //
            S ≠ pivot } → k,
        - term pivot +
          ∑ S :
            { S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp //
              S ≠ pivot },
            MvPolynomial.C (coeffSupport S) * term S.1 = 0 := by
    refine signed_subtype_sum_eq_zero_of_total_sum_eq_zero
      (α := RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp)
      (σ := Fin m × Fin n) k
      (support := fun S => S ≠ pivot)
      pivot (by simp [pivot]) coeff term ?_ ?_ ?_
    · simpa [pivot] using hpivot_coeff
    · intro S hne hnot
      exact False.elim (hnot hne)
    · simpa [term] using hsum
  rcases h with ⟨coeffRest, hrest⟩
  refine ⟨coeffRest, ?_⟩
  simpa [pivot, term, hpivot_laplace] using hrest

lemma exists_coeff_hodgeRowSplit_identity_of_total_laplace_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (P : RawMinorPair m n) (ν : Fin P.q) (hνp : ν.val < P.p)
    (coeff : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp) =
        (-1 : k))
    (hpivot_laplace :
      RawMinorPair.laplacePolynomial k
          (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp).toBiReshuffle.toPair =
        RawMinorPair.laplacePolynomial k P)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffRest :
        { S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp //
          S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp } → k,
      - RawMinorPair.laplacePolynomial k P +
        ∑ S :
          { S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp },
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0 := by
  classical
  let pivot := RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp
  let term : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp →
      MvPolynomial (Fin m × Fin n) k :=
    fun S => RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair
  have h :
      ∃ coeffSupport :
          { S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp //
            S ≠ pivot } → k,
        - term pivot +
          ∑ S :
            { S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp //
              S ≠ pivot },
            MvPolynomial.C (coeffSupport S) * term S.1 = 0 := by
    refine signed_subtype_sum_eq_zero_of_total_sum_eq_zero
      (α := RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp)
      (σ := Fin m × Fin n) k
      (support := fun S => S ≠ pivot)
      pivot (by simp [pivot]) coeff term ?_ ?_ ?_
    · simpa [pivot] using hpivot_coeff
    · intro S hne hnot
      exact False.elim (hnot hne)
    · simpa [term] using hsum
  rcases h with ⟨coeffRest, hrest⟩
  refine ⟨coeffRest, ?_⟩
  simpa [pivot, term, hpivot_laplace] using hrest

lemma exists_coeff_support_sum_of_componentColLaplaceSupport_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E →
          BiReshuffleSupport.IsSortedPromotable T E)
    (h :
      ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E } → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E },
            MvPolynomial.C (coeff E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  rcases h with ⟨coeff, hsum⟩
  rcases BiReshuffleSupport.exists_coeff_sortedPromotable_sum_of_componentColLaplaceSupport
      k (T := T) (ν := ν) (hνp := hνp) hprom coeff with
    ⟨coeffSorted, hsorted⟩
  rcases BiReshuffleSupport.exists_coeff_support_sum_raw_sortedPromotable
      k (T := T) coeffSorted with
    ⟨coeffRest, hsupport⟩
  refine ⟨coeffRest, ?_⟩
  rw [← hsupport, ← hsorted]
  exact hsum

lemma exists_coeff_support_sum_of_componentRowLaplaceSupport_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E →
          BiReshuffleSupport.IsSortedPromotable T E)
    (h :
      ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E } → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E },
            MvPolynomial.C (coeff E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  rcases h with ⟨coeff, hsum⟩
  rcases BiReshuffleSupport.exists_coeff_sortedPromotable_sum_of_componentRowLaplaceSupport
      k (T := T) (ν := ν) (hνp := hνp) hprom coeff with
    ⟨coeffSorted, hsorted⟩
  rcases BiReshuffleSupport.exists_coeff_support_sum_raw_sortedPromotable
      k (T := T) coeffSorted with
    ⟨coeffRest, hsupport⟩
  refine ⟨coeffRest, ?_⟩
  rw [← hsupport, ← hsorted]
  exact hsum

lemma swan_component_col_signed_identity_of_total_hodge_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (coeff : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp) =
        (-1 : k))
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E →
          BiReshuffleSupport.IsSortedPromotable T E)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  have hsplit :
      ∃ coeff :
          { S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S :
              { S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp //
                S ≠ RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp },
            MvPolynomial.C (coeff S) *
              RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0 :=
    exists_coeff_hodgeColSplit_identity_of_total_laplace_sum
      k T.toRawPair ν hνp
      coeff hpivot_coeff
      (RawMinorPair.BiReshuffle.HodgeColSplit.pivot_toBiReshuffle_toPair_laplacePolynomial
        k T.toRawPair ν hνp)
      hsum
  have hcomponent :
      ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsComponentColLaplaceSupport T ν hνp E },
            MvPolynomial.C (coeff E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0 :=
    exists_coeff_componentColLaplaceSupport_of_hodgeColSplit_identity
      k T ν hνp hsplit
  exact exists_coeff_support_sum_of_componentColLaplaceSupport_identity
    k T ν hνp hprom hcomponent

lemma swan_component_row_signed_identity_of_total_hodge_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (coeff : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp) =
        (-1 : k))
    (hprom :
      ∀ {E : RawMinorPair.BiReshuffle T.toRawPair},
        BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E →
          BiReshuffleSupport.IsSortedPromotable T E)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffRest : BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  have hsplit :
      ∃ coeff :
          { S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp //
            S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S :
              { S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp //
                S ≠ RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp },
            MvPolynomial.C (coeff S) *
              RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0 :=
    exists_coeff_hodgeRowSplit_identity_of_total_laplace_sum
      k T.toRawPair ν hνp
      coeff hpivot_coeff
      (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot_toBiReshuffle_toPair_laplacePolynomial
        k T.toRawPair ν hνp)
      hsum
  have hcomponent :
      ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsComponentRowLaplaceSupport T ν hνp E },
            MvPolynomial.C (coeff E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0 :=
    exists_coeff_componentRowLaplaceSupport_of_hodgeRowSplit_identity
      k T ν hνp hsplit
  exact exists_coeff_support_sum_of_componentRowLaplaceSupport_identity
    k T ν hνp hprom hcomponent

lemma exists_coeff_sizeBranchLaplaceSupport_of_containingSplit_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (h :
      ∃ coeff :
          { S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair //
            S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair } → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S :
              { S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair //
                S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair },
            MvPolynomial.C (coeff S) *
              RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0) :
    ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
        BiReshuffleSupport.IsSizeBranchLaplaceSupport T E } → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            BiReshuffleSupport.IsSizeBranchLaplaceSupport T E },
          MvPolynomial.C (coeff E) *
            RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
  classical
  rcases h with ⟨coeff, hsum⟩
  let Source :=
    { S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair //
      S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair }
  let SupportedSource :=
    { S : Source //
      BiReshuffleSupport.IsSizeBranchLaplaceSupport T S.1.toBiReshuffle }
  let term : Source → MvPolynomial (Fin m × Fin n) k :=
    fun S => RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair
  have hzero :
      ∀ S : Source,
        S ∉ Set.range (fun U : SupportedSource => U.1) →
          MvPolynomial.C (coeff S) * term S = 0 := by
    intro S hS
    by_cases hE : S.1.toBiReshuffle.AllInjective
    · have hne : S.1.toBiReshuffle.r ≠ T.F.t := by
        intro hr
        have hcard : S.1.rowSlots.card = T.toRawPair.p := by
          simpa using hr
        exact S.2
          (RawMinorPair.BiReshuffle.ContainingSplit.eq_pivot_of_rowSlots_card_eq
            S.1 hcard)
      have hsupp :
          BiReshuffleSupport.IsSizeBranchLaplaceSupport T S.1.toBiReshuffle :=
        BiReshuffleSupport.isSizeBranchLaplaceSupport_toBiReshuffle_of_containingSplit
          T S.1 hE hne
      exact False.elim (hS ⟨⟨S, hsupp⟩, rfl⟩)
    · simp [term,
        RawMinorPair.BiReshuffle.toPair_laplacePolynomial_eq_zero_of_not_allInjective
          k S.1.toBiReshuffle hE]
  have hrestrict :
      (∑ S : Source, MvPolynomial.C (coeff S) * term S) =
        ∑ S : SupportedSource, MvPolynomial.C (coeff S.1) * term S.1 := by
    exact fintype_sum_eq_sum_of_injective_support
      (fun U : SupportedSource => U.1) Subtype.val_injective
      (fun S : Source => MvPolynomial.C (coeff S) * term S) hzero
  let toSupport :
      SupportedSource →
        { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsSizeBranchLaplaceSupport T E } :=
    fun S => ⟨S.1.1.toBiReshuffle, S.2⟩
  rcases exists_fintype_coeff_pushforward_polynomial_sum
      toSupport (fun S : SupportedSource => coeff S.1)
      (fun E : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsSizeBranchLaplaceSupport T E } =>
        RawMinorPair.laplacePolynomial k E.1.toPair) with
    ⟨coeff', hpush⟩
  refine ⟨coeff', ?_⟩
  rw [← hpush, ← hrestrict]
  simpa [Source, term] using hsum

lemma exists_coeff_ne_pivot_containingSplit_of_total_sum_eq_zero
    {m n : ℕ}
    (k : Type*) [Field k]
    (P : RawMinorPair m n)
    (coeff : RawMinorPair.BiReshuffle.ContainingSplit P → k)
    (term : RawMinorPair.BiReshuffle.ContainingSplit P →
      MvPolynomial (Fin m × Fin n) k)
    (pivotTerm : MvPolynomial (Fin m × Fin n) k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.ContainingSplit.pivot P) = (-1 : k))
    (hpivot_term :
      term (RawMinorPair.BiReshuffle.ContainingSplit.pivot P) = pivotTerm)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit P,
        MvPolynomial.C (coeff S) * term S) = 0) :
    ∃ coeffRest :
        { S : RawMinorPair.BiReshuffle.ContainingSplit P //
          S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot P } → k,
      - pivotTerm +
        ∑ S :
          { S : RawMinorPair.BiReshuffle.ContainingSplit P //
            S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot P },
          MvPolynomial.C (coeffRest S) * term S.1 = 0 := by
  classical
  let pivot := RawMinorPair.BiReshuffle.ContainingSplit.pivot P
  have h :
      ∃ coeffSupport : { S : RawMinorPair.BiReshuffle.ContainingSplit P //
          S ≠ pivot } → k,
        - term pivot +
          ∑ S : { S : RawMinorPair.BiReshuffle.ContainingSplit P //
              S ≠ pivot },
            MvPolynomial.C (coeffSupport S) * term S.1 = 0 := by
    refine signed_subtype_sum_eq_zero_of_total_sum_eq_zero
      (α := RawMinorPair.BiReshuffle.ContainingSplit P)
      (σ := Fin m × Fin n) k
      (support := fun S => S ≠ pivot)
      pivot (by simp [pivot]) coeff term ?_ ?_ hsum
    · simpa [pivot] using hpivot_coeff
    · intro S hne hnot
      exact False.elim (hnot hne)
  rcases h with ⟨coeffRest, hrest⟩
  refine ⟨coeffRest, ?_⟩
  simpa [pivot, hpivot_term] using hrest

lemma exists_coeff_containingSplit_identity_of_total_laplace_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (P : RawMinorPair m n)
    (coeff : RawMinorPair.BiReshuffle.ContainingSplit P → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.ContainingSplit.pivot P) = (-1 : k))
    (hpivot_laplace :
      RawMinorPair.laplacePolynomial k
          (RawMinorPair.BiReshuffle.ContainingSplit.pivot P).toBiReshuffle.toPair =
        RawMinorPair.laplacePolynomial k P)
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit P,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffRest :
        { S : RawMinorPair.BiReshuffle.ContainingSplit P //
          S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot P } → k,
      - RawMinorPair.laplacePolynomial k P +
        ∑ S :
          { S : RawMinorPair.BiReshuffle.ContainingSplit P //
            S ≠ RawMinorPair.BiReshuffle.ContainingSplit.pivot P },
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.1.toBiReshuffle.toPair = 0 := by
  classical
  exact exists_coeff_ne_pivot_containingSplit_of_total_sum_eq_zero
    k P coeff
    (fun S => RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair)
    (RawMinorPair.laplacePolynomial k P)
    hpivot_coeff hpivot_laplace hsum

lemma exists_coeff_sizeBranchLaplaceSupport_of_total_containingSplit_laplace_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (coeff : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair → k)
    (hpivot_coeff :
      coeff (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair) = (-1 : k))
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0) :
    ∃ coeffSupport : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsSizeBranchLaplaceSupport T E } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsSizeBranchLaplaceSupport T E },
            MvPolynomial.C (coeffSupport E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
  classical
  apply exists_coeff_sizeBranchLaplaceSupport_of_containingSplit_identity k T
  exact exists_coeff_containingSplit_identity_of_total_laplace_sum
    k T.toRawPair coeff hpivot_coeff
    (RawMinorPair.BiReshuffle.ContainingSplit.pivot_toBiReshuffle_toPair_laplacePolynomial
      k T.toRawPair)
    hsum

lemma exists_coeff_total_containingSplit_laplace_sum_of_iccSplit
    {m n : ℕ}
    (k : Type*) [Field k]
    (P : RawMinorPair m n)
    (coeffIcc : RawMinorPair.BiReshuffle.ContainingSplit.IccSplit P → k)
    (hpivot_coeff :
      coeffIcc
          (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit
            (RawMinorPair.BiReshuffle.ContainingSplit.pivot P)) = (-1 : k))
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit.IccSplit P,
        MvPolynomial.C (coeffIcc S) *
          RawMinorPair.laplacePolynomial k
            (RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit S).toBiReshuffle.toPair) = 0) :
    ∃ coeff : RawMinorPair.BiReshuffle.ContainingSplit P → k,
      coeff (RawMinorPair.BiReshuffle.ContainingSplit.pivot P) = (-1 : k) ∧
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit P,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0 := by
  classical
  let coeff : RawMinorPair.BiReshuffle.ContainingSplit P → k :=
    fun S => coeffIcc (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit S)
  refine ⟨coeff, ?_, ?_⟩
  · simpa [coeff] using hpivot_coeff
  · rw [RawMinorPair.BiReshuffle.ContainingSplit.sum_containingSplit_eq_sum_iccSplit]
    simpa [coeff] using hsum

lemma swan_corollary2_8_size_containingSplit_total_laplace_sum_of_iccSplit
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (coeffIcc :
      RawMinorPair.BiReshuffle.ContainingSplit.IccSplit T.toRawPair → k)
    (hpivot_coeff :
      coeffIcc
          (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit
            (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair)) =
        (-1 : k))
    (hsum :
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit.IccSplit T.toRawPair,
        MvPolynomial.C (coeffIcc S) *
          RawMinorPair.laplacePolynomial k
            (RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit S).toBiReshuffle.toPair) =
        0) :
    ∃ coeff : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair → k,
      coeff (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair) = (-1 : k) ∧
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair,
        MvPolynomial.C (coeff S) *
          RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0 := by
  exact exists_coeff_total_containingSplit_laplace_sum_of_iccSplit
    k T.toRawPair coeffIcc hpivot_coeff hsum

noncomputable def swan_component_col_hodgeSplitFactor
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp) : k :=
  S.splitSignFactor (R := k) * ((-1 : k) ^ S.W.card)

lemma swan_component_col_hodgeSplitFactor_mul_self
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : RawMinorPair.BiReshuffle.HodgeColSplit P ν hνp) :
    swan_component_col_hodgeSplitFactor k S *
        swan_component_col_hodgeSplitFactor k S = 1 := by
  unfold swan_component_col_hodgeSplitFactor
  have hsplit := S.splitSignFactor_mul_self (R := k)
  have hpow := neg_one_pow_mul_self (R := k) S.W.card
  calc
    (S.splitSignFactor (R := k) * (-1 : k) ^ S.W.card) *
        (S.splitSignFactor (R := k) * (-1 : k) ^ S.W.card)
        =
      (S.splitSignFactor (R := k) * S.splitSignFactor (R := k)) *
        (((-1 : k) ^ S.W.card) * ((-1 : k) ^ S.W.card)) := by
          ring
    _ = 1 := by
          rw [hsplit, hpow]
          ring

noncomputable def swan_component_row_hodgeSplitFactor
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp) : k :=
  S.splitSignFactor (R := k) * ((-1 : k) ^ S.W.card)

lemma swan_component_row_hodgeSplitFactor_mul_self
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    {ν : Fin P.q} {hνp : ν.val < P.p}
    (S : RawMinorPair.BiReshuffle.HodgeRowSplit P ν hνp) :
    swan_component_row_hodgeSplitFactor k S *
        swan_component_row_hodgeSplitFactor k S = 1 := by
  unfold swan_component_row_hodgeSplitFactor
  have hsplit := S.splitSignFactor_mul_self (R := k)
  have hpow := neg_one_pow_mul_self (R := k) S.W.card
  calc
    (S.splitSignFactor (R := k) * (-1 : k) ^ S.W.card) *
        (S.splitSignFactor (R := k) * (-1 : k) ^ S.W.card)
        =
      (S.splitSignFactor (R := k) * S.splitSignFactor (R := k)) *
        (((-1 : k) ^ S.W.card) * ((-1 : k) ^ S.W.card)) := by
          ring
    _ = 1 := by
          rw [hsplit, hpow]
          ring

noncomputable def swan_component_col_hodgeCoeff
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp → k :=
  fun S =>
    - swan_component_col_hodgeSplitFactor k
        (RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp) *
      swan_component_col_hodgeSplitFactor k S

lemma swan_component_col_hodgeCoeff_pivot
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    swan_component_col_hodgeCoeff k T ν hνp
        (RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp) =
      (-1 : k) := by
  classical
  let pivot := RawMinorPair.BiReshuffle.HodgeColSplit.pivot T.toRawPair ν hνp
  have hsquare :
      swan_component_col_hodgeSplitFactor k pivot *
          swan_component_col_hodgeSplitFactor k pivot = 1 :=
    swan_component_col_hodgeSplitFactor_mul_self k pivot
  unfold swan_component_col_hodgeCoeff
  change
    - swan_component_col_hodgeSplitFactor k pivot *
        swan_component_col_hodgeSplitFactor k pivot = (-1 : k)
  calc
    - swan_component_col_hodgeSplitFactor k pivot *
        swan_component_col_hodgeSplitFactor k pivot
        =
      - (swan_component_col_hodgeSplitFactor k pivot *
          swan_component_col_hodgeSplitFactor k pivot) := by
          ring
    _ = (-1 : k) := by
          rw [hsquare]

noncomputable def swan_component_row_hodgeCoeff
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp → k :=
  fun S =>
    - swan_component_row_hodgeSplitFactor k
        (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp) *
      swan_component_row_hodgeSplitFactor k S

lemma swan_component_row_hodgeCoeff_pivot
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    swan_component_row_hodgeCoeff k T ν hνp
        (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp) =
      (-1 : k) := by
  classical
  let pivot := RawMinorPair.BiReshuffle.HodgeRowSplit.pivot T.toRawPair ν hνp
  have hsquare :
      swan_component_row_hodgeSplitFactor k pivot *
          swan_component_row_hodgeSplitFactor k pivot = 1 :=
    swan_component_row_hodgeSplitFactor_mul_self k pivot
  unfold swan_component_row_hodgeCoeff
  change
    - swan_component_row_hodgeSplitFactor k pivot *
        swan_component_row_hodgeSplitFactor k pivot = (-1 : k)
  calc
    - swan_component_row_hodgeSplitFactor k pivot *
        swan_component_row_hodgeSplitFactor k pivot
        =
      - (swan_component_row_hodgeSplitFactor k pivot *
          swan_component_row_hodgeSplitFactor k pivot) := by
          ring
    _ = (-1 : k) := by
          rw [hsquare]

noncomputable def swan_corollary2_8_size_splitFactor
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    (S : RawMinorPair.BiReshuffle.ContainingSplit P) : k :=
  S.splitSignFactor (R := k) * ((-1 : k) ^ S.colSlotsᶜ.card)

lemma swan_corollary2_8_size_splitFactor_mul_self
    {m n : ℕ}
    (k : Type*) [Field k]
    {P : RawMinorPair m n}
    (S : RawMinorPair.BiReshuffle.ContainingSplit P) :
    swan_corollary2_8_size_splitFactor k S *
        swan_corollary2_8_size_splitFactor k S = 1 := by
  unfold swan_corollary2_8_size_splitFactor
  have hsplit := S.splitSignFactor_mul_self (R := k)
  have hpow := neg_one_pow_mul_self (R := k) S.colSlotsᶜ.card
  calc
    (S.splitSignFactor (R := k) * (-1 : k) ^ S.colSlotsᶜ.card) *
        (S.splitSignFactor (R := k) * (-1 : k) ^ S.colSlotsᶜ.card)
        =
      (S.splitSignFactor (R := k) * S.splitSignFactor (R := k)) *
        (((-1 : k) ^ S.colSlotsᶜ.card) *
          ((-1 : k) ^ S.colSlotsᶜ.card)) := by
          ring
    _ = 1 := by
          rw [hsplit, hpow]
          ring

noncomputable def swan_corollary2_8_size_containingCoeff
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair → k :=
  fun S =>
    - swan_corollary2_8_size_splitFactor k
        (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair) *
      swan_corollary2_8_size_splitFactor k S

noncomputable def swan_corollary2_8_size_iccCoeff
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    RawMinorPair.BiReshuffle.ContainingSplit.IccSplit T.toRawPair → k :=
  fun S => swan_corollary2_8_size_containingCoeff k T
    (RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit S)

lemma swan_corollary2_8_size_iccCoeff_pivot
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) :
    swan_corollary2_8_size_iccCoeff k T
        (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit
          (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair)) =
      (-1 : k) := by
  classical
  let pivot := RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair
  have hpivot :
      RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit
          (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit pivot) =
        pivot :=
    RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit_toIccSplit pivot
  have hsquare :
      swan_corollary2_8_size_splitFactor k pivot *
          swan_corollary2_8_size_splitFactor k pivot = 1 :=
    swan_corollary2_8_size_splitFactor_mul_self k pivot
  unfold swan_corollary2_8_size_iccCoeff
    swan_corollary2_8_size_containingCoeff
  rw [hpivot]
  change
    - swan_corollary2_8_size_splitFactor k pivot *
        swan_corollary2_8_size_splitFactor k pivot = (-1 : k)
  calc
    - swan_corollary2_8_size_splitFactor k pivot *
        swan_corollary2_8_size_splitFactor k pivot
        =
      - (swan_corollary2_8_size_splitFactor k pivot *
          swan_corollary2_8_size_splitFactor k pivot) := by
          ring
    _ = (-1 : k) := by
          rw [hsquare]


/-- Size defect is one concrete way for a raw product to fail to be good. -/
lemma not_isGood_of_size_lt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    ¬ T.IsGood := by
  exact MinorIndex.not_pairLE_of_size_lt hsize

lemma toRawPair_q_pos_of_size_lt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    0 < T.toRawPair.q := by
  simpa [SwanRawLaplaceProductTerm.toRawPair] using
    lt_of_le_of_lt (Nat.zero_le T.F.t) hsize

lemma toRawPair_two_left_size_lt_total_of_size_lt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    2 * T.toRawPair.p < T.toRawPair.p + T.toRawPair.q := by
  simpa [SwanRawLaplaceProductTerm.toRawPair, two_mul] using
    Nat.add_lt_add_left hsize T.F.t

lemma leftSlotFinset_toRawPair_ne_univ_of_size_lt {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    RawMinorPair.BiReshuffle.leftSlotFinset T.toRawPair ≠ Finset.univ := by
  exact RawMinorPair.BiReshuffle.leftSlotFinset_ne_univ_of_right_pos
    T.toRawPair (toRawPair_q_pos_of_size_lt T hsize)

lemma leftSlotFinset_toRawPair_union_permPreimage_ne_univ_of_size_lt
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    RawMinorPair.BiReshuffle.leftSlotFinset T.toRawPair ∪
        RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset T.toRawPair π ≠
      Finset.univ := by
  exact
    RawMinorPair.BiReshuffle.leftSlotFinset_union_permPreimageLeftSlotFinset_ne_univ_of_two_mul_lt
      T.toRawPair (toRawPair_two_left_size_lt_total_of_size_lt T hsize) π

lemma sum_Icc_leftSlotFinset_toRawPair_union_permPreimage_neg_one_pow_card_compl_eq_zero
    {m n p q : ℕ}
    (k : Type*) [CommRing k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    (∑ s ∈ Finset.Icc
        (RawMinorPair.BiReshuffle.leftSlotFinset T.toRawPair ∪
          RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset T.toRawPair π)
        Finset.univ,
      (-1 : k) ^ sᶜ.card) = 0 := by
  exact
  RawMinorPair.BiReshuffle.sum_Icc_leftSlotFinset_union_permPreimage_neg_one_pow_card_compl_eq_zero
      k T.toRawPair
      (toRawPair_two_left_size_lt_total_of_size_lt T hsize) π

lemma MvPolynomial_C_equivPermSign
    {V : Type*} (k : Type*) [CommRing k]
    {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) :
    MvPolynomial.C (R := k) (σ := V)
        (RawMinorPair.BiReshuffle.equivPermSign (R := k) π) =
      ((Equiv.Perm.sign π : ℤˣ) : MvPolynomial V k) := by
  simp [RawMinorPair.BiReshuffle.equivPermSign]

noncomputable def swan_corollary2_8_size_commonLeibnizTerm
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.C
        (- swan_corollary2_8_size_splitFactor k
          (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair) *
        RawMinorPair.laplaceCoeff k T.toRawPair *
        RawMinorPair.BiReshuffle.equivPermSign (R := k) π) *
    ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
      RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair (π j) j

lemma swan_corollary2_8_size_leibnizTerm_eq_common
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (X : RawMinorPair.BiReshuffle.ContainingSplit.LeibnizTerm T.toRawPair) :
    MvPolynomial.C (swan_corollary2_8_size_containingCoeff k T X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)) =
      swan_corollary2_8_size_commonLeibnizTerm k T X.ambientPerm *
        MvPolynomial.C ((-1 : k) ^ X.1.colSlotsᶜ.card) := by
  classical
  let S := X.1
  let τ := X.2.1
  let σ := X.2.2
  let P := T.toRawPair
  let pivot := RawMinorPair.BiReshuffle.ContainingSplit.pivot P
  let a : k := - swan_corollary2_8_size_splitFactor k pivot
  let b : k := S.splitSignFactor (R := k)
  let c : k := (-1 : k) ^ S.colSlotsᶜ.card
  let d : k := RawMinorPair.laplaceCoeff k P
  let eτ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) τ
  let eσ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) σ
  let eπ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) (S.leibnizPerm τ σ)
  let M : MvPolynomial (Fin m × Fin n) k :=
    ∏ j : Fin (P.p + P.q),
      RawMinorPair.BiReshuffle.slotMatrix k P
        (S.leibnizPerm τ σ j) j
  have hlap :
      RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair = d := by
    simpa [P, d] using
      RawMinorPair.BiReshuffle.laplaceCoeff_toPair k S.toBiReshuffle
  have hsign :
      b * (eτ * eσ) = eπ := by
    simpa [b, eτ, eσ, eπ] using
      S.splitSignFactor_mul_blockSigns (R := k) τ σ
  have hsignC :
      MvPolynomial.C (b * (eτ * eσ)) =
        MvPolynomial.C (R := k) (σ := Fin m × Fin n) eπ := by
    exact congrArg (MvPolynomial.C (R := k) (σ := Fin m × Fin n)) hsign
  change
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign τ :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign σ :
              MvPolynomial (Fin m × Fin n) k)) * M)) =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c
  rw [hlap]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k τ]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k σ]
  simp only [MvPolynomial.C_mul] at hsignC
  calc
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C d *
          ((MvPolynomial.C eτ * MvPolynomial.C eσ) * M))
        =
      (MvPolynomial.C (a * d) *
        (MvPolynomial.C b * (MvPolynomial.C eτ * MvPolynomial.C eσ))) *
          M * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]
          ring_nf
    _ =
      (MvPolynomial.C (a * d) * MvPolynomial.C eπ) *
          M * MvPolynomial.C c := by
          rw [hsignC]
    _ =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]

noncomputable def swan_component_col_commonLeibnizTerm
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.C
        (- swan_component_col_hodgeSplitFactor k
          (RawMinorPair.BiReshuffle.HodgeColSplit.pivot
            T.toRawPair ν hνp) *
        RawMinorPair.laplaceCoeff k T.toRawPair *
        RawMinorPair.BiReshuffle.equivPermSign (R := k) π) *
    ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
      RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair (π j) j

noncomputable def swan_component_row_commonLeibnizTerm
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.C
        (- swan_component_row_hodgeSplitFactor k
          (RawMinorPair.BiReshuffle.HodgeRowSplit.pivot
            T.toRawPair ν hνp) *
        RawMinorPair.laplaceCoeff k T.toRawPair *
        RawMinorPair.BiReshuffle.equivPermSign (R := k) π) *
    ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
      RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair (π j) j

lemma swan_component_col_hodge_leibnizTerm_eq_common
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (X :
      RawMinorPair.BiReshuffle.HodgeColSplit.LeibnizTerm
        T.toRawPair ν hνp) :
    MvPolynomial.C (swan_component_col_hodgeCoeff k T ν hνp X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)) =
      swan_component_col_commonLeibnizTerm k T ν hνp X.ambientPerm *
        MvPolynomial.C ((-1 : k) ^ X.1.W.card) := by
  classical
  let S := X.1
  let τ := X.2.1
  let σ := X.2.2
  let P := T.toRawPair
  let pivot := RawMinorPair.BiReshuffle.HodgeColSplit.pivot P ν hνp
  let a : k := - swan_component_col_hodgeSplitFactor k pivot
  let b : k := S.splitSignFactor (R := k)
  let c : k := (-1 : k) ^ S.W.card
  let d : k := RawMinorPair.laplaceCoeff k P
  let eτ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) τ
  let eσ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) σ
  let eπ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) (S.leibnizPerm τ σ)
  let M : MvPolynomial (Fin m × Fin n) k :=
    ∏ j : Fin (P.p + P.q),
      RawMinorPair.BiReshuffle.slotMatrix k P
        (S.leibnizPerm τ σ j) j
  have hlap :
      RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair = d := by
    simpa [P, d] using
      RawMinorPair.BiReshuffle.laplaceCoeff_toPair k S.toBiReshuffle
  have hsign :
      b * (eτ * eσ) = eπ := by
    simpa [b, eτ, eσ, eπ] using
      S.splitSignFactor_mul_blockSigns (R := k) τ σ
  have hsignC :
      MvPolynomial.C (b * (eτ * eσ)) =
        MvPolynomial.C (R := k) (σ := Fin m × Fin n) eπ := by
    exact congrArg (MvPolynomial.C (R := k) (σ := Fin m × Fin n)) hsign
  change
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign τ :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign σ :
              MvPolynomial (Fin m × Fin n) k)) * M)) =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c
  rw [hlap]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k τ]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k σ]
  simp only [MvPolynomial.C_mul] at hsignC
  calc
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C d *
          ((MvPolynomial.C eτ * MvPolynomial.C eσ) * M))
        =
      (MvPolynomial.C (a * d) *
        (MvPolynomial.C b * (MvPolynomial.C eτ * MvPolynomial.C eσ))) *
          M * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]
          ring_nf
    _ =
      (MvPolynomial.C (a * d) * MvPolynomial.C eπ) *
          M * MvPolynomial.C c := by
          rw [hsignC]
    _ =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]

lemma swan_component_row_hodge_leibnizTerm_eq_common
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (X :
      RawMinorPair.BiReshuffle.HodgeRowSplit.LeibnizTerm
        T.toRawPair ν hνp) :
    MvPolynomial.C (swan_component_row_hodgeCoeff k T ν hνp X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)) =
      swan_component_row_commonLeibnizTerm k T ν hνp X.ambientPerm *
        MvPolynomial.C ((-1 : k) ^ X.1.W.card) := by
  classical
  let S := X.1
  let τ := X.2.1
  let σ := X.2.2
  let P := T.toRawPair
  let pivot := RawMinorPair.BiReshuffle.HodgeRowSplit.pivot P ν hνp
  let a : k := - swan_component_row_hodgeSplitFactor k pivot
  let b : k := S.splitSignFactor (R := k)
  let c : k := (-1 : k) ^ S.W.card
  let d : k := RawMinorPair.laplaceCoeff k P
  let eτ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) τ
  let eσ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) σ
  let eπ : k := RawMinorPair.BiReshuffle.equivPermSign (R := k) (S.leibnizPerm τ σ)
  let M : MvPolynomial (Fin m × Fin n) k :=
    ∏ j : Fin (P.p + P.q),
      RawMinorPair.BiReshuffle.slotMatrix k P
        (S.leibnizPerm τ σ j) j
  have hlap :
      RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair = d := by
    simpa [P, d] using
      RawMinorPair.BiReshuffle.laplaceCoeff_toPair k S.toBiReshuffle
  have hsign :
      b * (eτ * eσ) = eπ := by
    simpa [b, eτ, eσ, eπ] using
      S.splitSignFactor_mul_blockSigns (R := k) τ σ
  have hsignC :
      MvPolynomial.C (b * (eτ * eσ)) =
        MvPolynomial.C (R := k) (σ := Fin m × Fin n) eπ := by
    exact congrArg (MvPolynomial.C (R := k) (σ := Fin m × Fin n)) hsign
  change
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k S.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign τ :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign σ :
              MvPolynomial (Fin m × Fin n) k)) * M)) =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c
  rw [hlap]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k τ]
  rw [← MvPolynomial_C_equivPermSign (V := Fin m × Fin n) k σ]
  simp only [MvPolynomial.C_mul] at hsignC
  calc
    MvPolynomial.C (a * (b * c)) *
        (MvPolynomial.C d *
          ((MvPolynomial.C eτ * MvPolynomial.C eσ) * M))
        =
      (MvPolynomial.C (a * d) *
        (MvPolynomial.C b * (MvPolynomial.C eτ * MvPolynomial.C eσ))) *
          M * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]
          ring_nf
    _ =
      (MvPolynomial.C (a * d) * MvPolynomial.C eπ) *
          M * MvPolynomial.C c := by
          rw [hsignC]
    _ =
      (MvPolynomial.C (a * d * eπ) * M) * MvPolynomial.C c := by
          simp only [MvPolynomial.C_mul]

lemma swan_component_col_inner_powerset_sum_eq_zero
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    (∑ W : { W : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) //
        RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset T.toRawPair π ⊆
          RawMinorPair.BiReshuffle.Hodge.hodgeD T.toRawPair ν ∧
        W ∈ (RawMinorPair.BiReshuffle.Hodge.hodgeC T.toRawPair ν hνp \
          RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset
            T.toRawPair π).powerset },
      swan_component_col_commonLeibnizTerm k T ν hνp π *
        MvPolynomial.C ((-1 : k) ^ W.1.card)) = 0 := by
  classical
  let P := T.toRawPair
  let base : Finset (Fin (P.p + P.q)) :=
    RawMinorPair.BiReshuffle.Hodge.hodgeC P ν hνp \
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π
  let common := swan_component_col_commonLeibnizTerm k T ν hνp π
  let Source : Type :=
    { W : Finset (Fin (P.p + P.q)) //
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π ⊆
        RawMinorPair.BiReshuffle.Hodge.hodgeD P ν ∧
      W ∈ base.powerset }
  let Target : Type := { W : Finset (Fin (P.p + P.q)) // W ∈ base.powerset }
  change
    (∑ W : Source, common *
      MvPolynomial.C (R := k) (σ := Fin m × Fin n)
        ((-1 : k) ^ W.1.card)) = 0
  by_cases hpreD :
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π ⊆
        RawMinorPair.BiReshuffle.Hodge.hodgeD P ν
  · have hbase_nonempty : base.Nonempty := by
      simpa [P, base] using
        RawMinorPair.BiReshuffle.Hodge.hodgeC_sdiff_permPreimageLeftSlotFinset_nonempty
          P ν hνp π
    have hscalar :
        (∑ W ∈ base.powerset, (-1 : k) ^ W.card) = 0 := by
      exact Finset.sum_powerset_neg_one_pow_card_eq_zero_of_nonempty
        base hbase_nonempty
    have hpoly :
        (∑ W ∈ base.powerset,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.card)) = 0 := by
      have hmap :
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              (∑ W ∈ base.powerset, (-1 : k) ^ W.card) =
            ∑ W ∈ base.powerset,
              MvPolynomial.C (R := k) (σ := Fin m × Fin n)
                ((-1 : k) ^ W.card) := by
        exact map_sum (MvPolynomial.C (R := k) (σ := Fin m × Fin n))
          (fun W => (-1 : k) ^ W.card) base.powerset
      rw [← hmap, hscalar]
      simp
    let e : Source ≃ Target := {
      toFun W := ⟨W.1, W.2.2⟩
      invFun W := ⟨W.1, hpreD, W.2⟩
      left_inv := by
        intro W
        ext
        rfl
      right_inv := by
        intro W
        ext
        rfl }
    have htarget :
        (∑ W : Target,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0 := by
      letI : Fintype Target := Finset.Subtype.fintype base.powerset
      have huniv :
          (Finset.univ : Finset Target) = base.powerset.attach := by
        ext W
        constructor
        · intro _
          exact Finset.mem_attach base.powerset W
        · intro _
          exact Finset.mem_univ W
      change
        (∑ W ∈ (Finset.univ : Finset Target),
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0
      rw [huniv]
      exact
        (base.powerset.sum_attach
          (fun W =>
            MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              ((-1 : k) ^ W.card))).trans hpoly
    have hsource :
        (∑ W : Source,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0 := by
      calc
        (∑ W : Source,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card))
            =
          ∑ W : Target,
            MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              ((-1 : k) ^ W.1.card) := by
            refine Fintype.sum_equiv e _ _ ?_
            intro W
            rfl
        _ = 0 := htarget
    rw [← Finset.mul_sum, hsource]
    simp
  · apply Finset.sum_eq_zero
    intro W _hW
    exact False.elim (hpreD W.2.1)

lemma swan_component_col_hodgeSplit_total_laplace_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    (∑ S : RawMinorPair.BiReshuffle.HodgeColSplit T.toRawPair ν hνp,
      MvPolynomial.C (swan_component_col_hodgeCoeff k T ν hνp S) *
        RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0 := by
  classical
  rw [RawMinorPair.BiReshuffle.HodgeColSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    k (P := T.toRawPair)
    (swan_component_col_hodgeCoeff k T ν hνp)]
  rw [RawMinorPair.BiReshuffle.HodgeColSplit.LeibnizTerm.sum_eq_sum_ambientW
    (P := T.toRawPair) (ν := ν) (hνp := hνp)
    (f := fun X =>
      MvPolynomial.C (swan_component_col_hodgeCoeff k T ν hνp X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)))
    (g := fun π W =>
      swan_component_col_commonLeibnizTerm k T ν hνp π *
        MvPolynomial.C ((-1 : k) ^ W.1.card))]
  · apply Finset.sum_eq_zero
    intro π _hπ
    exact swan_component_col_inner_powerset_sum_eq_zero
      k T ν hνp π
  · intro X
    exact swan_component_col_hodge_leibnizTerm_eq_common
      k T ν hνp X

lemma swan_component_row_inner_powerset_sum_eq_zero
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    (∑ W : { W : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) //
        RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset
            T.toRawPair π.symm ⊆
          RawMinorPair.BiReshuffle.Hodge.hodgeD T.toRawPair ν ∧
        W ∈ (RawMinorPair.BiReshuffle.Hodge.hodgeC T.toRawPair ν hνp \
          RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset
            T.toRawPair π.symm).powerset },
      swan_component_row_commonLeibnizTerm k T ν hνp π *
        MvPolynomial.C ((-1 : k) ^ W.1.card)) = 0 := by
  classical
  let P := T.toRawPair
  let base : Finset (Fin (P.p + P.q)) :=
    RawMinorPair.BiReshuffle.Hodge.hodgeC P ν hνp \
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π.symm
  let common := swan_component_row_commonLeibnizTerm k T ν hνp π
  let Source : Type :=
    { W : Finset (Fin (P.p + P.q)) //
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π.symm ⊆
        RawMinorPair.BiReshuffle.Hodge.hodgeD P ν ∧
      W ∈ base.powerset }
  let Target : Type := { W : Finset (Fin (P.p + P.q)) // W ∈ base.powerset }
  change
    (∑ W : Source, common *
      MvPolynomial.C (R := k) (σ := Fin m × Fin n)
        ((-1 : k) ^ W.1.card)) = 0
  by_cases hpreD :
      RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset P π.symm ⊆
        RawMinorPair.BiReshuffle.Hodge.hodgeD P ν
  · have hbase_nonempty : base.Nonempty := by
      simpa [P, base] using
        RawMinorPair.BiReshuffle.Hodge.hodgeC_sdiff_permPreimageLeftSlotFinset_nonempty
          P ν hνp π.symm
    have hscalar :
        (∑ W ∈ base.powerset, (-1 : k) ^ W.card) = 0 := by
      exact Finset.sum_powerset_neg_one_pow_card_eq_zero_of_nonempty
        base hbase_nonempty
    have hpoly :
        (∑ W ∈ base.powerset,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.card)) = 0 := by
      have hmap :
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              (∑ W ∈ base.powerset, (-1 : k) ^ W.card) =
            ∑ W ∈ base.powerset,
              MvPolynomial.C (R := k) (σ := Fin m × Fin n)
                ((-1 : k) ^ W.card) := by
        exact map_sum (MvPolynomial.C (R := k) (σ := Fin m × Fin n))
          (fun W => (-1 : k) ^ W.card) base.powerset
      rw [← hmap, hscalar]
      simp
    let e : Source ≃ Target := {
      toFun W := ⟨W.1, W.2.2⟩
      invFun W := ⟨W.1, hpreD, W.2⟩
      left_inv := by
        intro W
        ext
        rfl
      right_inv := by
        intro W
        ext
        rfl }
    have htarget :
        (∑ W : Target,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0 := by
      letI : Fintype Target := Finset.Subtype.fintype base.powerset
      have huniv :
          (Finset.univ : Finset Target) = base.powerset.attach := by
        ext W
        constructor
        · intro _
          exact Finset.mem_attach base.powerset W
        · intro _
          exact Finset.mem_univ W
      change
        (∑ W ∈ (Finset.univ : Finset Target),
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0
      rw [huniv]
      exact
        (base.powerset.sum_attach
          (fun W =>
            MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              ((-1 : k) ^ W.card))).trans hpoly
    have hsource :
        (∑ W : Source,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card)) = 0 := by
      calc
        (∑ W : Source,
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ W.1.card))
            =
          ∑ W : Target,
            MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              ((-1 : k) ^ W.1.card) := by
            refine Fintype.sum_equiv e _ _ ?_
            intro W
            rfl
        _ = 0 := htarget
    rw [← Finset.mul_sum, hsource]
    simp
  · apply Finset.sum_eq_zero
    intro W _hW
    exact False.elim (hpreD W.2.1)

lemma swan_component_row_hodgeSplit_total_laplace_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t) :
    (∑ S : RawMinorPair.BiReshuffle.HodgeRowSplit T.toRawPair ν hνp,
      MvPolynomial.C (swan_component_row_hodgeCoeff k T ν hνp S) *
        RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0 := by
  classical
  rw [RawMinorPair.BiReshuffle.HodgeRowSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    k (P := T.toRawPair)
    (swan_component_row_hodgeCoeff k T ν hνp)]
  rw [RawMinorPair.BiReshuffle.HodgeRowSplit.LeibnizTerm.sum_eq_sum_ambientW
    (P := T.toRawPair) (ν := ν) (hνp := hνp)
    (f := fun X =>
      MvPolynomial.C (swan_component_row_hodgeCoeff k T ν hνp X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)))
    (g := fun π W =>
      swan_component_row_commonLeibnizTerm k T ν hνp π *
        MvPolynomial.C ((-1 : k) ^ W.1.card))]
  · apply Finset.sum_eq_zero
    intro π _hπ
    exact swan_component_row_inner_powerset_sum_eq_zero
      k T ν hνp π
  · intro X
    exact swan_component_row_hodge_leibnizTerm_eq_common
      k T ν hνp X

lemma swan_corollary2_8_size_inner_Icc_sum_eq_zero
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t)
    (π : Equiv.Perm (Fin (T.toRawPair.p + T.toRawPair.q))) :
    (∑ C :
        { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) //
          C ∈ Finset.Icc
            (RawMinorPair.BiReshuffle.leftSlotFinset T.toRawPair ∪
              RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset T.toRawPair π)
            Finset.univ },
        swan_corollary2_8_size_commonLeibnizTerm k T π *
          MvPolynomial.C ((-1 : k) ^ C.1ᶜ.card)) = 0 := by
  classical
  let interval : Finset (Finset (Fin (T.toRawPair.p + T.toRawPair.q))) :=
    Finset.Icc
      (RawMinorPair.BiReshuffle.leftSlotFinset T.toRawPair ∪
        RawMinorPair.BiReshuffle.permPreimageLeftSlotFinset T.toRawPair π)
      Finset.univ
  let common := swan_corollary2_8_size_commonLeibnizTerm k T π
  have hzero :=
    sum_Icc_leftSlotFinset_toRawPair_union_permPreimage_neg_one_pow_card_compl_eq_zero
      k T hsize π
  have hpoly_zero :
      (∑ s ∈ interval,
        MvPolynomial.C (R := k) (σ := Fin m × Fin n)
          ((-1 : k) ^ sᶜ.card)) = 0 := by
    have hmap :
        MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            (∑ s ∈ interval, (-1 : k) ^ sᶜ.card) =
          ∑ s ∈ interval,
            MvPolynomial.C (R := k) (σ := Fin m × Fin n)
              ((-1 : k) ^ sᶜ.card) := by
      exact map_sum (MvPolynomial.C (R := k) (σ := Fin m × Fin n))
        (fun s => (-1 : k) ^ sᶜ.card) interval
    rw [← hmap, hzero]
    simp
  have hsubtype :
      (∑ C :
        { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) // C ∈ interval },
        MvPolynomial.C (R := k) (σ := Fin m × Fin n)
          ((-1 : k) ^ C.1ᶜ.card)) = 0 := by
    letI : Fintype
        { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) // C ∈ interval } :=
      Finset.Subtype.fintype interval
    have huniv :
        (Finset.univ : Finset
          { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) // C ∈ interval }) =
          interval.attach := by
      ext C
      constructor
      · intro _
        exact Finset.mem_attach interval C
      · intro _
        exact Finset.mem_univ C
    change
      (∑ C ∈ (Finset.univ : Finset
        { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) // C ∈ interval }),
        MvPolynomial.C (R := k) (σ := Fin m × Fin n)
          ((-1 : k) ^ C.1ᶜ.card)) = 0
    rw [huniv]
    exact
      (interval.sum_attach
        (fun s =>
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ sᶜ.card))).trans hpoly_zero
  change
    (∑ C :
        { C : Finset (Fin (T.toRawPair.p + T.toRawPair.q)) // C ∈ interval },
        common *
          MvPolynomial.C (R := k) (σ := Fin m × Fin n)
            ((-1 : k) ^ C.1ᶜ.card)) = 0
  rw [← Finset.mul_sum]
  rw [hsubtype]
  simp

lemma swan_corollary2_8_size_containing_total_laplace_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    (∑ S : RawMinorPair.BiReshuffle.ContainingSplit T.toRawPair,
      MvPolynomial.C (swan_corollary2_8_size_containingCoeff k T S) *
        RawMinorPair.laplacePolynomial k S.toBiReshuffle.toPair) = 0 := by
  classical
  rw [RawMinorPair.BiReshuffle.ContainingSplit.sum_laplacePolynomial_eq_sum_leibnizTerm
    k (P := T.toRawPair)
    (swan_corollary2_8_size_containingCoeff k T)]
  rw [RawMinorPair.BiReshuffle.ContainingSplit.LeibnizTerm.sum_eq_sum_ambient_Icc
    (P := T.toRawPair)
    (f := fun X =>
      MvPolynomial.C (swan_corollary2_8_size_containingCoeff k T X.1) *
        (MvPolynomial.C
            (RawMinorPair.laplaceCoeff k X.1.toBiReshuffle.toPair) *
          (((Equiv.Perm.sign X.2.1 :
              MvPolynomial (Fin m × Fin n) k) *
            (Equiv.Perm.sign X.2.2 :
              MvPolynomial (Fin m × Fin n) k)) *
            ∏ j : Fin (T.toRawPair.p + T.toRawPair.q),
              RawMinorPair.BiReshuffle.slotMatrix k T.toRawPair
                (X.ambientPerm j) j)))
    (g := fun π C =>
      swan_corollary2_8_size_commonLeibnizTerm k T π *
        MvPolynomial.C ((-1 : k) ^ C.1ᶜ.card))]
  · apply Finset.sum_eq_zero
    intro π _hπ
    exact swan_corollary2_8_size_inner_Icc_sum_eq_zero k T hsize π
  · intro X
    exact swan_corollary2_8_size_leibnizTerm_eq_common k T X

lemma swan_corollary2_8_size_total_iccSplit_laplace_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.F.t < T.G.t) :
    ∃ coeffIcc :
        RawMinorPair.BiReshuffle.ContainingSplit.IccSplit T.toRawPair → k,
      coeffIcc
          (RawMinorPair.BiReshuffle.ContainingSplit.toIccSplit
            (RawMinorPair.BiReshuffle.ContainingSplit.pivot T.toRawPair)) =
        (-1 : k) ∧
      (∑ S : RawMinorPair.BiReshuffle.ContainingSplit.IccSplit T.toRawPair,
        MvPolynomial.C (coeffIcc S) *
          RawMinorPair.laplacePolynomial k
            (RawMinorPair.BiReshuffle.ContainingSplit.ofIccSplit S).toBiReshuffle.toPair) =
        0 := by
  classical
  refine ⟨swan_corollary2_8_size_iccCoeff k T,
    swan_corollary2_8_size_iccCoeff_pivot k T, ?_⟩
  have hcont :=
    swan_corollary2_8_size_containing_total_laplace_sum k T hsize
  rw [RawMinorPair.BiReshuffle.ContainingSplit.sum_containingSplit_eq_sum_iccSplit] at hcont
  simpa [swan_corollary2_8_size_iccCoeff,
    swan_corollary2_8_size_containingCoeff] using hcont

/-- Swan Corollary 2.8, size-defect determinant identity, in the raw
sorted-promotable form.

This is the genuine determinant/Laplace identity for the branch
`T.F.t < T.G.t`.  The finite sum ranges over raw bi-reshuffles whose four
determinants survive after deleting repeated rows/columns and whose sorted
first factor is promotable to a strictly smaller Swan first factor.

The downstream theorem `swan_corollary2_8_size_signed_determinant_laplace_identity`
is obtained from this statement by collecting equal sorted support terms in
`BiReshuffleSupport`. -/
theorem swan_corollary2_8_size_raw_sortedPromotable_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (_hp : 0 < p)
    (_hsize : T.F.t < T.G.t) :
    ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
        SwanRawLaplaceProductTerm.BiReshuffleSupport.IsSortedPromotable T E } → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
            SwanRawLaplaceProductTerm.BiReshuffleSupport.IsSortedPromotable T E },
          MvPolynomial.C (coeff E) *
            RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
  classical
  have hLaplaceSupport :
      ∃ coeff : { E : RawMinorPair.BiReshuffle T.toRawPair //
          BiReshuffleSupport.IsSizeBranchLaplaceSupport T E } → k,
        - RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ E : { E : RawMinorPair.BiReshuffle T.toRawPair //
              BiReshuffleSupport.IsSizeBranchLaplaceSupport T E },
            MvPolynomial.C (coeff E) *
              RawMinorPair.laplacePolynomial k E.1.toPair = 0 := by
    rcases swan_corollary2_8_size_total_iccSplit_laplace_sum
        k T _hsize with ⟨coeffIcc, hpivotIcc, hsumIcc⟩
    rcases swan_corollary2_8_size_containingSplit_total_laplace_sum_of_iccSplit
        k T coeffIcc hpivotIcc hsumIcc with
      ⟨coeff, hpivot, hsum⟩
    exact exists_coeff_sizeBranchLaplaceSupport_of_total_containingSplit_laplace_sum
      k T coeff hpivot hsum
  rcases hLaplaceSupport with ⟨coeffSupport, hSupport⟩
  rcases BiReshuffleSupport.exists_coeff_sortedPromotable_sum_of_sizeBranchLaplaceSupport
      k (T := T) coeffSupport with ⟨coeff, hpush⟩
  refine ⟨coeff, ?_⟩
  rw [← hpush]
  exact hSupport

/-- Swan's signed determinant/Laplace identity for the size-defect branch.

In Swan's proof of Theorem 3.1 this is the `|A| < |B|` bad-product case:
Corollary 2.8 gives a signed sum of Laplace products equal to zero, containing
the original product as the distinguished term.  After deleting determinant-zero
terms and promoting the surviving raw pairs to `BiReshuffleSupport`, this is the
exact signed identity needed by `swan_corollary2_7_size_pivot_laplace_identity`.

The theorem is deliberately stated at the raw Laplace-product level: the
following proof block removes the common Laplace sign and converts raw pairs to
`MinorWord`s. -/
theorem swan_corollary2_8_size_signed_determinant_laplace_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.F.t < T.G.t) :
    ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  rcases swan_corollary2_8_size_raw_sortedPromotable_identity
      k T hp hsize with ⟨coeff, hraw⟩
  rcases BiReshuffleSupport.exists_coeff_support_sum_raw_sortedPromotable
      k (T := T) coeff with ⟨coeffRest, hsupport⟩
  refine ⟨coeffRest, ?_⟩
  rw [← hsupport]
  exact hraw

theorem LT_wellFounded {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q} :
    WellFounded (@LT m n p q I J) := by
  classical
  exact InvImage.wf (fun T : SwanRawLaplaceProductTerm I J => T.F)
    MinorFactor.pairLT_wellFounded

def toGoodTerm {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) (hgood : T.IsGood) :
    SwanLaplaceProductTerm I J where
  F := T.F
  G := T.G
  pairLE := hgood
  firstLE := T.firstLE
  row_content := T.row_content
  col_content := T.col_content

lemma toGoodTerm_toWord {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) (hgood : T.IsGood) :
    (T.toGoodTerm hgood).toWord = T.toWord := by
  rfl

noncomputable def initial {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    SwanRawLaplaceProductTerm I J where
  F := { t := p, idx := I }
  G := { t := q, idx := J }
  firstLE := MinorIndex.PairLE.refl I
  row_content := by
    simp [MinorFactor.rowContent]
  col_content := by
    simp [MinorFactor.colContent]

lemma initial_isGood_iff {m n p q : ℕ}
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    (SwanRawLaplaceProductTerm.initial I J).IsGood ↔
      MinorIndex.PairLE I J := by
  rfl

lemma toPolynomial_initial {m n p q : ℕ}
    (k : Type*) [CommRing k]
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    MinorWord.toPolynomial k
        (SwanRawLaplaceProductTerm.initial I J).toWord =
      genericMinor k I * genericMinor k J := by
  simp [SwanRawLaplaceProductTerm.initial, SwanRawLaplaceProductTerm.toWord,
    MinorFactor.toPolynomial]

/-- Package a replacement pair whose first factor is strictly below the old
first factor as a raw Laplace-product term below `T`.  The row and column
content hypotheses are the content-preservation part of Swan's Corollary 2.8
after moving the original term to the other side. -/
def mkLower {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (F G : MinorFactor m n)
    (hF : MinorFactor.PairLT F T.F)
    (hrow :
      MinorWord.rowContent ⟨[F, G]⟩ =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      MinorWord.colContent ⟨[F, G]⟩ =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    SwanRawLaplaceProductTerm I J where
  F := F
  G := G
  firstLE := MinorIndex.PairLE.trans hF.pairLE T.firstLE
  row_content := hrow
  col_content := hcol

@[simp] lemma mkLower_F {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (F G : MinorFactor m n)
    (hF : MinorFactor.PairLT F T.F)
    (hrow :
      MinorWord.rowContent ⟨[F, G]⟩ =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      MinorWord.colContent ⟨[F, G]⟩ =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    (T.mkLower F G hF hrow hcol).F = F := rfl

lemma mkLower_LT {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (F G : MinorFactor m n)
    (hF : MinorFactor.PairLT F T.F)
    (hrow :
      MinorWord.rowContent ⟨[F, G]⟩ =
        MinorIndex.rowContent I + MinorIndex.rowContent J)
    (hcol :
      MinorWord.colContent ⟨[F, G]⟩ =
        MinorIndex.colContent I + MinorIndex.colContent J) :
    LT (T.mkLower F G hF hrow hcol) T := by
  simpa [LT, mkLower] using hF

end SwanRawLaplaceProductTerm

/-- One step of Swan Corollary 2.7: a bad raw Laplace product is rewritten as
a finite sum of raw products of strictly smaller bad-product rank. -/
structure SwanRawLaplaceReduction
    (k : Type*) [Field k]
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) where
  ι : Type
  instFintype : Fintype ι
  coeff : ι → k
  term : ι → SwanRawLaplaceProductTerm I J
  term_decrease :
    ∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T
  poly_eq :
    MinorWord.toPolynomial k T.toWord =
      ∑ x : ι,
        MvPolynomial.C (coeff x) *
          MinorWord.toPolynomial k
            (SwanRawLaplaceProductTerm.toWord (term x))

attribute [instance] SwanRawLaplaceReduction.instFintype

/-- A finished expansion of a raw Laplace product into good products.  This is
the induction target for Swan Corollary 2.8. -/
structure SwanRawGoodExpansion
    (k : Type*) [Field k]
    {m n p q : ℕ}
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J) where
  ι : Type
  instFintype : Fintype ι
  coeff : ι → k
  term : ι → SwanLaplaceProductTerm I J
  poly_eq :
    MinorWord.toPolynomial k T.toWord =
      ∑ x : ι,
        MvPolynomial.C (coeff x) *
          MinorWord.toPolynomial k
            (SwanLaplaceProductTerm.toWord (term x))

attribute [instance] SwanRawGoodExpansion.instFintype

namespace SwanRawGoodExpansion

def toInitialExpansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanRawGoodExpansion k
      (SwanRawLaplaceProductTerm.initial I J)) :
    SwanLaplaceProductExpansion k I J where
  ι := E.ι
  instFintype := E.instFintype
  coeff := E.coeff
  term := E.term
  poly_eq := by
    rw [← SwanRawLaplaceProductTerm.toPolynomial_initial k I J]
    exact E.poly_eq

end SwanRawGoodExpansion

lemma swan_raw_good_expansion_of_good
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hgood : T.IsGood) :
    Nonempty (SwanRawGoodExpansion k T) := by
  classical
  let G : SwanLaplaceProductTerm I J := T.toGoodTerm hgood
  refine ⟨
    { ι := PUnit
      instFintype := inferInstance
      coeff := fun _ => (1 : k)
      term := fun _ => G
      poly_eq := ?_ }⟩
  simp [G, SwanRawLaplaceProductTerm.toGoodTerm,
    SwanRawLaplaceProductTerm.toWord, SwanLaplaceProductTerm.toWord]

lemma swanRawLaplaceReduction_of_finite_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    {ι : Type} (inst : Fintype ι)
    (coeff : ι → k)
    (term : ι → SwanRawLaplaceProductTerm I J)
    (hdecr : ∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T)
    (hpoly :
      letI := inst
      MinorWord.toPolynomial k T.toWord =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanRawLaplaceProductTerm.toWord (term x))) :
    Nonempty (SwanRawLaplaceReduction k T) := by
  exact ⟨
    { ι := ι
      instFintype := inst
      coeff := coeff
      term := term
      term_decrease := hdecr
      poly_eq := hpoly }⟩

namespace SwanRawLaplaceReduction

noncomputable def bindGoodExpansion
    {m n p q : ℕ}
    {k : Type*} [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    {T : SwanRawLaplaceProductTerm I J}
    (R : SwanRawLaplaceReduction k T)
    (E : ∀ x : R.ι, SwanRawGoodExpansion k (R.term x)) :
    SwanRawGoodExpansion k T where
  ι := Sigma (fun x : R.ι => (E x).ι)
  instFintype := by
    classical
    infer_instance
  coeff := fun xy => R.coeff xy.1 * (E xy.1).coeff xy.2
  term := fun xy => (E xy.1).term xy.2
  poly_eq := by
    classical
    rw [R.poly_eq]
    calc
      (∑ x : R.ι,
        MvPolynomial.C (R.coeff x) *
          MinorWord.toPolynomial k
            (SwanRawLaplaceProductTerm.toWord (R.term x)))
          =
        ∑ x : R.ι,
          MvPolynomial.C (R.coeff x) *
            (∑ y : (E x).ι,
              MvPolynomial.C ((E x).coeff y) *
                MinorWord.toPolynomial k
                  (SwanLaplaceProductTerm.toWord ((E x).term y))) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [(E x).poly_eq]
      _ =
        ∑ x : R.ι, ∑ y : (E x).ι,
          MvPolynomial.C (R.coeff x * (E x).coeff y) *
            MinorWord.toPolynomial k
              (SwanLaplaceProductTerm.toWord ((E x).term y)) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _hy
          rw [MvPolynomial.C_mul]
          ring
      _ =
        ∑ xy : Sigma (fun x : R.ι => (E x).ι),
          MvPolynomial.C (R.coeff xy.1 * (E xy.1).coeff xy.2) *
            MinorWord.toPolynomial k
              (SwanLaplaceProductTerm.toWord ((E xy.1).term xy.2)) := by
          exact (Fintype.sum_sigma' (fun x y =>
            MvPolynomial.C (R.coeff x * (E x).coeff y) *
              MinorWord.toPolynomial k
                (SwanLaplaceProductTerm.toWord ((E x).term y)))).symm

end SwanRawLaplaceReduction

/-- Convert a signed raw Laplace identity supported on promotable bi-reshuffles
into the finite raw-reduction identity used by Corollary 2.7.

The determinant identity is naturally stated with `RawMinorPair.laplacePolynomial`,
so every term carries the same signed Laplace coefficient.  This helper removes
that common unit and promotes the surviving support terms to
`SwanRawLaplaceProductTerm`s. -/
lemma swan_raw_finite_identity_of_signed_support_laplace_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hSigned :
      ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
        -RawMinorPair.laplacePolynomial k T.toRawPair +
          ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
            MvPolynomial.C (coeffRest S) *
              RawMinorPair.laplacePolynomial k S.E.toPair = 0) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ term : ι → SwanRawLaplaceProductTerm I J,
        (∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T) ∧
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) := by
  classical
  let Support := SwanRawLaplaceProductTerm.BiReshuffleSupport T
  rcases hSigned with ⟨coeffRest, hSigned⟩
  let a : k := RawMinorPair.laplaceCoeff k T.toRawPair
  let P : MvPolynomial (Fin m × Fin n) k :=
    MinorWord.toPolynomial k T.toWord
  let Q : Support → MvPolynomial (Fin m × Fin n) k :=
    fun S => MinorWord.toPolynomial k S.toRawTerm.toWord
  have hSigned' :
      - (MvPolynomial.C a * P) +
        ∑ S : Support, MvPolynomial.C (coeffRest S) *
          (MvPolynomial.C a * Q S) = 0 := by
    have hpivot :
        RawMinorPair.laplacePolynomial k T.toRawPair =
          MvPolynomial.C a * P := by
      simpa [a, P] using
        SwanRawLaplaceProductTerm.toRawPair_laplacePolynomial
          k T
    have hterm :
        ∀ S : Support,
          RawMinorPair.laplacePolynomial k S.E.toPair =
            MvPolynomial.C a * Q S := by
      intro S
      simpa [a, Q] using
        SwanRawLaplaceProductTerm.ofBiReshuffleOfStrictMono_laplacePolynomial
          k T S.E S.hLrow S.hLcol S.hRrow S.hRcol S.firstLE
    simpa [Support, hpivot, hterm] using hSigned
  have hUnsigned :
      - P + ∑ S : Support, MvPolynomial.C (coeffRest S) * Q S = 0 := by
    exact signed_sum_cancel_common_C_unit
      (α := Support) (σ := Fin m × Fin n) k
      a (RawMinorPair.laplaceCoeff_isUnit k T.toRawPair)
      coeffRest P Q hSigned'
  have hpoly :
      P =
        ∑ S : Support, MvPolynomial.C (coeffRest S) * Q S := by
    have h' :
        (∑ S : Support, MvPolynomial.C (coeffRest S) * Q S) + -P = 0 := by
      simpa [add_comm] using hUnsigned
    have hneg :
        (∑ S : Support, MvPolynomial.C (coeffRest S) * Q S) = -(-P) :=
      eq_neg_of_add_eq_zero_left h'
    simpa using hneg.symm
  refine ⟨Support, inferInstance, coeffRest, (fun S : Support => S.toRawTerm),
    ?_, ?_⟩
  · intro S
    exact S.toRawTerm_LT
  · simpa [Support, P, Q] using hpoly

/-- Swan Corollary 2.7, size-defect case, before moving the distinguished
bad product to the other side.  The finite Laplace identity contains one
distinguished term equal to the original raw product, with coefficient `-1`;
all other terms have strictly smaller first factor.

This is the determinant-theoretic core of the size branch. -/
theorem swan_corollary2_7_size_pivot_laplace_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.F.t < T.G.t) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ pivot : ι,
      ∃ coeff : ι → k,
      ∃ F : ι → MinorFactor m n,
      ∃ G : ι → MinorFactor m n,
        coeff pivot = (-1 : k) ∧
        F pivot = T.F ∧
        G pivot = T.G ∧
        (∀ x : ι, x ≠ pivot → MinorFactor.PairLT (F x) T.F) ∧
        (∀ x : ι,
          MinorWord.rowContent ⟨[F x, G x]⟩ =
            MinorIndex.rowContent I + MinorIndex.rowContent J) ∧
        (∀ x : ι,
          MinorWord.colContent ⟨[F x, G x]⟩ =
            MinorIndex.colContent I + MinorIndex.colContent J) ∧
        (letI := inst
        (∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k ⟨[F x, G x]⟩) = 0) := by
  classical
  have hLaplace :
      ∃ ι : Type, ∃ inst : Fintype ι,
        ∃ pivot : ι,
        ∃ coeff : ι → k,
        ∃ term : ι → SwanRawLaplaceProductTerm I J,
          coeff pivot = (-1 : k) ∧
          term pivot = T ∧
          (∀ x : ι, x ≠ pivot → SwanRawLaplaceProductTerm.LT (term x) T) ∧
          (letI := inst
          (∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) = 0) := by
    let Support := SwanRawLaplaceProductTerm.BiReshuffleSupport T
    have hSupportLaplace :
        ∃ coeffRest : Support → k,
        let coeffOpt : Option Support → k
          | none => (-1 : k)
          | some S => coeffRest S
        let termOpt : Option Support → SwanRawLaplaceProductTerm I J
          | none => T
          | some S => S.toRawTerm
          (∑ x : Option Support,
            MvPolynomial.C (coeffOpt x) *
              MinorWord.toPolynomial k
                (termOpt x).toWord) = 0 := by
      /- Core determinant step: expand Swan's alternating Laplace
         relation for the size defect `T.F.t < T.G.t`, then discard zero terms.
         The surviving nonzero terms are exactly the promotable
         `BiReshuffleSupport`s.  The algebra below removes the common
         Laplace sign attached to every raw pair in this bi-reshuffle family. -/
      have hSignedSupportLaplace :
          ∃ coeffRest : Support → k,
            - RawMinorPair.laplacePolynomial k T.toRawPair +
              ∑ S : Support,
                MvPolynomial.C (coeffRest S) *
                  RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
        exact
          SwanRawLaplaceProductTerm.swan_corollary2_8_size_signed_determinant_laplace_identity
            k T hp hsize
      rcases hSignedSupportLaplace with ⟨coeffRest, hSigned⟩
      let a : k := RawMinorPair.laplaceCoeff k T.toRawPair
      let P : MvPolynomial (Fin m × Fin n) k :=
        MinorWord.toPolynomial k T.toWord
      let Q : Support → MvPolynomial (Fin m × Fin n) k :=
        fun S => MinorWord.toPolynomial k S.toRawTerm.toWord
      have hSigned' :
          - (MvPolynomial.C a * P) +
            ∑ S : Support, MvPolynomial.C (coeffRest S) *
              (MvPolynomial.C a * Q S) = 0 := by
        have hpivot :
            RawMinorPair.laplacePolynomial k T.toRawPair =
              MvPolynomial.C a * P := by
          simpa [a, P] using
            SwanRawLaplaceProductTerm.toRawPair_laplacePolynomial
              k T
        have hterm :
            ∀ S : Support,
              RawMinorPair.laplacePolynomial k S.E.toPair =
                MvPolynomial.C a * Q S := by
          intro S
          simpa [a, Q] using
            SwanRawLaplaceProductTerm.ofBiReshuffleOfStrictMono_laplacePolynomial
              k T S.E S.hLrow S.hLcol S.hRrow S.hRcol S.firstLE
        simpa [hpivot, hterm] using hSigned
      have hUnsigned :
          - P + ∑ S : Support, MvPolynomial.C (coeffRest S) * Q S = 0 := by
        exact signed_sum_cancel_common_C_unit
          (α := Support) (σ := Fin m × Fin n) k
          a (RawMinorPair.laplaceCoeff_isUnit k T.toRawPair)
          coeffRest P Q hSigned'
      refine ⟨coeffRest, ?_⟩
      let coeffOpt : Option Support → k
        | none => (-1 : k)
        | some S => coeffRest S
      let termOpt : Option Support → SwanRawLaplaceProductTerm I J
        | none => T
        | some S => S.toRawTerm
      simpa [coeffOpt, termOpt, P, Q] using hUnsigned
    rcases hSupportLaplace with ⟨coeffRest, hsum⟩
    let coeffOpt : Option Support → k
      | none => (-1 : k)
      | some S => coeffRest S
    let termOpt : Option Support → SwanRawLaplaceProductTerm I J
      | none => T
      | some S => S.toRawTerm
    refine ⟨Option Support, inferInstance, none,
      coeffOpt, termOpt, ?_, ?_, ?_, ?_⟩
    · rfl
    · rfl
    · intro x hx
      cases x with
      | none => exact False.elim (hx rfl)
      | some S => exact S.toRawTerm_LT
    · exact hsum
  rcases hLaplace with
    ⟨ι, inst, pivot, coeff, term, hpivot_coeff, hpivot_term, hdecr, hsum⟩
  let F : ι → MinorFactor m n := fun x => (term x).F
  let G : ι → MinorFactor m n := fun x => (term x).G
  refine ⟨ι, inst, pivot, coeff, F, G, hpivot_coeff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [F, hpivot_term]
  · simp [G, hpivot_term]
  · intro x hx
    exact hdecr x hx
  · intro x
    simpa [F, G, SwanRawLaplaceProductTerm.toWord] using (term x).row_content
  · intro x
    simpa [F, G, SwanRawLaplaceProductTerm.toWord] using (term x).col_content
  · simpa [F, G, SwanRawLaplaceProductTerm.toWord] using hsum

/-- Swan Corollary 2.7, size-defect case, in the support form supplied by
the Laplace-product computation: each produced pair has the same total
row/column content and a strictly smaller first factor. -/
theorem swan_corollary2_7_size_lower_factor_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.F.t < T.G.t) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ F : ι → MinorFactor m n,
      ∃ G : ι → MinorFactor m n,
      ∃ hF : ∀ x : ι, MinorFactor.PairLT (F x) T.F,
      ∃ hrow :
        ∀ x : ι,
          MinorWord.rowContent ⟨[F x, G x]⟩ =
            MinorIndex.rowContent I + MinorIndex.rowContent J,
      ∃ hcol :
        ∀ x : ι,
          MinorWord.colContent ⟨[F x, G x]⟩ =
            MinorIndex.colContent I + MinorIndex.colContent J,
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord
                  (T.mkLower (F x) (G x) (hF x) (hrow x) (hcol x)))) := by
  classical
  rcases swan_corollary2_7_size_pivot_laplace_identity
      k T hp hsize with
    ⟨ι, inst, pivot, coeff₀, F₀, G₀, hpivot_coeff, hpivot_F, hpivot_G,
      hlower, hrow₀, hcol₀, hsum_zero⟩
  let s : Finset ι := Finset.univ.erase pivot
  let ι' : Type := { x : ι // x ∈ s }
  let inst' : Fintype ι' := by infer_instance
  let coeff : ι' → k := fun x => coeff₀ x.1
  let F : ι' → MinorFactor m n := fun x => F₀ x.1
  let G : ι' → MinorFactor m n := fun x => G₀ x.1
  have hF : ∀ x : ι', MinorFactor.PairLT (F x) T.F := by
    intro x
    have hxne : x.1 ≠ pivot := (Finset.mem_erase.mp x.2).1
    exact hlower x.1 hxne
  have hrow : ∀ x : ι',
      MinorWord.rowContent ⟨[F x, G x]⟩ =
        MinorIndex.rowContent I + MinorIndex.rowContent J := by
    intro x
    exact hrow₀ x.1
  have hcol : ∀ x : ι',
      MinorWord.colContent ⟨[F x, G x]⟩ =
        MinorIndex.colContent I + MinorIndex.colContent J := by
    intro x
    exact hcol₀ x.1
  refine ⟨ι', inst', coeff, F, G, hF, hrow, hcol, ?_⟩
  let P : ι → MvPolynomial (Fin m × Fin n) k :=
    fun x =>
      MvPolynomial.C (coeff₀ x) *
        MinorWord.toPolynomial k ⟨[F₀ x, G₀ x]⟩
  have hpivot_term :
      P pivot = - MinorWord.toPolynomial k T.toWord := by
    simp [P, hpivot_coeff, hpivot_F, hpivot_G,
      SwanRawLaplaceProductTerm.toWord]
  have hsum_split :
      (∑ x : ι, P x) =
        P pivot + ∑ x : ι', P x.1 := by
    have hnot_mem : pivot ∉ s := by
      simp [s]
    have hsplit_univ :
        P pivot + Finset.sum s P = ∑ x : ι, P x := by
      simp [s]
    have hsubtype_sum :
        Finset.sum s P = ∑ x : ι', P x.1 := by
      simpa [ι'] using
        (s.sum_attach P).symm
    calc
      (∑ x : ι, P x) = P pivot + Finset.sum s P := hsplit_univ.symm
      _ = P pivot + ∑ x : ι', P x.1 := by rw [hsubtype_sum]
  have hsumP_zero : (∑ x : ι, P x) = 0 := by
    simpa [P] using hsum_zero
  have hrest :
      (∑ x : ι', P x.1) =
        MinorWord.toPolynomial k T.toWord := by
    have h := hsumP_zero
    rw [hsum_split, hpivot_term] at h
    have h' :
        (∑ x : ι', P x.1) + -MinorWord.toPolynomial k T.toWord = 0 := by
      simpa [add_comm] using h
    have hneg :
        (∑ x : ι', P x.1) = -(-MinorWord.toPolynomial k T.toWord) :=
      eq_neg_of_add_eq_zero_left h'
    simpa using hneg
  simpa [P, coeff, F, G, SwanRawLaplaceProductTerm.toWord] using hrest.symm

/-- Swan Corollary 2.7, size-defect case, as the raw finite identity with
strict first-factor decrease.  This is the determinant/Laplace content needed
to build one reduction step. -/
theorem swan_corollary2_7_size_finite_raw_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.F.t < T.G.t) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ term : ι → SwanRawLaplaceProductTerm I J,
        (∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T) ∧
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) := by
  rcases swan_corollary2_7_size_lower_factor_identity
      k T hp hsize with
    ⟨ι, inst, coeff, F, G, hF, hrow, hcol, hpoly⟩
  let term : ι → SwanRawLaplaceProductTerm I J :=
    fun x => T.mkLower (F x) (G x) (hF x) (hrow x) (hcol x)
  refine ⟨ι, inst, coeff, term, ?_, ?_⟩
  · intro x
    exact T.mkLower_LT (F x) (G x) (hF x) (hrow x) (hcol x)
  · simpa [term] using hpoly

/-- The component branch is immediate when the two raw factors are comparable
in the reverse order: commute the two minors and make the old second factor the
new first factor. -/
lemma swan_corollary2_7_reverse_pairLE_finite_raw_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hnotFG : ¬ MinorIndex.PairLE T.F.idx T.G.idx)
    (hGF : MinorIndex.PairLE T.G.idx T.F.idx) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ term : ι → SwanRawLaplaceProductTerm I J,
        (∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T) ∧
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) := by
  classical
  have hF : MinorFactor.PairLT T.G T.F :=
    MinorIndex.PairLT.of_pairLE_not_symm hGF hnotFG
  have hrow :
      MinorWord.rowContent ⟨[T.G, T.F]⟩ =
        MinorIndex.rowContent I + MinorIndex.rowContent J := by
    simpa [SwanRawLaplaceProductTerm.toWord, add_comm] using T.row_content
  have hcol :
      MinorWord.colContent ⟨[T.G, T.F]⟩ =
        MinorIndex.colContent I + MinorIndex.colContent J := by
    simpa [SwanRawLaplaceProductTerm.toWord, add_comm] using T.col_content
  let term : PUnit → SwanRawLaplaceProductTerm I J :=
    fun _ => T.mkLower T.G T.F hF hrow hcol
  refine ⟨PUnit, inferInstance, (fun _ => (1 : k)), term, ?_, ?_⟩
  · intro x
    exact T.mkLower_LT T.G T.F hF hrow hcol
  · simp only [SwanRawLaplaceProductTerm.toWord, MinorWord.toPolynomial_cons,
    MinorFactor.toPolynomial, MinorWord.toPolynomial_nil, Finset.univ_unique,
    PUnit.default_eq_unit, MvPolynomial.C_1, SwanRawLaplaceProductTerm.mkLower_F, mul_comm, one_mul,
    Finset.sum_const, Finset.card_singleton, one_smul, term]
    exact CommMonoid.mul_comm (genericMinor k T.F.idx) (genericMinor k T.G.idx)

/-- Swan Corollary 2.7, componentwise-defect case, as the raw finite identity
with strict first-factor decrease. -/
lemma swan_corollary2_7_component_finite_raw_identity_of_signed_identities
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t)
    (hj :
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j))
    (hrowSigned :
      ∀ (ν : Fin T.G.t) (_hνp : ν.val < T.F.t),
        (∀ μ : Fin T.G.t, μ < ν →
          T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤ T.G.idx.row μ) →
        SwanRawLaplaceProductTerm.RowBadAt T hsize ν →
        ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
          - RawMinorPair.laplacePolynomial k T.toRawPair +
            ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
              MvPolynomial.C (coeffRest S) *
                RawMinorPair.laplacePolynomial k S.E.toPair = 0)
    (hcolSigned :
      ∀ (ν : Fin T.G.t) (_hνp : ν.val < T.F.t),
        (∀ μ : Fin T.G.t, μ < ν →
          T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤ T.G.idx.col μ) →
        SwanRawLaplaceProductTerm.ColBadAt T hsize ν →
        ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
          - RawMinorPair.laplacePolynomial k T.toRawPair +
            ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
              MvPolynomial.C (coeffRest S) *
                RawMinorPair.laplacePolynomial k S.E.toPair = 0) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ term : ι → SwanRawLaplaceProductTerm I J,
        (∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T) ∧
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) := by
  classical
  rcases SwanRawLaplaceProductTerm.rowBad_or_colBad_of_component_violation
      T hsize j hj with hrowj | hcolj
  · have hne : (SwanRawLaplaceProductTerm.rowBadFinset T hsize).Nonempty := by
      refine ⟨j, ?_⟩
      simp [SwanRawLaplaceProductTerm.rowBadFinset, hrowj]
    let ν := SwanRawLaplaceProductTerm.minimalRowBadIndex T hsize hne
    have hνbad : SwanRawLaplaceProductTerm.RowBadAt T hsize ν :=
      SwanRawLaplaceProductTerm.minimalRowBadIndex_bad T hsize hne
    have hνmin :
        ∀ μ : Fin T.G.t, μ < ν →
          T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
            T.G.idx.row μ := by
      intro μ hμ
      exact SwanRawLaplaceProductTerm.row_le_before_minimalRowBadIndex
        T hsize hne μ hμ
    have hνp : ν.val < T.F.t := lt_of_lt_of_le ν.isLt hsize
    rcases hrowSigned ν hνp hνmin hνbad with ⟨coeffRest, hSigned⟩
    exact swan_raw_finite_identity_of_signed_support_laplace_identity
      k T ⟨coeffRest, hSigned⟩
  · have hne : (SwanRawLaplaceProductTerm.colBadFinset T hsize).Nonempty := by
      refine ⟨j, ?_⟩
      simp [SwanRawLaplaceProductTerm.colBadFinset, hcolj]
    let ν := SwanRawLaplaceProductTerm.minimalColBadIndex T hsize hne
    have hνbad : SwanRawLaplaceProductTerm.ColBadAt T hsize ν :=
      SwanRawLaplaceProductTerm.minimalColBadIndex_bad T hsize hne
    have hνmin :
        ∀ μ : Fin T.G.t, μ < ν →
          T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
            T.G.idx.col μ := by
      intro μ hμ
      exact SwanRawLaplaceProductTerm.col_le_before_minimalColBadIndex
        T hsize hne μ hμ
    have hνp : ν.val < T.F.t := lt_of_lt_of_le ν.isLt hsize
    rcases hcolSigned ν hνp hνmin hνbad with ⟨coeffRest, hSigned⟩
    exact swan_raw_finite_identity_of_signed_support_laplace_identity
      k T ⟨coeffRest, hSigned⟩

theorem swan_corollary2_7_component_row_signed_determinant_laplace_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.row ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.row μ)
    (hνbad : SwanRawLaplaceProductTerm.RowBadAt T hsize ν) :
    ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  exact SwanRawLaplaceProductTerm.swan_component_row_signed_identity_of_total_hodge_sum
    k T ν hνp
    (SwanRawLaplaceProductTerm.swan_component_row_hodgeCoeff
      k T ν hνp)
    (SwanRawLaplaceProductTerm.swan_component_row_hodgeCoeff_pivot
      k T ν hνp)
    (fun {E} hE =>
      SwanRawLaplaceProductTerm.BiReshuffleSupport.isSortedPromotable_of_componentRowLaplaceSupport
        T hsize ν hνp hνmin hνbad hE)
    (SwanRawLaplaceProductTerm.swan_component_row_hodgeSplit_total_laplace_sum
      k T ν hνp)

theorem swan_corollary2_7_component_col_signed_determinant_laplace_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hsize : T.G.t ≤ T.F.t)
    (ν : Fin T.G.t) (hνp : ν.val < T.F.t)
    (hνmin :
      ∀ μ : Fin T.G.t, μ < ν →
        T.F.idx.col ⟨μ.val, lt_of_lt_of_le μ.isLt hsize⟩ ≤
          T.G.idx.col μ)
    (hνbad : SwanRawLaplaceProductTerm.ColBadAt T hsize ν) :
    ∃ coeffRest : SwanRawLaplaceProductTerm.BiReshuffleSupport T → k,
      - RawMinorPair.laplacePolynomial k T.toRawPair +
        ∑ S : SwanRawLaplaceProductTerm.BiReshuffleSupport T,
          MvPolynomial.C (coeffRest S) *
            RawMinorPair.laplacePolynomial k S.E.toPair = 0 := by
  classical
  exact SwanRawLaplaceProductTerm.swan_component_col_signed_identity_of_total_hodge_sum
    k T ν hνp
    (SwanRawLaplaceProductTerm.swan_component_col_hodgeCoeff
      k T ν hνp)
    (SwanRawLaplaceProductTerm.swan_component_col_hodgeCoeff_pivot
      k T ν hνp)
    (fun {E} hE =>
      SwanRawLaplaceProductTerm.BiReshuffleSupport.isSortedPromotable_of_componentColLaplaceSupport
        T hsize ν hνp hνmin hνbad hE)
    (SwanRawLaplaceProductTerm.swan_component_col_hodgeSplit_total_laplace_sum
      k T ν hνp)

theorem swan_corollary2_7_component_finite_raw_identity
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (_hp : 0 < p)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t)
    (hj :
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j)) :
    ∃ ι : Type, ∃ inst : Fintype ι,
      ∃ coeff : ι → k,
      ∃ term : ι → SwanRawLaplaceProductTerm I J,
        (∀ x : ι, SwanRawLaplaceProductTerm.LT (term x) T) ∧
        (letI := inst
        MinorWord.toPolynomial k T.toWord =
          ∑ x : ι,
            MvPolynomial.C (coeff x) *
              MinorWord.toPolynomial k
                (SwanRawLaplaceProductTerm.toWord (term x))) := by
  classical
  have hnotFG : ¬ MinorIndex.PairLE T.F.idx T.G.idx :=
    MinorIndex.not_pairLE_of_violation hsize j hj
  by_cases hGF : MinorIndex.PairLE T.G.idx T.F.idx
  · exact swan_corollary2_7_reverse_pairLE_finite_raw_identity
      k T hnotFG hGF
  · exact swan_corollary2_7_component_finite_raw_identity_of_signed_identities
      k T hsize j hj
      (fun ν hνp hνmin hνbad =>
        swan_corollary2_7_component_row_signed_determinant_laplace_identity
          k T hsize ν hνp hνmin hνbad)
      (fun ν hνp hνmin hνbad =>
        swan_corollary2_7_component_col_signed_determinant_laplace_identity
          k T hsize ν hνp hνmin hνbad)

/-- Swan Corollary 2.7 in its correct one-step form. -/
theorem swan_corollary2_7_raw_bad_reduction_size
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.F.t < T.G.t) :
    Nonempty (SwanRawLaplaceReduction k T) := by
  rcases swan_corollary2_7_size_finite_raw_identity
      k T hp hsize with
    ⟨ι, inst, coeff, term, hdecr, hpoly⟩
  exact swanRawLaplaceReduction_of_finite_identity
    k (T := T) inst coeff term hdecr hpoly

theorem swan_corollary2_7_raw_bad_reduction_component
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hsize : T.G.t ≤ T.F.t) (j : Fin T.G.t)
    (hj :
      ¬
        (T.F.idx.row ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.row j ∧
         T.F.idx.col ⟨j.val, lt_of_lt_of_le j.isLt hsize⟩ ≤ T.G.idx.col j)) :
    Nonempty (SwanRawLaplaceReduction k T) := by
  rcases swan_corollary2_7_component_finite_raw_identity
      k T hp hsize j hj with
    ⟨ι, inst, coeff, term, hdecr, hpoly⟩
  exact swanRawLaplaceReduction_of_finite_identity
    k (T := T) inst coeff term hdecr hpoly

theorem swan_corollary2_7_raw_bad_reduction_of_witness
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (w : SwanRawLaplaceProductTerm.BadWitness T) :
    Nonempty (SwanRawLaplaceReduction k T) := by
  cases w with
  | size hsize =>
      exact swan_corollary2_7_raw_bad_reduction_size k T hp hsize
  | component hsize j hj =>
      exact swan_corollary2_7_raw_bad_reduction_component k T hp hsize j hj

theorem swan_corollary2_7_raw_bad_reduction
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (T : SwanRawLaplaceProductTerm I J)
    (hp : 0 < p)
    (hbad : ¬ T.IsGood) :
    Nonempty (SwanRawLaplaceReduction k T) := by
  exact swan_corollary2_7_raw_bad_reduction_of_witness
    k T hp (T.badWitness hbad)

/-- Swan Corollary 2.8 in the form needed for induction: every raw Laplace
product expands into good products. -/
theorem swan_corollary2_8_raw_good_expansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hp : 0 < p)
    (T : SwanRawLaplaceProductTerm I J) :
    Nonempty (SwanRawGoodExpansion k T) := by
  classical
  let C : SwanRawLaplaceProductTerm I J → Prop :=
    fun T => Nonempty (SwanRawGoodExpansion k T)
  change C T
  refine (SwanRawLaplaceProductTerm.LT_wellFounded
    (I := I) (J := J)).induction T ?_
  intro T ih
  by_cases hgood : T.IsGood
  · exact swan_raw_good_expansion_of_good k T hgood
  · rcases swan_corollary2_7_raw_bad_reduction k T hp hgood with ⟨R⟩
    let E : ∀ x : R.ι, SwanRawGoodExpansion k (R.term x) :=
      fun x => Classical.choice (ih (R.term x) (R.term_decrease x))
    exact ⟨R.bindGoodExpansion E⟩

/-- Swan Corollary 2.8: iterating Corollary 2.7 terminates and rewrites a
Laplace product as a finite sum of good products. -/
theorem swan_corollary2_8_laplace_product_good_expansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (_hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    Nonempty (SwanLaplaceProductExpansion k I J) := by
  rcases swan_corollary2_8_raw_good_expansion
      k hp (SwanRawLaplaceProductTerm.initial I J) with ⟨E⟩
  exact ⟨E.toInitialExpansion⟩

namespace SwanLaplaceProductExpansion

lemma poly_eq'
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J) :
    letI := E.instFintype
    genericMinor k I * genericMinor k J =
      ∑ x : E.ι,
        MvPolynomial.C (E.coeff x) *
          MinorWord.toPolynomial k
            (SwanLaplaceProductTerm.toWord (E.term x)) := by
  letI := E.instFintype
  exact E.poly_eq

lemma term_pairwisePairLE
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J)
    (x : E.ι) :
    MinorWord.PairwisePairLE (E.term x).toWord :=
  (E.term x).pairwisePairLE_toWord

lemma term_degree
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J)
    (x : E.ι) :
    MinorWord.degree (E.term x).toWord = p + q :=
  (E.term x).degree_toWord

lemma term_length_nondec
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J)
    (x : E.ι) :
    p ≤ MinorWord.length (E.term x).toWord :=
  (E.term x).length_nondec_toWord

/-- Upgrade a Laplace-product expansion to the local Swan two-minor expansion
once Swan Lemma 4.3 has supplied strict first-factor decrease for every
supported term. -/
def toSwanTwoMinorExpansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J)
    (hstrict : ∀ x : E.ι, MinorIndex.PairLT (E.term x).F.idx I) :
    SwanTwoMinorExpansion k I J where
  ι := E.ι
  instFintype := E.instFintype
  coeff := E.coeff
  term := fun x => (E.term x).toSwanTwoMinorTerm (hstrict x)
  poly_eq := by
    letI := E.instFintype
    simpa using E.poly_eq

end SwanLaplaceProductExpansion

lemma swan_two_minor_finite_sum_of_laplace_expansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (E : SwanLaplaceProductExpansion k I J)
    (hstrict : ∀ x : E.ι, MinorIndex.PairLT (E.term x).F.idx I) :
    ∃ (ι : Type) (inst : Fintype ι)
        (coeff : ι → k) (term : ι → SwanTwoMinorTerm I J),
      letI := inst
      genericMinor k I * genericMinor k J =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord (term x)) := by
  let E' := SwanLaplaceProductExpansion.toSwanTwoMinorExpansion k E hstrict
  exact ⟨E'.ι, E'.instFintype, E'.coeff, E'.term, E'.poly_eq⟩

lemma swan_two_minor_finite_sum_of_reverse_pairLE
    {m n p q : ℕ}
    (k : Type*) [Field k]
    {I : MinorIndex m n p} {J : MinorIndex m n q}
    (hJI : MinorIndex.PairLE J I) (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ (ι : Type) (inst : Fintype ι)
        (coeff : ι → k) (term : ι → SwanTwoMinorTerm I J),
      letI := inst
      genericMinor k I * genericMinor k J =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord (term x)) := by
  classical
  let F : MinorFactor m n := { t := q, idx := J }
  let G : MinorFactor m n := { t := p, idx := I }
  have hfirst : MinorIndex.PairLT F.idx I :=
    MinorIndex.PairLT.of_pairLE_not_symm hJI hnot
  let T : SwanTwoMinorTerm I J :=
    { F := F
      G := G
      pairLE := hJI
      firstLT := hfirst
      row_content := by
        simp [F, G, MinorFactor.rowContent, add_comm]
      col_content := by
        simp [F, G, MinorFactor.colContent, add_comm] }
  refine ⟨PUnit, inferInstance, (fun _ => (1 : k)), (fun _ => T), ?_⟩
  simp [T, SwanTwoMinorTerm.toWord, F, G, MinorFactor.toPolynomial, mul_comm]

/-- Swan Theorem 3.1: the Laplace-product straightening expansion into good
two-minor products.

In this local encoding, "good" means that each output term is a
`SwanLaplaceProductTerm`: the two produced factors are ordered, the first
factor is weakly improved relative to the original first factor, and row/column
content is preserved.  No strict first-factor decrease is asserted here; that
is Swan Lemma 4.3 below. -/
theorem swan_theorem3_1_laplace_product_expansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q) :
    Nonempty (SwanLaplaceProductExpansion k I J) := by
  exact swan_corollary2_8_laplace_product_good_expansion
    k hp hq I J

/-- Swan Lemma 4.3: for a nonstandard incomparable local pair, every good
product occurring in the Laplace-product expansion has first factor strictly
smaller than the original first factor. -/
theorem swan_lemma4_3_first_factor_strict
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hIJ : ¬ MinorIndex.PairLE I J)
    (_hJI : ¬ MinorIndex.PairLE J I)
    (E : SwanLaplaceProductExpansion k I J)
    (x : E.ι) :
    MinorIndex.PairLT (E.term x).F.idx I := by
  classical
  let T : SwanLaplaceProductTerm I J := E.term x
  apply T.firstLT_of_not_original_le_first
  intro hIF
  have hF_eq :
      T.F = ({ t := p, idx := I } : MinorFactor m n) :=
    MinorFactor.eq_of_pairLE_pairLE T.firstLE hIF
  have hrow_sum :
      MinorFactor.rowContent T.F + MinorFactor.rowContent T.G =
        MinorIndex.rowContent I + MinorIndex.rowContent J := by
    simpa [SwanLaplaceProductTerm.toWord] using T.row_content
  have hcol_sum :
      MinorFactor.colContent T.F + MinorFactor.colContent T.G =
        MinorIndex.colContent I + MinorIndex.colContent J := by
    simpa [SwanLaplaceProductTerm.toWord] using T.col_content
  have hG_row :
      MinorFactor.rowContent T.G =
        MinorFactor.rowContent ({ t := q, idx := J } : MinorFactor m n) := by
    rw [hF_eq] at hrow_sum
    simpa [MinorFactor.rowContent] using
      (add_left_cancel hrow_sum)
  have hG_col :
      MinorFactor.colContent T.G =
        MinorFactor.colContent ({ t := q, idx := J } : MinorFactor m n) := by
    rw [hF_eq] at hcol_sum
    simpa [MinorFactor.colContent] using
      (add_left_cancel hcol_sum)
  have hG_eq :
      T.G = ({ t := q, idx := J } : MinorFactor m n) :=
    MinorFactor.eq_of_rowContent_eq_colContent hG_row hG_col
  have hIJ' : MinorIndex.PairLE I J := by
    have hpair := T.pairLE
    rw [hF_eq, hG_eq] at hpair
    simpa using hpair
  exact hIJ hIJ'

/-- Swan's square Laplace-product straightening theorem, in the finite-sum
form used in the proof of Theorem 4.1.

This is the formal target corresponding to Swan Theorem 3.1.  The auxiliary
square matrix and the "good" replacement data are hidden in the output
`SwanTwoMinorTerm` after transport through the row/column maps of Theorem 4.1;
the next lemma isolates that transport step. -/
theorem swan_square_laplace_product_straightening
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ (ι : Type) (inst : Fintype ι)
        (coeff : ι → k) (term : ι → SwanTwoMinorTerm I J),
      letI := inst
      genericMinor k I * genericMinor k J =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord (term x)) := by
  classical
  by_cases hJI : MinorIndex.PairLE J I
  · exact swan_two_minor_finite_sum_of_reverse_pairLE
      k (I := I) (J := J) hJI hnot
  · -- The genuinely Hodge-theoretic branch: neither adjacent minor is below
    -- the other.  This is where Swan Theorem 3.1 supplies a Laplace-product
    -- finite expansion and Swan Lemma 4.3 upgrades weak first-factor
    -- improvement to strict improvement.
    rcases swan_theorem3_1_laplace_product_expansion
        k hp hq I J with ⟨E⟩
    exact swan_two_minor_finite_sum_of_laplace_expansion k E
      (fun x => swan_lemma4_3_first_factor_strict
        k I J hnot hJI E x)

/-- Swan Theorem 4.1 in the current `MinorIndex` encoding.

The square Laplace-product straightening theorem above has already been stated in
the `MinorIndex m n` setting, so this bridge is now just the public theorem-4.1
interface used by the local straightening argument. -/
theorem swan_rectangular_lift_from_square_laplace
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ (ι : Type) (inst : Fintype ι)
        (coeff : ι → k) (term : ι → SwanTwoMinorTerm I J),
      letI := inst
      genericMinor k I * genericMinor k J =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord (term x)) := by
  exact swan_square_laplace_product_straightening k hp hq I J hnot

/-- Swan Theorem 4.1 in the unbundled finite-sum form.

This is the determinant/Hodge part of the local straightening argument.  It is
kept unbundled so the downstream packaging theorem
`exists_swan_two_minor_expansion` has a small proof. -/
theorem swan_theorem4_1_finite_sum
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ (ι : Type) (inst : Fintype ι)
        (coeff : ι → k) (term : ι → SwanTwoMinorTerm I J),
      letI := inst
      genericMinor k I * genericMinor k J =
        ∑ x : ι,
          MvPolynomial.C (coeff x) *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord (term x)) := by
  exact swan_rectangular_lift_from_square_laplace k hp hq I J hnot

/-- Determinant-theoretic Swan Theorem 4.1 input in finite-expansion form. -/
theorem exists_swan_two_minor_expansion
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    Nonempty (SwanTwoMinorExpansion k I J) := by
  classical
  rcases swan_theorem4_1_finite_sum k
      hp hq I J hnot with ⟨ι, inst, coeff, term, hpoly⟩
  letI := inst
  exact ⟨
    { ι := ι
      instFintype := inst
      coeff := coeff
      term := term
      poly_eq := by
        simpa using hpoly }⟩

/-- Raw local Swan two-minor straightening relation.

Swan Theorem 4.1 supplies a finite linear combination of replacement pairs
satisfying the support data recorded in `SwanTwoMinorTerm`. -/
theorem swan_two_minor_straightening_relation_raw
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ c : SwanTwoMinorTerm I J →₀ k,
      genericMinor k I * genericMinor k J =
        c.sum (fun T a =>
          MvPolynomial.C a *
            MinorWord.toPolynomial k
              (SwanTwoMinorTerm.toWord T)) := by
  classical
  rcases exists_swan_two_minor_expansion k
      hp hq I J hnot with ⟨E⟩
  let cι : E.ι →₀ k := Finsupp.equivFunOnFinite.symm E.coeff
  let c : SwanTwoMinorTerm I J →₀ k := Finsupp.mapDomain E.term cι
  refine ⟨c, ?_⟩
  rw [E.poly_eq]
  change
    (∑ x : E.ι,
      MvPolynomial.C (E.coeff x) *
        MinorWord.toPolynomial k
          (SwanTwoMinorTerm.toWord (E.term x))) =
    c.sum (fun T a =>
      MvPolynomial.C a *
        MinorWord.toPolynomial k (SwanTwoMinorTerm.toWord T))
  change
    (∑ x : E.ι,
      MvPolynomial.C (E.coeff x) *
        MinorWord.toPolynomial k
          (SwanTwoMinorTerm.toWord (E.term x))) =
    (Finsupp.mapDomain E.term cι).sum (fun T a =>
      MvPolynomial.C a *
        MinorWord.toPolynomial k (SwanTwoMinorTerm.toWord T))
  rw [Finsupp.sum_mapDomain_index]
  · simp [cι, Finsupp.sum_fintype]
  · intro T
    simp
  · intro T a b
    simp [add_mul, MvPolynomial.C_add]

/-- Local Swan two-minor straightening relation needed for the nonstandard
branch of `straightening_law_exists_filtered`.

The output is a finite `MinorWord` expansion rather than a `YoungBitableau`
expansion because Swan's local relation may contain a unit factor
`(∅|∅) = 1`; `YoungBitableau.consMinor` only accepts positive-size factors.

The support data is exactly what is needed after embedding the rewritten local
word back into a larger bitableau product:

* polynomial equality for the two-minor product;
* every produced local word is explicitly a two-factor word;
* the two factors are standardly ordered;
* the new first factor is strictly smaller than the original first factor in
  Swan's minor-pair order;
* row and column content are preserved.

Degree preservation, local standardness as `MinorWord.PairwisePairLE`, and
nondecrease of the first-factor length are derived below from this primitive
support description. -/
theorem swan_two_minor_straightening_relation
    {m n p q : ℕ}
    (k : Type*) [Field k]
    (hp : 0 < p) (hq : 0 < q)
    (I : MinorIndex m n p) (J : MinorIndex m n q)
    (hnot : ¬ MinorIndex.PairLE I J) :
    ∃ c : MinorWord m n →₀ k,
      genericMinor k I * genericMinor k J =
        c.sum (fun W a =>
          MvPolynomial.C a * MinorWord.toPolynomial k W)
      ∧
      (∀ W, c W ≠ 0 →
        ∃ F G : MinorFactor m n,
          W.factors = [F, G]
          ∧ MinorIndex.PairLE F.idx G.idx
          ∧ MinorIndex.PairLT F.idx I
          ∧ MinorWord.rowContent W =
              MinorIndex.rowContent I + MinorIndex.rowContent J
          ∧ MinorWord.colContent W =
              MinorIndex.colContent I + MinorIndex.colContent J) := by
  classical
  rcases swan_two_minor_straightening_relation_raw k
      hp hq I J hnot with ⟨cRaw, hpolyRaw⟩
  let emb : SwanTwoMinorTerm I J → MinorWord m n :=
    fun T => SwanTwoMinorTerm.toWord T
  let c : MinorWord m n →₀ k := Finsupp.mapDomain emb cRaw
  refine ⟨c, ?_, ?_⟩
  · rw [hpolyRaw]
    change
      cRaw.sum (fun T a =>
          MvPolynomial.C a * MinorWord.toPolynomial k (emb T)) =
        (Finsupp.mapDomain emb cRaw).sum (fun W a =>
          MvPolynomial.C a * MinorWord.toPolynomial k W)
    rw [Finsupp.sum_mapDomain_index]
    · simp
    · intro W a b
      simp [add_mul]
  · intro W hW
    have hWmem : W ∈ c.support := by
      simpa [Finsupp.mem_support_iff] using hW
    have hWimage : W ∈ Finset.image emb cRaw.support := by
      exact Finsupp.mapDomain_support hWmem
    rcases Finset.mem_image.mp hWimage with ⟨T, hTmem, hTW⟩
    have hTW' : W = SwanTwoMinorTerm.toWord T := hTW.symm
    rw [hTW']
    exact SwanTwoMinorTerm.support_data T

lemma swan_two_minor_support_pairwisePairLE
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n}
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    MinorWord.PairwisePairLE W := by
  rcases hW with ⟨F, G, hfac, hFG, _hFI, _hrow, _hcol⟩
  rw [MinorWord.PairwisePairLE, hfac]
  simp [hFG]

lemma swan_two_minor_support_length_nondec
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n}
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    p ≤ MinorWord.length W := by
  rcases hW with ⟨F, G, hfac, _hFG, hFI, _hrow, _hcol⟩
  have hpF : p ≤ F.t := MinorIndex.PairLE.size_le hFI.pairLE
  rw [MinorWord.length, hfac]
  simp only [MinorFactor.length, List.foldr_cons, List.foldr_nil, zero_le, sup_of_le_left,
    le_sup_iff]
  exact Or.inl hpF

lemma swan_two_minor_support_degree
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n}
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    MinorWord.degree W = p + q := by
  classical
  rcases hW with ⟨F, G, _hfac, _hFG, _hFI, hrow, _hcol⟩
  calc
    MinorWord.degree W
        = ∑ i : Fin m, MinorWord.rowContent W i := by
          exact (MinorWord.rowContent_total W).symm
    _ = ∑ i : Fin m, (MinorIndex.rowContent I + MinorIndex.rowContent J) i := by
          rw [hrow]
    _ = (∑ i : Fin m, MinorIndex.rowContent I i) +
          (∑ i : Fin m, MinorIndex.rowContent J i) := by
          simp [Pi.add_apply, Finset.sum_add_distrib]
    _ = p + q := by
          rw [MinorIndex.rowContent_total I, MinorIndex.rowContent_total J]

lemma swan_two_minor_support_append_head_lt
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n} (rest : List (MinorFactor m n))
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    ∃ F G : MinorFactor m n,
      (⟨W.factors ++ rest⟩ : MinorWord m n).factors = F :: G :: rest ∧
      MinorIndex.PairLE F.idx G.idx ∧
      MinorIndex.PairLT F.idx I := by
  rcases hW with ⟨F, G, hfac, hFG, hFI, _hrow, _hcol⟩
  refine ⟨F, G, ?_, hFG, hFI⟩
  simp [hfac]

lemma swan_two_minor_support_append_degree
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n} (rest : List (MinorFactor m n))
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    MinorWord.degree (⟨W.factors ++ rest⟩ : MinorWord m n) =
      p + q + MinorWord.degree ⟨rest⟩ := by
  rw [MinorWord.degree_append]
  rw [swan_two_minor_support_degree hW]

lemma swan_two_minor_support_append_degree_factor
    {m n : ℕ} (H G : MinorFactor m n)
    {W : MinorWord m n} (rest : List (MinorFactor m n))
    (hW :
      ∃ F G' : MinorFactor m n,
        W.factors = [F, G']
        ∧ MinorIndex.PairLE F.idx G'.idx
        ∧ MinorIndex.PairLT F.idx H.idx
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent H.idx + MinorIndex.rowContent G.idx
        ∧ MinorWord.colContent W =
            MinorIndex.colContent H.idx + MinorIndex.colContent G.idx) :
    MinorWord.degree (⟨W.factors ++ rest⟩ : MinorWord m n) =
      H.t + MinorWord.degree ⟨G :: rest⟩ := by
  have hdeg := swan_two_minor_support_append_degree
    (I := H.idx) (J := G.idx) (W := W) rest hW
  simpa [MinorFactor.degree, Nat.add_assoc] using hdeg

lemma swan_two_minor_support_append_length_nondec
    {m n p q : ℕ} {I : MinorIndex m n p} {J : MinorIndex m n q}
    {W : MinorWord m n} (rest : List (MinorFactor m n))
    (hW :
      ∃ F G : MinorFactor m n,
        W.factors = [F, G]
        ∧ MinorIndex.PairLE F.idx G.idx
        ∧ MinorIndex.PairLT F.idx I
        ∧ MinorWord.rowContent W =
            MinorIndex.rowContent I + MinorIndex.rowContent J
        ∧ MinorWord.colContent W =
            MinorIndex.colContent I + MinorIndex.colContent J) :
    p ≤ MinorWord.length (⟨W.factors ++ rest⟩ : MinorWord m n) := by
  have hlocal : p ≤ MinorWord.length W :=
    swan_two_minor_support_length_nondec hW
  rw [MinorWord.length_append]
  exact le_trans hlocal (le_max_left _ _)

lemma minorWord_straightening_exists_degree_of_pairwise
    {m n : ℕ}
    (k : Type*) [Field k]
    (W : MinorWord m n)
    (hW : MinorWord.PairwisePairLE W) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k W =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = MinorWord.degree W) := by
  classical
  let S : StandardMinorWord m n := ⟨W, hW⟩
  refine ⟨Finsupp.single S (1 : k), ?_, ?_⟩
  · simp [S]
  · intro U hU
    have hU_eq : U = S := by
      by_contra hne
      have hzero : (Finsupp.single S (1 : k)) U = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hU hzero
    simp [hU_eq, S]

lemma minorWord_straightening_exists_degree_of_pairwise_factorCount
    {m n : ℕ}
    (k : Type*) [Field k]
    (W : MinorWord m n)
    (hW : MinorWord.PairwisePairLE W) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k W =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = MinorWord.degree W)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.factorCount U.1 ≤ MinorWord.factorCount W) := by
  classical
  let S : StandardMinorWord m n := ⟨W, hW⟩
  refine ⟨Finsupp.single S (1 : k), ?_, ?_, ?_⟩
  · simp [S]
  · intro U hU
    have hU_eq : U = S := by
      by_contra hne
      have hzero : (Finsupp.single S (1 : k)) U = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hU hzero
    simp [hU_eq, S]
  · intro U hU
    have hU_eq : U = S := by
      by_contra hne
      have hzero : (Finsupp.single S (1 : k)) U = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hU hzero
    simp [hU_eq, S]

lemma minorWord_finsupp_sum_append_right
    {m n : ℕ}
    (k : Type*) [Field k]
    (c : MinorWord m n →₀ k)
    (rest : List (MinorFactor m n)) :
    (c.sum fun W a =>
        MvPolynomial.C a *
          MinorWord.toPolynomial k ⟨W.factors ++ rest⟩) =
      (Finsupp.mapDomain
          (fun W : MinorWord m n => (⟨W.factors ++ rest⟩ : MinorWord m n))
          c).sum fun W a =>
        MvPolynomial.C a * MinorWord.toPolynomial k W := by
  classical
  rw [Finsupp.sum_mapDomain_index]
  · simp
  · intro W a b
    simp [add_mul, MvPolynomial.C_add]

lemma minorWord_finsupp_sum_mul_tail
    {m n : ℕ}
    (k : Type*) [Field k]
    (c : MinorWord m n →₀ k)
    (rest : List (MinorFactor m n)) :
    (c.sum fun W a =>
        MvPolynomial.C a * MinorWord.toPolynomial k W) *
      MinorWord.toPolynomial k ⟨rest⟩ =
      (Finsupp.mapDomain
          (fun W : MinorWord m n => (⟨W.factors ++ rest⟩ : MinorWord m n))
          c).sum fun W a =>
        MvPolynomial.C a * MinorWord.toPolynomial k W := by
  classical
  calc
    (c.sum fun W a =>
        MvPolynomial.C a * MinorWord.toPolynomial k W) *
      MinorWord.toPolynomial k ⟨rest⟩
        =
      c.sum fun W a =>
        MvPolynomial.C a *
          MinorWord.toPolynomial k ⟨W.factors ++ rest⟩ := by
          rw [Finsupp.sum, Finset.sum_mul, Finsupp.sum]
          apply Finset.sum_congr rfl
          intro W _hW
          rw [MinorWord.toPolynomial_append]
          ring
    _ =
      (Finsupp.mapDomain
          (fun W : MinorWord m n => (⟨W.factors ++ rest⟩ : MinorWord m n))
          c).sum fun W a =>
        MvPolynomial.C a * MinorWord.toPolynomial k W :=
          minorWord_finsupp_sum_append_right k c rest

lemma minorWord_head_insert_after_tail_straightening
    {m n : ℕ} (k : Type*) [Field k]
    (F : MinorFactor m n) (tail : MinorWord m n)
    (cTail : StandardMinorWord m n →₀ k)
    (hTail_poly :
      MinorWord.toPolynomial k tail =
        cTail.sum (fun S a =>
          MvPolynomial.C a * MinorWord.toPolynomial k S.1))
    (hTail_degree :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.degree S.1 = MinorWord.degree tail)
    (insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k)
    (hinsert_poly :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ =
          (insertCoeff S).sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1))
    (hinsert_degree :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          MinorWord.degree U.1 = F.t + MinorWord.degree S.1) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 =
          MinorWord.degree (⟨F :: tail.factors⟩ : MinorWord m n)) := by
  classical
  let c : StandardMinorWord m n →₀ k :=
    finsuppScalarBind cTail insertCoeff
  refine ⟨c, ?_, ?_⟩
  · have hhead_tail :
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
      calc
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩
            =
          MinorFactor.toPolynomial k F *
            MinorWord.toPolynomial k tail := by
            simp
        _ =
          MinorFactor.toPolynomial k F *
            (cTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k S.1) := by
            rw [hTail_poly]
        _ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
            rw [Finsupp.mul_sum]
            apply Finsupp.sum_congr
            intro S a
            simp [mul_assoc, mul_comm]
    rw [hhead_tail]
    have hdist :
        (cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩) =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              (insertCoeff S).sum (fun U b =>
                MvPolynomial.C b * MinorWord.toPolynomial k U.1) := by
      apply Finsupp.sum_congr
      intro S a
      by_cases hS : cTail S = 0
      · simp [hS]
      · rw [hinsert_poly S hS]
    rw [hdist]
    rw [← finsuppScalarBind_polynomial_sum
      (c := cTail) (d := insertCoeff)
      (v := fun U : StandardMinorWord m n =>
        MinorWord.toPolynomial k U.1)]
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cTail insertCoeff hU with ⟨S, hS, hSU⟩
    have hUdeg := hinsert_degree S U hS hSU
    have hSdeg := hTail_degree S hS
    rw [hUdeg, hSdeg]
    simp [MinorFactor.degree]

lemma minorWord_head_insert_after_tail_straightening_filtered
    {m n : ℕ} (k : Type*) [Field k]
    (F : MinorFactor m n) (tail : MinorWord m n)
    (cTail : StandardMinorWord m n →₀ k)
    (hTail_poly :
      MinorWord.toPolynomial k tail =
        cTail.sum (fun S a =>
          MvPolynomial.C a * MinorWord.toPolynomial k S.1))
    (hTail_degree :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.degree S.1 = MinorWord.degree tail)
    (insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k)
    (hinsert_poly :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ =
          (insertCoeff S).sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1))
    (hinsert_degree :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          MinorWord.degree U.1 = F.t + MinorWord.degree S.1)
    (hinsert_length :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          F.t ≤ MinorWord.length U.1) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 =
          MinorWord.degree (⟨F :: tail.factors⟩ : MinorWord m n))
      ∧
      (∀ U, c U ≠ 0 → F.t ≤ MinorWord.length U.1) := by
  classical
  let c : StandardMinorWord m n →₀ k :=
    finsuppScalarBind cTail insertCoeff
  refine ⟨c, ?_, ?_, ?_⟩
  · have hhead_tail :
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
      calc
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩
            =
          MinorFactor.toPolynomial k F *
            MinorWord.toPolynomial k tail := by
            simp
        _ =
          MinorFactor.toPolynomial k F *
            (cTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k S.1) := by
            rw [hTail_poly]
        _ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
            rw [Finsupp.mul_sum]
            apply Finsupp.sum_congr
            intro S a
            simp [mul_assoc, mul_comm]
    rw [hhead_tail]
    have hdist :
        (cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩) =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              (insertCoeff S).sum (fun U b =>
                MvPolynomial.C b * MinorWord.toPolynomial k U.1) := by
      apply Finsupp.sum_congr
      intro S a
      by_cases hS : cTail S = 0
      · simp [hS]
      · rw [hinsert_poly S hS]
    rw [hdist]
    rw [← finsuppScalarBind_polynomial_sum
      (c := cTail) (d := insertCoeff)
      (v := fun U : StandardMinorWord m n =>
        MinorWord.toPolynomial k U.1)]
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cTail insertCoeff hU with ⟨S, hS, hSU⟩
    have hUdeg := hinsert_degree S U hS hSU
    have hSdeg := hTail_degree S hS
    rw [hUdeg, hSdeg]
    simp [MinorFactor.degree]
  · exact finsuppScalarBind_support_property cTail insertCoeff
      (fun U => F.t ≤ MinorWord.length U.1)
      (by
        intro S U hS hSU
        exact hinsert_length S U hS hSU)

lemma minorWord_finsupp_bind_after_local_expansion
    {m n : ℕ} (k : Type*) [Field k]
    (cLocal : MinorWord m n →₀ k)
    (straighten : MinorWord m n → StandardMinorWord m n →₀ k)
    (hstraighten_poly :
      ∀ W : MinorWord m n, cLocal W ≠ 0 →
        MinorWord.toPolynomial k W =
          (straighten W).sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1))
    (hstraighten_degree :
      ∀ W : MinorWord m n, ∀ U : StandardMinorWord m n,
        cLocal W ≠ 0 → straighten W U ≠ 0 →
          MinorWord.degree U.1 = MinorWord.degree W) :
    ∃ c : StandardMinorWord m n →₀ k,
      cLocal.sum (fun W a =>
          MvPolynomial.C a * MinorWord.toPolynomial k W) =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        ∃ W : MinorWord m n,
          cLocal W ≠ 0 ∧ straighten W U ≠ 0 ∧
          MinorWord.degree U.1 = MinorWord.degree W) := by
  classical
  let c : StandardMinorWord m n →₀ k :=
    finsuppScalarBind cLocal straighten
  refine ⟨c, ?_, ?_⟩
  · have hdist :
        cLocal.sum (fun W a =>
            MvPolynomial.C a * MinorWord.toPolynomial k W) =
          cLocal.sum (fun W a =>
            MvPolynomial.C a *
              (straighten W).sum (fun U b =>
                MvPolynomial.C b * MinorWord.toPolynomial k U.1)) := by
      apply Finsupp.sum_congr
      intro W a
      by_cases hW : cLocal W = 0
      · simp [hW]
      · rw [hstraighten_poly W hW]
    rw [hdist]
    rw [← finsuppScalarBind_polynomial_sum
      (c := cLocal) (d := straighten)
      (v := fun U : StandardMinorWord m n =>
        MinorWord.toPolynomial k U.1)]
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cLocal straighten hU with ⟨W, hW, hWU⟩
    exact ⟨W, hW, hWU, hstraighten_degree W U hW hWU⟩

lemma minorWord_head_insert_after_tail_straightening_factorCount
    {m n : ℕ} (k : Type*) [Field k]
    (F : MinorFactor m n) (tail : MinorWord m n)
    (cTail : StandardMinorWord m n →₀ k)
    (hTail_poly :
      MinorWord.toPolynomial k tail =
        cTail.sum (fun S a =>
          MvPolynomial.C a * MinorWord.toPolynomial k S.1))
    (hTail_degree :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.degree S.1 = MinorWord.degree tail)
    (hTail_factorCount :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.factorCount S.1 ≤ MinorWord.factorCount tail)
    (insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k)
    (hinsert_poly :
      ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
        MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ =
          (insertCoeff S).sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1))
    (hinsert_degree :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          MinorWord.degree U.1 = F.t + MinorWord.degree S.1)
    (hinsert_length :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          F.t ≤ MinorWord.length U.1)
    (hinsert_factorCount :
      ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
        insertCoeff S U ≠ 0 →
          MinorWord.factorCount U.1 ≤ MinorWord.factorCount S.1 + 1) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 =
          MinorWord.degree (⟨F :: tail.factors⟩ : MinorWord m n))
      ∧
      (∀ U, c U ≠ 0 → F.t ≤ MinorWord.length U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.factorCount U.1 ≤
          MinorWord.factorCount (⟨F :: tail.factors⟩ : MinorWord m n)) := by
  classical
  let c : StandardMinorWord m n →₀ k :=
    finsuppScalarBind cTail insertCoeff
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · have hhead_tail :
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
      calc
        MinorWord.toPolynomial k ⟨F :: tail.factors⟩
            =
          MinorFactor.toPolynomial k F *
            MinorWord.toPolynomial k tail := by
            simp
        _ =
          MinorFactor.toPolynomial k F *
            (cTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k S.1) := by
            rw [hTail_poly]
        _ =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ := by
            rw [Finsupp.mul_sum]
            apply Finsupp.sum_congr
            intro S a
            simp [mul_assoc, mul_comm]
    rw [hhead_tail]
    have hdist :
        (cTail.sum fun S a =>
            MvPolynomial.C a *
              MinorWord.toPolynomial k ⟨F :: S.1.factors⟩) =
          cTail.sum fun S a =>
            MvPolynomial.C a *
              (insertCoeff S).sum (fun U b =>
                MvPolynomial.C b * MinorWord.toPolynomial k U.1) := by
      apply Finsupp.sum_congr
      intro S a
      by_cases hS : cTail S = 0
      · simp [hS]
      · rw [hinsert_poly S hS]
    rw [hdist]
    rw [← finsuppScalarBind_polynomial_sum
      (c := cTail) (d := insertCoeff)
      (v := fun U : StandardMinorWord m n =>
        MinorWord.toPolynomial k U.1)]
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cTail insertCoeff hU with ⟨S, hS, hSU⟩
    have hUdeg := hinsert_degree S U hS hSU
    have hSdeg := hTail_degree S hS
    rw [hUdeg, hSdeg]
    simp [MinorFactor.degree]
  · exact finsuppScalarBind_support_property cTail insertCoeff
      (fun U => F.t ≤ MinorWord.length U.1)
      (by
        intro S U hS hSU
        exact hinsert_length S U hS hSU)
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cTail insertCoeff hU with ⟨S, hS, hSU⟩
    have hUS := hinsert_factorCount S U hS hSU
    have hStail := hTail_factorCount S hS
    cases tail with
    | mk factors =>
        simp [MinorWord.factorCount] at hUS hStail ⊢
        omega

lemma minorWord_finsupp_bind_after_local_expansion_factorCount
    {m n : ℕ} (k : Type*) [Field k]
    (cLocal : MinorWord m n →₀ k)
    (straighten : MinorWord m n → StandardMinorWord m n →₀ k)
    (hstraighten_poly :
      ∀ W : MinorWord m n, cLocal W ≠ 0 →
        MinorWord.toPolynomial k W =
          (straighten W).sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1))
    (hstraighten_degree :
      ∀ W : MinorWord m n, ∀ U : StandardMinorWord m n,
        cLocal W ≠ 0 → straighten W U ≠ 0 →
          MinorWord.degree U.1 = MinorWord.degree W)
    (hstraighten_factorCount :
      ∀ W : MinorWord m n, ∀ U : StandardMinorWord m n,
        cLocal W ≠ 0 → straighten W U ≠ 0 →
          MinorWord.factorCount U.1 ≤ MinorWord.factorCount W) :
    ∃ c : StandardMinorWord m n →₀ k,
      cLocal.sum (fun W a =>
          MvPolynomial.C a * MinorWord.toPolynomial k W) =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        ∃ W : MinorWord m n,
          cLocal W ≠ 0 ∧ straighten W U ≠ 0 ∧
          MinorWord.degree U.1 = MinorWord.degree W ∧
          MinorWord.factorCount U.1 ≤ MinorWord.factorCount W) := by
  classical
  let c : StandardMinorWord m n →₀ k :=
    finsuppScalarBind cLocal straighten
  refine ⟨c, ?_, ?_⟩
  · have hdist :
        cLocal.sum (fun W a =>
            MvPolynomial.C a * MinorWord.toPolynomial k W) =
          cLocal.sum (fun W a =>
            MvPolynomial.C a *
              (straighten W).sum (fun U b =>
                MvPolynomial.C b * MinorWord.toPolynomial k U.1)) := by
      apply Finsupp.sum_congr
      intro W a
      by_cases hW : cLocal W = 0
      · simp [hW]
      · rw [hstraighten_poly W hW]
    rw [hdist]
    rw [← finsuppScalarBind_polynomial_sum
      (c := cLocal) (d := straighten)
      (v := fun U : StandardMinorWord m n =>
        MinorWord.toPolynomial k U.1)]
  · intro U hU
    rcases finsuppScalarBind_apply_ne_zero_exists
        cLocal straighten hU with ⟨W, hW, hWU⟩
    exact ⟨W, hW, hWU,
      hstraighten_degree W U hW hWU,
      hstraighten_factorCount W U hW hWU⟩

lemma minorFactor_mul_standardMinorWord_exists_filtered_of_ordered
    {m n : ℕ}
    (k : Type*) [Field k]
    (H : MinorFactor m n)
    (S : StandardMinorWord m n)
    (hHS : ∀ G ∈ S.1.factors, MinorIndex.PairLE H.idx G.idx) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = H.t + MinorWord.degree S.1)
      ∧
      (∀ U, c U ≠ 0 →
        H.t ≤ MinorWord.length U.1) := by
  classical
  let U : StandardMinorWord m n :=
    ⟨⟨H :: S.1.factors⟩,
      (MinorWord.PairwisePairLE_cons_iff H S.1.factors).mpr ⟨hHS, S.2⟩⟩
  refine ⟨Finsupp.single U (1 : k), ?_, ?_, ?_⟩
  · simp [U]
  · intro V hV
    have hV_eq : V = U := by
      by_contra hne
      have hzero : (Finsupp.single U (1 : k)) V = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hV hzero
    subst V
    simp [U, MinorFactor.degree]
  · intro V hV
    have hV_eq : V = U := by
      by_contra hne
      have hzero : (Finsupp.single U (1 : k)) V = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hV hzero
    subst V
    simp [U, MinorFactor.length]

lemma minorFactor_mul_standardMinorWord_exists_filtered_of_ordered_factorCount
    {m n : ℕ}
    (k : Type*) [Field k]
    (H : MinorFactor m n)
    (S : StandardMinorWord m n)
    (hHS : ∀ G ∈ S.1.factors, MinorIndex.PairLE H.idx G.idx) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = H.t + MinorWord.degree S.1)
      ∧
      (∀ U, c U ≠ 0 →
        H.t ≤ MinorWord.length U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.factorCount U.1 ≤ MinorWord.factorCount S.1 + 1) := by
  classical
  let U : StandardMinorWord m n :=
    ⟨⟨H :: S.1.factors⟩,
      (MinorWord.PairwisePairLE_cons_iff H S.1.factors).mpr ⟨hHS, S.2⟩⟩
  refine ⟨Finsupp.single U (1 : k), ?_, ?_, ?_, ?_⟩
  · simp [U]
  · intro V hV
    have hV_eq : V = U := by
      by_contra hne
      have hzero : (Finsupp.single U (1 : k)) V = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hV hzero
    subst V
    simp [U, MinorFactor.degree]
  · intro V hV
    have hV_eq : V = U := by
      by_contra hne
      have hzero : (Finsupp.single U (1 : k)) V = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hV hzero
    subst V
    simp [U, MinorFactor.length]
  · intro V hV
    have hV_eq : V = U := by
      by_contra hne
      have hzero : (Finsupp.single U (1 : k)) V = 0 := by
        rw [Finsupp.single_eq_of_ne hne]
      exact hV hzero
    subst V
    simp [U, MinorWord.factorCount]

lemma StandardMinorWord.exists_head_not_pairLE_of_not_forall_pairLE
    {m n : ℕ}
    (H : MinorFactor m n)
    (S : StandardMinorWord m n)
    (hnot : ¬ ∀ G ∈ S.1.factors, MinorIndex.PairLE H.idx G.idx) :
    ∃ G rest,
      S.1.factors = G :: rest ∧
      ¬ MinorIndex.PairLE H.idx G.idx ∧
      MinorWord.PairwisePairLE ⟨G :: rest⟩ := by
  classical
  cases hfac : S.1.factors with
  | nil =>
      exfalso
      apply hnot
      intro G hG
      simp [hfac] at hG
  | cons G rest =>
      refine ⟨G, rest, rfl, ?_, ?_⟩
      · intro hHG
        apply hnot
        intro K hK
        have hK' : K ∈ G :: rest := by
          simpa [hfac] using hK
        rcases List.mem_cons.mp hK' with rfl | hKrest
        · exact hHG
        · have hGK : MinorIndex.PairLE G.idx K.idx := by
            have hpair : MinorWord.PairwisePairLE ⟨G :: rest⟩ := by
              simpa [MinorWord.PairwisePairLE, hfac] using S.2
            exact (MinorWord.PairwisePairLE_cons_iff G rest).mp hpair |>.1 K hKrest
          exact MinorIndex.PairLE.trans hHG hGK
      · simpa [MinorWord.PairwisePairLE, hfac] using S.2

lemma minorFactor_insert_tail_measure_lt
    {m n : ℕ}
    {H G G' : MinorFactor m n}
    {S : StandardMinorWord m n} {rest : List (MinorFactor m n)}
    (hfac : S.1.factors = G :: rest) :
    Prod.Lex (fun x y : ℕ => x < y) MinorFactor.PairLT
      (MinorWord.factorCount (⟨rest⟩ : MinorWord m n) + 1, G')
      (MinorWord.factorCount S.1 + 1, H) := by
  apply Prod.Lex.left
  cases S with
  | mk W hpair =>
      cases W with
      | mk factors =>
          have hfac' : factors = G :: rest := hfac
          subst factors
          simp [MinorWord.factorCount]

lemma minorFactor_insert_head_measure_lt
    {m n : ℕ}
    {H F G G' : MinorFactor m n}
    {S S' : StandardMinorWord m n} {rest : List (MinorFactor m n)}
    (hfac : S.1.factors = G :: rest)
    (hcount :
      MinorWord.factorCount S'.1 ≤
        MinorWord.factorCount (⟨G' :: rest⟩ : MinorWord m n))
    (hFH : MinorIndex.PairLT F.idx H.idx) :
    Prod.Lex (fun x y : ℕ => x < y) MinorFactor.PairLT
      (MinorWord.factorCount S'.1 + 1, F)
      (MinorWord.factorCount S.1 + 1, H) := by
  have hle :
      MinorWord.factorCount S'.1 + 1 ≤
        MinorWord.factorCount S.1 + 1 := by
    cases S with
    | mk W hpair =>
        cases W with
        | mk factors =>
            have hfac' : factors = G :: rest := hfac
            subst factors
            simp [MinorWord.factorCount] at hcount ⊢
            omega
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right _ (by
      simpa [MinorFactor.PairLT] using hFH)

theorem minorFactor_mul_standardMinorWord_exists_filtered_strong
    {m n : ℕ}
    (k : Type*) [Field k]
    (H : MinorFactor m n) (hH : 0 < H.t)
    (S : StandardMinorWord m n) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = H.t + MinorWord.degree S.1)
      ∧
      (∀ U, c U ≠ 0 →
        H.t ≤ MinorWord.length U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.factorCount U.1 ≤ MinorWord.factorCount S.1 + 1) := by
  classical
  by_cases hHS : ∀ G ∈ S.1.factors, MinorIndex.PairLE H.idx G.idx
  · exact minorFactor_mul_standardMinorWord_exists_filtered_of_ordered_factorCount k H S hHS
  · rcases S.exists_head_not_pairLE_of_not_forall_pairLE H hHS with
      ⟨G, rest, hfac, hHG, hTail⟩
    have hRest : MinorWord.PairwisePairLE ⟨rest⟩ :=
      ((MinorWord.PairwisePairLE_cons_iff G rest).mp hTail).2
    let restStd : StandardMinorWord m n :=
      ⟨⟨rest⟩, hRest⟩
    have hGpos : 0 < G.t := by
      exact Nat.pos_of_ne_zero (by
        intro hzero
        apply hHG
        refine MinorIndex.PairLE.of_components ?_ ?_
        · simp [hzero]
        · intro j
          exact False.elim (Nat.not_lt_zero j.val (by
            simpa [hzero] using j.isLt)))
    rcases swan_two_minor_straightening_relation k
        hH hGpos H.idx G.idx hHG with
      ⟨cLocal, hLocal_poly, hLocal_support⟩
    let appendWord : MinorWord m n → MinorWord m n :=
      fun W => (⟨W.factors ++ rest⟩ : MinorWord m n)
    let cAppended : MinorWord m n →₀ k :=
      Finsupp.mapDomain appendWord cLocal
    have hLocal_tail_appended :
        MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
          cAppended.sum fun W a =>
            MvPolynomial.C a * MinorWord.toPolynomial k W := by
      have hLocal_tail :
          MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
            (cLocal.sum fun W a =>
                MvPolynomial.C a * MinorWord.toPolynomial k W) *
              MinorWord.toPolynomial k ⟨rest⟩ := by
        calc
          MinorWord.toPolynomial k ⟨H :: S.1.factors⟩
              =
            MinorFactor.toPolynomial k H *
              MinorFactor.toPolynomial k G *
                MinorWord.toPolynomial k ⟨rest⟩ := by
              rw [hfac]
              simp [mul_assoc]
          _ =
            (genericMinor k H.idx * genericMinor k G.idx) *
              MinorWord.toPolynomial k ⟨rest⟩ := by
              simp [MinorFactor.toPolynomial, mul_assoc]
          _ =
            (cLocal.sum fun W a =>
                MvPolynomial.C a * MinorWord.toPolynomial k W) *
              MinorWord.toPolynomial k ⟨rest⟩ := by
              rw [hLocal_poly]
      rw [hLocal_tail]
      simpa [cAppended, appendWord] using
        minorWord_finsupp_sum_mul_tail k cLocal rest
    have hAppended_degree :
        ∀ W : MinorWord m n, cAppended W ≠ 0 →
          MinorWord.degree W = H.t + MinorWord.degree ⟨G :: rest⟩ := by
      exact finsupp_mapDomain_support_property appendWord cLocal
        (fun W => MinorWord.degree W = H.t + MinorWord.degree ⟨G :: rest⟩)
        (by
          intro W hW
          exact swan_two_minor_support_append_degree_factor
            H G rest (hLocal_support W hW))
    have hAppended_length :
        ∀ W : MinorWord m n, cAppended W ≠ 0 →
          H.t ≤ MinorWord.length W := by
      exact finsupp_mapDomain_support_property appendWord cLocal
        (fun W => H.t ≤ MinorWord.length W)
        (by
          intro W hW
          exact swan_two_minor_support_append_length_nondec
            (I := H.idx) (J := G.idx) (W := W) rest
            (hLocal_support W hW))
    have hAppended_head_lt :
        ∀ W : MinorWord m n, cAppended W ≠ 0 →
          ∃ F G' : MinorFactor m n,
            W.factors = F :: G' :: rest ∧
            MinorIndex.PairLE F.idx G'.idx ∧
            MinorIndex.PairLT F.idx H.idx := by
      exact finsupp_mapDomain_support_property appendWord cLocal
        (fun W =>
          ∃ F G' : MinorFactor m n,
            W.factors = F :: G' :: rest ∧
            MinorIndex.PairLE F.idx G'.idx ∧
            MinorIndex.PairLT F.idx H.idx)
        (by
          intro W hW
          exact swan_two_minor_support_append_head_lt
            (I := H.idx) (J := G.idx) (W := W) rest
            (hLocal_support W hW))
    have hAppended_straighten :
        ∀ W : MinorWord m n, cAppended W ≠ 0 →
          ∃ c : StandardMinorWord m n →₀ k,
            MinorWord.toPolynomial k W =
              c.sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1)
            ∧
            (∀ U, c U ≠ 0 →
              MinorWord.degree U.1 = MinorWord.degree W)
            ∧
            (∀ U, c U ≠ 0 → H.t ≤ MinorWord.length U.1)
            ∧
            (∀ U, c U ≠ 0 →
              MinorWord.factorCount U.1 ≤ MinorWord.factorCount W) := by
      intro W hW
      rcases hAppended_head_lt W hW with ⟨F, G', hWfac, _hFG', hFH⟩
      have hFpos : 0 < F.t :=
        lt_of_lt_of_le hH hFH.pairLE.size_le
      have hTailStraight :
          ∃ cTail : StandardMinorWord m n →₀ k,
            MinorWord.toPolynomial k ⟨G' :: rest⟩ =
              cTail.sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1)
            ∧
            (∀ U, cTail U ≠ 0 →
              MinorWord.degree U.1 =
                MinorWord.degree (⟨G' :: rest⟩ : MinorWord m n))
            ∧
            (∀ U, cTail U ≠ 0 →
              MinorWord.factorCount U.1 ≤
                MinorWord.factorCount (⟨G' :: rest⟩ : MinorWord m n)) := by
        by_cases hG' : G'.t = 0
        · refine ⟨Finsupp.single restStd (1 : k), ?_, ?_, ?_⟩
          · have hGpoly :
                MinorFactor.toPolynomial k G' = 1 :=
              MinorFactor.toPolynomial_eq_one_of_size_zero k G' hG'
            simp [restStd, hGpoly]
          · intro U hU
            have hU_eq : U = restStd := by
              by_contra hne
              have hzero : (Finsupp.single restStd (1 : k)) U = 0 := by
                rw [Finsupp.single_eq_of_ne hne]
              exact hU hzero
            subst U
            simp [restStd, MinorFactor.degree, hG']
          · intro U hU
            have hU_eq : U = restStd := by
              by_contra hne
              have hzero : (Finsupp.single restStd (1 : k)) U = 0 := by
                rw [Finsupp.single_eq_of_ne hne]
              exact hU hzero
            subst U
            simp [restStd, MinorWord.factorCount]
        · have hGpos' : 0 < G'.t := Nat.pos_of_ne_zero hG'
          rcases minorFactor_mul_standardMinorWord_exists_filtered_strong k G' hGpos' restStd with
            ⟨cTail, hTail_poly, hTail_degree, _hTail_length,
              hTail_factorCount⟩
          refine ⟨cTail, hTail_poly, ?_, ?_⟩
          · intro U hU
            have hdeg := hTail_degree U hU
            simpa [restStd, MinorFactor.degree] using hdeg
          · intro U hU
            have hcnt := hTail_factorCount U hU
            simpa [restStd, MinorWord.factorCount] using hcnt
      rcases hTailStraight with
        ⟨cTail, hTail_poly, hTail_degree, hTail_factorCount⟩
      let insertWitness :
          (S' : { S' : StandardMinorWord m n // cTail S' ≠ 0 }) →
            ∃ c : StandardMinorWord m n →₀ k,
              MinorWord.toPolynomial k ⟨F :: S'.1.1.factors⟩ =
                c.sum (fun U a =>
                  MvPolynomial.C a * MinorWord.toPolynomial k U.1)
              ∧
              (∀ U, c U ≠ 0 →
                MinorWord.degree U.1 = F.t + MinorWord.degree S'.1.1)
              ∧
              (∀ U, c U ≠ 0 → F.t ≤ MinorWord.length U.1)
              ∧
              (∀ U, c U ≠ 0 →
                MinorWord.factorCount U.1 ≤
                  MinorWord.factorCount S'.1.1 + 1) :=
        fun S' =>
          minorFactor_mul_standardMinorWord_exists_filtered_strong k F hFpos S'.1
      let insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k :=
        fun S' =>
          if hS' : cTail S' ≠ 0 then
            Classical.choose (insertWitness ⟨S', hS'⟩)
          else 0
      have hinsert_poly :
          ∀ S' : StandardMinorWord m n, cTail S' ≠ 0 →
            MinorWord.toPolynomial k ⟨F :: S'.1.factors⟩ =
              (insertCoeff S').sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
        intro S' hS'
        have hspec := Classical.choose_spec (insertWitness ⟨S', hS'⟩)
        simpa [insertCoeff, hS'] using hspec.1
      have hinsert_degree :
          ∀ S' U : StandardMinorWord m n, cTail S' ≠ 0 →
            insertCoeff S' U ≠ 0 →
              MinorWord.degree U.1 = F.t + MinorWord.degree S'.1 := by
        intro S' U hS' hU
        have hspec := Classical.choose_spec (insertWitness ⟨S', hS'⟩)
        exact hspec.2.1 U (by simpa [insertCoeff, hS'] using hU)
      have hinsert_length :
          ∀ S' U : StandardMinorWord m n, cTail S' ≠ 0 →
            insertCoeff S' U ≠ 0 →
              F.t ≤ MinorWord.length U.1 := by
        intro S' U hS' hU
        have hspec := Classical.choose_spec (insertWitness ⟨S', hS'⟩)
        exact hspec.2.2.1 U (by simpa [insertCoeff, hS'] using hU)
      have hinsert_factorCount :
          ∀ S' U : StandardMinorWord m n, cTail S' ≠ 0 →
            insertCoeff S' U ≠ 0 →
              MinorWord.factorCount U.1 ≤ MinorWord.factorCount S'.1 + 1 := by
        intro S' U hS' hU
        have hspec := Classical.choose_spec (insertWitness ⟨S', hS'⟩)
        exact hspec.2.2.2 U (by simpa [insertCoeff, hS'] using hU)
      rcases minorWord_head_insert_after_tail_straightening_factorCount
          k F ⟨G' :: rest⟩ cTail hTail_poly hTail_degree
          hTail_factorCount insertCoeff hinsert_poly hinsert_degree
          hinsert_length hinsert_factorCount with
        ⟨c, hpoly, hdegree, hlengthF, hfactorCount⟩
      refine ⟨c, ?_, ?_, ?_, ?_⟩
      · cases W with
        | mk factors =>
            have hWfac' : factors = F :: G' :: rest := hWfac
            subst factors
            simpa using hpoly
      · intro U hU
        have hdeg := hdegree U hU
        cases W with
        | mk factors =>
            have hWfac' : factors = F :: G' :: rest := hWfac
            subst factors
            simpa using hdeg
      · intro U hU
        exact le_trans hFH.pairLE.size_le (hlengthF U hU)
      · intro U hU
        have hcnt := hfactorCount U hU
        cases W with
        | mk factors =>
            have hWfac' : factors = F :: G' :: rest := hWfac
            subst factors
            simpa using hcnt
    let straighten : MinorWord m n → StandardMinorWord m n →₀ k :=
      fun W =>
        if hW : cAppended W ≠ 0 then
          Classical.choose (hAppended_straighten W hW)
        else 0
    have hstraighten_poly :
        ∀ W : MinorWord m n, cAppended W ≠ 0 →
          MinorWord.toPolynomial k W =
            (straighten W).sum (fun U a =>
              MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
      intro W hW
      have hspec := Classical.choose_spec (hAppended_straighten W hW)
      simpa [straighten, hW] using hspec.1
    have hstraighten_degree :
        ∀ W U, cAppended W ≠ 0 → straighten W U ≠ 0 →
          MinorWord.degree U.1 = MinorWord.degree W := by
      intro W U hW hU
      have hspec := Classical.choose_spec (hAppended_straighten W hW)
      exact hspec.2.1 U (by simpa [straighten, hW] using hU)
    have hstraighten_length :
        ∀ W U, cAppended W ≠ 0 → straighten W U ≠ 0 →
          H.t ≤ MinorWord.length U.1 := by
      intro W U hW hU
      have hspec := Classical.choose_spec (hAppended_straighten W hW)
      exact hspec.2.2.1 U (by simpa [straighten, hW] using hU)
    have hstraighten_factorCount :
        ∀ W U, cAppended W ≠ 0 → straighten W U ≠ 0 →
          MinorWord.factorCount U.1 ≤ MinorWord.factorCount W := by
      intro W U hW hU
      have hspec := Classical.choose_spec (hAppended_straighten W hW)
      exact hspec.2.2.2 U (by simpa [straighten, hW] using hU)
    rcases minorWord_finsupp_bind_after_local_expansion_factorCount
        k cAppended straighten hstraighten_poly hstraighten_degree
        hstraighten_factorCount with ⟨c, hbind_poly, hbind_support⟩
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · rw [hLocal_tail_appended]
      exact hbind_poly
    · intro U hU
      rcases hbind_support U hU with ⟨W, hW, _hWU, hUdeg, _hUcount⟩
      have hWdeg := hAppended_degree W hW
      have hSdeg :
          MinorWord.degree S.1 =
            MinorWord.degree (⟨G :: rest⟩ : MinorWord m n) := by
        cases S with
        | mk W hpair =>
            cases W with
            | mk factors =>
                have hfac' : factors = G :: rest := hfac
                subst factors
                rfl
      rw [hUdeg, hWdeg, hSdeg]
    · intro U hU
      rcases hbind_support U hU with ⟨W, hW, hWU, _hUdeg, _hUcount⟩
      exact hstraighten_length W U hW hWU
    · intro U hU
      rcases hbind_support U hU with ⟨W, hW, _hWU, _hUdeg, hUcount⟩
      rcases hAppended_head_lt W hW with ⟨F, G', hWfac, _hFG', _hFH⟩
      have hWcount :
          MinorWord.factorCount W = rest.length + 2 := by
        cases W with
        | mk factors =>
            have hWfac' : factors = F :: G' :: rest := hWfac
            subst factors
            simp [MinorWord.factorCount]
      have hScount :
          MinorWord.factorCount S.1 + 1 = rest.length + 2 := by
        cases S with
        | mk W hpair =>
            cases W with
            | mk factors =>
                have hfac' : factors = G :: rest := hfac
                subst factors
                simp [MinorWord.factorCount]
      omega
termination_by
  (MinorWord.factorCount S.1 + 1, H)
decreasing_by
  all_goals
    simp_wf
    first
    | exact minorFactor_insert_tail_measure_lt
        (S := S) (H := H) (G := G) (G' := G') (rest := rest) hfac
    | exact minorFactor_insert_head_measure_lt
        (S := S) (H := H) (F := F) (G := G) (rest := rest)
        hfac (hTail_factorCount _ (by
          first
          | exact S'.2
          )) hFH

/-- Filtered insertion of a positive head factor into a standard minor word.

This is the filtered part of Swan Corollary 5.1.  It is proved by
well-founded induction on the head factor and the tail length; the
nonordered branch applies `swan_two_minor_straightening_relation` to the head
and the first factor of the standard tail, erases any zero-size unit factors,
and recurses on the new first factor supplied by `MinorIndex.PairLT`. -/
theorem minorFactor_mul_standardMinorWord_exists_filtered
    {m n : ℕ}
    (k : Type*) [Field k]
    (H : MinorFactor m n) (hH : 0 < H.t)
    (S : StandardMinorWord m n) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = H.t + MinorWord.degree S.1)
      ∧
      (∀ U, c U ≠ 0 →
        H.t ≤ MinorWord.length U.1) := by
  classical
  rcases minorFactor_mul_standardMinorWord_exists_filtered_strong k H hH S with
    ⟨c, hpoly, hdegree, hlength, _hfactorCount⟩
  exact ⟨c, hpoly, hdegree, hlength⟩

lemma minorWord_cons_of_tail_straightening_exists_degree
    {m n : ℕ}
    (k : Type*) [Field k]
    (F : MinorFactor m n) (tail : MinorWord m n)
    (hTail :
      ∃ cTail : StandardMinorWord m n →₀ k,
        MinorWord.toPolynomial k tail =
          cTail.sum (fun S a =>
            MvPolynomial.C a * MinorWord.toPolynomial k S.1)
        ∧
        (∀ S, cTail S ≠ 0 →
          MinorWord.degree S.1 = MinorWord.degree tail)) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k ⟨F :: tail.factors⟩ =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 =
          MinorWord.degree (⟨F :: tail.factors⟩ : MinorWord m n)) := by
  classical
  rcases hTail with ⟨cTail, hTail_poly, hTail_degree⟩
  by_cases hF : F.t = 0
  · refine ⟨cTail, ?_, ?_⟩
    · have hFpoly :
          MinorFactor.toPolynomial k F = 1 :=
        MinorFactor.toPolynomial_eq_one_of_size_zero k F hF
      simp only [MinorWord.toPolynomial_cons, hFpoly, one_mul]
      exact hTail_poly
    · intro U hU
      have hUdeg := hTail_degree U hU
      simpa [MinorFactor.degree, hF] using hUdeg
  · have hFpos : 0 < F.t := Nat.pos_of_ne_zero hF
    let insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k :=
      fun S => Classical.choose
        (minorFactor_mul_standardMinorWord_exists_filtered k F hFpos S)
    have hinsert_poly :
        ∀ S : StandardMinorWord m n, cTail S ≠ 0 →
          MinorWord.toPolynomial k ⟨F :: S.1.factors⟩ =
            (insertCoeff S).sum (fun U a =>
              MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
      intro S _hS
      have hspec := Classical.choose_spec
        (minorFactor_mul_standardMinorWord_exists_filtered k F hFpos S)
      simpa [insertCoeff] using hspec.1
    have hinsert_degree :
        ∀ S U : StandardMinorWord m n, cTail S ≠ 0 →
          insertCoeff S U ≠ 0 →
            MinorWord.degree U.1 = F.t + MinorWord.degree S.1 := by
      intro S U _hS hU
      have hspec := Classical.choose_spec
        (minorFactor_mul_standardMinorWord_exists_filtered k F hFpos S)
      exact hspec.2.1 U (by simpa [insertCoeff] using hU)
    exact minorWord_head_insert_after_tail_straightening
      k F tail cTail hTail_poly hTail_degree
      insertCoeff hinsert_poly hinsert_degree

/-- Degree-preserving straightening on arbitrary minor words.

This unfiltered statement is the recursive tool for straightening tails.  Unit
factors should be erased by `MinorWord.eraseUnits` before applying the
head/tail recursion. -/
theorem minorWord_straightening_exists_degree
    {m n : ℕ}
    (k : Type*) [Field k]
    (W : MinorWord m n) :
    ∃ c : StandardMinorWord m n →₀ k,
      MinorWord.toPolynomial k W =
        c.sum (fun U a =>
          MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      ∧
      (∀ U, c U ≠ 0 →
        MinorWord.degree U.1 = MinorWord.degree W) := by
  classical
  by_cases hW : MinorWord.PairwisePairLE W
  · exact minorWord_straightening_exists_degree_of_pairwise k W hW
  · have hcount : 2 ≤ MinorWord.factorCount W :=
      MinorWord.two_le_factorCount_of_not_pairwisePairLE hW
    rcases MinorWord.exists_two_cons_of_two_le_factorCount hcount with
      ⟨F, G, rest, hfac⟩
    by_cases hFG : MinorIndex.PairLE F.idx G.idx
    · have hTail :
          ¬ MinorWord.PairwisePairLE ⟨G :: rest⟩ := by
        have hWcons : ¬ MinorWord.PairwisePairLE ⟨F :: G :: rest⟩ := by
          intro hpair
          apply hW
          cases W with
          | mk factors =>
              rw [MinorWord.PairwisePairLE, hfac]
              simpa [MinorWord.PairwisePairLE] using hpair
        exact MinorWord.tail_not_pairwisePairLE_of_cons_cons_not_pairwise_of_head_le
          hFG hWcons
      have hTailStraight :
          ∃ c : StandardMinorWord m n →₀ k,
            MinorWord.toPolynomial k ⟨G :: rest⟩ =
              c.sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1)
            ∧
            (∀ U, c U ≠ 0 →
              MinorWord.degree U.1 =
                MinorWord.degree (⟨G :: rest⟩ : MinorWord m n)) :=
        minorWord_straightening_exists_degree k ⟨G :: rest⟩
      rcases minorWord_cons_of_tail_straightening_exists_degree
          k F ⟨G :: rest⟩ hTailStraight with
        ⟨c, hpoly, hdegree⟩
      refine ⟨c, ?_, ?_⟩
      · cases W with
        | mk factors =>
            have hfac' : factors = F :: G :: rest := hfac
            subst factors
            simpa using hpoly
      · intro U hU
        have hdeg := hdegree U hU
        cases W with
        | mk factors =>
            have hfac' : factors = F :: G :: rest := hfac
            subst factors
            simpa using hdeg
    · -- Apply the two-minor straightening relation to `F * G`, then
      -- recursively straighten each appended local word.
      have hFpos_or_zero : F.t = 0 ∨ 0 < F.t := Nat.eq_zero_or_pos F.t
      rcases hFpos_or_zero with hFzero | hFpos
      · have hTailStraight :
            ∃ c : StandardMinorWord m n →₀ k,
              MinorWord.toPolynomial k ⟨G :: rest⟩ =
                c.sum (fun U a =>
                  MvPolynomial.C a * MinorWord.toPolynomial k U.1)
              ∧
              (∀ U, c U ≠ 0 →
                MinorWord.degree U.1 =
                  MinorWord.degree (⟨G :: rest⟩ : MinorWord m n)) :=
          minorWord_straightening_exists_degree k ⟨G :: rest⟩
        rcases minorWord_cons_of_tail_straightening_exists_degree
            k F ⟨G :: rest⟩ hTailStraight with
          ⟨c, hpoly, hdegree⟩
        refine ⟨c, ?_, ?_⟩
        · cases W with
          | mk factors =>
              have hfac' : factors = F :: G :: rest := hfac
              subst factors
              simpa using hpoly
        · intro U hU
          have hdeg := hdegree U hU
          cases W with
          | mk factors =>
              have hfac' : factors = F :: G :: rest := hfac
              subst factors
              simpa using hdeg
      have hGpos : 0 < G.t := by
        by_cases hGzero : G.t = 0
        · exfalso
          apply hFG
          refine MinorIndex.PairLE.of_components ?_ ?_
          · simp [hGzero]
          · intro j
            exact False.elim (Nat.not_lt_zero j.val (by
              simpa [hGzero] using j.isLt))
        · exact Nat.pos_of_ne_zero hGzero
      rcases swan_two_minor_straightening_relation k
          hFpos hGpos F.idx G.idx hFG with
        ⟨cLocal, hLocal_poly, hLocal_support⟩
      let appendWord : MinorWord m n → MinorWord m n :=
        fun W => (⟨W.factors ++ rest⟩ : MinorWord m n)
      let cAppended : MinorWord m n →₀ k :=
        Finsupp.mapDomain appendWord cLocal
      have hLocal_appended :
          MinorWord.toPolynomial k ⟨F :: G :: rest⟩ =
            cAppended.sum fun W a =>
              MvPolynomial.C a * MinorWord.toPolynomial k W := by
        calc
          MinorWord.toPolynomial k ⟨F :: G :: rest⟩
              =
            (cLocal.sum fun W a =>
                MvPolynomial.C a * MinorWord.toPolynomial k W) *
              MinorWord.toPolynomial k ⟨rest⟩ := by
              simp only [MinorWord.toPolynomial_cons,
                MinorFactor.toPolynomial]
              calc
                genericMinor k F.idx *
                    (genericMinor k G.idx *
                      MinorWord.toPolynomial k ⟨rest⟩)
                    =
                  (genericMinor k F.idx * genericMinor k G.idx) *
                    MinorWord.toPolynomial k ⟨rest⟩ := by
                    ring
                _ =
                  (cLocal.sum fun W a =>
                      MvPolynomial.C a *
                        MinorWord.toPolynomial k W) *
                    MinorWord.toPolynomial k ⟨rest⟩ := by
                    rw [hLocal_poly]
          _ =
            cAppended.sum fun W a =>
              MvPolynomial.C a * MinorWord.toPolynomial k W := by
              simpa [cAppended, appendWord] using
                minorWord_finsupp_sum_mul_tail k cLocal rest
      have hAppended_degree :
          ∀ W' : MinorWord m n, cAppended W' ≠ 0 →
            MinorWord.degree W' =
              MinorWord.degree (⟨F :: G :: rest⟩ : MinorWord m n) := by
        intro W' hW'
        have hdeg :
            MinorWord.degree W' =
              F.t + MinorWord.degree ⟨G :: rest⟩ :=
          finsupp_mapDomain_support_property appendWord cLocal
            (fun W' => MinorWord.degree W' =
              F.t + MinorWord.degree ⟨G :: rest⟩)
            (by
              intro W hW
              exact swan_two_minor_support_append_degree_factor
                F G rest (hLocal_support W hW))
            W' hW'
        simpa [MinorFactor.degree, Nat.add_assoc] using hdeg
      have hAppended_head :
          ∀ W' : MinorWord m n, cAppended W' ≠ 0 →
            ∃ F' G' : MinorFactor m n,
              W'.factors = F' :: G' :: rest ∧
              MinorIndex.PairLE F'.idx G'.idx ∧
              MinorIndex.PairLT F'.idx F.idx := by
        exact finsupp_mapDomain_support_property appendWord cLocal
          (fun W' =>
            ∃ F' G' : MinorFactor m n,
              W'.factors = F' :: G' :: rest ∧
              MinorIndex.PairLE F'.idx G'.idx ∧
              MinorIndex.PairLT F'.idx F.idx)
          (by
            intro W hW
            exact swan_two_minor_support_append_head_lt
              (I := F.idx) (J := G.idx) (W := W) rest
              (hLocal_support W hW))
      have hAppended_straighten :
          ∀ W' : MinorWord m n, cAppended W' ≠ 0 →
            ∃ c : StandardMinorWord m n →₀ k,
              MinorWord.toPolynomial k W' =
                c.sum (fun U a =>
                  MvPolynomial.C a * MinorWord.toPolynomial k U.1)
              ∧
              (∀ U, c U ≠ 0 →
                MinorWord.degree U.1 = MinorWord.degree W') := by
        intro W' hW'
        rcases hAppended_head W' hW' with ⟨F', G', hWfac, _hFG', _hFlt⟩
        have hTailStraight :
            ∃ c : StandardMinorWord m n →₀ k,
              MinorWord.toPolynomial k ⟨G' :: rest⟩ =
                c.sum (fun U a =>
                  MvPolynomial.C a * MinorWord.toPolynomial k U.1)
              ∧
              (∀ U, c U ≠ 0 →
                MinorWord.degree U.1 =
                  MinorWord.degree (⟨G' :: rest⟩ : MinorWord m n)) :=
          minorWord_straightening_exists_degree k ⟨G' :: rest⟩
        rcases minorWord_cons_of_tail_straightening_exists_degree
            k F' ⟨G' :: rest⟩ hTailStraight with
          ⟨c, hpoly, hdegree⟩
        refine ⟨c, ?_, ?_⟩
        · cases W' with
          | mk factors =>
              have hWfac' : factors = F' :: G' :: rest := hWfac
              subst factors
              simpa using hpoly
        · intro U hU
          have hdeg := hdegree U hU
          cases W' with
          | mk factors =>
              have hWfac' : factors = F' :: G' :: rest := hWfac
              subst factors
              simpa using hdeg
      let straighten : MinorWord m n → StandardMinorWord m n →₀ k :=
        fun W' =>
          if hW' : cAppended W' ≠ 0 then
            Classical.choose (hAppended_straighten W' hW')
          else 0
      have hstraighten_poly :
          ∀ W' : MinorWord m n, cAppended W' ≠ 0 →
            MinorWord.toPolynomial k W' =
              (straighten W').sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
        intro W' hW'
        have hspec := Classical.choose_spec (hAppended_straighten W' hW')
        simpa [straighten, hW'] using hspec.1
      have hstraighten_degree :
          ∀ W' : MinorWord m n, ∀ U : StandardMinorWord m n,
            cAppended W' ≠ 0 → straighten W' U ≠ 0 →
              MinorWord.degree U.1 = MinorWord.degree W' := by
        intro W' U hW' hU
        have hspec := Classical.choose_spec (hAppended_straighten W' hW')
        exact hspec.2 U (by simpa [straighten, hW'] using hU)
      rcases minorWord_finsupp_bind_after_local_expansion
          k cAppended straighten hstraighten_poly
          hstraighten_degree with ⟨c, hbind_poly, hbind_support⟩
      refine ⟨c, ?_, ?_⟩
      · cases W with
        | mk factors =>
            have hfac' : factors = F :: G :: rest := hfac
            subst factors
            rw [hLocal_appended]
            exact hbind_poly
      · intro U hU
        rcases hbind_support U hU with ⟨W', hW', _hWU, hUdeg⟩
        rw [hUdeg, hAppended_degree W' hW']
        cases W with
        | mk factors =>
            have hfac' : factors = F :: G :: rest := hfac
            subst factors
            rfl
termination_by MinorWord.factorCount W
decreasing_by
  all_goals
    cases W with
    | mk factors =>
        simp [MinorWord.factorCount] at hfac ⊢
        subst factors
        simp

/-- Filtered straightening existence based on Swan’s proof: every bitableau
straightens to standard bitableaux of the same degree and no smaller length.
Equivalently, every nonzero output term has length at least the input length. -/
theorem straightening_law_exists_filtered
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n) :
    ∃ c : StandardYoungBitableau m n →₀ k,
      YoungBitableau.toPolynomial k B =
        c.sum (fun S a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S, c S ≠ 0 →
        YoungBitableau.degree S.1 = YoungBitableau.degree B)
      ∧
      (∀ S, c S ≠ 0 →
        YoungBitableau.length B ≤ YoungBitableau.length S.1) := by
  classical
  by_cases hv : 0 < B.v
  · let H : MinorFactor m n :=
      { t := B.size ⟨0, hv⟩, idx := B.minorindex ⟨0, hv⟩ }
    let T : MinorWord m n :=
      MinorWord.eraseUnits (YoungBitableau.toMinorWord (YoungBitableau.tail B hv))
    have hH : 0 < H.t := by
      simpa [H] using B.size_pos ⟨0, hv⟩
    rcases minorWord_straightening_exists_degree k T with
      ⟨dTail, hdTail_poly, hdTail_degree⟩
    have hinsert :
        ∀ S : StandardMinorWord m n, dTail S ≠ 0 →
          ∃ cS : StandardMinorWord m n →₀ k,
            MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
              cS.sum (fun U a =>
                MvPolynomial.C a * MinorWord.toPolynomial k U.1)
            ∧
            (∀ U, cS U ≠ 0 →
              MinorWord.degree U.1 = H.t + MinorWord.degree S.1)
            ∧
            (∀ U, cS U ≠ 0 →
              H.t ≤ MinorWord.length U.1) := by
      intro S _hS
      exact minorFactor_mul_standardMinorWord_exists_filtered k H hH S
    /- Interface layer for nonempty Young bitableaux:

       Since Young-bitableau sizes are weakly decreasing,
       `YoungBitableau.length B = H.t`.  Straighten the tail as a degree-only
       minor word, insert the positive head with the filtered insertion theorem,
       then transport standard minor words back to standard Young bitableaux
       after deleting unit factors. -/
    let insertCoeff : StandardMinorWord m n → StandardMinorWord m n →₀ k :=
      fun S =>
        if hS : dTail S ≠ 0 then Classical.choose (hinsert S hS) else 0
    have hinsert_poly :
        ∀ S : StandardMinorWord m n, dTail S ≠ 0 →
          MinorWord.toPolynomial k ⟨H :: S.1.factors⟩ =
            (insertCoeff S).sum (fun U a =>
              MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
      intro S hS
      have hspec := Classical.choose_spec (hinsert S hS)
      simpa [insertCoeff, hS] using hspec.1
    have hinsert_degree :
        ∀ S : StandardMinorWord m n, ∀ U : StandardMinorWord m n,
          dTail S ≠ 0 → insertCoeff S U ≠ 0 →
            MinorWord.degree U.1 = H.t + MinorWord.degree S.1 := by
      intro S U hS hU
      have hspec := Classical.choose_spec (hinsert S hS)
      exact hspec.2.1 U (by simpa [insertCoeff, hS] using hU)
    have hinsert_length :
        ∀ S : StandardMinorWord m n, ∀ U : StandardMinorWord m n,
          dTail S ≠ 0 → insertCoeff S U ≠ 0 →
            H.t ≤ MinorWord.length U.1 := by
      intro S U hS hU
      have hspec := Classical.choose_spec (hinsert S hS)
      exact hspec.2.2 U (by simpa [insertCoeff, hS] using hU)
    let cMinor : StandardMinorWord m n →₀ k :=
      finsuppScalarBind dTail insertCoeff
    have hminor_poly :
        YoungBitableau.toPolynomial k B =
          cMinor.sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1) := by
      rw [YoungBitableau.toPolynomial_eq_head_minorWord_mul_erased_tail
        k B hv]
      change
        MinorWord.toPolynomial k ⟨H :: T.factors⟩ =
          cMinor.sum (fun U a =>
            MvPolynomial.C a * MinorWord.toPolynomial k U.1)
      have hhead_tail :
          MinorWord.toPolynomial k ⟨H :: T.factors⟩ =
            dTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k
                ⟨H :: S.1.factors⟩ := by
        calc
          MinorWord.toPolynomial k ⟨H :: T.factors⟩
              =
            MinorFactor.toPolynomial k H *
              MinorWord.toPolynomial k T := by
              simp
          _ =
            MinorFactor.toPolynomial k H *
              (dTail.sum fun S a =>
                MvPolynomial.C a * MinorWord.toPolynomial k S.1) := by
              rw [hdTail_poly]
          _ =
            dTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k
                ⟨H :: S.1.factors⟩ := by
              rw [Finsupp.mul_sum]
              apply Finsupp.sum_congr
              intro S a
              simp [mul_assoc, mul_left_comm, mul_comm]
      rw [hhead_tail]
      have hdist :
          (dTail.sum fun S a =>
              MvPolynomial.C a * MinorWord.toPolynomial k
                ⟨H :: S.1.factors⟩) =
            dTail.sum fun S a =>
              MvPolynomial.C a *
                (insertCoeff S).sum (fun U b =>
                  MvPolynomial.C b * MinorWord.toPolynomial k U.1) := by
        apply Finsupp.sum_congr
        intro S a
        by_cases hS : dTail S = 0
        · simp [hS]
        · rw [hinsert_poly S hS]
      rw [hdist]
      rw [← finsuppScalarBind_polynomial_sum
        (c := dTail) (d := insertCoeff)
        (v := fun U : StandardMinorWord m n =>
          MinorWord.toPolynomial k U.1)]
    have hminor_degree :
        ∀ U : StandardMinorWord m n, cMinor U ≠ 0 →
          MinorWord.degree U.1 = YoungBitableau.degree B := by
      intro U hU
      rcases finsuppScalarBind_apply_ne_zero_exists
          dTail insertCoeff hU with ⟨S, hS, hSU⟩
      have hUdeg := hinsert_degree S U hS hSU
      have hSdeg := hdTail_degree S hS
      rw [hUdeg, hSdeg]
      exact YoungBitableau.degree_eq_head_minorWord_add_erased_tail B hv
    have hminor_length :
        ∀ U : StandardMinorWord m n, cMinor U ≠ 0 →
          YoungBitableau.length B ≤ MinorWord.length U.1 := by
      intro U hU
      rcases finsuppScalarBind_apply_ne_zero_exists
          dTail insertCoeff hU with ⟨S, hS, hSU⟩
      have hlen := hinsert_length S U hS hSU
      simpa [H, YoungBitableau.length_eq_head_size B hv] using hlen
    rcases standardMinorWord_pushforward_toYoungBitableauAfterEraseUnits k cMinor with
      ⟨cY, hpush_poly, hpush_support⟩
    refine ⟨cY, ?_, ?_, ?_⟩
    · rw [hminor_poly, hpush_poly]
    · intro S hS
      rcases hpush_support S hS with ⟨U, hU, hUS⟩
      rw [← hUS]
      rw [StandardMinorWord.toYoungBitableauAfterEraseUnits_degree]
      exact hminor_degree U hU
    · intro S hS
      rcases hpush_support S hS with ⟨U, hU, hUS⟩
      rw [← hUS]
      rw [StandardMinorWord.toYoungBitableauAfterEraseUnits_length]
      exact hminor_length U hU
  · have hBstd : YoungBitableau.IsStandard B :=
      YoungBitableau.isStandard_of_v_le_one (B := B) (by omega)
    exact straightening_law_exists_filtered_of_isStandard k B hBstd

/-- A degree-`d` monomial lies in the span of standard bitableaux of degree `d`.
This uses filtered straightening only for existence, not for uniqueness. -/
lemma monomial_mem_span_standardBitableau_degree
    {m n : ℕ}
    (k : Type*) [Field k]
    {d : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ)
    (hE : Finsupp.degree E = d) :
    MvPolynomial.monomial E (1 : k) ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              YoungBitableau.degree S.1 = d } =>
            YoungBitableau.toPolynomial k S.1.1)) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : { S : StandardYoungBitableau m n //
            YoungBitableau.degree S.1 = d } =>
          YoungBitableau.toPolynomial k S.1.1))
  have hmono_all :
      MvPolynomial.monomial E (1 : k) ∈
        Submodule.span k
          (Set.range
            (fun B : YoungBitableau m n =>
              YoungBitableau.toPolynomial k B)) :=
    monomial_mem_span_youngBitableau_toPolynomial_aux k E
  have hcomp_all :
      MvPolynomial.homogeneousComponent d (MvPolynomial.monomial E (1 : k)) ∈ W := by
    refine Submodule.span_induction
      (p := fun p _hp => MvPolynomial.homogeneousComponent d p ∈ W)
      ?mem ?zero ?add ?smul hmono_all
    · rintro p ⟨B, rfl⟩
      rcases straightening_law_exists_filtered k B with
        ⟨c, hpoly, hdeg, _hlen⟩
      change MvPolynomial.homogeneousComponent d
        (YoungBitableau.toPolynomial k B) ∈ W
      rw [hpoly]
      rw [homogeneousComponent_standardBitableau_finsupp_sum k]
      rw [Finsupp.sum]
      apply Submodule.sum_mem
      intro S hS
      by_cases hSd : YoungBitableau.degree S.1 = d
      · have hgen : YoungBitableau.toPolynomial k S.1 ∈ W := by
          exact Submodule.subset_span ⟨⟨S, hSd⟩, rfl⟩
        simpa [Finsupp.filter_apply, hSd, MvPolynomial.C_mul'] using
          W.smul_mem (c S) hgen
      · have hnot : S ∉ (c.filter fun S => YoungBitableau.degree S.1 = d).support := by
          rw [Finsupp.support_filter]
          exact fun h => hSd (Finset.mem_filter.mp h).2
        exact False.elim (hnot hS)
    · simp [W]
    · intro x y _hx _hy hxW hyW
      simpa [map_add] using W.add_mem hxW hyW
    · intro a x _hx hxW
      simpa [map_smul] using W.smul_mem a hxW
  have hmono_hom :
      MvPolynomial.homogeneousComponent d (MvPolynomial.monomial E (1 : k)) =
        MvPolynomial.monomial E (1 : k) := by
    have hmem :
        MvPolynomial.monomial E (1 : k) ∈
          MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [hE] using
        (MvPolynomial.isHomogeneous_monomial (R := k) (d := E) (1 : k) hE)
    simpa using MvPolynomial.homogeneousComponent_of_mem (m := d) hmem
  simpa [W, hmono_hom] using hcomp_all

/-- In each fixed degree, the standard bitableaux of that degree span the homogeneous
component.  This is now a filtered-straightening existence consequence. -/
theorem span_standardBitableau_degree_eq_homogeneousSubmodule
    {m n : ℕ}
    (k : Type*) [Field k]
    (d : ℕ) :
    Submodule.span k
      (Set.range
        (fun S : { S : StandardYoungBitableau m n //
            YoungBitableau.degree S.1 = d } =>
          YoungBitableau.toPolynomial k S.1.1)) =
    MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := by
  classical
  let StdDeg : Type :=
    { S : StandardYoungBitableau m n // YoungBitableau.degree S.1 = d }
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : StdDeg => YoungBitableau.toPolynomial k S.1.1))
  change W = MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro p ⟨S, rfl⟩
    change YoungBitableau.toPolynomial k S.1.1 ∈
      MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d
    rw [MvPolynomial.mem_homogeneousSubmodule]
    simpa [S.2] using YoungBitableau.toPolynomial_isHomogeneous k S.1.1
  · intro p hp
    have hxRestrict :
        p ∈
          MvPolynomial.restrictSupport k
            { E : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E = d } := by
      simpa [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
        MvPolynomial.restrictSupport] using hp
    rw [MvPolynomial.restrictSupport_eq_span] at hxRestrict
    refine Submodule.span_induction
      (p := fun p _hp => p ∈ W)
      ?mem ?zero ?add ?smul hxRestrict
    · rintro p ⟨E, hEd, rfl⟩
      exact monomial_mem_span_standardBitableau_degree k E hEd
    · simp [W]
    · intro p q _hp _hq hpW hqW
      exact W.add_mem hpW hqW
    · intro a p _hp hpW
      exact W.smul_mem a hpW

/-- Fixed-degree standard bitableaux are linearly independent: filtered
straightening gives spanning, and KRS gives the matching cardinality. -/
theorem standardBitableau_degree_linearIndependent
    {m n : ℕ}
    (k : Type*) [Field k]
    (d : ℕ) :
    LinearIndependent k
      (fun S : { S : StandardYoungBitableau m n //
          YoungBitableau.degree S.1 = d } =>
        YoungBitableau.toPolynomial k S.1.1) := by
  classical
  let StdDeg : Type :=
    { S : StandardYoungBitableau m n // YoungBitableau.degree S.1 = d }
  let DegreeMonomials : Type :=
    { E : (Fin m × Fin n) →₀ ℕ // Finsupp.degree E = d }
  have hDegreeFinite :
      Set.Finite
        { E : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E = d } := by
    exact (Finsupp.finite_of_degree_le (σ := Fin m × Fin n) d).subset
      (by
        intro E hE
        exact le_of_eq hE)
  haveI : Finite DegreeMonomials := hDegreeFinite.to_subtype
  haveI : Fintype DegreeMonomials := Fintype.ofFinite DegreeMonomials
  rcases exists_krsEquiv_of_degree m n d with ⟨κd, _hwidth⟩
  haveI : Fintype StdDeg := Fintype.ofEquiv DegreeMonomials κd
  have hH_finrank :
      Module.finrank k
          (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) =
        Nat.card DegreeMonomials := by
    calc
      Module.finrank k
          (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d)
          =
        Module.finrank k
          (MvPolynomial.restrictSupport k
            { E : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E = d }) := by
            rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
              MvPolynomial.restrictSupport]
      _ = Nat.card DegreeMonomials := by
            rw [Module.finrank_eq_nat_card_basis
              (MvPolynomial.basisRestrictSupport
                (R := k)
                { E : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E = d })]
            rfl
  have hcard :
      Fintype.card StdDeg =
        (Set.range
          (fun S : StdDeg =>
            YoungBitableau.toPolynomial k S.1.1)).finrank k := by
    calc
      Fintype.card StdDeg = Fintype.card DegreeMonomials := by
        exact (Fintype.card_congr κd).symm
      _ = Nat.card DegreeMonomials := Fintype.card_eq_nat_card
      _ = Module.finrank k
            (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) :=
          hH_finrank.symm
      _ =
          (Set.range
            (fun S : StdDeg =>
              YoungBitableau.toPolynomial k S.1.1)).finrank k := by
        rw [Set.finrank]
        rw [span_standardBitableau_degree_eq_homogeneousSubmodule k d]
  exact (linearIndependent_iff_card_eq_finrank_span).2 hcard

/-- Polynomial-level linear independence of standard bitableaux, supplied independently
from straightening uniqueness to avoid a circular proof. -/
theorem straightening_law_standardBitableau_linearIndependent
    {m n : ℕ}
    (k : Type*) [Field k] :
    LinearIndependent k
      (fun S : StandardYoungBitableau m n =>
        YoungBitableau.toPolynomial k S.1) := by
  apply standardBitableau_linearIndependent_of_degreewise
  intro d
  exact standardBitableau_degree_linearIndependent k d

/-- Existence of a polynomial expansion by standard bitableaux.  This is the spanning
part of straightening. -/
theorem straightening_law_polynomial_exists
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n) :
    ∃ c : StandardYoungBitableau m n →₀ k,
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) := by
  rcases straightening_law_exists_filtered k B with
    ⟨c, hpoly, _hdegree, _hlength⟩
  exact ⟨c, hpoly⟩

/-- Existence and uniqueness of the polynomial expansion by standard bitableaux. -/
theorem straightening_law_polynomial_exists_unique
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n) :
    ∃! c : StandardYoungBitableau m n →₀ k,
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) := by
  rcases straightening_law_polynomial_exists k B with
    ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact straightening_law_unique_of_linearIndependent k
    (straightening_law_standardBitableau_linearIndependent k)
    B d c hd hc

/-- Degree support for the unique straightening expansion. -/
theorem straightening_law_degree_support
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (c : StandardYoungBitableau m n →₀ k)
    (hpoly :
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)) :
    ∀ S : StandardYoungBitableau m n,
      c S ≠ 0 → YoungBitableau.degree S.1 = YoungBitableau.degree B := by
  rcases straightening_law_exists_filtered k B with
    ⟨d, hdpoly, hddegree, _hdlength⟩
  have hcd : c = d := by
    exact straightening_law_unique_of_linearIndependent k
      (straightening_law_standardBitableau_linearIndependent k)
      B c d hpoly hdpoly
  intro S hS
  rw [hcd] at hS
  exact hddegree S hS

/-- Length support for the unique straightening expansion. -/
theorem straightening_law_length_support
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n)
    (c : StandardYoungBitableau m n →₀ k)
    (hpoly :
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)) :
    ∀ S : StandardYoungBitableau m n,
      c S ≠ 0 → YoungBitableau.length B ≤ YoungBitableau.length S.1 := by
  rcases straightening_law_exists_filtered k B with
    ⟨d, hdpoly, _hddegree, hdlength⟩
  have hcd : c = d := by
    exact straightening_law_unique_of_linearIndependent k
      (straightening_law_standardBitableau_linearIndependent k)
      B c d hpoly hdpoly
  intro S hS
  rw [hcd] at hS
  exact hdlength S hS


/--
Proposition 3: straightening law for Young bitableaux.

Every bitableau can be uniquely expanded as a finite `k`-linear combination
of standard bitableaux. Every standard bitableau appearing with nonzero
coefficient has the same total degree, and its length is at least the length
of the original bitableau.
-/
theorem straightening_law
    {m n : ℕ}
    (k : Type*) [Field k]
    (B : YoungBitableau m n) :
    ∃! c : (StandardYoungBitableau m n →₀ k),
      YoungBitableau.toPolynomial k B
        =
      c.sum (fun S a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c S ≠ 0 → YoungBitableau.degree S.1 = YoungBitableau.degree B)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c S ≠ 0 → YoungBitableau.length B ≤ YoungBitableau.length S.1) := by
  rcases straightening_law_polynomial_exists_unique k B with
    ⟨c, hpoly, huniq_poly⟩
  refine ⟨c, ?_, ?_⟩
  · exact ⟨hpoly,
      straightening_law_degree_support k B c hpoly,
      straightening_law_length_support k B c hpoly⟩
  · intro d hd
    exact huniq_poly d hd.1


/--
Straightening-basis package for the determinantal ring.

If the images of the standard bitableaux of length at most `r` are linearly
independent and span `K[X] / J_r`, this theorem assembles them into the basis
used by the Hilbert-function argument.
-/
theorem exists_standardBitableau_basis_determinantalRing_of_straightening_basis
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hli :
      LinearIndependent k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1)))
    (hspan :
      Submodule.span k
        (Set.range
          (fun B : StandardYoungBitableauOfLengthLE m n r =>
            Ideal.Quotient.mk (Jr m n r k)
              (YoungBitableau.toPolynomial k B.1.1))) = ⊤) :
    ∃ b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k),
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1) := by
  exact exists_basis_eq_of_linearIndependent_span
    (fun B : StandardYoungBitableauOfLengthLE m n r =>
      Ideal.Quotient.mk (Jr m n r k)
        (YoungBitableau.toPolynomial k B.1.1))
    hli hspan

/--
Straightening gives the spanning step for bitableaux once standard bitableaux
of length greater than `r` are known to vanish in the quotient by `J_r`.
-/
theorem quotient_youngBitableau_mem_span_standardBitableau_lengthLE_of_straightening
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (B : YoungBitableau m n)
    (hlong :
      ∀ S : StandardYoungBitableau m n,
        r < YoungBitableau.length S.1 →
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k S.1) = 0) :
    Ideal.Quotient.mk (Jr m n r k)
        (YoungBitableau.toPolynomial k B) ∈
      Submodule.span k
        (Set.range
          (fun S : StandardYoungBitableauOfLengthLE m n r =>
            Ideal.Quotient.mk (Jr m n r k)
              (YoungBitableau.toPolynomial k S.1.1))) := by
  classical
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  let V : Submodule k (Rr m n r k) :=
    Submodule.span k
      (Set.range
        (fun S : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k S.1.1)))
  rcases straightening_law k B with
    ⟨c, ⟨hpoly, _hdeg, hlength⟩, _huniq⟩
  change q (YoungBitableau.toPolynomial k B) ∈ V
  rw [hpoly]
  change
    q (c.sum fun S a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) ∈ V
  rw [Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro S hS
  by_cases ha : c S = 0
  · simp [ha]
  by_cases hshort : YoungBitableau.length S.1 ≤ r
  · have hgen :
        q (YoungBitableau.toPolynomial k S.1) ∈ V := by
      refine Submodule.subset_span ?_
      exact ⟨⟨S, hshort⟩, rfl⟩
    have hsmul :
        c S • q (YoungBitableau.toPolynomial k S.1) ∈ V :=
      V.smul_mem (c S) hgen
    simpa [q, MvPolynomial.C_mul'] using hsmul
  · have hlongS : r < YoungBitableau.length S.1 :=
      Nat.lt_of_not_ge hshort
    have hz :
        q (YoungBitableau.toPolynomial k S.1) = 0 := by
      simpa [q] using hlong S hlongS
    simp [q, MvPolynomial.C_mul', hz]

/--
If every minor of size strictly larger than `r` belongs to `J_r`, then every
standard bitableau of length greater than `r` maps to zero in the
determinantal ring.
-/
theorem quotient_standardBitableau_eq_zero_of_length_gt_of_large_minors_mem_Jr
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (S : StandardYoungBitableau m n)
    (hS : r < YoungBitableau.length S.1) :
    Ideal.Quotient.mk (Jr m n r k)
      (YoungBitableau.toPolynomial k S.1) = 0 := by
  classical
  have hex :
      ∃ a : Fin S.1.v, r < S.1.size a := by
    by_contra h
    push_neg at h
    have hle : YoungBitableau.length S.1 ≤ r := by
      unfold YoungBitableau.length
      exact Finset.sup_le fun a _ => h a
    exact (not_lt_of_ge hle) hS
  rcases hex with ⟨a, ha⟩
  have hfactor :
      genericMinor k (S.1.minorindex a) ∈ Jr m n r k :=
    hlarge (S.1.minorindex a) ha
  have hprod :
      YoungBitableau.toPolynomial k S.1 ∈ Jr m n r k := by
    rw [YoungBitableau.toPolynomial]
    rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ a)]
    exact Ideal.mul_mem_right _ _ hfactor
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod

/--
Straightening plus the vanishing of all minors of size greater than `r` gives
the spanning step for every bitableau.
-/
theorem quotient_youngBitableau_mem_span_standardBitableau_lengthLE_of_large_minors_mem_Jr
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (B : YoungBitableau m n) :
    Ideal.Quotient.mk (Jr m n r k)
        (YoungBitableau.toPolynomial k B) ∈
      Submodule.span k
        (Set.range
          (fun S : StandardYoungBitableauOfLengthLE m n r =>
            Ideal.Quotient.mk (Jr m n r k)
              (YoungBitableau.toPolynomial k S.1.1))) := by
  exact
    quotient_youngBitableau_mem_span_standardBitableau_lengthLE_of_straightening k r B
      (fun S hS =>
        quotient_standardBitableau_eq_zero_of_length_gt_of_large_minors_mem_Jr k r hlarge S hS)

/--
If bitableaux span the quotient and all minors of size greater than `r`
belong to `J_r`, then the standard bitableaux of length at most `r` span the
determinantal ring.
-/
theorem span_standardBitableau_lengthLE_eq_top_of_youngBitableaux_span_and_large_minors
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (hyoung_span :
      ∀ p : MvPolynomial (Fin m × Fin n) k,
        Ideal.Quotient.mk (Jr m n r k) p ∈
          Submodule.span k
            (Set.range
              (fun B : YoungBitableau m n =>
                Ideal.Quotient.mk (Jr m n r k)
                  (YoungBitableau.toPolynomial k B)))) :
    Submodule.span k
        (Set.range
          (fun S : StandardYoungBitableauOfLengthLE m n r =>
            Ideal.Quotient.mk (Jr m n r k)
              (YoungBitableau.toPolynomial k S.1.1))) = ⊤ := by
  classical
  let Vshort : Submodule k (Rr m n r k) :=
    Submodule.span k
      (Set.range
        (fun S : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k S.1.1)))
  let Vall : Submodule k (Rr m n r k) :=
    Submodule.span k
      (Set.range
        (fun B : YoungBitableau m n =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B)))
  have hVall_le : Vall ≤ Vshort := by
    rw [Submodule.span_le]
    rintro x ⟨B, rfl⟩
    exact
    quotient_youngBitableau_mem_span_standardBitableau_lengthLE_of_large_minors_mem_Jr k r hlarge B
  apply eq_top_iff.mpr
  intro x _hx
  rcases Ideal.Quotient.mk_surjective x with ⟨p, rfl⟩
  change Ideal.Quotient.mk (Jr m n r k) p ∈ Vshort
  exact hVall_le (hyoung_span p)

/--
Basis criterion using the straightening spanning package: to finish the paper's
basis statement it is enough to prove bitableaux span the quotient, large minors
belong to `J_r`, and the short standard bitableaux are linearly independent in
the quotient.
-/
theorem exists_standardBitableau_basis_determinantalRing_of_youngBitableaux_span
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (hyoung_span :
      ∀ p : MvPolynomial (Fin m × Fin n) k,
        Ideal.Quotient.mk (Jr m n r k) p ∈
          Submodule.span k
            (Set.range
              (fun B : YoungBitableau m n =>
                Ideal.Quotient.mk (Jr m n r k)
                  (YoungBitableau.toPolynomial k B))))
    (hli :
      LinearIndependent k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))) :
    ∃ b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k),
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1) := by
  exact
  exists_standardBitableau_basis_determinantalRing_of_straightening_basis k r hli
   (span_standardBitableau_lengthLE_eq_top_of_youngBitableaux_span_and_large_minors
    k r hlarge hyoung_span)

/--
To show that bitableaux span the quotient it is enough to show this for
monomials.  This is the polynomial-basis reduction before identifying each
monomial with a product of `1 × 1` minors.
-/
theorem quotient_polynomial_mem_span_youngBitableau_of_monomials
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hmono :
      ∀ E : (Fin m × Fin n) →₀ ℕ,
        Ideal.Quotient.mk (Jr m n r k)
            (MvPolynomial.monomial E (1 : k)) ∈
          Submodule.span k
            (Set.range
              (fun B : YoungBitableau m n =>
                Ideal.Quotient.mk (Jr m n r k)
                  (YoungBitableau.toPolynomial k B)))) :
    ∀ p : MvPolynomial (Fin m × Fin n) k,
      Ideal.Quotient.mk (Jr m n r k) p ∈
        Submodule.span k
          (Set.range
            (fun B : YoungBitableau m n =>
              Ideal.Quotient.mk (Jr m n r k)
                (YoungBitableau.toPolynomial k B))) := by
  classical
  let V : Submodule k (Rr m n r k) :=
    Submodule.span k
      (Set.range
        (fun B : YoungBitableau m n =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B)))
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.comap q V
  have hmonomials_top :
      Submodule.span k
        (Set.range
          (fun E : (Fin m × Fin n) →₀ ℕ =>
            MvPolynomial.monomial E (1 : k))) = ⊤ := by
    simpa [MvPolynomial.coe_basisMonomials] using
      (MvPolynomial.basisMonomials (Fin m × Fin n) k).span_eq
  have hW_top : W = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hmonomials_top]
    apply Submodule.span_le.mpr
    rintro p ⟨E, rfl⟩
    change q (MvPolynomial.monomial E (1 : k)) ∈ V
    simpa [q, V] using hmono E
  intro p
  change q p ∈ V
  have hpW : p ∈ W := by
    rw [hW_top]
    trivial
  simpa [W] using hpW

/--
Basis criterion reduced to monomials: to prove the standard-bitableau basis it
is enough to show that every monomial lies in the span of bitableaux, that
larger minors vanish modulo `J_r`, and that the short standard bitableaux are
linearly independent in the quotient.
-/
/- Monomials are spanned, already in the polynomial ring, by products of
`1 × 1` minors, hence by Young bitableaux. -/
theorem monomial_mem_span_youngBitableau_toPolynomial
    {m n : ℕ}
    (k : Type*) [Field k]
    (E : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.monomial E (1 : k) ∈
      Submodule.span k
        (Set.range
          (fun B : YoungBitableau m n =>
            YoungBitableau.toPolynomial k B)) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun vf : Σ v : ℕ, Fin v → Fin m × Fin n =>
          YoungBitableau.toPolynomial k
            (YoungBitableau.oneMinorVec vf.1 vf.2)))
  have hmonoW :
      MvPolynomial.monomial E (1 : k) ∈ W := by
    simpa using
      (MvPolynomial.induction_on_monomial
        (motive := fun p : MvPolynomial (Fin m × Fin n) k => p ∈ W)
        (fun a => by
          have hgen :
              YoungBitableau.toPolynomial k
                  (YoungBitableau.oneMinorVec 0 (Fin.elim0)) ∈ W := by
            exact Submodule.subset_span ⟨⟨0, Fin.elim0⟩, rfl⟩
          have hsmul :
              a • YoungBitableau.toPolynomial k
                (YoungBitableau.oneMinorVec 0 (Fin.elim0)) ∈ W :=
            W.smul_mem a hgen
          simpa [YoungBitableau.toPolynomial_oneMinorVec,
            MvPolynomial.C_eq_smul_one] using hsmul)
        (fun p x hp => by
          refine Submodule.span_induction
            (p := fun y hy => y * MvPolynomial.X x ∈ W)
            ?mem ?zero ?add ?smul hp
          · intro y hy
            rcases hy with ⟨vf, rfl⟩
            rcases vf with ⟨v, f⟩
            have hgen :
                YoungBitableau.toPolynomial k
                    (YoungBitableau.oneMinorVec (v + 1) (Fin.snoc f x)) ∈ W := by
              exact Submodule.subset_span ⟨⟨v + 1, Fin.snoc f x⟩, rfl⟩
            rw [YoungBitableau.toPolynomial_oneMinorVec_snoc] at hgen
            exact hgen
          · simp
          · intro y z hy hz hyX hzX
            simpa [add_mul] using W.add_mem hyX hzX
          · intro a y hy hyX
            simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using W.smul_mem a hyX)
        E (1 : k))
  have hW_le :
      W ≤
        Submodule.span k
          (Set.range
            (fun B : YoungBitableau m n =>
              YoungBitableau.toPolynomial k B)) := by
    rw [Submodule.span_le]
    rintro p ⟨vf, rfl⟩
    exact Submodule.subset_span ⟨YoungBitableau.oneMinorVec vf.1 vf.2, rfl⟩
  exact hW_le hmonoW

/- The polynomial spanning statement for monomials descends to the determinantal
quotient. -/
theorem quotient_monomial_mem_span_youngBitableau
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (E : (Fin m × Fin n) →₀ ℕ) :
    Ideal.Quotient.mk (Jr m n r k)
        (MvPolynomial.monomial E (1 : k)) ∈
      Submodule.span k
        (Set.range
          (fun B : YoungBitableau m n =>
            Ideal.Quotient.mk (Jr m n r k)
              (YoungBitableau.toPolynomial k B))) := by
  classical
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  let Vq : Submodule k (Rr m n r k) :=
    Submodule.span k
      (Set.range
        (fun B : YoungBitableau m n =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B)))
  have hmap :
      ∀ p : MvPolynomial (Fin m × Fin n) k,
        p ∈
            Submodule.span k
              (Set.range
                (fun B : YoungBitableau m n =>
                  YoungBitableau.toPolynomial k B)) →
          q p ∈ Vq := by
    intro p hp
    refine Submodule.span_induction
      (p := fun y hy => q y ∈ Vq)
      ?mem ?zero ?add ?smul hp
    · intro y hy
      rcases hy with ⟨B, rfl⟩
      exact Submodule.subset_span ⟨B, rfl⟩
    · simp [q, Vq]
    · intro y z hy hz hyq hzq
      simpa [map_add] using Vq.add_mem hyq hzq
    · intro a y hy hyq
      simpa [map_smul] using Vq.smul_mem a hyq
  change q (MvPolynomial.monomial E (1 : k)) ∈ Vq
  exact hmap _
    (monomial_mem_span_youngBitableau_toPolynomial k E)

theorem exists_standardBitableau_basis_determinantalRing_of_monomials_span
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (hmono :
      ∀ E : (Fin m × Fin n) →₀ ℕ,
        Ideal.Quotient.mk (Jr m n r k)
            (MvPolynomial.monomial E (1 : k)) ∈
          Submodule.span k
            (Set.range
              (fun B : YoungBitableau m n =>
                Ideal.Quotient.mk (Jr m n r k)
                  (YoungBitableau.toPolynomial k B))))
    (hli :
      LinearIndependent k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))) :
    ∃ b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k),
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1) := by
  exact
    exists_standardBitableau_basis_determinantalRing_of_youngBitableaux_span k r hlarge
      (quotient_polynomial_mem_span_youngBitableau_of_monomials k r hmono)
      hli

/--
After the monomial-spanning step, the standard-bitableau basis follows from
determinantal vanishing of larger minors and linear independence of the short
standard bitableaux in the quotient.
-/
theorem exists_standardBitableau_basis_determinantalRing_of_large_minors_and_linearIndependent
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k)
    (hli :
      LinearIndependent k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))) :
    ∃ b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k),
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1) := by
  exact
    exists_standardBitableau_basis_determinantalRing_of_monomials_span k r hlarge
      (quotient_monomial_mem_span_youngBitableau k r)
      hli

/--
Linear independence in the quotient follows once we know that no nonzero
standard-bitableau expansion supported in length `≤ r` can lie in `J_r`.

This isolates the coefficient-vanishing consequence of straightening uniqueness
and the description of `J_r` by long minors.
-/
theorem standardBitableau_quotient_linearIndependent_of_Jr_coefficients_zero
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (hJ_coeff :
      ∀ c : StandardYoungBitableau m n →₀ k,
        (c.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) ∈
            Jr m n r k →
        ∀ B : StandardYoungBitableau m n,
          YoungBitableau.length B.1 ≤ r → c B = 0) :
    LinearIndependent k
      (fun B : StandardYoungBitableauOfLengthLE m n r =>
        Ideal.Quotient.mk (Jr m n r k)
          (YoungBitableau.toPolynomial k B.1.1)) := by
  classical
  rw [linearIndependent_iff]
  intro c hc
  let emb : StandardYoungBitableauOfLengthLE m n r ↪
      StandardYoungBitableau m n :=
    ⟨fun B => B.1, fun B C h => by
      cases B
      cases C
      simp_all⟩
  let cAll : StandardYoungBitableau m n →₀ k := Finsupp.embDomain emb c
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  have hq_sum :
      q (cAll.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
        =
      Finsupp.linearCombination k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1)) c := by
    let vAll : StandardYoungBitableau m n → Rr m n r k :=
      fun B =>
        Ideal.Quotient.mk (Jr m n r k)
          (YoungBitableau.toPolynomial k B.1)
    have hq_all :
        q (cAll.sum fun B a =>
            MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
          =
        Finsupp.linearCombination k vAll cAll := by
      rw [Finsupp.linearCombination_apply]
      rw [Finsupp.sum, map_sum, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro B hB
      rw [MvPolynomial.C_mul']
      simp [q, vAll]
    calc
      q (cAll.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
          = Finsupp.linearCombination k vAll cAll := hq_all
      _ =
          Finsupp.linearCombination k (vAll ∘ emb) c := by
            simp [cAll]
      _ =
          Finsupp.linearCombination k
            (fun B : StandardYoungBitableauOfLengthLE m n r =>
              Ideal.Quotient.mk (Jr m n r k)
                (YoungBitableau.toPolynomial k B.1.1)) c := by
            rfl
  have hpoly_mem :
      (cAll.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) ∈
          Jr m n r k := by
    have hq_zero :
        q (cAll.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
      rw [hq_sum]
      exact hc
    simpa [q] using (Ideal.Quotient.eq_zero_iff_mem.mp hq_zero)
  have hcAll_zero : cAll = 0 := by
    ext B
    by_cases hshort : YoungBitableau.length B.1 ≤ r
    · exact hJ_coeff cAll hpoly_mem B hshort
    · have hnot_range : B ∉ Set.range emb := by
        rintro ⟨Bshort, hB⟩
        have hlen : YoungBitableau.length B.1 ≤ r := by
          subst B
          exact Bshort.2
        exact hshort hlen
      simpa [cAll] using Finsupp.embDomain_notin_range emb c B hnot_range
  apply Finsupp.embDomain_injective emb
  simpa [cAll] using hcAll_zero

/--
Polynomial-level linear independence of standard bitableaux.  This is the
uniqueness content of the straightening law, isolated for reuse.
-/
theorem standardBitableau_toPolynomial_linearIndependent
    {m n : ℕ}
    (k : Type*) [Field k] :
    LinearIndependent k
      (fun B : StandardYoungBitableau m n =>
        YoungBitableau.toPolynomial k B.1) := by
  classical
  rw [linearIndependent_iff]
  intro c hc
  by_contra hcz
  have hsupp : c.support.Nonempty := by
    by_contra h
    have hs : c.support = ∅ := by
      ext B
      constructor
      · intro hB
        exact False.elim (h ⟨B, hB⟩)
      · intro hB
        simp at hB
    apply hcz
    exact Finsupp.support_eq_empty.mp hs
  rcases Finset.exists_min_image c.support
      (fun B : StandardYoungBitableau m n => YoungBitableau.length B.1)
      hsupp with
    ⟨B₀, hB₀mem, hB₀min⟩
  have hcB₀_ne : c B₀ ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hB₀mem
  let e : ℕ := YoungBitableau.degree B₀.1
  let cf : StandardYoungBitableau m n →₀ k :=
    c.filter fun B => YoungBitableau.degree B.1 = e
  have hcf_rel :
      Finsupp.linearCombination k
        (fun B : StandardYoungBitableau m n =>
          YoungBitableau.toPolynomial k B.1) cf = 0 := by
    have hTzero :
        c.sum (fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
      rw [Finsupp.linearCombination_apply] at hc
      simpa [MvPolynomial.C_mul'] using hc
    have hcomp_zero :
        MvPolynomial.homogeneousComponent e
          (c.sum fun B a =>
            MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0 := by
      rw [hTzero]
      simp
    have hcomp :=
      homogeneousComponent_standardBitableau_finsupp_sum k e c
    rw [hcomp] at hcomp_zero
    rw [Finsupp.linearCombination_apply]
    simpa [cf, MvPolynomial.C_mul'] using hcomp_zero
  have hcfB₀_ne : cf B₀ ≠ 0 := by
    simp [cf, e, hcB₀_ne]
  let a : k := cf B₀
  have ha : a ≠ 0 := hcfB₀_ne
  let c₀ : StandardYoungBitableau m n →₀ k := Finsupp.single B₀ (1 : k)
  let c₁ : StandardYoungBitableau m n →₀ k := c₀ - a⁻¹ • cf
  have hc₀_prop :
      YoungBitableau.toPolynomial k B₀.1 =
        c₀.sum (fun S b =>
          MvPolynomial.C b * YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c₀ S ≠ 0 → YoungBitableau.degree S.1 = YoungBitableau.degree B₀.1)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c₀ S ≠ 0 → YoungBitableau.length B₀.1 ≤ YoungBitableau.length S.1) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [c₀]
    · intro S hS
      have hSB : S = B₀ := by
        by_contra hne
        have : c₀ S = 0 := by simp [c₀, hne]
        exact hS this
      simp [hSB]
    · intro S hS
      have hSB : S = B₀ := by
        by_contra hne
        have : c₀ S = 0 := by simp [c₀, hne]
        exact hS this
      simp [hSB]
  have hc₁_poly :
      YoungBitableau.toPolynomial k B₀.1 =
        c₁.sum (fun S b =>
          MvPolynomial.C b * YoungBitableau.toPolynomial k S.1) := by
    have hlin_c₁ :
        Finsupp.linearCombination k
          (fun S : StandardYoungBitableau m n =>
            YoungBitableau.toPolynomial k S.1) c₁ =
          YoungBitableau.toPolynomial k B₀.1 := by
      dsimp [c₁, c₀]
      rw [map_sub, map_smul, hcf_rel]
      simp
    rw [Finsupp.linearCombination_apply] at hlin_c₁
    simpa [MvPolynomial.C_mul'] using hlin_c₁.symm
  have hc₁_deg :
      ∀ S : StandardYoungBitableau m n,
        c₁ S ≠ 0 → YoungBitableau.degree S.1 = YoungBitableau.degree B₀.1 := by
    intro S hS
    by_cases hSB : S = B₀
    · simp [hSB]
    · have hcfS : cf S ≠ 0 := by
        by_contra hcfS
        have hc₁S : c₁ S = 0 := by
          simp [c₁, c₀, hSB, hcfS]
        exact hS hc₁S
      have hSdeg : YoungBitableau.degree S.1 = e := by
        by_contra hne
        have : cf S = 0 := by simp [cf, hne]
        exact hcfS this
      simpa [e] using hSdeg
  have hc₁_len :
      ∀ S : StandardYoungBitableau m n,
        c₁ S ≠ 0 → YoungBitableau.length B₀.1 ≤ YoungBitableau.length S.1 := by
    intro S hS
    by_cases hSB : S = B₀
    · simp [hSB]
    · have hcfS : cf S ≠ 0 := by
        by_contra hcfS
        have hc₁S : c₁ S = 0 := by
          simp [c₁, c₀, hSB, hcfS]
        exact hS hc₁S
      have hcS : c S ≠ 0 := by
        by_contra hcS
        have : cf S = 0 := by
          by_cases hdeg : YoungBitableau.degree S.1 = e
          · simp [cf, hdeg, hcS]
          · simp [cf, hdeg]
        exact hcfS this
      have hSmem : S ∈ c.support := by
        simpa [Finsupp.mem_support_iff] using hcS
      exact hB₀min S hSmem
  have hc₁_prop :
      YoungBitableau.toPolynomial k B₀.1 =
        c₁.sum (fun S b =>
          MvPolynomial.C b * YoungBitableau.toPolynomial k S.1)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c₁ S ≠ 0 → YoungBitableau.degree S.1 = YoungBitableau.degree B₀.1)
      ∧
      (∀ S : StandardYoungBitableau m n,
        c₁ S ≠ 0 → YoungBitableau.length B₀.1 ≤ YoungBitableau.length S.1) :=
    ⟨hc₁_poly, hc₁_deg, hc₁_len⟩
  rcases straightening_law k B₀.1 with ⟨u, hu, huniq⟩
  have hc₀_eq : c₀ = u := huniq c₀ hc₀_prop
  have hc₁_eq : c₁ = u := huniq c₁ hc₁_prop
  have hsame : c₁ = c₀ := hc₁_eq.trans hc₀_eq.symm
  have hB₀_eval := DFunLike.congr_fun hsame B₀
  have hc₁_B₀ : c₁ B₀ = 0 := by
    simp [c₁, c₀, a, ha]
  have hc₀_B₀ : c₀ B₀ = 1 := by
    simp [c₀]
  have hzero_one : (0 : k) = 1 := by
    simp [hc₁_B₀, hc₀_B₀] at hB₀_eval
  exact zero_ne_one hzero_one

lemma youngBitableau_toPolynomial_mem_long_standard_span_of_length_lt
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (B : YoungBitableau m n)
    (hB : r < YoungBitableau.length B) :
    YoungBitableau.toPolynomial k B ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              r < YoungBitableau.length
                ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n))) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : { S : StandardYoungBitableau m n //
            r < YoungBitableau.length
              ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
          YoungBitableau.toPolynomial k
            ((S : StandardYoungBitableau m n) : YoungBitableau m n)))
  rcases straightening_law k B with
    ⟨c, ⟨hpoly, _hdeg, hlength⟩, _huniq⟩
  rw [hpoly]
  change
    (c.sum fun S a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k S.1) ∈ W
  rw [Finsupp.sum]
  refine W.sum_mem ?_
  intro S hS
  by_cases ha : c S = 0
  · simp [ha]
  · have hlongS : r < YoungBitableau.length S.1 :=
      lt_of_lt_of_le hB (hlength S ha)
    have hgen :
        YoungBitableau.toPolynomial k S.1 ∈ W := by
      exact Submodule.subset_span
        ⟨⟨S, hlongS⟩, rfl⟩
    simpa [MvPolynomial.C_mul'] using W.smul_mem (c S) hgen

lemma long_standard_span_mul_X_mem
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    {p : MvPolynomial (Fin m × Fin n) k}
    (hp : p ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              r < YoungBitableau.length
                ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n))))
    (x : Fin m × Fin n) :
    p * MvPolynomial.X x ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              r < YoungBitableau.length
                ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n))) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : { S : StandardYoungBitableau m n //
            r < YoungBitableau.length
              ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
          YoungBitableau.toPolynomial k
            ((S : StandardYoungBitableau m n) : YoungBitableau m n)))
  change p ∈ W at hp
  change p * MvPolynomial.X x ∈ W
  refine Submodule.span_induction
    (p := fun y _hy => y * MvPolynomial.X x ∈ W)
    ?mem ?zero ?add ?smul hp
  · intro y hy
    rcases hy with ⟨S, rfl⟩
    have hlongSnoc :
        r < YoungBitableau.length
          (YoungBitableau.snocOneMinor
            ((S : StandardYoungBitableau m n) : YoungBitableau m n) x) :=
      lt_of_lt_of_le S.2
        (YoungBitableau.length_le_length_snocOneMinor
          ((S : StandardYoungBitableau m n) : YoungBitableau m n) x)
    have hmem :=
      youngBitableau_toPolynomial_mem_long_standard_span_of_length_lt k r
        (YoungBitableau.snocOneMinor
          ((S : StandardYoungBitableau m n) : YoungBitableau m n) x)
        hlongSnoc
    simpa [W, YoungBitableau.toPolynomial_snocOneMinor] using hmem
  · simp [W]
  · intro y z _hy _hz hyX hzX
    simpa [add_mul] using W.add_mem hyX hzX
  · intro a y _hy hyX
    simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using W.smul_mem a hyX

lemma long_standard_span_mul_mem
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    {p q : MvPolynomial (Fin m × Fin n) k}
    (hp : p ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              r < YoungBitableau.length
                ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n)))) :
    p * q ∈
      Submodule.span k
        (Set.range
          (fun S : { S : StandardYoungBitableau m n //
              r < YoungBitableau.length
                ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n))) := by
  classical
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : { S : StandardYoungBitableau m n //
            r < YoungBitableau.length
              ((S : StandardYoungBitableau m n) : YoungBitableau m n) } =>
          YoungBitableau.toPolynomial k
            ((S : StandardYoungBitableau m n) : YoungBitableau m n)))
  change p ∈ W at hp
  change p * q ∈ W
  induction q using MvPolynomial.induction_on with
  | C a =>
      simpa [MvPolynomial.smul_eq_C_mul, mul_comm] using W.smul_mem a hp
  | add y z hy hz =>
      simpa [mul_add] using W.add_mem hy hz
  | mul_X q x hq =>
      simpa [mul_assoc] using
        long_standard_span_mul_X_mem k r (p := p * q) hq x

/--
Every element of `J_r` has a standard-bitableau expansion supported only on
standard bitableaux of length strictly larger than `r`.

This is the ideal-generation part of the straightening argument: each generator
contains an `(r + 1)`-minor, and straightening cannot decrease length.
-/
theorem exists_long_standardBitableau_expansion_of_mem_Jr
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (p : MvPolynomial (Fin m × Fin n) k)
    (hp : p ∈ Jr m n r k) :
    ∃ d : StandardYoungBitableau m n →₀ k,
      p =
        (d.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
      ∧
      ∀ B : StandardYoungBitableau m n,
        YoungBitableau.length B.1 ≤ r → d B = 0 := by
  classical
  let LongStd :=
    { S : StandardYoungBitableau m n //
        r < YoungBitableau.length ((S : StandardYoungBitableau m n) : YoungBitableau m n) }
  let W : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
    Submodule.span k
      (Set.range
        (fun S : LongStd =>
          YoungBitableau.toPolynomial k
            ((S : StandardYoungBitableau m n) : YoungBitableau m n)))
  have hpW : p ∈ W := by
    rw [Jr, detIdeal_eq_span_range] at hp
    change p ∈ W
    refine Submodule.span_induction
      (p := fun y _hy => y ∈ W)
      ?mem ?zero ?add ?smul hp
    · intro y hy
      rcases hy with ⟨I, rfl⟩
      have hlong :
          r < YoungBitableau.length
            (YoungBitableau.oneMinor (Nat.succ_pos r) I) := by
        simp [YoungBitableau.length_oneMinor]
      have hmem :=
        youngBitableau_toPolynomial_mem_long_standard_span_of_length_lt k r
          (YoungBitableau.oneMinor (Nat.succ_pos r) I)
          hlong
      simpa [W, LongStd, YoungBitableau.toPolynomial_oneMinor] using hmem
    · simp [W]
    · intro y z _hy _hz hyW hzW
      exact W.add_mem hyW hzW
    · intro q y _hy hyW
      have hymul :
          y * q ∈ W := by
        simpa [W, LongStd] using
          long_standard_span_mul_mem k r (p := y)
            (by simpa [W, LongStd] using hyW)
      simpa [mul_comm] using hymul
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hpW with ⟨e, he⟩
  let emb : LongStd ↪ StandardYoungBitableau m n :=
    ⟨fun S => S.1, by
      intro S T h
      cases S
      cases T
      simp_all⟩
  let d : StandardYoungBitableau m n →₀ k := Finsupp.embDomain emb e
  refine ⟨d, ?hpoly, ?hshort⟩
  · have hsum :
        d.sum (fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1)
          =
        e.sum (fun S a =>
          MvPolynomial.C a *
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n)) := by
      let vAll : StandardYoungBitableau m n →
          MvPolynomial (Fin m × Fin n) k :=
        fun B => YoungBitableau.toPolynomial k B.1
      have hlin :
          Finsupp.linearCombination k vAll d =
            Finsupp.linearCombination k (vAll ∘ emb) e := by
        simp [d]
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply] at hlin
      simpa [vAll, MvPolynomial.C_mul'] using hlin
    have he' :
        e.sum (fun S a =>
          MvPolynomial.C a *
            YoungBitableau.toPolynomial k
              ((S : StandardYoungBitableau m n) : YoungBitableau m n)) = p := by
      simpa [MvPolynomial.C_mul'] using he
    rw [← hsum] at he'
    exact he'.symm
  · intro B hB
    have hnot_range : B ∉ Set.range emb := by
      rintro ⟨S, hS⟩
      have hB_eq : B = emb S := hS.symm
      subst B
      exact (not_lt_of_ge hB) S.2
    simpa [d] using Finsupp.embDomain_notin_range emb e B hnot_range

/--
Coefficient vanishing for linear independence: an element of `J_r` written in
standard bitableaux has no coefficients on standard bitableaux of length at
most `r`.

This is proved from the uniqueness clause in
`straightening_law`, after rewriting elements of `J_r` as sums of bitableaux
containing an `(r + 1)`-minor.
-/
theorem standardBitableau_short_coefficients_zero_of_mem_Jr
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (c : StandardYoungBitableau m n →₀ k)
    (hc :
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) ∈
          Jr m n r k)
    (B : StandardYoungBitableau m n)
    (hB : YoungBitableau.length B.1 ≤ r) :
    c B = 0 := by
  classical
  let p : MvPolynomial (Fin m × Fin n) k :=
    c.sum fun B a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1
  rcases exists_long_standardBitableau_expansion_of_mem_Jr k r p hc with
    ⟨d, hd_eq, hd_short⟩
  let v : StandardYoungBitableau m n →
      MvPolynomial (Fin m × Fin n) k :=
    fun B => YoungBitableau.toPolynomial k B.1
  have hlin :
      Finsupp.linearCombination k v (c - d) = 0 := by
    rw [map_sub]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
    simp_rw [← MvPolynomial.C_mul']
    change
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) -
        (d.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0
    change p -
        (d.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1) = 0
    rw [hd_eq]
    exact sub_self _
  have hcd : c - d = 0 :=
    (linearIndependent_iff.mp
      (standardBitableau_toPolynomial_linearIndependent k) (c - d)) hlin
  have hcoeff : c B = d B := by
    have happly := DFunLike.congr_fun hcd B
    simpa using sub_eq_zero.mp happly
  rw [hcoeff]
  exact hd_short B hB

/--
The standard bitableaux of length at most `r` form a `K`-basis of the
determinantal ring `K[X] / J_r`.
-/
theorem exists_standardBitableau_basis_determinantalRing
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ) :
    ∃ b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k),
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1) := by
  classical
  -- Larger minors vanish modulo `J_r` by determinantal-ideal nesting.
  have hlarge :
      ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t),
        r < t → genericMinor k I ∈ Jr m n r k := by
    intro t I ht
    have hrt : r + 1 ≤ t := Nat.succ_le_iff.mpr ht
    simpa [Jr] using
      genericMinor_mem_detIdeal_of_le k hrt I
  -- Use linear independence of the standard bitableaux whose length is at most
  -- `r` in the determinantal quotient.
  have hli :
      LinearIndependent k
        (fun B : StandardYoungBitableauOfLengthLE m n r =>
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1)) := by
    exact
      standardBitableau_quotient_linearIndependent_of_Jr_coefficients_zero k r
        (standardBitableau_short_coefficients_zero_of_mem_Jr k r)
  -- All spanning work has now been discharged by the preceding bridge lemmas:
  -- monomials are spanned by `1 × 1` bitableaux, straightening replaces arbitrary
  -- bitableaux by standard ones, and long standard bitableaux vanish modulo `J_r`.
  exact
    exists_standardBitableau_basis_determinantalRing_of_large_minors_and_linearIndependent
      k r hlarge hli


end Determinantal
