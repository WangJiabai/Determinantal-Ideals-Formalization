/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.Sturmfels_lemma

/-!
# Minor terms for determinantal ideals

This file develops the exponent-vector and monomial-term language attached to a
`t × t` minor of the generic matrix.

It defines:

* `diagExp` / `diagMonomial`: the diagonal term;
* `permExp` / `permCoeff` / `permTerm`: the signed permutation terms in the
  determinant expansion;
* pointwise formulas for these exponent vectors;
* support, cardinality, and total-degree lemmas;
* the determinant expansion of a minor as a sum of permutation terms.
-/

open scoped BigOperators

namespace Determinantal

section Exponents

variable {m n t : ℕ}

/-- The exponent vector of the diagonal monomial of a `t × t` minor. -/
noncomputable def diagExp (I : MinorIndex m n t) : (Fin m × Fin n) →₀ ℕ :=
  ∑ k : Fin t, Finsupp.single (I.row k, I.col k) 1

/-- The exponent vector of the permutation term corresponding to `σ` in the determinant
expansion of a `t × t` minor. -/
noncomputable def permExp
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) : (Fin m × Fin n) →₀ ℕ :=
  ∑ k : Fin t, Finsupp.single (I.row k, I.col (σ k)) 1

noncomputable def antidiagExp (I : MinorIndex m n t) :
    (Fin m × Fin n) →₀ ℕ :=
  ∑ k : Fin t, Finsupp.single (I.row k, I.col (k.rev)) 1

@[simp] theorem permExp_one (I : MinorIndex m n t) :
    permExp I (1 : Equiv.Perm (Fin t)) = diagExp I := by
  simp [permExp, diagExp]

@[simp] theorem permExp_refl (I : MinorIndex m n t) :
    permExp I (Equiv.refl (Fin t)) = diagExp I := by
  simp [permExp, diagExp]


end Exponents

section MonomialTerms

variable {k : Type*} [CommSemiring k]
variable {m n t : ℕ}

/-- The diagonal monomial attached to a minor. -/
noncomputable def diagMonomial (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.monomial (diagExp I) 1

noncomputable def diagTerm (I : MinorIndex m n t) :
  MvPolynomial (Fin m × Fin n) k :=
  ∏ i : Fin t, (Matrix.diag (Matrix.submatrix (genericMatrix m n k) I.row I.col)) i

@[simp] theorem diagMonomial_def (I : MinorIndex m n t) :
  diagMonomial I = MvPolynomial.monomial (diagExp I) (1 : k) :=
  rfl

@[simp] theorem diagTerm_def (I : MinorIndex m n t) :
  diagTerm I = ∏ i : Fin t, (Matrix.diag (Matrix.submatrix (genericMatrix m n k) I.row I.col)) i :=
  rfl

/-- The anti-diagonal monomial attached to a minor. -/
noncomputable def antidiagMonomial (I : MinorIndex m n t) :
  MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.monomial (antidiagExp I) 1

@[simp] theorem antidiagMonomial_def (I : MinorIndex m n t) :
  antidiagMonomial I = MvPolynomial.monomial (antidiagExp I) 1 :=
  rfl

lemma diagTerm_eq_diagMonomial (I : MinorIndex m n t) :
  diagTerm (k := k) I = diagMonomial I:=by
  classical
  unfold diagTerm diagMonomial
  change
      (∏ i : Fin t,
        MvPolynomial.X (I.row i, I.col i)) =
      MvPolynomial.monomial (diagExp I) (1 : k)
  rw [diagExp]
  exact
    Eq.symm (MvPolynomial.monomial_sum_one Finset.univ fun i ↦ Finsupp.single (I.row i, I.col i) 1)

end MonomialTerms

section SignedPermutationTerms

variable {k : Type*} [CommRing k]
variable {m n t : ℕ}

/-- The coefficient `sign σ`, viewed in the coefficient ring. -/
noncomputable def permCoeff (σ : Equiv.Perm (Fin t)) : k :=
  (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : k)

/-- The signed permutation term occurring in the determinant expansion of a minor. -/
noncomputable def permTerm
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.monomial (permExp I σ) (permCoeff (k := k) σ)

@[simp] theorem permCoeff_one :
    permCoeff (k := k) (1 : Equiv.Perm (Fin t)) = 1 := by
  simp [permCoeff]

@[simp] theorem permTerm_one_eq_diagMonomial (I : MinorIndex m n t) :
    permTerm I (1 : Equiv.Perm (Fin t)) = diagMonomial (k := k) I := by
  simp [permTerm, diagMonomial, permCoeff, permExp_one]

@[simp] lemma coeff_permTerm
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    (c : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.coeff c (permTerm I σ) =
      if c = permExp I σ then permCoeff (k := k) σ else 0 := by
  simp [permTerm,eq_comm]


end SignedPermutationTerms

section PointwiseExponentLemmas

variable {m n t : ℕ}

/-- Pointwise formula for `diagExp`. -/
lemma diagExp_apply
    (I : MinorIndex m n t) (a : Fin m) (b : Fin n) :
    diagExp I (a, b) = if ∃ i : Fin t, I.row i = a ∧ I.col i = b then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col i = b
  · rcases h with ⟨i, hrow, hcol⟩
    have hpair :
        ∀ j : Fin t, ((I.row j, I.col j) = (a, b)) ↔ j = i := by
      intro j
      constructor
      · intro hj
        have hjrow : I.row j = I.row i := by
          calc
            I.row j = a := by simpa using congrArg Prod.fst hj
            _ = I.row i := hrow.symm
        exact I.row.injective hjrow
      · intro hj
        subst hj
        simp [hrow, hcol]
    simp [diagExp, Finsupp.single_apply, hpair]
    subst hrow hcol
    simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, and_self, implies_true, exists_eq]
  · have hpairFalse :
        ∀ j : Fin t, (I.row j, I.col j) ≠ (a, b) := by
      intro j hj
      exact h ⟨j, by simpa using congrArg Prod.fst hj, by simpa using congrArg Prod.snd hj⟩
    simp only [diagExp, Finsupp.coe_finset_sum, Finset.sum_apply, ne_eq, hpairFalse,
      not_false_eq_true, Finsupp.single_eq_of_ne', Finset.sum_const_zero, h, ↓reduceIte]

@[simp] lemma diagExp_apply_diag
    (I : MinorIndex m n t) (i : Fin t) :
    diagExp I (I.row i, I.col i) = 1 := by
  rw [diagExp_apply]
  exact if_pos ⟨i, rfl, rfl⟩

/-- Pointwise formula for `permExp`. -/
lemma permExp_apply
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    (a : Fin m) (b : Fin n) :
    permExp I σ (a, b) =
      if ∃ i : Fin t, I.row i = a ∧ I.col (σ i) = b then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col (σ i) = b
  · rcases h with ⟨i, hrow, hcol⟩
    have hpair :
        ∀ j : Fin t, ((I.row j, I.col (σ j)) = (a, b)) ↔ j = i := by
      intro j
      constructor
      · intro hj
        have hjrow : I.row j = I.row i := by
          calc
            I.row j = a := by simpa using congrArg Prod.fst hj
            _ = I.row i := hrow.symm
        exact I.row.injective hjrow
      · intro hj
        subst hj
        simp [hrow, hcol]
    simp [permExp, Finsupp.single_apply, hpair]
    subst hrow hcol
    simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, and_self, implies_true, exists_eq]
  · have hpairFalse :
        ∀ j : Fin t, (I.row j, I.col (σ j)) ≠ (a, b) := by
      intro j hj
      exact h ⟨j, by simpa using congrArg Prod.fst hj, by simpa using congrArg Prod.snd hj⟩
    simp [permExp, h, hpairFalse]

@[simp] lemma permExp_apply_image
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    permExp I σ (I.row i, I.col (σ i)) = 1 := by
  rw [permExp_apply]
  exact if_pos ⟨i, rfl, rfl⟩

/-- At a diagonal variable corresponding to a moved index, the permutation exponent vanishes. -/
lemma permExp_apply_diag_eq_zero
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    {i : Fin t}
    (hmove : σ i ≠ i)
    (_hfix : ∀ j : Fin t, j < i → σ j = j) :
    permExp I σ (I.row i, I.col i) = 0 := by
  rw [permExp_apply]
  refine if_neg ?_
  rintro ⟨j, hjrow, hjcol⟩
  have hj : j = i := I.row.injective hjrow
  subst hj
  exact hmove (I.col.injective hjcol)

/-- At a diagonal variable corresponding to a fixed index, the permutation exponent is `1`. -/
lemma permExp_apply_diag_of_fix
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    {i : Fin t} (hfixi : σ i = i) :
    permExp I σ (I.row i, I.col i) = 1 := by
  rw [permExp_apply]
  refine if_pos ?_
  exact ⟨i, rfl, by simp [hfixi]⟩

end PointwiseExponentLemmas

section PermutationCombinatorics

variable {t : ℕ}

/-- Every nontrivial permutation moves a least index. -/
lemma exists_min_moved
    {σ : Equiv.Perm (Fin t)} (hσ : σ ≠ 1) :
    ∃ i : Fin t, σ i ≠ i ∧ ∀ j : Fin t, j < i → σ j = j := by
  classical
  let s : Finset (Fin t) := Finset.univ.filter fun i => σ i ≠ i
  have hs : s.Nonempty := by
    by_contra hs'
    apply hσ
    ext i
    have hi_not : i ∉ s := by
      exact forall_not_of_not_exists hs' i
    simp_all only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
      Finset.mem_univ, Decidable.not_not, forall_const, not_true_eq_false,
      Finset.filter_false, Finset.notMem_empty, not_false_eq_true, Equiv.Perm.coe_one, id_eq, s]
  refine ⟨s.min' hs, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
  · intro j hj
    by_contra hj'
    have hjmem : j ∈ s := by
      simp [s, hj']
    exact not_lt_of_ge (Finset.min'_le s j hjmem) hj

/-- The least moved index is mapped to a strictly larger index. -/
lemma min_moved_lt_image
    {σ : Equiv.Perm (Fin t)} {i : Fin t}
    (hmove : σ i ≠ i)
    (hfix : ∀ j : Fin t, j < i → σ j = j) :
    i < σ i := by
  by_contra h
  have hle : σ i ≤ i := le_of_not_gt h
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hσσ : σ (σ i) = σ i := hfix (σ i) hlt
    exact hmove (σ.injective hσσ)
  · exact hmove heq

end PermutationCombinatorics

section ExponentInjectivity

variable {m n t : ℕ}

/-- The map `σ ↦ permExp I σ` is injective. -/
theorem permExp_injective
    (I : MinorIndex m n t) :
    Function.Injective (permExp I) := by
  intro σ τ hστ
  ext i
  have hσ : permExp I σ (I.row i, I.col (σ i)) = 1 := by
    simp
  have hτ : permExp I τ (I.row i, I.col (σ i)) = 1 := by
    rw [← hστ]
    exact hσ
  rw [permExp_apply] at hτ
  have hex : ∃ j : Fin t, I.row j = I.row i ∧ I.col (τ j) = I.col (σ i) := by
    by_contra hno
    simp at hτ
    simp_all only [EmbeddingLike.apply_eq_iff_eq, exists_eq_left, not_true_eq_false]
  rcases hex with ⟨j, hjrow, hjcol⟩
  have hj : j = i := I.row.injective hjrow
  subst hj
  simp_all only [EmbeddingLike.apply_eq_iff_eq, exists_eq_left,
    ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]

end ExponentInjectivity

section SupportAndDegree

variable {m n t : ℕ}

/-- The support of `diagExp` is the set of diagonal variables of the minor. -/
lemma support_diagExp
    (I : MinorIndex m n t) :
    (diagExp I).support =
      Finset.image (fun i : Fin t => (I.row i, I.col i)) Finset.univ := by
  classical
  ext x
  rcases x with ⟨a, b⟩
  simp [Finsupp.mem_support_iff, diagExp_apply]

/-- The support of `permExp I σ` is the set of variables occurring in the corresponding
permutation term. -/
lemma support_permExp
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    (permExp I σ).support =
      Finset.image (fun i : Fin t => (I.row i, I.col (σ i))) Finset.univ := by
  classical
  ext x
  rcases x with ⟨a, b⟩
  simp [Finsupp.mem_support_iff, permExp_apply]

/-- The support of `diagExp` has cardinality `t`. -/
lemma diagExp_card_support
    (I : MinorIndex m n t) :
    (diagExp I).support.card = t := by
  classical
  rw [support_diagExp]
  have hinj : Function.Injective (fun i : Fin t => (I.row i, I.col i)) := by
    intro i j hij
    exact I.row.injective (by simpa using congrArg Prod.fst hij)
  simpa using Finset.card_image_of_injective (s := Finset.univ) hinj

/-- The support of `permExp I σ` has cardinality `t`. -/
lemma permExp_card_support
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    (permExp I σ).support.card = t := by
  classical
  rw [support_permExp]
  have hinj : Function.Injective (fun i : Fin t => (I.row i, I.col (σ i))) := by
    intro i j hij
    exact I.row.injective (by simpa using congrArg Prod.fst hij)
  simpa using Finset.card_image_of_injective Finset.univ hinj

/-- The total degree of the diagonal exponent vector is `t`. -/
lemma diagExp_totalDegree
    (I : MinorIndex m n t) :
    (diagExp I).sum (fun _ e => e) = t := by
  classical
  unfold Finsupp.sum
  rw [support_diagExp]
  have hinj : Function.Injective (fun i : Fin t => (I.row i, I.col i)) := by
    intro i j hij
    exact I.row.injective (by simpa using congrArg Prod.fst hij)
  rw [Finset.sum_image]
  · simp [diagExp_apply_diag]
  · intro i _ j _ hij
    exact hinj hij

/-- The total degree of any permutation exponent vector is `t`. -/
lemma permExp_totalDegree
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    (permExp I σ).sum (fun _ e => e) = t := by
  classical
  unfold Finsupp.sum
  rw [support_permExp]
  have hinj : Function.Injective (fun i : Fin t => (I.row i, I.col (σ i))) := by
    intro i j hij
    exact I.row.injective (by simpa using congrArg Prod.fst hij)
  rw [Finset.sum_image]
  · simp [permExp_apply_image]
  · intro i _ j _ hij
    exact hinj hij

end SupportAndDegree

section DeterminantExpansion

variable {k : Type*} [CommRing k]
variable {m n t : ℕ}

/-- Determinant expansion of a minor as a sum of signed permutation monomials. -/
theorem minor_eq_sum_permTerm
    (I : MinorIndex m n t) :
    genericMinor (k := k) I =
      ∑ σ : Equiv.Perm (Fin t), permTerm I σ := by
  classical
  let M : Matrix (Fin t) (Fin t) (MvPolynomial (Fin m × Fin n) k) :=
    Matrix.submatrix (genericMatrix m n k) I.row I.col
  calc
    genericMinor I = M.det := by
      rfl
    _ = M.transpose.det := by
      simp [Matrix.det_transpose]
    _ = ∑ σ : Equiv.Perm (Fin t),
          ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin m × Fin n) k)) *
            ∏ i : Fin t, M.transpose (σ i) i := by
      rw [Matrix.det_apply']
    _ = ∑ σ : Equiv.Perm (Fin t), permTerm I σ := by
      refine Finset.sum_congr rfl ?_
      intro σ hσ
      change ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin m × Fin n) k)) *
          ∏ i : Fin t,
            (MvPolynomial.X (I.row i, I.col (σ i)) : MvPolynomial (Fin m × Fin n) k) =
          permTerm I σ
      rw [permTerm]
      change MvPolynomial.C (permCoeff σ) *
          ∏ i : Fin t,
            (MvPolynomial.monomial
              (Finsupp.single (I.row i, I.col (σ i)) 1) 1 :
                MvPolynomial (Fin m × Fin n) k) =
        MvPolynomial.monomial (permExp I σ) (permCoeff σ)
      symm
      simpa [permExp, permCoeff, MvPolynomial.X] using
        (MvPolynomial.monomial_sum_index
          (s := Finset.univ)
          (f := fun i : Fin t => Finsupp.single (I.row i, I.col (σ i)) 1)
          (a := permCoeff σ))

/-- The coefficient of `minor I` at the exponent vector `permExp I σ` is `permCoeff σ`. -/
lemma coeff_minor_permExp
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)) :
    MvPolynomial.coeff (permExp I σ) (genericMinor (k := k) I) = permCoeff σ := by
  classical
  rw [minor_eq_sum_permTerm]
  rw [MvPolynomial.coeff_sum]
  simp [coeff_permTerm, (permExp_injective I).eq_iff]

end DeterminantExpansion

/-- A square minor with arbitrary row and column maps.

Unlike `MinorIndex`, the maps are not required to be strictly increasing.
This is the right workspace for Laplace relations: exchange terms may have
repeated rows or columns, in which case the determinant is zero.  Nonzero
terms can later be promoted back to honest `MinorIndex` terms after proving
the row and column maps are injective. -/
structure RawMinorIndex (m n t : ℕ) where
  row : Fin t → Fin m
  col : Fin t → Fin n

namespace RawMinorIndex

noncomputable def toPolynomial {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t) : MvPolynomial (Fin m × Fin n) k :=
  Matrix.det <| Matrix.submatrix (genericMatrix m n k) R.row R.col

def ofMinorIndex {m n t : ℕ} (I : MinorIndex m n t) :
    RawMinorIndex m n t where
  row := I.row
  col := I.col

@[simp] lemma toPolynomial_ofMinorIndex {m n t : ℕ}
    {k : Type*} [CommRing k]
    (I : MinorIndex m n t) :
    RawMinorIndex.toPolynomial (k := k) (RawMinorIndex.ofMinorIndex I) =
      genericMinor (k := k) I := by
  rfl

noncomputable def rowContent {m n t : ℕ}
    (R : RawMinorIndex m n t) : Fin m →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (R.row a) 1

noncomputable def colContent {m n t : ℕ}
    (R : RawMinorIndex m n t) : Fin n →₀ ℕ :=
  ∑ a : Fin t, Finsupp.single (R.col a) 1

@[simp] lemma rowContent_ofMinorIndex {m n t : ℕ}
    (I : MinorIndex m n t) :
    RawMinorIndex.rowContent (RawMinorIndex.ofMinorIndex I) =
      MinorIndex.rowContent I := by
  rfl

@[simp] lemma colContent_ofMinorIndex {m n t : ℕ}
    (I : MinorIndex m n t) :
    RawMinorIndex.colContent (RawMinorIndex.ofMinorIndex I) =
      MinorIndex.colContent I := by
  rfl

lemma heq_of_cast_apply_eq {m n t u : ℕ} (h : t = u)
    {R : RawMinorIndex m n t} {S : RawMinorIndex m n u}
    (hrow : ∀ a : Fin u, R.row (Fin.cast h.symm a) = S.row a)
    (hcol : ∀ a : Fin u, R.col (Fin.cast h.symm a) = S.col a) :
    HEq R S := by
  cases h
  apply heq_of_eq
  cases R with
  | mk Rrow Rcol =>
      cases S with
      | mk Srow Scol =>
          simp only [Fin.cast_eq_self] at hrow hcol
          cases funext hrow
          cases funext hcol
          rfl

lemma rowContent_total {m n t : ℕ} (R : RawMinorIndex m n t) :
    (∑ i : Fin m, RawMinorIndex.rowContent R i) = t := by
  classical
  simp only [rowContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

lemma colContent_total {m n t : ℕ} (R : RawMinorIndex m n t) :
    (∑ j : Fin n, RawMinorIndex.colContent R j) = t := by
  classical
  simp only [colContent, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

lemma toPolynomial_eq_zero_of_row_eq {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t) {a b : Fin t}
    (hab : a ≠ b) (hrow : R.row a = R.row b) :
    RawMinorIndex.toPolynomial (k := k) R = 0 := by
  classical
  unfold RawMinorIndex.toPolynomial
  exact Matrix.det_zero_of_row_eq hab (by
    ext c
    simp [Matrix.submatrix_apply, hrow])

lemma toPolynomial_eq_zero_of_col_eq {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t) {a b : Fin t}
    (hab : a ≠ b) (hcol : R.col a = R.col b) :
    RawMinorIndex.toPolynomial (k := k) R = 0 := by
  classical
  unfold RawMinorIndex.toPolynomial
  exact Matrix.det_zero_of_column_eq hab (by
    intro r
    simp [Matrix.submatrix_apply, hcol])

lemma toPolynomial_eq_zero_of_not_injective_row {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t)
    (hrow : ¬ Function.Injective R.row) :
    RawMinorIndex.toPolynomial (k := k) R = 0 := by
  classical
  rw [Function.Injective] at hrow
  push_neg at hrow
  rcases hrow with ⟨a, b, heq, hne⟩
  exact R.toPolynomial_eq_zero_of_row_eq hne heq

lemma toPolynomial_eq_zero_of_not_injective_col {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t)
    (hcol : ¬ Function.Injective R.col) :
    RawMinorIndex.toPolynomial (k := k) R = 0 := by
  classical
  rw [Function.Injective] at hcol
  push_neg at hcol
  rcases hcol with ⟨a, b, heq, hne⟩
  exact R.toPolynomial_eq_zero_of_col_eq hne heq

/-- Promote a raw minor whose row and column maps are already strictly
increasing to an honest `MinorIndex`.  This is the no-sign bridge; a later
sorting bridge can reduce arbitrary injective raw minors to this case. -/
def toMinorIndexOfStrictMono {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col) :
    MinorIndex m n t where
  row := OrderEmbedding.ofStrictMono R.row hrow
  col := OrderEmbedding.ofStrictMono R.col hcol

@[simp] lemma toMinorIndexOfStrictMono_row {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col)
    (i : Fin t) :
    (R.toMinorIndexOfStrictMono hrow hcol).row i = R.row i := rfl

@[simp] lemma toMinorIndexOfStrictMono_col {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col)
    (i : Fin t) :
    (R.toMinorIndexOfStrictMono hrow hcol).col i = R.col i := rfl

@[simp] lemma of_toMinorIndexOfStrictMono {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col) :
    RawMinorIndex.ofMinorIndex (R.toMinorIndexOfStrictMono hrow hcol) = R := by
  cases R
  rfl

lemma toPolynomial_toMinorIndexOfStrictMono {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col) :
    genericMinor (k := k) (R.toMinorIndexOfStrictMono hrow hcol) =
      RawMinorIndex.toPolynomial (k := k) R := by
  rfl

@[simp] lemma rowContent_toMinorIndexOfStrictMono {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col) :
    MinorIndex.rowContent (R.toMinorIndexOfStrictMono hrow hcol) =
      RawMinorIndex.rowContent R := by
  rfl

@[simp] lemma colContent_toMinorIndexOfStrictMono {m n t : ℕ}
    (R : RawMinorIndex m n t)
    (hrow : StrictMono R.row) (hcol : StrictMono R.col) :
    MinorIndex.colContent (R.toMinorIndexOfStrictMono hrow hcol) =
      RawMinorIndex.colContent R := by
  rfl

def permute {m n t : ℕ} (R : RawMinorIndex m n t)
    (ρ κ : Equiv.Perm (Fin t)) : RawMinorIndex m n t where
  row := R.row ∘ ρ
  col := R.col ∘ κ

@[simp] lemma permute_row {m n t : ℕ} (R : RawMinorIndex m n t)
    (ρ κ : Equiv.Perm (Fin t)) (i : Fin t) :
    (R.permute ρ κ).row i = R.row (ρ i) := rfl

@[simp] lemma permute_col {m n t : ℕ} (R : RawMinorIndex m n t)
    (ρ κ : Equiv.Perm (Fin t)) (i : Fin t) :
    (R.permute ρ κ).col i = R.col (κ i) := rfl

lemma toPolynomial_permute {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t)
    (ρ κ : Equiv.Perm (Fin t)) :
    RawMinorIndex.toPolynomial (k := k) (R.permute ρ κ) =
      (Equiv.Perm.sign ρ : MvPolynomial (Fin m × Fin n) k) *
        (Equiv.Perm.sign κ : MvPolynomial (Fin m × Fin n) k) *
        RawMinorIndex.toPolynomial (k := k) R := by
  classical
  unfold RawMinorIndex.toPolynomial RawMinorIndex.permute
  change Matrix.det
      ((Matrix.submatrix (genericMatrix m n k) R.row R.col).submatrix ρ κ) =
    (Equiv.Perm.sign ρ : MvPolynomial (Fin m × Fin n) k) *
      (Equiv.Perm.sign κ : MvPolynomial (Fin m × Fin n) k) *
      Matrix.det (Matrix.submatrix (genericMatrix m n k) R.row R.col)
  let M : Matrix (Fin t) (Fin t) (MvPolynomial (Fin m × Fin n) k) :=
    Matrix.submatrix (genericMatrix m n k) R.row R.col
  have hsub :
      M.submatrix ρ κ = (M.submatrix ρ id).submatrix id κ := by
    ext i j
    rfl
  calc
    Matrix.det (M.submatrix ρ κ)
        = Matrix.det ((M.submatrix ρ id).submatrix id κ) := by rw [hsub]
    _ = (Equiv.Perm.sign κ : MvPolynomial (Fin m × Fin n) k) *
          Matrix.det (M.submatrix ρ id) := by
          rw [Matrix.det_permute']
    _ = (Equiv.Perm.sign κ : MvPolynomial (Fin m × Fin n) k) *
          ((Equiv.Perm.sign ρ : MvPolynomial (Fin m × Fin n) k) *
            Matrix.det M) := by
          rw [Matrix.det_permute]
    _ = (Equiv.Perm.sign ρ : MvPolynomial (Fin m × Fin n) k) *
          (Equiv.Perm.sign κ : MvPolynomial (Fin m × Fin n) k) *
            Matrix.det M := by
          ring

lemma rowContent_permute {m n t : ℕ}
    (R : RawMinorIndex m n t) (ρ κ : Equiv.Perm (Fin t)) :
    RawMinorIndex.rowContent (R.permute ρ κ) =
      RawMinorIndex.rowContent R := by
  classical
  unfold RawMinorIndex.rowContent RawMinorIndex.permute
  simpa [Function.comp_apply] using
    (Fintype.sum_equiv ρ
      (fun i : Fin t => Finsupp.single (R.row (ρ i)) 1)
      (fun i : Fin t => Finsupp.single (R.row i) 1)
      (by intro i; rfl))

lemma colContent_permute {m n t : ℕ}
    (R : RawMinorIndex m n t) (ρ κ : Equiv.Perm (Fin t)) :
    RawMinorIndex.colContent (R.permute ρ κ) =
      RawMinorIndex.colContent R := by
  classical
  unfold RawMinorIndex.colContent RawMinorIndex.permute
  simpa [Function.comp_apply] using
    (Fintype.sum_equiv κ
      (fun i : Fin t => Finsupp.single (R.col (κ i)) 1)
      (fun i : Fin t => Finsupp.single (R.col i) 1)
      (by intro i; rfl))

noncomputable def sorted {m n t : ℕ}
    (R : RawMinorIndex m n t) : RawMinorIndex m n t :=
  R.permute (Tuple.sort R.row) (Tuple.sort R.col)

lemma sorted_row_strictMono {m n t : ℕ}
    (R : RawMinorIndex m n t) (hrow : Function.Injective R.row) :
    StrictMono R.sorted.row := by
  simpa [sorted, permute] using
    strictMono_comp_tupleSort_of_injective R.row hrow

lemma sorted_col_strictMono {m n t : ℕ}
    (R : RawMinorIndex m n t) (hcol : Function.Injective R.col) :
    StrictMono R.sorted.col := by
  simpa [sorted, permute] using
    strictMono_comp_tupleSort_of_injective R.col hcol

lemma sorted_row_eq_orderEmbOfFin_image {m n t : ℕ}
    (R : RawMinorIndex m n t) (hrow : Function.Injective R.row) :
    R.sorted.row =
      (Finset.univ.image R.row).orderEmbOfFin (by
        rw [Finset.card_image_of_injective _ hrow]
        simp) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    simp [sorted, permute]
  · exact R.sorted_row_strictMono hrow

lemma sorted_col_eq_orderEmbOfFin_image {m n t : ℕ}
    (R : RawMinorIndex m n t) (hcol : Function.Injective R.col) :
    R.sorted.col =
      (Finset.univ.image R.col).orderEmbOfFin (by
        rw [Finset.card_image_of_injective _ hcol]
        simp) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    simp [sorted, permute]
  · exact R.sorted_col_strictMono hcol

lemma sorted_row_le_of_image_subset {m n r s : ℕ}
    (R : RawMinorIndex m n r) (S : RawMinorIndex m n s)
    (hR : Function.Injective R.row) (hS : Function.Injective S.row)
    (hsub : Finset.univ.image R.row ⊆ Finset.univ.image S.row)
    (i : Fin r) :
    S.sorted.row
        ⟨i, lt_of_lt_of_le i.isLt (by
          simpa [Finset.card_image_of_injective _ hR,
            Finset.card_image_of_injective _ hS] using
              Finset.card_le_card hsub)⟩ ≤
      R.sorted.row i := by
  have hcardR : (Finset.univ.image R.row).card = r := by
    rw [Finset.card_image_of_injective _ hR]
    simp
  rw [R.sorted_row_eq_orderEmbOfFin_image hR,
    S.sorted_row_eq_orderEmbOfFin_image hS]
  simpa using Finset.orderEmbOfFin_le_orderEmbOfFin_of_subset hsub
    (Fin.cast hcardR.symm i)

lemma sorted_col_le_of_image_subset {m n r s : ℕ}
    (R : RawMinorIndex m n r) (S : RawMinorIndex m n s)
    (hR : Function.Injective R.col) (hS : Function.Injective S.col)
    (hsub : Finset.univ.image R.col ⊆ Finset.univ.image S.col)
    (i : Fin r) :
    S.sorted.col
        ⟨i, lt_of_lt_of_le i.isLt (by
          simpa [Finset.card_image_of_injective _ hR,
            Finset.card_image_of_injective _ hS] using
              Finset.card_le_card hsub)⟩ ≤
      R.sorted.col i := by
  have hcardR : (Finset.univ.image R.col).card = r := by
    rw [Finset.card_image_of_injective _ hR]
    simp
  rw [R.sorted_col_eq_orderEmbOfFin_image hR,
    S.sorted_col_eq_orderEmbOfFin_image hS]
  simpa using Finset.orderEmbOfFin_le_orderEmbOfFin_of_subset hsub
    (Fin.cast hcardR.symm i)

lemma sorted_row_le_of_card_filter_le {m n t : ℕ}
    (R : RawMinorIndex m n t) (i : Fin t) (x : Fin m)
    (hcount :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.row a ≤ x).card) :
    R.sorted.row i ≤ x := by
  classical
  have hcard :
      (Finset.univ.filter fun a : Fin t => R.sorted.row a ≤ x).card =
        (Finset.univ.filter fun a : Fin t => R.row a ≤ x).card := by
    refine Finset.card_bijective (Tuple.sort R.row) (Tuple.sort R.row).bijective ?_
    intro a
    simp [RawMinorIndex.sorted, RawMinorIndex.permute]
  have hcount' :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.sorted.row a ≤ x).card := by
    simpa [hcard] using hcount
  have hmono : Monotone R.sorted.row := by
    simpa [RawMinorIndex.sorted, RawMinorIndex.permute, Function.comp_def] using
      Tuple.monotone_sort R.row
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (f := R.sorted.row) hmono).mp hcount'

lemma sorted_col_le_of_card_filter_le {m n t : ℕ}
    (R : RawMinorIndex m n t) (i : Fin t) (x : Fin n)
    (hcount :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.col a ≤ x).card) :
    R.sorted.col i ≤ x := by
  classical
  have hcard :
      (Finset.univ.filter fun a : Fin t => R.sorted.col a ≤ x).card =
        (Finset.univ.filter fun a : Fin t => R.col a ≤ x).card := by
    refine Finset.card_bijective (Tuple.sort R.col) (Tuple.sort R.col).bijective ?_
    intro a
    simp [RawMinorIndex.sorted, RawMinorIndex.permute]
  have hcount' :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.sorted.col a ≤ x).card := by
    simpa [hcard] using hcount
  have hmono : Monotone R.sorted.col := by
    simpa [RawMinorIndex.sorted, RawMinorIndex.permute, Function.comp_def] using
      Tuple.monotone_sort R.col
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (f := R.sorted.col) hmono).mp hcount'

lemma sorted_row_lt_of_card_filter_lt {m n t : ℕ}
    (R : RawMinorIndex m n t) (i : Fin t) (x : Fin m)
    (hcount :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.row a < x).card) :
    R.sorted.row i < x := by
  classical
  have hcard :
      (Finset.univ.filter fun a : Fin t => R.sorted.row a < x).card =
        (Finset.univ.filter fun a : Fin t => R.row a < x).card := by
    refine Finset.card_bijective (Tuple.sort R.row) (Tuple.sort R.row).bijective ?_
    intro a
    simp [RawMinorIndex.sorted, RawMinorIndex.permute]
  have hcount' :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.sorted.row a < x).card := by
    simpa [hcard] using hcount
  have hmono : Monotone R.sorted.row := by
    simpa [RawMinorIndex.sorted, RawMinorIndex.permute, Function.comp_def] using
      Tuple.monotone_sort R.row
  by_contra hnot
  have hxi : x ≤ R.sorted.row i := le_of_not_gt hnot
  have hsub :
      (Finset.univ.filter fun a : Fin t => R.sorted.row a < x) ⊆
        Finset.Iio i := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Iio]
    by_contra hai
    have hia : i ≤ a := le_of_not_gt hai
    exact not_lt_of_ge (le_trans hxi (hmono hia)) ha.2
  have hcard_le :
      (Finset.univ.filter fun a : Fin t => R.sorted.row a < x).card ≤ i.val := by
    calc
      (Finset.univ.filter fun a : Fin t => R.sorted.row a < x).card
          ≤ (Finset.Iio i).card := Finset.card_le_card hsub
      _ = i.val := by simp
  omega

lemma sorted_col_lt_of_card_filter_lt {m n t : ℕ}
    (R : RawMinorIndex m n t) (i : Fin t) (x : Fin n)
    (hcount :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.col a < x).card) :
    R.sorted.col i < x := by
  classical
  have hcard :
      (Finset.univ.filter fun a : Fin t => R.sorted.col a < x).card =
        (Finset.univ.filter fun a : Fin t => R.col a < x).card := by
    refine Finset.card_bijective (Tuple.sort R.col) (Tuple.sort R.col).bijective ?_
    intro a
    simp [RawMinorIndex.sorted, RawMinorIndex.permute]
  have hcount' :
      (i : ℕ) < (Finset.univ.filter fun a : Fin t => R.sorted.col a < x).card := by
    simpa [hcard] using hcount
  have hmono : Monotone R.sorted.col := by
    simpa [RawMinorIndex.sorted, RawMinorIndex.permute, Function.comp_def] using
      Tuple.monotone_sort R.col
  by_contra hnot
  have hxi : x ≤ R.sorted.col i := le_of_not_gt hnot
  have hsub :
      (Finset.univ.filter fun a : Fin t => R.sorted.col a < x) ⊆
        Finset.Iio i := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_Iio]
    by_contra hai
    have hia : i ≤ a := le_of_not_gt hai
    exact not_lt_of_ge (le_trans hxi (hmono hia)) ha.2
  have hcard_le :
      (Finset.univ.filter fun a : Fin t => R.sorted.col a < x).card ≤ i.val := by
    calc
      (Finset.univ.filter fun a : Fin t => R.sorted.col a < x).card
          ≤ (Finset.Iio i).card := Finset.card_le_card hsub
      _ = i.val := by simp
  omega

lemma toPolynomial_sorted {m n t : ℕ}
    {k : Type*} [CommRing k]
    (R : RawMinorIndex m n t) :
    RawMinorIndex.toPolynomial (k := k) R.sorted =
      (Equiv.Perm.sign (Tuple.sort R.row) : MvPolynomial (Fin m × Fin n) k) *
        (Equiv.Perm.sign (Tuple.sort R.col) : MvPolynomial (Fin m × Fin n) k) *
          RawMinorIndex.toPolynomial (k := k) R := by
  exact R.toPolynomial_permute (Tuple.sort R.row) (Tuple.sort R.col)

lemma rowContent_sorted {m n t : ℕ}
    (R : RawMinorIndex m n t) :
    RawMinorIndex.rowContent R.sorted = RawMinorIndex.rowContent R := by
  exact R.rowContent_permute (Tuple.sort R.row) (Tuple.sort R.col)

lemma colContent_sorted {m n t : ℕ}
    (R : RawMinorIndex m n t) :
    RawMinorIndex.colContent R.sorted = RawMinorIndex.colContent R := by
  exact R.colContent_permute (Tuple.sort R.row) (Tuple.sort R.col)

end RawMinorIndex


/-- A two-factor raw minor product.  This is the local object produced by
Laplace exchange before zero terms have been discarded and before injective
row/column maps have been promoted to `MinorIndex`. -/
structure RawMinorPair (m n : ℕ) where
  p : ℕ
  q : ℕ
  left : RawMinorIndex m n p
  right : RawMinorIndex m n q

namespace RawMinorPair

noncomputable def toPolynomial {m n : ℕ}
    {k : Type*} [CommRing k]
    (P : RawMinorPair m n) : MvPolynomial (Fin m × Fin n) k :=
  RawMinorIndex.toPolynomial (k := k) P.left *
    RawMinorIndex.toPolynomial (k := k) P.right

noncomputable def rowContent {m n : ℕ}
    (P : RawMinorPair m n) : Fin m →₀ ℕ :=
  RawMinorIndex.rowContent P.left + RawMinorIndex.rowContent P.right

noncomputable def colContent {m n : ℕ}
    (P : RawMinorPair m n) : Fin n →₀ ℕ :=
  RawMinorIndex.colContent P.left + RawMinorIndex.colContent P.right

def rowIndexSum {m n : ℕ} (P : RawMinorPair m n) : ℕ :=
  (∑ i : Fin P.p, (P.left.row i).val) +
    ∑ j : Fin P.q, (P.right.row j).val

def colIndexSum {m n : ℕ} (P : RawMinorPair m n) : ℕ :=
  (∑ i : Fin P.p, (P.left.col i).val) +
    ∑ j : Fin P.q, (P.right.col j).val

def laplaceSignExponent {m n : ℕ} (P : RawMinorPair m n) : ℕ :=
  P.rowIndexSum + P.colIndexSum

noncomputable def laplaceCoeff {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) : k :=
  (-1 : k) ^ P.laplaceSignExponent

noncomputable def laplacePolynomial {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    MvPolynomial (Fin m × Fin n) k :=
  MvPolynomial.C (P.laplaceCoeff (k := k)) *
    RawMinorPair.toPolynomial (k := k) P

noncomputable def sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair m n where
  p := P.p
  q := P.q
  left := P.left.sorted
  right := P.right.sorted

noncomputable def sortSign {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    MvPolynomial (Fin m × Fin n) k :=
  (Equiv.Perm.sign (Tuple.sort P.left.row) : MvPolynomial (Fin m × Fin n) k) *
    (Equiv.Perm.sign (Tuple.sort P.left.col) : MvPolynomial (Fin m × Fin n) k) *
    (Equiv.Perm.sign (Tuple.sort P.right.row) : MvPolynomial (Fin m × Fin n) k) *
    (Equiv.Perm.sign (Tuple.sort P.right.col) : MvPolynomial (Fin m × Fin n) k)

noncomputable def sortSignCoeff {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) : k :=
  (Equiv.Perm.sign (Tuple.sort P.left.row) : k) *
    (Equiv.Perm.sign (Tuple.sort P.left.col) : k) *
    (Equiv.Perm.sign (Tuple.sort P.right.row) : k) *
    (Equiv.Perm.sign (Tuple.sort P.right.col) : k)

lemma sortSign_eq_C {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    P.sortSign (k := k) = MvPolynomial.C (P.sortSignCoeff (k := k)) := by
  simp [RawMinorPair.sortSign, RawMinorPair.sortSignCoeff, MvPolynomial.C_mul]

lemma sortSign_mul_self {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    P.sortSign (k := k) * P.sortSign (k := k) = 1 := by
  let sρL : MvPolynomial (Fin m × Fin n) k :=
    (Equiv.Perm.sign (Tuple.sort P.left.row) :
      MvPolynomial (Fin m × Fin n) k)
  let sκL : MvPolynomial (Fin m × Fin n) k :=
    (Equiv.Perm.sign (Tuple.sort P.left.col) :
      MvPolynomial (Fin m × Fin n) k)
  let sρR : MvPolynomial (Fin m × Fin n) k :=
    (Equiv.Perm.sign (Tuple.sort P.right.row) :
      MvPolynomial (Fin m × Fin n) k)
  let sκR : MvPolynomial (Fin m × Fin n) k :=
    (Equiv.Perm.sign (Tuple.sort P.right.col) :
      MvPolynomial (Fin m × Fin n) k)
  have hρL : sρL * sρL = 1 := by
    simp [sρL, ← Int.cast_mul]
  have hκL : sκL * sκL = 1 := by
    simp [sκL, ← Int.cast_mul]
  have hρR : sρR * sρR = 1 := by
    simp [sρR, ← Int.cast_mul]
  have hκR : sκR * sκR = 1 := by
    simp [sκR, ← Int.cast_mul]
  change (sρL * sκL * sρR * sκR) *
      (sρL * sκL * sρR * sκR) = 1
  calc
    (sρL * sκL * sρR * sκR) * (sρL * sκL * sρR * sκR)
        = (sρL * sρL) * (sκL * sκL) * (sρR * sρR) * (sκR * sκR) := by
          ring
    _ = 1 := by
          rw [hρL, hκL, hρR, hκR]
          ring

def permute {m n : ℕ} (P : RawMinorPair m n)
    (ρL : Equiv.Perm (Fin P.p)) (κL : Equiv.Perm (Fin P.p))
    (ρR : Equiv.Perm (Fin P.q)) (κR : Equiv.Perm (Fin P.q)) :
    RawMinorPair m n where
  p := P.p
  q := P.q
  left := P.left.permute ρL κL
  right := P.right.permute ρR κR

lemma toPolynomial_permute {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n)
    (ρL : Equiv.Perm (Fin P.p)) (κL : Equiv.Perm (Fin P.p))
    (ρR : Equiv.Perm (Fin P.q)) (κR : Equiv.Perm (Fin P.q)) :
    RawMinorPair.toPolynomial (k := k) (P.permute ρL κL ρR κR) =
      (Equiv.Perm.sign ρL : MvPolynomial (Fin m × Fin n) k) *
        (Equiv.Perm.sign κL : MvPolynomial (Fin m × Fin n) k) *
        (Equiv.Perm.sign ρR : MvPolynomial (Fin m × Fin n) k) *
        (Equiv.Perm.sign κR : MvPolynomial (Fin m × Fin n) k) *
        RawMinorPair.toPolynomial (k := k) P := by
  classical
  rw [RawMinorPair.toPolynomial, RawMinorPair.toPolynomial,
    RawMinorPair.permute, RawMinorIndex.toPolynomial_permute,
    RawMinorIndex.toPolynomial_permute]
  ring

lemma rowContent_permute {m n : ℕ} (P : RawMinorPair m n)
    (ρL : Equiv.Perm (Fin P.p)) (κL : Equiv.Perm (Fin P.p))
    (ρR : Equiv.Perm (Fin P.q)) (κR : Equiv.Perm (Fin P.q)) :
    RawMinorPair.rowContent (P.permute ρL κL ρR κR) =
      RawMinorPair.rowContent P := by
  simp [RawMinorPair.rowContent, RawMinorPair.permute,
    RawMinorIndex.rowContent_permute]

lemma colContent_permute {m n : ℕ} (P : RawMinorPair m n)
    (ρL : Equiv.Perm (Fin P.p)) (κL : Equiv.Perm (Fin P.p))
    (ρR : Equiv.Perm (Fin P.q)) (κR : Equiv.Perm (Fin P.q)) :
    RawMinorPair.colContent (P.permute ρL κL ρR κR) =
      RawMinorPair.colContent P := by
  simp [RawMinorPair.colContent, RawMinorPair.permute,
    RawMinorIndex.colContent_permute]

lemma sorted_left_row_strictMono {m n : ℕ} (P : RawMinorPair m n)
    (hrow : Function.Injective P.left.row) :
    StrictMono P.sorted.left.row := by
  simpa [RawMinorPair.sorted] using
    RawMinorIndex.sorted_row_strictMono P.left hrow

lemma sorted_left_col_strictMono {m n : ℕ} (P : RawMinorPair m n)
    (hcol : Function.Injective P.left.col) :
    StrictMono P.sorted.left.col := by
  simpa [RawMinorPair.sorted] using
    RawMinorIndex.sorted_col_strictMono P.left hcol

lemma sorted_right_row_strictMono {m n : ℕ} (P : RawMinorPair m n)
    (hrow : Function.Injective P.right.row) :
    StrictMono P.sorted.right.row := by
  simpa [RawMinorPair.sorted] using
    RawMinorIndex.sorted_row_strictMono P.right hrow

lemma sorted_right_col_strictMono {m n : ℕ} (P : RawMinorPair m n)
    (hcol : Function.Injective P.right.col) :
    StrictMono P.sorted.right.col := by
  simpa [RawMinorPair.sorted] using
    RawMinorIndex.sorted_col_strictMono P.right hcol

lemma toPolynomial_sorted {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.toPolynomial (k := k) P.sorted =
      P.sortSign (k := k) * RawMinorPair.toPolynomial (k := k) P := by
  classical
  rw [RawMinorPair.toPolynomial, RawMinorPair.toPolynomial,
    RawMinorPair.sorted, RawMinorIndex.toPolynomial_sorted,
    RawMinorIndex.toPolynomial_sorted]
  simp [RawMinorPair.sortSign]
  ring

lemma rowContent_sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.rowContent P.sorted = RawMinorPair.rowContent P := by
  simp [RawMinorPair.rowContent, RawMinorPair.sorted,
    RawMinorIndex.rowContent_sorted]

lemma colContent_sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.colContent P.sorted = RawMinorPair.colContent P := by
  simp [RawMinorPair.colContent, RawMinorPair.sorted,
    RawMinorIndex.colContent_sorted]

lemma rowIndexSum_sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.rowIndexSum P.sorted = RawMinorPair.rowIndexSum P := by
  classical
  have hleft :
      (∑ i : Fin P.p,
          (P.left.row ((Tuple.sort P.left.row) i)).val) =
        ∑ i : Fin P.p, (P.left.row i).val := by
    simpa using
      (Fintype.sum_equiv (Tuple.sort P.left.row)
        (fun i : Fin P.p => (P.left.row ((Tuple.sort P.left.row) i)).val)
        (fun i : Fin P.p => (P.left.row i).val)
        (by intro i; rfl))
  have hright :
      (∑ i : Fin P.q,
          (P.right.row ((Tuple.sort P.right.row) i)).val) =
        ∑ i : Fin P.q, (P.right.row i).val := by
    simpa using
      (Fintype.sum_equiv (Tuple.sort P.right.row)
        (fun i : Fin P.q => (P.right.row ((Tuple.sort P.right.row) i)).val)
        (fun i : Fin P.q => (P.right.row i).val)
        (by intro i; rfl))
  simp [RawMinorPair.rowIndexSum, RawMinorPair.sorted,
    RawMinorIndex.sorted, RawMinorIndex.permute, hleft, hright]

lemma colIndexSum_sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.colIndexSum P.sorted = RawMinorPair.colIndexSum P := by
  classical
  have hleft :
      (∑ i : Fin P.p,
          (P.left.col ((Tuple.sort P.left.col) i)).val) =
        ∑ i : Fin P.p, (P.left.col i).val := by
    simpa using
      (Fintype.sum_equiv (Tuple.sort P.left.col)
        (fun i : Fin P.p => (P.left.col ((Tuple.sort P.left.col) i)).val)
        (fun i : Fin P.p => (P.left.col i).val)
        (by intro i; rfl))
  have hright :
      (∑ i : Fin P.q,
          (P.right.col ((Tuple.sort P.right.col) i)).val) =
        ∑ i : Fin P.q, (P.right.col i).val := by
    simpa using
      (Fintype.sum_equiv (Tuple.sort P.right.col)
        (fun i : Fin P.q => (P.right.col ((Tuple.sort P.right.col) i)).val)
        (fun i : Fin P.q => (P.right.col i).val)
        (by intro i; rfl))
  simp [RawMinorPair.colIndexSum, RawMinorPair.sorted,
    RawMinorIndex.sorted, RawMinorIndex.permute, hleft, hright]

lemma laplaceSignExponent_sorted {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.laplaceSignExponent P.sorted =
      RawMinorPair.laplaceSignExponent P := by
  simp [RawMinorPair.laplaceSignExponent, RawMinorPair.rowIndexSum_sorted,
    RawMinorPair.colIndexSum_sorted]

lemma laplaceCoeff_sorted {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.laplaceCoeff (k := k) P.sorted =
      RawMinorPair.laplaceCoeff (k := k) P := by
  simp [RawMinorPair.laplaceCoeff, RawMinorPair.laplaceSignExponent_sorted]

lemma laplacePolynomial_sorted {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.laplacePolynomial (k := k) P.sorted =
      P.sortSign (k := k) * RawMinorPair.laplacePolynomial (k := k) P := by
  rw [RawMinorPair.laplacePolynomial, RawMinorPair.laplacePolynomial,
    RawMinorPair.laplaceCoeff_sorted, RawMinorPair.toPolynomial_sorted]
  ring

lemma laplacePolynomial_eq_sortSign_mul_sorted {m n : ℕ}
    {k : Type*} [CommRing k] (P : RawMinorPair m n) :
    RawMinorPair.laplacePolynomial (k := k) P =
      P.sortSign (k := k) *
        RawMinorPair.laplacePolynomial (k := k) P.sorted := by
  rw [RawMinorPair.laplacePolynomial_sorted]
  have hsign := RawMinorPair.sortSign_mul_self (k := k) P
  calc
    RawMinorPair.laplacePolynomial (k := k) P
        = (P.sortSign (k := k) * P.sortSign (k := k)) *
            RawMinorPair.laplacePolynomial (k := k) P := by
          rw [hsign]
          simp
    _ = P.sortSign (k := k) *
          (P.sortSign (k := k) *
            RawMinorPair.laplacePolynomial (k := k) P) := by
          ring

def slotRow {m n : ℕ} (P : RawMinorPair m n) :
    Sum (Fin P.p) (Fin P.q) → Fin m
  | Sum.inl i => P.left.row i
  | Sum.inr j => P.right.row j

def slotCol {m n : ℕ} (P : RawMinorPair m n) :
    Sum (Fin P.p) (Fin P.q) → Fin n
  | Sum.inl i => P.left.col i
  | Sum.inr j => P.right.col j

lemma rowContent_eq_sum_slots {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.rowContent P =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotRow s) 1 := by
  classical
  cases P with
  | mk p q left right =>
      simp [RawMinorPair.rowContent, RawMinorPair.slotRow,
        RawMinorIndex.rowContent, Fintype.sum_sum_type]

lemma colContent_eq_sum_slots {m n : ℕ} (P : RawMinorPair m n) :
    RawMinorPair.colContent P =
      ∑ s : Sum (Fin P.p) (Fin P.q),
        Finsupp.single (P.slotCol s) 1 := by
  classical
  cases P with
  | mk p q left right =>
      simp [RawMinorPair.colContent, RawMinorPair.slotCol,
        RawMinorIndex.colContent, Fintype.sum_sum_type]

lemma rowIndexSum_eq_sum_slots {m n : ℕ} (P : RawMinorPair m n) :
    P.rowIndexSum =
      ∑ s : Sum (Fin P.p) (Fin P.q), (P.slotRow s).val := by
  classical
  cases P with
  | mk p q left right =>
      simp [RawMinorPair.rowIndexSum, RawMinorPair.slotRow,
        Fintype.sum_sum_type]

lemma colIndexSum_eq_sum_slots {m n : ℕ} (P : RawMinorPair m n) :
    P.colIndexSum =
      ∑ s : Sum (Fin P.p) (Fin P.q), (P.slotCol s).val := by
  classical
  cases P with
  | mk p q left right =>
      simp [RawMinorPair.colIndexSum, RawMinorPair.slotCol,
        Fintype.sum_sum_type]


end RawMinorPair

end Determinantal
