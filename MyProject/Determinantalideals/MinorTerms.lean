/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import MyProject.Determinantalideals.Basic

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

@[simp] theorem diagMonomial_def (I : MinorIndex m n t) :
    diagMonomial I = MvPolynomial.monomial (diagExp I) 1 :=
  rfl

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

end Determinantal
