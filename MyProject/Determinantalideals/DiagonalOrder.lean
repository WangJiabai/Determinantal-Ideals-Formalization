/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.MinorTerms

/-!
# Diagonal and anti-diagonal term orders for generic minors

This file defines `IsDiagonalTermOrder` and `IsAntidiagonalTermOrder`, constructs
the concrete orders `rowMajorLex` and `antiDiagonalLex`, and proves the
corresponding leading-exponent, leading-coefficient, and leading-term results
for generic minors. The anti-diagonal construction orders rows increasingly
and columns decreasingly within each row; `antiDiagonalLex_isAntidiagonal` is
the formal guarantee consumed by the final theorem.
-/

open scoped MonomialOrder

namespace Determinantal

section DiagonalProperty

variable {m n : ℕ}

/-- A monomial order is diagonal if, in every minor, every nontrivial permutation term is
strictly smaller than the diagonal term. -/
def IsDiagonalTermOrder (ord : MonomialOrder (Fin m × Fin n)) : Prop :=
  ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)),
    σ ≠ 1 → permExp I σ ≺[ord] diagExp I

/-- A monomial order is anti-diagonal if, in every minor, every permutation term except the
anti-diagonal one is strictly smaller than the anti-diagonal term. -/
def IsAntidiagonalTermOrder (ord : MonomialOrder (Fin m × Fin n)) : Prop :=
  ∀ ⦃t : ℕ⦄ (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t)),
    σ ≠ Fin.revPerm → permExp I σ ≺[ord] antidiagExp I

end DiagonalProperty

section ConcreteLex

variable (m n : ℕ)

/-- The row-major linear order on `Fin m × Fin n`, obtained by pulling back the usual order on
`Fin (m * n)` along `finProdFinEquiv`. -/
noncomputable def rowMajorVarOrder : LinearOrder (Fin m × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

/-- Well-foundedness of the strict row-major order on `Fin m × Fin n`. -/
noncomputable def rowMajorWF :
    @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ (rowMajorVarOrder m n).toPreorder) :=
  @Finite.to_wellFoundedGT
    (Fin m × Fin n)
    (inferInstance : Finite (Fin m × Fin n))
    (rowMajorVarOrder m n).toPreorder

/-- The lexicographic monomial order induced by the row-major order on variables. -/
noncomputable def rowMajorLex : MonomialOrder (Fin m × Fin n) :=
  @MonomialOrder.lex (Fin m × Fin n) (rowMajorVarOrder m n) (rowMajorWF m n)

/-- The variable order with increasing row indices and, within each row,
decreasing column indices. -/
noncomputable def antiDiagonalVarOrder : LinearOrder (Fin m × Fin n) :=
  LinearOrder.lift'
    (fun x : Fin m × Fin n => finProdFinEquiv (x.1, x.2.rev))
    (by
      intro x y h
      have hxy : (x.1, x.2.rev) = (y.1, y.2.rev) :=
        finProdFinEquiv.injective h
      injection hxy with hrow hcol
      apply Prod.ext
      · exact hrow
      · exact Fin.rev_injective hcol)

/-- Well-foundedness of the strict row/right-to-left column order on variables. -/
noncomputable def antiDiagonalWF :
    @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ (antiDiagonalVarOrder m n).toPreorder) :=
  @Finite.to_wellFoundedGT
    (Fin m × Fin n)
    (inferInstance : Finite (Fin m × Fin n))
    (antiDiagonalVarOrder m n).toPreorder

/-- The lexicographic monomial order induced by increasing rows and decreasing
columns within each row. The theorem `antiDiagonalLex_isAntidiagonal` proves
that it satisfies `IsAntidiagonalTermOrder`. -/
noncomputable def antiDiagonalLex : MonomialOrder (Fin m × Fin n) :=
  @MonomialOrder.lex (Fin m × Fin n) (antiDiagonalVarOrder m n) (antiDiagonalWF m n)


/-- In row-major order, a strictly smaller row index gives a strictly smaller variable. -/
lemma rowMajor_lt_of_row_lt
    {i i' : Fin m} {j : Fin n} {j' : Fin n}
    (h : i < i') :
    @LT.lt (Fin m × Fin n) (rowMajorVarOrder m n).toLT (i, j) (i', j') := by
  change finProdFinEquiv (i, j) < finProdFinEquiv (i', j')
  change ((finProdFinEquiv (i, j) : Fin (m * n))) <
      ((finProdFinEquiv (i', j') : Fin (m * n)) : ℕ)
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  have hiNat : (i : ℕ) < i' := h
  have hjNat : (j : ℕ) < n := j.isLt
  have h1 : (j : ℕ) + n * (i : ℕ) < n * (i + 1) := by
    linarith
  have h2 : n * ((i : ℕ) + 1) ≤ n * i' := by
    exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hiNat)
  have h3 : n * (i' : ℕ) ≤ j' + n * i' := by
    simp only [le_add_iff_nonneg_left, zero_le]
  exact lt_of_lt_of_le h1 (le_trans h2 h3)

/-- In row-major order, within the same row, a strictly smaller column index gives a strictly
smaller variable. -/
lemma rowMajor_lt_of_col_lt
    {i : Fin m} {j j' : Fin n}
    (h : j < j') :
    @LT.lt (Fin m × Fin n) (rowMajorVarOrder m n).toLT (i, j) (i, j') := by
  change finProdFinEquiv (i, j) < finProdFinEquiv (i, j')
  change ((finProdFinEquiv (i, j) : Fin (m * n)) : ℕ) <
      ((finProdFinEquiv (i, j') : Fin (m * n)) : ℕ)
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, add_lt_add_iff_right, Fin.val_fin_lt]
  exact h

/-- In the anti-diagonal variable order, a strictly smaller row index gives a strictly smaller
variable. -/
lemma antiDiagonal_lt_of_row_lt
    {i i' : Fin m} {j : Fin n} {j' : Fin n}
    (h : i < i') :
    @LT.lt (Fin m × Fin n) (antiDiagonalVarOrder m n).toLT (i, j) (i', j') := by
  change finProdFinEquiv (i, j.rev) < finProdFinEquiv (i', j'.rev)
  exact rowMajor_lt_of_row_lt m n h

/-- In the anti-diagonal variable order, within one row, a larger column index comes first. -/
lemma antiDiagonal_lt_of_col_gt
    {i : Fin m} {j j' : Fin n}
    (h : j' < j) :
    @LT.lt (Fin m × Fin n) (antiDiagonalVarOrder m n).toLT (i, j) (i, j') := by
  change finProdFinEquiv (i, j.rev) < finProdFinEquiv (i, j'.rev)
  exact rowMajor_lt_of_col_lt m n (Fin.rev_lt_rev.mpr h)

/-- At an anti-diagonal variable, the anti-diagonal exponent is `1`. -/
@[simp] lemma antidiagExp_apply_antidiag
    {t : ℕ}
    (I : MinorIndex m n t) (i : Fin t) :
    antidiagExp I (I.row i, I.col i.rev) = 1 := by
  classical
  rw [antidiagExp, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [Finsupp.single_eq_of_ne]
    intro hpair
    exact hji (I.row.injective (by simpa using congrArg Prod.fst hpair)).symm
  · intro hi
    simp at hi

/-- At an anti-diagonal variable corresponding to an index where `σ i = i.rev`, the permutation
exponent is `1`. -/
lemma permExp_apply_antidiag_of_rev
    {t : ℕ}
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    {i : Fin t} (hfixi : σ i = i.rev) :
    permExp I σ (I.row i, I.col i.rev) = 1 := by
  rw [permExp_apply]
  exact if_pos ⟨i, rfl, by simp [hfixi]⟩

/-- At an anti-diagonal variable corresponding to a moved index, the permutation exponent is `0`. -/
lemma permExp_apply_antidiag_eq_zero
    {t : ℕ}
    (I : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    {i : Fin t}
    (hmove : σ i ≠ i.rev) :
    permExp I σ (I.row i, I.col i.rev) = 0 := by
  rw [permExp_apply]
  refine if_neg ?_
  rintro ⟨j, hjrow, hjcol⟩
  have hj : j = i := I.row.injective hjrow
  subst hj
  exact hmove (I.col.injective hjcol)

/-- The row-major lexicographic order is a diagonal term order. -/
theorem rowMajorLex_isDiagonal :
    IsDiagonalTermOrder (rowMajorLex m n) := by
  classical
  intro t I σ hσ
  let instLO : LinearOrder (Fin m × Fin n) := rowMajorVarOrder m n
  let instWF :
      @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ instLO.toPreorder) := by
    simp [instLO, rowMajorWF]
  rw [show
      (rowMajorLex m n).toSyn (permExp I σ) <
        (rowMajorLex m n).toSyn (diagExp I) ↔
      @LT.lt (Lex ((Fin m × Fin n) →₀ ℕ))
        (@Finsupp.instLTLex
          (Fin m × Fin n) ℕ
          inferInstance
          instLO.toLT
          instLTNat)
        (toLex (permExp I σ))
        (toLex (diagExp I))
      by
        simpa [rowMajorLex, rowMajorWF, instLO, instWF] using
          (@MonomialOrder.lex_lt_iff
            (Fin m × Fin n)
            instLO
            instWF
            (permExp I σ)
            (diagExp I))]
  change Finsupp.Lex
      (fun x y : Fin m × Fin n => @LT.lt _ instLO.toLT x y)
      (fun a b : ℕ => a < b)
      (permExp I σ)
      (diagExp I)
  rw [Finsupp.lex_def]
  let s : Finset (Fin t) := Finset.univ.filter fun i => σ i ≠ i
  have hs : s.Nonempty := by
    by_contra hs'
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
    apply hσ
    ext i
    have hi_not : i ∉ s := by
      simp [hs0]
    have hfix : σ i = i := by
      simpa [s] using hi_not
    simpa using congrArg Fin.val hfix
  let i0 : Fin t := s.min' hs
  have hi0_mem : i0 ∈ s := Finset.min'_mem s hs
  have hi0_move : σ i0 ≠ i0 := (Finset.mem_filter.mp hi0_mem).2
  have hfix_before : ∀ j : Fin t, j < i0 → σ j = j := by
    intro j hj
    by_contra hjne
    have hjmem : j ∈ s := by
      simp [s, hjne]
    exact not_lt_of_ge (Finset.min'_le s j hjmem) hj
  have hi0_lt_sigma : i0 < σ i0 := by
    by_contra hnot
    have hle : σ i0 ≤ i0 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hfixσ : σ (σ i0) = σ i0 := hfix_before (σ i0) hlt
      exact hi0_move (σ.injective hfixσ)
    · exact hi0_move heq
  have rowMajor_row_lt
      {a a' : Fin m} {b b' : Fin n}
      (ha : a < a') :
      @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a', b') := by
    exact rowMajor_lt_of_row_lt m n ha
  have rowMajor_col_lt
      {a : Fin m} {b b' : Fin n}
      (hb : b < b') :
      @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a, b') := by
    exact rowMajor_lt_of_col_lt m n hb
  refine ⟨(I.row i0, I.col i0), ?_, ?_⟩
  · intro d hd
    by_cases hdiagd : ∃ k : Fin t, d = (I.row k, I.col k)
    · rcases hdiagd with ⟨k, rfl⟩
      have hk_lt : k < i0 := by
        by_contra hk_not
        have hk_ge : i0 ≤ k := le_of_not_gt hk_not
        rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
        · have hgt :
              @LT.lt (Fin m × Fin n) instLO.toLT
                (I.row i0, I.col i0) (I.row k, I.col k) :=
            rowMajor_row_lt
              (a := I.row i0) (a' := I.row k)
              (b := I.col i0) (b' := I.col k)
              (I.row.strictMono hk_gt)
          have hgt' :
              finProdFinEquiv (I.row i0, I.col i0) <
                finProdFinEquiv (I.row k, I.col k) := by
            simpa [instLO] using hgt
          have hd' :
              finProdFinEquiv (I.row k, I.col k) <
                finProdFinEquiv (I.row i0, I.col i0) := by
            simpa [instLO] using hd
          exact lt_irrefl _ (lt_trans hgt' hd')
        · exact lt_irrefl _ (by exact Option.some_lt_some.mp hd)
      have hkfix : σ k = k := hfix_before k hk_lt
      have hperm : permExp I σ (I.row k, I.col k) = 1 :=
        permExp_apply_diag_of_fix I σ hkfix
      have hdiag : diagExp I (I.row k, I.col k) = 1 :=
        diagExp_apply_diag (I := I) k
      simp [hperm, hdiag]
    · have hdiag0 : diagExp I d = 0 := by
        rw [diagExp, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col k) = d
        · exact False.elim (hdiagd ⟨k, hk'.symm⟩)
        · simp [hk']
      have hperm0 : permExp I σ d = 0 := by
        classical
        rw [permExp, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col (σ k)) = d
        · have hk_lt : k < i0 := by
            by_contra hk_not
            have hk_ge : i0 ≤ k := le_of_not_gt hk_not
            rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
            · have hjk :
                  @LT.lt (Fin m × Fin n) instLO.toLT
                    (I.row i0, I.col i0) (I.row k, I.col (σ k)) :=
                rowMajor_row_lt
                  (a := I.row i0) (a' := I.row k)
                  (b := I.col i0) (b' := I.col (σ k))
                  (I.row.strictMono hk_gt)
              have hjk' :
                  finProdFinEquiv (I.row i0, I.col i0) <
                    finProdFinEquiv d := by
                simpa [instLO, hk'] using hjk
              have hd' :
                  finProdFinEquiv d <
                    finProdFinEquiv (I.row i0, I.col i0) := by
                simpa [instLO] using hd
              exact lt_irrefl _ (lt_trans hjk' hd')
            · have hjk :
                  @LT.lt (Fin m × Fin n) instLO.toLT
                    (I.row i0, I.col i0) (I.row i0, I.col (σ i0)) :=
                rowMajor_col_lt (I.col.strictMono hi0_lt_sigma)
              have hjk' :
                  finProdFinEquiv (I.row i0, I.col i0) <
                    finProdFinEquiv d := by
                simpa [instLO, hk'] using hjk
              have hd' :
                  finProdFinEquiv d <
                    finProdFinEquiv (I.row i0, I.col i0) := by
                simpa [instLO] using hd
              exact lt_irrefl _ (lt_trans hjk' hd')
          have hkdiag : d = (I.row k, I.col k) := by
            calc
              d = (I.row k, I.col (σ k)) := hk'.symm
              _ = (I.row k, I.col k) :=
                congrArg (Prod.mk (I.row k)) (congrArg (⇑I.col) (hfix_before k hk_lt))
          exact False.elim (hdiagd ⟨k, hkdiag⟩)
        · simp [hk']
      simp [hdiag0, hperm0]
  · have hdiag_at : diagExp I (I.row i0, I.col i0) = 1 := by
      exact diagExp_apply_diag I i0
    have hperm_at : permExp I σ (I.row i0, I.col i0) = 0 := by
      exact permExp_apply_diag_eq_zero I σ hi0_move (fun j hj => hfix_before j hj)
    simp [hperm_at, hdiag_at]

/-- The row/right-to-left-column lexicographic order is an anti-diagonal term order. -/
theorem antiDiagonalLex_isAntidiagonal :
    IsAntidiagonalTermOrder (antiDiagonalLex m n) := by
  classical
  intro t I σ hσ
  let instLO : LinearOrder (Fin m × Fin n) := antiDiagonalVarOrder m n
  let instWF :
      @WellFoundedGT (Fin m × Fin n) (@Preorder.toLT _ instLO.toPreorder) := by
    simp [instLO, antiDiagonalWF]
  rw [show
      (antiDiagonalLex m n).toSyn (permExp I σ) <
        (antiDiagonalLex m n).toSyn (antidiagExp I) ↔
      @LT.lt (Lex ((Fin m × Fin n) →₀ ℕ))
        (@Finsupp.instLTLex
          (Fin m × Fin n) ℕ
          inferInstance
          instLO.toLT
          instLTNat)
        (toLex (permExp I σ))
        (toLex (antidiagExp I))
      by
        simpa [antiDiagonalLex, antiDiagonalWF, instLO, instWF] using
          (@MonomialOrder.lex_lt_iff
            (Fin m × Fin n)
            instLO
            instWF
            (permExp I σ)
            (antidiagExp I))]
  change Finsupp.Lex
      (fun x y : Fin m × Fin n => @LT.lt _ instLO.toLT x y)
      (fun a b : ℕ => a < b)
      (permExp I σ)
      (antidiagExp I)
  rw [Finsupp.lex_def]
  let s : Finset (Fin t) := Finset.univ.filter fun i => σ i ≠ i.rev
  have hs : s.Nonempty := by
    by_contra hs'
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
    apply hσ
    ext i
    have hi_not : i ∉ s := by
      simp [hs0]
    have hfix : σ i = i.rev := by
      simpa [s] using hi_not
    simpa [Fin.revPerm] using congrArg Fin.val hfix
  let i0 : Fin t := s.min' hs
  have hi0_mem : i0 ∈ s := Finset.min'_mem s hs
  have hi0_move : σ i0 ≠ i0.rev := (Finset.mem_filter.mp hi0_mem).2
  have hfix_before : ∀ j : Fin t, j < i0 → σ j = j.rev := by
    intro j hj
    by_contra hjne
    have hjmem : j ∈ s := by
      simp [s, hjne]
    exact not_lt_of_ge (Finset.min'_le s j hjmem) hj
  have hi0_sigma_lt_rev : σ i0 < i0.rev := by
    have hnot_gt : ¬ i0.rev < σ i0 := by
      intro hgt
      let j : Fin t := (σ i0).rev
      have hj_lt : j < i0 := by
        simpa [j] using (Fin.rev_lt_iff.mp hgt)
      have hfixj : σ j = j.rev := hfix_before j hj_lt
      have hsame : σ j = σ i0 := by
        simpa [j] using hfixj
      have hji : j = i0 := σ.injective hsame
      have : σ i0 = i0.rev := by
        calc
          σ i0 = j.rev := by simp [j]
          _ = i0.rev := congrArg Fin.rev hji
      exact hi0_move this
    have hle : σ i0 ≤ i0.rev := le_of_not_gt hnot_gt
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (hi0_move heq)
  have anti_row_lt
      {a a' : Fin m} {b b' : Fin n}
      (ha : a < a') :
      @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a', b') := by
    exact antiDiagonal_lt_of_row_lt m n ha
  have anti_col_gt
      {a : Fin m} {b b' : Fin n}
      (hb : b' < b) :
      @LT.lt (Fin m × Fin n) instLO.toLT (a, b) (a, b') := by
    exact antiDiagonal_lt_of_col_gt m n hb
  refine ⟨(I.row i0, I.col i0.rev), ?_, ?_⟩
  · intro d hd
    by_cases hanti : ∃ k : Fin t, d = (I.row k, I.col k.rev)
    · rcases hanti with ⟨k, rfl⟩
      have hk_lt : k < i0 := by
        by_contra hk_not
        have hk_ge : i0 ≤ k := le_of_not_gt hk_not
        rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
        · have hgt :
              @LT.lt (Fin m × Fin n) instLO.toLT
                (I.row i0, I.col i0.rev) (I.row k, I.col k.rev) :=
            anti_row_lt
              (a := I.row i0) (a' := I.row k)
              (b := I.col i0.rev) (b' := I.col k.rev)
              (I.row.strictMono hk_gt)
          have hgt' :
              finProdFinEquiv (I.row i0, (I.col i0.rev).rev) <
                finProdFinEquiv (I.row k, (I.col k.rev).rev) := by
            simpa [instLO, antiDiagonalVarOrder] using hgt
          have hd' :
              finProdFinEquiv (I.row k, (I.col k.rev).rev) <
                finProdFinEquiv (I.row i0, (I.col i0.rev).rev) := by
            simpa [instLO, antiDiagonalVarOrder] using hd
          exact lt_irrefl _ (lt_trans hgt' hd')
        · exact lt_irrefl _ (by exact Option.some_lt_some.mp hd)
      have hkfix : σ k = k.rev := hfix_before k hk_lt
      have hperm : permExp I σ (I.row k, I.col k.rev) = 1 :=
        permExp_apply_antidiag_of_rev m n I σ hkfix
      have hanti_at : antidiagExp I (I.row k, I.col k.rev) = 1 :=
        antidiagExp_apply_antidiag m n I k
      simp [hperm, hanti_at]
    · have hanti0 : antidiagExp I d = 0 := by
        rw [antidiagExp, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col k.rev) = d
        · exact False.elim (hanti ⟨k, hk'.symm⟩)
        · simp [hk']
      have hperm0 : permExp I σ d = 0 := by
        classical
        rw [permExp, Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finsupp.single_apply]
        by_cases hk' : (I.row k, I.col (σ k)) = d
        · have hk_lt : k < i0 := by
            by_contra hk_not
            have hk_ge : i0 ≤ k := le_of_not_gt hk_not
            rcases lt_or_eq_of_le hk_ge with hk_gt | rfl
            · have hjk :
                  @LT.lt (Fin m × Fin n) instLO.toLT
                    (I.row i0, I.col i0.rev) (I.row k, I.col (σ k)) :=
                anti_row_lt
                  (a := I.row i0) (a' := I.row k)
                  (b := I.col i0.rev) (b' := I.col (σ k))
                  (I.row.strictMono hk_gt)
              have hjk' :
                  finProdFinEquiv (I.row i0, (I.col i0.rev).rev) <
                    finProdFinEquiv (d.1, d.2.rev) := by
                simpa [instLO, antiDiagonalVarOrder, hk'] using hjk
              have hd' :
                  finProdFinEquiv (d.1, d.2.rev) <
                    finProdFinEquiv (I.row i0, (I.col i0.rev).rev) := by
                simpa [instLO, antiDiagonalVarOrder] using hd
              exact lt_irrefl _ (lt_trans hjk' hd')
            · have hjk :
                  @LT.lt (Fin m × Fin n) instLO.toLT
                    (I.row i0, I.col i0.rev) (I.row i0, I.col (σ i0)) :=
                anti_col_gt
                  (a := I.row i0)
                  (b := I.col i0.rev)
                  (b' := I.col (σ i0))
                  (I.col.strictMono hi0_sigma_lt_rev)
              have hjk' :
                  finProdFinEquiv (I.row i0, (I.col i0.rev).rev) <
                    finProdFinEquiv (d.1, d.2.rev) := by
                simpa [instLO, antiDiagonalVarOrder, hk'] using hjk
              have hd' :
                  finProdFinEquiv (d.1, d.2.rev) <
                    finProdFinEquiv (I.row i0, (I.col i0.rev).rev) := by
                simpa [instLO, antiDiagonalVarOrder] using hd
              exact lt_irrefl _ (lt_trans hjk' hd')
          have hkanti : d = (I.row k, I.col k.rev) := by
            calc
              d = (I.row k, I.col (σ k)) := hk'.symm
              _ = (I.row k, I.col k.rev) :=
                congrArg (Prod.mk (I.row k)) (congrArg (⇑I.col) (hfix_before k hk_lt))
          exact False.elim (hanti ⟨k, hkanti⟩)
        · simp [hk']
      simp [hanti0, hperm0]
  · have hanti_at : antidiagExp I (I.row i0, I.col i0.rev) = 1 := by
      exact antidiagExp_apply_antidiag m n I i0
    have hperm_at : permExp I σ (I.row i0, I.col i0.rev) = 0 := by
      exact permExp_apply_antidiag_eq_zero m n I σ hi0_move
    simp [hperm_at, hanti_at]

end ConcreteLex

section BridgeLemmas

variable {k : Type*} [CommRing k]
variable {m n t : ℕ}

/-- For a non-identity permutation, the corresponding exponent vector is different from the
diagonal exponent vector. -/
theorem permExp_ne_diagExp_of_ne_one
    (I : MinorIndex m n t) {σ : Equiv.Perm (Fin t)} (hσ : σ ≠ 1) :
    permExp I σ ≠ diagExp I := by
  intro hEq
  have hlt : permExp I σ ≺[rowMajorLex m n] diagExp I :=
    rowMajorLex_isDiagonal m n I σ hσ
  simp [hEq] at hlt

/-- For a permutation different from `Fin.revPerm`, the corresponding exponent vector is
different from the anti-diagonal exponent vector. -/
theorem permExp_ne_antidiagExp_of_ne_rev
    (I : MinorIndex m n t) {σ : Equiv.Perm (Fin t)} (hσ : σ ≠ Fin.revPerm) :
    permExp I σ ≠ antidiagExp I := by
  intro hEq
  have hlt : permExp I σ ≺[antiDiagonalLex m n] antidiagExp I :=
    antiDiagonalLex_isAntidiagonal m n I σ hσ
  simp [hEq] at hlt

/-- Every determinant permutation coefficient is a unit-valued sign, hence nonzero over a
nontrivial coefficient ring. -/
theorem permCoeff_ne_zero (k : Type*) [CommRing k] [Nontrivial k] {t : ℕ}
    (σ : Equiv.Perm (Fin t)) :
    permCoeff k σ ≠ 0 := by
  rw [permCoeff]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp [h]

end BridgeLemmas

section LeadingTermConsequences

variable {k : Type*} [CommRing k] [Nontrivial k]
variable {m n t : ℕ}

/-- Under a diagonal term order, the degree of a minor is its diagonal exponent vector. -/
theorem degree_minor_eq_diagExp
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.degree (genericMinor k I) = diagExp I := by
  classical
  apply ord.toSyn.injective
  apply le_antisymm
  · rw [ord.degree_le_iff]
    intro c hc
    have hcoeff : MvPolynomial.coeff c (genericMinor k I) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hc
    rw [minor_eq_sum_permTerm I, MvPolynomial.coeff_sum] at hcoeff
    have hex :
        ∃ σ : Equiv.Perm (Fin t),
          MvPolynomial.coeff c (permTerm k I σ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hcoeff <| by
        refine Finset.sum_eq_zero ?_
        intro σ hσ
        exact h σ
    rcases hex with ⟨σ, hσcoeff⟩
    have hc_eq : c = permExp I σ := by
      by_contra hne
      have : MvPolynomial.coeff c (permTerm k I σ) = 0 := by
        simp only [permTerm, permExp, MvPolynomial.coeff_monomial, ite_eq_right_iff]
        exact fun a => False.elim (hne a.symm)
      exact hσcoeff this
    by_cases hσ1 : σ = 1
    · subst hσ1
      simp [hc_eq, permExp_one]
    · exact le_of_lt <| by
        simpa [hc_eq] using hdiag I σ hσ1
  · have hsupp : diagExp I ∈ (genericMinor k I).support := by
      rw [MvPolynomial.mem_support_iff,
        minor_eq_sum_permTerm I, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin t))]
      · simp [permTerm, permCoeff, permExp_one, MvPolynomial.coeff_monomial]
      · intro σ hσ hσne
        simp [permTerm, MvPolynomial.coeff_monomial,
          permExp_ne_diagExp_of_ne_one I hσne]
      · intro h
        simp at h
    exact ord.le_degree hsupp

/-- Under a diagonal term order, the leading coefficient of a minor is `1`. -/
theorem leadingCoeff_minor_eq_one
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.leadingCoeff (genericMinor k I) = 1 := by
  rw [MonomialOrder.leadingCoeff]
  rw [degree_minor_eq_diagExp k ord hdiag I]
  rw [minor_eq_sum_permTerm I, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin t))]
  · simp [permTerm, permCoeff, permExp_one, MvPolynomial.coeff_monomial]
  · intro σ hσ hσne
    simp [permTerm, MvPolynomial.coeff_monomial,
      permExp_ne_diagExp_of_ne_one I hσne]
  · intro h
    simp at h

/-- Under a diagonal term order, every minor is monic. -/
theorem monic_minor_of_isDiagonal
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.Monic (genericMinor k I) := by
  simp [MonomialOrder.Monic, leadingCoeff_minor_eq_one k ord hdiag I]

/-- Under a diagonal term order, the leading term of a minor is the diagonal monomial. -/
theorem leadingTerm_minor_eq_diagMonomial
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.leadingTerm (genericMinor k I) = diagMonomial k I := by
  simp [MonomialOrder.leadingTerm, diagMonomial, degree_minor_eq_diagExp k ord hdiag I,
    leadingCoeff_minor_eq_one k ord hdiag I]

/-- Under an anti-diagonal term order, the degree of a minor is its anti-diagonal exponent
vector. -/
theorem degree_minor_eq_antidiagExp
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.degree (genericMinor k I) = antidiagExp I := by
  classical
  apply ord.toSyn.injective
  apply le_antisymm
  · rw [ord.degree_le_iff]
    intro c hc
    have hcoeff : MvPolynomial.coeff c (genericMinor k I) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hc
    rw [minor_eq_sum_permTerm I, MvPolynomial.coeff_sum] at hcoeff
    have hex :
        ∃ σ : Equiv.Perm (Fin t),
          MvPolynomial.coeff c (permTerm k I σ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hcoeff <| by
        refine Finset.sum_eq_zero ?_
        intro σ hσ
        exact h σ
    rcases hex with ⟨σ, hσcoeff⟩
    have hc_eq : c = permExp I σ := by
      by_contra hne
      have : MvPolynomial.coeff c (permTerm k I σ) = 0 := by
        simp only [permTerm, permExp, MvPolynomial.coeff_monomial, ite_eq_right_iff]
        exact fun a => False.elim (hne a.symm)
      exact hσcoeff this
    by_cases hσrev : σ = Fin.revPerm
    · subst hσrev
      simp [hc_eq, antidiagExp, permExp, Fin.revPerm]
    · exact le_of_lt <| by
        simpa [hc_eq] using hanti I σ hσrev
  · have hsupp : antidiagExp I ∈ (genericMinor k I).support := by
      rw [MvPolynomial.mem_support_iff,
        minor_eq_sum_permTerm I, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single (Fin.revPerm : Equiv.Perm (Fin t))]
      · simpa [permTerm, antidiagExp, permExp, Fin.revPerm,
          MvPolynomial.coeff_monomial] using
          (permCoeff_ne_zero k (Fin.revPerm : Equiv.Perm (Fin t)))
      · intro σ hσ hσne
        simp [permTerm, MvPolynomial.coeff_monomial,
          permExp_ne_antidiagExp_of_ne_rev I hσne]
      · intro h
        simp at h
    exact ord.le_degree hsupp

/-- Under an anti-diagonal term order, the leading coefficient of a minor is the sign of the
reverse permutation. -/
theorem leadingCoeff_minor_eq_revPermCoeff
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.leadingCoeff (genericMinor k I) =
      permCoeff k (Fin.revPerm : Equiv.Perm (Fin t)) := by
  rw [MonomialOrder.leadingCoeff]
  rw [degree_minor_eq_antidiagExp k ord hanti I]
  rw [minor_eq_sum_permTerm I, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (Fin.revPerm : Equiv.Perm (Fin t))]
  · simp [permTerm, antidiagExp, permExp, Fin.revPerm, MvPolynomial.coeff_monomial]
  · intro σ hσ hσne
    simp [permTerm, MvPolynomial.coeff_monomial,
      permExp_ne_antidiagExp_of_ne_rev I hσne]
  · intro h
    simp at h

/-- Under an anti-diagonal term order, the leading term of a minor is its anti-diagonal
monomial with the reverse-permutation sign coefficient. -/
theorem leadingTerm_minor_eq_antidiagMonomial_coeff
    (k : Type*) [CommRing k] [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.leadingTerm (genericMinor k I) =
      MvPolynomial.monomial (antidiagExp I)
        (permCoeff k (Fin.revPerm : Equiv.Perm (Fin t))) := by
  simp [MonomialOrder.leadingTerm, degree_minor_eq_antidiagExp k ord hanti I,
    leadingCoeff_minor_eq_revPermCoeff k ord hanti I]

/-- Specialization of `degree_minor_eq_diagExp` to the row-major lexicographic order. -/
theorem degree_minor_rowMajorLex
    (k : Type*) [CommRing k] [Nontrivial k] (I : MinorIndex m n t) :
    (rowMajorLex m n).degree (genericMinor k I) = diagExp I :=
  degree_minor_eq_diagExp k (rowMajorLex m n) (rowMajorLex_isDiagonal m n) I

/-- Specialization of `degree_minor_eq_antidiagExp` to the anti-diagonal lexicographic order. -/
theorem degree_minor_antiDiagonalLex
    (k : Type*) [CommRing k] [Nontrivial k] (I : MinorIndex m n t) :
    (antiDiagonalLex m n).degree (genericMinor k I) = antidiagExp I :=
  degree_minor_eq_antidiagExp k (antiDiagonalLex m n) (antiDiagonalLex_isAntidiagonal m n) I

/-- Specialization of `leadingTerm_minor_eq_diagMonomial` to the row-major lexicographic order. -/
theorem leadingTerm_minor_rowMajorLex
    (k : Type*) [CommRing k] [Nontrivial k] (I : MinorIndex m n t) :
    (rowMajorLex m n).leadingTerm (genericMinor k I) =
      diagMonomial k I :=
  leadingTerm_minor_eq_diagMonomial k (rowMajorLex m n) (rowMajorLex_isDiagonal m n) I

/-- Specialization of `leadingTerm_minor_eq_antidiagMonomial_coeff` to the anti-diagonal
lexicographic order. -/
theorem leadingTerm_minor_antiDiagonalLex
    (k : Type*) [CommRing k] [Nontrivial k] (I : MinorIndex m n t) :
    (antiDiagonalLex m n).leadingTerm (genericMinor k I) =
      MvPolynomial.monomial (antidiagExp I)
        (permCoeff k (Fin.revPerm : Equiv.Perm (Fin t))) :=
  leadingTerm_minor_eq_antidiagMonomial_coeff
    k (antiDiagonalLex m n) (antiDiagonalLex_isAntidiagonal m n) I

omit [Nontrivial k] in
lemma rowMajorLex_toSyn_lt_of_gap
    (E L : (Fin m × Fin n) →₀ ℕ)
    (x : Fin m × Fin n)
    (hEqBelow :
      ∀ y : Fin m × Fin n,
        @LT.lt (Fin m × Fin n) (rowMajorVarOrder m n).toLT y x →
          E y = L y)
    (hGap : E x < L x) :
    (rowMajorLex m n).toSyn E < (rowMajorLex m n).toSyn L := by
  classical
  let instLO : LinearOrder (Fin m × Fin n) := rowMajorVarOrder m n
  let instWF :
      @WellFoundedGT
        (Fin m × Fin n)
        (@Preorder.toLT _ instLO.toPreorder) := by
    simp [instLO, rowMajorWF]
  rw [show
      (rowMajorLex m n).toSyn E < (rowMajorLex m n).toSyn L ↔
      @LT.lt (Lex ((Fin m × Fin n) →₀ ℕ))
        (@Finsupp.instLTLex
          (Fin m × Fin n) ℕ
          inferInstance
          instLO.toLT
          instLTNat)
        (toLex E)
        (toLex L)
      by
        simpa [rowMajorLex, rowMajorWF, instLO, instWF] using
          (@MonomialOrder.lex_lt_iff
            (Fin m × Fin n)
            instLO
            instWF
            E
            L)]
  change Finsupp.Lex
      (fun x y : Fin m × Fin n => @LT.lt _ instLO.toLT x y)
      (fun a b : ℕ => a < b)
      E
      L
  rw [Finsupp.lex_def]
  refine ⟨x, ?_, hGap⟩
  intro y hy
  exact hEqBelow y hy


end LeadingTermConsequences

end Determinantal
