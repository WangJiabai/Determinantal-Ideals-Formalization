/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.Groebner
import Groebner.Reduced

/-!
# Reduced Gröbner bases for determinantal ideals

This file strengthens the Gröbner-basis component of Sturmfels's Theorem 1 after
normalizing every minor by its anti-diagonal leading coefficient.
-/

namespace Determinantal

/-- A generic minor normalized by its anti-diagonal leading coefficient. -/
noncomputable def normalizedGenericMinor
    (k : Type*) [Field k]
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  let c :=
    permCoeff k (Fin.revPerm : Equiv.Perm (Fin t))
  c⁻¹ • genericMinor k I

/--
The set of generic `(r + 1) × (r + 1)` minors normalized by the
inverse of their common anti-diagonal leading coefficient.
-/
noncomputable def normalizedGrPlusOne
    (m n r : ℕ) (k : Type*) [Field k] :
    Set (MvPolynomial (Fin m × Fin n) k) :=
  Set.range fun I : MinorIndex m n (r + 1) =>
    normalizedGenericMinor k I

private lemma minorIndex_eq_of_antidiagExp_le_permExp
    {m n t : ℕ}
    (I J : MinorIndex m n t) (σ : Equiv.Perm (Fin t))
    (h : antidiagExp J ≤ permExp I σ) :
    I = J := by
  classical
  have hrow_subset :
      Finset.univ.map J.row.toEmbedding ⊆
        Finset.univ.map I.row.toEmbedding := by
    intro a ha
    rcases Finset.mem_map.1 ha with ⟨j, _hj, rfl⟩
    have hle := h (J.row j, J.col j.rev)
    rw [antidiagExp_apply_antidiag, permExp_apply] at hle
    by_cases hex :
        ∃ i : Fin t, I.row i = J.row j ∧ I.col (σ i) = J.col j.rev
    · rcases hex with ⟨i, hirow, _hicol⟩
      exact Finset.mem_map.2 ⟨i, Finset.mem_univ i, hirow⟩
    · simp [hex] at hle
  have hrow_finset_eq :
      Finset.univ.map J.row.toEmbedding =
        Finset.univ.map I.row.toEmbedding := by
    apply Finset.eq_of_subset_of_card_le hrow_subset
    simp
  have hcol_subset :
      Finset.univ.map J.col.toEmbedding ⊆
        Finset.univ.map I.col.toEmbedding := by
    intro b hb
    rcases Finset.mem_map.1 hb with ⟨j, _hj, rfl⟩
    have hle := h (J.row j.rev, J.col j)
    have hant : antidiagExp J (J.row j.rev, J.col j) = 1 := by
      simpa using antidiagExp_apply_antidiag m n J j.rev
    rw [hant, permExp_apply] at hle
    by_cases hex :
        ∃ i : Fin t,
          I.row i = J.row j.rev ∧ I.col (σ i) = J.col j
    · rcases hex with ⟨i, _hirow, hicol⟩
      exact Finset.mem_map.2 ⟨σ i, Finset.mem_univ _, by simpa using hicol⟩
    · simp [hex] at hle
  have hcol_finset_eq :
      Finset.univ.map J.col.toEmbedding =
        Finset.univ.map I.col.toEmbedding := by
    apply Finset.eq_of_subset_of_card_le hcol_subset
    simp
  have hrow_range : Set.range J.row = Set.range I.row := by
    ext a
    have ha := congrArg (fun s => a ∈ s) hrow_finset_eq
    simpa using ha
  have hcol_range : Set.range J.col = Set.range I.col := by
    ext b
    have hb := congrArg (fun s => b ∈ s) hcol_finset_eq
    simpa using hb
  apply MinorIndex.ext
  · intro a
    have hrow : J.row = I.row := (OrderEmbedding.range_inj).mp hrow_range
    exact congrArg (fun f => f a) hrow.symm
  · intro a
    have hcol : J.col = I.col := (OrderEmbedding.range_inj).mp hcol_range
    exact congrArg (fun f => f a) hcol.symm

/--
For an anti-diagonal term order, every original generic minor is a remainder of
itself upon division by the other minors. Thus the original minors already
satisfy the interreduction part of the library's definition of reducedness.
-/
theorem GrPlusOne_isInterreduced_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ∀ p ∈ GrPlusOne m n r k,
      ord.IsRemainder p (GrPlusOne m n r k \ {p}) p := by
  classical
  intro p hp
  rcases hp with ⟨I, rfl⟩
  rw [MonomialOrder.IsGroebnerBasis.IsRemainder.self_iff]
  intro a ha q hq _hq0 hle
  rcases hq.1 with ⟨J, rfl⟩
  have hne : genericMinor k J ≠ genericMinor k I := by
    simpa using hq.2
  rcases (genericMinor_mem_support_iff_exists_permExp k I a).1 ha with
    ⟨σ, rfl⟩
  rw [degree_minor_eq_antidiagExp k ord hanti J] at hle
  have hIJ := minorIndex_eq_of_antidiagExp_le_permExp I J σ hle
  subst J
  exact hne rfl

/--
The coefficient-normalized minors form a Gröbner basis for every anti-diagonal
term order.
-/
theorem normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (normalizedGrPlusOne m n r k)
      (Jr m n r k) := by
  classical
  let c : k :=
    permCoeff k (Fin.revPerm : Equiv.Perm (Fin (r + 1)))
  change ord.IsGroebnerBasis
    (Set.range fun I : MinorIndex m n (r + 1) =>
      c⁻¹ • genericMinor k I)
    (Jr m n r k)
  apply MonomialOrder.IsGroebnerBasis.smul
      (f := fun _ : MinorIndex m n (r + 1) => c⁻¹)
      (f' := fun I => genericMinor k I)
      (I := Jr m n r k)
  · intro I
    exact isUnit_iff_ne_zero.mpr
      (inv_ne_zero (permCoeff_ne_zero k
        (Fin.revPerm : Equiv.Perm (Fin (r + 1)))))
  · exact
      theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
        k ord hanti

/--
For every anti-diagonal term order, the coefficient-normalized minors satisfy
the library's reducedness condition for their Gröbner-basis proof.
-/
theorem normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    (normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
      (r := r) k ord hanti).IsReduced := by
  classical
  rw [MonomialOrder.IsGroebnerBasis.IsReduced.isReduced_def]
  constructor
  · intro p hp
    rcases hp with ⟨I, rfl⟩
    dsimp only [normalizedGenericMinor]
    rw [MonomialOrder.Monic, MvPolynomial.smul_eq_C_mul,
      ord.leadingCoeff_mul',
      ord.leadingCoeff_C,
      leadingCoeff_minor_eq_revPermCoeff k ord hanti I,
      inv_mul_cancel₀ (permCoeff_ne_zero k
        (Fin.revPerm : Equiv.Perm (Fin (r + 1))))]
  · intro p hp a ha q hq hpq hle
    rcases hp with ⟨I, rfl⟩
    rcases hq with ⟨J, rfl⟩
    dsimp only [normalizedGenericMinor] at ha hle hpq
    rw [MvPolynomial.support_smul_eq
      (inv_ne_zero (permCoeff_ne_zero k
        (Fin.revPerm : Equiv.Perm (Fin (r + 1)))))] at ha
    rcases (genericMinor_mem_support_iff_exists_permExp k I a).1 ha with
      ⟨σ, rfl⟩
    rw [ord.degree_smul_of_mem_nonZeroDivisors
        (by simp [permCoeff_ne_zero k
          (Fin.revPerm : Equiv.Perm (Fin (r + 1)))]),
      degree_minor_eq_antidiagExp k ord hanti J] at hle
    have hIJ := minorIndex_eq_of_antidiagExp_le_permExp I J σ hle
    subst J
    exact hpq rfl

/--
The coefficient-normalized minors form a reduced Gröbner basis for every
anti-diagonal term order.
-/
theorem normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ∃ hGB :
        ord.IsGroebnerBasis
          (normalizedGrPlusOne m n r k)
          (Jr m n r k),
      hGB.IsReduced := by
  refine ⟨normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
    (r := r) k ord hanti, ?_⟩
  exact normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder
    (r := r) k ord hanti

/--
The coefficient-normalized reduced Gröbner-basis refinement of the
Gröbner-basis component of Sturmfels's Theorem 1.
-/
theorem theorem1_normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ∃ hGB :
        ord.IsGroebnerBasis
          (normalizedGrPlusOne m n r k)
          (Jr m n r k),
      hGB.IsReduced :=
  normalizedGrPlusOne_isReducedGroebnerBasis_of_isAntidiagonalTermOrder
    (r := r) k ord hanti

/--
The reducedness of the coefficient-normalized minors for the concrete
anti-diagonal lexicographic order.
-/
theorem normalizedGrPlusOne_isReduced_antiDiagonalLex
    {m n r : ℕ}
    (k : Type*) [Field k] :
    (normalizedGrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
      (r := r) k (antiDiagonalLex m n)
      (antiDiagonalLex_isAntidiagonal m n)).IsReduced := by
  exact normalizedGrPlusOne_isReduced_of_isAntidiagonalTermOrder
    (r := r) k (antiDiagonalLex m n)
      (antiDiagonalLex_isAntidiagonal m n)

end Determinantal
