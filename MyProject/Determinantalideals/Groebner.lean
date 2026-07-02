/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
import MyProject.Determinantalideals.StraighteningLaw
import Groebner.Groebner

namespace Determinantal

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Hilbert function and Sturmfels' Gröbner basis theorem -/

/--
Once the degree-`d` part of the determinantal ring is identified with the span
of the standard bitableau basis vectors of degree `d`, Corollary 4 follows
from the filtered KRS correspondence.
-/
private theorem hilbertFunction_detRing_eq_card_monomialExp_width_le_of_RrDegree_eq_span
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hspan :
      RrDegree m n r k d =
        Submodule.span k
          (Set.range
            (fun B :
              { B : StandardYoungBitableauOfLengthLE m n r //
                  YoungBitableau.degree B.1.1 = d } =>
              b B.1))) :
    Module.finrank k (RrDegree m n r k d)
    =
    Nat.card
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d ∧ monomialWidth E ≤ r } := by
  calc
    Module.finrank k (RrDegree m n r k d)
        =
      Module.finrank k
        (Submodule.span k
          (Set.range
            (fun B :
              { B : StandardYoungBitableauOfLengthLE m n r //
                  YoungBitableau.degree B.1.1 = d } =>
              b B.1))) := by
          rw [hspan]
    _ =
      Nat.card
        { B : StandardYoungBitableauOfLengthLE m n r //
            YoungBitableau.degree B.1.1 = d } := by
          exact finrank_span_range_basis_subtype b
            (fun B : StandardYoungBitableauOfLengthLE m n r =>
              YoungBitableau.degree B.1.1 = d)
    _ =
      Nat.card
        { E : (Fin m × Fin n) →₀ ℕ //
            Finsupp.degree E = d ∧ monomialWidth E ≤ r } :=
          natCard_standardBitableau_lengthLE_degree_eq_monomial_widthLE m n r d

/--
The easy inclusion in the graded-basis compatibility needed for Corollary 4:
standard bitableaux of degree `d` map into the degree-`d` component of the
determinantal ring.
-/
private theorem span_standardBitableau_degree_le_RrDegree
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hb :
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1)) :
    Submodule.span k
      (Set.range
        (fun B :
          { B : StandardYoungBitableauOfLengthLE m n r //
              YoungBitableau.degree B.1.1 = d } =>
          b B.1))
      ≤ RrDegree m n r k d := by
  rw [Submodule.span_le]
  rintro x ⟨B, rfl⟩
  change b B.1 ∈ RrDegree m n r k d
  rw [hb B.1]
  refine ⟨YoungBitableau.toPolynomial k B.1.1.1, ?_, rfl⟩
  change YoungBitableau.toPolynomial k B.1.1.1 ∈
    MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d
  rw [MvPolynomial.mem_homogeneousSubmodule]
  simpa [B.2] using
    (YoungBitableau.toPolynomial_isHomogeneous k B.1.1.1)

/-- Homogeneous projection of a scalar multiple of a standard bitableau polynomial. -/
private lemma homogeneousComponent_C_mul_standardBitableauOfLengthLE_toPolynomial
    {m n r : ℕ}
    (k : Type*) [Field k]
    (d : ℕ) (a : k) (B : StandardYoungBitableauOfLengthLE m n r) :
    MvPolynomial.homogeneousComponent d
      (MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
      =
    if YoungBitableau.degree B.1.1 = d then
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1
    else
      0 := by
  rw [MvPolynomial.homogeneousComponent_C_mul]
  have hmem :
      YoungBitableau.toPolynomial k B.1.1 ∈
        MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k
          (YoungBitableau.degree B.1.1) := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact YoungBitableau.toPolynomial_isHomogeneous k B.1.1
  rw [MvPolynomial.homogeneousComponent_of_mem (m := d) hmem]
  by_cases hdeg : d = YoungBitableau.degree B.1.1
  · simp [hdeg]
  · have hdeg' : YoungBitableau.degree B.1.1 ≠ d := by
      exact fun h => hdeg h.symm
    simp [hdeg, hdeg']

/--
Homogeneous projection of a finite standard-bitableau expansion keeps exactly
the terms whose bitableaux have the chosen degree.
-/
private lemma homogeneousComponent_standardBitableauOfLengthLE_finsupp_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (c : StandardYoungBitableauOfLengthLE m n r →₀ k) :
    MvPolynomial.homogeneousComponent d
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
      =
    (c.filter fun B => YoungBitableau.degree B.1.1 = d).sum fun B a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1 := by
  classical
  rw [Finsupp.sum, map_sum]
  simp_rw [homogeneousComponent_C_mul_standardBitableauOfLengthLE_toPolynomial
    k]
  rw [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hdeg : YoungBitableau.degree B.1.1 = d
  · simp [hdeg]
  · simp [hdeg]

/--
The quotient map sends a finite standard-bitableau polynomial expansion to the
same linear combination of the standard-bitableau basis in the determinantal
ring.
-/
private lemma quotientMap_standardBitableau_finsupp_sum
    {m n : ℕ}
    (k : Type*) [Field k]
    (r : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hb :
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))
    (c : StandardYoungBitableauOfLengthLE m n r →₀ k) :
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
      (c.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
      =
    Finsupp.linearCombination k b c := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [hb B, MvPolynomial.C_mul', map_smul]
  rfl

/--
If the degree-`e` homogeneous component of a standard-bitableau expansion lies
in `J_r`, then the degree-`e` part of its coefficient vector is zero.  This is
the linear-independence step used to show that homogeneous quotient elements
have homogeneous standard-bitableau coordinates.
-/
private lemma standardBitableau_filter_eq_zero_of_homogeneousComponent_mem_Jr
    {m n : ℕ}
    (k : Type*) [Field k]
    (r e : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hb :
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))
    (c : StandardYoungBitableauOfLengthLE m n r →₀ k)
    (hmem :
      MvPolynomial.homogeneousComponent e
        (c.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
        ∈ Jr m n r k) :
    c.filter (fun B => YoungBitableau.degree B.1.1 = e) = 0 := by
  classical
  let cf := c.filter (fun B => YoungBitableau.degree B.1.1 = e)
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  have hqzero :
      q (MvPolynomial.homogeneousComponent e
        (c.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)) = 0 := by
    simpa [q] using (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  have hcomp :
      MvPolynomial.homogeneousComponent e
        (c.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1)
        =
      cf.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1 := by
    simpa [cf] using
      homogeneousComponent_standardBitableauOfLengthLE_finsupp_sum
        k r e c
  have hqcf :
      q (cf.sum fun B a =>
        MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1) = 0 := by
    rw [← hcomp]
    exact hqzero
  have hlin :
      Finsupp.linearCombination k b cf = 0 := by
    have hqmap :=
      quotientMap_standardBitableau_finsupp_sum
        k r b hb cf
    rw [← hqmap]
    exact hqcf
  have hrepr := congrArg b.repr hlin
  simpa [cf] using hrepr

/--
Elements of the degree-`d` component have standard-bitableau coordinates only
on standard bitableaux of degree `d`.
-/
private theorem standardBitableau_repr_support_of_mem_RrDegree
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hb :
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1)) :
    ∀ x : RrDegree m n r k d,
      ↑(b.repr x.1).support ⊆
        { B : StandardYoungBitableauOfLengthLE m n r |
            YoungBitableau.degree B.1.1 = d } := by
  classical
  intro x B hB
  rw [Set.mem_setOf_eq]
  by_contra hne
  let c : StandardYoungBitableauOfLengthLE m n r →₀ k := b.repr x.1
  let T : MvPolynomial (Fin m × Fin n) k :=
    c.sum fun B a =>
      MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1
  let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
    (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
  rcases x.2 with ⟨p, hpH, hpq⟩
  have hqT : q T = x.1 := by
    dsimp [T]
    change (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
        (c.sum fun B a =>
          MvPolynomial.C a * YoungBitableau.toPolynomial k B.1.1) = x.1
    rw [quotientMap_standardBitableau_finsupp_sum k r b hb c]
    exact b.linearCombination_repr x.1
  have hp_sub_T : p - T ∈ Jr m n r k := by
    have hzero : q (p - T) = 0 := by
      rw [map_sub, hpq, hqT, sub_self]
    simpa [q] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  let e := YoungBitableau.degree B.1.1
  have he_ne_d : e ≠ d := hne
  have hJhom :
      (Jr m n r k).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k) :=
    detIdeal_isHomogeneous k r
  have hcomp_sub :
      MvPolynomial.homogeneousComponent e (p - T) ∈ Jr m n r k :=
    by
      have hproj :
          GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k)
            e (p - T) ∈ Jr m n r k :=
        hJhom e hp_sub_T
      convert hproj using 1
      rw [GradedRing.proj_apply]
      simpa using
        (MvPolynomial.decomposition.decompose'_apply (φ := p - T) (i := e)).symm
  have hpcomp_zero :
      MvPolynomial.homogeneousComponent e p = 0 := by
    rw [MvPolynomial.homogeneousComponent_of_mem (m := e) hpH]
    simp [he_ne_d]
  have hcomp_sub_eq :
      MvPolynomial.homogeneousComponent e (p - T) =
        - MvPolynomial.homogeneousComponent e T := by
    rw [map_sub, hpcomp_zero, zero_sub]
  have hTcomp_mem :
      MvPolynomial.homogeneousComponent e T ∈ Jr m n r k := by
    have hneg :
        - MvPolynomial.homogeneousComponent e T ∈ Jr m n r k := by
      simpa [hcomp_sub_eq] using hcomp_sub
    simpa using (neg_mem_iff.mp hneg)
  have hfilter_zero :
      c.filter (fun B => YoungBitableau.degree B.1.1 = e) = 0 := by
    dsimp [T] at hTcomp_mem
    exact standardBitableau_filter_eq_zero_of_homogeneousComponent_mem_Jr
      k r e b hb c hTcomp_mem
  have hcB_ne : c B ≠ 0 := by
    simpa [c, Finsupp.mem_support_iff] using hB
  have hcB_zero : c B = 0 := by
    have happly :
        (c.filter fun B => YoungBitableau.degree B.1.1 = e) B = 0 := by
      rw [hfilter_zero]
      rfl
    simpa [Finsupp.filter_apply, e] using happly
  exact hcB_ne hcB_zero

/--
To prove the hard inclusion for Corollary 4, it is enough to show that every
element of the degree-`d` component has standard-bitableau coordinates supported
only on standard bitableaux of degree `d`.
-/
private theorem RrDegree_le_span_standardBitableau_degree_of_repr_support
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hsupport :
      ∀ x : RrDegree m n r k d,
        ↑(b.repr x.1).support ⊆
          { B : StandardYoungBitableauOfLengthLE m n r |
              YoungBitableau.degree B.1.1 = d }) :
    RrDegree m n r k d ≤
      Submodule.span k
        (Set.range
          (fun B :
            { B : StandardYoungBitableauOfLengthLE m n r //
                YoungBitableau.degree B.1.1 = d } =>
            b B.1)) := by
  intro y hy
  have hset :
      b ''
        { B : StandardYoungBitableauOfLengthLE m n r |
          YoungBitableau.degree B.1.1 = d } =
        Set.range
          (fun B :
            { B : StandardYoungBitableauOfLengthLE m n r //
                YoungBitableau.degree B.1.1 = d } =>
            b B.1) := by
    ext z
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨⟨B, hB⟩, rfl⟩
    · rintro ⟨B, rfl⟩
      exact ⟨B.1, B.2, rfl⟩
  rw [← hset]
  exact (b.mem_span_image).2 (hsupport ⟨y, hy⟩)

/--
The graded-basis compatibility needed for Corollary 4, packaged in terms of
the standard-bitableau coordinate support.
-/
private theorem RrDegree_eq_span_standardBitableau_degree_of_repr_support
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ)
    (b : Module.Basis (StandardYoungBitableauOfLengthLE m n r) k (Rr m n r k))
    (hb :
      ∀ B : StandardYoungBitableauOfLengthLE m n r,
        b B =
          Ideal.Quotient.mk (Jr m n r k)
            (YoungBitableau.toPolynomial k B.1.1))
    (hsupport :
      ∀ x : RrDegree m n r k d,
        ↑(b.repr x.1).support ⊆
          { B : StandardYoungBitableauOfLengthLE m n r |
              YoungBitableau.degree B.1.1 = d }) :
    RrDegree m n r k d =
      Submodule.span k
        (Set.range
          (fun B :
            { B : StandardYoungBitableauOfLengthLE m n r //
                YoungBitableau.degree B.1.1 = d } =>
            b B.1)) := by
  exact le_antisymm
    (RrDegree_le_span_standardBitableau_degree_of_repr_support k r d b hsupport)
    (span_standardBitableau_degree_le_RrDegree k r d b hb)

/--
Corollary 4.

The degree `d` Hilbert function of the determinantal ring `K[X] / J_r`
equals the number of monomial exponent vectors of total degree `d`
whose width is at most `r`.
-/
theorem hilbertFunction_detRing_eq_card_monomialExp_width_le
    {m n : ℕ}
    (k : Type*) [Field k]
    (r d : ℕ) :
    Module.finrank k (RrDegree m n r k d)
    =
    Nat.card
      { E : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E = d ∧
          monomialWidth E ≤ r } := by
  rcases exists_standardBitableau_basis_determinantalRing
       k r with
    ⟨b, hb⟩
  exact
    hilbertFunction_detRing_eq_card_monomialExp_width_le_of_RrDegree_eq_span
      k r d b
      (RrDegree_eq_span_standardBitableau_degree_of_repr_support
        k r d b hb
        (standardBitableau_repr_support_of_mem_RrDegree
          k r d b hb))

/--
Lemma 5, initial monomial version.

For the paper's anti-diagonal lexicographic order, the initial monomial of a minor is its
anti-diagonal monomial.  Since `MonomialOrder.degree` records the exponent vector of the
leading monomial, this is the coefficient-free version of the paper's `init(D)` statement.
-/
theorem antidiagonalLex_degree_genericMinor_eq_antidiagExp
    {m n r : ℕ}
    (k : Type*) [CommRing k] [Nontrivial k]
    (I : MinorIndex m n (r + 1)) :
    (antiDiagonalLex m n).degree (genericMinor k I) =
      antidiagExp I :=
  degree_minor_antiDiagonalLex k I

/-- Lemma 5 in Sturmfels' paper. -/
theorem lemma5_degree_minor_antiDiagonalLex
    {m n r : ℕ}
    (k : Type*) [CommRing k] [Nontrivial k]
    (I : MinorIndex m n (r + 1)) :
    (antiDiagonalLex m n).degree (genericMinor k I) =
      antidiagExp I :=
  antidiagonalLex_degree_genericMinor_eq_antidiagExp k I

/--
Lemma 5, Lean leading-term version.

Lean's `leadingTerm` includes the coefficient.  Therefore the leading term is the
anti-diagonal monomial with coefficient `sign(Fin.revPerm)`.
-/
theorem antidiagonalLex_leadingTerm_genericMinor_eq_antidiagMonomial
    {m n r : ℕ}
    (k : Type*) [CommRing k] [Nontrivial k]
    (I : MinorIndex m n (r + 1)) :
    (antiDiagonalLex m n).leadingTerm (genericMinor k I) =
      MvPolynomial.monomial (antidiagExp I)
        (permCoeff k (Fin.revPerm : Equiv.Perm (Fin (r + 1)))) :=
  leadingTerm_minor_antiDiagonalLex k I

/-- Lemma 5 in Sturmfels' paper, including the leading coefficient. -/
theorem lemma5_leadingTerm_minor_antiDiagonalLex
    {m n r : ℕ}
    (k : Type*) [CommRing k] [Nontrivial k]
    (I : MinorIndex m n (r + 1)) :
    (antiDiagonalLex m n).leadingTerm (genericMinor k I) =
      MvPolynomial.monomial (antidiagExp I)
        (permCoeff k (Fin.revPerm : Equiv.Perm (Fin (r + 1)))) :=
  antidiagonalLex_leadingTerm_genericMinor_eq_antidiagMonomial k I

/--
Lemma 6.

For the monomial ideal `init(G_{r+1})`, a monomial belongs to the ideal if and
only if its width is at least `r + 1` (equivalently, strictly greater than `r`).

Monomials are represented by exponent vectors `E`; the polynomial monomial is
`MvPolynomial.monomial E 1`.
-/
theorem monomial_mem_initGrPlusOne_iff_width
    {m n r : ℕ}
    (k : Type*) [Field k]
    (E : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.monomial E (1 : k) ∈ initGrPlusOne m n r k
      ↔ r + 1 ≤ monomialWidth E := by
  rw [monomial_mem_initGrPlusOne_iff_exists_antidiagExp_le k]
  constructor
  · exact lemma6_forward_exists_antidiagExp_le_width
  · intro hwidth
    rcases exists_antidiagIndexList_sublist_generalizedPermutation_of_le_monomialWidth
        (E := E) (t := r + 1) (Nat.succ_pos r) hwidth with
      ⟨I, hsub⟩
    exact ⟨I, antidiagExp_le_of_antidiagIndexList_sublist_generalizedPermutation I hsub⟩

/-- Lemma 6 in Sturmfels' paper. -/
theorem lemma6_monomial_mem_initGrPlusOne_iff_width
    {m n r : ℕ}
    (k : Type*) [Field k]
    (E : (Fin m × Fin n) →₀ ℕ) :
    MvPolynomial.monomial E (1 : k) ∈ initGrPlusOne m n r k
      ↔ r + 1 ≤ monomialWidth E :=
  monomial_mem_initGrPlusOne_iff_width k E

/--
Theorem 1, Gröbner-basis statement.

The set `G_{r+1}` of all `(r + 1) × (r + 1)` minors is a Gröbner basis of the
determinantal ideal `J_r` with respect to the anti-diagonal lexicographic order from
the paper.

The paper also says "reduced"; with Lean's `leadingTerm`, the anti-diagonal term of
a determinant carries the coefficient `sign(Fin.revPerm)`, so the reduced-basis
refinement should be stated separately using the coefficient-normalized minors.
-/
theorem theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ord.IsGroebnerBasis (GrPlusOne m n r k) (Jr m n r k) := by
  classical
  have hG_def :
      GrPlusOne m n r k = minorSet k m n (r + 1) := rfl
  have hJ_def : Jr m n r k = detIdeal m n (r + 1) k := rfl
  have hG_spans_J : Ideal.span (GrPlusOne m n r k) = Jr m n r k := by
    rw [hG_def, hJ_def]
    exact (detIdeal_eq_span_range (k := k) (m := m) (n := n) (t := r + 1)).symm
  have hG_subset_J : GrPlusOne m n r k ⊆ Jr m n r k := by
    intro f hf
    rw [← hG_spans_J]
    exact Ideal.subset_span hf
  -- Lemma 5 identifies the initial monomial of every generator in `G_{r+1}`.
  have hLemma5 :
      ∀ I : MinorIndex m n (r + 1),
        ord.degree (genericMinor k I) = antidiagExp I := by
    intro I
    exact degree_minor_eq_antidiagExp k ord hanti I
  -- Hence `init(G_{r+1})` is exactly the monomial ideal generated by those
  -- anti-diagonal monomials; Lemma 6 gives the paper's width criterion for it.
  have hLemma6 :
      ∀ E : (Fin m × Fin n) →₀ ℕ,
        MvPolynomial.monomial E (1 : k) ∈ initGrPlusOne m n r k
          ↔ r + 1 ≤ monomialWidth E := by
    intro E
    exact monomial_mem_initGrPlusOne_iff_width k E
  -- Corollary 4 supplies the Hilbert-function count for `R_r = K[X] / J_r`.
  have hCor4 :
      ∀ d : ℕ,
        Module.finrank k (RrDegree m n r k d)
        =
        Nat.card
          { E : (Fin m × Fin n) →₀ ℕ //
              Finsupp.degree E = d ∧ monomialWidth E ≤ r } := by
    intro d
    exact hilbertFunction_detRing_eq_card_monomialExp_width_le k r d
  change ord.IsGroebnerBasis (GrPlusOne m n r k) (Jr m n r k)
  by_contra hnotGB
  -- If `G_{r+1}` is not a Gröbner basis, then the initial ideal generated by
  -- `G_{r+1}` is strictly smaller than the initial ideal of `J_r`.
  have hnot_initial_subset :
      ¬ (ord.leadingTerm '' (↑(Jr m n r k) :
          Set (MvPolynomial (Fin m × Fin n) k)) ⊆
        (Ideal.span (ord.leadingTerm '' (GrPlusOne m n r k)) :
          Set (MvPolynomial (Fin m × Fin n) k))) := by
    intro hsubset
    apply hnotGB
    exact
      (MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff
        (m := ord) (GrPlusOne m n r k) (Jr m n r k)).mpr
        ⟨hG_subset_J, hsubset⟩
  -- Lemma 5 converts the leading terms of the generators into the monomial ideal
  -- `init(G_{r+1})` used in the paper.  The reverse-permutation signs are units
  -- over the field, so they do not change the generated ideal.
  have hinitG_from_lemma5 :
      Ideal.span (ord.leadingTerm '' (GrPlusOne m n r k)) =
        initGrPlusOne m n r k := by
    have hdegree_generators :
        ∀ I : MinorIndex m n (r + 1),
          ord.degree (genericMinor k I) = antidiagExp I := hLemma5
    -- This is a coefficient-normalization step: replace each signed leading term
    -- by the corresponding coefficient-one anti-diagonal monomial.
    calc
      Ideal.span (ord.leadingTerm '' (GrPlusOne m n r k))
          = Ideal.span
              ((fun p : MvPolynomial (Fin m × Fin n) k =>
                  MvPolynomial.monomial (ord.degree p) (1 : k)) ''
                (GrPlusOne m n r k)) := by
            exact MonomialOrder.span_leadingTerm_eq_span_monomial._replace_
              (m := ord)
              (B := GrPlusOne m n r k)
              (by
                intro p hp
                rcases hp with ⟨I, rfl⟩
                rw [leadingCoeff_minor_eq_revPermCoeff
                  k ord hanti I]
                exact isUnit_iff_ne_zero.mpr
                  (permCoeff_ne_zero k
                    (Fin.revPerm : Equiv.Perm (Fin (r + 1)))))
      _ = initGrPlusOne m n r k := by
            apply congrArg Ideal.span
            ext q
            constructor
            · rintro ⟨p, ⟨I, rfl⟩, rfl⟩
              exact ⟨I, by simp [hdegree_generators I, antidiagMonomial]⟩
            · rintro ⟨I, rfl⟩
              refine ⟨genericMinor k I, ⟨I, rfl⟩, ?_⟩
              simp [hdegree_generators I, antidiagMonomial]
  -- This is the paper's sentence: "Suppose on the contrary that there exists a
  -- monomial `m` ..."  Here `E` is the exponent vector of that monomial.
  let initJr : Ideal (MvPolynomial (Fin m × Fin n) k) :=
    Ideal.span (ord.leadingTerm '' (↑(Jr m n r k) :
      Set (MvPolynomial (Fin m × Fin n) k)))
  have hcounter_monomial :
      ∃ E : (Fin m × Fin n) →₀ ℕ,
        ((MvPolynomial.monomial E (1 : k) ∈ initJr) ∧
          (MvPolynomial.monomial E (1 : k) ∉ initGrPlusOne m n r k)) := by
    -- Extract a coefficient-one monomial from the failed initial-ideal inclusion
    -- and rewrite the smaller initial ideal using `hinitG_from_lemma5`.
    have hnot_initial_subset' :
        ¬ (ord.leadingTerm '' (↑(Jr m n r k) :
            Set (MvPolynomial (Fin m × Fin n) k)) ⊆
          (initGrPlusOne m n r k :
            Set (MvPolynomial (Fin m × Fin n) k))) := by
      intro hsubset
      exact hnot_initial_subset <| by
        intro x hx
        rw [hinitG_from_lemma5]
        exact hsubset hx
    rw [Set.subset_def] at hnot_initial_subset'
    push_neg at hnot_initial_subset'
    rcases hnot_initial_subset' with ⟨lt, hlt_mem_initJ, hlt_not_initG⟩
    rcases hlt_mem_initJ with ⟨f, hfJ, rfl⟩
    have hf_ne_zero : f ≠ 0 := by
      intro hf
      apply hlt_not_initG
      simp [hf]
    let E : (Fin m × Fin n) →₀ ℕ := ord.degree f
    have hleadCoeff_unit : IsUnit (ord.leadingCoeff f) :=
      isUnit_iff_ne_zero.mpr ((MonomialOrder.leadingCoeff_ne_zero_iff (m := ord)).mpr hf_ne_zero)
    have hlead_mem_initJ : ord.leadingTerm f ∈ initJr := by
      exact Ideal.subset_span ⟨f, hfJ, rfl⟩
    refine ⟨E, ?_, ?_⟩
    · have hscaled :
          MvPolynomial.C ((hleadCoeff_unit.unit⁻¹).val) * ord.leadingTerm f ∈ initJr :=
        Ideal.mul_mem_left _ _ hlead_mem_initJ
      convert hscaled using 1
      rw [MonomialOrder.leadingTerm]
      rw [MvPolynomial.C_mul_monomial]
      simp [E, inv_mul_cancel₀ ((MonomialOrder.leadingCoeff_ne_zero_iff (m := ord)).mpr hf_ne_zero)]
    · intro hmono
      apply hlt_not_initG
      have hscaled :
          MvPolynomial.C (ord.leadingCoeff f) * MvPolynomial.monomial E (1 : k) ∈
            initGrPlusOne m n r k :=
        Ideal.mul_mem_left _ _ hmono
      convert hscaled using 1
      rw [MonomialOrder.leadingTerm]
      simp [E, MvPolynomial.C_mul_monomial]
  rcases hcounter_monomial with ⟨E, hm_mem_initJ, hm_not_initG⟩
  -- "Let `d := deg(m)`."
  let d : ℕ := Finsupp.degree E
  have hm_degree : Finsupp.degree E = d := rfl
  -- Lemma 6 says that not belonging to `init(G_{r+1})` is the same as having
  -- width at most `r`.
  have hm_width_le : monomialWidth E ≤ r := by
    have hnot_width : ¬ (r + 1 ≤ monomialWidth E) := by
      intro hwidth
      exact hm_not_initG ((hLemma6 E).2 hwidth)
    exact Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnot_width)
  have hm_counted_by_cor4 :
      Finsupp.degree E = d ∧ monomialWidth E ≤ r := by
    exact ⟨hm_degree, hm_width_le⟩
  let CountedMonomials : Type :=
    { E0 : (Fin m × Fin n) →₀ ℕ //
        Finsupp.degree E0 = d ∧ monomialWidth E0 ≤ r }
  -- Since the monomial still lies in the initial ideal of `J_r`, the degree-`d`
  -- part of `init(J_r)` is strictly larger than the degree-`d` part generated by
  -- `init(G_{r+1})`.  Passing to quotients gives the strict Hilbert-function
  -- inequality used in the paper.
  have hstrict_hilbert :
      Module.finrank k (RrDegree m n r k d) < Nat.card CountedMonomials := by
    let H : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
      MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d
    let InitG_d : Submodule k H :=
      Submodule.comap H.subtype
        (Submodule.restrictScalars k (initGrPlusOne m n r k))
    let InitJ_d : Submodule k H :=
      Submodule.comap H.subtype
        (Submodule.restrictScalars k initJr)
    -- Paper: "Then the `d`-th graded component `(init(G_{r+1}))_d` is a proper
    -- `K`-linear subspace of `(init(J_r))_d`."  The witness is precisely the
    -- monomial `m = x^E`: it lies in `init(J_r)`, has degree `d`, but is not in
    -- `init(G_{r+1})`.
    have hm_homogeneous :
        MvPolynomial.monomial E (1 : k) ∈
          MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_monomial (1 : k) (by simp [d])
    have hm_mem_InitJ_d :
        (⟨MvPolynomial.monomial E (1 : k), hm_homogeneous⟩ :
          MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) ∈ InitJ_d := by
      -- This is just `hm_mem_initJ` plus the degree computation.
      simp_all only [minorSet_eq_range, Order.add_one_le_iff,
      Set.image_subset_iff, not_lt, true_and,
        Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.restrictScalars_mem,  initJr, d, H, InitJ_d]
    have hm_not_mem_InitG_d :
        (⟨MvPolynomial.monomial E (1 : k), hm_homogeneous⟩ :
          MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) ∉ InitG_d := by
      -- This is just `hm_not_initG` plus the definition of the degree component.
      simp_all only [minorSet_eq_range, Order.add_one_le_iff,
      Set.image_subset_iff, not_lt, true_and,
        Submodule.mem_comap, Submodule.subtype_apply,
        Submodule.restrictScalars_mem,  initJr, d, H, InitJ_d,
        InitG_d]
    have hInitG_lt_InitJ : InitG_d < InitJ_d := by
      -- The inclusion `init(G_{r+1}) ⊆ init(J_r)` comes from
      -- `G_{r+1} ⊆ J_r`; properness is witnessed by `m`.
      have hinitG_le_initJ : initGrPlusOne m n r k ≤ initJr := by
        rw [← hinitG_from_lemma5]
        apply Ideal.span_le.mpr
        rintro _ ⟨f, hfG, rfl⟩
        exact Ideal.subset_span ⟨f, hG_subset_J hfG, rfl⟩
      have hle : InitG_d ≤ InitJ_d := by
        intro x hx
        change (x : MvPolynomial (Fin m × Fin n) k) ∈ initJr
        change (x : MvPolynomial (Fin m × Fin n) k) ∈ initGrPlusOne m n r k at hx
        exact hinitG_le_initJ hx
      have hnle : ¬ InitJ_d ≤ InitG_d := by
        intro hreverse
        exact hm_not_mem_InitG_d (hreverse hm_mem_InitJ_d)
      exact lt_iff_le_not_ge.mpr ⟨hle, hnle⟩
    -- Paper: "Lemma 6 implies
    -- `{monomials of degree d and width > r+1} = dim_K (init(G_{r+1}))_d`."
    -- With our indexing convention this is the degree-`d` part generated by
    -- monomials whose width is at least `r + 1`.
    let WideMonomials : Type :=
      { E0 : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E0 = d ∧ r + 1 ≤ monomialWidth E0 }
    have hdim_InitG :
        Module.finrank k InitG_d = Nat.card WideMonomials := by
      -- Basis of a monomial ideal in degree `d`, then rewrite membership by Lemma 6.
      -- This is the formal content of the displayed equality following Lemma 6.
      let WideSet : Set ((Fin m × Fin n) →₀ ℕ) :=
        { E0 | Finsupp.degree E0 = d ∧ r + 1 ≤ monomialWidth E0 }
      have hinitG_mem_iff :
          ∀ p : MvPolynomial (Fin m × Fin n) k,
            p ∈ initGrPlusOne m n r k ↔
              ∀ E0 ∈ p.support, r + 1 ≤ monomialWidth E0 := by
        intro p
        rw [initGrPlusOne]
        rw [show
            (Set.range fun I : MinorIndex m n (r + 1) => antidiagMonomial k I) =
              ((fun s => MvPolynomial.monomial s (1 : k)) ''
                (Set.range fun I : MinorIndex m n (r + 1) => antidiagExp I)) by
          ext q
          constructor
          · rintro ⟨I, rfl⟩
            exact ⟨antidiagExp I, ⟨I, rfl⟩, rfl⟩
          · rintro ⟨s, ⟨I, rfl⟩, rfl⟩
            exact ⟨I, rfl⟩]
        rw [MvPolynomial.mem_ideal_span_monomial_image]
        constructor
        · intro hp E0 hE0
          rcases hp E0 hE0 with ⟨s, ⟨I, hs⟩, hle⟩
          subst hs
          exact antidiagExp_le_monomialWidth I hle
        · intro hp E0 hE0
          have hmono :
              MvPolynomial.monomial E0 (1 : k) ∈ initGrPlusOne m n r k :=
            (hLemma6 E0).2 (hp E0 hE0)
          rcases (monomial_mem_initGrPlusOne_iff_exists_antidiagExp_le k E0).1 hmono with
            ⟨I, hle⟩
          exact ⟨antidiagExp I, ⟨I, rfl⟩, hle⟩
      have hmap_InitG :
          InitG_d.map H.subtype = MvPolynomial.restrictSupport k WideSet := by
        ext p
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [MvPolynomial.mem_restrictSupport_iff]
          intro E0 hE0
          have hxH :
              (x : MvPolynomial (Fin m × Fin n) k) ∈
                MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d :=
            x.2
          have hdeg : Finsupp.degree E0 = d := by
            rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
              Finsupp.mem_supported] at hxH
            exact hxH hE0
          have hxG :
              (x : MvPolynomial (Fin m × Fin n) k) ∈ initGrPlusOne m n r k := by
            change (x : MvPolynomial (Fin m × Fin n) k) ∈ initGrPlusOne m n r k at hx
            exact hx
          exact ⟨hdeg, (hinitG_mem_iff _).1 hxG E0 hE0⟩
        · intro hp
          rw [MvPolynomial.mem_restrictSupport_iff] at hp
          have hpH :
              p ∈ MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := by
            rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
              Finsupp.mem_supported]
            intro E0 hE0
            exact (hp hE0).1
          have hpG : p ∈ initGrPlusOne m n r k := by
            exact (hinitG_mem_iff p).2 fun E0 hE0 => (hp hE0).2
          refine ⟨⟨p, hpH⟩, ?_, rfl⟩
          change p ∈ initGrPlusOne m n r k
          exact hpG
      calc
        Module.finrank k InitG_d
            = Module.finrank k (InitG_d.map H.subtype) := by
                exact (Submodule.equivMapOfInjective H.subtype
                H.injective_subtype InitG_d).finrank_eq
        _ = Module.finrank k (MvPolynomial.restrictSupport k WideSet) := by
                rw [hmap_InitG]
        _ = Nat.card WideMonomials := by
                rw [Module.finrank_eq_nat_card_basis
                  (MvPolynomial.basisRestrictSupport (R := k) WideSet)]
                rfl
    have hdim_InitJ_gt :
        Nat.card WideMonomials < Module.finrank k InitJ_d := by
      -- A proper inclusion of finite-dimensional subspaces gives strict dimension
      -- inequality, after substituting `hdim_InitG`.
      rw [← hdim_InitG]
      haveI : FiniteDimensional k H := by
        dsimp [H]
        exact homogeneousSubmodule_finite k d
      exact Submodule.finrank_lt_finrank_of_lt hInitG_lt_InitJ
    -- Paper: `dim_K (init(J_r))_d = dim_K K[X]_d - dim_K (R_r)_d`.
    -- This is the Hilbert-function equality between an ideal and its quotient.
    let DegreeMonomials : Type :=
      { E0 : (Fin m × Fin n) →₀ ℕ // Finsupp.degree E0 = d }
    have hdim_total :
        Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) =
          Nat.card DegreeMonomials := by
      -- The degree-`d` homogeneous component has the monomial basis of degree `d`.
      calc
        Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d)
            = Module.finrank k
                (MvPolynomial.restrictSupport k
                  { E0 : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E0 = d }) := by
                rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
                  MvPolynomial.restrictSupport]
        _ = Nat.card DegreeMonomials := by
                rw [Module.finrank_eq_nat_card_basis
                  (MvPolynomial.basisRestrictSupport
                    (R := k)
                    { E0 : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E0 = d })]
                rfl
    let InitJMonomials : Type :=
      { E0 : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∈ initJr }
    let StandardJMonomials : Type :=
      { E0 : (Fin m × Fin n) →₀ ℕ //
          Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∉ initJr }
    have hdim_InitJ_monomial :
        Module.finrank k InitJ_d = Nat.card InitJMonomials := by
      -- Since `init(J_r)` is a monomial ideal, its degree-`d` part has the
      -- monomial basis consisting of degree-`d` monomials that belong to it.
      have hinitJ_mem_iff :
          ∀ p : MvPolynomial (Fin m × Fin n) k,
            p ∈ initJr ↔
              ∀ E0 ∈ p.support, MvPolynomial.monomial E0 (1 : k) ∈ initJr := by
        intro p
        dsimp [initJr]
        rw [MonomialOrder.span_leadingTerm_eq_span_monomial' (m := ord)
          (B := (↑(Jr m n r k) : Set (MvPolynomial (Fin m × Fin n) k)))]
        change p ∈ Ideal.span
            (((fun s => MvPolynomial.monomial s (1 : k)) ∘ ord.degree) ''
              (↑(Jr m n r k) \ {0} :
                Set (MvPolynomial (Fin m × Fin n) k))) ↔
          ∀ E0 ∈ p.support,
            MvPolynomial.monomial E0 (1 : k) ∈ Ideal.span
              (((fun s => MvPolynomial.monomial s (1 : k)) ∘ ord.degree) ''
                (↑(Jr m n r k) \ {0} :
                  Set (MvPolynomial (Fin m × Fin n) k)))
        rw [Set.image_comp]
        rw [MvPolynomial.mem_ideal_span_monomial_image]
        constructor
        · intro hp E0 hE0
          rw [MvPolynomial.mem_ideal_span_monomial_image]
          intro E1 hE1
          have hE0E1 : E0 = E1 := by
            simpa using hE1
          subst E1
          exact hp E0 hE0
        · intro hp E0 hE0
          have hmono := hp E0 hE0
          rw [MvPolynomial.mem_ideal_span_monomial_image] at hmono
          exact hmono E0 (by
            simp)
      have hmap_InitJ :
          InitJ_d.map H.subtype =
            MvPolynomial.restrictSupport k
              { E0 : (Fin m × Fin n) →₀ ℕ |
                Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∈ initJr } := by
        ext p
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [MvPolynomial.mem_restrictSupport_iff]
          intro E0 hE0
          have hxH :
              (x : MvPolynomial (Fin m × Fin n) k) ∈
                MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := x.2
          have hdeg : Finsupp.degree E0 = d := by
            rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
              Finsupp.mem_supported] at hxH
            exact hxH hE0
          have hxJ : (x : MvPolynomial (Fin m × Fin n) k) ∈ initJr := by
            change (x : MvPolynomial (Fin m × Fin n) k) ∈ initJr at hx
            exact hx
          exact ⟨hdeg, (hinitJ_mem_iff _).1 hxJ E0 hE0⟩
        · intro hp
          rw [MvPolynomial.mem_restrictSupport_iff] at hp
          have hpH :
              p ∈ MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d := by
            rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
              Finsupp.mem_supported]
            intro E0 hE0
            exact (hp hE0).1
          have hpJ : p ∈ initJr := by
            exact (hinitJ_mem_iff p).2 fun E0 hE0 => (hp hE0).2
          refine ⟨⟨p, hpH⟩, ?_, rfl⟩
          change p ∈ initJr
          exact hpJ
      calc
        Module.finrank k InitJ_d
            = Module.finrank k (InitJ_d.map H.subtype) := by
                exact (Submodule.equivMapOfInjective H.subtype
                H.injective_subtype InitJ_d).finrank_eq
        _ = Module.finrank k
              (MvPolynomial.restrictSupport k
                { E0 : (Fin m × Fin n) →₀ ℕ |
                  Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∈ initJr }) := by
                rw [hmap_InitJ]
        _ = Nat.card InitJMonomials := by
                rw [Module.finrank_eq_nat_card_basis
                  (MvPolynomial.basisRestrictSupport
                    (R := k)
                    { E0 : (Fin m × Fin n) →₀ ℕ |
                      Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∈ initJr })]
                rfl
    -- Lemma 6 partitions the degree-`d` monomials into wide monomials and the
    -- counted normal monomials of width at most `r`.
    have hdegree_partition :
        Nat.card DegreeMonomials =
          Nat.card WideMonomials + Nat.card CountedMonomials := by
      -- The two subsets are complementary among degree-`d` monomials because
      -- `¬ r + 1 ≤ width` is equivalent to `width ≤ r`.
      let split : DegreeMonomials ≃ (WideMonomials ⊕ CountedMonomials) :=
      { toFun := fun E0 : DegreeMonomials =>
          if hwide : r + 1 ≤ monomialWidth E0.1 then
            Sum.inl ⟨E0.1, ⟨E0.2, hwide⟩⟩
          else
            Sum.inr ⟨E0.1, ⟨E0.2, Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hwide)⟩⟩
        invFun := fun s : WideMonomials ⊕ CountedMonomials =>
          match s with
          | Sum.inl E0 => ⟨E0.1, E0.2.1⟩
          | Sum.inr E0 => ⟨E0.1, E0.2.1⟩
        left_inv := by
          intro E0
          by_cases hwide : r + 1 ≤ monomialWidth E0.1
          · simp [hwide]
          · simp [hwide]
        right_inv := by
          intro s
          cases s with
          | inl E0 =>
              simp [E0.2.2]
          | inr E0 =>
              have hnot : ¬ r + 1 ≤ monomialWidth E0.1 := by
                omega
              simp [hnot] }
      have hDegreeFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E0 = d } := by
        exact (Finsupp.finite_of_degree_le (σ := Fin m × Fin n) d).subset
          (by
            intro E0 hE0
            exact le_of_eq hE0)
      have hWideFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ |
                Finsupp.degree E0 = d ∧ r + 1 ≤ monomialWidth E0 } :=
        hDegreeFinite.subset (by
          intro E0 hE0
          exact hE0.1)
      have hCountedFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ |
                Finsupp.degree E0 = d ∧ monomialWidth E0 ≤ r } :=
        hDegreeFinite.subset (by
          intro E0 hE0
          exact hE0.1)
      haveI : Finite WideMonomials := hWideFinite.to_subtype
      haveI : Finite CountedMonomials := hCountedFinite.to_subtype
      calc
        Nat.card DegreeMonomials
            = Nat.card (WideMonomials ⊕ CountedMonomials) := Nat.card_congr split
        _ = Nat.card WideMonomials + Nat.card CountedMonomials := by
            rw [Nat.card_sum]
    have hdegree_partition_initJ :
        Nat.card DegreeMonomials =
          Nat.card InitJMonomials + Nat.card StandardJMonomials := by
      -- The degree-`d` monomials split according to membership in the monomial
      -- initial ideal `init(J_r)`.
      let split : DegreeMonomials ≃ (InitJMonomials ⊕ StandardJMonomials) :=
      { toFun := fun E0 : DegreeMonomials =>
          if hmem : MvPolynomial.monomial E0.1 (1 : k) ∈ initJr then
            Sum.inl ⟨E0.1, ⟨E0.2, hmem⟩⟩
          else
            Sum.inr ⟨E0.1, ⟨E0.2, hmem⟩⟩
        invFun := fun s : InitJMonomials ⊕ StandardJMonomials =>
          match s with
          | Sum.inl E0 => ⟨E0.1, E0.2.1⟩
          | Sum.inr E0 => ⟨E0.1, E0.2.1⟩
        left_inv := by
          intro E0
          by_cases hmem : MvPolynomial.monomial E0.1 (1 : k) ∈ initJr
          · simp [hmem]
          · simp [hmem]
        right_inv := by
          intro s
          cases s with
          | inl E0 =>
              simp [E0.2.2]
          | inr E0 =>
              simp [E0.2.2] }
      have hDegreeFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ | Finsupp.degree E0 = d } := by
        exact (Finsupp.finite_of_degree_le (σ := Fin m × Fin n) d).subset
          (by
            intro E0 hE0
            exact le_of_eq hE0)
      have hInitJFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ |
                Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∈ initJr } :=
        hDegreeFinite.subset (by
          intro E0 hE0
          exact hE0.1)
      have hStandardFinite :
          Set.Finite
            { E0 : (Fin m × Fin n) →₀ ℕ |
                Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∉ initJr } :=
        hDegreeFinite.subset (by
          intro E0 hE0
          exact hE0.1)
      haveI : Finite InitJMonomials := hInitJFinite.to_subtype
      haveI : Finite StandardJMonomials := hStandardFinite.to_subtype
      calc
        Nat.card DegreeMonomials
            = Nat.card (InitJMonomials ⊕ StandardJMonomials) := Nat.card_congr split
        _ = Nat.card InitJMonomials + Nat.card StandardJMonomials := by
            rw [Nat.card_sum]
    have hstandard_lt_counted :
        Nat.card StandardJMonomials < Nat.card CountedMonomials := by
      have hInitJ_card_gt :
          Nat.card WideMonomials < Nat.card InitJMonomials := by
        simpa [hdim_InitJ_monomial] using hdim_InitJ_gt
      omega
    -- Combining the strict inequality for initial ideals with the two dimension
    -- equalities yields the paper's strict Hilbert-function inequality.
    have hquotient_le_standard :
        Module.finrank k (RrDegree m n r k d) ≤ Nat.card StandardJMonomials := by
      let StandardSet : Set ((Fin m × Fin n) →₀ ℕ) :=
        { E0 | Finsupp.degree E0 = d ∧ MvPolynomial.monomial E0 (1 : k) ∉ initJr }
      let StandardPoly : Submodule k (MvPolynomial (Fin m × Fin n) k) :=
        MvPolynomial.restrictSupport k StandardSet
      let q : MvPolynomial (Fin m × Fin n) k →ₗ[k] Rr m n r k :=
        (Ideal.Quotient.mkₐ k (Jr m n r k)).toLinearMap
      have hStandardFinite :
          Set.Finite StandardSet := by
        exact (Finsupp.finite_of_degree_le (σ := Fin m × Fin n) d).subset
          (by
            intro E0 hE0
            exact le_of_eq hE0.1)
      haveI : Finite StandardJMonomials := hStandardFinite.to_subtype
      haveI : Finite StandardSet := hStandardFinite.to_subtype
      haveI : Module.Finite k StandardPoly := by
        dsimp [StandardPoly]
        exact Module.Finite.of_basis
          (MvPolynomial.basisRestrictSupport (R := k) StandardSet)
      have hRr_le : RrDegree m n r k d ≤ Submodule.map q StandardPoly := by
        rintro y ⟨p, hpH, rfl⟩
        rcases MonomialOrder.IsRemainder.exists_isRemainder'
            (m := ord)
            (B := (↑(Jr m n r k) : Set (MvPolynomial (Fin m × Fin n) k))) p with
          ⟨rem, hrem⟩
        rcases hrem with ⟨⟨g, h_eq, _hdeg⟩, hsmall⟩
        have hrem_full :
            ord.IsRemainder p
              (↑(Jr m n r k) : Set (MvPolynomial (Fin m × Fin n) k)) rem :=
          ⟨⟨g, h_eq, _hdeg⟩, hsmall⟩
        let remd : MvPolynomial (Fin m × Fin n) k :=
          MvPolynomial.homogeneousComponent d rem
        have hp_sub_rem : p - rem ∈ Jr m n r k := by
          rw [h_eq]
          simp only [add_sub_cancel_right]
          rw [Finsupp.linearCombination_apply]
          exact Ideal.sum_mem _ fun b _ =>
            Ideal.mul_mem_left _ _ (show (b : MvPolynomial (Fin m × Fin n) k) ∈
              Jr m n r k from b.2)
        have hp_sub_remd : p - remd ∈ Jr m n r k := by
          have hJhom :
              (Jr m n r k).IsHomogeneous
                (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k) :=
            detIdeal_isHomogeneous k r
          have hcomp :
              GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k)
                d (p - rem) ∈ Jr m n r k :=
            hJhom d hp_sub_rem
          convert hcomp using 1
          rw [map_sub]
          have hproj_p :
              GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k)
                d p = p := by
            rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hpH]
          have hproj_rem :
              GradedRing.proj (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k)
                d rem = remd := by
            rw [GradedRing.proj_apply]
            dsimp [remd]
            simpa using
              (MvPolynomial.decomposition.decompose'_apply (φ := rem) (i := d))
          rw [hproj_p, hproj_rem]
        have hq_eq : q p = q remd := by
          have hzero : q (p - remd) = 0 := by
            simpa [q] using (Ideal.Quotient.eq_zero_iff_mem.mpr hp_sub_remd)
          simpa [q, map_sub, sub_eq_zero] using hzero
        have hremd_std : remd ∈ StandardPoly := by
          dsimp [StandardPoly]
          rw [MvPolynomial.mem_restrictSupport_iff]
          intro E0 hE0
          have hcoeff_ne :
              MvPolynomial.coeff E0 remd ≠ 0 := by
            simpa [MvPolynomial.mem_support_iff] using hE0
          dsimp [remd] at hcoeff_ne
          rw [MvPolynomial.coeff_homogeneousComponent] at hcoeff_ne
          by_cases hdeg : Finsupp.degree E0 = d
          · have hErem : E0 ∈ rem.support := by
              rw [MvPolynomial.mem_support_iff]
              intro hcoeff
              rw [hcoeff, if_pos hdeg] at hcoeff_ne
              exact hcoeff_ne rfl
            have hnot :
                MvPolynomial.monomial E0 (1 : k) ∉ initJr := by
              have hterm_not :
                  MvPolynomial.monomial E0 (rem.coeff E0) ∉ initJr := by
                simpa [initJr] using
                  MonomialOrder.IsRemainder.term_notMem_span_leadingTerm
                    (m := ord) hrem_full E0 hErem
              intro hmem
              exact hterm_not <| by
                simpa [MvPolynomial.C_mul_monomial] using
                  Ideal.mul_mem_left initJr (MvPolynomial.C (rem.coeff E0)) hmem
            exact ⟨hdeg, hnot⟩
          · rw [if_neg hdeg] at hcoeff_ne
            exact False.elim (hcoeff_ne rfl)
        refine ⟨remd, hremd_std, ?_⟩
        exact hq_eq.symm
      calc
        Module.finrank k (RrDegree m n r k d)
            ≤ Module.finrank k (Submodule.map q StandardPoly) :=
              Submodule.finrank_mono hRr_le
        _ ≤ Module.finrank k StandardPoly :=
              Submodule.finrank_map_le q StandardPoly
        _ = Nat.card StandardJMonomials := by
              dsimp [StandardPoly, StandardSet]
              rw [Module.finrank_eq_nat_card_basis
                (MvPolynomial.basisRestrictSupport
                  (R := k)
                  { E0 : (Fin m × Fin n) →₀ ℕ |
                    Finsupp.degree E0 = d ∧
                      MvPolynomial.monomial E0 (1 : k) ∉ initJr })]
              rfl
    exact lt_of_le_of_lt hquotient_le_standard hstandard_lt_counted
  -- Corollary 4 gives equality with the same cardinality, contradicting the
  -- strict inequality above.
  have hCor4_d := hCor4 d
  rw [hCor4_d] at hstrict_hilbert
  have hstrict_self : Nat.card CountedMonomials < Nat.card CountedMonomials := by
    simp [CountedMonomials] at hstrict_hilbert
  exact (lt_irrefl _ hstrict_self)

/--
Theorem 1 specialized to the concrete anti-diagonal lexicographic order.
-/
theorem theorem1_GrPlusOne_isGroebnerBasis
    {m n r : ℕ}
    (k : Type*) [Field k] :
    (antiDiagonalLex m n).IsGroebnerBasis (GrPlusOne m n r k) (Jr m n r k) :=
  theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder k
    (antiDiagonalLex m n)
    (antiDiagonalLex_isAntidiagonal m n)

/--
Sturmfels' Theorem 1 for any anti-diagonal term order.

The set `G_{r+1}` of all `(r + 1) × (r + 1)` generic minors is a Gröbner basis of
`J_r` whenever the term order makes the anti-diagonal term leading in every minor.
-/
theorem GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder
    {m n r : ℕ}
    (k : Type*) [Field k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hanti : IsAntidiagonalTermOrder ord) :
    ord.IsGroebnerBasis (GrPlusOne m n r k) (Jr m n r k) :=
  theorem1_GrPlusOne_isGroebnerBasis_of_isAntidiagonalTermOrder k ord hanti

/--
Sturmfels' Theorem 1 for the concrete anti-diagonal lexicographic order.

The set `G_{r+1}` of all `(r + 1) × (r + 1)` generic minors is a Gröbner basis of
`J_r` for `antiDiagonalLex`.
-/
theorem GrPlusOne_isGroebnerBasis_antiDiagonalLex
    {m n r : ℕ}
    {k : Type*} [Field k] :
    (antiDiagonalLex m n).IsGroebnerBasis (GrPlusOne m n r k) (Jr m n r k) :=
  theorem1_GrPlusOne_isGroebnerBasis k



end Determinantal
