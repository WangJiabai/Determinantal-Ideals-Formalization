import Mathlib
import MyProject.Determinantalideals.Ideal
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.DiagonalOrder
import Groebner.Groebner
import Groebner.Remainder
import Groebner.Ideal

namespace Determinantal

section first

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

lemma minorSet_leadingCoeff_isUnit_or_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (t : ℕ) :
    ∀ g ∈ minorSet (m := m) (n := n) (k := k) t,
      IsUnit (ord.leadingCoeff g) ∨ g = 0 := by
  intro g hg
  rcases hg with ⟨I, rfl⟩
  left
  simp [leadingCoeff_minor_eq_one (ord := ord) hdiag I]

omit [Nontrivial k] in
lemma minorSet_subset_detIdeal (t : ℕ) :
    minorSet (m := m) (n := n) (k := k) t ⊆ detIdeal m n t k := by
  intro g hg
  rcases hg with ⟨I, rfl⟩
  exact minor_mem_detIdeal (k := k) I

theorem minorSet_isGroebnerBasis_iff_pairwise_sPolynomial_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (t : ℕ) :
    ord.IsGroebnerBasis
      (minorSet (k := k) t)
      (detIdeal m n t k)
      ↔
    ∀ I J : MinorIndex m n t,
      ord.IsRemainder
        (ord.sPolynomial (genericMinor I) (genericMinor J))
        (minorSet (k := k) t) 0 := by
  rw [detIdeal]
  refine
    (MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero₀
      (minorSet_leadingCoeff_isUnit_or_zero ord hdiag t)).trans ?_
  constructor
  · intro h I J
    exact h
      ⟨genericMinor I, ⟨I, rfl⟩⟩
      ⟨genericMinor J, ⟨J, rfl⟩⟩
  · intro h g₁ g₂
    rcases g₁ with ⟨g₁, hg₁⟩
    rcases g₂ with ⟨g₂, hg₂⟩
    rcases hg₁ with ⟨I, rfl⟩
    rcases hg₂ with ⟨J, rfl⟩
    exact h I J


end first

section second

theorem isRemainder_zero_range_iff
    {σ α : Type*}
    {ord : MonomialOrder σ}
    {R : Type*} [CommSemiring R]
    {f : α → MvPolynomial σ R}
    {p : MvPolynomial σ R} :
    ord.IsRemainder p (Set.range f) 0 ↔
      ∃ a : α →₀ MvPolynomial σ R,
        p = Finsupp.linearCombination _ f a ∧
        ∀ i ∈ a.support,
          ord.toWithBotSyn (ord.withBotDegree (f i)) +
            ord.toWithBotSyn (ord.withBotDegree (a i))
              ≤ ord.toWithBotSyn (ord.withBotDegree p) := by
  classical
  rw [MonomialOrder.IsRemainder.isRemainder_range p f 0]
  simp only [add_zero, MvPolynomial.support_zero, Finset.notMem_empty, ne_eq, IsEmpty.forall_iff,
    implies_true, and_true, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨a, ha, hdeg⟩
    exact ⟨a, ha, fun i hi => hdeg i⟩
  · rintro ⟨a, ha, hdeg⟩
    refine ⟨a, ha, ?_⟩
    intro i
    by_cases hi : i ∈ a.support
    · exact hdeg i (Finsupp.mem_support_iff.mp hi)
    · subst ha
      simp_all only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not,
        MonomialOrder.withBotDegree_zero, MonomialOrder.toWithBotSyn_apply_bot,
         WithBot.add_bot, bot_le]

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]

theorem isRemainder_zero_minorSet_iff
    (ord : MonomialOrder (Fin m × Fin n))
    {p : MvPolynomial (Fin m × Fin n) k} :
    ord.IsRemainder p (minorSet t) 0 ↔
      ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
        p = Finsupp.linearCombination _ (fun I ↦ genericMinor I) a ∧
        ∀ I ∈ a.support,
          ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
            ord.toWithBotSyn (ord.withBotDegree (a I))
              ≤ ord.toWithBotSyn (ord.withBotDegree p) := by
  simpa [minorSet]
    using (isRemainder_zero_range_iff (f := fun I : MinorIndex m n t ↦ genericMinor I) (p := p))


end second


section third

variable {m n t : ℕ}
variable (k : Type*) [CommRing k]



theorem sPolynomial_minor_eq [Nontrivial k]
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t) :
    ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      MvPolynomial.monomial (diagExp J - diagExp I) 1 * genericMinor I
        - MvPolynomial.monomial (diagExp I - diagExp J) 1 * genericMinor J := by
  simp only [MonomialOrder.sPolynomial, degree_minor_eq_diagExp ord hdiag J,
    degree_minor_eq_diagExp ord hdiag I, leadingCoeff_minor_eq_one ord hdiag J,
    leadingCoeff_minor_eq_one ord hdiag I]

end third

section fourth

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

def diagDisjoint (I J : MinorIndex m n t) : Prop :=
  Disjoint (diagExp I).support (diagExp J).support

theorem sPolynomial_minor_eq_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.sPolynomial (genericMinor I) (genericMinor J) =
      diagMonomial J * genericMinor (k := k) I - diagMonomial I * genericMinor J := by
  have hdisj' : Disjoint (diagExp I).support (diagExp J).support := by
    simpa [diagDisjoint] using hdisj
  have hsubJI : diagExp J - diagExp I = diagExp J := by
    ext x
    by_cases hI0 : diagExp I x = 0
    · simp [hI0]
    · have hJ0 : diagExp J x = 0 := by
        by_contra hJ0
        have hxI : x ∈ (diagExp I).support := by
          simp [Finsupp.mem_support_iff, hI0]
        have hxJ : x ∈ (diagExp J).support := by
          simp [Finsupp.mem_support_iff, hJ0]
        exact (Finset.disjoint_left.mp hdisj' hxI hxJ)
      simp [hJ0]
  have hsubIJ : diagExp I - diagExp J = diagExp I := by
    ext x
    by_cases hJ0 : diagExp J x = 0
    · simp [hJ0]
    · have hI0 : diagExp I x = 0 := by
        by_contra hI0
        have hxI : x ∈ (diagExp I).support := by
          simp [Finsupp.mem_support_iff, hI0]
        have hxJ : x ∈ (diagExp J).support := by
          simp [Finsupp.mem_support_iff, hJ0]
        exact (Finset.disjoint_left.mp hdisj' hxI hxJ)
      simp [hI0]
  rw [MonomialOrder.sPolynomial]
  rw [degree_minor_eq_diagExp ord hdiag I, degree_minor_eq_diagExp ord hdiag J]
  rw [leadingCoeff_minor_eq_one ord hdiag I, leadingCoeff_minor_eq_one ord hdiag J]
  rw [hsubJI, hsubIJ]
  simp [diagMonomial]

theorem sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      (diagMonomial J - genericMinor J) * genericMinor I
    + (genericMinor I - diagMonomial I) * genericMinor J := by
  rw[sPolynomial_minor_eq_of_diagDisjoint ord hdiag hdisj]
  ring


theorem withBotDegree_mul_genericMinor_eq_left
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t)
    {f : MvPolynomial (Fin m × Fin n) k} :
    ord.toWithBotSyn (ord.withBotDegree (f * genericMinor I)) =
      ord.toWithBotSyn (ord.withBotDegree f) +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
  have hreg : ord.leadingCoeff (genericMinor (k := k) I) ∈ nonZeroDivisors k := by
    have hunit : IsUnit (ord.leadingCoeff (genericMinor (k := k) I)) := by
      simp [leadingCoeff_minor_eq_one ord hdiag I]
    exact hunit.mem_nonZeroDivisors
  simpa using congrArg ord.toWithBotSyn
    (ord.withBotDegree_mul_of_right_mem_nonZeroDivisors hreg)

theorem withBotDegree_mul_genericMinor_eq_right
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t)
    {f : MvPolynomial (Fin m × Fin n) k} :
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I * f)) =
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
      ord.toWithBotSyn (ord.withBotDegree f) := by
  have hreg : ord.leadingCoeff (genericMinor (k := k) I) ∈ nonZeroDivisors k := by
    have hunit : IsUnit (ord.leadingCoeff (genericMinor (k := k) I)) := by
      simp [leadingCoeff_minor_eq_one  ord hdiag I]
    exact hunit.mem_nonZeroDivisors
  simpa using congrArg ord.toWithBotSyn
    (ord.withBotDegree_mul_of_left_mem_nonZeroDivisors hreg)

theorem minor_ne_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    genericMinor (k := k) I ≠ 0 := by
  rw [← ord.leadingCoeff_ne_zero_iff]
  simp [leadingCoeff_minor_eq_one ord hdiag I]

theorem withBotDegree_minor_sub_diag_lt_minor
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I : MinorIndex m n t) :
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      <
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) I)) := by
  have hminor : genericMinor (k := k) I ≠ 0 := minor_ne_zero (k := k) ord hdiag I
  by_cases hzero : genericMinor (k := k) I - diagMonomial I = 0
  · rw [hzero]
    refine bot_lt_iff_ne_bot.mpr ?_
    simpa [ord.withBotDegree_eq]
  · change
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      <
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I))
    refine (ord.withBotDegree_lt_withBotDegree_iff_of_ne_zero
      (f := genericMinor (k := k) I - diagMonomial I)
      (g := genericMinor (k := k) I)
      hzero).2 ?_
    have hlead :
        ord.leadingTerm (genericMinor (k := k) I) = ord.leadingTerm (diagMonomial I) := by
      rw [leadingTerm_minor_eq_diagMonomial (k := k) ord hdiag I]
      simp [diagMonomial]
    have hmem :
        ord.degree (genericMinor (k := k) I - diagMonomial I) ∈
          (genericMinor (k := k) I - diagMonomial I).support := by
      rw [MvPolynomial.mem_support_iff]
      simpa [MonomialOrder.leadingCoeff] using
        (ord.leadingCoeff_ne_zero_iff).2 hzero
    have hsupp :=
      ord.support_sub_of_leadingTerm_eq_leadingTerm
        (p := genericMinor (k := k) I) (q := diagMonomial I) hlead
        (a := ord.degree (genericMinor (k := k) I - diagMonomial I)) hmem
    rcases hsupp with h | h
    · exact h.2
    · have hdeg_diag :
          ord.degree (diagMonomial (k := k) I) = ord.degree (genericMinor (k := k) I) := by
        rcases ord.leadingTerm_eq_leadingTerm_iff.mp hlead with ⟨_, hdeg⟩
        exact hdeg.symm
      simpa [hdeg_diag] using h.2

theorem withBotDegree_tail_lt_minor
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (J : MinorIndex m n t) :
    ord.toWithBotSyn
      (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      <
    ord.toWithBotSyn
      (ord.withBotDegree (genericMinor (k := k) J)) := by
    have h :=
    withBotDegree_minor_sub_diag_lt_minor
      (k := k) (ord := ord) hdiag J
    rw [show diagMonomial J - genericMinor (k := k) J =
      -(genericMinor (k := k) J - diagMonomial J) by abel, ord.withBotDegree_neg]
    exact withBotDegree_minor_sub_diag_lt_minor ord hdiag J

omit [Nontrivial k] in
theorem degree_tail_eq_permExp
    (ord : MonomialOrder (Fin m × Fin n))
    (I : MinorIndex m n t)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0) :
    ∃ σ : Equiv.Perm (Fin t),
      σ ≠ 1 ∧
      ord.degree (genericMinor (k := k) I - diagMonomial I) = permExp I σ := by
  classical
  let c := ord.degree (genericMinor (k := k) I - diagMonomial I)
  have htail :
      genericMinor (k := k) I - diagMonomial I =
        ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), permTerm (k := k) I σ := by
    rw [minor_eq_sum_permTerm (k := k) I]
    simp only [Finset.mem_univ, Finset.sum_erase_eq_sub, permTerm_one_eq_diagMonomial]
  have hcoeff :
      MvPolynomial.coeff c (genericMinor (k := k) I - diagMonomial I) ≠ 0 := by
    simpa [c, MonomialOrder.leadingCoeff] using
      (ord.leadingCoeff_ne_zero_iff).2 hI
  rw [htail, MvPolynomial.coeff_sum] at hcoeff
  have hex :
      ∃ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)),
        MvPolynomial.coeff c (permTerm (k := k) I σ) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hcoeff <| by
      refine Finset.sum_eq_zero ?_
      intro σ hσ
      exact h σ hσ
  rcases hex with ⟨σ, hσmem, hσcoeff⟩
  have hσne : σ ≠ 1 := (Finset.mem_erase.mp hσmem).1
  have hc_eq : c = permExp I σ := by
    by_contra hne
    have : MvPolynomial.coeff c (permTerm (k := k) I σ) = 0 := by
      simp [coeff_permTerm, hne]
    exact hσcoeff this
  refine ⟨σ, hσne, ?_⟩
  simpa [c] using hc_eq

omit [Nontrivial k] in
theorem degree_diag_sub_minor_eq_permExp
    (ord : MonomialOrder (Fin m × Fin n))
    (J : MinorIndex m n t)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ∃ σ : Equiv.Perm (Fin t),
      σ ≠ 1 ∧
      ord.degree (diagMonomial J - genericMinor (k := k) J) = permExp J σ := by
  have hnegJ :
      -(diagMonomial J - genericMinor (k := k) J) =
        genericMinor (k := k) J - diagMonomial J := by
    abel
  have hJ' : genericMinor (k := k) J - diagMonomial J ≠ 0 := by
    simpa [hnegJ] using (neg_ne_zero.mpr hJ)
  rcases degree_tail_eq_permExp ord J hJ' with
    ⟨σ, hσ, hdeg⟩
  refine ⟨σ, hσ, ?_⟩
  calc
    ord.degree (diagMonomial J - genericMinor (k := k) J)
        = ord.degree (-(genericMinor (k := k) J - diagMonomial J)) := by
            congr 1
            abel
    _ = ord.degree (genericMinor (k := k) J - diagMonomial J) := by rw [MonomialOrder.degree_neg]
    _ = permExp J σ := hdeg

theorem permExp_add_diagExp_ne_diagExp_add_permExp_of_diagDisjoint
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    {σ τ : Equiv.Perm (Fin t)}
    (hσ : σ ≠ 1) :
    permExp J σ + diagExp I ≠ permExp I τ + diagExp J := by
  classical
  have hdisj' : Disjoint (diagExp I).support (diagExp J).support := by
    simpa [diagDisjoint] using hdisj
  rcases exists_min_moved hσ with ⟨j0, hmove, hfix_before⟩
  let d : Fin m × Fin n := (J.row j0, J.col j0)
  have hdJ_mem : d ∈ (diagExp J).support := by
    have : diagExp J d = 1 := by
      simp [d]
    exact by
      simp [Finsupp.mem_support_iff, this, d]
  have hdI_not : d ∉ (diagExp I).support := by
    intro hdI
    exact (Finset.disjoint_left.mp hdisj' hdI hdJ_mem)
  have hdI_zero : diagExp I d = 0 := by
    by_contra hne
    exact hdI_not <| by
      simp [Finsupp.mem_support_iff, hne]
  have hleft_zero : (permExp J σ + diagExp I) d = 0 := by
    simp [Finsupp.add_apply, d, hdI_zero,
      permExp_apply_diag_eq_zero J σ hmove hfix_before]
  have hright_ne_zero : (permExp I τ + diagExp J) d ≠ 0 := by
    simp [Finsupp.add_apply, d, diagExp_apply_diag]
  intro hEq
  have hval := congrArg (fun e => e d) hEq
  simp only [hleft_zero, Finsupp.coe_add, Pi.add_apply] at hval
  exact Ne.elim hright_ne_zero (id (Eq.symm hval))

theorem tail_products_have_distinct_withBotDegree_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ord.toWithBotSyn (ord.withBotDegree
      ((diagMonomial J - genericMinor (k := k) J) * genericMinor (k := k) I))
    ≠
    ord.toWithBotSyn (ord.withBotDegree
      ((genericMinor (k := k) I - diagMonomial I) * genericMinor J)) := by
  classical
  rcases degree_diag_sub_minor_eq_permExp ord J hJ with
    ⟨σ, hσ, hdegJ⟩
  rcases degree_tail_eq_permExp ord I hI with
    ⟨τ, hτ, hdegI⟩
  intro hEq
  have hmulL :
      ord.toWithBotSyn
        (ord.withBotDegree
          ((diagMonomial J - genericMinor (k := k) J) * genericMinor (k := k) I))
      =
      ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
    simpa using
      withBotDegree_mul_genericMinor_eq_left ord hdiag I
  have hmulR :
      ord.toWithBotSyn
        (ord.withBotDegree
          ((genericMinor (k := k) I - diagMonomial I) * genericMinor J))
      =
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
      +
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) := by
    simpa using
      withBotDegree_mul_genericMinor_eq_left ord hdiag J
        (f := genericMinor (k := k) I - diagMonomial I)
  have hsumEq :
      (((ord.toSyn (permExp J σ) : ord.syn) : WithBot ord.syn) +
        ((ord.toSyn (diagExp I) : ord.syn) : WithBot ord.syn))
        =
      (((ord.toSyn (permExp I τ) : ord.syn) : WithBot ord.syn) +
        ((ord.toSyn (diagExp J) : ord.syn) : WithBot ord.syn)) := by
    rw [hmulL, hmulR] at hEq
    simpa [ord.withBotDegree_eq, hJ, hI, (minor_ne_zero ord hdiag I), (minor_ne_zero ord hdiag J),
      hdegJ, hdegI,
      degree_minor_eq_diagExp (k := k) ord hdiag I,
      degree_minor_eq_diagExp (k := k) ord hdiag J,
      ord.toWithBotSyn_apply_coe] using hEq
  have hdegEq' :
      ((ord.toSyn (permExp J σ + diagExp I) : ord.syn) : WithBot ord.syn)
        =
      ((ord.toSyn (permExp I τ + diagExp J) : ord.syn) : WithBot ord.syn) := by
    simpa [← WithBot.coe_add, ← map_add] using hsumEq
  have hdegEq :
      ord.toSyn (permExp J σ + diagExp I)
        =
      ord.toSyn (permExp I τ + diagExp J) := by
    exact_mod_cast hdegEq'
  have hcontra :
      permExp J σ + diagExp I ≠ permExp I τ + diagExp J :=
    permExp_add_diagExp_ne_diagExp_add_permExp_of_diagDisjoint
      (I := I) (J := J) hdisj hσ
  exact hcontra (ord.toSyn.injective hdegEq)

omit [Nontrivial k] in
theorem toWithBotSyn_withBotDegree_add_eq_max_of_ne
    (ord : MonomialOrder (Fin m × Fin n))
    {f g : MvPolynomial (Fin m × Fin n) k}
    (hne : ord.withBotDegree f ≠ ord.withBotDegree g) :
    ord.toWithBotSyn (ord.withBotDegree (f + g)) =
      max (ord.toWithBotSyn (ord.withBotDegree f))
          (ord.toWithBotSyn (ord.withBotDegree g)) := by
  have hne' :
      ord.toWithBotSyn (ord.withBotDegree f) ≠
      ord.toWithBotSyn (ord.withBotDegree g) := by
    intro h
    apply hne
    exact ord.toWithBotSyn.injective h
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hadd :
        ord.withBotDegree (f + g) = ord.withBotDegree g := by
      exact ord.withBotDegree_add_of_right_lt (f := f) (g := g) hlt
    rw [hadd]
    exact (max_eq_right_of_lt hlt).symm
  · have hadd :
        ord.withBotDegree (f + g) = ord.withBotDegree f := by
      exact ord.withBotDegree_add_of_lt (f := f) (g := g) hgt
    rw [hadd]
    exact (max_eq_left_of_lt hgt).symm


theorem degree_bound_left_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hJ : diagMonomial J - genericMinor (k := k) J ≠ 0) :
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
      ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
      ≤
      ord.toWithBotSyn
        (ord.withBotDegree
          (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  let A := (diagMonomial J - genericMinor J) * genericMinor (k := k) I
  let B := (genericMinor (k := k) I - diagMonomial I) * genericMinor J
  have hs :
      ord.sPolynomial (genericMinor I) (genericMinor J) = A + B := by
    simp [A, B, sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj]
  have hAdeg :
      ord.toWithBotSyn (ord.withBotDegree A) =
        ord.toWithBotSyn (ord.withBotDegree (diagMonomial (k := k) J - genericMinor J)) +
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) := by
    simp [A, withBotDegree_mul_genericMinor_eq_left (k := k) (ord := ord) hdiag I, add_comm]
  by_cases hI : genericMinor (k := k) I - diagMonomial I = 0
  · have hB0 : B = 0 := by
      simp [B, hI]
    have hsA :
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) = A := by
      rw [hs, hB0, add_zero]
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
          ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
          =
        ord.toWithBotSyn (ord.withBotDegree A) := by
          rw [hAdeg, add_comm]
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          rw [hsA]
    trivial
  · have hAB_ne_syn :
        ord.toWithBotSyn (ord.withBotDegree A) ≠
        ord.toWithBotSyn (ord.withBotDegree B) := by
      simpa [A, B] using
        tail_products_have_distinct_withBotDegree_of_diagDisjoint
          (k := k) (ord := ord) hdiag hdisj hI hJ
    have hAB_ne :
        ord.withBotDegree A ≠ ord.withBotDegree B := by
      intro hEq
      apply hAB_ne_syn
      simp [hEq]
    have hsdeg :
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) =
          max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := by
      rw [hs]
      exact toWithBotSyn_withBotDegree_add_eq_max_of_ne (ord := ord) hAB_ne
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) I)) +
          ord.toWithBotSyn (ord.withBotDegree (diagMonomial J - genericMinor (k := k) J))
          =
        ord.toWithBotSyn (ord.withBotDegree A) := by
          rw [hAdeg, add_comm]
      _ ≤ max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := le_max_left _ _
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          exact hsdeg.symm

theorem degree_bound_right_tail_coeff_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J)
    (hI : genericMinor (k := k) I - diagMonomial I ≠ 0) :
    ord.toWithBotSyn
        (ord.withBotDegree (genericMinor (k := k) J)) +
      ord.toWithBotSyn
        (ord.withBotDegree
          (genericMinor (k := k) I - diagMonomial I))
      ≤
      ord.toWithBotSyn (ord.withBotDegree
        (ord.sPolynomial (genericMinor (k:= k) I) (genericMinor J))) := by
  let A := (diagMonomial J - genericMinor J) * genericMinor (k := k) I
  let B := (genericMinor (k := k) I - diagMonomial I) * genericMinor J
  have hs :
      ord.sPolynomial (genericMinor I) (genericMinor J) = A + B := by
    simp [A, B, sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
      (k := k) (ord := ord) hdiag hdisj]
  have hBdeg :
      ord.toWithBotSyn (ord.withBotDegree B) =
        ord.toWithBotSyn
          (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I)) +
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) := by
    simp [B, withBotDegree_mul_genericMinor_eq_left
      (k := k) (ord := ord) hdiag J, add_comm]
  by_cases hJ : diagMonomial (k := k) J - genericMinor J = 0
  · have hA0 : A = 0 := by
      simp [A, hJ]
    have hsB :
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) = B := by
      rw [hs, hA0, zero_add]
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) +
          ord.toWithBotSyn
            (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
          =
        ord.toWithBotSyn (ord.withBotDegree B) := by
          rw [hBdeg, add_comm]
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          rw [hsB]
    trivial
  · have hAB_ne_syn :
        ord.toWithBotSyn (ord.withBotDegree A) ≠
        ord.toWithBotSyn (ord.withBotDegree B) := by
      simpa [A, B] using
        tail_products_have_distinct_withBotDegree_of_diagDisjoint
          (k := k) (ord := ord) hdiag hdisj hI hJ
    have hAB_ne :
        ord.withBotDegree A ≠ ord.withBotDegree B := by
      intro hEq
      apply hAB_ne_syn
      simp [hEq]
    have hsdeg :
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) =
          max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := by
      rw [hs]
      exact toWithBotSyn_withBotDegree_add_eq_max_of_ne (ord := ord) hAB_ne
    calc
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) J)) +
          ord.toWithBotSyn
            (ord.withBotDegree (genericMinor (k := k) I - diagMonomial I))
          =
        ord.toWithBotSyn (ord.withBotDegree B) := by
          rw [hBdeg, add_comm]
      _ ≤ max (ord.toWithBotSyn (ord.withBotDegree A))
              (ord.toWithBotSyn (ord.withBotDegree B)) := le_max_right _ _
      _ =
        ord.toWithBotSyn
          (ord.withBotDegree
            (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
          symm
          exact hsdeg

theorem exists_diagDisjoint_sPolynomial_certificate
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      ord.sPolynomial (genericMinor (k := k) I) (genericMinor J) =
      Finsupp.linearCombination _ (fun K ↦ genericMinor K) a
      ∧
      ∀ K ∈ a.support,
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
      ord.toWithBotSyn (ord.withBotDegree (a K))
    ≤ ord.toWithBotSyn (ord.withBotDegree
    (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  classical
  by_cases hIJ : I = J
  · refine ⟨0, ?_, ?_⟩
    · subst hIJ
      simp [MonomialOrder.sPolynomial]
    · intro K hK
      simp at hK
  · let a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
      Finsupp.single I (diagMonomial J - genericMinor (k := k) J) +
      Finsupp.single J (genericMinor (k := k) I - diagMonomial I)
    refine ⟨a, ?_, ?_⟩
    · calc
        ord.sPolynomial (genericMinor (k := k) I) (genericMinor J)
            =
          (diagMonomial J - genericMinor J) * genericMinor I
            +
          (genericMinor I - diagMonomial I) * genericMinor J := by
              simpa using
                sPolynomial_minor_eq_tail_certificate_of_diagDisjoint
                  (k := k) (ord := ord) hdiag hdisj
        _ =
          Finsupp.linearCombination _ (fun K ↦ genericMinor K) a := by
            simp [a]
            ring
    · intro K hK
      rw [Finsupp.mem_support_iff] at hK
      by_cases hKI : K = I
      · subst hKI
        have hcoeffJ : diagMonomial J - genericMinor (k := k) J ≠ 0 := by
          simpa [a, hIJ] using hK
        have hval : a K = diagMonomial J - genericMinor (k := k) J := by
          simp [a, hIJ]
        simpa [hval] using
          degree_bound_left_tail_coeff_of_diagDisjoint
            (k := k) (ord := ord) hdiag hdisj hcoeffJ
      · by_cases hKJ : K = J
        · subst hKJ
          have hJI : K ≠ I := by
            intro h
            exact hIJ h.symm
          have hcoeffI : genericMinor (k := k) I - diagMonomial I ≠ 0 := by
            simpa [a, hIJ, hJI] using hK
          have hval : a K = genericMinor (k := k) I - diagMonomial I := by
            simp [a, hJI]
          simpa [hval] using
            degree_bound_right_tail_coeff_of_diagDisjoint ord hdiag hdisj hcoeffI
        · exfalso
          have : a K = 0 := by
            simp [a, hKI, hKJ]
          exact hK this

theorem isRemainder_sPolynomial_minor_zero_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ord.IsRemainder
      (ord.sPolynomial (genericMinor I) (genericMinor J)) (minorSet (k := k) t) 0 := by
  rw [isRemainder_zero_minorSet_iff]
  exact exists_diagDisjoint_sPolynomial_certificate ord hdiag hdisj

end fourth

section fifthPrep

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

/-- The `S`-polynomial of two generic minors. -/
noncomputable abbrev sPolyMinor
    (ord : MonomialOrder (Fin m × Fin n))
    (I J : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) k :=
  ord.sPolynomial (genericMinor I) (genericMinor J)

/-- Complexity of a pair of minors: the number of common diagonal variables. -/
noncomputable def complexity (I J : MinorIndex m n t) : ℕ :=
  ((diagExp I).support ∩ (diagExp J).support).card

lemma complexity_eq_zero_iff_diagDisjoint
    (I J : MinorIndex m n t) :
    complexity I J = 0 ↔ diagDisjoint I J := by
  classical
  unfold complexity diagDisjoint
  rw [Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.symm

lemma complexity_pos_iff_not_diagDisjoint
    (I J : MinorIndex m n t) :
    0 < complexity I J ↔ ¬ diagDisjoint I J := by
  classical
  rw [← complexity_eq_zero_iff_diagDisjoint (I := I) (J := J)]
  exact pos_iff_ne_zero

lemma exists_common_diag_of_complexity_pos
    {I J : MinorIndex m n t}
    (hpos : 0 < complexity I J) :
    ∃ x : Fin m × Fin n,
      x ∈ (diagExp I).support ∧ x ∈ (diagExp J).support := by
  classical
  have hne :
      ((diagExp I).support ∩ (diagExp J).support).Nonempty := by
    exact Finset.card_pos.mp hpos
  rcases hne with ⟨x, hx⟩
  exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩

/-- A coefficient family certifying that `p` is a linear combination of minors
with the required degree bounds. -/
def IsMinorCertificate
    (ord : MonomialOrder (Fin m × Fin n))
    (p : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) : Prop :=
  p = Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) a ∧
  ∀ K ∈ a.support,
    ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
      ord.toWithBotSyn (ord.withBotDegree (a K))
        ≤ ord.toWithBotSyn (ord.withBotDegree p)

omit [Nontrivial k] in
lemma isMinorCertificate_iff
    (ord : MonomialOrder (Fin m × Fin n))
    (p : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) :
    IsMinorCertificate (k := k) ord p a ↔
      p = Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) a ∧
      ∀ K ∈ a.support,
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
          ord.toWithBotSyn (ord.withBotDegree (a K))
            ≤ ord.toWithBotSyn (ord.withBotDegree p) := by
  rfl

lemma exists_minorCertificate_of_diagDisjoint
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (hdisj : diagDisjoint I J) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      IsMinorCertificate (k := k) ord (sPolyMinor (k := k) ord I J) a := by
  simpa [sPolyMinor, IsMinorCertificate] using
    exists_diagDisjoint_sPolynomial_certificate
      (k := k) (ord := ord) hdiag hdisj

/-- Multiply every coefficient in a finitely supported family by the same polynomial on the left. -/
noncomputable def coeffMul
    (q : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) :
    MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
  a.mapRange (fun f => q * f) (by simp)

omit [Nontrivial k] in
@[simp] lemma coeffMul_apply
    (q : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k)
    (K : MinorIndex m n t) :
    coeffMul q a K = q * a K := by
  simp [coeffMul]

omit [Nontrivial k] in
lemma coeffMul_support_subset
    (q : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) :
    (coeffMul q a).support ⊆ a.support := by
  intro K hK
  by_contra hnot
  have : a K = 0 := Finsupp.notMem_support_iff.mp hnot
  have hzero : coeffMul q a K = 0 := by
    simp [coeffMul_apply, this]
  simp_all only [Finsupp.mem_support_iff, ne_eq, not_true_eq_false]

omit [Nontrivial k] in
lemma linearCombination_coeffMul
    (q : MvPolynomial (Fin m × Fin n) k)
    (a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) :
    Finsupp.linearCombination _ (fun K ↦ genericMinor K)
        (coeffMul q a)
      =
    q *
      Finsupp.linearCombination _ (fun K ↦ genericMinor K) a := by
  have hcoeff : coeffMul q a = q • a := by
    ext K
    simp [coeffMul]
  rw [hcoeff]
  simp [smul_eq_mul]

omit [Nontrivial k] in
lemma linearCombination_add
    (a b : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k) :
    Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) (a + b)
      =
    Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) a
      +
    Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) b := by
  simp only [map_add]

/-- One reduction step for the `S`-polynomial of two minors:
either it is already a direct certificate, or it reduces to a smaller pair. -/
inductive SPolynomialStepResult
    (ord : MonomialOrder (Fin m × Fin n))
    (I J : MinorIndex m n t) where
  | done
      (direct : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k)
      (eq_decomposition :
          sPolyMinor ord I J
            =
          Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct)
      (direct_bound :
          ∀ K ∈ direct.support,
            ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
              ord.toWithBotSyn (ord.withBotDegree (direct K))
                ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)))
    : SPolynomialStepResult ord I J
  | recur
      (nextI : MinorIndex m n t)
      (nextJ : MinorIndex m n t)
      (direct : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k)
      (multiplier : MvPolynomial (Fin m × Fin n) k)
      (complexity_lt : complexity nextI nextJ < complexity I J)
      (eq_decomposition :
          sPolyMinor ord I J
            =
          Finsupp.linearCombination _ (fun K ↦ genericMinor K) direct
            +
          multiplier * sPolyMinor ord nextI nextJ)
      (direct_bound :
          ∀ K ∈ direct.support,
            ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
              ord.toWithBotSyn (ord.withBotDegree (direct K))
                ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)))
      (multiplier_bound :
          ord.toWithBotSyn (ord.withBotDegree multiplier) +
            ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord nextI nextJ))
              ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)))
    : SPolynomialStepResult ord I J

omit [Nontrivial k] in
/-- Turn one step result into a minor certificate, using recursion only in the `recur` case. -/
theorem SPolynomialStepResult.to_minorCertificate
    (ord : MonomialOrder (Fin m × Fin n))
    {I J : MinorIndex m n t}
    (step : SPolynomialStepResult (k := k) ord I J)
    (hrec :
      ∀ I' J' : MinorIndex m n t,
        complexity I' J' < complexity I J →
          ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
            IsMinorCertificate (k := k) ord (sPolyMinor (k := k) ord I' J') a) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      IsMinorCertificate (k := k) ord (sPolyMinor (k := k) ord I J) a := by
  classical
  cases step with
  | done direct eq_decomposition direct_bound =>
      exact ⟨direct, eq_decomposition, direct_bound⟩
  | recur nextI nextJ direct multiplier complexity_lt
    eq_decomposition direct_bound multiplier_bound =>
      rcases hrec nextI nextJ complexity_lt with ⟨aRec, haRec_eq, haRec_deg⟩
      let a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
        direct + coeffMul (k := k) multiplier aRec
      refine ⟨a, ?_, ?_⟩
      · calc
          sPolyMinor (k := k) ord I J
              =
            Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
              +
            multiplier * sPolyMinor (k := k) ord nextI nextJ := by
                simpa using eq_decomposition
          _ =
            Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
              +
            multiplier *
              Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) aRec := by
                simp [haRec_eq]
          _ =
            Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
              +
            Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K)
              (coeffMul (k := k) multiplier aRec) := by
                rw [linearCombination_coeffMul]
          _ =
            Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K)
              (direct + coeffMul (k := k) multiplier aRec) := by
                rw [linearCombination_add]
          _ = Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) a := by
                rfl
      · intro K hK
        let b : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
          coeffMul (k := k) multiplier aRec
        have hb_bound :
            ∀ K ∈ b.support,
              ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                ord.toWithBotSyn (ord.withBotDegree (b K))
                  ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
          intro K hKb
          have hK_rec : K ∈ aRec.support := by
            exact coeffMul_support_subset (k := k) multiplier aRec hKb
          have hrecK :
              ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                ord.toWithBotSyn (ord.withBotDegree (aRec K))
                  ≤
                ord.toWithBotSyn
                  (ord.withBotDegree
                    (sPolyMinor (k := k) ord nextI nextJ)) := by
            exact haRec_deg K hK_rec
          have hmul :
            ord.toWithBotSyn (ord.withBotDegree (multiplier * aRec K))
              ≤
            ord.toWithBotSyn (ord.withBotDegree multiplier) +
              ord.toWithBotSyn (ord.withBotDegree (aRec K)) := by
            exact ord.withBotDegree_mul_le' multiplier (aRec K)
          have hmul' :
              ord.toWithBotSyn (ord.withBotDegree (multiplier * aRec K)) +
                  ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K))
                ≤
              (ord.toWithBotSyn (ord.withBotDegree multiplier) +
                  ord.toWithBotSyn (ord.withBotDegree (aRec K))) +
                ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) := by
            exact add_le_add_left hmul _
          calc
            ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                ord.toWithBotSyn (ord.withBotDegree (b K))
                =
            ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                ord.toWithBotSyn (ord.withBotDegree (multiplier * aRec K)) := by
                  simp [b, coeffMul_apply]
            _ ≤
            ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                (ord.toWithBotSyn (ord.withBotDegree multiplier) +
                  ord.toWithBotSyn (ord.withBotDegree (aRec K))) := by
                  simpa [add_assoc, add_left_comm, add_comm] using hmul'
            _ =
            (ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                ord.toWithBotSyn (ord.withBotDegree (aRec K))) +
              ord.toWithBotSyn (ord.withBotDegree multiplier) := by
                rw [add_assoc, add_comm
                      (ord.toWithBotSyn (ord.withBotDegree multiplier))
                      (ord.toWithBotSyn (ord.withBotDegree (aRec K))), ← add_assoc]
            _ ≤
            ord.toWithBotSyn
                (ord.withBotDegree
                  (sPolyMinor (k := k) ord nextI nextJ)) +
              ord.toWithBotSyn (ord.withBotDegree multiplier) :=
                add_le_add_left hrecK
                  (ord.toWithBotSyn (ord.withBotDegree multiplier))
            _ =
            ord.toWithBotSyn (ord.withBotDegree multiplier) +
              ord.toWithBotSyn
                (ord.withBotDegree
                  (sPolyMinor (k := k) ord nextI nextJ)) := by
                    exact add_comm _ _
            _ ≤
            ord.toWithBotSyn
              (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
                simpa [sPolyMinor] using multiplier_bound
        by_cases hK_direct : K ∈ direct.support
        · by_cases hK_b : K ∈ b.support
          · have hdirect := direct_bound K hK_direct
            have hb := hb_bound K hK_b
            have hsum :
                ord.toWithBotSyn (ord.withBotDegree (a K))
                  ≤
                ord.toWithBotSyn (ord.withBotDegree (direct K)) ⊔
                  ord.toWithBotSyn (ord.withBotDegree (b K)) := by
              simpa [a, b] using
                (ord.withBotDegree_add_le (f := direct K) (g := b K))
            calc
              ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                  ord.toWithBotSyn (ord.withBotDegree (a K))
                  ≤
              ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                  (ord.toWithBotSyn (ord.withBotDegree (direct K)) ⊔
                    ord.toWithBotSyn (ord.withBotDegree (b K))) := by
                      exact add_le_add_right hsum _
              _ =
              (ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                  ord.toWithBotSyn (ord.withBotDegree (direct K))) ⊔
                (ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
                  ord.toWithBotSyn (ord.withBotDegree (b K))) := by
                    rw [add_max]
              _ ≤
              ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
                exact sup_le hdirect hb
          · have hKb0 : b K = 0 := Finsupp.notMem_support_iff.mp hK_b
            have haK : a K = direct K := by
              simp [a, b, hKb0]
            simpa [haK] using direct_bound K hK_direct
        · have hKb : K ∈ b.support := by
            rw [Finsupp.mem_support_iff] at hK ⊢
            intro hzero
            apply hK
            have hdirect0 : direct K = 0 := Finsupp.notMem_support_iff.mp hK_direct
            simp [a, b, hdirect0, hzero]
          have hdirect0 : direct K = 0 := Finsupp.notMem_support_iff.mp hK_direct
          have haK : a K = b K := by
            simp [a, b, hdirect0]
          simpa [haK] using hb_bound K hKb

set_option linter.style.induction false in
theorem exists_sPolynomial_minor_certificate_by_complexity
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (hstep :
      ∀ I J : MinorIndex m n t,
        0 < complexity I J →
          SPolynomialStepResult (k := k) ord I J) :
    ∀ I J : MinorIndex m n t,
      ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
        IsMinorCertificate (k := k) ord (sPolyMinor (k := k) ord I J) a := by
  classical
  have hmain :
      ∀ c : ℕ,
        ∀ I J : MinorIndex m n t,
          complexity I J = c →
            ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
              IsMinorCertificate (k := k) ord (sPolyMinor (k := k) ord I J) a := by
    intro c
    induction' c using Nat.case_strong_induction_on with c ih
    · intro I J hIJ
      have hdisj : diagDisjoint I J := by
        exact (complexity_eq_zero_iff_diagDisjoint (I := I) (J := J)).mp hIJ
      exact exists_minorCertificate_of_diagDisjoint
        (k := k) (ord := ord) hdiag hdisj
    · intro I J hIJ
      have hpos : 0 < complexity I J := by
        rw [hIJ]
        exact Nat.succ_pos c
      let step : SPolynomialStepResult (k := k) ord I J := hstep I J hpos
      exact step.to_minorCertificate (k := k) (ord := ord) (I := I) (J := J)
        (hrec := by
          intro I' J' hlt
          have hlt' : complexity I' J' < c + 1 := by
            simpa [hIJ] using hlt
          have hle : complexity I' J' ≤ c := Nat.lt_succ_iff.mp hlt'
          exact ih (complexity I' J') hle I' J' rfl)
  intro I J
  exact hmain (complexity I J) I J rfl

/-- The explicit coefficient family used for the nontrivial overlapping case. -/
noncomputable def overlapDirectCoeffs
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J)
    (hIJ : I ≠ J) :
    MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k := by
  sorry

theorem overlapDirectCoeffs_eq_sPolynomial
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J)
    (hIJ : I ≠ J) :
    sPolyMinor (k := k) ord I J
      =
    Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K)
      (overlapDirectCoeffs (k := k) ord hdiag I J hpos hIJ) := by
  sorry

theorem overlapDirectCoeffs_degree_bound
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J)
    (hIJ : I ≠ J) :
    ∀ K ∈ (overlapDirectCoeffs (k := k) ord hdiag I J hpos hIJ).support,
      ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
        ord.toWithBotSyn
          (ord.withBotDegree
            ((overlapDirectCoeffs (k := k) ord hdiag I J hpos hIJ) K))
          ≤
        ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
  sorry

theorem exists_overlap_direct_certificate_of_ne
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J)
    (hIJ : I ≠ J) :
    ∃ direct : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      sPolyMinor (k := k) ord I J
        =
      Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
      ∧
      ∀ K ∈ direct.support,
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
          ord.toWithBotSyn (ord.withBotDegree (direct K))
            ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
  refine ⟨overlapDirectCoeffs (k := k) ord hdiag I J hpos hIJ, ?_, ?_⟩
  · exact overlapDirectCoeffs_eq_sPolynomial
      (k := k) (ord := ord) hdiag I J hpos hIJ
  · exact overlapDirectCoeffs_degree_bound
      (k := k) (ord := ord) hdiag I J hpos hIJ

noncomputable def sPolynomial_minor_stepResult_of_ne
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J)
    (hIJ : I ≠ J) :
    SPolynomialStepResult (k := k) ord I J := by
  classical
  let hcert :
      ∃ direct : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
        sPolyMinor (k := k) ord I J
          =
        Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
        ∧
        ∀ K ∈ direct.support,
          ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
            ord.toWithBotSyn (ord.withBotDegree (direct K))
              ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) :=
    exists_overlap_direct_certificate_of_ne
      (k := k) (ord := ord) hdiag I J hpos hIJ
  let direct : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k :=
    Classical.choose hcert
  have hspec :
      sPolyMinor (k := k) ord I J
        =
      Finsupp.linearCombination _ (fun K ↦ genericMinor (k := k) K) direct
      ∧
      ∀ K ∈ direct.support,
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
          ord.toWithBotSyn (ord.withBotDegree (direct K))
            ≤ ord.toWithBotSyn (ord.withBotDegree (sPolyMinor (k := k) ord I J)) := by
    exact Classical.choose_spec hcert
  rcases hspec with ⟨hEq, hBound⟩
  exact SPolynomialStepResult.done (k := k) (ord := ord) (I := I) (J := J) direct hEq hBound

/-- One-step result: split off the trivial case `I = J`,
and reduce the rest to the hard step above. -/
noncomputable def sPolynomial_minor_stepResult
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t)
    (hpos : 0 < complexity I J) :
    SPolynomialStepResult (k := k) ord I J := by
  classical
  by_cases hIJ : I = J
  · subst hIJ
    refine SPolynomialStepResult.done (k := k) (ord := ord) (I := I) (J := I) 0 ?_ ?_
    · simp [sPolyMinor]
    · intro K hK
      exfalso
      simp at hK
  · exact sPolynomial_minor_stepResult_of_ne
      (k := k) (ord := ord) hdiag I J hpos hIJ


end fifthPrep





section fifth

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]



theorem exists_sPolynomial_minor_certificate
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t) :
    ∃ a : MinorIndex m n t →₀ MvPolynomial (Fin m × Fin n) k,
      ord.sPolynomial (genericMinor I) (genericMinor (k := k) J) =
        Finsupp.linearCombination _ (fun K ↦ genericMinor K) a
      ∧
      ∀ K ∈ a.support,
        ord.toWithBotSyn (ord.withBotDegree (genericMinor (k := k) K)) +
          ord.toWithBotSyn (ord.withBotDegree (a K))
            ≤ ord.toWithBotSyn
                (ord.withBotDegree
                  (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))) := by
  simpa [sPolyMinor, IsMinorCertificate] using
    exists_sPolynomial_minor_certificate_by_complexity ord hdiag
      (sPolynomial_minor_stepResult ord hdiag)
      I J

theorem isRemainder_sPolynomial_minor_zero
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t) :
    ord.IsRemainder
      (ord.sPolynomial (genericMinor (k := k) I) (genericMinor J))
      (minorSet t) 0 := by
  rw [isRemainder_zero_minorSet_iff]
  exact exists_sPolynomial_minor_certificate  ord hdiag I J

end fifth



section

variable {m n t : ℕ}
variable {k : Type*} [CommRing k]




theorem minorSet_isGroebnerBasis_of_isDiagonalTermOrder
    {k : Type*} [CommRing k] [Nontrivial k]
    {m n : ℕ}
    (ord : MonomialOrder (Fin m × Fin n))
    (t : ℕ)
    (hdiag : IsDiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (minorSet (k := k) t)
      (detIdeal m n t k) := by
  rw [minorSet_isGroebnerBasis_iff_pairwise_sPolynomial_zero ord hdiag]
  intro I J
  exact isRemainder_sPolynomial_minor_zero ord hdiag I J



end


end Determinantal
