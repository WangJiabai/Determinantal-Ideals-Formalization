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




end fifthPrep

section paper_prop_1_0

variable {σ : Type*}
variable {R : Type*} [CommRing R]

/-- The exponent of `lcm (Head f) (Head g)`. -/
noncomputable def headLcm
    (ord : MonomialOrder σ)
    (f g : MvPolynomial σ R) : σ →₀ ℕ :=
  ord.degree f ⊔ ord.degree g

/-- A representation of `S(f,g)` as a linear combination of elements of `G`
whose summands are all strictly below `lcm (Head f) (Head g)`. -/
def AdjacentSmallSPolynomialRep
    (ord : MonomialOrder σ)
    (G : Set (MvPolynomial σ R))
    (f g : MvPolynomial σ R) : Prop :=
  ∃ a : G →₀ MvPolynomial σ R,
    ord.sPolynomial f g =
      Finsupp.linearCombination _ (fun h : G ↦ (h : MvPolynomial σ R)) a ∧
    ∀ h ∈ a.support,
      ∃ d : σ →₀ ℕ, ∃ c : R,
        c ≠ 0 ∧
        a h = MvPolynomial.monomial d c ∧
        (h : MvPolynomial σ R) ≠ 0 ∧
        ord.toSyn (ord.degree ((a h) * (h : MvPolynomial σ R))) <
          ord.toSyn (headLcm ord f g)

/-- A finite chain `f = F 0, ..., F p = f'` inside `G` satisfying the two
conditions in CGG Prop. (1.0.3). -/
def HasGoodChain
    (ord : MonomialOrder σ)
    (G : Set (MvPolynomial σ R))
    (f f' : MvPolynomial σ R) : Prop :=
  ∃ p : ℕ, ∃ F : Fin (p + 1) → MvPolynomial σ R,
    F 0 = f ∧
    F ⟨p, Nat.lt_succ_self p⟩ = f' ∧
    (∀ i, F i ∈ G) ∧
    (Finset.univ.sup (fun i : Fin (p + 1) ↦ ord.degree (F i)) = headLcm ord f f') ∧
    (∀ i : Fin p,
      AdjacentSmallSPolynomialRep ord G (F i.castSucc) (F i.succ))


lemma isGroebnerBasis_of_pairwise_hasGoodChain
    (ord : MonomialOrder σ)
    (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R))
    (hspan : Ideal.span G = I)
    (hmonic : ∀ g ∈ G, ord.leadingCoeff g = 1)
    (hchain : ∀ f ∈ G, ∀ f' ∈ G, HasGoodChain ord G f f') :
    ord.IsGroebnerBasis G I := by
  sorry

end paper_prop_1_0

section paper1_1

variable {m n t : ℕ}

/-
`MinorIndex m n t` is assumed to be:
structure MinorIndex (m n t : ℕ) where
  row : Fin t ↪o Fin m
  col : Fin t ↪o Fin n
-/

/-- Paper-style 1-based row sequence with sentinels:
`rowExt I 0 = 0`, `rowExt I j = I.row (j-1) + 1` for `1 ≤ j ≤ t`,
and `rowExt I j = m+1` for `j > t`. -/
def rowExt (I : MinorIndex m n t) (j : ℕ) : ℕ :=
  if h0 : j = 0 then
    0
  else if hj : j ≤ t then
    ((I.row ⟨j - 1, by omega⟩ : Fin m).1 + 1)
  else
    m + 1

/-- Paper-style 1-based column sequence with sentinels:
`colExt I 0 = 0`, `colExt I j = I.col (j-1) + 1` for `1 ≤ j ≤ t`,
and `colExt I j = n+1` for `j > t`. -/
def colExt (I : MinorIndex m n t) (j : ℕ) : ℕ :=
  if h0 : j = 0 then
    0
  else if hj : j ≤ t then
    ((I.col ⟨j - 1, by omega⟩ : Fin n).1 + 1)
  else
    n + 1

/-- `diffAt I J j` means that the `j`-th paper-position (`j = 1, ..., t`)
has different row/column data in `I` and `J`.

We use paper-style 1-based indexing on `ℕ`; for `j = 0` or `j > t`, this is `False`. -/
def diffAt (I J : MinorIndex m n t) (j : ℕ) : Prop :=
  match j with
  | 0 => False
  | k + 1 =>
      if hk : k < t then
        (I.row ⟨k, hk⟩, I.col ⟨k, hk⟩) ≠ (J.row ⟨k, hk⟩, J.col ⟨k, hk⟩)
      else
        False

/-- Paper's
`p := max { i : (α_i, β_i) ≠ (α'_i, β'_i) }`.

If there is no such index, `Nat.findGreatest` returns `0`. -/
noncomputable def pClose (I J : MinorIndex m n t) : ℕ := by
  classical
  exact Nat.findGreatest (diffAt I J) t



/-- Predicate for paper's
`s := max { j : j < p, α_j < α'_{j+1}, β_j < β'_{j+1} }`. -/
def sPred (I J : MinorIndex m n t) (j : ℕ) : Prop :=
  j < pClose I J ∧
    rowExt I j < rowExt J (j + 1) ∧
    colExt I j < colExt J (j + 1)

/-- Paper's `s`. Note that `j = 0` is allowed, thanks to the sentinel values. -/
noncomputable def sClose (I J : MinorIndex m n t) : ℕ := by
  classical
  exact Nat.findGreatest (sPred I J) (pClose I J)




/-- Predicate for paper's
`u := min { k : s < k, α'_k < α_{k+1}, β'_k < β_{k+1} }`.

This is the paper's third index, renamed to `uClose` to avoid conflict with
the ambient minor size parameter `t`. -/
def uPred (I J : MinorIndex m n t) (k : ℕ) : Prop :=
  sClose I J < k ∧
    rowExt J k < rowExt I (k + 1) ∧
    colExt J k < colExt I (k + 1)

/-- Paper's third index `t`, renamed here as `uClose`.

We define it as the least `k` satisfying `uPred`. In the intended applications
(one later proves `I ≠ J` / `Close I J` hypotheses), such a `k` exists. If Lean
cannot find one definitionally, we fall back to the ambient size `t`. -/
noncomputable def uClose (I J : MinorIndex m n t) : ℕ := by
  classical
  exact if h : ∃ k, uPred I J k then Nat.find h else t

/-- Raw row coordinates of the paper's `μ = μ((α,β),(α',β'))`.

This is the piecewise sequence
`(α₁,…,α_s, α'_{s+1},…,α'_u, α_{u+1},…,α_r)` in 0-based Lean indexing. -/
noncomputable def muRow (I J : MinorIndex m n t) (k : Fin t) : Fin m :=
  if k.1 + 1 ≤ sClose I J then
    I.row k
  else if k.1 + 1 ≤ uClose I J then
    J.row k
  else
    I.row k

/-- Raw column coordinates of the paper's `μ = μ((α,β),(α',β'))`.

This is the piecewise sequence
`(β₁,…,β_s, β'_{s+1},…,β'_u, β_{u+1},…,β_r)` in 0-based Lean indexing. -/
noncomputable def muCol (I J : MinorIndex m n t) (k : Fin t) : Fin n :=
  if k.1 + 1 ≤ sClose I J then
    I.col k
  else if k.1 + 1 ≤ uClose I J then
    J.col k
  else
    I.col k

def strictMonoToOrderEmbedding
    {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) : α ↪o β :=
  { toFun := f
    inj' := hf.injective
    map_rel_iff' := by
      intro a b
      constructor
      · intro hab
        by_contra hba
        have hlt : b < a := lt_of_not_ge hba
        have h' : f b < f a := hf hlt
        exact not_lt_of_ge hab h'
      · intro hab
        exact hf.monotone hab }


lemma exists_diffAt
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    ∃ j ≤ t, diffAt I J j := by
  have hdiff : ∃ k : Fin t, (I.row k, I.col k) ≠ (J.row k, J.col k) := by
    by_contra h
    push_neg at h
    apply hIJ
    cases I with
    | mk rowI colI =>
      cases J with
      | mk rowJ colJ =>
        simp only [Prod.mk.injEq, MinorIndex.mk.injEq] at h ⊢
        have hrow : rowI = rowJ := by
          ext k
          have h:=h k
          refine Fin.val_eq_of_eq ?_
          exact h.1
        have hcol : colI = colJ := by
          ext k
          have h:=h k
          refine Fin.val_eq_of_eq ?_
          exact h.2
        simp [hrow, hcol]
  rcases hdiff with ⟨k, hk⟩
  refine ⟨k.1 + 1, Nat.succ_le_of_lt k.2, ?_⟩
  simpa [diffAt, k.2] using hk

lemma pClose_spec
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    diffAt I J (pClose I J) := by
  classical
  rcases exists_diffAt I J hIJ with ⟨j, hjle, hj⟩
  unfold pClose
  exact Nat.findGreatest_spec hjle hj


lemma pClose_le
    (I J : MinorIndex m n t) :
    pClose I J ≤ t := by
    classical
    unfold pClose
    exact Nat.findGreatest_le t

lemma rowExt_zero_lt_one
    (I : MinorIndex m n t) :
    rowExt I 0 < rowExt I 1 := by
  unfold rowExt
  by_cases h1 : 1 ≤ t
  · simp [h1]
  · simp [h1]

lemma colExt_zero_lt_one
    (I : MinorIndex m n t) :
    colExt I 0 < colExt I 1 := by
  unfold colExt
  by_cases h1 : 1 ≤ t
  · simp [h1]
  · simp [h1]

lemma sPred_zero_of_ne
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    sPred I J 0 := by
  have hp : 0 < pClose I J := by
    have hspec : diffAt I J (pClose I J) := pClose_spec I J hIJ
    by_contra h0
    have hz : pClose I J = 0 := Nat.eq_zero_of_not_pos h0
    simp [hz, diffAt] at hspec
  refine ⟨hp, ?_, ?_⟩
  · simpa [rowExt] using (rowExt_zero_lt_one J)
  · simpa [colExt] using (colExt_zero_lt_one J)

lemma sClose_lt_pClose
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    sClose I J < pClose I J := by
  classical
  letI : DecidablePred (sPred I J) := fun a =>
    Classical.propDecidable (sPred I J a)
  have h0pred : sPred I J 0 := sPred_zero_of_ne I J hIJ
  have hspec : sPred I J (sClose I J) := by
    unfold sClose
    exact Nat.findGreatest_spec (show 0 ≤ pClose I J by omega) h0pred
  exact hspec.1

lemma sClose_lt_uClose
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    sClose I J < uClose I J := by
  classical
  letI : DecidablePred (uPred I J) := fun a =>
    Classical.propDecidable (uPred I J a)
  have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
  have hp : pClose I J ≤ t := pClose_le I J
  unfold uClose
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact lt_of_lt_of_le hs hp

lemma sClose_spec
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    sPred I J (sClose I J) := by
  classical
  letI : DecidablePred (sPred I J) := fun a =>
    Classical.propDecidable (sPred I J a)
  have h0 : sPred I J 0 := sPred_zero_of_ne I J hIJ
  unfold sClose
  exact Nat.findGreatest_spec (show 0 ≤ pClose I J by omega) h0

lemma uPred_pClose
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    uPred I J (pClose I J) := by
  classical
  let p := pClose I J
  have hs : sClose I J < p := by
    simpa [p] using sClose_lt_pClose I J hIJ
  have hp_le : p ≤ t := by
    simpa [p] using pClose_le I J
  have hp_diff : diffAt I J p := by
    simpa [p] using pClose_spec I J hIJ
  have hp_pos : 0 < p := by
    by_contra hp0
    have hpz : p = 0 := Nat.eq_zero_of_not_pos hp0
    have : diffAt I J 0 := by
      simpa [p, hpz] using hp_diff
    simp [diffAt] at this
  refine ⟨by simpa [p] using hs, ?_, ?_⟩
  · -- rowExt J p < rowExt I (p+1)
    by_cases hp1 : p + 1 ≤ t
    · have hp_lt_t : p < t := by
        omega
      let k0 : Fin t := ⟨p - 1, by omega⟩
      let k1 : Fin t := ⟨p, hp_lt_t⟩
      have hnodiff : ¬ diffAt I J (p + 1) := by
        intro hd
        have hle : p + 1 ≤ p := Nat.le_findGreatest hp1 hd
        omega
      have hpair_eq : (I.row k1, I.col k1) = (J.row k1, J.col k1) := by
        by_contra hneq
        exact hnodiff (by
          simpa [diffAt, p, hp1, hp_lt_t, k1] using hneq)
      have hrowJp : rowExt J p = (J.row k0).1 + 1 := by
        unfold rowExt
        simp [p, hp_pos.ne', hp_le, k0]
      have hrowIp1 : rowExt I (p + 1) = (I.row k1).1 + 1 := by
        unfold rowExt
        simp [p, hp1, k1]
      have hk01 : k0 < k1 := by
        simp only [Fin.mk_lt_mk, tsub_lt_self_iff, zero_lt_one, and_true, k0, k1]
        exact Nat.zero_lt_of_lt hs
      have hinc : (J.row k0).1 + 1 < (J.row k1).1 + 1 := by
        exact Nat.succ_lt_succ <| by
          simpa using (J.row.strictMono hk01)
      rw [hrowJp, hrowIp1]
      grind
    · let k0 : Fin t := ⟨p - 1, by omega⟩
      have hrowJp : rowExt J p = (J.row k0).1 + 1 := by
        unfold rowExt
        simp [p, hp_pos.ne', hp_le, k0]
      have hrowIp1 : rowExt I (p + 1) = m + 1 := by
        unfold rowExt
        simp [p, hp1]
      rw [hrowJp, hrowIp1]
      exact Nat.succ_lt_succ (J.row k0).2
  · -- colExt J p < colExt I (p+1)
    by_cases hp1 : p + 1 ≤ t
    · have hp_lt_t : p < t := by
        omega
      let k0 : Fin t := ⟨p - 1, by omega⟩
      let k1 : Fin t := ⟨p, hp_lt_t⟩
      have hnodiff : ¬ diffAt I J (p + 1) := by
        intro hd
        have hle : p + 1 ≤ p := Nat.le_findGreatest hp1 hd
        omega
      have hpair_eq : (I.row k1, I.col k1) = (J.row k1, J.col k1) := by
        by_contra hneq
        exact hnodiff (by
          simpa [diffAt, p, hp1, hp_lt_t, k1] using hneq)
      have hcolJp : colExt J p = (J.col k0).1 + 1 := by
        unfold colExt
        simp [p, hp_pos.ne', hp_le, k0]
      have hcolIp1 : colExt I (p + 1) = (I.col k1).1 + 1 := by
        unfold colExt
        simp [p, hp1, k1]
      have hk01 : k0 < k1 := by
        simp only [Fin.mk_lt_mk, tsub_lt_self_iff, zero_lt_one, and_true, k0, k1]
        exact Nat.zero_lt_of_lt hs
      have hinc : (J.col k0).1 + 1 < (J.col k1).1 + 1 := by
        exact Nat.succ_lt_succ <| by
          simpa using (J.col.strictMono hk01)
      rw [hcolJp, hcolIp1]
      grind
    · let k0 : Fin t := ⟨p - 1, by omega⟩
      have hcolJp : colExt J p = (J.col k0).1 + 1 := by
        unfold colExt
        simp [p, hp_pos.ne', hp_le, k0]
      have hcolIp1 : colExt I (p + 1) = n + 1 := by
        unfold colExt
        simp [p, hp1]
      rw [hcolJp, hcolIp1]
      exact Nat.succ_lt_succ (J.col k0).2

lemma uClose_spec
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    uPred I J (uClose I J) := by
  classical
  have hp : uPred I J (pClose I J) := uPred_pClose I J hIJ
  unfold uClose
  split_ifs with h
  · exact Nat.find_spec h
  · exfalso
    exact h ⟨pClose I J, hp⟩

lemma uClose_le_pClose
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    uClose I J ≤ pClose I J := by
  classical
  have hp : uPred I J (pClose I J) := uPred_pClose I J hIJ
  unfold uClose
  split_ifs with h
  · exact Nat.find_le hp
  · exfalso
    exact h ⟨pClose I J, hp⟩

lemma rowExt_monotone (I : MinorIndex m n t) : Monotone (rowExt I) := by
  intro i j hij
  unfold rowExt
  by_cases hi0 : i = 0
  · subst hi0
    split_ifs <;> grind
  · by_cases hj0 : j = 0
    · subst hj0
      simp_all only [nonpos_iff_eq_zero]
    · by_cases hjt : j ≤ t
      · have hit : i ≤ t := le_trans hij hjt
        simp only [hi0, ↓reduceDIte, hit, hj0, hjt, add_le_add_iff_right, Fin.val_fin_le,
          OrderEmbedding.le_iff_le, Fin.mk_le_mk, tsub_le_iff_right, ge_iff_le]
        have hk :
            (⟨i - 1, by omega⟩ : Fin t) ≤ ⟨j - 1, by omega⟩ := by
          simpa using (show i - 1 ≤ j - 1 by exact Nat.sub_le_sub_right hij 1)
        exact Nat.le_add_of_sub_le hk
      · by_cases hit : i ≤ t
        · simp [hi0, hj0, hit, hjt]
        · simp [hi0, hj0, hit, hjt]

lemma colExt_monotone (I : MinorIndex m n t) : Monotone (colExt I) := by
  intro i j hij
  unfold colExt
  by_cases hi0 : i = 0
  · subst hi0
    split_ifs <;> omega
  · by_cases hj0 : j = 0
    · omega
    · by_cases hjt : j ≤ t
      · have hit : i ≤ t := le_trans hij hjt
        simp only [hi0, ↓reduceDIte, hit, hj0, hjt, add_le_add_iff_right, Fin.val_fin_le,
          OrderEmbedding.le_iff_le, Fin.mk_le_mk, tsub_le_iff_right, ge_iff_le]
        have hk :
            (⟨i - 1, by omega⟩ : Fin t) ≤ ⟨j - 1, by omega⟩ := by
          simpa using (show i - 1 ≤ j - 1 by omega)
        exact Nat.le_add_of_sub_le hk
      · by_cases hit : i ≤ t
        · simp [hi0, hj0, hit, hjt]
        · simp [hi0, hj0, hit, hjt]

lemma muRow_strictMono_of_ne
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    StrictMono (muRow I J) := by
  intro a b hab
  have hsSpec : sPred I J (sClose I J) := sClose_spec I J hIJ
  have huSpec : uPred I J (uClose I J) := uClose_spec I J hIJ
  have hsu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
  have hmonoI : Monotone (rowExt I) := rowExt_monotone I
  have hmonoJ : Monotone (rowExt J) := rowExt_monotone J
  by_cases haS : a.1 + 1 ≤ sClose I J
  · by_cases hbU : b.1 + 1 ≤ uClose I J
    · by_cases hbS : b.1 + 1 ≤ sClose I J
      · -- both in the left block: both come from `I.row`
        simpa [muRow, haS, hbS] using I.row.strictMono hab
      · -- left block to middle block
        have hs1_le_b : sClose I J + 1 ≤ b.1 + 1 := by
          omega
        have hleft :
            rowExt I (a.1 + 1) ≤ rowExt I (sClose I J) := by
          exact hmonoI haS
        have hright :
            rowExt J (sClose I J + 1) ≤ rowExt J (b.1 + 1) := by
          exact hmonoJ hs1_le_b
        have hbound :
            rowExt I (sClose I J) < rowExt J (sClose I J + 1) := by
          exact hsSpec.2.1
        have hnat :
            rowExt I (a.1 + 1) < rowExt J (b.1 + 1) := by
          exact lt_of_le_of_lt hleft (lt_of_lt_of_le hbound hright)
        have hA :
            rowExt I (a.1 + 1) = (muRow I J a).1 + 1 := by
          simp [rowExt, muRow, haS]
        have hB :
            rowExt J (b.1 + 1) = (muRow I J b).1 + 1 := by
          simp [rowExt, muRow, hbS, hbU]
        rw [hA, hB] at hnat
        have hnat' : (muRow I J a).1 < (muRow I J b).1 := by
          exact Nat.lt_of_succ_lt_succ hnat
        simpa using hnat'
    · -- `b` is in the right block, so both endpoints come from `I.row`
      have hbS : ¬ b.1 + 1 ≤ sClose I J := by
        omega
      simpa [muRow, haS, hbS, hbU] using I.row.strictMono hab
  · by_cases haU : a.1 + 1 ≤ uClose I J
    · by_cases hbU : b.1 + 1 ≤ uClose I J
      · -- both in the middle block: both come from `J.row`
        have hbS : ¬ b.1 + 1 ≤ sClose I J := by
          omega
        simpa [muRow, haS, haU, hbS, hbU] using J.row.strictMono hab
      · -- middle block to right block
        have hu1_le_b : uClose I J + 1 ≤ b.1 + 1 := by
          omega
        have hleft :
            rowExt J (a.1 + 1) ≤ rowExt J (uClose I J) := by
          exact hmonoJ haU
        have hright :
            rowExt I (uClose I J + 1) ≤ rowExt I (b.1 + 1) := by
          exact hmonoI hu1_le_b
        have hbound :
            rowExt J (uClose I J) < rowExt I (uClose I J + 1) := by
          exact huSpec.2.1
        have hnat :
            rowExt J (a.1 + 1) < rowExt I (b.1 + 1) := by
          exact lt_of_le_of_lt hleft (lt_of_lt_of_le hbound hright)
        have hA :
            rowExt J (a.1 + 1) = (muRow I J a).1 + 1 := by
          simp [rowExt, muRow, haS, haU]
        have hbS : ¬ b.1 + 1 ≤ sClose I J := by
          omega
        have hB :
            rowExt I (b.1 + 1) = (muRow I J b).1 + 1 := by
          simp [rowExt, muRow, hbS, hbU]
        rw [hA, hB] at hnat
        have hnat' : (muRow I J a).1 < (muRow I J b).1 := by
          exact Nat.lt_of_succ_lt_succ hnat
        simpa using hnat'
    · -- `a` is already in the right block, hence so is `b`;
      -- both come from `I.row`
      have hbU : ¬ b.1 + 1 ≤ uClose I J := by
        omega
      have hbS : ¬ b.1 + 1 ≤ sClose I J := by
        omega
      simpa [muRow, haS, haU, hbS, hbU] using I.row.strictMono hab

lemma muCol_strictMono_of_ne
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    StrictMono (muCol I J) := by
  intro a b hab
  have hsSpec : sPred I J (sClose I J) := sClose_spec I J hIJ
  have huSpec : uPred I J (uClose I J) := uClose_spec I J hIJ
  have hsu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
  have hmonoI : Monotone (colExt I) := colExt_monotone I
  have hmonoJ : Monotone (colExt J) := colExt_monotone J
  by_cases haS : a.1 + 1 ≤ sClose I J
  · by_cases hbU : b.1 + 1 ≤ uClose I J
    · by_cases hbS : b.1 + 1 ≤ sClose I J
      · -- both in the left block
        simpa [muCol, haS, hbS] using I.col.strictMono hab
      · -- left block to middle block
        have hs1_le_b : sClose I J + 1 ≤ b.1 + 1 := by
          omega
        have hleft :
            colExt I (a.1 + 1) ≤ colExt I (sClose I J) := by
          exact hmonoI haS
        have hright :
            colExt J (sClose I J + 1) ≤ colExt J (b.1 + 1) := by
          exact hmonoJ hs1_le_b
        have hbound :
            colExt I (sClose I J) < colExt J (sClose I J + 1) := by
          exact hsSpec.2.2
        have hnat :
            colExt I (a.1 + 1) < colExt J (b.1 + 1) := by
          exact lt_of_le_of_lt hleft (lt_of_lt_of_le hbound hright)
        have hA :
            colExt I (a.1 + 1) = (muCol I J a).1 + 1 := by
          simp [colExt, muCol, haS]
        have hB :
            colExt J (b.1 + 1) = (muCol I J b).1 + 1 := by
          simp [colExt, muCol, hbS, hbU]
        rw [hA, hB] at hnat
        have hnat' : (muCol I J a).1 < (muCol I J b).1 := by
          exact Nat.lt_of_succ_lt_succ hnat
        simpa using hnat'
    · -- left block to right block: both endpoints come from I.col
      have hbS : ¬ b.1 + 1 ≤ sClose I J := by
        omega
      simpa [muCol, haS, hbS, hbU] using I.col.strictMono hab
  · by_cases haU : a.1 + 1 ≤ uClose I J
    · by_cases hbU : b.1 + 1 ≤ uClose I J
      · -- both in the middle block
        have hbS : ¬ b.1 + 1 ≤ sClose I J := by
          omega
        simpa [muCol, haS, haU, hbS, hbU] using J.col.strictMono hab
      · -- middle block to right block
        have hu1_le_b : uClose I J + 1 ≤ b.1 + 1 := by
          omega
        have hleft :
            colExt J (a.1 + 1) ≤ colExt J (uClose I J) := by
          exact hmonoJ haU
        have hright :
            colExt I (uClose I J + 1) ≤ colExt I (b.1 + 1) := by
          exact hmonoI hu1_le_b
        have hbound :
            colExt J (uClose I J) < colExt I (uClose I J + 1) := by
          exact huSpec.2.2
        have hnat :
            colExt J (a.1 + 1) < colExt I (b.1 + 1) := by
          exact lt_of_le_of_lt hleft (lt_of_lt_of_le hbound hright)
        have hA :
            colExt J (a.1 + 1) = (muCol I J a).1 + 1 := by
          simp [colExt, muCol, haS, haU]
        have hbS : ¬ b.1 + 1 ≤ sClose I J := by
          omega
        have hB :
            colExt I (b.1 + 1) = (muCol I J b).1 + 1 := by
          simp [colExt, muCol, hbS, hbU]
        rw [hA, hB] at hnat
        have hnat' : (muCol I J a).1 < (muCol I J b).1 := by
          exact Nat.lt_of_succ_lt_succ hnat
        simpa using hnat'
    · -- both in the right block
      have hbU : ¬ b.1 + 1 ≤ uClose I J := by
        omega
      have hbS : ¬ b.1 + 1 ≤ sClose I J := by
        omega
      simpa [muCol, haS, haU, hbS, hbU] using I.col.strictMono hab


/-
At this point, the "raw" paper definitions are done.

To package `muRow` and `muCol` into an actual `MinorIndex m n t`, you still need
the cross-boundary monotonicity lemmas coming from the paper's inequalities
(essentially the content around Lemma 1.4).

  hrow : StrictMono (muRow I J)
  hcol : StrictMono (muCol I J)

-/
noncomputable def mu
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    MinorIndex m n t :=
  { row := strictMonoToOrderEmbedding (muRow I J) (muRow_strictMono_of_ne I J hIJ)
    col := strictMonoToOrderEmbedding (muCol I J) (muCol_strictMono_of_ne I J hIJ) }

lemma eq_at_succ_of_mu_eq_left
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = I) :
    let k : Fin t := ⟨sClose I J, by
      have hp : pClose I J ≤ t := pClose_le I J
      have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
      omega⟩
    (J.row k = I.row k) ∧ (J.col k = I.col k) := by
  dsimp
  let k : Fin t := ⟨sClose I J, by
    have hp : pClose I J ≤ t := pClose_le I J
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    omega⟩
  have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
    simp [k]
  have hk_le_u : k.1 + 1 ≤ uClose I J := by
    simpa [k] using Nat.succ_le_of_lt (sClose_lt_uClose I J hIJ)
  have hrow_eq : (mu I J hIJ).row k = I.row k := by
    exact congrArg (fun M : MinorIndex m n t => M.row k) hmu
  have hcol_eq : (mu I J hIJ).col k = I.col k := by
    exact congrArg (fun M : MinorIndex m n t => M.col k) hmu
  constructor
  · simpa [mu, strictMonoToOrderEmbedding, muRow, hk_not_le_s, hk_le_u] using hrow_eq
  · simpa [mu, strictMonoToOrderEmbedding, muCol, hk_not_le_s, hk_le_u] using hcol_eq


lemma sPred_succ_of_mu_eq_left
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = I)
    (hsp : sClose I J + 1 < pClose I J) :
    sPred I J (sClose I J + 1) := by
  let k0 : Fin t := ⟨sClose I J, by
    have hp : pClose I J ≤ t := pClose_le I J
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact Nat.lt_of_lt_of_le hs hp⟩
  let k1 : Fin t := ⟨sClose I J + 1, by
    have hp : pClose I J ≤ t := pClose_le I J
    exact Nat.lt_of_lt_of_le hsp hp⟩
  have heq : (J.row k0 = I.row k0) ∧ (J.col k0 = I.col k0) := by
    simpa [k0] using (eq_at_succ_of_mu_eq_left I J hIJ hmu)
  have hk01 : k0 < k1 := by
    change sClose I J < sClose I J + 1
    exact lt_add_one (sClose I J)
  have hJrow : J.row k0 < J.row k1 := J.row.strictMono hk01
  have hJcol : J.col k0 < J.col k1 := J.col.strictMono hk01
  have hIrow : I.row k0 < J.row k1 := by
    simpa [heq.1] using hJrow
  have hIcol : I.col k0 < J.col k1 := by
    simpa [heq.2] using hJcol
  have hs1_le_t : sClose I J + 1 ≤ t := by
    have hp : pClose I J ≤ t := pClose_le I J
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact Nat.le_trans hs hp
  have hs2_le_t : sClose I J + 2 ≤ t := by
    have hp : pClose I J ≤ t := pClose_le I J
    exact Nat.le_trans hsp hp
  have hrowExtI :
      rowExt I (sClose I J + 1) = (I.row k0).1 + 1 := by
    unfold rowExt
    simp [k0, hs1_le_t]
  have hrowExtJ :
      rowExt J (sClose I J + 2) = (J.row k1).1 + 1 := by
    unfold rowExt
    simp [k1, hs2_le_t]
  have hcolExtI :
      colExt I (sClose I J + 1) = (I.col k0).1 + 1 := by
    unfold colExt
    simp [k0, hs1_le_t]
  have hcolExtJ :
      colExt J (sClose I J + 2) = (J.col k1).1 + 1 := by
    unfold colExt
    simp [k1, hs2_le_t]
  refine ⟨hsp, ?_, ?_⟩
  · have hnat : (I.row k0).1 + 1 < (J.row k1).1 + 1 := by
      exact Nat.succ_lt_succ (by simpa using hIrow)
    simpa [hrowExtI, hrowExtJ] using hnat
  · have hnat : (I.col k0).1 + 1 < (J.col k1).1 + 1 := by
      exact Nat.succ_lt_succ (by simpa using hIcol)
    simpa [hcolExtI, hcolExtJ] using hnat

lemma succ_sClose_eq_pClose_of_mu_eq_left
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = I) :
    sClose I J + 1 = pClose I J := by
  have hle : sClose I J + 1 ≤ pClose I J := by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact Order.add_one_le_iff.mpr hs
  have hnotlt : ¬ sClose I J + 1 < pClose I J := by
    intro hsp
    have hsPred : sPred I J (sClose I J + 1) :=
      sPred_succ_of_mu_eq_left I J hIJ hmu hsp
    classical
    letI : DecidablePred (sPred I J) := fun a =>
      Classical.propDecidable (sPred I J a)
    have hsle : sClose I J + 1 ≤ sClose I J := by
      unfold sClose
      exact Nat.le_findGreatest (show sClose I J + 1 ≤ pClose I J by omega) hsPred
    simp at hsle
  simp only [not_lt] at hnotlt
  exact Eq.symm (Nat.le_antisymm hnotlt hle)

/-Lemma 1.2-/
lemma mu_ne_left
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    mu I J hIJ ≠ I := by
  intro hmu
  have hsltp : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
  have hple : pClose I J ≤ t := pClose_le I J
  let k : Fin t := ⟨sClose I J, by omega⟩
  have heq :
      (J.row k = I.row k) ∧ (J.col k = I.col k) := by
    simpa [k] using
      (eq_at_succ_of_mu_eq_left I J hIJ hmu)
  have hsp : sClose I J + 1 = pClose I J :=
    succ_sClose_eq_pClose_of_mu_eq_left I J hIJ hmu
  have hp : diffAt I J (pClose I J) :=
    pClose_spec I J hIJ
  have hp' : diffAt I J (sClose I J + 1) := by
    simpa [hsp] using hp
  have hklt : sClose I J < t := by
    omega
  have hneq :
      (I.row k, I.col k) ≠ (J.row k, J.col k) := by
    simpa [diffAt, hklt, k] using hp'
  have hpair :
      (I.row k, I.col k) = (J.row k, J.col k) := by
    exact Prod.ext heq.1.symm heq.2.symm
  exact hneq hpair

lemma mu_congr_proof
    (I J : MinorIndex m n t)
    {h₁ h₂ : I ≠ J} :
    mu I J h₁ = mu I J h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst this
  rfl

lemma mu_ne_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    mu J I hIJ.symm ≠ J := by
  exact mu_ne_left J I hIJ.symm

end paper1_1

section paper1_3
variable {m n t : ℕ}

def Close (I J : MinorIndex m n t) : Prop :=
  ∃ hIJ : I ≠ J, mu I J hIJ = J ∧ mu J I hIJ.symm = I

lemma Close.ne
    {I J : MinorIndex m n t}
    (h : Close I J) :
    I ≠ J := h.choose

lemma Close.symm {I J : MinorIndex m n t} (h : Close I J) : Close J I := by
  rcases h with ⟨hIJ, hμIJ, hμJI⟩
  exact ⟨hIJ.symm, hμJI, hμIJ⟩

lemma Close.mu_eq_right
    {I J : MinorIndex m n t}
    (h : Close I J) :
    mu I J h.choose = J := h.choose_spec.1

lemma Close.mu_eq_left
    {I J : MinorIndex m n t}
    (h : Close I J) :
    mu J I h.choose.symm = I := h.choose_spec.2

end paper1_3

section paper1_4

variable {m n t : ℕ}

/-- Paper-style pair at 1-based position `j`. -/
def pairExt (I : MinorIndex m n t) (j : ℕ) : ℕ × ℕ :=
  (rowExt I j, colExt I j)

lemma diffAt_symm
    (I J : MinorIndex m n t) (j : ℕ) :
    diffAt I J j ↔ diffAt J I j := by
  cases j with
  | zero =>
      simp [diffAt]
  | succ k =>
      by_cases hk : k < t
      · simp [diffAt, hk, ne_comm];grind
      · simp [diffAt, hk]

lemma pClose_eq_symm
    (I J : MinorIndex m n t) :
    pClose I J = pClose J I := by
  classical
  by_cases hIJ : I = J
  · subst hIJ
    rfl
  · have hle₁ : pClose I J ≤ pClose J I := by
      have hp : diffAt I J (pClose I J) := pClose_spec I J hIJ
      have hp' : diffAt J I (pClose I J) := (diffAt_symm I J _).mp hp
      exact Nat.le_findGreatest (pClose_le I J) hp'
    have hle₂ : pClose J I ≤ pClose I J := by
      have hp : diffAt J I (pClose J I) := by exact pClose_spec J I fun a ↦ hIJ (id (Eq.symm a))
      have hp' : diffAt I J (pClose J I) := (diffAt_symm J I _).mp hp
      exact Nat.le_findGreatest (pClose_le J I) hp'
    exact le_antisymm hle₁ hle₂

/-! ### Step-strictness of the extended sequences -/

lemma rowExt_step_lt
    (I : MinorIndex m n t)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hjt : j < t) :
    rowExt I j < rowExt I (j + 1) := by
  let k0 : Fin t := ⟨j - 1, by omega⟩
  let k1 : Fin t := ⟨j, hjt⟩
  have hk01 : k0 < k1 := by
    simp [k0, k1]
    omega
  have hfin : I.row k0 < I.row k1 := I.row.strictMono hk01
  have hj_le_t : j ≤ t := by omega
  have hj1_le_t : j + 1 ≤ t := by omega
  have hrowj : rowExt I j = (I.row k0).1 + 1 := by
    unfold rowExt
    grind
  have hrowj1 : rowExt I (j + 1) = (I.row k1).1 + 1 := by
    unfold rowExt
    simp [hj1_le_t, k1]
  have hnat : (I.row k0).1 + 1 < (I.row k1).1 + 1 := by
    exact Nat.succ_lt_succ <| by
      simpa using hfin
  simpa [hrowj, hrowj1] using hnat

lemma colExt_step_lt
    (I : MinorIndex m n t)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hjt : j < t) :
    colExt I j < colExt I (j + 1) := by
  let k0 : Fin t := ⟨j - 1, by omega⟩
  let k1 : Fin t := ⟨j, hjt⟩
  have hk01 : k0 < k1 := by
    simp [k0, k1]
    omega
  have hfin : I.col k0 < I.col k1 := I.col.strictMono hk01
  have hj_le_t : j ≤ t := by omega
  have hj1_le_t : j + 1 ≤ t := by omega
  have hcolj : colExt I j = (I.col k0).1 + 1 := by
    unfold colExt
    grind
  have hcolj1 : colExt I (j + 1) = (I.col k1).1 + 1 := by
    unfold colExt
    simp [hj1_le_t, k1]
  have hnat : (I.col k0).1 + 1 < (I.col k1).1 + 1 := by
    exact Nat.succ_lt_succ <| by
      simpa using hfin
  simpa [hcolj, hcolj1] using hnat

/-! ### `diffAt` and `pairExt` on the genuine range `1..t` -/

lemma diffAt_iff_pairExt_ne
    (I J : MinorIndex m n t)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hj2 : j ≤ t) :
    diffAt I J j ↔ pairExt I j ≠ pairExt J j := by
  cases j with
  | zero =>
      omega
  | succ k =>
      have hk : k < t := by omega
      simp [diffAt, pairExt, rowExt, colExt, hk, hj2]
      grind

/-! ### Equality of pairs before `s` and after `u` under `mu I J = J` -/

lemma pairExt_eq_of_mu_eq_right_le_s
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hj2 : j ≤ sClose I J) :
    pairExt I j = pairExt J j := by
  let k : Fin t := ⟨j - 1, by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    have hp : pClose I J ≤ t := pClose_le I J
    omega⟩
  have hrow_eq : (mu I J hIJ).row k = J.row k := by
    exact congrArg (fun M : MinorIndex m n t => M.row k) hmu
  have hcol_eq : (mu I J hIJ).col k = J.col k := by
    exact congrArg (fun M : MinorIndex m n t => M.col k) hmu
  have hk_le_s : k.1 + 1 ≤ sClose I J := by
    simp [k]
    omega
  have hrow0 : I.row k = J.row k := by
    simpa [mu, strictMonoToOrderEmbedding, muRow, hk_le_s] using hrow_eq
  have hcol0 : I.col k = J.col k := by
    simpa [mu, strictMonoToOrderEmbedding, muCol, hk_le_s] using hcol_eq
  have hj_le_t : j ≤ t := by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact le_trans hj2 <| le_trans (Nat.le_of_lt hs) (pClose_le I J)
  have hrowExtI : rowExt I j = (I.row k).1 + 1 := by
    unfold rowExt
    grind
  have hrowExtJ : rowExt J j = (J.row k).1 + 1 := by
    unfold rowExt
    grind
  have hcolExtI : colExt I j = (I.col k).1 + 1 := by
    unfold colExt
    grind
  have hcolExtJ : colExt J j = (J.col k).1 + 1 := by
    unfold colExt
    grind
  apply Prod.ext
  · simp only [pairExt]; rw [hrowExtI, hrowExtJ, hrow0]
  · simp only [pairExt]; rw [hcolExtI, hcolExtJ, hcol0]

lemma pairExt_eq_of_mu_eq_right_gt_u
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J)
    {j : ℕ}
    (hj1 : uClose I J < j)
    (hj2 : j ≤ t) :
    pairExt I j = pairExt J j := by
  have hjpos : 0 < j := by omega
  let k : Fin t := ⟨j - 1, by omega⟩
  have hrow_eq : (mu I J hIJ).row k = J.row k := by
    exact congrArg (fun M : MinorIndex m n t => M.row k) hmu
  have hcol_eq : (mu I J hIJ).col k = J.col k := by
    exact congrArg (fun M : MinorIndex m n t => M.col k) hmu
  have hk_succ : k.1 + 1 = j := by
    simp only [k]
    exact Nat.sub_add_cancel hjpos
  have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
    rw [hk_succ]
    have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
    omega
  have hk_not_le_u : ¬ k.1 + 1 ≤ uClose I J := by
    simp [k]
    omega
  have hrow0 : I.row k = J.row k := by
    simpa [mu, strictMonoToOrderEmbedding, muRow, hk_not_le_s, hk_not_le_u] using hrow_eq
  have hcol0 : I.col k = J.col k := by
    simpa [mu, strictMonoToOrderEmbedding, muCol, hk_not_le_s, hk_not_le_u] using hcol_eq
  have hrowExtI : rowExt I j = (I.row k).1 + 1 := by
    unfold rowExt
    simp [hjpos.ne', hj2, k]
  have hrowExtJ : rowExt J j = (J.row k).1 + 1 := by
    unfold rowExt
    simp [hjpos.ne', hj2, k]
  have hcolExtI : colExt I j = (I.col k).1 + 1 := by
    unfold colExt
    simp [hjpos.ne', hj2, k]
  have hcolExtJ : colExt J j = (J.col k).1 + 1 := by
    unfold colExt
    simp [hjpos.ne', hj2, k]
  apply Prod.ext
  · simp only [pairExt]; rw [hrowExtI, hrowExtJ, hrow0]
  · simp only [pairExt]; rw [hcolExtI, hcolExtJ, hcol0]

/-! ### `sClose + 1` is the first differing position under `mu I J = J` -/

lemma not_diffAt_lt_succ_sClose_of_mu_eq_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hjlt : j < sClose I J + 1) :
    ¬ diffAt I J j := by
  have hj2 : j ≤ sClose I J := by omega
  have hEq : pairExt I j = pairExt J j :=
    pairExt_eq_of_mu_eq_right_le_s I J hIJ hmu hj1 hj2
  have hj_le_t : j ≤ t := by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact le_trans hj2 <| le_trans (Nat.le_of_lt hs) (pClose_le I J)
  intro hdiff
  exact ((diffAt_iff_pairExt_ne I J hj1 hj_le_t).mp hdiff) hEq

lemma diffAt_succ_sClose_of_mu_eq_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    diffAt I J (sClose I J + 1) := by
  let q := sClose I J + 1
  have hq_le_p : q ≤ pClose I J := by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    omega
  by_cases hqp : q = pClose I J
  · simpa [q, hqp] using pClose_spec I J hIJ
  · have hqp_lt : q < pClose I J := by
      omega
    by_contra hnd
    have hq_le_t : q ≤ t := by
      exact le_trans hq_le_p (pClose_le I J)
    have hEq : pairExt I q = pairExt J q := by
      apply Classical.byContradiction
      intro hneq
      exact hnd ((diffAt_iff_pairExt_ne I J (by omega) hq_le_t).2 hneq)
    have hrow : rowExt I q < rowExt J (q + 1) := by
      have hEqRow : rowExt I q = rowExt J q := congrArg Prod.fst hEq
      have hstep : rowExt J q < rowExt J (q + 1) := by
        exact rowExt_step_lt J (by omega) (by
          exact lt_of_lt_of_le hqp_lt (pClose_le I J))
      exact hEqRow ▸ hstep
    have hcol : colExt I q < colExt J (q + 1) := by
      have hEqCol : colExt I q = colExt J q := congrArg Prod.snd hEq
      have hstep : colExt J q < colExt J (q + 1) := by
        exact colExt_step_lt J (by omega) (by
          exact lt_of_lt_of_le hqp_lt (pClose_le I J))
      exact hEqCol ▸ hstep
    have hsPred : sPred I J q := ⟨hqp_lt, hrow, hcol⟩
    classical
    letI : DecidablePred (sPred I J) := fun a =>
      Classical.propDecidable (sPred I J a)
    have hle : q ≤ sClose I J := by
      unfold sClose
      exact Nat.le_findGreatest (show q ≤ pClose I J by exact hq_le_p) hsPred
    omega

lemma firstDiff_succ_sClose_of_mu_eq_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J) :
    diffAt I J (sClose I J + 1) ∧
      ∀ j : ℕ, 1 ≤ j → j < sClose I J + 1 → ¬ diffAt I J j := by
  constructor
  · exact diffAt_succ_sClose_of_mu_eq_right I J hIJ
  · intro j hj1 hjlt
    exact not_diffAt_lt_succ_sClose_of_mu_eq_right I J hIJ hmu hj1 hjlt

/-! ### Tail-agreement after `uClose` and a minimality principle for `uClose` -/

lemma tailAgree_after_u_of_mu_eq_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J) :
    ∀ j : ℕ, uClose I J < j → j ≤ t → pairExt I j = pairExt J j := by
  intro j hj1 hj2
  exact pairExt_eq_of_mu_eq_right_gt_u I J hIJ hmu hj1 hj2

lemma uPred_of_tailAgree
    (I J : MinorIndex m n t)
    (q : ℕ)
    (hsq : sClose I J < q)
    (hqle : q ≤ t)
    (htail : ∀ j : ℕ, q < j → j ≤ t → pairExt I j = pairExt J j) :
    uPred I J q := by
  refine ⟨hsq, ?_, ?_⟩
  · by_cases hqt : q < t
    · have hEq : pairExt I (q + 1) = pairExt J (q + 1) := htail (q + 1) (by omega) (by omega)
      have hEqRow : rowExt I (q + 1) = rowExt J (q + 1) := congrArg Prod.fst hEq
      have hstep : rowExt J q < rowExt J (q + 1) := rowExt_step_lt J (by omega) hqt
      exact Nat.lt_of_lt_of_eq hstep (id (Eq.symm hEqRow))
    · have hqeq : q = t := by omega
      subst hqeq
      unfold rowExt
      by_cases ht0 : q = 0
      · grind
      · have htle : q ≤ q := le_rfl
        have htnz : q ≠ 0 := ht0
        simp [htnz]
  · by_cases hqt : q < t
    · have hEq : pairExt I (q + 1) = pairExt J (q + 1) := htail (q + 1) (by omega) (by omega)
      have hEqCol : colExt I (q + 1) = colExt J (q + 1) := congrArg Prod.snd hEq
      have hstep : colExt J q < colExt J (q + 1) := colExt_step_lt J (by omega) hqt
      grind
    · have hqeq : q = t := by omega
      subst hqeq
      unfold colExt
      by_cases ht0 : q = 0
      · grind
      · have htle : q ≤ q := le_rfl
        have htnz : q ≠ 0 := ht0
        simp [htnz]

lemma uClose_le_of_tailAgree
    (I J : MinorIndex m n t)
    (q : ℕ)
    (hsq : sClose I J < q)
    (hqle : q ≤ t)
    (htail : ∀ j : ℕ, q < j → j ≤ t → pairExt I j = pairExt J j) :
    uClose I J ≤ q := by
  classical
  have huq : uPred I J q := uPred_of_tailAgree I J q hsq hqle htail
  unfold uClose
  split_ifs with h
  · exact Nat.find_le huq
  · exfalso
    exact h ⟨q, huq⟩


/-! ### Lemma 1.4(i)

The integers `s` and `t` attached to `(I,J)` coincide with the corresponding
integers for `(J,I)`. In our notation the paper's second index `t` is `uClose`.
-/

/-- Lemma 1.4(i), first half: `s = s'`. -/
lemma close_sClose_eq_symm
    (I J : MinorIndex m n t)
    (hC : Close I J) :
    sClose I J = sClose J I := by
  have hIJ : I ≠ J := hC.ne
  have hμIJ : mu I J hIJ = J := by
    simpa using hC.mu_eq_right
  have hμJI : mu J I hIJ.symm = I := by
    simpa using hC.mu_eq_left
  have hfirstIJ :=
    firstDiff_succ_sClose_of_mu_eq_right I J hIJ hμIJ
  have hfirstJI :=
    firstDiff_succ_sClose_of_mu_eq_right J I hIJ.symm hμJI
  have hdiffIJ : diffAt I J (sClose I J + 1) := hfirstIJ.1
  have hdiffJI : diffAt I J (sClose J I + 1) := by
    exact (diffAt_symm J I _).mp hfirstJI.1
  have hle₁ : sClose I J + 1 ≤ sClose J I + 1 := by
    by_contra hlt
    have hlt' : sClose J I + 1 < sClose I J + 1 := lt_of_not_ge hlt
    have hnd : ¬ diffAt I J (sClose J I + 1) :=
      hfirstIJ.2 (sClose J I + 1) (by omega) hlt'
    exact hnd hdiffJI
  have hle₂ : sClose J I + 1 ≤ sClose I J + 1 := by
    by_contra hlt
    have hlt' : sClose I J + 1 < sClose J I + 1 := lt_of_not_ge hlt
    have hnd : ¬ diffAt J I (sClose I J + 1) :=
      hfirstJI.2 (sClose I J + 1) (by omega) hlt'
    exact hnd ((diffAt_symm I J _).mp hdiffIJ)
  omega

/-- Lemma 1.4(i), second half: `t = t'`.
Here the paper's second index `t` is our `uClose`. -/
lemma close_uClose_eq_symm
    (I J : MinorIndex m n t)
    (hC : Close I J) :
    uClose I J = uClose J I := by
  have hIJ : I ≠ J := hC.ne
  have hμIJ : mu I J hIJ = J := by
    simpa using hC.mu_eq_right
  have hμJI : mu J I hIJ.symm = I := by
    simpa using hC.mu_eq_left
  have hsEq : sClose I J = sClose J I :=
    close_sClose_eq_symm I J hC
  have hle₁ : uClose I J ≤ uClose J I := by
    apply uClose_le_of_tailAgree (I := I) (J := J) (q := uClose J I)
    · -- `sClose I J < uClose J I`
      rw [hsEq]
      exact sClose_lt_uClose J I hIJ.symm
    · -- `uClose J I ≤ t`
      exact le_trans (uClose_le_pClose J I hIJ.symm) (pClose_le J I)
    · -- agreement after `uClose J I`
      intro j hj₁ hj₂
      have htail :
          pairExt J j = pairExt I j :=
        tailAgree_after_u_of_mu_eq_right J I hIJ.symm hμJI j hj₁ hj₂
      simpa [eq_comm] using htail
  have hle₂ : uClose J I ≤ uClose I J := by
    apply uClose_le_of_tailAgree (I := J) (J := I) (q := uClose I J)
    · -- `sClose J I < uClose I J`
      rw [← hsEq]
      exact sClose_lt_uClose I J hIJ
    · -- `uClose I J ≤ t`
      exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
    · -- agreement after `uClose I J`
      intro j hj₁ hj₂
      exact Eq.symm (tailAgree_after_u_of_mu_eq_right I J hIJ hμIJ j hj₁ hj₂)
  exact le_antisymm hle₁ hle₂

/-! ### Lemma 1.4(ii)

For every `s+1 ≤ i,j ≤ t`, the pair at position `i` in `I` is different
from the pair at position `j` in `J`.
-/

lemma mid_le_t_of_close
    (I J : MinorIndex m n t)
    (hC : Close I J)
    {j : ℕ}
    (hj : j ≤ uClose I J) :
    j ≤ t := by
  exact le_trans hj (le_trans (uClose_le_pClose I J hC.ne) (pClose_le I J))

lemma pairExt_mu_eq_right_of_mid
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {j : ℕ}
    (hj1 : sClose I J + 1 ≤ j)
    (hj2 : j ≤ uClose I J) :
    pairExt (mu I J hIJ) j = pairExt J j := by
  have hjt : j ≤ t := by
    exact le_trans hj2 (le_trans (uClose_le_pClose I J hIJ) (pClose_le I J))
  have hj0 : j ≠ 0 := by
    omega
  have hns : ¬ j ≤ sClose I J := by
    omega
  apply Prod.ext
  · unfold pairExt rowExt
    simp [mu, strictMonoToOrderEmbedding, muRow, hj0, hjt]
    grind
  · unfold pairExt colExt
    simp [mu, strictMonoToOrderEmbedding, muCol, hj0, hjt]
    grind

lemma pairExt_mu_eq_left_of_mid
    (I J : MinorIndex m n t)
    (hC : Close I J)
    {i : ℕ}
    (hi1 : sClose I J + 1 ≤ i)
    (hi2 : i ≤ uClose I J) :
    pairExt (mu J I hC.ne.symm) i = pairExt I i := by
  have hsEq : sClose I J = sClose J I := close_sClose_eq_symm I J hC
  have huEq : uClose I J = uClose J I := close_uClose_eq_symm I J hC
  have hi1' : sClose J I + 1 ≤ i := by
    rwa [← hsEq]
  have hi2' : i ≤ uClose J I := by
    rwa [← huEq]
  simpa using
    (pairExt_mu_eq_right_of_mid (I := J) (J := I) (hIJ := hC.ne.symm) hi1' hi2')

/-- Lemma 1.4(iv), first inequality chain on the row side. -/
lemma close_row_chain_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (sClose I J + 1)) :
    ∀ i : ℕ, sClose I J + 1 ≤ i → i ≤ uClose I J →
      rowExt J (uClose I J) < rowExt I i := by
  intro i hi₁ hi₂
  have hmono : Monotone (rowExt I) := rowExt_monotone I
  have hle : rowExt I (sClose I J + 1) ≤ rowExt I i := by
    exact hmono hi₁
  exact lt_of_lt_of_le hrowLt hle


lemma close_chain_row_le_to_prev_col_le
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hrow :
      rowExt J (uClose I J) ≤ rowExt I i) :
    colExt I i ≤ colExt J (i - 1) := by
  classical
  by_contra hnot
  have hi_pos : 0 < i := by
    omega
  have hu_le_t : uClose I J ≤ t := by
    exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have hk_pos : 1 ≤ i - 1 := by
    omega
  have hk_lt_t : i - 1 < t := by
    omega
  have hstep_row : rowExt J (i - 1) < rowExt J i := by
    have : rowExt J (i - 1) < rowExt J ((i - 1) + 1) := by
      exact rowExt_step_lt J hk_pos hk_lt_t
    simpa [Nat.sub_add_cancel hi_pos] using this
  have hrow_i_le_u : rowExt J i ≤ rowExt J (uClose I J) := by
    exact rowExt_monotone J hi₂
  have hrow_prev_lt_u : rowExt J (i - 1) < rowExt J (uClose I J) := by
    exact lt_of_lt_of_le hstep_row hrow_i_le_u
  have hrow_prev_lt_i : rowExt J (i - 1) < rowExt I i := by
    exact lt_of_lt_of_le hrow_prev_lt_u hrow
  have hcol_prev_lt_i : colExt J (i - 1) < colExt I i := by
    exact lt_of_not_ge hnot
  have hk_uPred : uPred I J (i - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · simpa [Nat.sub_add_cancel hi_pos] using hrow_prev_lt_i
    · simpa [Nat.sub_add_cancel hi_pos] using hcol_prev_lt_i
  have hex : ∃ k, uPred I J k := ⟨pClose I J, uPred_pClose I J hIJ⟩
  have hu_le_prev : uClose I J ≤ i - 1 := by
    unfold uClose
    split_ifs
    · exact Nat.find_le hk_uPred
  have : i ≤ i - 1 := by
    exact le_trans hi₂ hu_le_prev
  omega

lemma close_chain_prev_col_le_to_col_lt
    (I J : MinorIndex m n t)
    {i : ℕ}
    (hIJ : I ≠ J)
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hcol :
      colExt I i ≤ colExt J (i - 1)) :
    colExt I i < colExt J i := by
    have hit : i ≤ t := by
      exact le_trans hi₂ <| le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
    have hi_pos : 0 < i := by
      omega
    have hi1_pos : 1 ≤ i - 1 := by
      omega
    have hi1_lt_t : i - 1 < t := by
      omega
    have hstep : colExt J (i - 1) < colExt J i := by
      have : colExt J (i - 1) < colExt J ((i - 1) + 1) := by
        exact colExt_step_lt J hi1_pos hi1_lt_t
      simpa [Nat.sub_add_cancel hi_pos] using this
    exact lt_of_le_of_lt hcol hstep


lemma close_chain_col_lt_to_prev_row_le
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hcol :
      colExt I i < colExt J i) :
    rowExt J i ≤ rowExt I (i - 1) := by
  by_contra hnot
  have hrow : rowExt I (i - 1) < rowExt J i := by
    exact lt_of_not_ge hnot
  have hi_pos : 0 < i := by
    omega
  have hi_le_t : i ≤ t := by
    exact le_trans hi₂ <| le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have him1_pos : 1 ≤ i - 1 := by
    omega
  have him1_lt_t : i - 1 < t := by
    omega
  have hstep_col : colExt I (i - 1) < colExt I i := by
    have : colExt I (i - 1) < colExt I ((i - 1) + 1) := by
      exact colExt_step_lt I him1_pos him1_lt_t
    simpa [Nat.sub_add_cancel hi_pos] using this
  have hcol_prev : colExt I (i - 1) < colExt J i := by
    exact lt_of_lt_of_le hstep_col (Nat.le_of_lt hcol)
  have hsPred : sPred I J (i - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · have hu_le_p : uClose I J ≤ pClose I J := uClose_le_pClose I J hIJ
      omega
    · simpa [Nat.sub_add_cancel hi_pos] using hrow
    · simpa [Nat.sub_add_cancel hi_pos] using hcol_prev
  classical
  letI : DecidablePred (sPred I J) := fun a =>
    Classical.propDecidable (sPred I J a)
  have him1_le_s : i - 1 ≤ sClose I J := by
    unfold sClose
    have him1_le_p : i - 1 ≤ pClose I J := by
      have hu_le_p : uClose I J ≤ pClose I J := uClose_le_pClose I J hIJ
      omega
    exact Nat.le_findGreatest him1_le_p hsPred
  omega

lemma close_chain_prev_row_le_to_prev_row_lt
    (I J : MinorIndex m n t)
    {i : ℕ}
    (hIJ : I ≠ J)
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hrow :
      rowExt J i ≤ rowExt I (i - 1)) :
    rowExt J (i - 1) < rowExt I (i - 1) := by
    have hit : i ≤ t := by
      exact le_trans hi₂ <| le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
    have hi_pos : 0 < i := by
      omega
    have hi1_pos : 1 ≤ i - 1 := by
      omega
    have hi1_lt_t : i - 1 < t := by
      omega
    have hstep : rowExt J (i - 1) < rowExt J i := by
      have : rowExt J (i - 1) < rowExt J ((i - 1) + 1) := by
        exact rowExt_step_lt J hi1_pos hi1_lt_t
      simpa [Nat.sub_add_cancel hi_pos] using this
    exact Nat.lt_of_lt_of_le hstep hrow


/-! ### Lemma 1.4(iii)

If `α_s = α'_t`, then `t = s+1`.
In our notation: if the row-coordinate at `sClose` in `I` equals the
row-coordinate at `uClose` in `J`, then `uClose = sClose + 1`.
-/

/-- Lemma 1.4(iii). -/
lemma close_chain_at_index
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hrow :
      rowExt J (uClose I J) ≤ rowExt I i) :
    rowExt J (i - 1) < rowExt I (i - 1) := by
  have h1 : colExt I i ≤ colExt J (i - 1) :=
    close_chain_row_le_to_prev_col_le I J hIJ hi₁ hi₂ hrow
  have h2 : colExt I i < colExt J i :=
    close_chain_prev_col_le_to_col_lt I J hIJ hi₁ hi₂ h1
  have h3 : rowExt J i ≤ rowExt I (i - 1) :=
    close_chain_col_lt_to_prev_row_le I J hIJ hi₁ hi₂ h2
  exact close_chain_prev_row_le_to_prev_row_lt I J hIJ hi₁ hi₂ h3

lemma close_uClose_ne_gt_of_rowEq
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowEq :
      rowExt I (sClose I J + 1) = rowExt J (uClose I J))
    (hgt : sClose I J + 1 < uClose I J) :
    False := by
  sorry

lemma close_uClose_eq_succ_of_rowEq
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowEq :
      rowExt I (sClose I J + 1) = rowExt J (uClose I J)) :
    uClose I J = sClose I J + 1 := by
  have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hC.ne
  have hle : sClose I J + 1 ≤ uClose I J := by omega
  by_contra hne
  have hgt : sClose I J + 1 < uClose I J := by omega
  exact close_uClose_ne_gt_of_rowEq I J hC hrowEq hgt

/-- Case `α_s = α'_t`: then the middle block has length one. -/
lemma close_pairExt_ne_mid_of_rowEq
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowEq :
      rowExt I (sClose I J + 1) = rowExt J (uClose I J))
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₁ : sClose I J + 1 ≤ j)
    (hj₂ : j ≤ uClose I J) :
    pairExt I i ≠ pairExt J j := by
  have hIJ : I ≠ J := hC.ne
  have hu : uClose I J = sClose I J + 1 :=
    close_uClose_eq_succ_of_rowEq I J hC hrowEq
  have hi : i = sClose I J + 1 := by
    linarith
  have hj : j = sClose I J + 1 := by
    linarith
  have hs1_le_t : sClose I J + 1 ≤ t := by
    have hsltp : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact le_trans (Nat.succ_le_of_lt hsltp) (pClose_le I J)
  have hneq :
      pairExt I (sClose I J + 1) ≠ pairExt J (sClose I J + 1) := by
    have hdiff : diffAt I J (sClose I J + 1) :=
      diffAt_succ_sClose_of_mu_eq_right I J hIJ
    exact (diffAt_iff_pairExt_ne I J (by omega) hs1_le_t).mp hdiff
  simpa [hi, hj] using hneq

/-- In the strict case `α'_t < α_s`, every middle row of `I` is strictly above `α'_t`. -/
lemma close_mid_row_gt_uClose_row_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (sClose I J + 1))
    {i : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J) :
    rowExt J (uClose I J) < rowExt I i := by
  exact close_row_chain_of_uClose_row_lt I J hrowLt i hi₁ hi₂

/-- Case `α'_t < α_s`: use the row/column chains from Lemma 1.4(iv)
to force all middle pairs to be distinct. -/
lemma close_pairExt_ne_mid_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (sClose I J + 1))
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₂ : j ≤ uClose I J) :
    pairExt I i ≠ pairExt J j := by
  have hiRow : rowExt J (uClose I J) < rowExt I i := by
    exact close_row_chain_of_uClose_row_lt (I := I) (J := J) hrowLt i hi₁ hi₂
  have hmonoJ : Monotone (rowExt J) := rowExt_monotone J
  have hjRow : rowExt J j ≤ rowExt J (uClose I J) := by
    exact hmonoJ hj₂
  have hstrict : rowExt J j < rowExt I i := by
    exact lt_of_le_of_lt hjRow hiRow
  intro heq
  have hfst : rowExt I i = rowExt J j := by
    exact congrArg Prod.fst heq
  simp [hfst] at hstrict

lemma not_row_boundary_gt_of_close (I J : MinorIndex m n t) (hC : Close I J) :
  ¬ rowExt I (sClose I J + 1) < rowExt J (uClose I J) := by sorry


/-- Lemma 1.4(ii), final assembly. -/
lemma close_pairExt_ne_mid_core
    (I J : MinorIndex m n t)
    (hC : Close I J)
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₁ : sClose I J + 1 ≤ j)
    (hj₂ : j ≤ uClose I J)
    (heq : pairExt I i = pairExt J j) :
    False := by
  have htri :=
    lt_trichotomy (rowExt J (uClose I J)) (rowExt I (sClose I J + 1))
  rcases htri with hlt | heqRow | hgt
  · exact (close_pairExt_ne_mid_of_uClose_row_lt I J hlt hi₁ hi₂ hj₂) heq
  · exact (close_pairExt_ne_mid_of_rowEq I J hC heqRow.symm
      hi₁ hi₂ hj₁ hj₂) heq
  · exact (not_row_boundary_gt_of_close I J hC) hgt

/-- Lemma 1.4(ii). -/
lemma close_pairExt_ne_mid
    (I J : MinorIndex m n t)
    (hC : Close I J)
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₁ : sClose I J + 1 ≤ j)
    (hj₂ : j ≤ uClose I J) :
    pairExt I i ≠ pairExt J j := by
  intro heq
  exact close_pairExt_ne_mid_core I J hC hi₁ hi₂ hj₁ hj₂ heq



/-! ### Lemma 1.4(iv)

If `α'_t < α_s`, then:
1. for every `s+1 ≤ i ≤ t`, one has `α'_t < α_i`;
2. for every `s+1 ≤ j < t`, one has `β_j < β_{j+1} ≤ β'_t`;
3. moreover, if `s+1 < t`, then `β_s < β'_t`.

Again the paper's second index `t` is our `uClose`.
-/

lemma close_col_step_lt_mid
    (I J : MinorIndex m n t)
    (hC : Close I J) :
    ∀ j : ℕ, sClose I J + 1 ≤ j → j < uClose I J →
      colExt I j < colExt I (j + 1) := by
  intro j hj₁ hj₂
  have hIJ : I ≠ J := hC.ne
  have hu_le_t : uClose I J ≤ t := by
    exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have hj_pos : 0 < j := by
    omega
  have hj_le_t : j ≤ t := by
    omega
  have hj1_le_t : j + 1 ≤ t := by
    omega
  let k0 : Fin t := ⟨j - 1, by omega⟩
  let k1 : Fin t := ⟨j, by omega⟩
  have hk01 : k0 < k1 := by
    simp [k0, k1]
    omega
  have hfin : I.col k0 < I.col k1 := I.col.strictMono hk01
  have hcolj : colExt I j = (I.col k0).1 + 1 := by
    unfold colExt
    simp [hj_pos.ne', hj_le_t, k0]
  have hcolj1 : colExt I (j + 1) = (I.col k1).1 + 1 := by
    unfold colExt
    simp [hj1_le_t, k1]
  have hnat : (I.col k0).1 + 1 < (I.col k1).1 + 1 := by
    exact Nat.succ_lt_succ <| by
      simpa using hfin
  simpa [hcolj, hcolj1] using hnat

/-- Lemma 1.4(iv), second inequality chain on the column side. -/
lemma close_col_chain_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (sClose I J + 1)) :
    ∀ j : ℕ, sClose I J + 1 ≤ j → j < uClose I J →
      colExt I j < colExt I (j + 1) ∧
      colExt I (j + 1) ≤ colExt J (uClose I J) := by
  sorry

/-- Lemma 1.4(iv), final strict inequality when `s+1 < t`. -/
lemma close_last_col_lt_uClose_col_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (sClose I J + 1))
    (hst : sClose I J + 1 < uClose I J) :
    colExt I (uClose I J) < colExt J (uClose I J) := by
  sorry

end paper1_4

section

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]



theorem genericMinor_isGroebnerBasis_of_isDiagonalTermOrder
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (Set.range (genericMinor (t := t)))
      (detIdeal m n t k) := by
  sorry

theorem minorSet_isGroebnerBasis_of_isDiagonalTermOrder
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (minorSet t)
      (detIdeal m n t k) := by
  simpa [minorSet_eq_range] using
    genericMinor_isGroebnerBasis_of_isDiagonalTermOrder ord hdiag

end


end Determinantal
