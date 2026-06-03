import Mathlib

namespace Determinantal

lemma Finset.orderEmbOfFin_le_orderEmbOfFin_of_subset
    {α : Type*} [LinearOrder α] {s t : Finset α}
    (hst : s ⊆ t) (i : Fin s.card) :
    t.orderEmbOfFin rfl
        ⟨i, lt_of_lt_of_le i.isLt (Finset.card_le_card hst)⟩ ≤
      s.orderEmbOfFin rfl i := by
  have hp : List.Subperm s.sort t.sort := by
    exact (s.sort_nodup (· ≤ ·)).subperm (by
      intro x hx
      simpa only [Finset.mem_sort] using hst (by
        simpa only [Finset.mem_sort] using hx))
  have hsub : List.Sublist s.sort t.sort :=
    List.sublist_of_subperm_of_sortedLE hp
      s.sortedLT_sort.sortedLE t.sortedLT_sort.sortedLE
  rcases List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub with ⟨f, hf⟩
  let si : Fin s.sort.length := Fin.cast (by simp) i
  let ti : Fin t.sort.length :=
    Fin.cast (by simp) ⟨i, lt_of_lt_of_le i.isLt (Finset.card_le_card hst)⟩
  have hfval : ∀ (n : ℕ) (hn : n < s.sort.length),
      n ≤ (f ⟨n, hn⟩).val := by
    intro n
    induction n with
    | zero =>
        intro _hn
        omega
    | succ n ih =>
        intro hn
        have hn' : n < s.sort.length := lt_trans (Nat.lt_succ_self n) hn
        have hlt : f ⟨n, hn'⟩ < f ⟨n + 1, hn⟩ :=
          f.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self n))
        have ih' := ih hn'
        change n ≤ (f ⟨n, hn'⟩).val at ih'
        change (f ⟨n, hn'⟩).val < (f ⟨n + 1, hn⟩).val at hlt
        omega
  have hfi : ti ≤ f si := by
    change i.val ≤ (f si).val
    simpa [si] using hfval i.val (by simp)
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply]
  change t.sort.get ti ≤ s.sort.get si
  rw [hf si]
  exact t.sortedLT_sort.sortedLE.monotone_get hfi

namespace Finset

lemma sum_powerset_neg_one_pow_card_sdiff
    {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (hs : s.Nonempty) :
    (∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hs
  | insert a s ha ih =>
      rw [_root_.Finset.powerset_insert s a]
      have hdisj : Disjoint (s.powerset) (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro t ht hti
        rcases Finset.mem_image.mp hti with ⟨u, hu, rfl⟩
        exact ha ((Finset.mem_powerset.mp ht) (by simp))
      rw [_root_.Finset.sum_union hdisj]
      rw [_root_.Finset.sum_image]
      · have hpair :
            (∑ t ∈ s.powerset, (-1 : R) ^ ((insert a s) \ t).card) =
              - ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
          have hsdiff :
              ((insert a s) \ t) = insert a (s \ t) := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [hat]
            · simp [hxa]
          rw [hsdiff, Finset.card_insert_of_notMem]
          · simp [pow_succ]
          · intro has
            exact False.elim (ha ((Finset.mem_sdiff.mp has).1))
        have hpair' :
            (∑ t ∈ s.powerset, (-1 : R) ^ ((insert a s) \ insert a t).card) =
              ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card := by
          apply Finset.sum_congr rfl
          intro t ht
          have hsdiff : ((insert a s) \ insert a t) = s \ t := by
            ext x
            by_cases hxa : x = a
            · subst x
              simp [ha]
            · simp [hxa]
          rw [hsdiff]
        rw [hpair, hpair']
        simp
      · intro x hx y hy hxy
        have hax : a ∉ x := fun h => ha ((Finset.mem_powerset.mp hx) h)
        have hay : a ∉ y := fun h => ha ((Finset.mem_powerset.mp hy) h)
        exact Finset.Subset.antisymm
          ((Finset.insert_subset_insert_iff (s := x) (t := y) hax).mp (by
            rw [hxy]))
          ((Finset.insert_subset_insert_iff (s := y) (t := x) hay).mp (by
            rw [← hxy]))

lemma sum_powerset_neg_one_pow_card_eq_zero_of_nonempty
    {α R : Type*} [CommRing R]
    (s : Finset α) (hs : s.Nonempty) :
    (∑ t ∈ s.powerset, (-1 : R) ^ t.card) = 0 := by
  classical
  have hreindex :
      (∑ t ∈ s.powerset, (-1 : R) ^ t.card) =
        ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card := by
    refine Finset.sum_nbij'
      (fun t => s \ t) (fun t => s \ t) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact Finset.mem_powerset.mpr Finset.sdiff_subset
    · intro t ht
      exact Finset.mem_powerset.mpr Finset.sdiff_subset
    · intro t ht
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp ht)
    · intro t ht
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp ht)
    · intro t ht
      rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp ht)]
  rw [hreindex]
  exact sum_powerset_neg_one_pow_card_sdiff s hs

lemma sum_Icc_neg_one_pow_card_compl_eq_zero
    {α R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (s : Finset α) (hs : s ≠ Finset.univ) :
    (∑ t ∈ Finset.Icc s Finset.univ, (-1 : R) ^ tᶜ.card) = 0 := by
  classical
  let d : Finset α := Finset.univ \ s
  have hd : d.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hdempty
    apply hs
    apply Finset.eq_univ_of_forall
    intro x
    by_contra hxs
    have hx : x ∈ d := by
      simp [d, hxs]
    simp [d, hdempty] at hx
  rw [Finset.Icc_eq_image_powerset (Finset.subset_univ s)]
  rw [Finset.sum_image]
  · have hcard :
        ∀ u ∈ d.powerset, ((s ∪ u)ᶜ : Finset α).card = (d \ u).card := by
      intro u hu
      congr
      ext x
      have hu' : u ⊆ d := Finset.mem_powerset.mp hu
      by_cases hxs : x ∈ s
      · have hxud : x ∉ u := fun hxu =>
          (Finset.mem_sdiff.mp (hu' hxu)).2 hxs
        simp [d, hxs, hxud]
      · simp [d, hxs]
    calc
      (∑ x ∈ d.powerset, (-1 : R) ^ (s ∪ x)ᶜ.card)
          = ∑ x ∈ d.powerset, (-1 : R) ^ (d \ x).card := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hcard x hx]
      _ = 0 := sum_powerset_neg_one_pow_card_sdiff d hd
  · intro u hu v hv huv
    have hu' : u ⊆ d := Finset.mem_powerset.mp hu
    have hv' : v ⊆ d := Finset.mem_powerset.mp hv
    apply Finset.Subset.antisymm
    · intro x hx
      have hxsu : x ∈ s ∪ u := by
        exact Finset.mem_union_right s hx
      have hxsv : x ∈ s ∪ v := by
        change x ∈ (fun y => s ∪ y) v
        change x ∈ (fun y => s ∪ y) u at hxsu
        rwa [huv] at hxsu
      rcases Finset.mem_union.mp hxsu with hxs | hxu
      · exact False.elim ((Finset.mem_sdiff.mp (hu' hx)).2 hxs)
      · rcases Finset.mem_union.mp hxsv with hxs | hxv
        · exact False.elim ((Finset.mem_sdiff.mp (hu' hx)).2 hxs)
        · exact hxv
    · intro x hx
      have hxsv : x ∈ s ∪ v := by
        exact Finset.mem_union_right s hx
      have hxsu : x ∈ s ∪ u := by
        change x ∈ (fun y => s ∪ y) u
        change x ∈ (fun y => s ∪ y) v at hxsv
        rwa [← huv] at hxsv
      rcases Finset.mem_union.mp hxsv with hxs | hxv
      · exact False.elim ((Finset.mem_sdiff.mp (hv' hx)).2 hxs)
      · rcases Finset.mem_union.mp hxsu with hxs | hxu
        · exact False.elim ((Finset.mem_sdiff.mp (hv' hx)).2 hxs)
        · exact hxu

end Finset

/-- The degree-`d` homogeneous component of a polynomial
ring in finitely many variables is finite. -/
lemma homogeneousSubmodule_finite
    {m n : ℕ}
    {k : Type*} [Field k]
    (d : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin m × Fin n) k d) := by
  let S : Set ((Fin m × Fin n) →₀ ℕ) := {E | Finsupp.degree E = d}
  have hS : S.Finite := by
    exact (Finsupp.finite_of_degree_le (σ := Fin m × Fin n) d).subset
      (by
        intro E hE
        exact le_of_eq hE)
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  rw [Finsupp.supported_eq_span_single]
  exact Module.Finite.span_of_finite k (hS.image (fun E => Finsupp.single E (1 : k)))

/-- Rank-nullity for the restriction of a linear map to a finite-dimensional subspace. -/
lemma finrank_comap_ker_add_finrank_map
    {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (H : Submodule k V)
    [FiniteDimensional k H] :
    Module.finrank k (Submodule.comap H.subtype (LinearMap.ker f)) +
      Module.finrank k (Submodule.map f H) =
        Module.finrank k H := by
  let fH : H →ₗ[k] W := f.comp H.subtype
  have hker :
      LinearMap.ker fH = Submodule.comap H.subtype (LinearMap.ker f) := by
    ext x
    rfl
  have hrange :
      LinearMap.range fH = Submodule.map f H := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  calc
    Module.finrank k (Submodule.comap H.subtype (LinearMap.ker f)) +
        Module.finrank k (Submodule.map f H)
        = Module.finrank k (LinearMap.ker fH) +
            Module.finrank k (LinearMap.range fH) := by
            rw [hker, hrange]
    _ = Module.finrank k H := by
            rw [add_comm]
            exact LinearMap.finrank_range_add_finrank_ker fH

/-- Rank-nullity for the quotient map, with the kernel identified as the ideal. -/
lemma quotient_finrank_comap_restrictScalars_add_finrank_map
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (I : Ideal A) (H : Submodule k A)
    [FiniteDimensional k H] :
    Module.finrank k
        (Submodule.comap H.subtype (Submodule.restrictScalars k I)) +
      Module.finrank k
        (Submodule.map (Ideal.Quotient.mkₐ k I).toLinearMap H) =
        Module.finrank k H := by
  have hker :
      LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap =
        Submodule.restrictScalars k I := by
    ext x
    simp [LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker]
  exact finrank_comap_ker_add_finrank_map
    (f := (Ideal.Quotient.mkₐ k I).toLinearMap) H

/-- The span of a subfamily of a basis has dimension equal to the cardinality
of the subfamily's index type. -/
lemma finrank_span_range_basis_subtype
    {k M ι : Type*} [Field k]
    [AddCommGroup M] [Module k M]
    (b : Module.Basis ι k M) (p : ι → Prop) :
    Module.finrank k
      (Submodule.span k (Set.range fun i : { i : ι // p i } => b i.1))
      =
    Nat.card { i : ι // p i } := by
  classical
  have hli :
      LinearIndependent k (fun i : { i : ι // p i } => b i.1) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  rw [Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]

/-- Package a linearly independent spanning family as a basis without changing
the displayed vectors. -/
lemma exists_basis_eq_of_linearIndependent_span
    {k M ι : Type*} [Field k]
    [AddCommGroup M] [Module k M]
    (v : ι → M)
    (hli : LinearIndependent k v)
    (hspan : Submodule.span k (Set.range v) = ⊤) :
    ∃ b : Module.Basis ι k M, ∀ i, b i = v i := by
  let b : Module.Basis ι k M :=
    Module.Basis.mk hli (by simpa using hspan.ge)
  refine ⟨b, ?_⟩
  intro i
  exact Module.Basis.mk_apply hli (by simpa using hspan.ge) i

/-- Sorting a tuple through an injective map gives a strictly monotone tuple. -/
lemma strictMono_comp_tupleSort_of_injective {t u : ℕ}
    (f : Fin t → Fin u) (hf : Function.Injective f) :
    StrictMono (f ∘ Tuple.sort f) := by
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  exact hmono.strictMono_iff_injective.mpr
    (hf.comp (Equiv.injective (Tuple.sort f)))

/-- In any commutative ring, `(-1)^r` is self-inverse. -/
lemma neg_one_pow_mul_self {R : Type*} [CommRing R] (r : ℕ) :
    ((-1 : R) ^ r) * ((-1 : R) ^ r) = 1 := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      simp only [pow_succ]
      calc
        ((-1 : R) ^ r * -1) * ((-1 : R) ^ r * -1)
            =
          ((-1 : R) ^ r * ((-1 : R) ^ r)) * ((-1 : R) * (-1 : R)) := by
            ring
    _ = 1 := by
            rw [ih]
            ring

/-- A coefficient-triangularity criterion for polynomial linear independence.

For each vector `v i`, choose a monomial `key i` and an ordered rank `rank i`.  If the
chosen coefficient of `v i` is nonzero, and no `v j` can contribute to the coefficient
at `key i` unless `rank i ≤ rank j`, then a maximal-rank term in any finite relation
cannot cancel. -/
theorem mvPolynomial_linearIndependent_of_coeff_triangular
    {σ ι κ : Type*}
    {k : Type*} [Field k]
    [LinearOrder κ]
    (v : ι → MvPolynomial σ k)
    (key : ι → σ →₀ ℕ)
    (rank : ι → κ)
    (hrank : Function.Injective rank)
    (hdiag : ∀ i, MvPolynomial.coeff (key i) (v i) ≠ 0)
    (htri :
      ∀ i j,
        MvPolynomial.coeff (key i) (v j) ≠ 0 →
          rank i ≤ rank j) :
    LinearIndependent k v := by
  classical
  rw [linearIndependent_iff]
  intro c hc
  by_contra hc_ne
  have hsupp : c.support.Nonempty := by
    by_contra hsupp
    have hsupport_empty : c.support = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hsupp
    exact hc_ne (Finsupp.support_eq_empty.mp hsupport_empty)
  rcases Finset.exists_max_image c.support rank hsupp with
    ⟨i₀, hi₀mem, hi₀max⟩
  have hci₀_ne : c i₀ ≠ 0 := by
    simpa [Finsupp.mem_support_iff] using hi₀mem
  have hcoeff_zero :
      MvPolynomial.coeff (key i₀)
        (Finsupp.linearCombination k v c) = 0 := by
    rw [hc]
    simp
  have hcoeff_sum :
      MvPolynomial.coeff (key i₀)
        (Finsupp.linearCombination k v c)
        =
      c.sum fun j a => a * MvPolynomial.coeff (key i₀) (v j) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  have hsum_eq :
      c.sum (fun j a => a * MvPolynomial.coeff (key i₀) (v j)) =
        c i₀ * MvPolynomial.coeff (key i₀) (v i₀) := by
    rw [Finsupp.sum]
    apply Finset.sum_eq_single i₀
    · intro j hj hji
      have hcoeff_j_zero :
          MvPolynomial.coeff (key i₀) (v j) = 0 := by
        by_contra hcoeff_j
        have hle_forward : rank i₀ ≤ rank j := htri i₀ j hcoeff_j
        have hle_back : rank j ≤ rank i₀ := hi₀max j hj
        have hrank_eq : rank i₀ = rank j := le_antisymm hle_forward hle_back
        have hij : i₀ = j := hrank hrank_eq
        exact hji hij.symm
      simp [hcoeff_j_zero]
    · intro hi₀not
      exact False.elim (hi₀not hi₀mem)
  have hsum_zero :
      c.sum (fun j a => a * MvPolynomial.coeff (key i₀) (v j)) = 0 := by
    simpa [hcoeff_sum] using hcoeff_zero
  have hdiag_nonzero :
      c i₀ * MvPolynomial.coeff (key i₀) (v i₀) ≠ 0 :=
    mul_ne_zero hci₀_ne (hdiag i₀)
  exact hdiag_nonzero (by simpa [hsum_eq] using hsum_zero)

/-- A nonzero coefficient of a homogeneous multivariate polynomial has the
homogeneous degree. -/
lemma mvPolynomial_coeff_ne_zero_degree_of_isHomogeneous
    {σ : Type*} {k : Type*} [Field k]
    {p : MvPolynomial σ k} {d : ℕ} {E : σ →₀ ℕ}
    (hp : p.IsHomogeneous d)
    (hcoeff : MvPolynomial.coeff E p ≠ 0) :
    Finsupp.degree E = d := by
  have hp_mem :
      p ∈ MvPolynomial.homogeneousSubmodule σ k d := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact hp
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    Finsupp.mem_supported] at hp_mem
  exact hp_mem (by
    simpa [MvPolynomial.mem_support_iff] using hcoeff)

/-- Bind a finitely supported coefficient vector through finitely supported
coefficient expansions, multiplying outer and inner coefficients. -/
noncomputable def finsuppScalarBind
    {α β : Type*} {k : Type*} [Field k]
    (c : α →₀ k) (d : α → β →₀ k) : β →₀ k :=
  c.sum fun a ca => ca • d a

lemma finsuppScalarBind_apply
    {α β : Type*} {k : Type*} [Field k]
    (c : α →₀ k) (d : α → β →₀ k) (b : β) :
    finsuppScalarBind c d b = c.sum fun a ca => ca * d a b := by
  classical
  rw [finsuppScalarBind, Finsupp.sum]
  conv_rhs => rw [Finsupp.sum]
  simp

lemma finsuppScalarBind_apply_ne_zero_exists
    {α β : Type*} {k : Type*} [Field k]
    (c : α →₀ k) (d : α → β →₀ k) {b : β}
    (hb : finsuppScalarBind c d b ≠ 0) :
    ∃ a : α, c a ≠ 0 ∧ d a b ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hb
  rw [finsuppScalarBind_apply]
  rw [Finsupp.sum]
  refine Finset.sum_eq_zero ?_
  intro a _ha
  by_cases hca : c a = 0
  · simp [hca]
  · have hda : d a b = 0 := h a hca
    simp [hda]

lemma finsuppScalarBind_support_property
    {α β : Type*} {k : Type*} [Field k]
    (c : α →₀ k) (d : α → β →₀ k) (P : β → Prop)
    (h : ∀ a b, c a ≠ 0 → d a b ≠ 0 → P b) :
    ∀ b, finsuppScalarBind c d b ≠ 0 → P b := by
  intro b hb
  rcases finsuppScalarBind_apply_ne_zero_exists c d hb with
    ⟨a, hca, hdb⟩
  exact h a b hca hdb

lemma finsupp_mapDomain_support_property
    {α β : Type*} {k : Type*} [AddCommMonoid k]
    (f : α → β) (c : α →₀ k) (P : β → Prop)
    (h : ∀ a, c a ≠ 0 → P (f a)) :
    ∀ b, Finsupp.mapDomain f c b ≠ 0 → P b := by
  classical
  intro b hb
  have hbmem : b ∈ (Finsupp.mapDomain f c).support := by
    simpa [Finsupp.mem_support_iff] using hb
  have himage : b ∈ Finset.image f c.support :=
    Finsupp.mapDomain_support hbmem
  rcases Finset.mem_image.mp himage with ⟨a, hamem, rfl⟩
  exact h a (by simpa [Finsupp.mem_support_iff] using hamem)

lemma finsuppScalarBind_polynomial_sum
    {α β σ : Type*} {k : Type*} [Field k]
    (c : α →₀ k) (d : α → β →₀ k)
    (v : β → MvPolynomial σ k) :
    (finsuppScalarBind c d).sum
        (fun b a => MvPolynomial.C a * v b) =
      c.sum fun a ca =>
        MvPolynomial.C ca *
          (d a).sum (fun b db => MvPolynomial.C db * v b) := by
  classical
  unfold finsuppScalarBind
  change
    ((∑ a ∈ c.support, c a • d a).sum
        (fun b a => MvPolynomial.C a * v b)) =
      ∑ a ∈ c.support,
        MvPolynomial.C (c a) *
          (d a).sum (fun b db => MvPolynomial.C db * v b)
  rw [←Finsupp.sum_finset_sum_index]
  · apply Finset.sum_congr rfl
    intro a _ha
    rw [Finsupp.sum_smul_index]
    · calc
        (d a).sum (fun b db => MvPolynomial.C (c a * db) * v b)
            =
          (d a).sum (fun b db =>
            MvPolynomial.C (c a) * (MvPolynomial.C db * v b)) := by
            apply Finsupp.sum_congr
            intro b db
            simp [MvPolynomial.C_mul, mul_assoc]
        _ =
          MvPolynomial.C (c a) *
            (d a).sum (fun b db => MvPolynomial.C db * v b) := by
            rw [← Finsupp.mul_sum]
    · intro b
      simp
  · intro a
    simp
  · intro a x y
    rw [MvPolynomial.C_add, add_mul]

end Determinantal
