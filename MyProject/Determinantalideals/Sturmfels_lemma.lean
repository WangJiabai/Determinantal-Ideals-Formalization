import Mathlib
import MyProject.Determinantalideals.Basic
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.Ideal
import MyProject.Determinantalideals.DiagonalOrder
import Groebner.Groebner

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

/-- Sort a list of matrix indices in row-column order.

This is the word of the generalized permutation attached to the input list.
-/
def generalizedPermutation
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin m × Fin n) :=
  ((xs.map toLex).insertionSort (fun x y : Fin m ×ₗ Fin n => x ≤ y)).map ofLex

namespace generalizedPermutation

theorem generalizedPermutation_sorted
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (generalizedPermutation xs).Pairwise (fun x y => toLex x ≤ toLex y) := by
  unfold generalizedPermutation
  simpa [List.pairwise_map] using
    (List.pairwise_insertionSort
      (fun x y : Fin m ×ₗ Fin n => x ≤ y)
      (xs.map toLex))

/-- The generalized permutation word contains exactly the same indices as the input list. -/
theorem generalizedPermutation_perm
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (generalizedPermutation xs).Perm xs := by
  unfold generalizedPermutation
  simpa [Function.comp_def] using
    ((List.perm_insertionSort
      (fun x y : Fin m ×ₗ Fin n => x ≤ y)
      (xs.map toLex)).map ofLex)

theorem generalizedPermutation_unique
    {m n : ℕ}
    {xs w₁ w₂ : List (Fin m × Fin n)}
    (h₁perm : w₁.Perm xs)
    (h₁sorted : w₁.Pairwise (fun x y => toLex x ≤ toLex y))
    (h₂perm : w₂.Perm xs)
    (h₂sorted : w₂.Pairwise (fun x y => toLex x ≤ toLex y)) :
    w₁ = w₂ := by
  have h₁sortedLex :
      (w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Pairwise
        (fun x y => x ≤ y) := by
    simpa [List.pairwise_map] using h₁sorted
  have h₂sortedLex :
      (w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Pairwise
        (fun x y => x ≤ y) := by
    simpa [List.pairwise_map] using h₂sorted
  have hpermLex :
      (w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)).Perm
        (w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n)) :=
    (h₁perm.map toLex).trans (h₂perm.map toLex).symm
  have hmap :
      w₁.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n) =
        w₂.map (toLex : Fin m × Fin n → Fin m ×ₗ Fin n) :=
    hpermLex.eq_of_pairwise' h₁sortedLex h₂sortedLex
  exact (toLex : (Fin m × Fin n) ≃ Fin m ×ₗ Fin n).injective.list_map hmap

/-- The upper row of the generalized permutation. -/
def upperWord
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin m) :=
  (generalizedPermutation xs).map fun x => x.1

/-- The lower row of the generalized permutation. This is the row used to define width. -/
def lowerWord
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    List (Fin n) :=
  (generalizedPermutation xs).map fun x => x.2

lemma lowerWord_length
    {m n : ℕ}
    (xs : List (Fin m × Fin n)) :
    (lowerWord xs).length = xs.length := by
  unfold lowerWord
  rw [List.length_map]
  exact (generalizedPermutation_perm xs).length_eq

lemma lowerWord_ne_nil_of_ne_nil
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hxs : xs ≠ []) :
    lowerWord xs ≠ [] := by
  intro h
  have hlen : xs.length = 0 := by
    have hlen' := lowerWord_length xs
    rw [h] at hlen'
    exact hlen'.symm
  apply hxs
  cases xs with
  | nil =>
      rfl
  | cons x xs =>
      simp at hlen

/-- Width of a monomial-index list.

Given a list of matrix indices, first form the generalized permutation,
then take the lower row, and finally take the maximal length of a strictly
decreasing subsequence of that lower row.
-/
def width {m n : ℕ}
    (xs : List (Fin m × Fin n)) : ℕ :=
  (((lowerWord xs).sublists.filter
    (fun s : List (Fin n) =>
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)))))
    |>.foldl (fun acc s => max acc s.length) 0

lemma foldl_max_length_ge_acc
    {α : Type*}
    (L : List (List α))
    (acc : ℕ) :
    acc ≤ L.foldl (fun acc s => max acc s.length) acc := by
  induction L generalizing acc with
  | nil =>
      rfl
  | cons s L ih =>
      simpa using
        le_trans
          (Nat.le_max_left acc s.length)
          (ih (max acc s.length))

lemma length_le_foldl_max_length_of_mem_aux
    {α : Type*}
    {s : List α}
    (L : List (List α))
    (acc : ℕ)
    (hs : s ∈ L) :
    s.length ≤ L.foldl (fun acc t => max acc t.length) acc := by
  induction L generalizing acc with
  | nil =>
      simp at hs
  | cons t L ih =>
      simp only [List.mem_cons] at hs
      cases hs with
      | inl h =>
          rw [h]
          exact
            le_trans
              (Nat.le_max_right acc t.length)
              (foldl_max_length_ge_acc L (max acc t.length))
      | inr h =>
          exact ih (max acc t.length) h

lemma length_le_foldl_max_length_of_mem
    {α : Type*}
    {L : List (List α)}
    {s : List α}
    (hs : s ∈ L) :
    s.length ≤ L.foldl (fun acc t => max acc t.length) 0 := by
  exact length_le_foldl_max_length_of_mem_aux L 0 hs

lemma length_le_width_of_mem_filtered_sublists
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {s : List (Fin n)}
    (hs :
      s ∈ ((lowerWord xs).sublists.filter
        (fun s : List (Fin n) =>
          (s.zip s.tail).all (fun p => decide (p.1 > p.2))))) :
    s.length ≤ width xs := by
  unfold width
  exact length_le_foldl_max_length_of_mem hs

lemma one_le_width_of_lowerWord_ne_nil
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (h : lowerWord xs ≠ []) :
    1 ≤ width xs := by
  unfold width
  cases hW : lowerWord xs with
  | nil =>
      exact False.elim (h hW)
  | cons a t =>
      have hmem :
          [a] ∈ (((a :: t).sublists.filter
            (fun s : List (Fin n) =>
              (s.zip s.tail).all (fun p => decide (p.1 > p.2))))) := by
        simp
      simpa [hW] using
        (length_le_foldl_max_length_of_mem
          (L := ((a :: t).sublists.filter
            (fun s : List (Fin n) =>
              (s.zip s.tail).all (fun p => decide (p.1 > p.2)))))
          (s := [a])
          hmem)

lemma two_le_width_of_desc_pair_sublist
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {a b : Fin n}
    (hsub : List.Sublist [a, b] (lowerWord xs))
    (hab : a > b) :
    2 ≤ width xs := by
  apply length_le_width_of_mem_filtered_sublists
    (xs := xs)
    (s := [a, b])
  have hmem_sub : [a, b] ∈ (lowerWord xs).sublists := by
    exact (List.mem_sublists).2 hsub
  simp [hmem_sub, hab]

lemma not_desc_pair_sublist_of_width_eq_one
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hw : width xs = 1)
    {a b : Fin n}
    (hsub : List.Sublist [a, b] (lowerWord xs)) :
    ¬ a > b := by
  intro hab
  have h2 : 2 ≤ width xs :=
    two_le_width_of_desc_pair_sublist
      (xs := xs) hsub hab
  omega

lemma foldl_max_length_le
    {α : Type*}
    (L : List (List α))
    (B acc : ℕ)
    (hacc : acc ≤ B)
    (hL : ∀ s ∈ L, s.length ≤ B) :
    L.foldl (fun acc s => max acc s.length) acc ≤ B := by
  induction L generalizing acc with
  | nil =>
      simpa using hacc
  | cons s L ih =>
      simp only [List.mem_cons] at hL
      have hs : s.length ≤ B := hL s (Or.inl rfl)
      have htail : ∀ t ∈ L, t.length ≤ B := by
        intro t ht
        exact hL t (Or.inr ht)
      exact ih (max acc s.length) (max_le hacc hs) htail

lemma width_le_one_of_lowerWord_pairwise_le
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hmono : (lowerWord xs).Pairwise (fun a b => a ≤ b)) :
    width xs ≤ 1 := by
  unfold width
  apply foldl_max_length_le
  · exact Nat.zero_le 1
  · intro s hs
    have hs_mem :
        s ∈ (lowerWord xs).sublists := by
      exact (List.mem_filter.mp hs).1
    have hs_dec :
        (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true := by
      exact (List.mem_filter.mp hs).2
    have hsub : List.Sublist s (lowerWord xs) := by
      exact (List.mem_sublists).1 hs_mem
    have hs_mono : s.Pairwise (fun a b => a ≤ b) := by
      exact hmono.sublist hsub
    cases s with
    | nil =>
        simp
    | cons a s' =>
        cases s' with
        | nil =>
            simp
        | cons b t =>
            have hgt : a > b := by
              have h := hs_dec
              simp only [List.tail_cons, List.zip_cons_cons, gt_iff_lt, List.all_cons,
                Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Prod.forall] at h
              exact h.1
            have hle : a ≤ b := by
              have h := hs_mono
              simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
              exact h.1.1
            exact False.elim ((not_lt_of_ge hle) hgt)

lemma pairwise_le_of_no_desc_pair_sublist
    {n : ℕ}
    {l : List (Fin n)}
    (hno :
      ∀ a b : Fin n,
        List.Sublist [a, b] l → ¬ a > b) :
    l.Pairwise (fun a b => a ≤ b) := by
  induction l with
  | nil =>
      simp
  | cons a t ih =>
      simp only [List.pairwise_cons]
      constructor
      · intro b hb
        have hsub_tail : List.Sublist [b] t := by
          exact (List.singleton_sublist).2 hb
        have hsub : List.Sublist [a, b] (a :: t) := by
          simpa using hsub_tail.cons₂ a
        exact le_of_not_gt (hno a b hsub)
      · apply ih
        intro a' b' hsub'
        exact hno a' b' (hsub'.cons a)

lemma width_eq_one_iff_lowerWord_pairwise_le
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    (hxs : lowerWord xs ≠ []) :
    width xs = 1 ↔
      (lowerWord xs).Pairwise (fun a b => a ≤ b) := by
  constructor
  · intro hw
    apply pairwise_le_of_no_desc_pair_sublist
    intro a b hsub
    exact
      not_desc_pair_sublist_of_width_eq_one
        (xs := xs) hw hsub
  · intro hmono
    apply le_antisymm
    · exact width_le_one_of_lowerWord_pairwise_le
        (xs := xs) hmono
    · exact one_le_width_of_lowerWord_ne_nil
        (xs := xs) hxs

/-- Expand a monomial exponent vector into the list of all matrix-variable indices.

The index `(i,j)` appears exactly `E (i,j)` times.
-/
def indicesOfMonomialExp {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ) :
    List (Fin m × Fin n) :=
  List.flatMap
    (fun i : Fin m =>
      List.flatMap
        (fun j : Fin n =>
          List.replicate (E (i, j)) (i, j))
        (List.finRange n))
    (List.finRange m)

lemma count_indicesOfMonomialExp
    {m n : ℕ}
    (E : (Fin m × Fin n) →₀ ℕ)
    (p : Fin m × Fin n) :
    (indicesOfMonomialExp E).count p = E p := by
  classical
  rcases p with ⟨pi, pj⟩
  rw [indicesOfMonomialExp]
  rw [List.count_flatMap]
  calc
    (List.map
        (List.count (pi, pj) ∘
          fun i => List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
            (List.finRange n))
        (List.finRange m)).sum
        =
      ∑ i : Fin m,
        List.count (pi, pj)
          (List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
            (List.finRange n)) := by
        simpa [Function.comp_def] using
          (Fin.sum_univ_def
            (fun i : Fin m =>
              List.count (pi, pj)
                (List.flatMap (fun j => List.replicate (E (i, j)) (i, j))
                  (List.finRange n)))).symm
    _ =
      ∑ i : Fin m, ∑ j : Fin n,
        List.count (pi, pj) (List.replicate (E (i, j)) (i, j)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [List.count_flatMap]
        simpa [Function.comp_def] using
          (Fin.sum_univ_def
            (fun j : Fin n =>
              List.count (pi, pj) (List.replicate (E (i, j)) (i, j)))).symm
    _ =
      ∑ i : Fin m, ∑ j : Fin n,
        if (i, j) = (pi, pj) then E (i, j) else 0 := by
        simp [List.count_replicate, beq_iff_eq]
    _ = E (pi, pj) := by
        rw [Finset.sum_eq_single (s := Finset.univ) (a := pi)
          (f := fun i : Fin m => ∑ j : Fin n,
            if (i, j) = (pi, pj) then E (i, j) else 0)]
        · simp
        · intro i _ hi
          simp [hi]
        · intro hi
          exact False.elim (hi (Finset.mem_univ pi))

end generalizedPermutation

/-- The paper's width of a monomial, with monomials represented by exponent vectors. -/
def monomialWidth {m n : ℕ} (E : (Fin m × Fin n) →₀ ℕ) : ℕ :=
  generalizedPermutation.width
    (generalizedPermutation.indicesOfMonomialExp E)

lemma antidiagExp_apply'
    {m n t : ℕ}
    (I : MinorIndex m n t) (a : Fin m) (b : Fin n) :
    antidiagExp I (a, b) =
      if ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b then 1 else 0 := by
  classical
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b
  · rcases h with ⟨i, hrow, hcol⟩
    have hpair :
        ∀ j : Fin t, ((I.row j, I.col j.rev) = (a, b)) ↔ j = i := by
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
    simp [antidiagExp, Finsupp.single_apply, hpair]
    subst hrow hcol
    simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, exists_eq]
  · have hpairFalse :
        ∀ j : Fin t, (I.row j, I.col j.rev) ≠ (a, b) := by
      intro j hj
      exact h ⟨j, by simpa using congrArg Prod.fst hj, by simpa using congrArg Prod.snd hj⟩
    simp [antidiagExp, h, hpairFalse]

/-- The list of anti-diagonal variables in a minor, in increasing row order. -/
abbrev antidiagIndexList {m n t : ℕ} (I : MinorIndex m n t) :
    List (Fin m × Fin n) :=
  List.ofFn fun i : Fin t => (I.row i, I.col i.rev)

lemma count_antidiagIndexList
    {m n t : ℕ}
    (I : MinorIndex m n t)
    (p : Fin m × Fin n) :
    (antidiagIndexList I).count p = antidiagExp I p := by
  classical
  rcases p with ⟨a, b⟩
  rw [antidiagExp_apply']
  by_cases h : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b
  · rcases h with ⟨i, hirow, hicol⟩
    have hex : ∃ i : Fin t, I.row i = a ∧ I.col i.rev = b := ⟨i, hirow, hicol⟩
    have hcount : (antidiagIndexList I).count (a, b) = 1 := by
      have hnodup : (antidiagIndexList I).Nodup := by
        rw [antidiagIndexList, List.nodup_ofFn]
        intro x y hxy
        have hrow : I.row x = I.row y := by
          simpa using congrArg Prod.fst hxy
        exact I.row.injective hrow
      have hmem : (a, b) ∈ antidiagIndexList I := by
        rw [antidiagIndexList, List.mem_ofFn']
        exact ⟨i, by simp [hirow, hicol]⟩
      exact List.count_eq_one_of_mem hnodup hmem
    simp [hex, hcount]
  · have hnotmem : (a, b) ∉ antidiagIndexList I := by
      simp [antidiagIndexList, h]
    have hcount : (antidiagIndexList I).count (a, b) = 0 :=
      List.count_eq_zero_of_not_mem hnotmem
    simp [h, hcount]

lemma antidiagIndexList_pairwise_lex
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).Pairwise (fun x y => toLex x ≤ toLex y) := by
  rw [antidiagIndexList, List.pairwise_ofFn]
  intro i j hij
  exact Prod.Lex.toLex_le_toLex.2
    (Or.inl (I.row.strictMono hij))

lemma antidiagIndexList_nodup
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).Nodup := by
  rw [antidiagIndexList, List.nodup_ofFn]
  intro x y hxy
  have hrow : I.row x = I.row y := by
    simpa using congrArg Prod.fst hxy
  exact I.row.injective hrow

lemma mem_indicesOfMonomialExp_of_pos
    {m n : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    {p : Fin m × Fin n}
    (hp : 0 < E p) :
    p ∈ generalizedPermutation.indicesOfMonomialExp E := by
  rw [← List.count_pos_iff]
  simpa [generalizedPermutation.count_indicesOfMonomialExp] using hp

lemma antidiagExp_pos_of_mem_antidiagIndexList
    {m n t : ℕ}
    {I : MinorIndex m n t}
    {p : Fin m × Fin n}
    (hp : p ∈ antidiagIndexList I) :
    0 < antidiagExp I p := by
  rcases p with ⟨a, b⟩
  rw [antidiagExp_apply']
  rw [antidiagIndexList, List.mem_ofFn'] at hp
  rcases hp with ⟨i, hi⟩
  have hrow : I.row i = a := by
    simpa using congrArg Prod.fst hi
  have hcol : I.col i.rev = b := by
    simpa using congrArg Prod.snd hi
  rw [if_pos ⟨i, hrow, hcol⟩]
  norm_num

lemma antidiagIndexList_subperm_indicesOfMonomialExp_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Subperm (antidiagIndexList I)
      (generalizedPermutation.indicesOfMonomialExp E) := by
  exact (antidiagIndexList_nodup I).subperm fun p hp =>
    mem_indicesOfMonomialExp_of_pos
      (lt_of_lt_of_le (antidiagExp_pos_of_mem_antidiagIndexList hp) (hle p))

lemma antidiagIndexList_sublist_generalizedPermutation_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Sublist (antidiagIndexList I)
      (generalizedPermutation
        (generalizedPermutation.indicesOfMonomialExp E)) := by
  classical
  haveI :
      Std.Antisymm (fun x y : Fin m × Fin n => toLex x ≤ toLex y) :=
    ⟨fun _ _ hxy hyx => (toLex : Fin m × Fin n ≃ Fin m ×ₗ Fin n).injective
      (le_antisymm hxy hyx)⟩
  refine List.sublist_of_subperm_of_pairwise
    (r := fun x y : Fin m × Fin n => toLex x ≤ toLex y)
    ?_ ?_ ?_
  · exact (antidiagIndexList_subperm_indicesOfMonomialExp_of_antidiagExp_le
      (E := E) I hle).trans
      ((generalizedPermutation.generalizedPermutation_perm
        (generalizedPermutation.indicesOfMonomialExp E)).symm.subperm)
  · exact antidiagIndexList_pairwise_lex I
  · exact generalizedPermutation.generalizedPermutation_sorted
      (generalizedPermutation.indicesOfMonomialExp E)

lemma antidiagIndexList_map_snd
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (antidiagIndexList I).map Prod.snd =
      List.ofFn (fun i : Fin t => I.col i.rev) := by
  simp [antidiagIndexList, List.map_ofFn, Function.comp_def]

lemma antidiagIndexList_lowerWord_sublist_of_antidiagExp_le
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    List.Sublist
      (List.ofFn (fun i : Fin t => I.col i.rev))
      (generalizedPermutation.lowerWord
        (generalizedPermutation.indicesOfMonomialExp E)) := by
  have hsub :=
    (antidiagIndexList_sublist_generalizedPermutation_of_antidiagExp_le
      (E := E) I hle).map Prod.snd
  simpa [generalizedPermutation.lowerWord, antidiagIndexList_map_snd, Function.comp_def] using hsub

lemma antidiagLower_pairwise_gt
    {m n t : ℕ}
    (I : MinorIndex m n t) :
    (List.ofFn (fun i : Fin t => I.col i.rev)).Pairwise (fun a b => a > b) := by
  rw [List.pairwise_ofFn]
  intro i j hij
  exact I.col.strictMono (Fin.rev_lt_rev.mpr hij)

lemma zip_tail_all_gt_of_pairwise_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hs : s.Pairwise (fun a b => a > b)) :
    (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true := by
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      cases s with
      | nil =>
          simp
      | cons b t =>
          have hs' :
              (∀ x ∈ b :: t, a > x) ∧
                (b :: t).Pairwise (fun a b => a > b) := by
            simpa [List.pairwise_cons] using hs
          have hab : a > b := hs'.1 b (by simp)
          have htail : (b :: t).Pairwise (fun a b => a > b) := hs'.2
          simp only [List.tail_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hab, ih htail⟩

lemma length_le_width_of_lowerWord_sublist_pairwise_gt
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {s : List (Fin n)}
    (hsub : List.Sublist s (generalizedPermutation.lowerWord xs))
    (hpair : s.Pairwise (fun a b => a > b)) :
    s.length ≤ generalizedPermutation.width xs := by
  apply generalizedPermutation.length_le_width_of_mem_filtered_sublists
    (xs := xs) (s := s)
  have hs_mem : s ∈ (generalizedPermutation.lowerWord xs).sublists :=
    (List.mem_sublists).2 hsub
  have hall :
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true :=
    zip_tail_all_gt_of_pairwise_gt hpair
  simp [hs_mem, hall]

namespace generalizedPermutation

lemma exists_mem_of_pos_le_foldl_max_length_aux
    {α : Type*}
    {L : List (List α)}
    {acc t : ℕ}
    (hacc : acc < t)
    (h : t ≤ L.foldl (fun acc s => max acc s.length) acc) :
    ∃ s ∈ L, t ≤ s.length := by
  induction L generalizing acc with
  | nil =>
      simp at h
      omega
  | cons s L ih =>
      simp only [List.foldl_cons] at h
      by_cases hs : t ≤ s.length
      · exact ⟨s, by simp, hs⟩
      · have hmax_lt : max acc s.length < t := by
          rw [Nat.max_lt]
          exact ⟨hacc, Nat.lt_of_not_ge hs⟩
        rcases ih hmax_lt h with ⟨u, huL, htu⟩
        exact ⟨u, by simp [huL], htu⟩

lemma exists_mem_of_pos_le_foldl_max_length
    {α : Type*}
    {L : List (List α)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ L.foldl (fun acc s => max acc s.length) 0) :
    ∃ s ∈ L, t ≤ s.length :=
  exists_mem_of_pos_le_foldl_max_length_aux ht h

lemma exists_decreasing_sublist_of_le_width
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ width xs) :
    ∃ s : List (Fin n),
      List.Sublist s (lowerWord xs) ∧
      (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true ∧
      t ≤ s.length := by
  unfold width at h
  rcases exists_mem_of_pos_le_foldl_max_length (L :=
      (lowerWord xs).sublists.filter
        (fun s : List (Fin n) =>
          (s.zip s.tail).all (fun p => decide (p.1 > p.2)))) ht h with
    ⟨s, hs, hlen⟩
  simp only [List.mem_filter] at hs
  exact ⟨s, (List.mem_sublists).1 hs.1, hs.2, hlen⟩

lemma isChain_gt_of_zip_tail_all_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hall : (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true) :
    s.IsChain (fun a b => a > b) := by
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      cases s with
      | nil =>
          simp
      | cons b t =>
          simp only [List.tail_cons, List.zip_cons_cons, List.all_cons,
            Bool.and_eq_true, decide_eq_true_eq] at hall
          exact List.isChain_cons_cons.2 ⟨hall.1, ih hall.2⟩

lemma pairwise_gt_of_zip_tail_all_gt
    {n : ℕ}
    {s : List (Fin n)}
    (hall : (s.zip s.tail).all (fun p => decide (p.1 > p.2)) = true) :
    s.Pairwise (fun a b => a > b) := by
  exact (List.sortedGT_iff_isChain.2
    (isChain_gt_of_zip_tail_all_gt hall)).pairwise

lemma exists_decreasing_sublistLen_of_le_width
    {m n : ℕ}
    {xs : List (Fin m × Fin n)}
    {t : ℕ}
    (ht : 0 < t)
    (h : t ≤ width xs) :
    ∃ s : List (Fin n),
      s.length = t ∧
      List.Sublist s (lowerWord xs) ∧
      s.Pairwise (fun a b => a > b) := by
  rcases exists_decreasing_sublist_of_le_width (xs := xs) ht h with
    ⟨s, hsub, hall, hlen⟩
  refine ⟨s.take t, ?_, ?_, ?_⟩
  · simp [Nat.min_eq_left hlen]
  · exact (List.take_sublist t s).trans hsub
  · exact (pairwise_gt_of_zip_tail_all_gt hall).sublist (List.take_sublist t s)

end generalizedPermutation

lemma exists_antidiagIndexList_sublist_generalizedPermutation_of_le_monomialWidth
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (ht : 0 < t)
    (hwidth : t ≤ monomialWidth E) :
    ∃ I : MinorIndex m n t,
      List.Sublist (antidiagIndexList I)
        (generalizedPermutation
          (generalizedPermutation.indicesOfMonomialExp E)) := by
  classical
  let xs := generalizedPermutation.indicesOfMonomialExp E
  let w := generalizedPermutation xs
  rcases generalizedPermutation.exists_decreasing_sublistLen_of_le_width
      (xs := xs) ht (by simpa [monomialWidth, xs] using hwidth) with
    ⟨s, hs_len, hs_sub, hs_pair⟩
  have hs_sub_map :
      s.Sublist (w.map Prod.snd) := by
    simpa [generalizedPermutation.lowerWord, w, xs] using hs_sub
  rcases List.sublist_map_iff.mp hs_sub_map with ⟨ys, hys_sub, hs_map⟩
  have hys_len : ys.length = t := by
    have hlen := congrArg List.length hs_map
    simpa [hs_len] using hlen.symm
  have hys_sorted : ys.Pairwise (fun x y => toLex x ≤ toLex y) := by
    exact (generalizedPermutation.generalizedPermutation_sorted xs).sublist (by
      simpa [w] using hys_sub)
  have hys_cols_pair :
      ys.Pairwise (fun x y : Fin m × Fin n => x.2 > y.2) := by
    have hmap_pair :
        (ys.map Prod.snd).Pairwise (fun a b => a > b) := by
      simpa [← hs_map] using hs_pair
    simpa [List.pairwise_map] using hmap_pair
  let rowFun : Fin t → Fin m :=
    fun i => (ys.get (i.cast hys_len.symm)).1
  let colFun : Fin t → Fin n :=
    fun i => (ys.get (i.rev.cast hys_len.symm)).2
  have hrow_strict : StrictMono rowFun := by
    intro i j hij
    have hij' : i.cast hys_len.symm < j.cast hys_len.symm := by
      simpa using hij
    have hlex := hys_sorted.rel_get_of_lt hij'
    have hcolgt := hys_cols_pair.rel_get_of_lt hij'
    rcases Prod.Lex.toLex_le_toLex.1 hlex with hrow | hsame
    · simpa [rowFun] using hrow
    · rcases hsame with ⟨_hroweq, hcolle⟩
      exact False.elim ((not_lt_of_ge hcolle) hcolgt)
  have hcol_strict : StrictMono colFun := by
    intro i j hij
    have hrev : j.rev.cast hys_len.symm < i.rev.cast hys_len.symm := by
      simpa using (Fin.rev_lt_rev.mpr hij)
    have hcolgt := hys_cols_pair.rel_get_of_lt hrev
    simpa [colFun] using hcolgt
  let I : MinorIndex m n t :=
    { row := OrderEmbedding.ofStrictMono rowFun hrow_strict
      col := OrderEmbedding.ofStrictMono colFun hcol_strict }
  refine ⟨I, ?_⟩
  have hanti_eq : antidiagIndexList I = ys := by
    apply List.ext_get
    · simp [antidiagIndexList, hys_len]
    · intro i hi₁ hi₂
      have hidx : t - (t - (i + 1) + 1) = i := by
        omega
      simp [antidiagIndexList, I, rowFun, colFun, hidx]
  simpa [hanti_eq, w] using hys_sub

lemma antidiagExp_le_of_antidiagIndexList_sublist_generalizedPermutation
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hsub : List.Sublist (antidiagIndexList I)
      (generalizedPermutation
        (generalizedPermutation.indicesOfMonomialExp E))) :
    antidiagExp I ≤ E := by
  intro p
  have hsubperm :
      List.Subperm (antidiagIndexList I)
        (generalizedPermutation.indicesOfMonomialExp E) :=
    hsub.subperm.trans
      ((generalizedPermutation.generalizedPermutation_perm
        (generalizedPermutation.indicesOfMonomialExp E)).subperm)
  have hcount :
      (antidiagIndexList I).count p ≤
        (generalizedPermutation.indicesOfMonomialExp E).count p :=
    hsubperm.count_le p
  rw [count_antidiagIndexList I p,
    generalizedPermutation.count_indicesOfMonomialExp] at hcount
  exact hcount

lemma antidiagExp_le_monomialWidth
    {m n t : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (I : MinorIndex m n t)
    (hle : antidiagExp I ≤ E) :
    t ≤ monomialWidth E := by
  have hsub :=
    antidiagIndexList_lowerWord_sublist_of_antidiagExp_le
      (E := E) I hle
  have hpair := antidiagLower_pairwise_gt I
  have hlen :
      (List.ofFn (fun i : Fin t => I.col i.rev)).length = t := by
    simp
  simpa [monomialWidth, hlen] using
    length_le_width_of_lowerWord_sublist_pairwise_gt
      (xs := generalizedPermutation.indicesOfMonomialExp E)
      hsub hpair

lemma lemma6_forward_exists_antidiagExp_le_width
    {m n r : ℕ}
    {E : (Fin m × Fin n) →₀ ℕ}
    (h : ∃ I : MinorIndex m n (r + 1), antidiagExp I ≤ E) :
    r + 1 ≤ monomialWidth E := by
  rcases h with ⟨I, hI⟩
  exact antidiagExp_le_monomialWidth I hI

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

end Determinantal
