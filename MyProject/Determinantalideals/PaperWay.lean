import Mathlib
import MyProject.Determinantalideals.Ideal
import MyProject.Determinantalideals.MinorTerms
import MyProject.Determinantalideals.DiagonalOrder
import Groebner.Groebner
import Groebner.Remainder
import Groebner.Ideal

namespace Determinantal

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
  have hj_le_t : j ≤ t := by
    omega
  have hj1_le_t : j + 1 ≤ t := by
    omega
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
  have hj_le_t : j ≤ t := by
    omega
  have hj1_le_t : j + 1 ≤ t := by
    omega
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
      have hk : k < t := by
        omega
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
  · simp only [pairExt]
    rw [hrowExtI, hrowExtJ, hrow0]
  · simp only [pairExt]
    rw [hcolExtI, hcolExtJ, hcol0]

lemma pairExt_eq_of_mu_eq_right_gt_u
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J)
    {j : ℕ}
    (hj1 : uClose I J < j)
    (hj2 : j ≤ t) :
    pairExt I j = pairExt J j := by
  have hjpos : 0 < j := by
    omega
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
  · simp only [pairExt]
    rw [hrowExtI, hrowExtJ, hrow0]
  · simp only [pairExt]
    rw [hcolExtI, hcolExtJ, hcol0]

/-! ### `sClose + 1` is the first differing position under `mu I J = J` -/

lemma not_diffAt_lt_succ_sClose_of_mu_eq_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hmu : mu I J hIJ = J)
    {j : ℕ}
    (hj1 : 1 ≤ j)
    (hjlt : j < sClose I J + 1) :
    ¬ diffAt I J j := by
  have hj2 : j ≤ sClose I J := by
    omega
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
      exact Nat.lt_of_lt_of_eq hstep (Eq.symm hEqRow)
    · have hqeq : q = t := by omega
      subst hqeq
      unfold rowExt
      by_cases ht0 : q = 0
      · grind
      · have htnz : q ≠ 0 := ht0
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
      · have htnz : q ≠ 0 := ht0
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
integers for `(J,I)`. In our notation the paper's second index `t` is `uClose`. -/

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
  have hfirstIJ := firstDiff_succ_sClose_of_mu_eq_right I J hIJ hμIJ
  have hfirstJI := firstDiff_succ_sClose_of_mu_eq_right J I hIJ.symm hμJI
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
  have hsEq : sClose I J = sClose J I := close_sClose_eq_symm I J hC
  have hle₁ : uClose I J ≤ uClose J I := by
    apply uClose_le_of_tailAgree (I := I) (J := J) (q := uClose J I)
    · rw [hsEq]
      exact sClose_lt_uClose J I hIJ.symm
    · exact le_trans (uClose_le_pClose J I hIJ.symm) (pClose_le J I)
    · intro j hj₁ hj₂
      have htail : pairExt J j = pairExt I j :=
        tailAgree_after_u_of_mu_eq_right J I hIJ.symm hμJI j hj₁ hj₂
      simpa [eq_comm] using htail
  have hle₂ : uClose J I ≤ uClose I J := by
    apply uClose_le_of_tailAgree (I := J) (J := I) (q := uClose I J)
    · rw [← hsEq]
      exact sClose_lt_uClose I J hIJ
    · exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
    · intro j hj₁ hj₂
      exact Eq.symm (tailAgree_after_u_of_mu_eq_right I J hIJ hμIJ j hj₁ hj₂)
  exact le_antisymm hle₁ hle₂

/-! ### Lemma 1.4(ii)

For every `s+1 ≤ i,j ≤ t`, the pair at position `i` in `I` is different
from the pair at position `j` in `J`. -/

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

/-! ### The implication chain used in Lemma 1.4(iii)(iv)

For `s+1 < i ≤ t`, the paper uses the local chain
`α'_i ≤ α_i ⇒ β_i ≤ β'_{i-1} ⇒ β_i < β'_i ⇒ α'_i ≤ α_{i-1} ⇒ α'_{i-1} < α_{i-1}`.
Only the first arrow is still missing below; the remaining three local steps are already
formalized. -/

/-- First local arrow in the paper's implication chain. -/
lemma close_chain_row_le_to_prev_col_le
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hrow :
      rowExt J i ≤ rowExt I i) :
    colExt I i ≤ colExt J (i - 1) := by
  classical
  by_contra hnot
  have hi_pos : 0 < i := by
    omega
  have hi_le_t : i ≤ t := by
    exact le_trans hi₂ <| le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have him1_pos : 1 ≤ i - 1 := by
    omega
  have him1_lt_t : i - 1 < t := by
    omega
  have hstep_row : rowExt J (i - 1) < rowExt J i := by
    have : rowExt J (i - 1) < rowExt J ((i - 1) + 1) := by
      exact rowExt_step_lt J him1_pos him1_lt_t
    simpa [Nat.sub_add_cancel hi_pos] using this
  have hrow_prev_lt_i : rowExt J (i - 1) < rowExt I i := by
    exact lt_of_lt_of_le hstep_row hrow
  have hcol_prev_lt_i : colExt J (i - 1) < colExt I i := by
    exact lt_of_not_ge hnot
  have him1_uPred : uPred I J (i - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · omega
    · simpa [Nat.sub_add_cancel hi_pos] using hrow_prev_lt_i
    · simpa [Nat.sub_add_cancel hi_pos] using hcol_prev_lt_i
  have hu_le_prev : uClose I J ≤ i - 1 := by
    unfold uClose
    split_ifs with h
    · exact Nat.find_le him1_uPred
    · exfalso
      exact h ⟨pClose I J, uPred_pClose I J hIJ⟩
  have : i ≤ i - 1 := by
    exact le_trans hi₂ hu_le_prev
  omega

/-- Second local arrow in the paper's implication chain. -/
lemma close_chain_prev_col_le_to_col_lt
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
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

/-- Third local arrow in the paper's implication chain. -/
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

/-- Fourth local arrow in the paper's implication chain. -/
lemma close_chain_prev_row_le_to_prev_row_lt
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
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

/-- Packaged local implication chain. -/
lemma close_chain_at_index
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : sClose I J + 1 < i)
    (hi₂ : i ≤ uClose I J)
    (hrow :
      rowExt J i ≤ rowExt I i) :
    rowExt J (i - 1) < rowExt I (i - 1) := by
  have h1 : colExt I i ≤ colExt J (i - 1) :=
    close_chain_row_le_to_prev_col_le I J hIJ hi₁ hi₂ hrow
  have h2 : colExt I i < colExt J i :=
    close_chain_prev_col_le_to_col_lt I J hIJ hi₁ hi₂ h1
  have h3 : rowExt J i ≤ rowExt I (i - 1) :=
    close_chain_col_lt_to_prev_row_le I J hIJ hi₁ hi₂ h2
  exact close_chain_prev_row_le_to_prev_row_lt I J hIJ hi₁ hi₂ h3

/-! ### Lemma 1.4(iii)

If `α_t = α'_t`, then `t = s+1`.

In our notation, the paper's `t` is `uClose I J`, so the hypothesis is that
the row-coordinates of `I` and `J` agree at the common index `uClose I J`. -/

/-- Lemma 1.4(iii). -/
lemma close_uClose_eq_succ_of_rowEq
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowEq :
      rowExt I (uClose I J) = rowExt J (uClose I J)) :
    uClose I J = sClose I J + 1 := by
  have hIJ : I ≠ J := hC.ne
  have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
  have hle : sClose I J + 1 ≤ uClose I J := by
    exact Order.add_one_le_iff.mpr hsltu
  have hu_le : uClose I J ≤ sClose I J + 1 := by
    by_contra hnot
    have hgt : sClose I J + 1 < uClose I J := by
      exact Nat.lt_of_not_le hnot
    have h1 := close_chain_row_le_to_prev_col_le I J hIJ hgt le_rfl hrowEq.symm.le
    have h2 := close_chain_prev_col_le_to_col_lt I J hIJ hgt le_rfl h1
    have h3 := close_chain_col_lt_to_prev_row_le I J hIJ hgt le_rfl h2
    have hu_pos : 0 < uClose I J := by
      exact Nat.zero_lt_of_lt hsltu
    have hu1_pos : 1 ≤ uClose I J - 1 := by
      omega
    have hu1_lt_t : uClose I J - 1 < t := by
      have hu_le_t : uClose I J ≤ t := by
        exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
      exact Nat.sub_one_lt_of_le hu_pos hu_le_t
    have hstepI : rowExt I (uClose I J - 1) < rowExt I (uClose I J) := by
      have :
          rowExt I (uClose I J - 1) <
            rowExt I ((uClose I J - 1) + 1) := by
        exact rowExt_step_lt I hu1_pos hu1_lt_t
      simpa [Nat.sub_add_cancel hu_pos] using this
    have hlt : rowExt J (uClose I J) < rowExt I (uClose I J) := by
      exact lt_of_le_of_lt h3 hstepI
    have : rowExt I (uClose I J) < rowExt I (uClose I J) := by
      simp [hrowEq] at hlt
    exact lt_irrefl _ this
  exact le_antisymm hu_le hle


/-- Case `α_t = α'_t`: then the middle block has length one. -/
lemma close_pairExt_ne_mid_of_rowEq
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowEq :
      rowExt I (uClose I J) = rowExt J (uClose I J))
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₁ : sClose I J + 1 ≤ j)
    (hj₂ : j ≤ uClose I J) :
    pairExt I i ≠ pairExt J j := by
  have hIJ : I ≠ J := hC.ne
  have hu : uClose I J = sClose I J + 1 :=
    close_uClose_eq_succ_of_rowEq I J hC hrowEq
  have hi : i = uClose I J := by
    omega
  have hj : j = uClose I J := by
    omega
  have hu_le_t : uClose I J ≤ t := by
    exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have hu_pos : 1 ≤ uClose I J := by
    have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
    omega
  have hneq : pairExt I (uClose I J) ≠ pairExt J (uClose I J) := by
    have hdiff₁ : diffAt I J (sClose I J + 1) :=
      diffAt_succ_sClose_of_mu_eq_right I J hIJ
    have hdiffu : diffAt I J (uClose I J) := by
      simpa [hu] using hdiff₁
    exact (diffAt_iff_pairExt_ne I J hu_pos hu_le_t).mp hdiffu
  simpa [hi, hj] using hneq

/-! ### Lemma 1.4(iv)

If `α'_t < α_t`, then:
1. for every `s+1 ≤ i ≤ t`, one has `α'_i < α_i`;
2. for every `s+1 ≤ j < t`, one has `β_j < β_{j+1} ≤ β'_j`;
3. moreover, if `s+1 < t`, then `β_t < β'_t`.

Again the paper's second index `t` is our `uClose I J`. -/

/-- Lemma 1.4(iv), first inequality chain on the row side:
for every middle index `i`, one has `α'_i < α_i`. -/
lemma close_row_chain_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (uClose I J)) :
    ∀ i : ℕ, sClose I J + 1 ≤ i → i ≤ uClose I J →
      rowExt J i < rowExt I i := by
  have hIJ : I ≠ J := by
    intro hEq
    subst hEq
    exact lt_irrefl _ hrowLt
  have hmain :
      ∀ d j : ℕ,
        uClose I J - j = d →
        sClose I J + 1 ≤ j →
        j ≤ uClose I J →
        rowExt J j < rowExt I j := by
    intro d
    induction d with
    | zero =>
        intro j hd hj₁ hj₂
        have hj : j = uClose I J := by
          omega
        subst hj
        exact hrowLt
    | succ d ih =>
        intro j hd hj₁ hj₂
        have hj_lt_u : j < uClose I J := by
          omega
        have hd' : uClose I J - (j + 1) = d := by
          omega
        have hnext :
            rowExt J (j + 1) < rowExt I (j + 1) := by
          exact ih (j + 1) hd' (by omega) (by omega)
        have hprev :
            rowExt J ((j + 1) - 1) < rowExt I ((j + 1) - 1) := by
          exact close_chain_at_index
            I J hIJ
            (i := j + 1)
            (by omega)
            (by omega)
            (Nat.le_of_lt hnext)
        simpa using hprev
  intro i hi₁ hi₂
  exact hmain (uClose I J - i) i rfl hi₁ hi₂

/-- The middle-step strict column increase in `I`. -/
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

/-- Lemma 1.4(iv), second inequality chain on the column side:
for every `s+1 ≤ j < t`, one has `β_j < β_{j+1} ≤ β'_j`. -/
lemma close_col_chain_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (uClose I J)) :
    ∀ j : ℕ, sClose I J + 1 ≤ j → j < uClose I J →
      colExt I j < colExt I (j + 1) ∧
      colExt I (j + 1) ≤ colExt J j := by
  intro j hj₁ hj₂
  have hIJ : I ≠ J := hC.ne
  have hrowj1 : rowExt J (j + 1) < rowExt I (j + 1) := by
    exact close_row_chain_of_uClose_row_lt I J hrowLt (j + 1) (by omega) (by omega)
  have hle_row : rowExt J (j + 1) ≤ rowExt I (j + 1) := Nat.le_of_lt hrowj1
  have hcol_le : colExt I (j + 1) ≤ colExt J j := by
    exact close_chain_row_le_to_prev_col_le I J hIJ (by omega) (by omega) hle_row
  have hcol_lt : colExt I j < colExt I (j + 1) := by
    exact close_col_step_lt_mid I J hC j hj₁ hj₂
  exact ⟨hcol_lt, hcol_le⟩

/-- Lemma 1.4(iv), final strict inequality when `s+1 < t`:
one has `β_t < β'_t`. -/
lemma close_last_col_lt_uClose_col_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (uClose I J))
    (hst : sClose I J + 1 < uClose I J) :
    colExt I (uClose I J) < colExt J (uClose I J) := by
  have hIJ : I ≠ J := hC.ne
  have hu_pos : 0 < uClose I J := by
    have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
    omega
  have hu_le_t : uClose I J ≤ t := by
    exact le_trans (uClose_le_pClose I J hIJ) (pClose_le I J)
  have hchain :
      colExt I (uClose I J - 1) < colExt I (uClose I J) ∧
      colExt I (uClose I J) ≤ colExt J (uClose I J - 1) := by
    have hpred_ge : sClose I J + 1 ≤ uClose I J - 1 := by
      omega
    have hpred_lt : uClose I J - 1 < uClose I J := by
      omega
    simpa [Nat.sub_add_cancel hu_pos] using
      close_col_chain_of_uClose_row_lt I J hC hrowLt (uClose I J - 1) hpred_ge hpred_lt
  have hstepJ : colExt J (uClose I J - 1) < colExt J (uClose I J) := by
    have hu1_pos : 1 ≤ uClose I J - 1 := by
      omega
    have hu1_lt_t : uClose I J - 1 < t := by
      omega
    have : colExt J (uClose I J - 1) < colExt J ((uClose I J - 1) + 1) := by
      exact colExt_step_lt J hu1_pos hu1_lt_t
    simpa [Nat.sub_add_cancel hu_pos] using this
  exact lt_of_le_of_lt hchain.2 hstepJ

/-- Case `α'_t < α_t`: use Lemma 1.4(iv) to force all middle pairs to be distinct. -/
lemma close_pairExt_ne_mid_of_uClose_row_lt
    (I J : MinorIndex m n t)
    (hC : Close I J)
    (hrowLt :
      rowExt J (uClose I J) < rowExt I (uClose I J))
    {i j : ℕ}
    (hi₁ : sClose I J + 1 ≤ i)
    (hi₂ : i ≤ uClose I J)
    (hj₁ : sClose I J + 1 ≤ j)
    (hj₂ : j ≤ uClose I J) :
    pairExt I i ≠ pairExt J j := by
  intro heq
  by_cases hij : i < j
  · have hi_lt_u : i < uClose I J := by
      omega
    have hcolchain :
        colExt I i < colExt I (i + 1) ∧
        colExt I (i + 1) ≤ colExt J i := by
      exact close_col_chain_of_uClose_row_lt
        I J hC hrowLt i hi₁ hi_lt_u
    have hmonoJ : Monotone (colExt J) := colExt_monotone J
    have hi_le_j : i ≤ j := Nat.le_of_lt hij
    have hJi_le_Jj : colExt J i ≤ colExt J j := hmonoJ hi_le_j
    have hstrict : colExt I i < colExt J j := by
      exact lt_of_lt_of_le hcolchain.1 (le_trans hcolchain.2 hJi_le_Jj)
    have hEqCol : colExt I i = colExt J j := congrArg Prod.snd heq
    exact (Nat.ne_of_lt hstrict) hEqCol
  · have hj_le_i : j ≤ i := by
      omega
    have hrowj : rowExt J j < rowExt I j := by
      exact close_row_chain_of_uClose_row_lt I J hrowLt j hj₁ hj₂
    have hmonoI : Monotone (rowExt I) := rowExt_monotone I
    have hIj_le_Ii : rowExt I j ≤ rowExt I i := hmonoI hj_le_i
    have hstrict : rowExt J j < rowExt I i := by
      exact lt_of_lt_of_le hrowj hIj_le_Ii
    have hEqRow : rowExt I i = rowExt J j := congrArg Prod.fst heq
    exact (Nat.ne_of_lt hstrict) hEqRow.symm

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
  have huEq : uClose I J = uClose J I := close_uClose_eq_symm I J hC
  have hsEq : sClose I J = sClose J I := close_sClose_eq_symm I J hC
  intro heq
  have htri := lt_trichotomy (rowExt J (uClose I J)) (rowExt I (uClose I J))
  rcases htri with hlt | heqRow | hgt
  · exact (close_pairExt_ne_mid_of_uClose_row_lt I J hC hlt hi₁ hi₂ hj₁ hj₂) heq
  · exact (close_pairExt_ne_mid_of_rowEq I J hC heqRow.symm hi₁ hi₂ hj₁ hj₂) heq
  · have hj₁' : sClose J I + 1 ≤ j := by
      rwa [← hsEq]
    have hj₂' : j ≤ uClose J I := by
      rwa [← huEq]
    have hi₁' : sClose J I + 1 ≤ i := by
      rwa [← hsEq]
    have hi₂' : i ≤ uClose J I := by
      rwa [← huEq]
    have hneq' :
        pairExt J j ≠ pairExt I i := by
      have hgt' : rowExt I (uClose J I) < rowExt J (uClose J I) := by
        simpa [huEq] using hgt
      exact close_pairExt_ne_mid_of_uClose_row_lt J I hC.symm hgt' hj₁' hj₂' hi₁' hi₂'
    exact hneq' heq.symm

end paper1_4

section paper1_5

variable {m n t : ℕ}

/-- The distance used in the induction of CGG Prop. 1.5. -/
def closeDist (I J : MinorIndex m n t) : ℕ :=
  ∑ k : Fin t,
    (Nat.dist (I.row k).1 (J.row k).1 +
      Nat.dist (I.col k).1 (J.col k).1)

/-- Every pair of `K` comes from either the left endpoint `I` or the right endpoint `J`. -/
def PairExtFromEndpoints
    (I J K : MinorIndex m n t) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ t →
    pairExt K i = pairExt I i ∨ pairExt K i = pairExt J i

/-- A paper-1.5 style chain of indices:
`F 0 = I`, `F p = J`, and every adjacent pair is `Close`. -/
def IndexCloseChain
    (I J : MinorIndex m n t)
    (p : ℕ)
    (F : Fin (p + 1) → MinorIndex m n t) : Prop :=
  F 0 = I ∧
  F ⟨p, Nat.lt_succ_self p⟩ = J ∧
  (∀ i : Fin p, Close (F i.castSucc) (F i.succ))

/-- Every term of the chain uses only pairs coming from the two endpoints. -/
def IndexChainUsesOnlyEndpoints
    (I J : MinorIndex m n t)
    (p : ℕ)
    (F : Fin (p + 1) → MinorIndex m n t) : Prop :=
  ∀ q : Fin (p + 1), PairExtFromEndpoints I J (F q)

lemma closeDist_comm
    (I J : MinorIndex m n t) :
    closeDist I J = closeDist J I := by
  unfold closeDist
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [Nat.dist_comm]

lemma PairExtFromEndpoints.refl_left
    (I J : MinorIndex m n t) :
    PairExtFromEndpoints I J I := by
  intro i hi₁ hi₂
  exact Or.inl rfl

lemma PairExtFromEndpoints.refl_right
    (I J : MinorIndex m n t) :
    PairExtFromEndpoints I J J := by
  intro i hi₁ hi₂
  exact Or.inr rfl

lemma pairExt_mu_eq_left_le_s
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : 1 ≤ i)
    (hi₂ : i ≤ sClose I J) :
    pairExt (mu I J hIJ) i = pairExt I i := by
  let k : Fin t := ⟨i - 1, by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    have hp : pClose I J ≤ t := pClose_le I J
    omega⟩
  have hk_eq : k.1 + 1 = i := by
    simp only [k]
    exact Nat.sub_add_cancel hi₁
  have hk_le_s : k.1 + 1 ≤ sClose I J := by
    simpa [hk_eq] using hi₂
  have hi_t : i ≤ t := by
    have hs : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    exact le_trans hi₂ <| le_trans (Nat.le_of_lt hs) (pClose_le I J)
  have hrow :
      rowExt (mu I J hIJ) i = rowExt I i := by
    unfold rowExt
    have hi0 : i ≠ 0 := by omega
    simp [hi0, hi_t, mu, strictMonoToOrderEmbedding, muRow, k, hk_le_s]
  have hcol :
      colExt (mu I J hIJ) i = colExt I i := by
    unfold colExt
    have hi0 : i ≠ 0 := by omega
    simp [hi0, hi_t, mu, strictMonoToOrderEmbedding, muCol, k, hk_le_s]
  exact Prod.ext hrow hcol

lemma pairExt_mu_eq_left_gt_u
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : uClose I J < i)
    (hi₂ : i ≤ t) :
    pairExt (mu I J hIJ) i = pairExt I i := by
  have hi0 : 0 < i := by omega
  let k : Fin t := ⟨i - 1, by omega⟩
  have hk_eq : k.1 + 1 = i := by
    simp only [k]
    exact Nat.sub_add_cancel hi0
  have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
    rw [hk_eq]
    have hsu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
    omega
  have hk_not_le_u : ¬ k.1 + 1 ≤ uClose I J := by
    rw [hk_eq]
    omega
  have hrow :
      rowExt (mu I J hIJ) i = rowExt I i := by
    unfold rowExt
    have hi0' : i ≠ 0 := by omega
    simp [hi0', hi₂, mu, strictMonoToOrderEmbedding, muRow, k, hk_not_le_s, hk_not_le_u]
  have hcol :
      colExt (mu I J hIJ) i = colExt I i := by
    unfold colExt
    have hi0' : i ≠ 0 := by omega
    simp [hi0', hi₂, mu, strictMonoToOrderEmbedding, muCol, k, hk_not_le_s, hk_not_le_u]
  exact Prod.ext hrow hcol

/-- At each genuine paper-position, `μ(I,J)` takes its pair either from `I` or from `J`. -/
lemma mu_pairExt_eq_left_or_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {i : ℕ}
    (hi₁ : 1 ≤ i)
    (hi₂ : i ≤ t) :
    pairExt (mu I J hIJ) i = pairExt I i ∨
      pairExt (mu I J hIJ) i = pairExt J i := by
  by_cases hiS : i ≤ sClose I J
  · left
    exact pairExt_mu_eq_left_le_s I J hIJ hi₁ hiS
  · by_cases hiU : i ≤ uClose I J
    · right
      exact pairExt_mu_eq_right_of_mid I J hIJ (by omega) hiU
    · left
      exact pairExt_mu_eq_left_gt_u I J hIJ (by omega) hi₂

lemma mu_pairExtFromEndpoints
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    PairExtFromEndpoints I J (mu I J hIJ) := by
  intro i hi₁ hi₂
  exact mu_pairExt_eq_left_or_right I J hIJ hi₁ hi₂

/-- If a point uses only pairs from `I` and `μ(I,J)`,
then it already uses only pairs from `I` and `J`. -/
lemma pairExtFromEndpoints_trans_of_mu
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {K L : MinorIndex m n t}
    (hK : K = mu I J hIJ)
    (hL : PairExtFromEndpoints I K L) :
    PairExtFromEndpoints I J L := by
  intro i hi₁ hi₂
  rcases hL i hi₁ hi₂ with hLI | hLK
  · exact Or.inl hLI
  · subst hK
    rcases mu_pairExt_eq_left_or_right I J hIJ hi₁ hi₂ with hKI | hKJ
    · exact Or.inl (hLK.trans hKI)
    · exact Or.inr (hLK.trans hKJ)

/-- If a point uses only pairs from `μ(I,J)` and `J`,
 then it already uses only pairs from `I` and `J`. -/
lemma pairExtFromEndpoints_trans_of_mu'
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    {K L : MinorIndex m n t}
    (hK : K = mu I J hIJ)
    (hL : PairExtFromEndpoints K J L) :
    PairExtFromEndpoints I J L := by
  intro i hi₁ hi₂
  rcases hL i hi₁ hi₂ with hLK | hLJ
  · subst hK
    rcases mu_pairExt_eq_left_or_right I J hIJ hi₁ hi₂ with hKI | hKJ
    · exact Or.inl (hLK.trans hKI)
    · exact Or.inr (hLK.trans hKJ)
  · exact Or.inr hLJ

/-- Base case for Prop. 1.5: if `I` and `J` are already close, take the 2-term chain. -/
lemma exists_indexCloseChain_of_close
    (I J : MinorIndex m n t)
    (hC : Close I J) :
    ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
      IndexCloseChain I J p F ∧
      IndexChainUsesOnlyEndpoints I J p F := by
  classical
  refine ⟨1, ?_, ?_, ?_⟩
  · intro q
    exact if q.1 = 0 then I else J
  · constructor
    · simp
    · constructor
      · simp
      · intro i
        have hi : i = 0 := Fin.eq_zero i
        subst hi
        simp [hC]
  · intro q
    fin_cases q
    · simpa using (PairExtFromEndpoints.refl_left (I := I) (J := J))
    · simpa using (PairExtFromEndpoints.refl_right (I := I) (J := J))

/-- If `I` and `J` are not close, at least one of the two directed `μ`-steps
fails to reach the other endpoint. -/
lemma not_close_oriented
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hNC : ¬ Close I J) :
    mu I J hIJ ≠ J ∨ mu J I hIJ.symm ≠ I := by
  by_cases h₁ : mu I J hIJ = J
  · right
    intro h₂
    exact hNC ⟨hIJ, h₁, h₂⟩
  · exact Or.inl h₁

/-- Prop. 1.5, part (a): the intermediate point `μ(I,J)` is strictly closer to `I`
provided it is not already equal to `J`. -/
lemma closeDist_mu_lt_left_of_ne_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J)
    (hμ : mu I J hIJ ≠ J) :
    closeDist (mu I J hIJ) I < closeDist I J := by
  classical
  unfold closeDist
  refine Finset.sum_lt_sum ?_ ?_
  · intro k hk
    by_cases hs : k.1 + 1 ≤ sClose I J
    · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs]
    · by_cases hu : k.1 + 1 ≤ uClose I J
      · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs, hu, Nat.dist_comm]
      · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs, hu]
  · rcases exists_diffAt (mu I J hIJ) J hμ with ⟨j, hjt, hdiffμJ⟩
    have hj1 : 1 ≤ j := by
      cases j with
      | zero =>
          simp [diffAt] at hdiffμJ
      | succ j =>
          omega
    let k : Fin t := ⟨j - 1, by omega⟩
    have hk_succ : k.1 + 1 = j := by
      simp [k, Nat.sub_add_cancel hj1]
    have hnot_mid : ¬ (sClose I J < j ∧ j ≤ uClose I J) := by
      intro hmid
      have hEq : pairExt (mu I J hIJ) j = pairExt J j := by
        apply Prod.ext
        · unfold pairExt rowExt
          have hj0 : j ≠ 0 := by omega
          have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
            rw [hk_succ]
            omega
          have hk_le_u : k.1 + 1 ≤ uClose I J := by
            rw [hk_succ]
            omega
          simp [mu, strictMonoToOrderEmbedding, muRow, hj0, hjt, k, hk_not_le_s, hk_le_u]
        · unfold pairExt colExt
          have hj0 : j ≠ 0 := by omega
          have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
            rw [hk_succ]
            omega
          have hk_le_u : k.1 + 1 ≤ uClose I J := by
            rw [hk_succ]
            omega
          simp [mu, strictMonoToOrderEmbedding, muCol, hj0, hjt, k, hk_not_le_s, hk_le_u]
      have hneq :
          pairExt (mu I J hIJ) j ≠ pairExt J j :=
        (diffAt_iff_pairExt_ne (mu I J hIJ) J hj1 hjt).mp hdiffμJ
      exact hneq hEq
    have hside : j ≤ sClose I J ∨ uClose I J < j := by
      omega
    have hEqμI : pairExt (mu I J hIJ) j = pairExt I j := by
      cases hside with
      | inl hjs =>
          apply Prod.ext
          · unfold pairExt rowExt
            have hj0 : j ≠ 0 := by omega
            have hk_le_s : k.1 + 1 ≤ sClose I J := by
              rw [hk_succ]
              exact hjs
            simp [mu, strictMonoToOrderEmbedding, muRow, hj0, hjt, k, hk_le_s]
          · unfold pairExt colExt
            have hj0 : j ≠ 0 := by omega
            have hk_le_s : k.1 + 1 ≤ sClose I J := by
              rw [hk_succ]
              exact hjs
            simp [mu, strictMonoToOrderEmbedding, muCol, hj0, hjt, k, hk_le_s]
      | inr huj =>
          apply Prod.ext
          · unfold pairExt rowExt
            have hj0 : j ≠ 0 := by omega
            have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
              rw [hk_succ]
              have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
              omega
            have hk_not_le_u : ¬ k.1 + 1 ≤ uClose I J := by
              rw [hk_succ]
              omega
            simp [mu, strictMonoToOrderEmbedding, muRow, hj0, hjt, k, hk_not_le_s, hk_not_le_u]
          · unfold pairExt colExt
            have hj0 : j ≠ 0 := by omega
            have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
              rw [hk_succ]
              have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
              omega
            have hk_not_le_u : ¬ k.1 + 1 ≤ uClose I J := by
              rw [hk_succ]
              omega
            simp [mu, strictMonoToOrderEmbedding, muCol, hj0, hjt, k, hk_not_le_s, hk_not_le_u]
    have hneqμJ :
        pairExt (mu I J hIJ) j ≠ pairExt J j :=
      (diffAt_iff_pairExt_ne (mu I J hIJ) J hj1 hjt).mp hdiffμJ
    have hneqIJ : pairExt I j ≠ pairExt J j := by
      intro hEq
      exact hneqμJ (hEqμI.trans hEq)
    have hdiffIJ : diffAt I J j :=
      (diffAt_iff_pairExt_ne I J hj1 hjt).mpr hneqIJ
    have hdiffIJ' : diffAt I J (k.1 + 1) := by
      simpa [hk_succ] using hdiffIJ
    have hrawneq : (I.row k, I.col k) ≠ (J.row k, J.col k) := by
      simpa [diffAt, k, k.2] using hdiffIJ'
    have hrow_or_col : I.row k ≠ J.row k ∨ I.col k ≠ J.col k := by
      by_cases hrow : I.row k = J.row k
      · right
        intro hcol
        apply hrawneq
        exact Prod.ext hrow hcol
      · exact Or.inl hrow
    have hf0 :
        Nat.dist ((mu I J hIJ).row k).1 (I.row k).1 +
            Nat.dist ((mu I J hIJ).col k).1 (I.col k).1 = 0 := by
      cases hside with
      | inl hjs =>
          have hk_le_s : k.1 + 1 ≤ sClose I J := by
            rw [hk_succ]
            exact hjs
          simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hk_le_s]
      | inr huj =>
          have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
            rw [hk_succ]
            have hsltu : sClose I J < uClose I J := sClose_lt_uClose I J hIJ
            omega
          have hk_not_le_u : ¬ k.1 + 1 ≤ uClose I J := by
            rw [hk_succ]
            omega
          simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hk_not_le_s, hk_not_le_u]
    have hgpos :
        0 <
          Nat.dist (I.row k).1 (J.row k).1 +
            Nat.dist (I.col k).1 (J.col k).1 := by
      rcases hrow_or_col with hrow | hcol
      · have hrowv : (I.row k).1 ≠ (J.row k).1 := by
          intro hval
          apply hrow
          exact Fin.ext hval
        have hdist : 0 < Nat.dist (I.row k).1 (J.row k).1 := Nat.dist_pos_of_ne hrowv
        omega
      · have hcolv : (I.col k).1 ≠ (J.col k).1 := by
          intro hval
          apply hcol
          exact Fin.ext hval
        have hdist : 0 < Nat.dist (I.col k).1 (J.col k).1 := Nat.dist_pos_of_ne hcolv
        omega
    refine ⟨k, by simp, ?_⟩
    rw [hf0]
    exact hgpos

/-- Prop. 1.5, part (b): the intermediate point `μ(I,J)` is strictly closer to `J`
provided it is not already equal to `J`. -/
lemma closeDist_mu_lt_right_of_ne_right
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    closeDist (mu I J hIJ) J < closeDist I J := by
  classical
  unfold closeDist
  refine Finset.sum_lt_sum ?_ ?_
  · intro k hk
    by_cases hs : k.1 + 1 ≤ sClose I J
    · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs]
    · by_cases hu : k.1 + 1 ≤ uClose I J
      · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs, hu]
      · simp [mu, strictMonoToOrderEmbedding, muRow, muCol, hs, hu]
  · have hsltp : sClose I J < pClose I J := sClose_lt_pClose I J hIJ
    have hple : pClose I J ≤ t := pClose_le I J
    have hslt : sClose I J < t := lt_of_lt_of_le hsltp hple
    let k : Fin t := ⟨sClose I J, hslt⟩
    have hk_not_le_s : ¬ k.1 + 1 ≤ sClose I J := by
      simp [k]
    have hk_le_u : k.1 + 1 ≤ uClose I J := by
      simpa [k] using Nat.succ_le_of_lt (sClose_lt_uClose I J hIJ)
    have hf0 :
        Nat.dist ((mu I J hIJ).row k).1 (J.row k).1 +
            Nat.dist ((mu I J hIJ).col k).1 (J.col k).1 = 0 := by
      simp [mu, strictMonoToOrderEmbedding, muRow, muCol, k, hk_not_le_s, hk_le_u]
    have hdiff : diffAt I J (sClose I J + 1) :=
      diffAt_succ_sClose_of_mu_eq_right I J hIJ
    have hrawneq : (I.row k, I.col k) ≠ (J.row k, J.col k) := by
      simpa [diffAt, k, hslt] using hdiff
    have hrow_or_col : I.row k ≠ J.row k ∨ I.col k ≠ J.col k := by
      by_cases hrow : I.row k = J.row k
      · right
        intro hcol
        apply hrawneq
        exact Prod.ext hrow hcol
      · exact Or.inl hrow
    have hgpos :
        0 <
          Nat.dist (I.row k).1 (J.row k).1 +
            Nat.dist (I.col k).1 (J.col k).1 := by
      rcases hrow_or_col with hrow | hcol
      · have hrowv : (I.row k).1 ≠ (J.row k).1 := by
          intro hval
          apply hrow
          exact Fin.ext hval
        have hdist : 0 < Nat.dist (I.row k).1 (J.row k).1 :=
          Nat.dist_pos_of_ne hrowv
        omega
      · have hcolv : (I.col k).1 ≠ (J.col k).1 := by
          intro hval
          apply hcol
          exact Fin.ext hval
        have hdist : 0 < Nat.dist (I.col k).1 (J.col k).1 :=
          Nat.dist_pos_of_ne hcolv
        omega
    refine ⟨k, by simp, ?_⟩
    rw [hf0]
    exact hgpos

/-- Concatenate two close-chains. -/
lemma indexCloseChain_append
    {I K J : MinorIndex m n t}
    {p q : ℕ}
    {F : Fin (p + 1) → MinorIndex m n t}
    {G : Fin (q + 1) → MinorIndex m n t}
    (hF : IndexCloseChain I K p F)
    (hG : IndexCloseChain K J q G)
    (hFep : IndexChainUsesOnlyEndpoints I J p F)
    (hGep : IndexChainUsesOnlyEndpoints I J q G) :
    ∃ r : ℕ, ∃ H : Fin (r + 1) → MinorIndex m n t,
      IndexCloseChain I J r H ∧
      IndexChainUsesOnlyEndpoints I J r H := by
  classical
  rcases hF with ⟨hF0, hFp, hFadj⟩
  rcases hG with ⟨hG0, hGq, hGadj⟩
  let H : Fin (p + q + 1) → MinorIndex m n t := fun r =>
    if hr : r.1 ≤ p then
      F ⟨r.1, by omega⟩
    else
      G ⟨r.1 - p, by
        have hrlt : r.1 < p + q + 1 := r.2
        omega⟩
  refine ⟨p + q, H, ?_, ?_⟩
  · constructor
    · have h0 : (0 : ℕ) ≤ p := Nat.zero_le p
      simpa [H, h0] using hF0
    · constructor
      · by_cases hq0 : q = 0
        · subst hq0
          have hKJ : K = J := by
            simpa using hG0.symm.trans hGq
          have hlast : (p : ℕ) ≤ p := le_rfl
          simpa [H, hlast, hKJ] using hFp
        · have hlast : ¬ (p + q ≤ p) := by omega
          simpa [H, hlast, hq0] using hGq
      · intro i
        by_cases hip : i.1 < p
        · let j : Fin p := ⟨i.1, hip⟩
          have hcast : (i.castSucc).1 ≤ p := by
            simpa using (le_of_lt hip : i.1 ≤ p)
          have hsucc : (i.succ).1 ≤ p := by
            simpa using (Nat.succ_le_of_lt hip : i.1 + 1 ≤ p)
          have hHi : H i.castSucc = F j.castSucc := by
            exact dif_pos hcast
          have hHnext : H i.succ = F j.succ := by
            exact dif_pos hip
          rw [hHi, hHnext]
          exact hFadj j
        · by_cases hieq : i.1 = p
          · have hqpos : 0 < q := by
              have hi_lt : i.1 < p + q := i.2
              omega
            have hcast : (i.castSucc).1 ≤ p := by
              simp [hieq]
            have hsucc : ¬ (i.succ).1 ≤ p := by
              simp [hieq]
            have hHi : H i.castSucc = K := by
              unfold H
              simp [hieq, hFp]
            have hHnext : H i.succ = G ⟨1, by omega⟩ := by
              unfold H
              simp [hieq]
            have hmid : Close K (G ⟨1, by omega⟩) := by
              simpa [hG0] using hGadj ⟨0, hqpos⟩
            rw [hHi, hHnext]
            exact hmid
          · have hgt : p < i.1 := by omega
            let j : Fin q := ⟨i.1 - p, by
              have hi_lt : i.1 < p + q := i.2
              omega⟩
            have hcast : ¬ (i.castSucc).1 ≤ p := by
              simpa using (not_le_of_gt hgt : ¬ i.1 ≤ p)
            have hsucc : ¬ (i.succ).1 ≤ p := by
              have hs : p < i.1 + 1 := Nat.lt_succ_of_lt hgt
              simpa using (not_le_of_gt hs : ¬ (i.1 + 1 ≤ p))
            have hHi : H i.castSucc = G j.castSucc := by
              exact dif_neg hcast
            have hidx : (⟨i.1 + 1 - p, by
              have hi_lt : i.1 < p + q := i.2
              omega⟩ : Fin (q + 1)) = j.succ := by
              apply Fin.ext
              simp [j]
              omega
            have hHnext : H i.succ = G j.succ := by
              have htmp : H i.succ = G ⟨i.1 + 1 - p, by
                  have hi_lt : i.1 < p + q := i.2
                  omega⟩ := by
                unfold H
                simp only [Fin.val_succ, Order.add_one_le_iff]
                exact dif_neg hip
              exact htmp.trans (by rw [hidx])
            rw [hHi, hHnext]
            exact hGadj j
  · intro r
    by_cases hr : r.1 ≤ p
    · simpa [H, hr] using hFep ⟨r.1, by omega⟩
    · simpa [H, hr] using hGep ⟨r.1 - p, by
        have hrlt : r.1 < p + q + 1 := r.2
        omega⟩

/-- Strong-induction form of Prop. 1.5. -/
theorem exists_indexCloseChain_aux
    (N : ℕ) :
    ∀ I J : MinorIndex m n t,
      closeDist I J ≤ N →
      I ≠ J →
      ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
        IndexCloseChain I J p F ∧
        IndexChainUsesOnlyEndpoints I J p F := by
  intro I J hdist hIJ
  have hstrong :
      ∀ N : ℕ,
        ∀ I J : MinorIndex m n t,
          closeDist I J ≤ N →
          I ≠ J →
          (∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain I J p F ∧
              IndexChainUsesOnlyEndpoints I J p F) ∧
          (∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain J I p F ∧
              IndexChainUsesOnlyEndpoints J I p F) := by
    intro N
    refine Nat.strong_induction_on N ?_
    intro N ih I J hdist hIJ
    by_cases hC : Close I J
    · exact
        ⟨exists_indexCloseChain_of_close I J hC,
         exists_indexCloseChain_of_close J I hC.symm⟩
    · rcases not_close_oriented I J hIJ hC with hμ | hμ
      · let K : MinorIndex m n t := mu I J hIJ
        have hK : K = mu I J hIJ := rfl
        have hIK_ne : I ≠ K := by
          intro hEq
          have hne : K ≠ I := by
            simpa [hK] using (mu_ne_left I J hIJ)
          exact hne hEq.symm
        have hKJ_ne : K ≠ J := by
          simpa [hK] using hμ
        have hIK_lt : closeDist I K < N := by
          have hlt' : closeDist K I < closeDist I J := by
            simpa [hK] using
              (closeDist_mu_lt_left_of_ne_right I J hIJ hμ)
          have hlt : closeDist I K < closeDist I J := by
            simpa [closeDist_comm] using hlt'
          exact lt_of_lt_of_le hlt hdist
        have hKJ_lt : closeDist K J < N := by
          have hlt : closeDist K J < closeDist I J := by
            simpa [hK] using
              (closeDist_mu_lt_right_of_ne_right I J hIJ)
          exact lt_of_lt_of_le hlt hdist
        have hrecIK :=
          ih (closeDist I K) hIK_lt I K le_rfl hIK_ne
        have hrecKJ :=
          ih (closeDist K J) hKJ_lt K J le_rfl hKJ_ne
        rcases hrecIK with ⟨hIK, hKI⟩
        rcases hrecKJ with ⟨hKJ, hJK⟩
        have hK_from_IJ : PairExtFromEndpoints I J K := by
          exact mu_pairExtFromEndpoints I J hIJ
        have hK_from_JI : PairExtFromEndpoints J I K := by
          intro i hi₁ hi₂
          rcases hK_from_IJ i hi₁ hi₂ with hKI | hKJ
          · exact Or.inr hKI
          · exact Or.inl hKJ
        rcases hIK with ⟨p₁, F₁, hF₁, hF₁ep⟩
        rcases hKJ with ⟨p₂, F₂, hF₂, hF₂ep⟩
        have hF₁epIJ : IndexChainUsesOnlyEndpoints I J p₁ F₁ := by
          intro q
          exact
            pairExtFromEndpoints_trans_of_mu
              (I := I) (J := J) (hIJ := hIJ)
              (K := K) (L := F₁ q) hK (hF₁ep q)
        have hF₂epIJ : IndexChainUsesOnlyEndpoints I J p₂ F₂ := by
          intro q
          exact
            pairExtFromEndpoints_trans_of_mu'
              (I := I) (J := J) (hIJ := hIJ)
              (K := K) (L := F₂ q) hK (hF₂ep q)
        have hforw :
            ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain I J p F ∧
              IndexChainUsesOnlyEndpoints I J p F := by
          exact indexCloseChain_append hF₁ hF₂ hF₁epIJ hF₂epIJ
        rcases hJK with ⟨p₃, F₃, hF₃, hF₃ep⟩
        rcases hKI with ⟨p₄, F₄, hF₄, hF₄ep⟩
        have hF₃epJI : IndexChainUsesOnlyEndpoints J I p₃ F₃ := by
          intro q i hi₁ hi₂
          rcases hF₃ep q i hi₁ hi₂ with hJq | hKq
          · exact Or.inl hJq
          · rcases hK_from_JI i hi₁ hi₂ with hKJ | hKI
            · exact Or.inl (hKq.trans hKJ)
            · exact Or.inr (hKq.trans hKI)
        have hF₄epJI : IndexChainUsesOnlyEndpoints J I p₄ F₄ := by
          intro q i hi₁ hi₂
          rcases hF₄ep q i hi₁ hi₂ with hKq | hIq
          · rcases hK_from_JI i hi₁ hi₂ with hKJ | hKI
            · exact Or.inl (hKq.trans hKJ)
            · exact Or.inr (hKq.trans hKI)
          · exact Or.inr hIq
        have hback :
            ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain J I p F ∧
              IndexChainUsesOnlyEndpoints J I p F := by
          exact indexCloseChain_append hF₃ hF₄ hF₃epJI hF₄epJI
        exact ⟨hforw, hback⟩
      · let K : MinorIndex m n t := mu J I hIJ.symm
        have hK : K = mu J I hIJ.symm := rfl
        have hJK_ne : J ≠ K := by
          intro hEq
          have hne : K ≠ J := by
            simpa [hK] using (mu_ne_left J I hIJ.symm)
          exact hne hEq.symm
        have hKI_ne : K ≠ I := by
          simpa [hK] using hμ
        have hJK_lt : closeDist J K < N := by
          have hlt' : closeDist K J < closeDist J I := by
            simpa [hK] using
              (closeDist_mu_lt_left_of_ne_right J I hIJ.symm hμ)
          have hlt : closeDist J K < closeDist I J := by
            simpa [closeDist_comm] using hlt'
          exact lt_of_lt_of_le hlt hdist
        have hKI_lt : closeDist K I < N := by
          have hlt' : closeDist K I < closeDist J I := by
            simpa [hK] using
              (closeDist_mu_lt_right_of_ne_right J I hIJ.symm)
          have hlt : closeDist K I < closeDist I J := by
            simpa [closeDist_comm] using hlt'
          exact lt_of_lt_of_le hlt hdist
        have hrecJK :=
          ih (closeDist J K) hJK_lt J K le_rfl hJK_ne
        have hrecKI :=
          ih (closeDist K I) hKI_lt K I le_rfl hKI_ne
        rcases hrecJK with ⟨hJK, hKJ⟩
        rcases hrecKI with ⟨hKI, hIK⟩
        have hK_from_JI : PairExtFromEndpoints J I K := by
          exact mu_pairExtFromEndpoints J I hIJ.symm
        have hK_from_IJ : PairExtFromEndpoints I J K := by
          intro i hi₁ hi₂
          rcases hK_from_JI i hi₁ hi₂ with hKJ | hKI
          · exact Or.inr hKJ
          · exact Or.inl hKI
        rcases hIK with ⟨p₁, F₁, hF₁, hF₁ep⟩
        rcases hKJ with ⟨p₂, F₂, hF₂, hF₂ep⟩
        have hF₁epIJ : IndexChainUsesOnlyEndpoints I J p₁ F₁ := by
          intro q i hi₁ hi₂
          rcases hF₁ep q i hi₁ hi₂ with hIq | hKq
          · exact Or.inl hIq
          · rcases hK_from_IJ i hi₁ hi₂ with hKI | hKJ
            · exact Or.inl (hKq.trans hKI)
            · exact Or.inr (hKq.trans hKJ)
        have hF₂epIJ : IndexChainUsesOnlyEndpoints I J p₂ F₂ := by
          intro q i hi₁ hi₂
          rcases hF₂ep q i hi₁ hi₂ with hKq | hJq
          · rcases hK_from_IJ i hi₁ hi₂ with hKI | hKJ
            · exact Or.inl (hKq.trans hKI)
            · exact Or.inr (hKq.trans hKJ)
          · exact Or.inr hJq
        have hforw :
            ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain I J p F ∧
              IndexChainUsesOnlyEndpoints I J p F := by
          exact indexCloseChain_append hF₁ hF₂ hF₁epIJ hF₂epIJ
        rcases hJK with ⟨p₃, F₃, hF₃, hF₃ep⟩
        rcases hKI with ⟨p₄, F₄, hF₄, hF₄ep⟩
        have hF₃epJI : IndexChainUsesOnlyEndpoints J I p₃ F₃ := by
          intro q i hi₁ hi₂
          rcases hF₃ep q i hi₁ hi₂ with hJq | hKq
          · exact Or.inl hJq
          · rcases hK_from_JI i hi₁ hi₂ with hKJ | hKI
            · exact Or.inl (hKq.trans hKJ)
            · exact Or.inr (hKq.trans hKI)
        have hF₄epJI : IndexChainUsesOnlyEndpoints J I p₄ F₄ := by
          intro q
          exact
            pairExtFromEndpoints_trans_of_mu'
              (I := J) (J := I) (hIJ := hIJ.symm)
              (K := K) (L := F₄ q) hK (hF₄ep q)
        have hback :
            ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
              IndexCloseChain J I p F ∧
              IndexChainUsesOnlyEndpoints J I p F := by
          exact indexCloseChain_append hF₃ hF₄ hF₃epJI hF₄epJI
        exact ⟨hforw, hback⟩
  exact (hstrong N I J hdist hIJ).1

/-- CGG Prop. 1.5 in index-chain form. -/
theorem exists_indexCloseChain
    (I J : MinorIndex m n t)
    (hIJ : I ≠ J) :
    ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
      IndexCloseChain I J p F ∧
      IndexChainUsesOnlyEndpoints I J p F := by
  simpa using
    (exists_indexCloseChain_aux (m := m) (n := n) (t := t) (N := closeDist I J)
      I J le_rfl hIJ)

end paper1_5

section paper1_5_bridge

variable {m n t : ℕ}
variable {k : Type*} [CommRing k] [Nontrivial k]

/-!
Bridge lemmas from the paper's combinatorial chain (Prop. 1.5)
to the Groebner-basis API (`HasGoodChain`, `AdjacentSmallSPolynomialRep`, etc.).
-/

/-- If every position of `K` comes from one of the two endpoints `I,J`,
then the diagonal exponent of `K` is bounded by the join of the endpoint
diagonal exponents.

This is the key combinatorial-to-monomial bridge extracted from Prop. 1.5. -/
lemma diagExp_le_sup_of_pairExtFromEndpoints
    {I J K : MinorIndex m n t}
    (hK : PairExtFromEndpoints I J K) :
    diagExp K ≤ diagExp I ⊔ diagExp J := by
  change ∀ x, diagExp K x ≤ (diagExp I ⊔ diagExp J) x
  intro x
  rcases x with ⟨a, b⟩
  by_cases hx : ∃ i : Fin t, K.row i = a ∧ K.col i = b
  · rcases hx with ⟨i, hrowKi, hcolKi⟩
    have hi₁ : 1 ≤ i.1 + 1 := by omega
    have hi₂ : i.1 + 1 ≤ t := by
      exact Nat.succ_le_of_lt i.2
    have hpair :
        pairExt K (i.1 + 1) = pairExt I (i.1 + 1) ∨
          pairExt K (i.1 + 1) = pairExt J (i.1 + 1) :=
      hK (i.1 + 1) hi₁ hi₂
    have hrowExtK : rowExt K (i.1 + 1) = (K.row i).1 + 1 := by
      unfold rowExt
      simp [i.2]
    have hcolExtK : colExt K (i.1 + 1) = (K.col i).1 + 1 := by
      unfold colExt
      simp [i.2]
    have hKdiag : diagExp K (a, b) = 1 := by
      rw [diagExp_apply]
      exact if_pos ⟨i, hrowKi, hcolKi⟩
    rcases hpair with hKI | hKJ
    · have hrowExtI : rowExt I (i.1 + 1) = (I.row i).1 + 1 := by
        unfold rowExt
        simp [i.2]
      have hcolExtI : colExt I (i.1 + 1) = (I.col i).1 + 1 := by
        unfold colExt
        simp [i.2]
      have hEqRowExt : rowExt K (i.1 + 1) = rowExt I (i.1 + 1) :=
        congrArg Prod.fst hKI
      have hEqColExt : colExt K (i.1 + 1) = colExt I (i.1 + 1) :=
        congrArg Prod.snd hKI
      have hrowIK : I.row i = K.row i := by
        apply Fin.ext
        rw [hrowExtK, hrowExtI] at hEqRowExt
        omega
      have hcolIK : I.col i = K.col i := by
        apply Fin.ext
        rw [hcolExtK, hcolExtI] at hEqColExt
        omega
      have hIdiag : diagExp I (a, b) = 1 := by
        rw [diagExp_apply]
        refine if_pos ?_
        exact ⟨i, hrowIK.trans hrowKi, hcolIK.trans hcolKi⟩
      rw [hKdiag]
      change 1 ≤ max (diagExp I (a, b)) (diagExp J (a, b))
      rw [hIdiag]
      simp
    · have hrowExtJ : rowExt J (i.1 + 1) = (J.row i).1 + 1 := by
        unfold rowExt
        simp [i.2]
      have hcolExtJ : colExt J (i.1 + 1) = (J.col i).1 + 1 := by
        unfold colExt
        simp [i.2]
      have hEqRowExt : rowExt K (i.1 + 1) = rowExt J (i.1 + 1) :=
        congrArg Prod.fst hKJ
      have hEqColExt : colExt K (i.1 + 1) = colExt J (i.1 + 1) :=
        congrArg Prod.snd hKJ
      have hrowJK : J.row i = K.row i := by
        apply Fin.ext
        rw [hrowExtK, hrowExtJ] at hEqRowExt
        omega
      have hcolJK : J.col i = K.col i := by
        apply Fin.ext
        rw [hcolExtK, hcolExtJ] at hEqColExt
        omega
      have hJdiag : diagExp J (a, b) = 1 := by
        rw [diagExp_apply]
        refine if_pos ?_
        exact ⟨i, hrowJK.trans hrowKi, hcolJK.trans hcolKi⟩
      rw [hKdiag]
      change 1 ≤ max (diagExp I (a, b)) (diagExp J (a, b))
      rw [hJdiag]
      simp
  · have hKzero : diagExp K (a, b) = 0 := by
      rw [diagExp_apply]
      exact if_neg hx
    rw [hKzero]
    exact Nat.zero_le _

/-- Under a diagonal term order, the `headLcm` of two minors is exactly the join
of their diagonal exponent vectors. -/
lemma headLcm_genericMinor_eq_sup_diagExp
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t) :
    headLcm ord (genericMinor (k := k) I) (genericMinor J) =
      diagExp I ⊔ diagExp J := by
  unfold headLcm
  rw [degree_minor_eq_diagExp ord hdiag I,
      degree_minor_eq_diagExp ord hdiag J]

/-- A convenient degree bound once one already knows a diagonal-exponent bound. -/
lemma degree_minor_le_headLcm_of_diagExp_le
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J K : MinorIndex m n t}
    (hdeg : diagExp K ≤ diagExp I ⊔ diagExp J) :
    ord.degree (genericMinor (k := k) K) ≤
      headLcm ord (genericMinor (k := k) I) (genericMinor (k := k) J) := by
  rw [degree_minor_eq_diagExp (k := k) ord hdiag K]
  rw [headLcm_genericMinor_eq_sup_diagExp (k := k) ord hdiag I J]
  exact hdeg

/-- Degree bound for a minor occurring in a Prop. 1.5 chain. -/
lemma degree_minor_le_headLcm_of_pairExtFromEndpoints
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J K : MinorIndex m n t}
    (hK : PairExtFromEndpoints I J K) :
    ord.degree (genericMinor (k := k) K) ≤
      headLcm ord (genericMinor (k := k) I) (genericMinor (k := k) J) := by
  exact degree_minor_le_headLcm_of_diagExp_le
    (k := k) ord hdiag (I := I) (J := J) (K := K)
    (diagExp_le_sup_of_pairExtFromEndpoints hK)

omit [Nontrivial k] in
/-- Every term of an index close-chain gives a generator of `minorSet`. -/
lemma indexCloseChain_term_mem_minorSet
    {p : ℕ}
    {F : Fin (p + 1) → MinorIndex m n t} :
    ∀ q : Fin (p + 1),
      genericMinor (F q) ∈ minorSet (k := k) t := by
  intro q
  exact minor_mem_minorSet (k := k) (F q)

omit [Nontrivial k] in
/-- If every term of an index-chain has degree bounded by the endpoint `headLcm`,
then the supremum of all degrees along the chain is exactly that endpoint `headLcm`
because the two endpoints are themselves present in the chain. -/
lemma indexCloseChain_sup_eq_headLcm_of_degree_le
    (ord : MonomialOrder (Fin m × Fin n))
    {I J : MinorIndex m n t}
    {p : ℕ}
    {F : Fin (p + 1) → MinorIndex m n t}
    (hchain : IndexCloseChain I J p F)
    (hdeg :
      ∀ q : Fin (p + 1),
        ord.degree (genericMinor (k := k) (F q)) ≤
          headLcm ord (genericMinor I) (genericMinor (k := k) J)) :
    Finset.univ.sup (fun q : Fin (p + 1) ↦ ord.degree (genericMinor (k := k) (F q))) =
      headLcm ord (genericMinor I) (genericMinor (k := k) J) := by
  rcases hchain with ⟨h0, hp, _hclose⟩
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro q hq
    exact hdeg q
  · rw [headLcm]
    refine sup_le_iff.mpr ?_
    constructor
    · simpa [h0] using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin (p + 1))))
          (f := fun q : Fin (p + 1) ↦ ord.degree (genericMinor (k := k) (F q)))
          (by simp : (0 : Fin (p + 1)) ∈ (Finset.univ : Finset (Fin (p + 1)))))
    · simpa [hp] using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin (p + 1))))
          (f := fun q : Fin (p + 1) ↦ ord.degree (genericMinor (k := k) (F q)))
          (by
            simp : (⟨p, Nat.lt_succ_self p⟩ : Fin (p + 1)) ∈
              (Finset.univ : Finset (Fin (p + 1)))))

/-- In particular, the degree condition in `HasGoodChain` follows from the endpoint-only
property in Prop. 1.5 together with the diagonal-order degree computation for minors. -/
lemma indexCloseChain_sup_eq_headLcm_of_usesOnlyEndpoints
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    {p : ℕ}
    {F : Fin (p + 1) → MinorIndex m n t}
    (hchain : IndexCloseChain I J p F)
    (huse : IndexChainUsesOnlyEndpoints I J p F) :
    Finset.univ.sup (fun q : Fin (p + 1) ↦ ord.degree (genericMinor (k := k) (F q))) =
      headLcm ord (genericMinor (k := k) I) (genericMinor (k := k) J) := by
  apply indexCloseChain_sup_eq_headLcm_of_degree_le (k := k) (ord := ord) hchain
  intro q
  exact degree_minor_le_headLcm_of_pairExtFromEndpoints ord hdiag (huse q)

omit [Nontrivial k] in
/-- Turn an index-chain into a polynomial good chain, provided the degree-sup equality
and the adjacent small-`S` representations are available. -/
lemma hasGoodChain_of_indexCloseChain
    (ord : MonomialOrder (Fin m × Fin n))
    {I J : MinorIndex m n t}
    {p : ℕ}
    {F : Fin (p + 1) → MinorIndex m n t}
    (hchain : IndexCloseChain I J p F)
    (hsup :
      Finset.univ.sup (fun q : Fin (p + 1) ↦ ord.degree (genericMinor (k := k) (F q))) =
        headLcm ord (genericMinor (k := k) I) (genericMinor (k := k) J))
    (hadj :
      ∀ i : Fin p,
        AdjacentSmallSPolynomialRep
          ord
          (minorSet (m := m) (n := n) (k := k) t)
          (genericMinor (k := k) (F i.castSucc))
          (genericMinor (k := k) (F i.succ))) :
    HasGoodChain
      ord
      (minorSet (m := m) (n := n) (k := k) t)
      (genericMinor (k := k) I)
      (genericMinor (k := k) J) := by
  rcases hchain with ⟨h0, hp, hclose⟩
  refine ⟨p, (fun q ↦ genericMinor (k := k) (F q)), ?_⟩
  refine ⟨by simp [h0], ?_⟩
  refine ⟨by simp [hp], ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q
    exact minor_mem_minorSet (k := k) (F q)
  · simpa using hsup
  · intro i
    exact hadj i

/-- A more convenient packaged version: Prop. 1.5 gives an index-chain,
and Prop. 2.1 (for close pairs) gives the adjacent small-`S` representations;
together they produce a polynomial good chain between the two minors. -/
theorem hasGoodChain_minor_of_prop1_5_closeRep
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    {I J : MinorIndex m n t}
    (h15 :
      ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
        IndexCloseChain I J p F ∧
        IndexChainUsesOnlyEndpoints I J p F)
    (hcloseRep :
      ∀ A B : MinorIndex m n t,
        Close A B →
        AdjacentSmallSPolynomialRep
          ord
          (minorSet (m := m) (n := n) (k := k) t)
          (genericMinor (k := k) A)
          (genericMinor (k := k) B)) :
    HasGoodChain
      ord
      (minorSet (m := m) (n := n) (k := k) t)
      (genericMinor (k := k) I)
      (genericMinor (k := k) J) := by
  rcases h15 with ⟨p, F, hchain, huse⟩
  refine hasGoodChain_of_indexCloseChain (k := k) (ord := ord) (I := I) (J := J)
    (p := p) (F := F) hchain ?_ ?_
  · exact indexCloseChain_sup_eq_headLcm_of_usesOnlyEndpoints
      (k := k) (ord := ord) hdiag hchain huse
  · intro i
    exact hcloseRep _ _ (hchain.2.2 i)

omit [Nontrivial k] in
/-- Reduce the pairwise `HasGoodChain` condition on `minorSet` to the corresponding
statement indexed by `MinorIndex`. -/
lemma pairwise_hasGoodChain_minorSet_of_index
    (ord : MonomialOrder (Fin m × Fin n))
    (hindex :
      ∀ I J : MinorIndex m n t,
        HasGoodChain
          ord
          (minorSet (k := k) t)
          (genericMinor I)
          (genericMinor J)) :
    ∀ f ∈ minorSet t,
      ∀ g ∈ minorSet t,
        HasGoodChain
          ord
          (minorSet (k := k) t)
          f g := by
  intro f hf g hg
  rcases hf with ⟨I, rfl⟩
  rcases hg with ⟨J, rfl⟩
  exact hindex I J

/-- Final bridge to Prop. 1.0:
once one has indexwise good chains for all pairs of minors, the whole minor family is a
Groebner basis of the determinantal ideal. -/
theorem minorSet_isGroebnerBasis_of_diagonal_order_and_indexHasGoodChains
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (hindex :
      ∀ I J : MinorIndex m n t,
        HasGoodChain
          ord
          (minorSet (m := m) (n := n) (k := k) t)
          (genericMinor (k := k) I)
          (genericMinor (k := k) J)) :
    ord.IsGroebnerBasis
      (minorSet (m := m) (n := n) (k := k) t)
      (detIdeal m n t k) := by
  apply isGroebnerBasis_of_pairwise_hasGoodChain
    (ord := ord)
    (G := minorSet (m := m) (n := n) (k := k) t)
    (I := detIdeal m n t k)
  · rfl
  · intro g hg
    rcases hg with ⟨I, rfl⟩
    simpa using leadingCoeff_minor_eq_one (k := k) (ord := ord) hdiag I
  · exact pairwise_hasGoodChain_minorSet_of_index (k := k) (ord := ord) hindex

lemma hasGoodChain_refl_minor
    (ord : MonomialOrder (Fin m × Fin n))
    (I : MinorIndex m n t) :
    HasGoodChain
      ord
      (minorSet (m := m) (n := n) (k := k) t)
      (genericMinor (k := k) I)
      (genericMinor (k := k) I) := by
  sorry

theorem closePair_adjacentSmallSPolynomialRep
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (A B : MinorIndex m n t)
    (hC : Close A B) :
    AdjacentSmallSPolynomialRep
      ord
      (minorSet (m := m) (n := n) (k := k) t)
      (genericMinor (k := k) A)
      (genericMinor (k := k) B) := by
  sorry

/-- The main "paper route" assembly theorem:
from Prop. 1.5 + the close-pair analysis in §2.1, obtain a good chain
between any two minors. -/
theorem minor_hasGoodChain_of_isDiagonalTermOrder
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord)
    (I J : MinorIndex m n t) :
    HasGoodChain
      ord
      (minorSet (m := m) (n := n) (k := k) t)
      (genericMinor (k := k) I)
      (genericMinor (k := k) J) := by
  classical
  by_cases hIJ : I = J
  · -- This case is not the substantive content of the paper:
    -- Prop. 1.5 is stated for distinct endpoints.
    -- So Lean needs a separate trivial self-chain lemma.
    subst hIJ
    exact hasGoodChain_refl_minor ord I
  · -- h15 is exactly Prop. 1.5 in index-chain form.
    have h15 :
        ∃ p : ℕ, ∃ F : Fin (p + 1) → MinorIndex m n t,
          IndexCloseChain I J p F ∧
          IndexChainUsesOnlyEndpoints I J p F := by
      exact exists_indexCloseChain (m := m) (n := n) (t := t) I J hIJ
    rcases h15 with ⟨p, F, hchain, huse⟩
    -- This is the formalization-only bridge:
    -- from the "endpoint-only" property in Prop. 1.5 to the degree/headLcm equality
    -- required by `HasGoodChain`.
    have hsup :
        Finset.univ.sup (fun q : Fin (p + 1) ↦
          ord.degree (genericMinor (k := k) (F q))) =
          headLcm ord (genericMinor I) (genericMinor (k := k) J) := by
      exact
        indexCloseChain_sup_eq_headLcm_of_usesOnlyEndpoints ord hdiag hchain huse
    -- This is the close-pair part of §2.1:
    -- every adjacent pair in the chain is close, hence has the required
    -- small S-polynomial representation.
    have hadj :
        ∀ i : Fin p,
          AdjacentSmallSPolynomialRep
            ord
            (minorSet (m := m) (n := n) (k := k) t)
            (genericMinor (k := k) (F i.castSucc))
            (genericMinor (k := k) (F i.succ)) := by
      intro i
      have hC : Close (F i.castSucc) (F i.succ) := hchain.2.2 i
      exact
        closePair_adjacentSmallSPolynomialRep
          (k := k) (ord := ord) hdiag
          (F i.castSucc) (F i.succ) hC
    -- Final assembly into `HasGoodChain`.
    exact
      hasGoodChain_of_indexCloseChain
        (k := k) (ord := ord)
        (I := I) (J := J)
        (p := p) (F := F)
        hchain hsup hadj

theorem minorSet_isGroebnerBasis_of_isDiagonalTermOrder'
    (ord : MonomialOrder (Fin m × Fin n))
    (hdiag : IsDiagonalTermOrder ord) :
    ord.IsGroebnerBasis
      (minorSet (m := m) (n := n) (k := k) t)
      (detIdeal m n t k) := by
  apply
    minorSet_isGroebnerBasis_of_diagonal_order_and_indexHasGoodChains ord hdiag
  intro I J
  exact minor_hasGoodChain_of_isDiagonalTermOrder ord hdiag I J

end paper1_5_bridge




/-
/-! ## A concrete example -/
/-- rows `[0,2,4,5]`, i.e. paper rows `[1,3,5,6]` -/
def rowI : Fin 4 → Fin 6
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 5

/-- rows `[0,3,4,5]`, i.e. paper rows `[1,4,5,6]` -/
def rowJ : Fin 4 → Fin 6
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 5

/-- cols `[1,3,6,7]`, i.e. paper cols `[2,4,7,8]` -/
def colI : Fin 4 → Fin 8
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 7

/-- cols `[1,3,5,7]`, i.e. paper cols `[2,4,6,8]` -/
def colJ : Fin 4 → Fin 8
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 5
  | ⟨3, _⟩ => 7

def rowIEmb : Fin 4 ↪o Fin 6 where
  toFun := rowI
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [rowI] at h ⊢
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [rowI]

def rowJEmb : Fin 4 ↪o Fin 6 where
  toFun := rowJ
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [rowJ] at h ⊢
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [rowJ]

def colIEmb : Fin 4 ↪o Fin 8 where
  toFun := colI
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [colI] at h ⊢
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [colI]

def colJEmb : Fin 4 ↪o Fin 8 where
  toFun := colJ
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [colJ] at h ⊢
  map_rel_iff' := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [colJ]

def Iex : MinorIndex 6 8 4 :=
  { row := rowIEmb
    col := colIEmb }

def Jex : MinorIndex 6 8 4 :=
  { row := rowJEmb
    col := colJEmb }

/-!
The paper positions are:

I : (1,2), (3,4), (5,7), (6,8)
J : (1,2), (4,4), (5,6), (6,8)

So differences occur exactly at positions 2 and 3.
-/

example : ¬ diffAt Iex Jex 1 := by
  simp [diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : diffAt Iex Jex 2 := by
  simp [diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : diffAt Iex Jex 3 := by
  simp [diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : ¬ diffAt Iex Jex 4 := by
  simp [diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]

noncomputable local instance diffAtDecidablePred {m n t : ℕ} (I J : MinorIndex m n t) :
    DecidablePred (diffAt I J) := by
  intro j
  classical
  unfold diffAt
  infer_instance

/-- Hence the greatest differing position is `3`. -/
example : Nat.findGreatest (diffAt Iex Jex) 4 = 3 := by
  simp [diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : pClose Iex Jex = 3 := by
  simp [pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb, colIEmb, colJEmb, rowI, rowJ, colI, colJ]


noncomputable local instance sPredDecidablePred {m n t : ℕ} (I J : MinorIndex m n t) :
    DecidablePred (sPred I J) := by
  intro j
  classical
  unfold sPred
  infer_instance

example : sPred Iex Jex 0 := by
  simp [sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : sPred Iex Jex 1 := by
  simp [sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : sPred Iex Jex 2 := by
  simp [sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : ¬ sPred Iex Jex 3 := by
  simp [sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : Nat.findGreatest (sPred Iex Jex) (pClose Iex Jex) = 2 := by
  simp [sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : sClose Iex Jex = 2 := by
  simp [sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

noncomputable local instance uPredDecidablePred {m n t : ℕ} (I J : MinorIndex m n t) :
    DecidablePred (uPred I J) := by
  intro k
  classical
  unfold uPred
  infer_instance

example : uPred Iex Jex 3 := by
  simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : uPred Iex Jex 4 := by
  simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : uClose Iex Jex = 3 := by
  have h0 : ¬ uPred Iex Jex 0 := by
    simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have h1 : ¬ uPred Iex Jex 1 := by
    simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have h2 : ¬ uPred Iex Jex 2 := by
    simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have h3 : uPred Iex Jex 3 := by
    simp [uPred, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  classical
  unfold uClose
  letI : DecidablePred (uPred Iex Jex) := fun a =>
    Classical.propDecidable (uPred Iex Jex a)
  split_ifs with h
  · exact (Nat.find_eq_iff (h := h)).2 <| by
      constructor
      · exact h3
      · intro m hm
        interval_cases m
        · exact h0
        · exact h1
        · exact h2
  · exfalso
    exact h ⟨3, h3⟩

/-!
We reuse the previous concrete example:

Iex : rows [0,2,4,5], cols [1,3,6,7]
Jex : rows [0,3,4,5], cols [1,3,5,7]

So in paper coordinates:
Iex = (1,2),(3,4),(5,7),(6,8)
Jex = (1,2),(4,4),(5,6),(6,8)

and we already know:
p = 3, s = 2, u = 3.
-/



/-! ## Verify `muRow` -/

example : muRow Iex Jex ⟨0, by decide⟩ = 0 := by
  simp [muRow, sClose, sPred, rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : muRow Iex Jex ⟨1, by decide⟩ = 2 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : muRow Iex Jex ⟨2, by decide⟩ = 4 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : muRow Iex Jex ⟨3, by decide⟩ = 5 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

/-! ## Verify `muCol` -/

example : muCol Iex Jex ⟨0, by decide⟩ = 1 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : muCol Iex Jex ⟨1, by decide⟩ = 3 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

example : muCol Iex Jex ⟨2, by decide⟩ = 5 := by
  have hs : sClose Iex Jex = 2 := by
    simp [sClose, sPred, rowExt, colExt,
      pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
      colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
            diffAt, Iex, Jex, rowIEmb, rowJEmb,
            colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;>
            simp [uPred, sClose, sPred, rowExt, colExt, pClose,
              diffAt, Iex, Jex, rowIEmb, rowJEmb,
              colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by
        simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
          colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muCol, hs, hu]
  rfl


example : muCol Iex Jex ⟨3, by decide⟩ = 7 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

/-! ## Strict monotonicity of the concrete `muRow` / `muCol` -/

lemma muRow_Iex_Jex_strictMono : StrictMono (muRow Iex Jex) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp [muRow, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]

lemma muCol_Iex_Jex_strictMono : StrictMono (muCol Iex Jex) := by
  intro a b hab
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;> simp [uPred, sClose, sPred,
           rowExt, colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by simp [uPred, sClose, sPred, rowExt,
       colExt, pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  fin_cases a <;> fin_cases b <;> simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk,
    Fin.reduceLT, gt_iff_lt] at hab ⊢
  · simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp only [muCol, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, hs,
    Nat.one_le_ofNat, ↓reduceIte, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff, hu, le_refl]
    exact Fin.coe_sub_iff_lt.mp rfl
  · simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp only [muCol, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.reduceAdd, hs, le_refl,
    ↓reduceIte, Nat.reduceMod, Nat.reduceLeDiff, hu]
    exact Fin.coe_sub_iff_lt.mp rfl
  · simp [muCol, sClose, sPred, rowExt, colExt, pClose,
  diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  · simp only [muCol, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, hs,
    Nat.reduceLeDiff, ↓reduceIte, hu, le_refl, Nat.mod_succ]
    exact Fin.coe_sub_iff_lt.mp rfl

/-- The concrete `mu(Iex,Jex)` packages the expected row/column data. -/
noncomputable def muEx : MinorIndex 6 8 4 :=
  mu Iex Jex muRow_Iex_Jex_strictMono muCol_Iex_Jex_strictMono

example : muEx.row ⟨0, by decide⟩ = 0 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  simp [muEx, mu, strictMonoToOrderEmbedding, muRow, hs]
  rfl

example : muEx.row ⟨1, by decide⟩ = 2 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  simp [muEx, mu, strictMonoToOrderEmbedding, muRow, hs]
  rfl

example : muEx.row ⟨2, by decide⟩ = 4 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
            diffAt, Iex, Jex, rowIEmb, rowJEmb,
            colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;>
            simp [uPred, sClose, sPred, rowExt, colExt, pClose,
              diffAt, Iex, Jex, rowIEmb, rowJEmb,
              colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by
        simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
          colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muEx, mu, strictMonoToOrderEmbedding, muRow, hs, hu]
  rfl

example : muEx.row ⟨3, by decide⟩ = 5 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
            diffAt, Iex, Jex, rowIEmb, rowJEmb,
            colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;>
            simp [uPred, sClose, sPred, rowExt, colExt, pClose,
              diffAt, Iex, Jex, rowIEmb, rowJEmb,
              colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by
        simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
          colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muEx, mu, strictMonoToOrderEmbedding, muRow, hs, hu]
  rfl

example : muEx.col ⟨0, by decide⟩ = 1 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  simp [muEx, mu, strictMonoToOrderEmbedding, muCol, hs]
  rfl

example : muEx.col ⟨1, by decide⟩ = 3 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  simp [muEx, mu, strictMonoToOrderEmbedding, muCol, hs,]
  rfl

example : muEx.col ⟨2, by decide⟩ = 5 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
            diffAt, Iex, Jex, rowIEmb, rowJEmb,
            colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;>
            simp [uPred, sClose, sPred, rowExt, colExt, pClose,
              diffAt, Iex, Jex, rowIEmb, rowJEmb,
              colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by
        simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
          colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muEx, mu, strictMonoToOrderEmbedding, muCol, hs, hu]
  rfl

example : muEx.col ⟨3, by decide⟩ = 7 := by
  have hs : sClose Iex Jex = 2 := by simp [sClose, sPred, rowExt, colExt,
  pClose, diffAt, Iex, Jex, rowIEmb, rowJEmb,
  colIEmb, colJEmb, rowI, rowJ, colI, colJ]
  have hu : uClose Iex Jex = 3 := by
    classical
    unfold uClose
    letI : DecidablePred (uPred Iex Jex) := fun a =>
      Classical.propDecidable (uPred Iex Jex a)
    split_ifs with h
    · exact (Nat.find_eq_iff (h := h)).2 <| by
        constructor
        · simp [uPred, sClose, sPred, rowExt, colExt, pClose,
            diffAt, Iex, Jex, rowIEmb, rowJEmb,
            colIEmb, colJEmb, rowI, rowJ, colI, colJ]
        · intro m hm
          interval_cases m <;>
            simp [uPred, sClose, sPred, rowExt, colExt, pClose,
              diffAt, Iex, Jex, rowIEmb, rowJEmb,
              colIEmb, colJEmb, rowI, rowJ, colI, colJ]
    · exfalso
      exact h ⟨3, by
        simp [uPred, sClose, sPred, rowExt, colExt, pClose,
          diffAt, Iex, Jex, rowIEmb, rowJEmb,
          colIEmb, colJEmb, rowI, rowJ, colI, colJ]⟩
  simp [muEx, mu, strictMonoToOrderEmbedding, muCol, hs, hu]
  rfl
-/







end Determinantal
