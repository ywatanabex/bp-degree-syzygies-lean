import BPFixedPoints.Incidence.IncidenceUniversalKoszulFaces

/-! # Regular sequences are Koszul-regular; exactness of `K_G` on charts from regularity

This file proves the algebraic fact behind the chart exactness of the universal Koszul complex,
in the form of Stacks Tag 062F, and applies it to the existing regular sequences of chart
equations.

* **Koszul complexes on edge subsets.** `koszulDiffOn s f = Σ_{e ∈ s} f_e · erase e` on the total
  exterior module `Koszul.Space E A`, and `KoszulSuppIn s k z` (support on `k`-element subsets of
  `s`). The exterior multiplication `Koszul.insert a` splits off a new edge `a ∉ s`
  (`koszulDiffOn_insert_decomp`), and the degree-zero image of `koszulDiffOn s f` is the ideal of
  the `f_e`, `e ∈ s` (`mem_span_iff_koszulDiffOn`).
* **Stacks 062F.** If the `f_e`, listed along a duplicate-free list `l`, form a weakly regular
  sequence (`RingTheory.Sequence.IsWeaklyRegular`), the Koszul complex of the `f_e`, `e ∈ l`, is
  exact in every positive degree (`koszulDiffOn_exact_of_isWeaklyRegular`, by induction on the
  list); for a list of all edges this is exactness of the graded Koszul complex
  (`gradedKoszul_exact_of_isWeaklyRegular`). No order on the list is needed.
* **Charts.** With the regular chart equations `incidenceProjectiveEquation σ`
  (`incidenceProjectiveEquationList_isRegular`) and the chart frame of `K_G`
  (`incUniversalKoszul_chart`), `K_G` is exact in every positive homological degree on every chart
  (`incUniversalKoszul_chart_exact_of_regular`); this gives the chart case of
  `incUniversalKoszul_face_exact` independently of the face contraction.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CechProduct ProjectiveLine RingTheory.Sequence

set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

/-! ### Regular sequences are Koszul-regular -/

section Regular

variable {E : Type} [LinearOrder E] [Fintype E] {A : Type*} [CommRing A]

/-- The Koszul differential of the `f_e` with `e` in a finite edge set `s`. -/
noncomputable def koszulDiffOn (s : Finset E) (f : E → A) : Module.End A (Koszul.Space E A) :=
  ∑ e ∈ s, f e • Koszul.erase e

/-- An element of the total exterior module is supported on `k`-element subsets of `s`. -/
def KoszulSuppIn (s : Finset E) (k : ℕ) (z : Koszul.Space E A) : Prop :=
  ∀ T, z T ≠ 0 → T ⊆ s ∧ T.card = k

/-- The exterior multiplication `insert a` evaluated at a subset `T`. -/
theorem koszul_insert_apply (a : E) (w : Koszul.Space E A) (T : Finset E) :
    Koszul.insert a w T = if a ∈ T then Koszul.sign (T.erase a) a * w (T.erase a) else 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    split_ifs <;> ring
  | single S c =>
    rw [Koszul.insert_single]
    by_cases haS : a ∈ S
    · rw [ite_eq_left haS, Finsupp.coe_zero, Pi.zero_apply]
      by_cases haT : a ∈ T
      · rw [ite_eq_left haT, Finsupp.single_apply, ite_eq_right, mul_zero]
        intro h
        rw [h] at haS
        exact Finset.notMem_erase a T haS
      · rw [ite_eq_right haT]
    · rw [ite_eq_right haS, Finsupp.single_apply]
      by_cases hT : insert a S = T
      · subst hT
        rw [ite_eq_left rfl, ite_eq_left (Finset.mem_insert_self a S),
          Finset.erase_insert haS, Finsupp.single_eq_same]
      · rw [ite_eq_right hT]
        by_cases haT : a ∈ T
        · rw [ite_eq_left haT, Finsupp.single_apply, ite_eq_right, mul_zero]
          intro h
          apply hT
          rw [h, Finset.insert_erase haT]
        · rw [ite_eq_right haT]

/-- Contraction with an edge outside `s` kills elements supported on subsets of `s`. -/
theorem koszul_erase_eq_zero_of_suppIn {s : Finset E} {a : E} (ha : a ∉ s) {k : ℕ}
    {z : Koszul.Space E A} (hz : KoszulSuppIn s k z) : Koszul.erase a z = 0 := by
  ext T
  rw [koszul_erase_apply, Finsupp.coe_zero, Pi.zero_apply]
  by_cases haT : a ∉ T
  · rw [ite_eq_left haT]
    by_cases h : z (insert a T) = 0
    · rw [h, mul_zero]
    · exact (ha ((hz _ h).1 (Finset.mem_insert_self a T))).elim
  · rw [ite_eq_right haT]

/-- `erase a ∘ insert a` is the identity on elements killed by `erase a`. -/
theorem koszul_erase_insert_of_erase_eq_zero (a : E) {w : Koszul.Space E A}
    (hw : Koszul.erase a w = 0) : Koszul.erase a (Koszul.insert a w) = w := by
  have h := LinearMap.congr_fun (Koszul.erase_insert_add_insert_erase (A := A) a a) w
  simp only [ite_true, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply, hw,
    map_zero, add_zero] at h
  exact h

/-- The Koszul differential on `s` anticommutes with exterior multiplication by an edge outside
`s`. -/
theorem koszulDiffOn_insert {s : Finset E} {a : E} (ha : a ∉ s) (f : E → A)
    (w : Koszul.Space E A) :
    koszulDiffOn s f (Koszul.insert a w) = -Koszul.insert a (koszulDiffOn s f w) := by
  simp only [koszulDiffOn, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  have hea : e ≠ a := fun h => ha (h ▸ he)
  have h := LinearMap.congr_fun (Koszul.erase_insert_add_insert_erase (A := A) e a) w
  simp only [hea, ite_false, LinearMap.add_apply, Module.End.mul_apply,
    LinearMap.zero_apply] at h
  rw [eq_neg_of_add_eq_zero_left h, smul_neg]

/-- The Koszul differential on `insert a s`. -/
theorem koszulDiffOn_insert_set {s : Finset E} {a : E} (ha : a ∉ s) (f : E → A) :
    koszulDiffOn (insert a s) f = koszulDiffOn s f + f a • Koszul.erase a := by
  rw [koszulDiffOn, Finset.sum_insert ha, add_comm]
  rfl

/-- The Koszul differential on `s` lowers the degree of elements supported in `s`. -/
theorem koszulDiffOn_suppIn {s : Finset E} (f : E → A) {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn s (k + 1) z) : KoszulSuppIn s k (koszulDiffOn s f z) := by
  intro T hT
  simp only [koszulDiffOn, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, koszul_erase_apply] at hT
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  by_cases heT : e ∉ T
  · rw [ite_eq_left heT] at he
    have hz' := hz (insert e T) (fun h => he (by rw [h, mul_zero, mul_zero]))
    refine ⟨(Finset.subset_insert e T).trans hz'.1, ?_⟩
    have := hz'.2
    rw [Finset.card_insert_of_notMem heT] at this
    omega
  · rw [ite_eq_right heT, mul_zero] at he
    exact (he rfl).elim

/-- The contraction `erase a` maps elements supported in `insert a s` to elements supported in
`s`, lowering the degree. -/
theorem koszul_erase_suppIn {s : Finset E} {a : E} {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn (insert a s) (k + 1) z) : KoszulSuppIn s k (Koszul.erase a z) := by
  intro T hT
  rw [koszul_erase_apply] at hT
  by_cases haT : a ∉ T
  · rw [ite_eq_left haT] at hT
    have hz' := hz (insert a T) (fun h => hT (by rw [h, mul_zero]))
    refine ⟨fun x hx => ?_, ?_⟩
    · have hx' := hz'.1 (Finset.mem_insert_of_mem hx)
      rcases Finset.mem_insert.mp hx' with h | h
      · exact (haT (h ▸ hx)).elim
      · exact h
    · have := hz'.2
      rw [Finset.card_insert_of_notMem haT] at this
      omega
  · rw [ite_eq_right haT] at hT
    exact (hT rfl).elim

/-- The part of an element supported in `insert a s` away from `a` is supported in `s`. -/
theorem koszul_erase_insert_suppIn {s : Finset E} {a : E} {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn (insert a s) k z) :
    KoszulSuppIn s k (Koszul.erase a (Koszul.insert a z)) := by
  intro T hT
  rw [koszul_erase_apply] at hT
  by_cases haT : a ∉ T
  · rw [ite_eq_left haT, koszul_insert_apply, ite_eq_left (Finset.mem_insert_self a T),
      Finset.erase_insert haT] at hT
    have hz' := hz T (fun h => hT (by rw [h, mul_zero, mul_zero]))
    refine ⟨fun x hx => ?_, hz'.2⟩
    rcases Finset.mem_insert.mp (hz'.1 hx) with h | h
    · exact (haT (h ▸ hx)).elim
    · exact h
  · rw [ite_eq_right haT] at hT
    exact (hT rfl).elim

/-- Exterior multiplication by `a` maps elements supported in `s` to elements supported in
`insert a s`, raising the degree. -/
theorem koszul_insert_suppIn {s : Finset E} {a : E} {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn s k z) : KoszulSuppIn (insert a s) (k + 1) (Koszul.insert a z) := by
  intro T hT
  rw [koszul_insert_apply] at hT
  by_cases haT : a ∈ T
  · rw [ite_eq_left haT] at hT
    have hz' := hz (T.erase a) (fun h => hT (by rw [h, mul_zero]))
    refine ⟨fun x hx => ?_, ?_⟩
    · by_cases hxa : x = a
      · exact hxa ▸ Finset.mem_insert_self a s
      · exact Finset.mem_insert_of_mem (hz'.1 (Finset.mem_erase.mpr ⟨hxa, hx⟩))
    · have := hz'.2
      rw [Finset.card_erase_of_mem haT] at this
      have h1 : 1 ≤ T.card := Finset.card_pos.mpr ⟨a, haT⟩
      omega
  · rw [ite_eq_right haT] at hT
    exact (hT rfl).elim

theorem koszulSuppIn_zero {s : Finset E} {k : ℕ} : KoszulSuppIn s k (0 : Koszul.Space E A) :=
  fun _ h => (h rfl).elim

theorem koszulSuppIn_add {s : Finset E} {k : ℕ} {z w : Koszul.Space E A}
    (hz : KoszulSuppIn s k z) (hw : KoszulSuppIn s k w) : KoszulSuppIn s k (z + w) := by
  intro T hT
  rw [Finsupp.add_apply] at hT
  by_cases h : z T = 0
  · rw [h, zero_add] at hT
    exact hw T hT
  · exact hz T h

theorem koszulSuppIn_neg {s : Finset E} {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn s k z) : KoszulSuppIn s k (-z) := by
  intro T hT
  rw [Finsupp.neg_apply, neg_ne_zero] at hT
  exact hz T hT

theorem koszulSuppIn_smul {s : Finset E} {k : ℕ} (c : A) {z : Koszul.Space E A}
    (hz : KoszulSuppIn s k z) : KoszulSuppIn s k (c • z) := by
  intro T hT
  rw [Finsupp.smul_apply] at hT
  by_cases h : z T = 0
  · rw [h, smul_zero] at hT
    exact (hT rfl).elim
  · exact hz T h

/-- The empty-set coefficient of the Koszul differential on `s`. -/
theorem koszulDiffOn_apply_empty (s : Finset E) (f : E → A) (u : Koszul.Space E A) :
    koszulDiffOn s f u ∅ = ∑ e ∈ s, f e * u {e} := by
  simp only [koszulDiffOn, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, koszul_erase_apply,
    Finset.notMem_empty, not_false_eq_true, ite_true]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hs : Koszul.sign (A := A) (∅ : Finset E) e = 1 := by
    simp [Koszul.sign, Koszul.index]
  rw [hs, one_mul]
  rfl

/-- **The degree-zero image is the ideal.** An element `c` lies in the ideal generated by the
`f_e`, `e ∈ s`, exactly when `c` is the empty-set coefficient of the Koszul differential of an
element supported on one-element subsets of `s`. -/
theorem mem_span_iff_koszulDiffOn (s : Finset E) (f : E → A) (c : A) :
    c ∈ Ideal.span (f '' (s : Set E)) ↔
      ∃ u, KoszulSuppIn s 1 u ∧ koszulDiffOn s f u ∅ = c := by
  constructor
  · intro hc
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination A).mp hc
    let u : Koszul.Space E A := ∑ e ∈ s, Finsupp.single {e} (l e)
    have hu : ∀ e' ∈ s, u {e'} = l e' := by
      intro e' he'
      simp only [u, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
        Finset.singleton_inj]
      rw [Finset.sum_ite_eq' s e' (fun e => l e), ite_eq_left he']
    refine ⟨u, ?_, ?_⟩
    · intro T hT
      simp only [u, Finsupp.coe_finsetSum, Finset.sum_apply] at hT
      obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
      rw [Finsupp.single_apply] at hne
      by_cases hT' : {e} = T
      · subst hT'
        exact ⟨Finset.singleton_subset_iff.mpr he, Finset.card_singleton e⟩
      · rw [ite_eq_right hT'] at hne
        exact (hne rfl).elim
    · rw [koszulDiffOn_apply_empty, Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset l hl]
      · refine Finset.sum_congr rfl fun e he => ?_
        rw [hu e he, smul_eq_mul, mul_comm]
      · intro e _
        rw [zero_smul]
  · rintro ⟨u, -, rfl⟩
    rw [koszulDiffOn_apply_empty]
    exact Ideal.sum_mem _ fun e he =>
      Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e, he, rfl⟩)

/-- Support in `s` implies support in any larger edge set. -/
theorem KoszulSuppIn.mono {s t : Finset E} (hst : s ⊆ t) {k : ℕ} {z : Koszul.Space E A}
    (hz : KoszulSuppIn s k z) : KoszulSuppIn t k z :=
  fun T hT => ⟨(hz T hT).1.trans hst, (hz T hT).2⟩

/-- An element supported on the empty subset is determined by its empty-set coefficient. -/
theorem koszulSuppIn_zero_ext {s : Finset E} {x y : Koszul.Space E A}
    (hx : KoszulSuppIn s 0 x) (hy : KoszulSuppIn s 0 y) (h : x ∅ = y ∅) : x = y := by
  ext T
  by_cases hT : T = ∅
  · subst hT
    exact h
  · have hx' : x T = 0 := by
      by_contra hne
      exact hT (Finset.card_eq_zero.mp (hx T hne).2)
    have hy' : y T = 0 := by
      by_contra hne
      exact hT (Finset.card_eq_zero.mp (hy T hne).2)
    rw [hx', hy']

/-- Contraction with `a` anticommutes with the Koszul differential on `s`. -/
theorem koszul_erase_koszulDiffOn (s : Finset E) (f : E → A) (a : E) (y : Koszul.Space E A) :
    Koszul.erase a (koszulDiffOn s f y) = -koszulDiffOn s f (Koszul.erase a y) := by
  simp only [koszulDiffOn, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h := LinearMap.congr_fun (Koszul.erase_anticomm (A := A) a e) y
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
  rw [h, smul_neg]

/-- **The Koszul differential on `insert a s`, decomposed.** For `z₀` and `w` supported in `s`
(with `a ∉ s`), `d(z₀ + e_a ∧ w) = (d_s z₀ + f_a w) - e_a ∧ d_s w`. -/
theorem koszulDiffOn_insert_decomp {s : Finset E} {a : E} (ha : a ∉ s) (f : E → A) {m n : ℕ}
    {z₀ w : Koszul.Space E A} (hz₀ : KoszulSuppIn s m z₀) (hw : KoszulSuppIn s n w) :
    koszulDiffOn (insert a s) f (z₀ + Koszul.insert a w) =
      (koszulDiffOn s f z₀ + f a • w) - Koszul.insert a (koszulDiffOn s f w) := by
  rw [koszulDiffOn_insert_set ha, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_add,
    koszulDiffOn_insert ha, koszul_erase_eq_zero_of_suppIn ha hz₀,
    koszul_erase_insert_of_erase_eq_zero a (koszul_erase_eq_zero_of_suppIn ha hw)]
  abel_nf

/-- The nonzerodivisor condition of a weakly regular sequence, for the last element. -/
theorem mul_mem_span_of_isSMulRegular {l : List E} (f : E → A) (a : E)
    (h : IsSMulRegular (A ⧸ (Ideal.ofList (l.map f) • ⊤ : Submodule A A)) (f a)) (c : A)
    (hc : f a * c ∈ Ideal.span (f '' (l.toFinset : Set E))) :
    c ∈ Ideal.span (f '' (l.toFinset : Set E)) := by
  have hI : (Ideal.ofList (l.map f) • ⊤ : Submodule A A) = Ideal.span (f '' (l.toFinset : Set E)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList]
    congr 1
    ext r
    simp
  rw [hI] at h
  have h0 : f a • (Submodule.Quotient.mk c : A ⧸ Ideal.span (f '' (l.toFinset : Set E))) =
      f a • (0 : A ⧸ Ideal.span (f '' (l.toFinset : Set E))) := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Submodule.Quotient.mk_eq_zero]
    exact hc
  have := h h0
  exact (Submodule.Quotient.mk_eq_zero _).mp this

/-- **A weakly regular sequence is Koszul-regular** (Stacks, Tag 062F). If the `f_e`, listed along
a duplicate-free list `l` of edges, form a weakly regular sequence in `A`, then the Koszul complex
of the `f_e`, `e ∈ l`, is exact in every positive degree. The proof is the usual induction on the
length, splitting off the last element. -/
theorem koszulDiffOn_exact_of_isWeaklyRegular (f : E → A) (l : List E) (hl : l.Nodup)
    (hreg : IsWeaklyRegular A (l.map f)) (k : ℕ) (z : Koszul.Space E A)
    (hz : KoszulSuppIn l.toFinset (k + 1) z) (hdz : koszulDiffOn l.toFinset f z = 0) :
    ∃ y, KoszulSuppIn l.toFinset (k + 2) y ∧ koszulDiffOn l.toFinset f y = z := by
  induction l using List.reverseRecOn generalizing k z with
  | nil =>
    refine ⟨0, koszulSuppIn_zero, ?_⟩
    have hz0 : z = 0 := by
      ext T
      by_contra h
      have hT := hz T h
      have hT0 : T = ∅ := Finset.subset_empty.mp (by simpa using hT.1)
      have := hT.2
      rw [hT0, Finset.card_empty] at this
      omega
    rw [map_zero, hz0]
  | append_singleton l a ih =>
    have hnd : l.Nodup := (List.nodup_append.mp hl).1
    have ha : a ∉ l.toFinset := by
      intro h
      exact (List.nodup_append.mp hl).2.2 a (List.mem_toFinset.mp h) a
        (List.mem_singleton_self a) rfl
    have hset : (l ++ [a]).toFinset = insert a l.toFinset := by
      ext x
      simp
    rw [List.map_append, List.map_singleton] at hreg
    obtain ⟨hregl, hlast⟩ := (isWeaklyRegular_append_iff A _ _).mp hreg
    rw [isWeaklyRegular_singleton_iff] at hlast
    have hregc := mul_mem_span_of_isSMulRegular f a hlast
    rw [hset] at hz hdz ⊢
    set s := l.toFinset with hs
    let w := Koszul.erase a z
    let z₀ := Koszul.erase a (Koszul.insert a z)
    have hzdec : z = z₀ + Koszul.insert a w := by
      have h := LinearMap.congr_fun (Koszul.erase_insert_add_insert_erase (A := A) a a) z
      simp only [ite_true, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h
      exact h.symm
    have hw : KoszulSuppIn s k w := koszul_erase_suppIn hz
    have hz₀ : KoszulSuppIn s (k + 1) z₀ := koszul_erase_insert_suppIn hz
    rw [hzdec, koszulDiffOn_insert_decomp ha f hz₀ hw] at hdz
    -- Separate the parts with and without `a`.
    have hdw : koszulDiffOn s f w = 0 := by
      have h := congrArg (Koszul.erase a) hdz
      rw [map_sub, map_zero, koszul_erase_insert_of_erase_eq_zero a
        (by rw [koszul_erase_koszulDiffOn, koszul_erase_eq_zero_of_suppIn ha hw, map_zero,
          neg_zero])] at h
      have h0 : Koszul.erase a (koszulDiffOn s f z₀ + f a • w) = 0 := by
        rw [map_add, map_smul, koszul_erase_koszulDiffOn,
          koszul_erase_eq_zero_of_suppIn ha hz₀, koszul_erase_eq_zero_of_suppIn ha hw, map_zero,
          neg_zero, smul_zero, add_zero]
      rw [h0, zero_sub, neg_eq_zero] at h
      exact h
    have hcyc : koszulDiffOn s f z₀ + f a • w = 0 := by
      rw [hdw, map_zero, sub_zero] at hdz
      exact hdz
    -- `w` is a boundary.
    have hu : ∃ u, KoszulSuppIn s (k + 1) u ∧ koszulDiffOn s f u = w := by
      cases k with
      | zero =>
        have hmem : f a * w ∅ ∈ Ideal.span (f '' (s : Set E)) := by
          have h := congrArg (fun x : Koszul.Space E A => x ∅) hcyc
          simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
            Finsupp.coe_zero, Pi.zero_apply] at h
          rw [eq_neg_of_add_eq_zero_right h]
          exact neg_mem ((mem_span_iff_koszulDiffOn s f _).mpr ⟨z₀, hz₀, rfl⟩)
        obtain ⟨u, hu1, hu2⟩ := (mem_span_iff_koszulDiffOn s f _).mp (hregc _ hmem)
        exact ⟨u, hu1, koszulSuppIn_zero_ext (koszulDiffOn_suppIn f hu1) hw hu2⟩
      | succ k' =>
        exact ih hnd hregl k' w hw hdw
    obtain ⟨u, hu1, hu2⟩ := hu
    have hcyc' : koszulDiffOn s f (z₀ + f a • u) = 0 := by
      rw [map_add, map_smul, hu2, hcyc]
    obtain ⟨v, hv1, hv2⟩ := ih hnd hregl k (z₀ + f a • u)
      (koszulSuppIn_add hz₀ (koszulSuppIn_smul _ hu1)) hcyc'
    refine ⟨v + Koszul.insert a (-u), koszulSuppIn_add (hv1.mono (Finset.subset_insert a s))
      (koszul_insert_suppIn (koszulSuppIn_neg hu1)), ?_⟩
    rw [koszulDiffOn_insert_decomp ha f hv1 (koszulSuppIn_neg hu1), hv2, map_neg, hu2,
      map_neg, smul_neg, hzdec]
    abel

/-- **Koszul-regularity of the graded Koszul complex.** If the `f_e`, listed along a
duplicate-free list containing every edge, form a weakly regular sequence, the graded Koszul
complex of `f` is exact in every positive degree. -/
theorem gradedKoszul_exact_of_isWeaklyRegular (f : E → A) (l : List E) (hl : l.Nodup)
    (hcov : ∀ e, e ∈ l) (hreg : IsWeaklyRegular A (l.map f)) (k : ℕ)
    (y : Set.powersetCard E (k + 1) → A) (hy : gradedKoszul f k y = 0) :
    ∃ y', gradedKoszul f (k + 1) y' = y := by
  have huniv : l.toFinset = Finset.univ := by
    ext e
    simp [hcov e]
  have hd : koszulDiffOn l.toFinset f = Koszul.differential f := by
    rw [huniv]
    rfl
  have hz : KoszulSuppIn l.toFinset (k + 1) (koszulEmbed (k + 1) y) := by
    intro T hT
    rw [koszulEmbed_apply] at hT
    by_cases h : T.card = k + 1
    · exact ⟨by rw [huniv]; exact Finset.subset_univ T, h⟩
    · rw [dite_eq_right h] at hT
      exact (hT rfl).elim
  have hdz : koszulDiffOn l.toFinset f (koszulEmbed (k + 1) y) = 0 := by
    rw [hd, koszul_differential_embed, hy, map_zero]
  obtain ⟨y0, -, hy0⟩ := koszulDiffOn_exact_of_isWeaklyRegular f l hl hreg k _ hz hdz
  refine ⟨koszulProj (k + 2) y0, ?_⟩
  rw [← koszulProj_differential, ← hd, hy0, koszulProj_koszulEmbed]

end Regular

/-! ### Exactness of `K_G` on charts from the regular sequence of chart equations -/

section Charts

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- **Exactness of `K_G` on a chart from the regular chart equations.** On the chart `σ` (the face
open of `chartFace σ`), a section of `∧^{k+1} F_G^∨` killed by the differential of `K_G` is a
boundary. The proof uses only that the chart equations `incidenceProjectiveEquation σ` form a
regular sequence in `MvPolynomial V S_G` (`incidenceProjectiveEquationList_isRegular`), that a
regular sequence is Koszul-regular (`gradedKoszul_exact_of_isWeaklyRegular`, Stacks 062F), and that
the chart sections of `K_G` are the Koszul complex of the chart equations
(`incUniversalKoszul_chart`). -/
theorem incUniversalKoszul_chart_exact_of_regular (k : ℕ) (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) (k + 1),
      univFaceOpen (IncCoeffRing E) V (chartFace σ)))
    (hx : ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X k).val.app
      (op _)).hom x = 0) :
    ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) (k + 2),
        univFaceOpen (IncCoeffRing E) V (chartFace σ)),
      ((G.univKoszulDifferential (R := IncCoeffRing E) MvPolynomial.X (k + 1)).val.app
        (op _)).hom y = x := by
  have hy : gradedKoszul (G.incidenceProjectiveEquation σ) k
      (G.incUnivChartKoszulEquiv (k + 1) σ x) = 0 := by
    rw [← incUniversalKoszul_chart, hx]
    exact (G.incUnivChartKoszulEquiv k σ).map_zero
  obtain ⟨y', hy'⟩ := gradedKoszul_exact_of_isWeaklyRegular (G.incidenceProjectiveEquation σ)
    (Finset.univ : Finset E).toList (Finset.nodup_toList _)
    (fun e => Finset.mem_toList.mpr (Finset.mem_univ e))
    (G.incidenceProjectiveEquationList_isRegular σ).toIsWeaklyRegular k _ hy
  refine ⟨(G.incUnivChartKoszulEquiv (k + 2) σ).symm y', ?_⟩
  apply (G.incUnivChartKoszulEquiv (k + 1) σ).injective
  rw [incUniversalKoszul_chart, AddEquiv.apply_symm_apply, hy']

end Charts

end BPFixedPoints.Multigraph
