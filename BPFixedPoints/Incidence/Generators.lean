import BPFixedPoints.Incidence.StateCohomology

/-!
# Module generators and real sectors: combinatorial part of `alg:generator-real-bridge`

The paper states Σ_q β_{0,q}=#{collections of vertex-disjoint simple cycles,
including empty}≤2^ν, with equality iff edge-disjoint simple cycles are
vertex-disjoint; maximum degree at most three suffices.
`IsSimpleCycle C` is a nonempty minimal Eulerian edge set, including cycles
of two parallel edges. `IsSimpleCycle.deg` gives degrees zero or two using
cycle-space dimension one and the handshake identity.
`IsCycleUnion S` means degrees zero or two. `betti_zero_eq_card` counts these
by edge size q. The union map bijects vertex-disjoint cycle collections and
cycle unions (`card_cycleCollections`).
`sum_betti_zero_le`, `sum_betti_zero_eq_iff` and `sum_betti_zero_eq_of_deg_le_three`
prove the bound, equality criterion and degree-three case.
`Paper.lean` combines equality with `Real/Count.lean` to identify this count
with the minimum real-root count over fields for fixed nonzero real couplings.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-! ### Degree lemmas -/

theorem deg_union_of_disjoint {S T : Finset E} (h : Disjoint S T) (v : V) :
    G.deg (S ∪ T) v = G.deg S v + G.deg T v := by
  unfold deg
  rw [Finset.sum_union h]

theorem deg_sdiff_add {S T : Finset E} (h : T ⊆ S) (v : V) :
    G.deg (S \ T) v + G.deg T v = G.deg S v := by
  rw [← G.deg_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

theorem mem_support_iff {S : Finset E} {v : V} : v ∈ G.support S ↔ 0 < G.deg S v := by
  simp [support]

/-- An endpoint belongs to the support of any edge set containing that edge. -/
theorem fst_mem_support {S : Finset E} {e : E} (he : e ∈ S) : G.fst e ∈ G.support S := by
  rw [mem_support_iff]
  have h1 : 1 ≤ G.endCount e (G.fst e) := by simp [endCount]
  have h2 := Finset.single_le_sum (f := fun e' => G.endCount e' (G.fst e))
    (fun _ _ => Nat.zero_le _) he
  show 0 < ∑ x ∈ S, G.endCount x (G.fst e)
  omega

theorem mem_support_of_incident {S : Finset E} {e : E} (he : e ∈ S) {v : V}
    (hv : G.Incident e v) : v ∈ G.support S := by
  rw [mem_support_iff]
  have h1 : 1 ≤ G.endCount e v := by
    have := (G.endCount_eq_zero_iff e v).not.2 (not_not.2 hv); omega
  have h2 := Finset.single_le_sum (f := fun e' => G.endCount e' v)
    (fun _ _ => Nat.zero_le _) he
  show 0 < ∑ x ∈ S, G.endCount x v
  omega

theorem isEvenSet_union {S T : Finset E} (h : Disjoint S T) (hS : G.IsEvenSet S)
    (hT : G.IsEvenSet T) : G.IsEvenSet (S ∪ T) := fun v => by
  rw [G.deg_union_of_disjoint h]; exact (hS v).add (hT v)

theorem isEvenSet_sdiff {S T : Finset E} (h : T ⊆ S) (hS : G.IsEvenSet S)
    (hT : G.IsEvenSet T) : G.IsEvenSet (S \ T) := fun v => by
  have := G.deg_sdiff_add h v
  have h1 := hS v
  have h2 := hT v
  rw [← this] at h1
  exact (Nat.even_add.1 h1).2 h2

/-! ### Simple cycles -/

/-- Simple cycle: a nonempty Eulerian set whose only nonempty Eulerian subset is itself. -/
def IsSimpleCycle (C : Finset E) : Prop :=
  C.Nonempty ∧ G.IsEvenSet C ∧ ∀ D ⊆ C, D.Nonempty → G.IsEvenSet D → D = C

/-- Cycle union: degree zero or two at every vertex, corresponding to a union of vertex-disjoint simple cycles. -/
def IsCycleUnion (S : Finset E) : Prop := ∀ v, G.deg S v = 0 ∨ G.deg S v = 2

instance : DecidablePred G.IsCycleUnion := fun S => by unfold IsCycleUnion; infer_instance

instance : DecidablePred G.IsSimpleCycle := fun C => by unfold IsSimpleCycle; infer_instance

variable {G} in
theorem IsCycleUnion.isEvenSet {S : Finset E} (h : G.IsCycleUnion S) : G.IsEvenSet S := by
  intro v
  rcases h v with h | h <;> rw [h] <;> decide

variable {G} in
/-- The only Eulerian subsets of a simple cycle are empty and the entire cycle. -/
theorem IsSimpleCycle.evenSubsets {C : Finset E} (h : G.IsSimpleCycle C) :
    G.evenSubsets C = {∅, C} := by
  ext D
  rw [mem_evenSubsets, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hD, hDe⟩
    rcases D.eq_empty_or_nonempty with h0 | hne
    · exact Or.inl h0
    · exact Or.inr (h.2.2 D hD hne hDe)
  · rintro (rfl | rfl)
    · exact ⟨Finset.empty_subset _, fun v => by simp⟩
    · exact ⟨subset_refl _, h.2.1⟩

variable {G} in
/-- **A simple cycle has degrees zero or two.** Its cycle space has dimension one, so |C|≤v(C); it has no degree-one vertices, and the handshake identity forces every positive degree to be two. -/
theorem IsSimpleCycle.isCycleUnion {C : Finset E} (h : G.IsSimpleCycle C) :
    G.IsCycleUnion C := by
  have hne : C ≠ ∅ := Finset.nonempty_iff_ne_empty.1 h.1
  have h1 := G.card_evenSubsets C
  rw [h.evenSubsets, Finset.card_pair (Ne.symm hne)] at h1
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict C).incMap) = 1 := by
    have : 2 ^ 1 = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict C).incMap) := h1
    exact (Nat.pow_right_injective le_rfl this).symm
  have hA := G.card_add_one_le_finrank_restrict h.1
  have hc := G.isContributing_of_isEvenSet h.2.1
  exact G.deg_eq_two_of_card_le ((G.wt_phi_ne_zero_iff C).2 hc) (by omega)

variable {G} in
theorem IsSimpleCycle.deg_eq_two {C : Finset E} (h : G.IsSimpleCycle C) {v : V}
    (hv : v ∈ G.support C) : G.deg C v = 2 := by
  rcases h.isCycleUnion v with h0 | h2
  · rw [mem_support_iff] at hv; omega
  · exact h2

/-- **A simple cycle through each support vertex.** If v lies in an Eulerian set S, choose an Eulerian subset C⊆S containing v with minimal edge count; it is a simple cycle through v. -/
theorem exists_simpleCycle_through {S : Finset E} (hS : G.IsEvenSet S) {v : V}
    (hv : v ∈ G.support S) : ∃ C ⊆ S, G.IsSimpleCycle C ∧ v ∈ G.support C := by
  classical
  set 𝒜 := S.powerset.filter fun D => G.IsEvenSet D ∧ v ∈ G.support D
  have hne : 𝒜.Nonempty := ⟨S, by simp [𝒜, hS, hv]⟩
  obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image 𝒜 Finset.card hne
  simp only [𝒜, Finset.mem_filter, Finset.mem_powerset] at hC hmin
  obtain ⟨hCS, hCe, hvC⟩ := hC
  have hCne : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [mem_support_iff, deg] at hvC
  refine ⟨C, hCS, ⟨hCne, hCe, fun D hDC hDne hDe => ?_⟩, hvC⟩
  -- Either C\D or D contains v in its support.
  have hsplit := G.deg_sdiff_add hDC v
  rw [mem_support_iff] at hvC
  by_cases hvD : 0 < G.deg D v
  · have := hmin D ⟨hDC.trans hCS, hDe, (G.mem_support_iff).2 hvD⟩
    exact Finset.eq_of_subset_of_card_le hDC this
  · exfalso
    have hvCD : v ∈ G.support (C \ D) := by rw [mem_support_iff]; omega
    have := hmin (C \ D) ⟨Finset.sdiff_subset.trans hCS, G.isEvenSet_sdiff hDC hCe hDe, hvCD⟩
    have hlt : (C \ D).card < C.card := Finset.card_lt_card (Finset.sdiff_ssubset hDC hDne)
    omega

/-! ### Cycle unions and cycle collections -/

/-- If S⊆T are cycle unions, every T-edge incident to a support vertex of S lies in S, since degree two is saturated. -/
theorem mem_of_cycleUnion {S T : Finset E} (hT : G.IsCycleUnion T) (hST : S ⊆ T) {v : V}
    (hv : G.deg S v = 2) {e : E} (he : e ∈ T) (hev : G.Incident e v) : e ∈ S := by
  by_contra heS
  have h1 := G.deg_sdiff_add hST v
  have h2 : 1 ≤ G.deg (T \ S) v := by
    have := (G.endCount_eq_zero_iff e v).not.2 (not_not.2 hev)
    have hmem : e ∈ T \ S := Finset.mem_sdiff.2 ⟨he, heS⟩
    have := Finset.single_le_sum (f := fun e => G.endCount e v) (fun _ _ => Nat.zero_le _) hmem
    show 1 ≤ ∑ x ∈ T \ S, G.endCount x v
    omega
  rcases hT v with h | h <;> omega

/-- If a simple cycle C lies in a cycle union S, all S-edges at support vertices of C lie in C. -/
theorem mem_of_simpleCycle_sub {S C : Finset E} (hS : G.IsCycleUnion S) (hC : G.IsSimpleCycle C)
    (hCS : C ⊆ S) {v : V} (hv : v ∈ G.support C) {e : E} (he : e ∈ S) (hev : G.Incident e v) :
    e ∈ C :=
  G.mem_of_cycleUnion hS hCS (hC.deg_eq_two hv) he hev

/-- If D∩C has the degree of D on the support of C and zero outside, then D∩C is Eulerian. -/
theorem isEvenSet_inter_of {C D : Finset E} (hD : G.IsEvenSet D)
    (hin : ∀ v ∈ G.support C, ∀ e ∈ D, G.Incident e v → e ∈ C) : G.IsEvenSet (D ∩ C) := by
  intro v
  by_cases hv : v ∈ G.support C
  · have : G.deg (D ∩ C) v = G.deg D v := by
      unfold deg
      refine Finset.sum_subset Finset.inter_subset_left fun e heD heDC => ?_
      rw [G.endCount_eq_zero_iff]
      intro hev
      exact heDC (Finset.mem_inter.2 ⟨heD, hin v hv e heD hev⟩)
    rw [this]; exact hD v
  · have h0 : G.deg C v = 0 := by rw [mem_support_iff] at hv; omega
    have : G.deg (D ∩ C) v = 0 := by
      have := G.deg_mono (Finset.inter_subset_right (s₁ := D) (s₂ := C)) v
      omega
    rw [this]; exact ⟨0, rfl⟩

/-- If simple cycles C,D have a D-edge incident to the support of C and every D-edge there lies in C, then D=C. -/
theorem simpleCycle_eq_of {C D : Finset E} (hC : G.IsSimpleCycle C) (hD : G.IsSimpleCycle D)
    (hin : ∀ v ∈ G.support C, ∀ e ∈ D, G.Incident e v → e ∈ C)
    (hmeet : (D ∩ C).Nonempty) : D = C := by
  have hev := G.isEvenSet_inter_of hD.2.1 hin
  have h1 : D ∩ C = D := hD.2.2 _ Finset.inter_subset_left hmeet hev
  have h2 : D ∩ C = C := hC.2.2 _ Finset.inter_subset_right hmeet hev
  rw [← h1, h2]

/-- Collection of vertex-disjoint simple cycles. -/
def IsCycleCollection (𝒞 : Finset (Finset E)) : Prop :=
  (∀ C ∈ 𝒞, G.IsSimpleCycle C) ∧
    ∀ C ∈ 𝒞, ∀ D ∈ 𝒞, C ≠ D → Disjoint (G.support C) (G.support D)

/-- The degree of a vertex in the union of a vertex-disjoint cycle collection is its degree in the unique cycle through it. -/
theorem deg_biUnion {𝒞 : Finset (Finset E)} (h𝒞 : G.IsCycleCollection 𝒞) (v : V) :
    G.deg (𝒞.biUnion id) v = ∑ C ∈ 𝒞, G.deg C v := by
  unfold deg
  rw [Finset.sum_biUnion]
  · rfl
  · intro C hC D hD hCD
    simp only [id, Function.onFun]
    rw [Finset.disjoint_left]
    intro e heC heD
    exact Finset.disjoint_left.1 (h𝒞.2 C hC D hD hCD) (G.fst_mem_support heC)
      (G.fst_mem_support heD)

theorem isCycleUnion_biUnion {𝒞 : Finset (Finset E)} (h𝒞 : G.IsCycleCollection 𝒞) :
    G.IsCycleUnion (𝒞.biUnion id) := by
  intro v
  rw [G.deg_biUnion h𝒞]
  by_cases hv : ∃ C ∈ 𝒞, v ∈ G.support C
  · obtain ⟨C, hC, hvC⟩ := hv
    rw [Finset.sum_eq_single C]
    · exact (h𝒞.1 C hC).isCycleUnion v
    · intro D hD hDC
      have := Finset.disjoint_left.1 (h𝒞.2 C hC D hD (Ne.symm hDC)) hvC
      rw [mem_support_iff] at this; omega
    · intro h; exact absurd hC h
  · push Not at hv
    left
    refine Finset.sum_eq_zero fun C hC => ?_
    have := hv C hC
    rw [mem_support_iff] at this; omega

/-- A collection is determined by its union: its members are exactly the simple cycles contained in that union. -/
theorem mem_cycleCollection_iff {𝒞 : Finset (Finset E)} (h𝒞 : G.IsCycleCollection 𝒞)
    {D : Finset E} : D ∈ 𝒞 ↔ D ⊆ 𝒞.biUnion id ∧ G.IsSimpleCycle D := by
  constructor
  · intro hD
    exact ⟨fun e he => Finset.mem_biUnion.2 ⟨D, hD, he⟩, h𝒞.1 D hD⟩
  · rintro ⟨hDS, hD⟩
    obtain ⟨e, he⟩ := hD.1
    obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.1 (hDS he)
    have hS := G.isCycleUnion_biUnion h𝒞
    have hCS : C ⊆ 𝒞.biUnion id := fun f hf => Finset.mem_biUnion.2 ⟨C, hC, hf⟩
    have : D = C := G.simpleCycle_eq_of (h𝒞.1 C hC) hD
      (fun v hv f hf hfv => G.mem_of_simpleCycle_sub hS (h𝒞.1 C hC) hCS hv (hDS hf) hfv)
      ⟨e, Finset.mem_inter.2 ⟨he, heC⟩⟩
    exact this ▸ hC

/-- All simple cycles in a cycle union form a vertex-disjoint collection whose union is the original set. -/
theorem cycleCollection_of_cycleUnion {S : Finset E} (hS : G.IsCycleUnion S) :
    G.IsCycleCollection (S.powerset.filter G.IsSimpleCycle) ∧
      (S.powerset.filter G.IsSimpleCycle).biUnion id = S := by
  classical
  constructor
  · refine ⟨fun C hC => (Finset.mem_filter.1 hC).2, fun C hC D hD hCD => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC hD
    rw [Finset.disjoint_left]
    intro v hvC hvD
    apply hCD
    -- D-edges at v lie in C, so D∩C is nonempty.
    obtain ⟨e, heD, hev⟩ : ∃ e ∈ D, G.Incident e v := by
      rw [mem_support_iff] at hvD
      by_contra h
      push Not at h
      have := (G.deg_eq_zero_iff D v).2 h
      omega
    have heC := G.mem_of_simpleCycle_sub hS hC.2 hC.1 hvC (hD.1 heD) hev
    exact (G.simpleCycle_eq_of hC.2 hD.2
      (fun w hw f hf hfw => G.mem_of_simpleCycle_sub hS hC.2 hC.1 hw (hD.1 hf) hfw)
      ⟨e, Finset.mem_inter.2 ⟨heD, heC⟩⟩).symm
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset, id]
    constructor
    · rintro ⟨C, ⟨hCS, -⟩, heC⟩; exact hCS heC
    · intro he
      obtain ⟨C, hCS, hC, hvC⟩ := G.exists_simpleCycle_through hS.isEvenSet
        (G.fst_mem_support he)
      exact ⟨C, ⟨hCS, hC⟩, G.mem_of_simpleCycle_sub hS hC hCS hvC he (Or.inl rfl)⟩

/-- **Cycle unions biject with collections of vertex-disjoint simple cycles, including the empty collection.** -/
theorem card_cycleCollections [DecidablePred G.IsCycleCollection] :
    (Finset.univ.filter G.IsCycleCollection).card = (Finset.univ.filter G.IsCycleUnion).card := by
  classical
  refine Finset.card_bij (fun 𝒞 _ => 𝒞.biUnion id) ?_ ?_ ?_
  · intro 𝒞 h𝒞
    rw [Finset.mem_filter] at h𝒞 ⊢
    exact ⟨Finset.mem_univ _, G.isCycleUnion_biUnion h𝒞.2⟩
  · intro 𝒞₁ h₁ 𝒞₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    ext D
    rw [G.mem_cycleCollection_iff h₁.2, G.mem_cycleCollection_iff h₂.2]
    rw [h]
  · intro S hS
    rw [Finset.mem_filter] at hS
    obtain ⟨h1, h2⟩ := G.cycleCollection_of_cycleUnion hS.2
    exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩, h2⟩

/-! ### Generator count and 2^ν -/

/-- The sum of the zeroth Betti row counts cycle unions. -/
theorem sum_betti_zero_eq_card :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q =
      (Finset.univ.filter G.IsCycleUnion).card := by
  classical
  simp_rw [betti_zero_eq_card]
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card)
    (t := Finset.range (Fintype.card E + 1))]
  · refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ext S
    simp [IsCycleUnion, and_comm]
  · intro S _
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ S))

theorem cycleUnions_subset_evenSets :
    Finset.univ.filter G.IsCycleUnion ⊆ Finset.univ.filter G.IsEvenSet := by
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.isEvenSet⟩

/-- **The generator count is at most 2^ν.** -/
theorem sum_betti_zero_le :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q ≤ 2 ^ G.nu := by
  rw [sum_betti_zero_eq_card, ← card_evenSets_eq_two_pow_nu]
  exact Finset.card_le_card G.cycleUnions_subset_evenSets

/-- Equality holds iff every Eulerian edge set is a cycle union. -/
theorem sum_betti_zero_eq_iff_evenSets :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q = 2 ^ G.nu ↔
      ∀ S, G.IsEvenSet S → G.IsCycleUnion S := by
  rw [sum_betti_zero_eq_card, ← card_evenSets_eq_two_pow_nu]
  constructor
  · intro h S hS
    have := Finset.eq_of_subset_of_card_le G.cycleUnions_subset_evenSets h.ge
    have hmem : S ∈ Finset.univ.filter G.IsEvenSet := by simp [hS]
    rw [← this] at hmem
    exact (Finset.mem_filter.1 hmem).2
  · intro h
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hU => hU.isEvenSet, h S⟩

/-- **Equality criterion.** Σ_q β_{0,q}=2^ν iff every two edge-disjoint simple cycles are vertex-disjoint. -/
theorem sum_betti_zero_eq_iff :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q = 2 ^ G.nu ↔
      ∀ C D, G.IsSimpleCycle C → G.IsSimpleCycle D → Disjoint C D →
        Disjoint (G.support C) (G.support D) := by
  rw [sum_betti_zero_eq_iff_evenSets]
  constructor
  · intro h C D hC hD hCD
    rw [Finset.disjoint_left]
    intro v hvC hvD
    have hU := h _ (G.isEvenSet_union hCD hC.2.1 hD.2.1)
    have := hU v
    rw [G.deg_union_of_disjoint hCD, hC.deg_eq_two hvC, hD.deg_eq_two hvD] at this
    omega
  · intro h S hS v
    by_contra hv
    push Not at hv
    have hvS : v ∈ G.support S := by rw [mem_support_iff]; omega
    obtain ⟨C, hCS, hC, hvC⟩ := G.exists_simpleCycle_through hS hvS
    have h2 := hC.deg_eq_two hvC
    have hsplit := G.deg_sdiff_add hCS v
    have hev : Even (G.deg S v) := hS v
    have h4 : 4 ≤ G.deg S v := by
      obtain ⟨k, hk⟩ := hev
      omega
    have hvSC : v ∈ G.support (S \ C) := by rw [mem_support_iff]; omega
    obtain ⟨D, hDS, hD, hvD⟩ := G.exists_simpleCycle_through
      (G.isEvenSet_sdiff hCS hS hC.2.1) hvSC
    have hCD : Disjoint C D := by
      rw [Finset.disjoint_left]
      intro e heC heD
      exact (Finset.mem_sdiff.1 (hDS heD)).2 heC
    exact Finset.disjoint_left.1 (h C D hC hD hCD) hvC hvD

/-- **Equality holds when maximum degree is at most three.** -/
theorem sum_betti_zero_eq_of_deg_le_three (h : ∀ v, G.deg Finset.univ v ≤ 3) :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q = 2 ^ G.nu := by
  rw [sum_betti_zero_eq_iff_evenSets]
  intro S hS v
  have h1 := G.deg_mono (Finset.subset_univ S) v
  have h2 := h v
  obtain ⟨k, hk⟩ := hS v
  omega

/-- Generator count equals the number of vertex-disjoint simple-cycle collections, including empty. -/
theorem sum_betti_zero_eq_card_cycleCollections [DecidablePred G.IsCycleCollection] :
    ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti 0 q =
      (Finset.univ.filter G.IsCycleCollection).card := by
  rw [sum_betti_zero_eq_card, card_cycleCollections]

end Multigraph

end BPFixedPoints

/-! ## Parity of state weights and real states: combinatorial parts of `real:positive-bound` and `real:all-real-states` -/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- wt(S) modulo two is the indicator that S is Eulerian. -/
theorem wt_cast_zmod_two (S : Finset E) :
    (G.wt phi S : ZMod 2) = if G.IsEvenSet S then 1 else 0 := by
  rw [wt, Nat.cast_prod]
  simp only [phi_cast_zmod_two]
  rw [Finset.prod_boole]
  simp [IsEvenSet]

/-- **wt(S) is odd iff S is Eulerian.** -/
theorem odd_wt_iff (S : Finset E) : Odd (G.wt phi S) ↔ G.IsEvenSet S := by
  rw [← ZMod.natCast_eq_one_iff_odd, wt_cast_zmod_two]
  split_ifs with h <;> simp [h]

/-- **Q(G)≡2^ν mod 2**, since there are 2^ν Eulerian edge sets. -/
theorem Q_modEq_two_pow_nu : G.Q ≡ 2 ^ G.nu [MOD 2] := by
  rw [← ZMod.natCast_eq_natCast_iff, Q_cast_zmod_two, card_evenSets_eq_two_pow_nu]

theorem phi_eq_one_iff (d : ℕ) : phi d = 1 ↔ d = 0 ∨ d = 2 := by
  rcases d with _ | _ | _ | k <;> simp [phi]

/-- **wt(S)=1 iff every degree is zero or two.** These are generator states, all of whose roots become real at strong fields. -/
theorem wt_eq_one_iff (S : Finset E) : G.wt phi S = 1 ↔ G.IsCycleUnion S := by
  constructor
  · intro h v
    have hdvd : phi (G.deg S v) ∣ G.wt phi S :=
      Finset.dvd_prod_of_mem (fun v => phi (G.deg S v)) (Finset.mem_univ v)
    rw [h, Nat.dvd_one, phi_eq_one_iff] at hdvd
    exact hdvd
  · intro h
    exact (G.wt_eq_one_of_deg h).1

/-- An Eulerian edge set with a vertex of degree at least four has weight at least three. -/
theorem three_le_wt {S : Finset E} (hS : G.IsEvenSet S) {v : V} (hv : 4 ≤ G.deg S v) :
    3 ≤ G.wt phi S := by
  have hdvd : phi (G.deg S v) ∣ G.wt phi S :=
    Finset.dvd_prod_of_mem (fun v => phi (G.deg S v)) (Finset.mem_univ v)
  have hne : G.wt phi S ≠ 0 :=
    (G.wt_phi_ne_zero_iff S).2 (G.isContributing_of_isEvenSet hS)
  have h3 : 3 ≤ phi (G.deg S v) := by
    rw [phi_of_pos (by omega)]; omega
  exact h3.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd)

end Multigraph

end BPFixedPoints
