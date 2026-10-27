import BPFixedPoints.Incidence.CycleSpace

/-!
# Numerical state cohomology (`alg:state-cohomology`) and τ,ρ,d_G

Use the paper's §3 notation for arbitrary multigraphs, including disconnected
graphs and isolated vertices. Define `Comp`, `compVerts K`, `compEdges K` and
connected `compGraph K` (`compGraph_connected`); the component cycle-space
dimension is m_K+1−n_K (`finrank_ker_restrict_compEdges`).
Let τ=`tau` count tree components, including isolated vertices; ρ=`rho`=m−n+τ
and d_G=`dG`=3m+n−τ. Then d_G+ρ=4m (`dG_add_rho`), and ρ is the sum of
ν(C)−1 over cyclic components (`rho_eq_sum`).
For contributing states S, 0≤|S|−v(S)≤ρ (`card_support_le_of_isContributing`,
`card_le_card_support_add_rho`). The bound is attained (`exists_isContributing_card_eq`)
by taking cyclic-component 2-cores, via leaf-removal induction `exists_contributing_sub`.
Thus β_{p,q} vanishes for p>ρ (`betti_eq_zero_of_rho_lt`) and some entry in
row ρ is nonzero (`exists_betti_rho_ne_zero`), the numerical part of the exact
resolution length in `alg:resolution`.
The total of `stateDim`, representing dim E₁^{−q,j}=Σ_{|S|=q,v(S)=j}wt(S),
is Q (`sum_stateDim_eq_Q`). This module only treats combinatorial dimensions,
not sheaf cohomology, Künneth or H^j(ℙ¹,𝒪(−d)) itself.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-! ### Connected components -/

/-- Type of connected components of G. -/
def Comp : Type _ := Quotient (G.compSetoid Finset.univ)

/-- Component containing a vertex. -/
def compOf (v : V) : G.Comp := Quotient.mk (G.compSetoid Finset.univ) v

noncomputable instance : Fintype G.Comp := by
  unfold Comp
  exact Fintype.ofFinite _

noncomputable instance : DecidableEq G.Comp := Classical.decEq _

theorem compOf_eq_compOf_iff {a b : V} : G.compOf a = G.compOf b ↔ G.Reach Finset.univ a b :=
  Quotient.eq (r := G.compSetoid Finset.univ)

theorem compOf_surjective : Function.Surjective G.compOf :=
  Quotient.mk_surjective

theorem compOf_fst_eq_snd (e : E) : G.compOf (G.fst e) = G.compOf (G.snd e) :=
  (G.compOf_eq_compOf_iff).2 (G.reach_fst_snd (Finset.mem_univ e))

theorem card_comp : Fintype.card G.Comp = G.numComponents := by
  rw [numComponents, numComp, ← Nat.card_eq_fintype_card]
  rfl

/-- Vertex set of component K. -/
noncomputable def compVerts (K : G.Comp) : Finset V := Finset.univ.filter fun v => G.compOf v = K

/-- Edge set of component K. -/
noncomputable def compEdges (K : G.Comp) : Finset E :=
  Finset.univ.filter fun e => G.compOf (G.fst e) = K

variable {G} in
theorem mem_compVerts {K : G.Comp} {v : V} : v ∈ G.compVerts K ↔ G.compOf v = K := by
  simp [compVerts]

variable {G} in
theorem mem_compEdges {K : G.Comp} {e : E} : e ∈ G.compEdges K ↔ G.compOf (G.fst e) = K := by
  simp [compEdges]

variable {G} in
theorem mem_compEdges' {K : G.Comp} {e : E} : e ∈ G.compEdges K ↔ G.compOf (G.snd e) = K := by
  rw [mem_compEdges, compOf_fst_eq_snd]

/-- Both endpoints of an edge lie in its component. -/
theorem compOf_of_incident {e : E} {v : V} (h : G.Incident e v) :
    G.compOf v = G.compOf (G.fst e) := by
  rcases h with h | h
  · rw [h]
  · rw [← h, compOf_fst_eq_snd]

theorem card_eq_sum_compVerts : Fintype.card V = ∑ K, (G.compVerts K).card := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := G.compOf)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rfl

theorem card_eq_sum_compEdges : Fintype.card E = ∑ K, (G.compEdges K).card := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := fun e => G.compOf (G.fst e))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rfl

/-! ### Component decomposition -/

/-- Component-K part of S: S∩E(K). -/
noncomputable def compPart (S : Finset E) (K : G.Comp) : Finset E := S.filter fun e => e ∈ G.compEdges K

theorem compPart_subset (S : Finset E) (K : G.Comp) : G.compPart S K ⊆ S :=
  Finset.filter_subset _ _

theorem compPart_subset_compEdges (S : Finset E) (K : G.Comp) : G.compPart S K ⊆ G.compEdges K :=
  fun _ he => (Finset.mem_filter.1 he).2

theorem deg_compPart (S : Finset E) (K : G.Comp) (v : V) :
    G.deg (G.compPart S K) v = if G.compOf v = K then G.deg S v else 0 := by
  unfold deg compPart
  rw [Finset.sum_filter]
  split_ifs with hv
  · refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs with he
    · rfl
    · symm
      rw [G.endCount_eq_zero_iff]
      intro hi
      apply he
      rw [mem_compEdges, ← G.compOf_of_incident hi, hv]
  · refine Finset.sum_eq_zero fun e _ => ?_
    split_ifs with he
    · rw [G.endCount_eq_zero_iff]
      intro hi
      apply hv
      rw [G.compOf_of_incident hi, ← mem_compEdges]
      exact he
    · rfl

theorem support_compPart (S : Finset E) (K : G.Comp) :
    G.support (G.compPart S K) = (G.support S).filter fun v => G.compOf v = K := by
  ext v
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, deg_compPart]
  split_ifs with hv <;> simp [hv]

theorem card_eq_sum_compPart (S : Finset E) : S.card = ∑ K, (G.compPart S K).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e => G.compOf (G.fst e))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  ext e
  simp [compPart, mem_compEdges]

theorem card_support_eq_sum_compPart (S : Finset E) :
    (G.support S).card = ∑ K, (G.support (G.compPart S K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := G.compOf) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [support_compPart]

theorem isContributing_compPart {S : Finset E} (hS : G.IsContributing S) (K : G.Comp) :
    G.IsContributing (G.compPart S K) := by
  intro v
  rw [deg_compPart]
  split_ifs
  · exact hS v
  · omega

theorem support_subset_compVerts {S : Finset E} {K : G.Comp} (h : S ⊆ G.compEdges K) :
    G.support S ⊆ G.compVerts K := by
  intro v hv
  rw [mem_compVerts]
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  by_contra hne
  have : G.deg S v = 0 := by
    rw [deg_eq_zero_iff]
    intro e he hi
    apply hne
    rw [G.compOf_of_incident hi]
    exact mem_compEdges.1 (h he)
  omega

/-! ### A component as a graph -/

/-- Component K regarded as its own graph. -/
noncomputable def compGraph (K : G.Comp) :
    Multigraph {v // v ∈ G.compVerts K} {e // e ∈ G.compEdges K} where
  fst e := ⟨G.fst e.1, mem_compVerts.2 (mem_compEdges.1 e.2)⟩
  snd e := ⟨G.snd e.1, mem_compVerts.2 (mem_compEdges'.1 e.2)⟩

theorem compGraph_endCount (K : G.Comp) (e : {e // e ∈ G.compEdges K})
    (v : {v // v ∈ G.compVerts K}) : (G.compGraph K).endCount e v = G.endCount e.1 v.1 := by
  simp [endCount, compGraph, Subtype.ext_iff]

theorem compGraph_deg (K : G.Comp) (T : Finset {e // e ∈ G.compEdges K})
    (v : {v // v ∈ G.compVerts K}) :
    (G.compGraph K).deg T v = G.deg (T.map (Function.Embedding.subtype _)) v.1 := by
  simp [deg, Finset.sum_map, compGraph_endCount]

theorem compGraph_loopless (hG : G.Loopless) (K : G.Comp) : (G.compGraph K).Loopless := by
  intro e h
  exact hG e.1 (congrArg Subtype.val h)

/-- A component graph is connected. -/
theorem compGraph_connected (K : G.Comp) : (G.compGraph K).Connected := by
  obtain ⟨v₀, hv₀⟩ := G.compOf_surjective K
  refine ⟨⟨⟨v₀, mem_compVerts.2 hv₀⟩, Finset.mem_univ _⟩, fun _ _ => ⟨Finset.mem_univ _,
    Finset.mem_univ _⟩, fun a _ b _ => ?_⟩
  -- Lift a path of G into its component.
  have lift : ∀ x : V, G.Reach Finset.univ a.1 x → ∀ hx : x ∈ G.compVerts K,
      Relation.ReflTransGen ((G.compGraph K).Adj Finset.univ) a ⟨x, hx⟩ := by
    intro x hax
    induction hax with
    | refl => intro hx; exact Relation.ReflTransGen.refl
    | @tail x y hax hxy ih =>
      intro hy
      obtain ⟨e, -, he⟩ := hxy
      have hcxy : G.compOf x = G.compOf y := by
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2, compOf_fst_eq_snd]
        · rw [← h1, ← h2, compOf_fst_eq_snd]
      have hx : x ∈ G.compVerts K := by
        rw [mem_compVerts] at hy ⊢; rw [hcxy, hy]
      have heK : e ∈ G.compEdges K := by
        rw [mem_compEdges]
        rcases he with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1]; exact mem_compVerts.1 hx
        · rw [h1]; exact mem_compVerts.1 hy
      refine Relation.ReflTransGen.tail (ih hx) ⟨⟨e, heK⟩, Finset.mem_univ _, ?_⟩
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hab : G.Reach Finset.univ a.1 b.1 := by
    rw [← compOf_eq_compOf_iff, mem_compVerts.1 a.2, mem_compVerts.1 b.2]
  simpa using lift b.1 hab b.2

/-- An edge set contained in E(K) has degree zero outside K. -/
theorem deg_eq_zero_of_subset_compEdges {S : Finset E} {K : G.Comp} (h : S ⊆ G.compEdges K)
    {v : V} (hv : v ∉ G.compVerts K) : G.deg S v = 0 := by
  have := G.support_subset_compVerts h
  by_contra hne
  exact hv (this (by simp [support]; omega))

/-- Eulerian sets of the component graph biject with Eulerian sets of G contained in E(K). -/
theorem card_evenSubsets_compEdges (K : G.Comp) :
    (G.evenSubsets (G.compEdges K)).card =
      (Finset.univ.filter (G.compGraph K).IsEvenSet).card := by
  symm
  refine Finset.card_bij (fun T _ => T.map (Function.Embedding.subtype _)) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    rw [mem_evenSubsets]
    refine ⟨fun e he => ?_, fun v => ?_⟩
    · obtain ⟨e', -, rfl⟩ := Finset.mem_map.1 he
      exact e'.2
    · by_cases hv : v ∈ G.compVerts K
      · have := hT.2 ⟨v, hv⟩
        rwa [compGraph_deg] at this
      · rw [G.deg_eq_zero_of_subset_compEdges (fun e he => by
          obtain ⟨e', -, rfl⟩ := Finset.mem_map.1 he; exact e'.2) hv]
        exact ⟨0, rfl⟩
  · intro T₁ _ T₂ _ h
    exact Finset.map_injective _ h
  · intro S hS
    rw [mem_evenSubsets] at hS
    refine ⟨S.subtype (· ∈ G.compEdges K), ?_, Finset.subtype_map_of_mem fun e he => hS.1 he⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun v => ?_⟩
    rw [compGraph_deg, Finset.subtype_map_of_mem fun e he => hS.1 he]
    exact hS.2 v.1

/-- **Component cycle-space dimension.** dim H₁(K;𝔽₂)+n_K=m_K+1. -/
theorem finrank_ker_restrict_compEdges (K : G.Comp) :
    Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict (G.compEdges K)).incMap) +
      (G.compVerts K).card = (G.compEdges K).card + 1 := by
  have hc := G.compGraph_connected K
  have h1 := G.card_evenSubsets (G.compEdges K)
  rw [card_evenSubsets_compEdges, (G.compGraph K).card_evenSets_of_connected hc] at h1
  have h2 := Nat.pow_right_injective le_rfl h1
  have hle := (G.compGraph K).card_vertex_le_of_connected hc
  simp only [Fintype.card_coe] at hle
  rw [← h2]
  unfold cycleRank
  simp only [Fintype.card_coe]
  omega

theorem card_compVerts_le (K : G.Comp) : (G.compVerts K).card ≤ (G.compEdges K).card + 1 := by
  have := G.finrank_ker_restrict_compEdges K
  omega

/-! ### τ, ρ and d_G -/

/-- Tree component: m_K+1=n_K, including isolated vertices. -/
def IsTreeComp (K : G.Comp) : Prop := (G.compEdges K).card + 1 = (G.compVerts K).card

noncomputable instance (K : G.Comp) : Decidable (G.IsTreeComp K) := by
  unfold IsTreeComp; infer_instance

/-- τ(G): number of tree components, including isolated vertices. -/
noncomputable def tau : ℕ := (Finset.univ.filter G.IsTreeComp).card

/-- ρ(G) = m − n + τ。 -/
noncomputable def rho : ℕ := Fintype.card E + G.tau - Fintype.card V

/-- d_G=3m+n−τ, the dimension of the universal edge-incidence ring. -/
noncomputable def dG : ℕ := 3 * Fintype.card E + Fintype.card V - G.tau

theorem tau_le_numComponents : G.tau ≤ G.numComponents := by
  rw [← card_comp]
  exact Finset.card_filter_le _ _

/-- For each component, n_K≤m_K+[K is a tree]. -/
theorem card_compVerts_le' (K : G.Comp) :
    (G.compVerts K).card ≤ (G.compEdges K).card + if G.IsTreeComp K then 1 else 0 := by
  have := G.card_compVerts_le K
  split_ifs with h
  · omega
  · unfold IsTreeComp at h; omega

theorem sum_ite_isTreeComp : (∑ K, if G.IsTreeComp K then 1 else 0) = G.tau := by
  rw [tau, Finset.card_filter]

theorem card_le_card_add_tau : Fintype.card V ≤ Fintype.card E + G.tau := by
  rw [G.card_eq_sum_compVerts, G.card_eq_sum_compEdges, ← sum_ite_isTreeComp,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun K _ => G.card_compVerts_le' K

theorem rho_add_card : G.rho + Fintype.card V = Fintype.card E + G.tau := by
  have := G.card_le_card_add_tau
  unfold rho; omega

/-- ρ=Σ_{cyclic components C}(ν(C)−1)=Σ_{non-tree K}(m_K−n_K). -/
theorem rho_eq_sum :
    (G.rho : ℤ) = ∑ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K),
      ((G.compEdges K).card - (G.compVerts K).card : ℤ) := by
  have h := G.rho_add_card
  have hV := G.card_eq_sum_compVerts
  have hE := G.card_eq_sum_compEdges
  have hsplit : ∑ K, ((G.compEdges K).card - (G.compVerts K).card : ℤ) =
      ∑ K ∈ Finset.univ.filter (fun K => ¬ G.IsTreeComp K),
        ((G.compEdges K).card - (G.compVerts K).card : ℤ) - G.tau := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ G.IsTreeComp, tau]
    have : ∑ K ∈ Finset.univ.filter G.IsTreeComp,
        ((G.compEdges K).card - (G.compVerts K).card : ℤ) =
        ∑ K ∈ Finset.univ.filter G.IsTreeComp, (-1 : ℤ) := by
      refine Finset.sum_congr rfl fun K hK => ?_
      have := (Finset.mem_filter.1 hK).2
      unfold IsTreeComp at this
      omega
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    ring
  have : ∑ K, ((G.compEdges K).card - (G.compVerts K).card : ℤ) =
      (Fintype.card E : ℤ) - Fintype.card V := by
    rw [Finset.sum_sub_distrib, hV, hE]
    push_cast
    ring
  have hρ : (G.rho : ℤ) = Fintype.card E + G.tau - Fintype.card V := by
    have : (G.rho : ℤ) + Fintype.card V = Fintype.card E + G.tau := by exact_mod_cast h
    linarith
  linarith

theorem tau_le_card : G.tau ≤ Fintype.card V :=
  G.tau_le_numComponents.trans G.numComponents_le

/-- d_G + ρ = 4m。 -/
theorem dG_add_rho : G.dG + G.rho = 4 * Fintype.card E := by
  have h1 := G.rho_add_card
  have h2 := G.tau_le_card
  unfold dG
  omega

/-! ### Range of |S|−v(S) for contributing states -/

/-- A tree component has no nonempty contributing state. In a cyclic component, a contributing state satisfies |S_K|+n_K≤v(S_K)+m_K. -/
theorem card_compPart_le {S : Finset E} (hS : G.IsContributing S) (K : G.Comp) :
    (G.compPart S K).card + (G.compVerts K).card ≤
      (G.support (G.compPart S K)).card + (G.compEdges K).card +
        if G.IsTreeComp K then 1 else 0 := by
  have hK := G.card_compVerts_le' K
  rcases (G.compPart S K).eq_empty_or_nonempty with h0 | hne
  · rw [h0]; simp only [Finset.card_empty, zero_add]
    have : G.support ∅ = ∅ := by ext v; simp [support]
    rw [this, Finset.card_empty, zero_add]
    exact hK
  · have h1 := G.card_add_one_le_finrank_restrict hne
    have h2 := G.finrank_ker_restrict_mono (G.compPart_subset_compEdges S K)
    have h3 := G.finrank_ker_restrict_compEdges K
    have h4 := G.card_support_le_of_isContributing (G.isContributing_compPart hS K)
    split_ifs with ht
    · unfold IsTreeComp at ht; omega
    · omega

/-- **Upper bound.** A contributing state satisfies |S|≤v(S)+ρ. -/
theorem card_le_card_support_add_rho {S : Finset E} (hS : G.IsContributing S) :
    S.card ≤ (G.support S).card + G.rho := by
  have hsum := Finset.sum_le_sum fun K (_ : K ∈ Finset.univ) => G.card_compPart_le hS K
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← G.card_eq_sum_compPart, ← G.card_eq_sum_compVerts, ← G.card_support_eq_sum_compPart,
    ← G.card_eq_sum_compEdges, sum_ite_isTreeComp] at hsum
  have := G.rho_add_card
  omega

/-! ### Attaining the bound by leaf removal -/

/-- **Leaf removal.** Every edge set A contains a contributing T with the same Eulerian subsets and v(T)+|A|≤v(A)+|T|; removing a leaf decreases both edge count and support size by at least one. -/
theorem exists_contributing_sub (A : Finset E) :
    ∃ T ⊆ A, G.IsContributing T ∧ G.evenSubsets T = G.evenSubsets A ∧
      (G.support T).card + A.card ≤ (G.support A).card + T.card := by
  induction A using Finset.strongInduction with
  | H A ih =>
  by_cases hA : G.IsContributing A
  · exact ⟨A, subset_refl _, hA, rfl, le_refl _⟩
  · simp only [IsContributing, not_forall, not_not] at hA
    obtain ⟨u, hu⟩ := hA
    obtain ⟨e, heA, heu⟩ : ∃ e ∈ A, G.Incident e u := by
      by_contra h
      push Not at h
      have := (G.deg_eq_zero_iff A u).2 h
      omega
    have hsplit : G.deg A u = G.deg (A.erase e) u + G.endCount e u := by
      conv_lhs => rw [← Finset.insert_erase heA]
      rw [G.deg_insert (Finset.notMem_erase e A)]
    have hcnt : 1 ≤ G.endCount e u := by
      have := (G.endCount_eq_zero_iff e u).not.2 (not_not.2 heu)
      omega
    have hdeg0 : G.deg (A.erase e) u = 0 := by omega
    obtain ⟨T, hTA, hTc, hTev, hTcard⟩ := ih (A.erase e) (Finset.erase_ssubset heA)
    refine ⟨T, hTA.trans (Finset.erase_subset e A), hTc, ?_, ?_⟩
    · rw [hTev]
      ext S
      rw [mem_evenSubsets, mem_evenSubsets]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1.trans (Finset.erase_subset e A), h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨fun f hf => Finset.mem_erase.2 ⟨fun hfe => ?_, h1 hf⟩, h2⟩
        subst hfe
        have hle : G.deg S u ≤ G.deg A u := G.deg_mono h1 u
        have hge : G.endCount f u ≤ G.deg S u := by
          unfold deg
          exact Finset.single_le_sum (f := fun e => G.endCount e u) (fun _ _ => Nat.zero_le _) hf
        have h1' : G.deg S u = 1 := by omega
        have := h2 u
        rw [h1'] at this
        exact Nat.not_even_one this
    · have hsupp : (G.support (A.erase e)).card + 1 ≤ (G.support A).card := by
        have hsub : G.support (A.erase e) ⊆ (G.support A).erase u := by
          intro v hv
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          refine Finset.mem_erase.2 ⟨fun h => by rw [h] at hv; omega, ?_⟩
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
          exact lt_of_lt_of_le hv (G.deg_mono (Finset.erase_subset e A) v)
        have hu : u ∈ G.support A := by
          simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hu] at this
        have : 0 < (G.support A).card := Finset.card_pos.2 ⟨u, hu⟩
        omega
      have := Finset.card_erase_of_mem heA
      have : 0 < A.card := Finset.card_pos.2 ⟨e, heA⟩
      omega

/-- Cyclic-component 2-core: a contributing T⊆E(K) with |T|+n_K=v(T)+m_K. -/
theorem exists_core_compEdges (K : G.Comp) (hK : ¬ G.IsTreeComp K) :
    ∃ T ⊆ G.compEdges K, G.IsContributing T ∧
      T.card + (G.compVerts K).card = (G.support T).card + (G.compEdges K).card := by
  obtain ⟨T, hTA, hTc, hTev, hTcard⟩ := G.exists_contributing_sub (G.compEdges K)
  refine ⟨T, hTA, hTc, ?_⟩
  have hdim := G.finrank_ker_restrict_compEdges K
  unfold IsTreeComp at hK
  have hle := G.card_compVerts_le K
  have hpos : 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict (G.compEdges K)).incMap) := by
    omega
  -- T is nonempty since E(K) contains a nonempty Eulerian subset.
  have hdimT : Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict T).incMap) =
      Module.finrank (ZMod 2) (LinearMap.ker (G.edgeRestrict (G.compEdges K)).incMap) := by
    have h1 := G.card_evenSubsets T
    rw [hTev, G.card_evenSubsets] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hTne : T.Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    have h1 := G.card_evenSubsets T
    have : G.evenSubsets T = {∅} := by
      ext S; rw [mem_evenSubsets, h0, Finset.mem_singleton, Finset.subset_empty]
      constructor
      · exact fun h => h.1
      · rintro rfl; exact ⟨rfl, fun v => by simp⟩
    rw [this, Finset.card_singleton, hdimT] at h1
    have : 2 ^ 1 ≤ 2 ^ Module.finrank (ZMod 2)
        (LinearMap.ker (G.edgeRestrict (G.compEdges K)).incMap) := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hA := G.card_add_one_le_finrank_restrict hTne
  have hsupp := Finset.card_le_card (G.support_subset_compVerts (subset_refl (G.compEdges K)))
  omega

/-- **Attainment.** Some contributing S satisfies |S|=v(S)+ρ, by taking the union of cyclic-component 2-cores. -/
theorem exists_isContributing_card_eq :
    ∃ S : Finset E, G.IsContributing S ∧ S.card = (G.support S).card + G.rho := by
  classical
  have hcore : ∀ K : G.Comp, ∃ T ⊆ G.compEdges K, G.IsContributing T ∧
      T.card + (G.compVerts K).card =
        (G.support T).card + (G.compEdges K).card + if G.IsTreeComp K then 1 else 0 := by
    intro K
    by_cases hK : G.IsTreeComp K
    · refine ⟨∅, Finset.empty_subset _, fun v => by simp, ?_⟩
      have : G.support ∅ = ∅ := by ext v; simp [support]
      rw [this]
      simp only [hK, ↓reduceIte]
      unfold IsTreeComp at hK
      simp [hK]
    · obtain ⟨T, h1, h2, h3⟩ := G.exists_core_compEdges K hK
      exact ⟨T, h1, h2, by simp only [hK, ↓reduceIte]; omega⟩
  choose T hTsub hTc hTcard using hcore
  set S := Finset.univ.biUnion T with hSdef
  have hpart : ∀ K, G.compPart S K = T K := by
    intro K
    ext e
    simp only [compPart, Finset.mem_filter, hSdef, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨L, hL⟩, heK⟩
      have : L = K := by
        rw [← mem_compEdges.1 (hTsub L hL), ← mem_compEdges.1 heK]
      exact this ▸ hL
    · intro he
      exact ⟨⟨K, he⟩, hTsub K he⟩
  have hSc : G.IsContributing S := by
    intro v h1
    have := hTc (G.compOf v) v
    rw [← hpart, deg_compPart] at this
    simp only [↓reduceIte] at this
    exact this h1
  refine ⟨S, hSc, ?_⟩
  have hsum : ∑ K, ((T K).card + (G.compVerts K).card) =
      ∑ K, ((G.support (T K)).card + (G.compEdges K).card +
        if G.IsTreeComp K then 1 else 0) := Finset.sum_congr rfl fun K _ => hTcard K
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← G.card_eq_sum_compVerts, ← G.card_eq_sum_compEdges, sum_ite_isTreeComp] at hsum
  have hS1 : S.card = ∑ K, (T K).card := by
    rw [G.card_eq_sum_compPart S]; simp only [hpart]
  have hS2 : (G.support S).card = ∑ K, (G.support (T K)).card := by
    rw [G.card_support_eq_sum_compPart S]; simp only [hpart]
  have := G.rho_add_card
  omega

/-! ### Betti row range -/

/-- **The Betti table occupies rows zero through ρ.** -/
theorem betti_eq_zero_of_rho_lt {i : ℕ} (hi : G.rho < i) (k : ℕ) : G.betti i k = 0 := by
  unfold betti
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [Finset.mem_filter] at hS
  by_contra hw
  have := G.card_le_card_support_add_rho ((G.wt_phi_ne_zero_iff S).1 hw)
  omega

/-- **Row ρ is nonzero**, the numerical part of exact minimal-resolution length ρ. -/
theorem exists_betti_rho_ne_zero : ∃ k, G.betti G.rho k ≠ 0 := by
  obtain ⟨S, hSc, hS⟩ := G.exists_isContributing_card_eq
  refine ⟨S.card, fun h0 => ?_⟩
  unfold betti at h0
  have hmem : S ∈ Finset.univ.filter fun T : Finset E =>
      T.card = S.card ∧ T.card - (G.support T).card = G.rho := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have := (Finset.sum_eq_zero_iff.1 h0) S hmem
  exact (G.wt_phi_ne_zero_iff S).2 hSc this

/-! ### First-page dimensions -/

/-- dim E₁^{−q,j}(G) = Σ_{|S| = q, v(S) = j} wt(S)（`alg:state-dimensions`）。 -/
def stateDim (q j : ℕ) : ℕ :=
  ∑ S ∈ Finset.univ.filter fun S : Finset E => S.card = q ∧ (G.support S).card = j, G.wt phi S

/-- β_{p,q}=dim E₁^{−q,q−p}, since contributing states satisfy v(S)≤|S|. -/
theorem betti_eq_stateDim {p q : ℕ} (hp : p ≤ q) : G.betti p q = G.stateDim q (q - p) := by
  unfold betti stateDim
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hw : G.wt phi S = 0
  · simp [hw]
  · have := G.card_support_le S hw
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro ⟨h1, h2⟩; omega

/-- The total first-page dimension is Q. -/
theorem sum_stateDim_eq_Q :
    ∑ q ∈ Finset.range (Fintype.card E + 1), ∑ j ∈ Finset.range (Fintype.card V + 1),
      G.stateDim q j = G.Q := by
  unfold stateDim
  simp_rw [Finset.sum_filter]
  rw [Q, QOn, Finset.powerset_univ]
  calc ∑ q ∈ Finset.range (Fintype.card E + 1), ∑ j ∈ Finset.range (Fintype.card V + 1),
        ∑ S : Finset E, (if S.card = q ∧ (G.support S).card = j then G.wt phi S else 0)
      = ∑ q ∈ Finset.range (Fintype.card E + 1), ∑ S : Finset E,
          ∑ j ∈ Finset.range (Fintype.card V + 1),
            (if S.card = q ∧ (G.support S).card = j then G.wt phi S else 0) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_comm
    _ = ∑ S : Finset E, ∑ q ∈ Finset.range (Fintype.card E + 1),
          ∑ j ∈ Finset.range (Fintype.card V + 1),
            (if S.card = q ∧ (G.support S).card = j then G.wt phi S else 0) := Finset.sum_comm
    _ = ∑ S : Finset E, G.wt phi S := by
      refine Finset.sum_congr rfl fun S _ => ?_
      have hq : S.card ∈ Finset.range (Fintype.card E + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ S))
      have hj : (G.support S).card ∈ Finset.range (Fintype.card V + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ _))
      rw [Finset.sum_eq_single_of_mem _ hq, Finset.sum_eq_single_of_mem _ hj]
      · simp
      · intro j _ hj'; simp [Ne.symm hj']
      · intro q _ hq'
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [ite_eq_right_iff]
        rintro ⟨h, -⟩
        exact absurd h.symm hq'

/-- Nonzero first-page terms satisfy 0≤q−j≤ρ. -/
theorem stateDim_eq_zero_of {q j : ℕ} (h : q < j ∨ G.rho < q - j) : G.stateDim q j = 0 := by
  unfold stateDim
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [Finset.mem_filter] at hS
  by_contra hw
  have h1 := G.card_support_le S hw
  have h2 := G.card_le_card_support_add_rho ((G.wt_phi_ne_zero_iff S).1 hw)
  omega

end Multigraph

end BPFixedPoints
