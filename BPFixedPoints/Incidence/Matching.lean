import BPFixedPoints.Incidence.StateCohomology
import Mathlib.Combinatorics.Hall.Finite

/-!
# Matching vertices to incident edges

After removing one vertex from each tree component, match all remaining
vertices to distinct incident edges. Prove Hall's condition on proper vertex
subsets of connected graphs using injectivity of the difference map after
extension by zero. Self-loops and parallel edges are allowed.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Edges with at least one endpoint in a vertex set. -/
noncomputable def incidentEdges (S : Finset V) : Finset E :=
  Finset.univ.filter fun e => ∃ v ∈ S, G.Incident e v

@[simp] theorem mem_incidentEdges (S : Finset V) (e : E) :
    e ∈ G.incidentEdges S ↔ G.fst e ∈ S ∨ G.snd e ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv, h | h⟩ := (Finset.mem_filter.mp h).2
    · exact Or.inl (h.symm ▸ hv)
    · exact Or.inr (h.symm ▸ hv)
  · rintro (h | h)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.fst e, h, Or.inl rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.snd e, h, Or.inr rfl⟩

@[simp] theorem incidentEdges_univ : G.incidentEdges Finset.univ = Finset.univ := by
  ext e
  simp

/-- On a connected graph the difference map is injective on functions supported in a proper vertex subset, so the number of incident edges is at least the subset size. -/
theorem card_le_incidentEdges_of_ne_univ (hc : G.Connected) (S : Finset V)
    (hS : S ≠ Finset.univ) : S.card ≤ (G.incidentEdges S).card := by
  classical
  let ext : (S → ℚ) → V → ℚ := fun x v => if hv : v ∈ S then x ⟨v, hv⟩ else 0
  let d : (S → ℚ) →ₗ[ℚ] (G.incidentEdges S → ℚ) :=
    { toFun := fun x e => ext x (G.fst e) - ext x (G.snd e)
      map_add' := by
        intro x y
        funext e
        simp only [ext, Pi.add_apply]
        split_ifs <;> ring
      map_smul' := by
        intro c x
        funext e
        simp only [ext, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> ring }
  have hd : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have he : ∀ e, ext x (G.fst e) = ext x (G.snd e) := by
      intro e
      by_cases h : e ∈ G.incidentEdges S
      · have := congrFun hx ⟨e, h⟩
        exact sub_eq_zero.mp this
      · rw [G.mem_incidentEdges] at h
        push Not at h
        simp [ext, h.1, h.2]
    have hr : ∀ a b, G.Reach Finset.univ a b → ext x a = ext x b := by
      intro a b hab
      induction hab with
      | refl => rfl
      | @tail b c hab hbc ih =>
          rcases hbc with ⟨e, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact ih.trans (by simpa [← h1, ← h2] using he e)
          · exact ih.trans (by simpa [← h1, ← h2] using (he e).symm)
    obtain ⟨v₀, hv₀⟩ : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hS (Finset.eq_univ_of_forall h)
    funext v
    have h := hr v v₀ (hc.2.2 v (Finset.mem_univ _) v₀ (Finset.mem_univ _))
    simpa [ext, v.property, hv₀] using h
  have := LinearMap.finrank_le_finrank_of_injective hd
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using this

/-- A proper vertex subset of a connected graph, or the full vertex set when its size is at most the edge count, has distinct incident edges. -/
theorem exists_incident_injection (hc : G.Connected) (S : Finset V)
    (hS : S ≠ Finset.univ ∨ Fintype.card V ≤ Fintype.card E) :
    ∃ f : S → E, Function.Injective f ∧ ∀ v, G.Incident (f v) v := by
  classical
  let t : S → Finset E := fun v => Finset.univ.filter fun e => G.Incident e v
  have hhall : ∀ s : Finset S, s.card ≤ (s.biUnion t).card := by
    intro s
    let T : Finset V := s.image Subtype.val
    have hcard : T.card = s.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hinc : G.incidentEdges T = s.biUnion t := by
      ext e
      simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
        T, Finset.mem_image, Finset.mem_biUnion, t]
      aesop
    rw [← hinc, ← hcard]
    by_cases hT : T = Finset.univ
    · have hST : S = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro v
        have : v ∈ T := hT ▸ Finset.mem_univ v
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp this
        exact w.property
      have hVE := hS.resolve_left (not_not.mpr hST)
      simpa [hT] using hVE
    · exact G.card_le_incidentEdges_of_ne_univ hc T hT
  obtain ⟨f, hf, hfi⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hhall
  exact ⟨f, hf, fun v => (Finset.mem_filter.mp (hfi v)).2⟩

/-- Representative vertex of each component. -/
noncomputable def compRoot (K : G.Comp) : V := Quotient.out K

@[simp] theorem compOf_compRoot (K : G.Comp) : G.compOf (G.compRoot K) = K :=
  Quotient.out_eq K

theorem compRoot_injective : Function.Injective G.compRoot := by
  intro K L h
  simpa using congrArg G.compOf h

/-- Set of representative vertices of tree components. -/
noncomputable def treeRoots : Finset V :=
  (Finset.univ.filter G.IsTreeComp).image G.compRoot

theorem card_treeRoots : G.treeRoots.card = G.tau := by
  rw [treeRoots, Finset.card_image_of_injective _ G.compRoot_injective]
  rfl

/-- Vertices other than tree-component representatives; retain every vertex in cyclic components. -/
noncomputable def matchingVerts : Finset V := G.treeRootsᶜ

theorem card_matchingVerts : G.matchingVerts.card = Fintype.card V - G.tau := by
  rw [matchingVerts, Finset.card_compl, G.card_treeRoots]

theorem card_matchingVerts_add_tau : G.matchingVerts.card + G.tau = Fintype.card V := by
  rw [G.card_matchingVerts, Nat.sub_add_cancel G.tau_le_card]

theorem compRoot_notMem_matchingVerts {K : G.Comp} (hK : G.IsTreeComp K) :
    G.compRoot K ∉ G.matchingVerts := by
  simp only [matchingVerts, Finset.mem_compl, not_not]
  exact Finset.mem_image.mpr ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK⟩, rfl⟩

theorem exists_component_incident_injection (K : G.Comp) :
    ∃ f : {v : V // v ∈ G.matchingVerts ∧ G.compOf v = K} → E,
      Function.Injective f ∧ (∀ v, G.Incident (f v) v) ∧
        ∀ v, f v ∈ G.compEdges K := by
  classical
  let S : Finset {v // v ∈ G.compVerts K} :=
    Finset.univ.filter fun v => v.val ∈ G.matchingVerts
  have hS : S ≠ Finset.univ ∨
      Fintype.card {v // v ∈ G.compVerts K} ≤ Fintype.card {e // e ∈ G.compEdges K} := by
    by_cases hK : G.IsTreeComp K
    · left
      intro h
      have hr : G.compRoot K ∈ G.compVerts K := by simp [mem_compVerts]
      have hm : (⟨G.compRoot K, hr⟩ : {v // v ∈ G.compVerts K}) ∈ S :=
        h ▸ Finset.mem_univ _
      exact G.compRoot_notMem_matchingVerts hK (Finset.mem_filter.mp hm).2
    · right
      simpa only [Fintype.card_coe, hK, ↓reduceIte, add_zero] using
        G.card_compVerts_le' K
  obtain ⟨f, hfinj, hfinc⟩ :=
    (G.compGraph K).exists_incident_injection (G.compGraph_connected K) S hS
  let lift : {v : V // v ∈ G.matchingVerts ∧ G.compOf v = K} → S := fun v =>
    ⟨⟨v.val, mem_compVerts.mpr v.property.2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.property.1⟩⟩
  refine ⟨fun v => (f (lift v)).val, ?_, ?_, fun v => (f (lift v)).property⟩
  · intro v w h
    have h' := hfinj (Subtype.ext h)
    exact Subtype.ext (congrArg (fun z : S => z.val.val) h')
  · intro v
    rcases hfinc (lift v) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

/-- After deleting one vertex per tree component, match the remaining vertices to distinct incident edges. -/
theorem exists_vertex_edge_matching :
    ∃ f : G.matchingVerts → E, Function.Injective f ∧ ∀ v, G.Incident (f v) v := by
  classical
  choose f hfinj hfinc hfcomp using G.exists_component_incident_injection
  let lift (v : G.matchingVerts) :
      {w : V // w ∈ G.matchingVerts ∧ G.compOf w = G.compOf v} := ⟨v, v.property, rfl⟩
  have hf : ∀ (K L : G.Comp)
      (v : {v : V // v ∈ G.matchingVerts ∧ G.compOf v = K})
      (w : {v : V // v ∈ G.matchingVerts ∧ G.compOf v = L}),
      f K v = f L w → v.val = w.val := by
    intro K L v w h
    have hK : K = L := by
      have hv := mem_compEdges.mp (hfcomp K v)
      have hw := mem_compEdges.mp (hfcomp L w)
      rw [h] at hv
      exact hv.symm.trans hw
    subst L
    exact congrArg Subtype.val (hfinj K h)
  refine ⟨fun v => f (G.compOf v) (lift v), ?_, fun v => hfinc _ (lift v)⟩
  intro v w h
  exact Subtype.ext (hf _ _ (lift v) (lift w) h)

/-- Incident-edge embedding used for the dimension lower bound. -/
noncomputable def vertexEdgeMatching : G.matchingVerts ↪ E :=
  ⟨G.exists_vertex_edge_matching.choose, G.exists_vertex_edge_matching.choose_spec.1⟩

theorem incident_vertexEdgeMatching (v : G.matchingVerts) :
    G.Incident (G.vertexEdgeMatching v) v :=
  G.exists_vertex_edge_matching.choose_spec.2 v

end BPFixedPoints.Multigraph
