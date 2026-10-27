import BPFixedPoints.Incidence.IncidenceVertexMapStateInjective
import BPFixedPoints.Incidence.IncidenceVertexMapCycleScalars

/-!
# The state formula for vertex maps on non-colliding states

Let `φ : VertexMap G H` (edges unchanged, vertices possibly identified) and let `S` be an edge set
such that the vertex function is injective on the vertex support `G.support S`. Then the support of
`S` in `H` is `φ(G.support S)`, with the same degrees, and a state `⟨S, κ⟩` of `H` restricts to the
state `statePullOn ⟨S, κ⟩` of `G`: the local index at `v ∈ G.support S` is the index of `κ` at
`φ v`, and every other vertex carries the `H⁰` index. This is a bijection between the states of
`G` and of `H` with edge set `S` (both are determined by their values on the support).

**Main result** (`incidenceTorFullState_vertexMap_apply_of_injOn`): for every Tor class `y` of `G`
and every state `b` of `H` whose edge set has injective vertex support in `G`,
`H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
  vertexMapSign ℂ φ.vertex (G.support b.1) * G.incidenceTorFullState p y (φ.statePullOn b h)`.
The sign is the Koszul sign of carrying the degree-one factors at the support vertices along `φ`,
relative to the enumerations `Fintype.equivFin V` and `Fintype.equivFin W`; for a vertex bijection
it is `vertexPermSign`. Together with the collision vanishing and the edge-set preservation of
`IncidenceVertexMapSupport` this describes the Tor map of a vertex map completely on full state
vectors (`incidenceTorFullState_vertexMap_apply_of_mem_edgeSetPiece`).

The Tor map is Mathlib's functoriality of the left derived functor; the formula is proved by
comparing it with Tor maps whose state formulas are known, and by proving that the concrete maps
agree:
* the inclusion of the subgraph of the edges in `S` (an edge map with injective edge function,
  `EdgeMap.incidenceTorFullState_edgeMap`); the Tor maps of `φ` and of its restriction commute with
  these inclusions in every degree (`incidenceTorMap_edgeRestrictInclusion_all`, from the
  naturality of derived ring maps `leftDerived_map_comp_derivedRingMap`), and the classes supported
  on `S` come from the subgraph (`EdgeMap.exists_incidenceTorEdgeMap_eq`);
* in the subgraph every vertex outside the support of `S` is isolated; the inclusion of the vertex
  support and its composite with `φ` are injective vertex maps, whose state formula is
  `incidenceTorFullState_vertexMap_of_injective` (pullback of Čech chains along a coordinate
  projection), and the first one is surjective on Tor
  (`incidenceTorFullState_vertexMap_apply_of_supported`);
* the signs compose by `vertexMapSign_comp`.

**Degree zero.** For a cycle union `S` whose support is not collided, the scalar of `S` is the sign:
`cycleScalar_eq_vertexMapSign`; hence `z_C ↦ vertexMapSign ℂ φ.vertex (G.support C) • z_{φ(C)}`
for every simple cycle `C` whose vertices are not identified (`incidenceTorMap_cycleClass_eq`,
`cycleAlgebraHom_X_eq`), refining `exists_ne_zero_cycleAlgebraHom_X`. The restriction of states is
a bijection on each non-colliding edge set (`stateFibreEquiv`), and on a class whose full state is
one basis state the formula reads `single a r ↦ single (statePushOn a) (± r)`
(`incidenceTorFullState_vertexMap_of_single`).

Not covered here: orientation signs of edges and characteristic-free versions (the reduction to
the edge-set component uses the edge-sign eigenspace decomposition over `ℂ`). The geometric side
(the pullback of exterior cohomology along the coordinate map `a_φ`) is in `VertexMapPullbackTwist`
and its comparison with this formula in `VertexMapPullbackExterior`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory Finsupp CechProduct MvPolynomial

/-! ## Resolution states by their values -/

section States

variable {V E : Type} [DecidableEq V] {G : Multigraph V E}

/-- Two resolution states with the same edge set and the same local index values are equal. -/
theorem incResolutionBasis_ext {b b' : G.IncResolutionBasis} (h1 : b.1 = b'.1)
    (h2 : ∀ v, (b.2 v).val = (b'.2 v).val) : b = b' := by
  obtain ⟨S, κ⟩ := b
  obtain ⟨S', κ'⟩ := b'
  dsimp only at h1 h2
  subst h1
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  funext v
  exact Fin.ext (h2 v)

/-- Equal resolution states have the same local index values. -/
theorem incResolutionBasis_val_eq {b b' : G.IncResolutionBasis} (h : b = b') (v : V) :
    (b.2 v).val = (b'.2 v).val := by
  subst h
  rfl

/-- Transport of a state index along an equality of twists keeps its values. -/
theorem hBasis_cast_val {d d' : V → ℕ} (h : d = d') (κ : HBasis d) (v : V) :
    ((cast (congrArg HBasis h) κ) v).val = (κ v).val := by
  subst h
  rfl

end States

/-! ## Edge maps with injective edge function -/

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

theorem stateIndex_snd_val (a : G.IncResolutionBasis) (h : Set.InjOn φ.edge a.1) (v : V) :
    ((φ.stateIndex a h).2 v).val = (a.2 v).val :=
  hBasis_cast_val (φ.deg_edgeSet h).symm a.2 v

/-- For an injective edge function the image state index is injective. -/
theorem stateIndex_injective (hinj : Function.Injective φ.edge) {a a' : G.IncResolutionBasis}
    (h : φ.stateIndex a hinj.injOn = φ.stateIndex a' hinj.injOn) : a = a' := by
  have h1 : a.1 = a'.1 := Finset.image_injective hinj (congrArg Sigma.fst h)
  refine incResolutionBasis_ext h1 fun v => ?_
  rw [← φ.stateIndex_snd_val a hinj.injOn, ← φ.stateIndex_snd_val a' hinj.injOn]
  exact incResolutionBasis_val_eq h v

/-- Coefficients of the state map at image states, for an injective edge function. -/
theorem stateMap_apply_stateIndex (R : Type) [CommRing R] (hinj : Function.Injective φ.edge)
    (z : G.IncResolutionBasis →₀ R) (a : G.IncResolutionBasis) :
    φ.stateMap R z (φ.stateIndex a hinj.injOn) = (φ.wedgeSign a.1 : R) * z a := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single a' r =>
    rw [stateMap_single_of_injOn _ R a' hinj.injOn]
    by_cases ha : a' = a
    · subst ha
      rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne (Ne.symm ha), mul_zero]
      intro h
      exact ha (φ.stateIndex_injective hinj h.symm)

/-- **Classes supported on image states come from the source.** For an injective edge function,
every Tor class of `H` whose full state vanishes off the image states is the image of a Tor class
of `G`. -/
theorem exists_incidenceTorEdgeMap_eq (hinj : Function.Injective φ.edge) (p : ℕ)
    (y : H.incidenceTor p)
    (hy : ∀ b, (∀ a, φ.stateIndex a hinj.injOn ≠ b) → H.incidenceTorFullState p y b = 0) :
    ∃ t, φ.incidenceTorEdgeMap p t = y := by
  let z : G.IncResolutionBasis →₀ ℂ := Finsupp.equivFunOnFinite.symm fun a =>
    (φ.wedgeSign a.1 : ℂ) * H.incidenceTorFullState p y (φ.stateIndex a hinj.injOn)
  have hz : ∀ a : G.IncResolutionBasis, G.incResolutionDegree a ≠ p → z a = 0 := by
    intro a ha
    change (φ.wedgeSign a.1 : ℂ) * H.incidenceTorFullState p y (φ.stateIndex a hinj.injOn) = 0
    rw [H.incidenceTorFullState_apply_of_ne p y _ (by rwa [incResolutionDegree_stateIndex]),
      mul_zero]
  obtain ⟨t, ht⟩ := G.exists_incidenceTorFullState_eq p z hz
  refine ⟨t, H.incidenceTorFullState_injective p ?_⟩
  rw [incidenceTorFullState_edgeMap, ht]
  ext b
  by_cases hb : ∃ a, φ.stateIndex a hinj.injOn = b
  · obtain ⟨a, rfl⟩ := hb
    rw [stateMap_apply_stateIndex _ ℂ hinj]
    change (φ.wedgeSign a.1 : ℂ) * ((φ.wedgeSign a.1 : ℂ) *
      H.incidenceTorFullState p y (φ.stateIndex a hinj.injOn)) = _
    rw [← mul_assoc, ← Int.cast_mul, φ.wedgeSign_mul_self hinj.injOn, Int.cast_one, one_mul]
  · push Not at hb
    rw [hy b hb]
    apply stateMap_apply_eq_zero
    intro a h' hab
    exact absurd hab (hb a)

end EdgeMap

/-! ## Subgraph inclusions -/

section Subgraph

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

/-- The inclusion of a subgraph preserves the order of edges, so its wedge signs are one. -/
theorem wedgeSign_edgeRestrictInclusion (G : Multigraph V E) (A : Finset E)
    (T : Finset {e // e ∈ A}) : (G.edgeRestrictInclusion A).wedgeSign T = 1 := by
  rw [EdgeMap.wedgeSign_of_injOn _ (G.edgeRestrictInclusion_injOn A _)]
  have h : (G.edgeRestrictInclusion A).inversions T = 0 := by
    unfold EdgeMap.inversions
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right_iff]
    rintro ⟨hab, hba⟩
    exact absurd hab (not_lt_of_gt hba)
  rw [h, pow_zero]

/-- A state of `G` with edge set `A`, as a state of the subgraph of the edges in `A`. -/
def edgeRestrictState (G : Multigraph V E) (A : Finset E) (b : G.IncResolutionBasis)
    (hb : b.1 = A) : (G.edgeRestrict A).IncResolutionBasis :=
  ⟨Finset.univ, fun v => Fin.cast (by rw [edgeRestrict_deg_univ, hb]) (b.2 v)⟩

/-- The subgraph state goes back to the state under the inclusion. -/
theorem stateIndex_edgeRestrictState (G : Multigraph V E) (A : Finset E)
    (b : G.IncResolutionBasis) (hb : b.1 = A) :
    (G.edgeRestrictInclusion A).stateIndex (G.edgeRestrictState A b hb)
        ((G.edgeRestrictInclusion_injOn A _)) = b := by
  refine incResolutionBasis_ext ?_ fun v => ?_
  · rw [EdgeMap.stateIndex_fst, edgeRestrictState, edgeRestrictInclusion_edgeSet_univ, hb]
  · rw [EdgeMap.stateIndex_snd_val]
    rfl

/-- Every edge of the subgraph of the edges in `A` has its endpoints in the support of `A`. -/
theorem edgeRestrict_endpoints_mem_support (G : Multigraph V E) (A : Finset E)
    (e : {e // e ∈ A}) :
    (G.edgeRestrict A).fst e ∈ (G.edgeRestrict A).support Finset.univ ∧
      (G.edgeRestrict A).snd e ∈ (G.edgeRestrict A).support Finset.univ := by
  rw [G.edgeRestrict_support_univ A]
  exact ⟨G.fst_mem_support e.property, G.mem_support_of_incident e.property (Or.inr rfl)⟩

end Subgraph

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Naturality for subgraph inclusions in every degree -/

/-- **Naturality for subgraph inclusions in every homological degree.** The Tor maps of a vertex map
and of its restriction to the subgraphs of the edges in `A` commute with the Tor maps of the
inclusions. -/
theorem incidenceTorMap_edgeRestrictInclusion_all (A : Finset E) (p : ℕ)
    (t : (G.edgeRestrict A).incidenceTor p) :
    φ.incidenceTorMap p ((G.edgeRestrictInclusion A).incidenceTorEdgeMap p t) =
      (H.edgeRestrictInclusion A).incidenceTorEdgeMap p
        ((φ.edgeRestrict A).incidenceTorMap p t) := by
  have h := leftDerived_map_comp_derivedRingMap (G.edgeRestrictInclusion A).coeffRingHom
    constantCoeff constantCoeff (G.edgeRestrictInclusion A).constantCoeff_comp_coeffRingHom
    (φ.edgeRestrict A).incidenceModuleHom φ.incidenceModuleHom
    (G.edgeRestrictInclusion A).incidenceModuleMap (H.edgeRestrictInclusion A).incidenceModuleMap
    (fun x => (φ.incidenceHom_edgeRestrictInclusion A x).symm) p
  exact (congrArg (fun F => F.hom t) h).symm

/-! ## The restricted state -/

/-- **The restriction of a resolution state** of `H` to `G`, for an edge set on whose vertex
support in `G` the vertex function is injective: the edge set is kept, the local index at a support
vertex `v` is the index at `φ v`, and every other vertex carries the `H⁰` index. -/
def statePullOn (b : H.IncResolutionBasis) (h : Set.InjOn φ.vertex (G.support b.1)) :
    G.IncResolutionBasis :=
  ⟨b.1, fun v => if hv : v ∈ G.support b.1 then
      Fin.cast (congrArg phi (φ.deg_vertex_of_injOn h hv)) (b.2 (φ.vertex v))
    else ⟨0, by
      have h0 : G.deg b.1 v = 0 := by rw [mem_support_iff] at hv; omega
      rw [h0, phi_zero]
      exact Nat.one_pos⟩⟩

@[simp] theorem statePullOn_fst (b : H.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support b.1)) :
    (φ.statePullOn b h).1 = b.1 := rfl

theorem statePullOn_snd_val (b : H.IncResolutionBasis) (h : Set.InjOn φ.vertex (G.support b.1))
    (v : V) : ((φ.statePullOn b h).2 v).val =
      if v ∈ G.support b.1 then (b.2 (φ.vertex v)).val else 0 := by
  unfold statePullOn
  dsimp only
  split_ifs <;> rfl

/-- Restriction of states with a non-colliding edge set is injective. -/
theorem statePullOn_injective {b b' : H.IncResolutionBasis} (h : Set.InjOn φ.vertex (G.support b.1))
    (h' : Set.InjOn φ.vertex (G.support b'.1)) (hbb : φ.statePullOn b h = φ.statePullOn b' h') :
    b = b' := by
  have h1 : b.1 = b'.1 := by
    have e := congrArg Sigma.fst hbb
    exact e
  refine incResolutionBasis_ext h1 fun w => ?_
  by_cases hw : w ∈ H.support b.1
  · obtain ⟨v, hv, rfl⟩ := φ.exists_mem_support_of_mem_support hw
    have hv' : v ∈ G.support b'.1 := h1 ▸ hv
    have e := incResolutionBasis_val_eq hbb v
    rw [statePullOn_snd_val, statePullOn_snd_val] at e
    simp only [hv, hv', ↓reduceIte] at e
    exact e
  · have hw' : w ∉ H.support b'.1 := h1 ▸ hw
    rw [mem_support_iff, not_lt, Nat.le_zero] at hw hw'
    have hlt := (b.2 w).isLt
    have hlt' := (b'.2 w).isLt
    have e1 : phi (H.deg b.1 w) = 1 := by rw [hw, phi_zero]
    have e2 : phi (H.deg b'.1 w) = 1 := by rw [hw', phi_zero]
    omega

/-! ## Vertex maps whose edges lie in the support of one edge set -/

/-- If every edge has its endpoints in the support of `S₀`, the support of every edge set lies in
the support of `S₀`. -/
theorem support_subset_of_endpoints {S₀ : Finset E}
    (hE : ∀ e, G.fst e ∈ G.support S₀ ∧ G.snd e ∈ G.support S₀) (T : Finset E) :
    G.support T ⊆ G.support S₀ := by
  intro v hv
  rw [mem_support_iff] at hv
  unfold deg at hv
  obtain ⟨e, -, he⟩ := Finset.exists_lt_of_sum_lt (s := T) (f := fun _ => 0)
    (g := fun e => G.endCount e v) (by simpa using hv)
  unfold endCount at he
  by_cases h1 : G.fst e = v
  · exact h1 ▸ (hE e).1
  · by_cases h2 : G.snd e = v
    · exact h2 ▸ (hE e).2
    · simp [h1, h2] at he

/-- **State formula when every edge lies in the support of `S₀`.** If every edge of `G` has its
endpoints in the support of `S₀` and the vertex function is injective there, the Tor map of `φ`
satisfies the state formula at every state of `H`. -/
theorem incidenceTorFullState_vertexMap_apply_of_supported {S₀ : Finset E}
    (hE : ∀ e, G.fst e ∈ G.support S₀ ∧ G.snd e ∈ G.support S₀)
    (hinj : Set.InjOn φ.vertex (G.support S₀)) (p : ℕ) (y : G.incidenceTor p)
    (b : H.IncResolutionBasis) (h : Set.InjOn φ.vertex (G.support b.1)) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
      vertexMapSign ℂ φ.vertex (G.support b.1) *
        G.incidenceTorFullState p y (φ.statePullOn b h) := by
  set incl := G.supportInclusion S₀ hE
  have hincl : Function.Injective incl.vertex := Subtype.val_injective
  have hk : Function.Injective (incl.trans φ).vertex := fun a a' haa =>
    Subtype.ext (hinj a.property a'.property haa)
  obtain ⟨y'', rfl⟩ := incl.incidenceTorMap_surjective_of_injective hincl p y
  rw [← incidenceTorMap_trans, (incl.trans φ).incidenceTorFullState_vertexMap_apply_of_injective hk,
    incl.incidenceTorFullState_vertexMap_apply_of_injective hincl]
  have hsupp : G.support b.1 ⊆ G.support S₀ := support_subset_of_endpoints hE b.1
  -- the two restricted states agree
  have hstate : (incl.trans φ).statePull hk b = incl.statePull hincl (φ.statePullOn b h) := by
    refine incResolutionBasis_ext rfl fun a => ?_
    rw [statePull_snd_val, statePull_snd_val, statePullOn_snd_val]
    change (b.2 (φ.vertex a.val)).val =
      if a.val ∈ G.support b.1 then (b.2 (φ.vertex a.val)).val else 0
    split_ifs with ha
    · rfl
    · have hdeg := (incl.trans φ).deg_vertex_of_injective hk b.1 a
      rw [supportGraph_deg] at hdeg
      rw [mem_support_iff, not_lt, Nat.le_zero] at ha
      have hlt := (b.2 (φ.vertex a.val)).isLt
      have h1 : phi (H.deg b.1 (φ.vertex a.val)) = 1 := by
        change phi (H.deg b.1 ((incl.trans φ).vertex a)) = 1
        rw [hdeg, ha, phi_zero]
      omega
  -- the signs compose
  have himage : (twistSupport ((G.supportGraph S₀ hE).deg b.1)).image Subtype.val =
      G.support b.1 := by
    ext v
    simp only [Finset.mem_image, mem_twistSupport, supportGraph_deg, mem_support_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Nat.pos_of_ne_zero ha
    · intro hv
      exact ⟨⟨v, hsupp ((mem_support_iff G).2 hv)⟩, Nat.pos_iff_ne_zero.1 hv, rfl⟩
  have hsign : vertexMapSign ℂ (incl.trans φ).vertex
      (twistSupport ((G.supportGraph S₀ hE).deg b.1)) =
      vertexMapSign ℂ φ.vertex (G.support b.1) *
        vertexMapSign ℂ incl.vertex (twistSupport ((G.supportGraph S₀ hE).deg b.1)) := by
    change vertexMapSign ℂ (φ.vertex ∘ Subtype.val) _ = _
    rw [vertexMapSign_comp ℂ Subtype.val φ.vertex _ Subtype.val_injective.injOn
      (by rw [himage]; exact h), himage]
    rfl
  rw [hstate, hsign, statePullOn_fst, mul_assoc]

/-! ## The general state formula -/

/-- **State formula for vertex maps on non-colliding states.** Let `b` be a state of `H` whose edge
set has a vertex support in `G` on which the vertex function is injective. The coefficient of the
image of a Tor class at `b` is the Koszul sign `vertexMapSign ℂ φ.vertex (G.support b.1)` times the
coefficient of the class at the restricted state `φ.statePullOn b h`. -/
theorem incidenceTorFullState_vertexMap_apply_of_injOn (p : ℕ) (y : G.incidenceTor p)
    (b : H.IncResolutionBasis) (h : Set.InjOn φ.vertex (G.support b.1)) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
      vertexMapSign ℂ φ.vertex (G.support b.1) *
        G.incidenceTorFullState p y (φ.statePullOn b h) := by
  obtain ⟨S, κ⟩ := b
  -- reduce to the edge-set component of `S`
  rw [φ.incidenceTorFullState_vertexMap_component p y ⟨S, κ⟩]
  have hcomp : G.incidenceTorFullState p y (φ.statePullOn ⟨S, κ⟩ h) =
      G.incidenceTorFullState p (G.incidenceTorEdgeSetComponent p S y)
        (φ.statePullOn ⟨S, κ⟩ h) := by
    rw [incidenceTorFullState_edgeSetComponent, Finsupp.filter_apply]
    simp only [statePullOn_fst, ↓reduceIte]
  rw [hcomp]
  set yS := G.incidenceTorEdgeSetComponent p S y
  -- the component comes from the subgraph of the edges in `S`
  have hιG : Function.Injective (G.edgeRestrictInclusion S).edge := Subtype.val_injective
  have hιH : Function.Injective (H.edgeRestrictInclusion S).edge := Subtype.val_injective
  obtain ⟨t, ht⟩ := (G.edgeRestrictInclusion S).exists_incidenceTorEdgeMap_eq hιG p yS (by
    intro b₀ hb₀
    rw [incidenceTorFullState_edgeSetComponent, Finsupp.filter_apply]
    split_ifs with h₀
    · exact absurd (G.stateIndex_edgeRestrictState S b₀ h₀) (hb₀ _)
    · rfl)
  rw [← ht, incidenceTorMap_edgeRestrictInclusion_all, EdgeMap.incidenceTorFullState_edgeMap,
    EdgeMap.incidenceTorFullState_edgeMap]
  -- the state of `H` and its restriction come from the subgraphs
  set aH := H.edgeRestrictState S ⟨S, κ⟩ rfl
  have hL : (H.edgeRestrictInclusion S).stateMap ℂ ((H.edgeRestrict S).incidenceTorFullState p
        ((φ.edgeRestrict S).incidenceTorMap p t)) ⟨S, κ⟩ =
      (H.edgeRestrict S).incidenceTorFullState p ((φ.edgeRestrict S).incidenceTorMap p t) aH := by
    conv_lhs => rw [← H.stateIndex_edgeRestrictState S ⟨S, κ⟩ rfl]
    rw [EdgeMap.stateMap_apply_stateIndex _ ℂ hιH, wedgeSign_edgeRestrictInclusion, Int.cast_one,
      one_mul]
  rw [hL]
  have hsuppA : (G.edgeRestrict S).support Finset.univ = G.support S :=
    G.edgeRestrict_support_univ S
  have hinjA : Set.InjOn (φ.edgeRestrict S).vertex ((G.edgeRestrict S).support Finset.univ) := by
    rw [hsuppA, edgeRestrict_vertex]
    exact h
  have hA := (φ.edgeRestrict S).incidenceTorFullState_vertexMap_apply_of_supported
    (G.edgeRestrict_endpoints_mem_support S) hinjA p t aH hinjA
  rw [hA]
  have hpull : φ.statePullOn ⟨S, κ⟩ h =
      (G.edgeRestrictInclusion S).stateIndex ((φ.edgeRestrict S).statePullOn aH hinjA)
        (G.edgeRestrictInclusion_injOn S _) := by
    refine incResolutionBasis_ext ?_ fun v => ?_
    · change S = (G.edgeRestrictInclusion S).edgeSet Finset.univ
      rw [edgeRestrictInclusion_edgeSet_univ]
    · rw [EdgeMap.stateIndex_snd_val, statePullOn_snd_val, statePullOn_snd_val]
      change _ = if v ∈ (G.edgeRestrict S).support Finset.univ then (κ (φ.vertex v)).val else 0
      rw [hsuppA]
  rw [hpull, EdgeMap.stateMap_apply_stateIndex _ ℂ hιG, wedgeSign_edgeRestrictInclusion,
    Int.cast_one, one_mul]
  change vertexMapSign ℂ φ.vertex ((G.edgeRestrict S).support Finset.univ) * _ = _
  rw [hsuppA]

/-- **The Tor map of a vertex map on full state vectors.** For a class `y` supported on the edge
set `S` and a state `b` of `H`: the coefficient of the image at `b` is zero unless `b` has edge set
`S`; if `b` has edge set `S` and the vertex function collides on `G.support S` it is zero; and
otherwise it is given by the state formula. -/
theorem incidenceTorFullState_vertexMap_apply_of_mem_edgeSetPiece {p : ℕ} {S : Finset E}
    {y : G.incidenceTor p} (hy : y ∈ G.incidenceTorEdgeSetPiece p S) (b : H.IncResolutionBasis) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
      if h : b.1 = S ∧ Set.InjOn φ.vertex (G.support b.1) then
        vertexMapSign ℂ φ.vertex (G.support b.1) *
          G.incidenceTorFullState p y (φ.statePullOn b h.2)
      else 0 := by
  split_ifs with h
  · exact φ.incidenceTorFullState_vertexMap_apply_of_injOn p y b h.2
  · by_cases hb : b.1 = S
    · have hcol : ¬ Set.InjOn φ.vertex (G.support S) := fun hinj => h ⟨hb, hb ▸ hinj⟩
      rw [φ.incidenceTorMap_eq_zero_of_not_injOn hcol hy, map_zero, Finsupp.zero_apply]
    · exact (H.mem_incidenceTorEdgeSetPiece_iff p S _).1
        (φ.incidenceTorMap_mem_edgeSetPiece hy) b hb

/-! ## The restriction as a bijection of states -/

/-- The local index map of the restriction on the states of one non-colliding edge set. -/
def hPullOn (S : Finset E) (h : Set.InjOn φ.vertex (G.support S)) (κ : HBasis (H.deg S)) :
    HBasis (G.deg S) :=
  (φ.statePullOn ⟨S, κ⟩ h).2

theorem hPullOn_injective (S : Finset E) (h : Set.InjOn φ.vertex (G.support S)) :
    Function.Injective (φ.hPullOn S h) := by
  intro κ κ' hκ
  have hs : φ.statePullOn ⟨S, κ⟩ h = φ.statePullOn ⟨S, κ'⟩ h := by
    change (⟨S, φ.hPullOn S h κ⟩ : G.IncResolutionBasis) = ⟨S, φ.hPullOn S h κ'⟩
    rw [hκ]
  have e := φ.statePullOn_injective h h hs
  exact eq_of_heq (Sigma.mk.inj_iff.mp e).2

/-- **The restriction is a bijection** between the states of `H` and of `G` with a non-colliding
edge set `S`. -/
noncomputable def stateFibreEquiv (S : Finset E) (h : Set.InjOn φ.vertex (G.support S)) :
    HBasis (H.deg S) ≃ HBasis (G.deg S) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).2
    ⟨φ.hPullOn_injective S h, φ.card_stateFibre_eq_of_injOn h⟩)

@[simp] theorem stateFibreEquiv_apply (S : Finset E) (h : Set.InjOn φ.vertex (G.support S))
    (κ : HBasis (H.deg S)) : φ.stateFibreEquiv S h κ = φ.hPullOn S h κ := rfl

/-- The state of `H` restricting to a given state of `G` with a non-colliding edge set. -/
noncomputable def statePushOn (a : G.IncResolutionBasis) (h : Set.InjOn φ.vertex (G.support a.1)) :
    H.IncResolutionBasis :=
  ⟨a.1, (φ.stateFibreEquiv a.1 h).symm a.2⟩

@[simp] theorem statePushOn_fst (a : G.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support a.1)) :
    (φ.statePushOn a h).1 = a.1 := rfl

theorem statePullOn_statePushOn (a : G.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support a.1)) : φ.statePullOn (φ.statePushOn a h) h = a := by
  obtain ⟨S, κ⟩ := a
  change (⟨S, φ.stateFibreEquiv S h ((φ.stateFibreEquiv S h).symm κ)⟩ : G.IncResolutionBasis) = _
  rw [Equiv.apply_symm_apply]

/-- A state of `H` with a non-colliding edge set is the state pushed from its restriction. -/
theorem statePushOn_statePullOn (b : H.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support b.1)) :
    φ.statePushOn (φ.statePullOn b h) h = b := by
  refine φ.statePullOn_injective (b := φ.statePushOn (φ.statePullOn b h) h) (b' := b) h h ?_
  exact φ.statePullOn_statePushOn (φ.statePullOn b h) h

/-- **The state formula on a basis state.** If the full state of `y` is a multiple of one basis
state `a` of `G` whose edge set has injective vertex support, the full state of its image is the
Koszul sign times the same multiple of the state of `H` restricting to `a`. -/
theorem incidenceTorFullState_vertexMap_of_single {p : ℕ} {y : G.incidenceTor p}
    {a : G.IncResolutionBasis} {r : ℂ} (hy : G.incidenceTorFullState p y = single a r)
    (h : Set.InjOn φ.vertex (G.support a.1)) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) =
      single (φ.statePushOn a h) (vertexMapSign ℂ φ.vertex (G.support a.1) * r) := by
  ext b
  rw [φ.incidenceTorFullState_vertexMap_apply_of_mem_edgeSetPiece
    (G.mem_incidenceTorEdgeSetPiece_of_fullState_single hy) b]
  split_ifs with hb
  · obtain ⟨hb1, hb2⟩ := hb
    rw [hy]
    by_cases hab : φ.statePullOn b hb2 = a
    · have hba : φ.statePushOn a h = b := by
        rw [← φ.statePushOn_statePullOn b hb2]
        subst hab
        rfl
      rw [hab, single_eq_same, ← hba, single_eq_same, statePushOn_fst]
    · rw [single_eq_of_ne hab, mul_zero, single_eq_of_ne]
      intro hba
      apply hab
      subst hba
      exact φ.statePullOn_statePushOn a h
  · rw [single_eq_of_ne]
    intro hba
    apply hb
    subst hba
    exact ⟨rfl, h⟩

/-- For a vertex bijection the sign of the state formula is the Koszul sign `stateSign` of the
relabeling. -/
theorem _root_.BPFixedPoints.Multigraph.VertexRelabel.vertexMapSign_eq_stateSign
    {V' W' : Type} [DecidableEq V'] [Fintype V'] [DecidableEq W'] [Fintype W']
    {G' : Multigraph V' E} {H' : Multigraph W' E} (ψ : VertexRelabel G' H') (S : Finset E) :
    vertexMapSign ℂ ψ.vertex (G'.support S) = ψ.stateSign ℂ S := by
  have hs : G'.support S = twistSupport (G'.deg S) := by
    ext v
    rw [mem_support_iff, mem_twistSupport, Nat.pos_iff_ne_zero]
  rw [hs]
  rfl

/-! ## Degree zero: the image of `z_C` is `± z_{φ(C)}` -/

/-- **The scalar of a non-colliding cycle union is the Koszul sign.** -/
theorem cycleScalar_eq_vertexMapSign {S : Finset E} (hS : G.IsCycleUnion S)
    (h : Set.InjOn φ.vertex (G.support S)) :
    φ.cycleScalar S = vertexMapSign ℂ φ.vertex (G.support S) := by
  have hS' : H.IsCycleUnion S := (φ.isCycleUnion_iff_injOn hS).2 h
  rw [cycleScalar, dite_eq_left hS', φ.incidenceTorFullState_vertexMap_apply_of_injOn 0 _ _ h,
    G.incidenceTorFullState_cycleUnionClass hS]
  have hpull : φ.statePullOn (H.cycleUnionState S hS') h = G.cycleUnionState S hS := by
    apply G.eq_cycleUnionState_of_fst_eq hS _ _ rfl
    rw [← G.incResolutionDegree_cycleUnionState S hS]
    rfl
  rw [hpull, single_eq_same, mul_one]
  rfl

/-- **`z_C ↦ ± z_{φ(C)}` in degree-zero Tor.** If the vertex function is injective on the vertices
of a simple cycle `C`, the degree-zero Tor map sends the class of `C` to the Koszul sign
`vertexMapSign ℂ φ.vertex (G.support C)` times the class of the simple cycle `φ(C)` of `H`. -/
theorem incidenceTorMap_cycleClass_eq (C : G.SimpleCycle)
    (h : Set.InjOn φ.vertex (G.support C.val)) :
    φ.incidenceTorMap 0 (G.cycleClass C) =
      vertexMapSign ℂ φ.vertex (G.support C.val) • H.cycleClass (φ.mapCycle C h) := by
  change φ.incidenceTorMap 0 (G.cycleUnionClass C.val) = _ • H.cycleUnionClass C.val
  rw [φ.incidenceTorMap_cycleUnionClass_eq C.property.isCycleUnion,
    φ.cycleScalar_eq_vertexMapSign C.property.isCycleUnion h]

/-- **`z_C ↦ ± z_{φ(C)}`** in the cycle-compatibility algebras, with the Koszul sign
`vertexMapSign ℂ φ.vertex (G.support C)`. -/
theorem cycleAlgebraHom_X_eq (C : G.SimpleCycle) (h : Set.InjOn φ.vertex (G.support C.val)) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) =
      vertexMapSign ℂ φ.vertex (G.support C.val) •
        Ideal.Quotient.mk H.cycleCompatibilityIdeal (X (φ.mapCycle C h)) := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_X,
    φ.incidenceTorMap_cycleClass_eq C h, map_smul, cycleAlgebraEquivTor_X]

end VertexMap

end BPFixedPoints.Multigraph
