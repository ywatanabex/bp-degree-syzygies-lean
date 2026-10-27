import BPFixedPoints.Incidence.IncidenceVertexMapCycles
import BPFixedPoints.Incidence.IncidenceEdgeMapTor

/-!
# Vertex maps in degree zero: the image of `z_C` is a nonzero multiple of `z_{φ(C)}`

Let `φ : VertexMap G H`. By `IncidenceVertexMapCycles`, the degree-zero Tor map sends the class of a
cycle union `S` of `G` to a scalar multiple of the class of `S` in `H`. Here the scalar is named
(`cycleScalar`), it is multiplicative under composition (`cycleScalar_trans`) and equals one for the
identity (`cycleScalar_refl`), and it is shown to be nonzero whenever the vertex function is
injective on the vertices of a simple cycle:

* **Retractions.** If every edge of `G` has its endpoints in the vertex support of `S` and the
  vertex function is injective there, restrict the vertex type of `G` to the support
  (`supportGraph`, with the inclusion `supportInclusion`) and choose a retraction of `H` onto it
  (`supportRetraction`). The composite of the inclusion, `φ` and the retraction is the identity
  vertex map, so the product of the three scalars is one (`cycleScalar_ne_zero_of_supported`).
* **Subgraphs.** In general, restrict to the subgraph of the edges of `C` (`edgeRestrict`). The edge
  map of the inclusion of a subgraph sends the class of a cycle union to its wedge sign times the
  class of its image (`EdgeMap.incidenceTorEdgeMap_cycleUnionClass`), and the degree-zero Tor maps
  of the inclusions commute with those of `φ` and of its restriction
  (`incidenceTorMap_edgeRestrictInclusion`).

Consequently, for a simple cycle `C` of `G` whose vertices are pairwise not identified,
`z_C ↦ c · z_{φ(C)}` with `c ≠ 0` (`exists_ne_zero_incidenceTorMap_cycleClass`,
`exists_ne_zero_cycleAlgebraHom_X`), and `z_C ↦ 0` exactly when two vertices of `C` are identified
(`cycleAlgebraHom_X_eq_zero_iff`).

Not proved here: that the scalar is `±1`. The argument above only shows that the scalars of an
inclusion, of `φ` and of a retraction multiply to one; fixing the value needs a state formula for
the degree-zero lift.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp MvPolynomial

/-! ## Edge maps in degree zero -/

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] [LinearOrder E']
  [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- In degree zero the Tor map of an edge map is induced by its incidence ring map. -/
theorem incidenceTorEdgeMap_incidenceRingToTor (u : G.IncidenceRing) :
    φ.incidenceTorEdgeMap 0 (G.incidenceRingToTor u) = H.incidenceRingToTor (φ.incidenceHom u) := by
  obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
  rw [incidenceRingToTor_augmentation, incidenceTorEdgeMap_class, ← freeTermMap_augmentation,
    incidenceRingToTor_augmentation]

/-- An edge map which is injective on a cycle union sends its class to its wedge sign times the
class of the image edge set. -/
theorem incidenceTorEdgeMap_cycleUnionClass {S : Finset E} (hS : G.IsCycleUnion S)
    (h : Set.InjOn φ.edge S) :
    φ.incidenceTorEdgeMap 0 (G.cycleUnionClass S) =
      (φ.wedgeSign S : ℂ) • H.cycleUnionClass (φ.edgeSet S) := by
  have hdeg : H.incResolutionDegree (φ.stateIndex (G.cycleUnionState S hS) h) = 0 := by
    rw [incResolutionDegree_stateIndex, incResolutionDegree_cycleUnionState]
  have hS' : H.IsCycleUnion (φ.edgeSet S) :=
    H.isCycleUnion_of_incResolutionDegree_eq_zero _ hdeg
  apply H.incidenceTorFullState_injective 0
  rw [φ.incidenceTorFullState_edgeMap_of_single 0 _ (G.cycleUnionState S hS) 1
    (G.incidenceTorFullState_cycleUnionClass hS) h, map_smul,
    H.incidenceTorFullState_cycleUnionClass hS', smul_single, smul_eq_mul, mul_one]
  congr 1
  · exact H.eq_cycleUnionState_of_fst_eq hS' _ hdeg rfl
  · rw [mul_one]
    rfl

/-- The wedge sign of an edge set on which the edge function is injective is nonzero. -/
theorem wedgeSign_ne_zero {S : Finset E} (h : Set.InjOn φ.edge S) : (φ.wedgeSign S : ℂ) ≠ 0 := by
  rw [wedgeSign_of_injOn φ h]
  push_cast
  exact pow_ne_zero _ (by norm_num)

end EdgeMap

/-! ## Subgraph inclusions -/

/-- The edge map of the inclusion of the subgraph of the edges in `A`. -/
def edgeRestrictInclusion {V E : Type} (G : Multigraph V E) (A : Finset E) :
    EdgeMap (G.edgeRestrict A) G where
  edge := Subtype.val
  reversed := fun _ => false
  fst_edge _ := rfl
  snd_edge _ := rfl

@[simp] theorem edgeRestrictInclusion_edge {V E : Type} (G : Multigraph V E) (A : Finset E) :
    (G.edgeRestrictInclusion A).edge = Subtype.val := rfl

/-- The image of all edges of the subgraph of the edges in `A` is `A`. -/
theorem edgeRestrictInclusion_edgeSet_univ {V E : Type} [DecidableEq E] (G : Multigraph V E)
    (A : Finset E) : (G.edgeRestrictInclusion A).edgeSet Finset.univ = A := by
  rw [EdgeMap.edgeSet_def, edgeRestrictInclusion_edge, Finset.univ_eq_attach,
    Finset.attach_image_val]

/-- The inclusion of a subgraph is injective on edges. -/
theorem edgeRestrictInclusion_injOn {V E : Type} (G : Multigraph V E) (A : Finset E)
    (S : Set {e // e ∈ A}) : Set.InjOn (G.edgeRestrictInclusion A).edge S :=
  Subtype.val_injective.injOn

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- The restriction of a vertex map to the subgraphs of the edges in `A`. -/
def edgeRestrict (A : Finset E) : VertexMap (G.edgeRestrict A) (H.edgeRestrict A) where
  vertex := φ.vertex
  fst_edge e := φ.fst_edge e.1
  snd_edge e := φ.snd_edge e.1

@[simp] theorem edgeRestrict_vertex (A : Finset E) : (φ.edgeRestrict A).vertex = φ.vertex := rfl

/-- The torus maps of a vertex map and of its restriction commute with the inclusions of the
subgraphs. -/
theorem torusHom_edgeRestrictInclusion (A : Finset E) (x : (G.edgeRestrict A).IncTorusRing) :
    φ.torusHom ((G.edgeRestrictInclusion A).torusHom x) =
      (H.edgeRestrictInclusion A).torusHom ((φ.edgeRestrict A).torusHom x) := by
  have h : φ.torusHom.comp (G.edgeRestrictInclusion A).torusHom =
      (H.edgeRestrictInclusion A).torusHom.comp (φ.edgeRestrict A).torusHom := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro w
    change φ.torusHom ((G.edgeRestrictInclusion A).torusHom (Ideal.Quotient.mk _ (X w))) =
      (H.edgeRestrictInclusion A).torusHom ((φ.edgeRestrict A).torusHom (Ideal.Quotient.mk _ (X w)))
    rw [EdgeMap.torusHom_mk, torusHom_mk, torusHom_mk, EdgeMap.torusHom_mk, rename_X, rename_X,
      rename_X, rename_X]
    rcases w with v | v | c <;> rfl
  exact AlgHom.congr_fun h x

/-- The incidence ring maps of a vertex map and of its restriction commute with the inclusions of
the subgraphs. -/
theorem incidenceHom_edgeRestrictInclusion (A : Finset E) (u : (G.edgeRestrict A).IncidenceRing) :
    φ.incidenceHom ((G.edgeRestrictInclusion A).incidenceHom u) =
      (H.edgeRestrictInclusion A).incidenceHom ((φ.edgeRestrict A).incidenceHom u) :=
  Subtype.ext (φ.torusHom_edgeRestrictInclusion A u.val)

/-- **Naturality for subgraph inclusions in degree zero.** -/
theorem incidenceTorMap_edgeRestrictInclusion (A : Finset E)
    (t : (G.edgeRestrict A).incidenceTor 0) :
    φ.incidenceTorMap 0 ((G.edgeRestrictInclusion A).incidenceTorEdgeMap 0 t) =
      (H.edgeRestrictInclusion A).incidenceTorEdgeMap 0 ((φ.edgeRestrict A).incidenceTorMap 0 t) := by
  obtain ⟨u, rfl⟩ := (G.edgeRestrict A).incidenceRingToTor_surjective t
  rw [EdgeMap.incidenceTorEdgeMap_incidenceRingToTor, incidenceTorMap_incidenceRingToTor,
    incidenceTorMap_incidenceRingToTor, EdgeMap.incidenceTorEdgeMap_incidenceRingToTor]
  exact congrArg H.incidenceRingToTor (φ.incidenceHom_edgeRestrictInclusion A u)

/-! ## The scalar of a cycle union -/

/-- The scalar by which the degree-zero Tor map multiplies the class of an edge set: the
coordinate of the image at the state of `S` in `H`, and zero if `S` is not a cycle union of
`H`. -/
noncomputable def cycleScalar (S : Finset E) : ℂ :=
  if hS : H.IsCycleUnion S then
    H.incidenceTorFullState 0 (φ.incidenceTorMap 0 (G.cycleUnionClass S)) (H.cycleUnionState S hS)
  else 0

/-- The degree-zero Tor map multiplies the class of a cycle union by its scalar. -/
theorem incidenceTorMap_cycleUnionClass_eq {S : Finset E} (hS : G.IsCycleUnion S) :
    φ.incidenceTorMap 0 (G.cycleUnionClass S) = φ.cycleScalar S • H.cycleUnionClass S := by
  obtain ⟨c, hc⟩ := φ.exists_incidenceTorMap_cycleUnionClass hS
  by_cases hS' : H.IsCycleUnion S
  · have hcs : φ.cycleScalar S = c := by
      rw [cycleScalar, dite_eq_left hS', hc, map_smul, H.incidenceTorFullState_cycleUnionClass hS',
        Finsupp.smul_apply, single_eq_same, smul_eq_mul, mul_one]
    rw [hcs, hc]
  · rw [hc, H.cycleUnionClass_of_not hS', smul_zero, smul_zero]

/-- The scalar of the identity vertex map is one. -/
theorem cycleScalar_refl (G : Multigraph V E) {S : Finset E} (hS : G.IsCycleUnion S) :
    (refl G).cycleScalar S = 1 := by
  rw [cycleScalar, dite_eq_left hS, funext (incidenceTorMap_refl G 0),
    G.incidenceTorFullState_cycleUnionClass hS, single_eq_same]

/-- The scalars are multiplicative under composition. -/
theorem cycleScalar_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) {S : Finset E} (hS : G.IsCycleUnion S) (hS' : H.IsCycleUnion S) :
    (φ.trans χ).cycleScalar S = χ.cycleScalar S * φ.cycleScalar S := by
  by_cases hK : K.IsCycleUnion S
  · apply smul_left_injective ℂ (K.cycleUnionClass_ne_zero hK)
    change (φ.trans χ).cycleScalar S • K.cycleUnionClass S =
      (χ.cycleScalar S * φ.cycleScalar S) • K.cycleUnionClass S
    rw [← incidenceTorMap_cycleUnionClass_eq _ hS, incidenceTorMap_trans,
      incidenceTorMap_cycleUnionClass_eq _ hS, map_smul, incidenceTorMap_cycleUnionClass_eq _ hS',
      smul_smul, mul_comm]
  · rw [cycleScalar, dite_eq_right hK, cycleScalar, dite_eq_right hK, zero_mul]

/-! ## Retractions onto the vertex support -/

end VertexMap

section Support

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

/-- The graph with the same edges on the vertex support of `S`, when every edge has its endpoints
there. -/
def supportGraph (G : Multigraph V E) (S : Finset E)
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) :
    Multigraph {v // v ∈ G.support S} E where
  fst e := ⟨G.fst e, (hE e).1⟩
  snd e := ⟨G.snd e, (hE e).2⟩

/-- The inclusion of the vertex support. -/
def supportInclusion (G : Multigraph V E) (S : Finset E)
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) :
    VertexMap (G.supportGraph S hE) G where
  vertex := Subtype.val
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- Degrees on the vertex support are the degrees in the original graph. -/
theorem supportGraph_deg (G : Multigraph V E) (S : Finset E)
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) (T : Finset E)
    (p : {v // v ∈ G.support S}) : (G.supportGraph S hE).deg T p = G.deg T p.val := by
  unfold deg endCount
  simp only [supportGraph, Subtype.ext_iff]

/-- A cycle union of `G` is a cycle union of the graph on its vertex support. -/
theorem isCycleUnion_supportGraph (G : Multigraph V E) {S : Finset E} (hS : G.IsCycleUnion S)
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) :
    (G.supportGraph S hE).IsCycleUnion S := fun p => by
  rw [supportGraph_deg]
  exact hS p.val

end Support

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- A retraction of the vertices of `H` onto the vertex support of `S`, inverse to the vertex
function on the support. -/
noncomputable def supportRetraction (S : Finset E) (hne : (G.support S).Nonempty) (w : W) :
    {v // v ∈ G.support S} := by
  classical
  exact if h : ∃ v ∈ G.support S, φ.vertex v = w then ⟨h.choose, h.choose_spec.1⟩
    else ⟨hne.choose, hne.choose_spec⟩

/-- The retraction inverts the vertex function on the vertex support. -/
theorem supportRetraction_vertex {S : Finset E} (hne : (G.support S).Nonempty)
    (hinj : Set.InjOn φ.vertex (G.support S)) {v : V} (hv : v ∈ G.support S) :
    φ.supportRetraction S hne (φ.vertex v) = ⟨v, hv⟩ := by
  classical
  have h : ∃ v' ∈ G.support S, φ.vertex v' = φ.vertex v := ⟨v, hv, rfl⟩
  unfold supportRetraction
  rw [dite_eq_left h]
  apply Subtype.ext
  exact hinj h.choose_spec.1 hv h.choose_spec.2

/-- The retraction as a vertex map from `H` to the graph on the vertex support of `S`. -/
noncomputable def supportRetractionMap {S : Finset E} (hne : (G.support S).Nonempty)
    (hinj : Set.InjOn φ.vertex (G.support S))
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) :
    VertexMap H (G.supportGraph S hE) where
  vertex := φ.supportRetraction S hne
  fst_edge e := by
    rw [φ.fst_edge, φ.supportRetraction_vertex hne hinj (hE e).1]
    rfl
  snd_edge e := by
    rw [φ.snd_edge, φ.supportRetraction_vertex hne hinj (hE e).2]
    rfl

/-- Including the vertex support, applying `φ` and retracting is the identity vertex map. -/
theorem supportInclusion_trans_retraction {S : Finset E} (hne : (G.support S).Nonempty)
    (hinj : Set.InjOn φ.vertex (G.support S))
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) :
    (G.supportInclusion S hE).trans (φ.trans (φ.supportRetractionMap hne hinj hE)) =
      refl (G.supportGraph S hE) := by
  apply ext'
  funext p
  exact φ.supportRetraction_vertex hne hinj p.property

/-- **Nonvanishing through a retraction.** If every edge of `G` has its endpoints in the vertex
support of the cycle union `S` and the vertex function is injective there, the scalar of `S` is
nonzero. -/
theorem cycleScalar_ne_zero_of_supported {S : Finset E} (hS : G.IsCycleUnion S)
    (hne : (G.support S).Nonempty) (hinj : Set.InjOn φ.vertex (G.support S))
    (hE : ∀ e, G.fst e ∈ G.support S ∧ G.snd e ∈ G.support S) : φ.cycleScalar S ≠ 0 := by
  have hS₀ := G.isCycleUnion_supportGraph hS hE
  have hS₁ : H.IsCycleUnion S := (φ.isCycleUnion_iff_injOn hS).2 hinj
  have h := cycleScalar_refl (G.supportGraph S hE) hS₀
  rw [← φ.supportInclusion_trans_retraction hne hinj hE,
    cycleScalar_trans _ _ hS₀ hS, cycleScalar_trans _ _ hS hS₁] at h
  intro h0
  rw [h0, mul_zero, zero_mul] at h
  exact zero_ne_one h

/-! ## Simple cycles -/

/-- The restriction of a simple cycle to the subgraph of its edges: the set of all edges is a
cycle union with the same vertex support. -/
theorem isCycleUnion_edgeRestrict_univ {C : Finset E} (hC : G.IsCycleUnion C) :
    (G.edgeRestrict C).IsCycleUnion Finset.univ := fun v => by
  rw [edgeRestrict_deg_univ]
  exact hC v

/-- **`z_C ↦ c · z_{φ(C)}` with `c ≠ 0`.** If the vertex function is injective on the vertices of a
simple cycle `C`, the degree-zero Tor map sends the class of `C` to a nonzero multiple of the class
of the simple cycle `C` of `H`. -/
theorem exists_ne_zero_incidenceTorMap_cycleClass (C : G.SimpleCycle)
    (h : Set.InjOn φ.vertex (G.support C.val)) :
    ∃ c : ℂ, c ≠ 0 ∧ φ.incidenceTorMap 0 (G.cycleClass C) = c • H.cycleClass (φ.mapCycle C h) := by
  set A := C.val
  have hA : G.IsCycleUnion A := C.property.isCycleUnion
  have hU : (G.edgeRestrict A).IsCycleUnion Finset.univ := isCycleUnion_edgeRestrict_univ hA
  have hsupp : (G.edgeRestrict A).support Finset.univ = G.support A :=
    G.edgeRestrict_support_univ A
  have hE : ∀ e, (G.edgeRestrict A).fst e ∈ (G.edgeRestrict A).support Finset.univ ∧
      (G.edgeRestrict A).snd e ∈ (G.edgeRestrict A).support Finset.univ := by
    intro e
    rw [hsupp]
    exact ⟨G.fst_mem_support e.property, G.mem_support_of_incident e.property (Or.inr rfl)⟩
  have hne : ((G.edgeRestrict A).support Finset.univ).Nonempty := by
    rw [hsupp]
    exact G.support_nonempty_of_isSimpleCycle C.property
  have hinj : Set.InjOn (φ.edgeRestrict A).vertex ((G.edgeRestrict A).support Finset.univ) := by
    rw [hsupp, edgeRestrict_vertex]
    exact h
  have hc := (φ.edgeRestrict A).cycleScalar_ne_zero_of_supported hU hne hinj hE
  have hHU : (H.edgeRestrict A).IsCycleUnion Finset.univ :=
    ((φ.edgeRestrict A).isCycleUnion_iff_injOn hU).2 hinj
  have hG := (G.edgeRestrictInclusion A).incidenceTorEdgeMap_cycleUnionClass hU
    (G.edgeRestrictInclusion_injOn A _)
  have hH := (H.edgeRestrictInclusion A).incidenceTorEdgeMap_cycleUnionClass hHU
    (H.edgeRestrictInclusion_injOn A _)
  rw [edgeRestrictInclusion_edgeSet_univ] at hG hH
  have key : ((G.edgeRestrictInclusion A).wedgeSign Finset.univ : ℂ) •
        φ.incidenceTorMap 0 (G.cycleUnionClass A) =
      ((φ.edgeRestrict A).cycleScalar Finset.univ *
        ((H.edgeRestrictInclusion A).wedgeSign Finset.univ : ℂ)) • H.cycleUnionClass A := by
    have hsq := φ.incidenceTorMap_edgeRestrictInclusion A ((G.edgeRestrict A).cycleUnionClass
      Finset.univ)
    rw [hG, (φ.edgeRestrict A).incidenceTorMap_cycleUnionClass_eq hU] at hsq
    rw [← map_smul, hsq, map_smul, hH, smul_smul]
  have hwG := (G.edgeRestrictInclusion A).wedgeSign_ne_zero (G.edgeRestrictInclusion_injOn A
    (Finset.univ : Finset {e // e ∈ A}))
  have hwH := (H.edgeRestrictInclusion A).wedgeSign_ne_zero (H.edgeRestrictInclusion_injOn A
    (Finset.univ : Finset {e // e ∈ A}))
  refine ⟨((G.edgeRestrictInclusion A).wedgeSign Finset.univ : ℂ)⁻¹ *
    ((φ.edgeRestrict A).cycleScalar Finset.univ *
      ((H.edgeRestrictInclusion A).wedgeSign Finset.univ : ℂ)), ?_, ?_⟩
  · exact mul_ne_zero (inv_ne_zero hwG) (mul_ne_zero hc hwH)
  · change φ.incidenceTorMap 0 (G.cycleUnionClass A) = _ • H.cycleUnionClass A
    rw [mul_smul, ← key, smul_smul, inv_mul_cancel₀ hwG, one_smul]

/-- **`z_C ↦ c · z_{φ(C)}` with `c ≠ 0`** in the cycle-compatibility algebras. -/
theorem exists_ne_zero_cycleAlgebraHom_X (C : G.SimpleCycle)
    (h : Set.InjOn φ.vertex (G.support C.val)) :
    ∃ c : ℂ, c ≠ 0 ∧ φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) =
      c • Ideal.Quotient.mk H.cycleCompatibilityIdeal (X (φ.mapCycle C h)) := by
  obtain ⟨c, hc, hcC⟩ := φ.exists_ne_zero_incidenceTorMap_cycleClass C h
  refine ⟨c, hc, H.cycleAlgebraEquivTor.injective ?_⟩
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_X, hcC, map_smul,
    cycleAlgebraEquivTor_X]

/-- **Where `z_C` goes, in one statement.** The image of `z_C` is zero exactly when the vertex
function identifies two vertices of `C`; otherwise it is a nonzero multiple of `z_{φ(C)}`. -/
theorem cycleAlgebraHom_X_eq_zero_iff (C : G.SimpleCycle) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) = 0 ↔
      ¬ Set.InjOn φ.vertex (G.support C.val) := by
  constructor
  · intro h0 h
    obtain ⟨c, hc, hcC⟩ := φ.exists_ne_zero_cycleAlgebraHom_X C h
    rw [hcC] at h0
    have hX : Ideal.Quotient.mk H.cycleCompatibilityIdeal (X (φ.mapCycle C h)) ≠ 0 := by
      intro hX
      have h1 := congrArg H.cycleAlgebraEquivTor hX
      rw [cycleAlgebraEquivTor_X, map_zero] at h1
      exact H.cycleUnionClass_ne_zero (φ.mapCycle C h).property.isCycleUnion h1
    apply hX
    have h1 := congrArg (fun a => c⁻¹ • a) h0
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] at h1
    exact h1
  · exact φ.cycleAlgebraHom_X_of_not_injOn C

end VertexMap

end BPFixedPoints.Multigraph
