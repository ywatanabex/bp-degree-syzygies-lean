import BPFixedPoints.Incidence.IncidenceVertexMapTor
import BPFixedPoints.Incidence.IncidenceCycleAlgebraQuotient
import BPFixedPoints.Incidence.IncidenceEdgeSignResolution

/-!
# Vertex maps in homological degree zero: the cycle-compatibility algebras

Let `φ : VertexMap G H`. In homological degree zero the Tor map of `φ` is a map of commutative
complex algebras (`incidenceTorZeroAlgHom`, by `incidenceTorMap_product` and
`incidenceTorMap_one`). Under `Tor_0 ≅ U/(S_+)U` it is the map induced by the incidence ring map:
`incidenceTorMap_incidenceRingToTor` and the quotient map `augmentationQuotientHom`
(`incidenceQuotientEquivTor_augmentationQuotientHom`). Transported to the cycle-compatibility
algebras it is `cycleAlgebraHom : ℂ[z_C]/(z_C z_D) → ℂ[z_C]/(z_C z_D)`, which agrees with the
map induced on `U/(S_+)U` (`cycleAlgebraHom_incidenceQuotient`).

**Where `z_C` goes.** The class of a cycle union `S` of `G` goes to a scalar multiple of the class
of the edge set `S` in `H` (`exists_incidenceTorMap_cycleUnionClass`). The proof uses the edge
signs: the vertex map commutes with every edge sign change (`incidenceHom_edgeSignIncidence`), the
edge sign `ε` acts on the degree-zero class of an element of `U` by scaling the state of each edge
set `T` by `∏_{e ∈ T} ε_e` (`incidenceTorFullState_edgeSign`), and a Tor class on which every edge
sign acts by the character of `S` is a multiple of the class of `S`
(`exists_eq_smul_cycleUnionClass`), because the characters of the edge sign group separate edge
sets. Consequently, for a simple cycle `C` of `G`:
* if the vertex function is injective on the vertices of `C`, then `C` is a simple cycle of `H`
  and `z_C ↦ c · z_{φ(C)}` for some `c ∈ ℂ` (`cycleAlgebraHom_X_of_injOn`);
* if two distinct vertices of `C` are identified, then `z_C ↦ 0` (`cycleAlgebraHom_X_of_identify`).

**Acceptance example.** If `C` and `D` are vertex-disjoint simple cycles of `G` and the vertex
function identifies a vertex of `C` with a vertex of `D`, then `z_C z_D ≠ 0` in the
cycle-compatibility algebra of `G`, while its image is zero, because the images share a vertex in
`H` (`cycleAlgebra_X_mul_X_ne_zero`, `cycleAlgebraHom_X_mul_X_of_identify`,
`cycleAlgebraHom_acceptance`).

The scalar `c` is shown to be nonzero in `IncidenceVertexMapCycleScalars` (naturality for subgraph
inclusions combined with retractions). Not proved: that `c = ±1`. That needs a state formula for
the chain-level lift in degree zero (an explicit description of the augmentation of a cycle state),
which is not formalized.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp MvPolynomial ResolutionTools

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Degree-zero Tor as an algebra -/

/-- The Tor map in degree zero is multiplicative. -/
theorem incidenceTorMap_zero_mul (x y : G.incidenceTor 0) :
    φ.incidenceTorMap 0 (x * y) = φ.incidenceTorMap 0 x * φ.incidenceTorMap 0 y :=
  φ.incidenceTorMap_product 0 0 x y

/-- **The Tor map in degree zero is an algebra map** of the commutative degree-zero Tor
algebras. -/
noncomputable def incidenceTorZeroAlgHom : G.incidenceTor 0 →ₐ[ℂ] H.incidenceTor 0 :=
  AlgHom.ofLinearMap (φ.incidenceTorMap 0) φ.incidenceTorMap_one φ.incidenceTorMap_zero_mul

@[simp] theorem incidenceTorZeroAlgHom_apply (x : G.incidenceTor 0) :
    φ.incidenceTorZeroAlgHom x = φ.incidenceTorMap 0 x := rfl

/-- In degree zero the Tor map is induced by the incidence ring map: the class of `u` goes to the
class of its image. -/
theorem incidenceTorMap_incidenceRingToTor (u : G.IncidenceRing) :
    φ.incidenceTorMap 0 (G.incidenceRingToTor u) = H.incidenceRingToTor (φ.incidenceHom u) := by
  obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
  rw [incidenceRingToTor_augmentation, incidenceTorMap_class, ← freeTermLift_augmentation,
    incidenceRingToTor_augmentation]

/-! ## The map of `U/(S_+)U` -/

/-- The incidence ring map carries the coefficient augmentation ideal into the coefficient
augmentation ideal. -/
theorem incidenceAugmentationIdeal_le_comap :
    G.incidenceAugmentationIdeal ≤ H.incidenceAugmentationIdeal.comap φ.incidenceHom := by
  rw [incidenceAugmentationIdeal, Ideal.map_le_iff_le_comap]
  intro s hs
  rw [Ideal.mem_comap, Ideal.mem_comap, incidenceHom_coeffHom]
  exact Ideal.mem_map_of_mem _ hs

/-- The map `U_G/(S_G)_+U_G → U_H/(S_H)_+U_H` induced by the incidence ring map. -/
noncomputable def augmentationQuotientHom :
    G.IncidenceAugmentationQuotient →ₐ[ℂ] H.IncidenceAugmentationQuotient :=
  Ideal.quotientMapₐ _ φ.incidenceHom φ.incidenceAugmentationIdeal_le_comap

/-- The map of quotients on the class of an element. -/
theorem augmentationQuotientHom_mk (u : G.IncidenceRing) :
    φ.augmentationQuotientHom (Ideal.Quotient.mk _ u) =
      Ideal.Quotient.mk _ (φ.incidenceHom u) := rfl

/-- Under `U/(S_+)U ≅ Tor_0` the map of quotients is the Tor map in degree zero. -/
theorem incidenceQuotientEquivTor_augmentationQuotientHom (a : G.IncidenceAugmentationQuotient) :
    H.incidenceQuotientEquivTor (φ.augmentationQuotientHom a) =
      φ.incidenceTorMap 0 (G.incidenceQuotientEquivTor a) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [augmentationQuotientHom_mk, incidenceQuotientEquivTor_mk, incidenceQuotientEquivTor_mk,
    incidenceTorMap_incidenceRingToTor]

/-! ## The map of cycle-compatibility algebras -/

/-- **The map of cycle-compatibility algebras** induced by a vertex map: the degree-zero Tor map
transported along `cycleAlgebraEquivTor`. -/
noncomputable def cycleAlgebraHom : G.CycleAlgebra →ₐ[ℂ] H.CycleAlgebra :=
  H.cycleAlgebraEquivTor.symm.toAlgHom.comp
    (φ.incidenceTorZeroAlgHom.comp G.cycleAlgebraEquivTor.toAlgHom)

/-- The map of cycle-compatibility algebras is the degree-zero Tor map under
`cycleAlgebraEquivTor`. -/
theorem cycleAlgebraEquivTor_cycleAlgebraHom (a : G.CycleAlgebra) :
    H.cycleAlgebraEquivTor (φ.cycleAlgebraHom a) = φ.incidenceTorMap 0 (G.cycleAlgebraEquivTor a) :=
  H.cycleAlgebraEquivTor.apply_symm_apply _

/-- The map of cycle-compatibility algebras is the map of `U/(S_+)U` transported along
`incidenceQuotientEquivCycleAlgebra`. -/
theorem cycleAlgebraHom_incidenceQuotient (a : G.IncidenceAugmentationQuotient) :
    φ.cycleAlgebraHom (G.incidenceQuotientEquivCycleAlgebra a) =
      H.incidenceQuotientEquivCycleAlgebra (φ.augmentationQuotientHom a) := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom]
  change φ.incidenceTorMap 0 (G.cycleAlgebraEquivTor (G.cycleAlgebraEquivTor.symm
      (G.incidenceQuotientEquivTor a))) =
    H.cycleAlgebraEquivTor (H.cycleAlgebraEquivTor.symm
      (H.incidenceQuotientEquivTor (φ.augmentationQuotientHom a)))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    incidenceQuotientEquivTor_augmentationQuotientHom]

/-- Identity law for the maps of cycle-compatibility algebras. -/
theorem cycleAlgebraHom_refl (G : Multigraph V E) (a : G.CycleAlgebra) :
    (refl G).cycleAlgebraHom a = a := by
  apply G.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, incidenceTorMap_refl]

/-- Composition law for the maps of cycle-compatibility algebras. -/
theorem cycleAlgebraHom_trans {U : Type} [DecidableEq U] [Fintype U] {K : Multigraph U E}
    (χ : VertexMap H K) (a : G.CycleAlgebra) :
    (φ.trans χ).cycleAlgebraHom a = χ.cycleAlgebraHom (φ.cycleAlgebraHom a) := by
  apply K.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_cycleAlgebraHom,
    cycleAlgebraEquivTor_cycleAlgebraHom, incidenceTorMap_trans]

/-! ## Edge signs -/

/-- The torus map of a vertex map commutes with every edge sign change. -/
theorem torusHom_edgeSignTorus (ε : EdgeSign E) (x : G.IncTorusRing) :
    φ.torusHom (G.edgeSignTorus ε x) = H.edgeSignTorus ε (φ.torusHom x) := by
  have h : φ.torusHom.comp (G.edgeSignTorus ε).toAlgHom =
      (H.edgeSignTorus ε).toAlgHom.comp φ.torusHom := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro w
    change φ.torusHom (G.edgeSignTorus ε (Ideal.Quotient.mk _ (X w))) =
      H.edgeSignTorus ε (φ.torusHom (Ideal.Quotient.mk _ (X w)))
    rw [edgeSignTorus_mk, torusHom_mk, torusHom_mk, edgeSignTorus_mk, varSignHom_X, rename_X,
      map_mul, map_intCast, rename_X, varSignHom_X]
    rcases w with v | v | c <;> rfl
  exact AlgHom.congr_fun h x

/-- The incidence ring map of a vertex map commutes with every edge sign change. -/
theorem incidenceHom_edgeSignIncidence (ε : EdgeSign E) (u : G.IncidenceRing) :
    φ.incidenceHom (G.edgeSignIncidence ε u) = H.edgeSignIncidence ε (φ.incidenceHom u) :=
  Subtype.ext (φ.torusHom_edgeSignTorus ε u.val)

end VertexMap

section EdgeSignTorZero

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- An edge sign acts on the degree-zero class of an element of the incidence ring by the
edge-sign scaling of its full state vector. -/
theorem incidenceTorFullState_edgeSign (ε : EdgeSign E) (u : G.IncidenceRing) :
    G.incidenceTorFullState 0 (G.incidenceRingToTor (G.edgeSignIncidence ε u)) =
      G.edgeSignState ε ℂ (G.incidenceTorFullState 0 (G.incidenceRingToTor u)) := by
  obtain ⟨x, rfl⟩ := G.incResolutionAugmentation_surjective u
  rw [← edgeSignFreeTerm_augmentation, incidenceRingToTor_augmentation,
    incidenceRingToTor_augmentation, incidenceTorFullState_class, incidenceTorFullState_class,
    edgeSignFreeTerm_val, mapRange_edgeSignResolution]

/-- The edge sign that is `-1` on one edge and `1` elsewhere. -/
def singleEdgeSign (e : E) : EdgeSign E := fun e' => if e' = e then -1 else 1

/-- The sign of an edge set for the edge sign of a single edge. -/
theorem setSign_singleEdgeSign (e : E) (T : Finset E) :
    (singleEdgeSign e).setSign ℂ T = if e ∈ T then -1 else 1 := by
  unfold EdgeSign.setSign singleEdgeSign
  have h : ∀ e' : E, ((((if e' = e then (-1 : ℤˣ) else 1 : ℤˣ) : ℤ) : ℂ)) =
      if e' = e then -1 else 1 := by
    intro e'
    split_ifs <;> simp
  simp only [h]
  exact Finset.prod_ite_eq' T e (fun _ => (-1 : ℂ))

/-- A resolution state of homological degree zero whose edge set is the cycle union `S` is the
state of `S`. -/
theorem eq_cycleUnionState_of_fst_eq {S : Finset E} (hS : G.IsCycleUnion S)
    (b : G.IncResolutionBasis) (hb : G.incResolutionDegree b = 0) (h : b.1 = S) :
    b = G.cycleUnionState S hS := by
  have key : ∀ (T : Finset E) (hT : G.IsCycleUnion T), T = S →
      G.cycleUnionState T hT = G.cycleUnionState S hS := by
    rintro T hT rfl
    rfl
  rw [G.eq_cycleUnionState b hb]
  exact key _ _ h

/-- **Edge-sign characters separate edge sets.** A degree-zero Tor class on which every edge sign
acts through the character of the edge set `S` is a scalar multiple of the class of `S` (zero if
`S` is not a cycle union). -/
theorem exists_eq_smul_cycleUnionClass (S : Finset E) (y : G.incidenceTor 0)
    (hy : ∀ ε : EdgeSign E, G.edgeSignState ε ℂ (G.incidenceTorFullState 0 y) =
      ε.setSign ℂ S • G.incidenceTorFullState 0 y) :
    ∃ c : ℂ, y = c • G.cycleUnionClass S := by
  -- every state where the class is nonzero has edge set `S`
  have hsupp : ∀ b : G.IncResolutionBasis, G.incidenceTorFullState 0 y b ≠ 0 → b.1 = S := by
    intro b hb
    by_contra hne
    obtain ⟨e, he⟩ : ∃ e, ¬ (e ∈ b.1 ↔ e ∈ S) := by
      by_contra h
      push Not at h
      exact hne (Finset.ext h)
    have h := congrArg (fun z => z b) (hy (singleEdgeSign e))
    simp only [edgeSignState_apply, Finsupp.smul_apply, smul_eq_mul,
      setSign_singleEdgeSign] at h
    apply hb
    by_cases hb1 : e ∈ b.1
    · have hS : e ∉ S := fun hS => he (iff_of_true hb1 hS)
      simp only [hb1, hS, ite_true, ite_false] at h
      linear_combination -h / 2
    · have hS : e ∈ S := by
        by_contra hS
        exact he (iff_of_false hb1 hS)
      simp only [hb1, hS, ite_true, ite_false] at h
      linear_combination h / 2
  by_cases hS : G.IsCycleUnion S
  · refine ⟨G.incidenceTorFullState 0 y (G.cycleUnionState S hS), ?_⟩
    apply G.incidenceTorFullState_injective 0
    rw [map_smul, G.incidenceTorFullState_cycleUnionClass hS]
    ext b
    rw [Finsupp.smul_apply, smul_eq_mul]
    by_cases hb : b = G.cycleUnionState S hS
    · rw [hb, single_eq_same, mul_one]
    · rw [single_eq_of_ne hb, mul_zero]
      by_contra h0
      apply hb
      have hb1 := hsupp b h0
      by_cases hdeg : G.incResolutionDegree b = 0
      · exact G.eq_cycleUnionState_of_fst_eq hS b hdeg hb1
      · exact absurd (G.incidenceTorFullState_apply_of_ne 0 y b hdeg) h0
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    apply G.incidenceTorFullState_injective 0
    rw [map_zero]
    ext b
    rw [Finsupp.zero_apply]
    by_contra h0
    have hb1 := hsupp b h0
    by_cases hdeg : G.incResolutionDegree b = 0
    · exact hS (hb1 ▸ G.isCycleUnion_of_incResolutionDegree_eq_zero b hdeg)
    · exact h0 (G.incidenceTorFullState_apply_of_ne 0 y b hdeg)

/-- An edge sign acts on the class of a cycle union through the character of its edge set. -/
theorem incidenceRingToTor_edgeSign_of_cycleUnionClass {S : Finset E} (hS : G.IsCycleUnion S)
    (ε : EdgeSign E) (u : G.IncidenceRing) (hu : G.incidenceRingToTor u = G.cycleUnionClass S) :
    G.incidenceRingToTor (G.edgeSignIncidence ε u) = ε.setSign ℂ S • G.cycleUnionClass S := by
  apply G.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_edgeSign, hu, map_smul, G.incidenceTorFullState_cycleUnionClass hS,
    edgeSignState_single, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end EdgeSignTorZero

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Where the class of a cycle goes -/

/-- **The image of the class of a cycle union.** The degree-zero Tor map sends the class of a
cycle union `S` of `G` to a scalar multiple of the class of the edge set `S` in `H`; the latter is
zero unless `S` is a cycle union of `H`. -/
theorem exists_incidenceTorMap_cycleUnionClass {S : Finset E} (hS : G.IsCycleUnion S) :
    ∃ c : ℂ, φ.incidenceTorMap 0 (G.cycleUnionClass S) = c • H.cycleUnionClass S := by
  obtain ⟨u, hu⟩ := G.incidenceRingToTor_surjective (G.cycleUnionClass S)
  apply H.exists_eq_smul_cycleUnionClass S
  intro ε
  have hy : φ.incidenceTorMap 0 (G.cycleUnionClass S) =
      H.incidenceRingToTor (φ.incidenceHom u) := by
    rw [← hu, incidenceTorMap_incidenceRingToTor]
  rw [hy, ← incidenceTorFullState_edgeSign, ← incidenceHom_edgeSignIncidence,
    ← φ.incidenceTorMap_incidenceRingToTor (G.edgeSignIncidence ε u),
    G.incidenceRingToTor_edgeSign_of_cycleUnionClass hS ε u hu, map_smul, map_smul, ← hy]

/-- If the vertex function identifies two distinct vertices of a cycle union, its class goes to
zero. -/
theorem incidenceTorMap_cycleUnionClass_of_identify {S : Finset E} (hS : G.IsCycleUnion S)
    {v v' : V} (hv : v ∈ G.support S) (hv' : v' ∈ G.support S) (hne : v ≠ v')
    (h : φ.vertex v = φ.vertex v') : φ.incidenceTorMap 0 (G.cycleUnionClass S) = 0 := by
  obtain ⟨c, hc⟩ := φ.exists_incidenceTorMap_cycleUnionClass hS
  rw [hc, H.cycleUnionClass_of_not (φ.not_isCycleUnion_of_identify hS hv hv' hne h), smul_zero]

/-- The simple cycle of `H` given by a simple cycle of `G` on whose vertices the vertex function is
injective. -/
def mapCycle (C : G.SimpleCycle) (h : Set.InjOn φ.vertex (G.support C.val)) : H.SimpleCycle :=
  ⟨C.val, φ.isSimpleCycle_of_injOn C.property h⟩

@[simp] theorem mapCycle_val (C : G.SimpleCycle) (h : Set.InjOn φ.vertex (G.support C.val)) :
    (φ.mapCycle C h).val = C.val := rfl

/-- The image of the generator `z_C` in degree-zero Tor is a scalar multiple of the class of the
edge set `C` in `H`. -/
theorem exists_incidenceTorMap_cycleClass (C : G.SimpleCycle) :
    ∃ c : ℂ, φ.incidenceTorMap 0 (G.cycleClass C) = c • H.cycleUnionClass C.val :=
  φ.exists_incidenceTorMap_cycleUnionClass C.property.isCycleUnion

/-- The image of `z_C` in the cycle-compatibility algebra of `H` is a scalar multiple of the
element corresponding to the class of the edge set `C`. -/
theorem exists_cycleAlgebraHom_X (C : G.SimpleCycle) :
    ∃ c : ℂ, φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) =
      c • H.cycleAlgebraEquivTor.symm (H.cycleUnionClass C.val) := by
  obtain ⟨c, hc⟩ := φ.exists_incidenceTorMap_cycleClass C
  refine ⟨c, H.cycleAlgebraEquivTor.injective ?_⟩
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_X, hc, map_smul,
    AlgEquiv.apply_symm_apply]

/-- **`z_C ↦ c · z_{φ(C)}`.** If the vertex function is injective on the vertices of a simple cycle
`C`, then `C` is a simple cycle of `H` and `z_C` goes to a scalar multiple of `z_C` in the
cycle-compatibility algebra of `H`. -/
theorem cycleAlgebraHom_X_of_injOn (C : G.SimpleCycle) (h : Set.InjOn φ.vertex (G.support C.val)) :
    ∃ c : ℂ, φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) =
      c • Ideal.Quotient.mk H.cycleCompatibilityIdeal (X (φ.mapCycle C h)) := by
  obtain ⟨c, hc⟩ := φ.exists_cycleAlgebraHom_X C
  refine ⟨c, ?_⟩
  rw [hc]
  congr 1
  apply H.cycleAlgebraEquivTor.injective
  rw [AlgEquiv.apply_symm_apply, cycleAlgebraEquivTor_X]
  rfl

/-- **`z_C ↦ 0`.** If the vertex function identifies two distinct vertices of a simple cycle `C`,
then `z_C` goes to zero. -/
theorem cycleAlgebraHom_X_of_identify (C : G.SimpleCycle) {v v' : V} (hv : v ∈ G.support C.val)
    (hv' : v' ∈ G.support C.val) (hne : v ≠ v') (h : φ.vertex v = φ.vertex v') :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) = 0 := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, cycleAlgebraEquivTor_X, map_zero]
  exact φ.incidenceTorMap_cycleUnionClass_of_identify C.property.isCycleUnion hv hv' hne h

/-- `z_C` goes to zero exactly when it is not sent to a multiple of a generator: if the vertex
function is not injective on the vertices of `C`, the image is zero. -/
theorem cycleAlgebraHom_X_of_not_injOn (C : G.SimpleCycle)
    (h : ¬ Set.InjOn φ.vertex (G.support C.val)) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C)) = 0 := by
  simp only [Set.InjOn, not_forall] at h
  obtain ⟨v, hv, v', hv', hvv', hne⟩ := h
  exact φ.cycleAlgebraHom_X_of_identify C hv hv' hne hvv'

/-! ## The acceptance example -/

/-- If the vertex function sends a vertex of `C` and a vertex of `D` to the same vertex, the images
of `z_C` and `z_D` multiply to zero. -/
theorem cycleAlgebraHom_X_mul_X_of_identify (C D : G.SimpleCycle) {c d : V}
    (hc : c ∈ G.support C.val) (hd : d ∈ G.support D.val) (h : φ.vertex c = φ.vertex d) :
    φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D)) = 0 := by
  apply H.cycleAlgebraEquivTor.injective
  rw [cycleAlgebraEquivTor_cycleAlgebraHom, map_mul, map_mul, map_zero, cycleAlgebraEquivTor_X,
    cycleAlgebraEquivTor_X, incidenceTorMap_zero_mul]
  obtain ⟨a, ha⟩ := φ.exists_incidenceTorMap_cycleClass C
  obtain ⟨b, hb⟩ := φ.exists_incidenceTorMap_cycleClass D
  rw [ha, hb, smul_mul_smul_comm, H.cycleUnionClass_mul_of_not_disjoint, smul_zero]
  rw [Finset.not_disjoint_iff]
  exact ⟨φ.vertex c, φ.vertex_mem_support hc, h ▸ φ.vertex_mem_support hd⟩

/-- For vertex-disjoint simple cycles `C` and `D` the product `z_C z_D` is nonzero in the
cycle-compatibility algebra. -/
theorem _root_.BPFixedPoints.Multigraph.cycleAlgebra_X_mul_X_ne_zero (C D : G.SimpleCycle)
    (h : Disjoint (G.support C.val) (G.support D.val)) :
    Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D) ≠ 0 := by
  intro h0
  have h1 := congrArg G.cycleAlgebraEquivTor h0
  rw [map_mul, map_mul, map_zero, cycleAlgebraEquivTor_X, cycleAlgebraEquivTor_X, cycleClass,
    cycleClass, G.cycleUnionClass_mul_of_disjoint C.property.isCycleUnion D.property.isCycleUnion h,
    cycleUnionSign_eq_pow] at h1
  have hne := G.cycleUnionClass_ne_zero
    (G.isCycleUnion_union C.property.isCycleUnion D.property.isCycleUnion h)
  exact hne ((smul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (by norm_num)))

/-- **Acceptance example.** Let `C` and `D` be vertex-disjoint simple cycles of `G`, and let the
vertex function identify a vertex of `C` with a vertex of `D`. Then `z_C z_D` is nonzero in the
cycle-compatibility algebra of `G`, and it goes to zero, since the images share a vertex in `H`. -/
theorem cycleAlgebraHom_acceptance (C D : G.SimpleCycle)
    (hCD : Disjoint (G.support C.val) (G.support D.val)) {c d : V} (hc : c ∈ G.support C.val)
    (hd : d ∈ G.support D.val) (h : φ.vertex c = φ.vertex d) :
    Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D) ≠ 0 ∧
      φ.cycleAlgebraHom (Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C * X D)) = 0 :=
  ⟨cycleAlgebra_X_mul_X_ne_zero C D hCD, φ.cycleAlgebraHom_X_mul_X_of_identify C D hc hd h⟩

end VertexMap

end BPFixedPoints.Multigraph
