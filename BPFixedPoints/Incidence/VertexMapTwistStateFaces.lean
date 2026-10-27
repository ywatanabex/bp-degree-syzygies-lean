import BPFixedPoints.Incidence.VertexMapTwistStateFrames
import BPFixedPoints.Incidence.VertexMapCellPullback
import BPFixedPoints.Incidence.VertexPermutationTwistFaces

/-!
# Face coordinates of pulled back multi-twist sections

Let `f : V → W` be any function of finite vertex sets, `a_f : (P¹)^W → (P¹)^V` its coordinate map
and `a_f^* O(a) ≅ O(b)` the twist isomorphism `vertexTwistPullbackIso` of `VertexMapPullbackTwist`
(`b w = Σ_{f v = w} a v`). For a face `q : W → Fin 3`, the coordinate map sends the face open of `q`
into the face open of `q ∘ f` (`vertexFaceOpen_le_preimage`), and the face coordinate rings are
related by the comorphism `facePull f q R : FaceRing R (q ∘ f) →ₐ[R] FaceRing R q`, which sends the
variable of `v` to the variable of `f v` (exponent vectors are summed over the fibres of `f`,
`faceMonoidPull`).

Proved here:
* the face maps commute with `a_f` after `facePull` (`vertexFaceι_pull`), hence the face
  coordinates of a pulled back function are the pulled back face coordinates
  (`vertexFaceSectionsEquiv_pull`);
* the comparison `g⁻¹ M → g^* M` sends inverse images of sections to images under the unit of the
  module adjunction (`moduleSheafPullbackComparison_topPullSection`);
* **face coordinates of pulled back twist sections** (`vertexTwistPullSection_faceSections`): for a
  section `s` of `O(a)` on the face open of `q ∘ f`, the face coordinates on the face of `q` of its
  image `vertexTwistPullSection` (unit of the module adjunction followed by the twist isomorphism)
  are `facePull f q R` of the face coordinates of `s`. This uses the frame computation
  `pullLocalFrame_coefficient` of `VertexMapTwistStateFrames` on the chart frames that define the
  twist isomorphism; nothing is defined through states.

These hold for every function `f`, including functions identifying vertices.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open ProjectiveLine CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

section Pull

variable {V W : Type} [DecidableEq W] (f : V → W) (q : W → Fin 3)

/-- The exponent vectors of a face of `V` pulled back from a face `q` of `W` along `f`, pushed to
`W` by summing over the fibres. -/
noncomputable def faceMonoidPull [Fintype V] :
    FaceMonoid (fun v => q (f v)) →+ FaceMonoid q :=
  ∑ v, (AddMonoidHom.single (fun w => FaceExponent (q w)) (f v)).comp
    (Pi.evalAddMonoidHom (fun v => FaceExponent (q (f v))) v)

/-- The pulled back exponent vector of a single exponent at `v` is the single exponent at `f v`. -/
theorem faceMonoidPull_single [Fintype V] [DecidableEq V] (v : V)
    (x : FaceExponent (q (f v))) :
    faceMonoidPull f q (Pi.single (M := fun v => FaceExponent (q (f v))) v x) =
      Pi.single (M := fun w => FaceExponent (q w)) (f v) x := by
  rw [faceMonoidPull, AddMonoidHom.finsetSum_apply, Finset.sum_eq_single v]
  · simp
  · intro u _ hu
    simp [Pi.single_eq_of_ne hu]
  · intro h
    exact absurd (Finset.mem_univ v) h

variable (R : Type) [CommRing R]

/-- **The comorphism of the coordinate map on face rings**: the variable of `v` of the face
`q ∘ f` goes to the variable of `f v` of the face `q`. -/
noncomputable def facePull [Fintype V] : FaceRing R (fun v => q (f v)) →ₐ[R] FaceRing R q :=
  AddMonoidAlgebra.mapDomainAlgHom R R (faceMonoidPull f q)

/-- The comorphism of face rings on monomials. -/
theorem facePull_single [Fintype V] (m : FaceMonoid (fun v => q (f v))) (r : R) :
    facePull f q R (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single (faceMonoidPull f q m) r :=
  AddMonoidAlgebra.mapDomain_single

/-- The pulled back variable of `v` is the variable of `f v`. -/
theorem facePull_faceVariable [Fintype V] [DecidableEq V] (v : V) :
    facePull f q R (faceVariable R (fun v => q (f v)) v) = faceVariable R q (f v) := by
  rw [faceVariable, facePull_single, faceMonoidPull_single, faceVariable]

end Pull

section Faces

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] (f : V → W)

/-- **Face maps along the coordinate map.** The face map of `q` followed by the coordinate map
`a_f` is the face map of `q ∘ f` after the comorphism of face rings. -/
theorem vertexFaceι_pull (q : W → Fin 3) :
    Spec.map (CommRingCat.ofHom (facePull f q R).toRingHom) ≫ vertexFaceι R V (fun v => q (f v)) =
      vertexFaceι R W q ≫ vertexSchemeMap R f := by
  let k : vertexFaceOverBase R W q ⟶ vertexFaceOverBase R V (fun v => q (f v)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (facePull f q R).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (facePull f q R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R (fun v => q (f v))))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R q)))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (facePull f q R).comp_algebraMap))
  have he : k ≫ vertexFaceOver R V (fun v => q (f v)) =
      vertexFaceOver R W q ≫ vertexOverBaseMap R f := by
    apply vertexOverBase_hom_ext R
    intro v
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (facePull f q R).toRingHom) ≫
        vertexFaceι R V (fun v => q (f v))) ≫ (vertexProjectionOver R V v).left =
      (vertexFaceι R W q ≫ vertexSchemeMap R f) ≫ (vertexProjectionOver R V v).left
    rw [Category.assoc, vertexFaceι_projection, Category.assoc, vertexSchemeMap_projection,
      vertexFaceι_projection]
    dsimp only [vertexFaceProjection]
    rw [evaluationChart_natural]
    have hc : (facePull f q R).toRingHom.comp (algebraMap R (FaceRing R (fun v => q (f v)))) =
        algebraMap R (FaceRing R q) := (facePull f q R).comp_algebraMap
    rw [hc]
    change evaluationChart (algebraMap R (FaceRing R q))
      (facePull f q R (faceVariable R (fun v => q (f v)) v)) (vertexFacePivot (q (f v))) = _
    rw [facePull_faceVariable]
  exact congrArg Over.Hom.left he

omit [DecidableEq V] [DecidableEq W] in
/-- The coordinate map pulls back the face open of a face of `V` to the face open of the same face
for the cover `v ↦ U_W (f v)`. -/
theorem vertexSchemeMap_preimage_faceOpen (p : V → Fin 3) :
    vertexSchemeMap R f ⁻¹ᵁ binaryCoverFaceOpen (vertexCoordinateOpen R V) p =
      binaryCoverFaceOpen (fun v => vertexCoordinateOpen R W (f v)) p :=
  faceOpen_pull (vertexSchemeMap R f).base (fun v => vertexCoordinateOpen R W (f v))
    (vertexCoordinateOpen R V) (fun v i => vertexSchemeMap_preimage_coordinateOpen R f v i) p

omit [DecidableEq V] [DecidableEq W] in
/-- The face open of `q` lies in the preimage of the face open of `q ∘ f`. -/
theorem vertexFaceOpen_le_preimage (q : W → Fin 3) :
    binaryCoverFaceOpen (vertexCoordinateOpen R W) q ≤
      vertexSchemeMap R f ⁻¹ᵁ binaryCoverFaceOpen (vertexCoordinateOpen R V) (fun v => q (f v)) := by
  rw [vertexSchemeMap_preimage_faceOpen]
  exact le_iInf fun v => iInf_le (fun w => binaryCoverFaceFactor (vertexCoordinateOpen R W w) (q w))
    (f v)

/-- **Face coordinates of pulled back functions.** The face coordinates on the face of `q` of the
pullback of a function on the face of `q ∘ f` are the pulled back face coordinates. -/
theorem vertexFaceSectionsEquiv_pull (q : W → Fin 3)
    (y : Γ(vertexScheme R V, binaryCoverFaceOpen (vertexCoordinateOpen R V) (fun v => q (f v)))) :
    vertexFaceSectionsEquiv R W q ((vertexScheme R W).presheaf.map
        (homOfLE (vertexFaceOpen_le_preimage R f q)).op ((vertexSchemeMap R f).app _ y)) =
      facePull f q R (vertexFaceSectionsEquiv R V (fun v => q (f v)) y) :=
  affineOpenSectionsIsoAt_pullback (vertexSchemeMap R f)
    (CommRingCat.ofHom (facePull f q R).toRingHom) (vertexFaceι R W q)
    (vertexFaceι R V (fun v => q (f v))) (vertexFaceι_pull R f q) _ _ (vertexFaceι_opensRange R W q)
    (vertexFaceι_opensRange R V _) _ y

end Faces

section Comparison

variable {X Y : Scheme.{0}} (g : Y ⟶ X) (M : X.Modules)

/-- **The comparison `g⁻¹ M → g^* M` on pulled back sections.** It sends the inverse image of a
section (the unit of the abelian adjunction) to its image under the unit of the module adjunction. -/
theorem moduleSheafPullbackComparison_topPullSection (O : X.Opens) (s : Γ(M, O)) :
    (moduleSheafPullbackComparison g M).hom.app (op ((Opens.map g.base).obj O))
        (topPullSection g.base ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) O s) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app O) s := by
  have h : ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g.base).homEquiv _ _)
      (moduleSheafPullbackComparison g M) = (SheafOfModules.toSheaf X.ringCatSheaf).map
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) := by
    unfold moduleSheafPullbackComparison
    exact Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op O)) h) s

end Comparison

section Twist

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] (f : V → W) (a : V → ℤ) (b : W → ℤ)
  (hb : ∀ w, b w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), a v)

omit [DecidableEq V] [DecidableEq W] in
/-- The pulled back chart frames of `VertexMapPullbackTwist` are pulled back local frames. -/
theorem vertexTwistPullChartIso_eq (τ : W → Fin 2) :
    vertexTwistPullChartIso R f a τ =
      pullLocalFrame (vertexSchemeMap R f) (vertexTwistSheaf R V a)
        (vertexChartOpen R V (fun v => τ (f v))) (vertexTwistSheafChartIso R V a _)
        (vertexChartOpen R W τ) (vertexChartMapLift R f τ) (vertexChartMapLift_fac R f τ) :=
  rfl

omit [DecidableEq V] in
/-- The chart coefficients of `O(b)` after the twist isomorphism are the coefficients of the
pulled back chart frame. -/
theorem vertexTwistSheafChartCoefficient_pullbackIso (τ : W → Fin 2) (S : (vertexScheme R W).Opens)
    (hS : S ≤ vertexChartOpen R W τ) (t : Γ(vertexTwistPullback R f a, S)) :
    vertexTwistSheafChartCoefficient R W b τ S hS ((vertexTwistPullbackIso R f a b hb).hom.app S t) =
      ((moduleOverUnitIso (vertexScheme R W) (vertexTwistPullback R f a) (vertexChartOpen R W τ)
        (vertexTwistPullChartIso R f a τ)).hom.val.app (op (Over.mk (homOfLE hS)))).hom t :=
  congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hS)))).hom t)
    (vertexTwistPullbackIso_chart R f a b hb τ)

/-- The section of `O(b)` over the preimage of an open given by a section of `O(a)`: the unit of
the module adjunction for `a_f`, followed by the twist isomorphism. -/
noncomputable def vertexTwistPullSection (O : (vertexScheme R V).Opens)
    (s : Γ(vertexTwistSheaf R V a, O)) : Γ(vertexTwistSheaf R W b, vertexSchemeMap R f ⁻¹ᵁ O) :=
  (vertexTwistPullbackIso R f a b hb).hom.app _
    ((((Scheme.Modules.pullbackPushforwardAdjunction (vertexSchemeMap R f)).unit.app
      (vertexTwistSheaf R V a)).app O) s)

/-- **Face coordinates of pulled back twist sections.** On the face of `q`, the face coordinates
of the pulled back section of a section of `O(a)` on the face of `q ∘ f` are the pulled back face
coordinates. -/
theorem vertexTwistPullSection_faceSections (q : W → Fin 3)
    (s : Γ(vertexTwistSheaf R V a, binaryCoverFaceOpen (vertexCoordinateOpen R V) (fun v => q (f v)))) :
    vertexTwistSheafFaceSectionsEquiv R W b q ((vertexTwistSheaf R W b).presheaf.map
        (homOfLE (vertexFaceOpen_le_preimage R f q)).op (vertexTwistPullSection R f a b hb _ s)) =
      facePull f q R (vertexTwistSheafFaceSectionsEquiv R V a (fun v => q (f v)) s) := by
  rw [vertexTwistSheafFaceSectionsEquiv_apply, vertexTwistSheafFaceSectionsEquiv_apply,
    vertexTwistPullSection]
  have hn := ConcreteCategory.congr_hom
    ((vertexTwistPullbackIso R f a b hb).hom.mapPresheaf.naturality
      (homOfLE (vertexFaceOpen_le_preimage R f q)).op)
    ((((Scheme.Modules.pullbackPushforwardAdjunction (vertexSchemeMap R f)).unit.app
      (vertexTwistSheaf R V a)).app _) s)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
  erw [← hn, vertexTwistSheafChartCoefficient_pullbackIso, vertexTwistPullChartIso_eq,
    pullLocalFrame_coefficient]
  exact vertexFaceSectionsEquiv_pull R f q _

end Twist

end BPFixedPoints.Multigraph
