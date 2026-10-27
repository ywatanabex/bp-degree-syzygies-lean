import BPFixedPoints.Incidence.ProjectivePowerCoordinates
import BPFixedPoints.Incidence.ProjectiveLineChartPreimages
import BPFixedPoints.Incidence.CechFaceTransitionUnits

/-! # Original mixed face coordinates in the actual projective product

The maps use the existing face rings and their existing refinements. Right
coordinates invert on Laurent faces by the original Proj transition formula.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- A Laurent face uses the original left pivot; a right face uses the right pivot. -/
def vertexFacePivot (i : Fin 3) : Fin 2 := if i = 1 then 1 else 0

/-- The original face coordinate as an actual morphism to its Proj factor. -/
noncomputable def vertexFaceProjection (q : V → Fin 3) (v : V) :
    Spec (CommRingCat.of (FaceRing R q)) ⟶ projectiveLine R :=
  evaluationChart (algebraMap R (FaceRing R q)) (faceVariable R q v) (vertexFacePivot (q v))

omit [Fintype V] in
/-- Original face refinement keeps the actual projective coordinate, including inversion. -/
@[reassoc] theorem vertexFaceProjection_refinement {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) ≫
      vertexFaceProjection R V q v = vertexFaceProjection R V r v := by
  dsimp only [vertexFaceProjection]
  rw [evaluationChart_natural]
  have hc : (faceRefinementMap R h).toRingHom.comp (algebraMap R (FaceRing R q)) =
      algebraMap R (FaceRing R r) := (faceRefinementMap R h).comp_algebraMap
  rw [hc]
  change evaluationChart (algebraMap R (FaceRing R r))
    (faceRefinementMap R h (faceVariable R q v)) (vertexFacePivot (q v)) = _
  rw [faceRefinement_variable]
  split_ifs with hf
  · simp only [vertexFacePivot, hf.1, hf.2, ite_true, Fin.reduceEq, ite_false]
    simpa only [faceLaurentUnit_val] using
      (evaluationChart_unit_transition (algebraMap R (FaceRing R r)) (faceLaurentUnit R r v hf.2)).symm
  · have hp : vertexFacePivot (q v) = vertexFacePivot (r v) := by
      rcases h v with he | he
      · rw [he]
      · have hq : q v ≠ 1 := fun hh => hf ⟨hh, he⟩
        simp [vertexFacePivot, hq, he]
    rw [hp]

/-- The original mixed face spectrum over its original coefficient scheme. -/
noncomputable def vertexFaceOverBase (q : V → Fin 3) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R q))))

/-- Each original face coordinate respects the original base map. -/
noncomputable def vertexFaceProjectionOver (q : V → Fin 3) (v : V) :
    vertexFaceOverBase R V q ⟶ overBase R :=
  Over.homMk (vertexFaceProjection R V q v) (evaluationChart_toSpecBase _ _ _)

/-- Assemble the original face coordinates by the actual product universal property. -/
noncomputable def vertexFaceOver (q : V → Fin 3) :
    vertexFaceOverBase R V q ⟶ vertexOverBase R V :=
  (vertexIsProduct R V).lift (Fan.mk (vertexFaceOverBase R V q) (vertexFaceProjectionOver R V q))

/-- The original polynomial/Laurent face maps into the actual projective product. -/
noncomputable def vertexFaceι (q : V → Fin 3) :
    Spec (CommRingCat.of (FaceRing R q)) ⟶ vertexScheme R V := (vertexFaceOver R V q).left

/-- The actual face map retains every original vertex coordinate. -/
@[reassoc] theorem vertexFaceι_projection (q : V → Fin 3) (v : V) :
    vertexFaceι R V q ≫ (vertexProjectionOver R V v).left = vertexFaceProjection R V q v :=
  congrArg Over.Hom.left ((vertexIsProduct R V).fac
    (Fan.mk (vertexFaceOverBase R V q) (vertexFaceProjectionOver R V q)) ⟨v⟩)

/-- The actual face map retains the original coefficient inclusion. -/
@[reassoc] theorem vertexFaceι_toBase (q : V → Fin 3) :
    vertexFaceι R V q ≫ vertexToBase R V =
      Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R q))) := (vertexFaceOver R V q).w

/-- Actual face maps commute with the existing mixed-coordinate restrictions. -/
@[reassoc] theorem vertexFaceι_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) ≫ vertexFaceι R V q =
      vertexFaceι R V r := by
  let g : vertexFaceOverBase R V r ⟶ vertexFaceOverBase R V q :=
    Over.homMk (Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R q))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R r)))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext ((faceRefinementMap R h).comp_algebraMap)))
  have he : g ≫ vertexFaceOver R V q = vertexFaceOver R V r := by
    apply (vertexIsProduct R V).hom_ext
    intro ⟨v⟩
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) ≫ vertexFaceι R V q) ≫
      (vertexProjectionOver R V v).left = vertexFaceι R V r ≫ (vertexProjectionOver R V v).left
    rw [Category.assoc, vertexFaceι_projection, vertexFaceι_projection, vertexFaceProjection_refinement]
  exact congrArg Over.Hom.left he

/-- The original Boolean chart choices as the actual two Proj pivots. -/
def vertexBooleanPivot (σ : V → Bool) (v : V) : Fin 2 := if σ v then 1 else 0

/-- An overlap-free original face uses the original vertex polynomial chart. -/
@[reassoc] theorem vertexFaceι_chart (σ : V → Bool) :
    Spec.map (CommRingCat.ofHom (chartFaceRingEquiv (R := R) σ).symm.toRingHom) ≫
      vertexChartι R V (vertexBooleanPivot V σ) = vertexFaceι R V (chartFace σ) := by
  let g : vertexFaceOverBase R V (chartFace σ) ⟶ SchemeTools.polynomialOverBase R V :=
    Over.homMk (Spec.map (CommRingCat.ofHom (chartFaceRingEquiv (R := R) σ).symm.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (chartFaceRingEquiv (R := R) σ).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial V R))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R (chartFace σ))))
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro c
      exact (chartFaceRingEquiv (R := R) σ).symm.commutes c)
  have he : g ≫ vertexChartOver R V (vertexBooleanPivot V σ) = vertexFaceOver R V (chartFace σ) := by
    apply (vertexIsProduct R V).hom_ext
    intro ⟨v⟩
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (chartFaceRingEquiv (R := R) σ).symm.toRingHom) ≫
      vertexChartι R V (vertexBooleanPivot V σ)) ≫ (vertexProjectionOver R V v).left =
        vertexFaceι R V (chartFace σ) ≫ (vertexProjectionOver R V v).left
    rw [Category.assoc, vertexChartι_projection, vertexFaceι_projection]
    have hp : vertexFacePivot (chartFace σ v) = vertexBooleanPivot V σ v := by
      cases hb : σ v <;> simp [vertexFacePivot, vertexBooleanPivot, chartFace, hb]
    dsimp only [vertexFaceProjection, evaluationChart]
    rw [hp, ← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro c
      simpa using (chartFaceRingEquiv (R := R) σ).symm.commutes c
    · simp
  exact congrArg Over.Hom.left he

end BPFixedPoints.ProjectiveLine
