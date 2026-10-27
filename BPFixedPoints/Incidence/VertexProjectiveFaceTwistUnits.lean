import BPFixedPoints.Incidence.VertexProjectiveFaceSections
import BPFixedPoints.Incidence.VertexProjectiveTwistPairCoefficients
import BPFixedPoints.Incidence.ProjectiveLineLaurentEvaluation
import BPFixedPoints.Incidence.SchemeModuleGeometricCoefficients
import BPFixedPoints.Incidence.CechLineBundleTransitions

/-! # Original geometric twist units in the existing mixed face coordinates -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- A refined face lies in both original canonical containing charts. -/
theorem vertexFaceRefinement_le_pair {q r : V → Fin 3} (h : FaceRefines q r) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r ≤
      vertexChartPairOpen R V (vertexBooleanPivot V (vertexFaceBaseChoice V q))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r)) :=
  le_inf ((vertexBinaryFaceOpen_refinement R V h).trans
    (vertexBinaryFaceOpen_le_chart R V _ q (vertexFaceBaseChoice_refines V q)))
    (vertexBinaryFaceOpen_le_chart R V _ r (vertexFaceBaseChoice_refines V r))

/-- The original affine face factors through the actual original pair open. -/
noncomputable def vertexFaceRefinementPairLift {q r : V → Fin 3} (h : FaceRefines q r) :
    Spec (CommRingCat.of (FaceRing R r)) ⟶
      (vertexChartPairOpen R V (vertexBooleanPivot V (vertexFaceBaseChoice V q))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r))).toScheme :=
  IsOpenImmersion.lift _ (vertexFaceι R V r) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply vertexFaceRefinement_le_pair R V h
    rw [← vertexFaceι_opensRange R V r]
    exact ⟨x,rfl⟩)

/-- The factorization retains the original affine face morphism. -/
@[reassoc] theorem vertexFaceRefinementPairLift_fac {q r : V → Fin 3} (h : FaceRefines q r) :
    vertexFaceRefinementPairLift R V h ≫
      (vertexChartPairOpen R V (vertexBooleanPivot V (vertexFaceBaseChoice V q))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r))).ι = vertexFaceι R V r :=
  IsOpenImmersion.lift_fac _ _ _

/-- The pair-factor path is the original face projection at every vertex. -/
@[reassoc] theorem vertexFaceRefinementPairLift_projection {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    (vertexFaceRefinementPairLift R V h ≫
      vertexChartPairProjectionLift R V (vertexBooleanPivot V (vertexFaceBaseChoice V q))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r)) v) ≫
          (standardPairOpen R (vertexBooleanPivot V (vertexFaceBaseChoice V q) v)
            (vertexBooleanPivot V (vertexFaceBaseChoice V r) v)).ι = vertexFaceProjection R V r v := by
  rw [Category.assoc, vertexChartPairProjectionLift_fac, ← Category.assoc,
    vertexFaceRefinementPairLift_fac, vertexFaceι_projection]

/-- Each original geometric pair-factor unit evaluates to its existing face transition power. -/
theorem vertexFaceRefinement_factor_unit {q r : V → Fin 3} (h : FaceRefines q r)
    (a : V → ℤ) (v : V) :
    (Scheme.ΓSpecIso (CommRingCat.of (FaceRing R r))).hom
      ((vertexFaceRefinementPairLift R V h ≫
        vertexChartPairProjectionLift R V (vertexBooleanPivot V (vertexFaceBaseChoice V q))
          (vertexBooleanPivot V (vertexFaceBaseChoice V r)) v).appTop
            (twistSheafPairUnit R (a v) (vertexBooleanPivot V (vertexFaceBaseChoice V q) v)
              (vertexBooleanPivot V (vertexFaceBaseChoice V r) v) :
                Γ((standardPairOpen R (vertexBooleanPivot V (vertexFaceBaseChoice V q) v)
                  (vertexBooleanPivot V (vertexFaceBaseChoice V r) v)).toScheme, ⊤))) =
      (faceTransitionUnit R h v ^ a v : (FaceRing R r)ˣ) := by
  by_cases hf : q v = 1 ∧ r v = 2
  · have hi : vertexBooleanPivot V (vertexFaceBaseChoice V q) v = 1 := by
      simp [vertexBooleanPivot, vertexFaceBaseChoice, hf.1]
    have hj : vertexBooleanPivot V (vertexFaceBaseChoice V r) v = 0 := by
      simp [vertexBooleanPivot, vertexFaceBaseChoice, hf.2]
    simp only [faceTransitionUnit, dite_eq_left hf]
    apply pairUnit_evaluation_reverse_of_eq (algebraMap R (FaceRing R r)) (faceLaurentUnit R r v hf.2)
      (a v) _ _ hi hj
    simpa only [vertexFaceProjection, vertexFacePivot, hf.2, Fin.reduceEq, ite_false, faceLaurentUnit_val]
      using vertexFaceRefinementPairLift_projection R V h v
  · have he : vertexBooleanPivot V (vertexFaceBaseChoice V q) v =
        vertexBooleanPivot V (vertexFaceBaseChoice V r) v := by
      rcases h v with he | he
      · simp [vertexBooleanPivot, vertexFaceBaseChoice, he]
      · have hq : q v ≠ 1 := fun hh => hf ⟨hh,he⟩
        simp [vertexBooleanPivot, vertexFaceBaseChoice, he, hq]
    have hu : twistSheafPairUnit R (a v) (vertexBooleanPivot V (vertexFaceBaseChoice V q) v)
        (vertexBooleanPivot V (vertexFaceBaseChoice V r) v) = 1 := by
      exact twistSheafPairUnit_eq_one_of_eq R (a v) _ _ he
    rw [hu]
    simp [faceTransitionUnit, hf]

/-- The originally specified geometric pair transition has exactly the existing multi-twist coordinate. -/
theorem vertexFaceRefinement_pair_unit {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    vertexFaceSectionsEquiv R V r
      (vertexTwistSheafPairTransitionCoefficient R V a
        (vertexBooleanPivot V (vertexFaceBaseChoice V q)) (vertexBooleanPivot V (vertexFaceBaseChoice V r))
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r) (vertexFaceRefinement_le_pair R V h)) =
      (multiTwistTransition R h a : FaceRing R r) := by
  let σ := vertexBooleanPivot V (vertexFaceBaseChoice V q)
  let τ := vertexBooleanPivot V (vertexFaceBaseChoice V r)
  let P := vertexChartPairOpen R V σ τ
  let W := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r
  let g := vertexFaceRefinementPairLift R V h
  have hc := SheafTools.affineOpenSectionsIsoAt_multiplication (vertexScheme R V) P
    (vertexFaceι R V r) W (vertexFaceι_opensRange R V r)
    (vertexFaceRefinement_le_pair R V h) g (vertexFaceRefinementPairLift_fac R V h)
    (vertexTwistSheafPairUnit R V a σ τ : Γ(P.toScheme, ⊤))
  refine hc.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of (FaceRing R r))).hom
    (g.appTop (↑(∏ v, vertexTwistPairFactorUnit R V a σ τ v))) =
      ↑(∏ v, faceTransitionUnit R h v ^ a v)
  rw [Units.coe_prod, map_prod, map_prod, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro v _
  exact vertexFaceRefinement_factor_unit R V h a v

end BPFixedPoints.ProjectiveLine
