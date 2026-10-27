import BPFixedPoints.Incidence.SchemeModuleLocalFramePullbackCoherence
import BPFixedPoints.Incidence.ProjectiveLineTwistPairRestriction
import BPFixedPoints.Incidence.VertexProjectiveTwistPairFrames

/-! # Original pair frames along the specified vertex chart factorizations

The original pair lifts followed by the standard open inclusions agree with the
original chart lifts. These comparisons do not assume projections are open immersions.
The ambient restriction comparison is proved in VertexProjectiveTwistPairChartComparison.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original pair lift and original left chart lift give the same standard-open morphism. -/
theorem vertexChartPairProjectionLift_left (σ τ : V → Fin 2) (v : V) :
    vertexChartPairProjectionLift R V σ τ v ≫
      (projectiveLine R).homOfLE (standardPairOpen_le_left R (σ v) (τ v)) =
    (vertexScheme R V).homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left) ≫
      vertexChartOpenProjectionLift R V σ v := by
  apply (cancel_mono (standardOpen R (σ v)).ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, vertexChartPairProjectionLift_fac,
    vertexChartOpenProjectionLift_fac]
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- The original pair lift and original right chart lift give the same standard-open morphism. -/
theorem vertexChartPairProjectionLift_right (σ τ : V → Fin 2) (v : V) :
    vertexChartPairProjectionLift R V σ τ v ≫
      (projectiveLine R).homOfLE (standardPairOpen_le_right R (σ v) (τ v)) =
    (vertexScheme R V).homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right) ≫
      vertexChartOpenProjectionLift R V τ v := by
  apply (cancel_mono (standardOpen R (τ v)).ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, vertexChartPairProjectionLift_fac,
    vertexChartOpenProjectionLift_fac]
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- The original left pair factor frame equals the pullback of the original left standard frame along the chart path. -/
theorem vertexTwistPairFactorIso_left_refined (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    vertexTwistPairFactorIso R V a σ τ v false =
      (Scheme.Modules.restrictFunctorIsoPullback (vertexChartPairOpen R V σ τ).ι).app _ ≪≫
        (Scheme.Modules.pullbackComp (vertexChartPairOpen R V σ τ).ι
          (vertexProjectionOver R V v).left).app _ ≪≫
        SheafTools.modulePullbackLocalUnitIso _ (standardOpen R (σ v)) (twistSheaf R (a v))
          (twistSheafStandardIso R (a v) (σ v))
          ((vertexScheme R V).homOfLE inf_le_left ≫ vertexChartOpenProjectionLift R V σ v)
          (by rw [Category.assoc, vertexChartOpenProjectionLift_fac,
            ← Category.assoc, Scheme.homOfLE_ι]) := by
  have h := SheafTools.modulePullbackLocalUnitIso_refine_fac
    (homOfLE (standardPairOpen_le_left R (σ v) (τ v))) (twistSheaf R (a v))
    (twistSheafStandardIso R (a v) (σ v))
    ((vertexChartPairOpen R V σ τ).ι ≫ (vertexProjectionOver R V v).left)
    ((vertexScheme R V).homOfLE inf_le_left ≫ vertexChartOpenProjectionLift R V σ v)
    (by rw [Category.assoc, vertexChartOpenProjectionLift_fac, ← Category.assoc, Scheme.homOfLE_ι])
    (vertexChartPairProjectionLift R V σ τ v) (vertexChartPairProjectionLift_fac R V σ τ v)
    (vertexChartPairProjectionLift_left R V σ τ v)
  rw [twistSheafPairIso_eq_left_restriction] at h
  dsimp only [vertexTwistPairFactorIso]
  rw [h]

/-- The original right pair factor frame equals the pullback of the original right standard frame along the chart path. -/
theorem vertexTwistPairFactorIso_right_refined (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    vertexTwistPairFactorIso R V a σ τ v true =
      (Scheme.Modules.restrictFunctorIsoPullback (vertexChartPairOpen R V σ τ).ι).app _ ≪≫
        (Scheme.Modules.pullbackComp (vertexChartPairOpen R V σ τ).ι
          (vertexProjectionOver R V v).left).app _ ≪≫
        SheafTools.modulePullbackLocalUnitIso _ (standardOpen R (τ v)) (twistSheaf R (a v))
          (twistSheafStandardIso R (a v) (τ v))
          ((vertexScheme R V).homOfLE inf_le_right ≫ vertexChartOpenProjectionLift R V τ v)
          (by rw [Category.assoc, vertexChartOpenProjectionLift_fac,
            ← Category.assoc, Scheme.homOfLE_ι]) := by
  have h := SheafTools.modulePullbackLocalUnitIso_refine_fac
    (homOfLE (standardPairOpen_le_right R (σ v) (τ v))) (twistSheaf R (a v))
    (twistSheafStandardIso R (a v) (τ v))
    ((vertexChartPairOpen R V σ τ).ι ≫ (vertexProjectionOver R V v).left)
    ((vertexScheme R V).homOfLE inf_le_right ≫ vertexChartOpenProjectionLift R V τ v)
    (by rw [Category.assoc, vertexChartOpenProjectionLift_fac, ← Category.assoc, Scheme.homOfLE_ι])
    (vertexChartPairProjectionLift R V σ τ v) (vertexChartPairProjectionLift_fac R V σ τ v)
    (vertexChartPairProjectionLift_right R V σ τ v)
  rw [twistSheafPairIso_eq_right_restriction] at h
  dsimp only [vertexTwistPairFactorIso]
  rw [h]

end BPFixedPoints.ProjectiveLine
