import BPFixedPoints.Incidence.SchemeModulePullbackRestrictionFrames
import BPFixedPoints.Incidence.VertexProjectiveTwistPairRefinement
import BPFixedPoints.Incidence.VertexProjectiveTwistChartRestriction

/-! # The specified original pair frames are restrictions of the original vertex chart frames

The original chart frames, pair frames, fixed vertex enumeration and tensor
brackets are retained. The comparison includes the empty vertex set.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original left chart factor restricts to the originally specified left pair factor. -/
theorem vertexTwistFactorChartIso_left_restriction (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    SheafTools.moduleLocalFrameRestriction (vertexScheme R V)
      (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left))
      ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj (twistSheaf R (a v)))
      (vertexTwistFactorChartIso R V a σ v) = vertexTwistPairFactorIso R V a σ τ v false := by
  rw [vertexTwistPairFactorIso_left_refined]
  simpa only [vertexTwistFactorChartIso] using
    SheafTools.moduleLocalFrameRestriction_pullbackLocalFrame (vertexScheme R V)
      (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left))
      (vertexProjectionOver R V v).left (standardOpen R (σ v)) (twistSheaf R (a v))
      (twistSheafStandardIso R (a v) (σ v))
      (vertexChartOpenProjectionLift R V σ v) (vertexChartOpenProjectionLift_fac R V σ v)

/-- The original right chart factor restricts to the originally specified right pair factor. -/
theorem vertexTwistFactorChartIso_right_restriction (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    SheafTools.moduleLocalFrameRestriction (vertexScheme R V)
      (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right))
      ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj (twistSheaf R (a v)))
      (vertexTwistFactorChartIso R V a τ v) = vertexTwistPairFactorIso R V a σ τ v true := by
  rw [vertexTwistPairFactorIso_right_refined]
  simpa only [vertexTwistFactorChartIso] using
    SheafTools.moduleLocalFrameRestriction_pullbackLocalFrame (vertexScheme R V)
      (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right))
      (vertexProjectionOver R V v).left (standardOpen R (τ v)) (twistSheaf R (a v))
      (twistSheafStandardIso R (a v) (τ v))
      (vertexChartOpenProjectionLift R V τ v) (vertexChartOpenProjectionLift_fac R V τ v)

/-- The original left multi-twist chart frame restricts to the originally specified left pair frame. -/
theorem vertexTwistSheafChartFrameRestriction_left_pair (a : V → ℤ) (σ τ : V → Fin 2) :
    vertexTwistSheafChartFrameRestriction R V a σ (vertexChartPairOpen R V σ τ) inf_le_left =
      vertexTwistSheafPairIso R V a σ τ false := by
  rw [vertexTwistSheafChartFrameRestriction_factors]
  dsimp only [vertexTwistSheafPairIso]
  congr 1
  funext i
  exact vertexTwistFactorChartIso_left_restriction R V a σ τ ((Fintype.equivFin V).symm i)

/-- The original right multi-twist chart frame restricts to the originally specified right pair frame. -/
theorem vertexTwistSheafChartFrameRestriction_right_pair (a : V → ℤ) (σ τ : V → Fin 2) :
    vertexTwistSheafChartFrameRestriction R V a τ (vertexChartPairOpen R V σ τ) inf_le_right =
      vertexTwistSheafPairIso R V a σ τ true := by
  rw [vertexTwistSheafChartFrameRestriction_factors]
  dsimp only [vertexTwistSheafPairIso]
  congr 1
  funext i
  exact vertexTwistFactorChartIso_right_restriction R V a σ τ ((Fintype.equivFin V).symm i)

/-- The restrictions of the original chart frames have the original vertex-labelled Laurent product transition. -/
theorem vertexTwistSheafChartFrameRestriction_transition (a : V → ℤ) (σ τ : V → Fin 2) :
    (vertexTwistSheafChartFrameRestriction R V a σ
      (vertexChartPairOpen R V σ τ) inf_le_left).hom =
    (vertexTwistSheafChartFrameRestriction R V a τ
      (vertexChartPairOpen R V σ τ) inf_le_right).hom ≫
        SheafTools.unitGlobalMultiplication (vertexChartPairOpen R V σ τ).toScheme
          (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)) := by
  rw [vertexTwistSheafChartFrameRestriction_left_pair,
    vertexTwistSheafChartFrameRestriction_right_pair]
  exact vertexTwistSheafPairIso_transition R V a σ τ

end BPFixedPoints.ProjectiveLine
