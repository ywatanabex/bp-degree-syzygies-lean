import BPFixedPoints.Incidence.SchemeModuleFrameGeometricComparison
import BPFixedPoints.Incidence.VertexProjectiveTwistChartRestriction

/-! # Native geometric restriction of the original vertex-twist chart frames

These equalities preserve the specified original chart frames and finite tensor
factors. Equality with the specified original pair frames is proved in
VertexProjectiveTwistPairChartComparison.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original chart restriction equals the native geometric restriction of that same frame. -/
theorem vertexTwistSheafChartFrameRestriction_eq_geometric (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    vertexTwistSheafChartFrameRestriction R V a σ W hW =
      SheafTools.moduleGeometricFrameRestriction (vertexScheme R V) (homOfLE hW)
        (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a σ) :=
  SheafTools.moduleLocalFrameRestriction_eq_geometric _ _ _ _

/-- The geometric restriction of the original multi-twist frame retains its original tensor factors. -/
theorem vertexTwistSheafChartFrameRestriction_geometric_factors (a : V → ℤ)
    (σ : V → Fin 2) (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    vertexTwistSheafChartFrameRestriction R V a σ W hW =
      SheafTools.moduleTensorFamilyLocalUnitIso (vertexScheme R V) W (Fintype.card V)
        (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)))
        (fun i => SheafTools.moduleGeometricFrameRestriction (vertexScheme R V) (homOfLE hW)
          (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)) i)
          (vertexTwistFactorChartIso R V a σ ((Fintype.equivFin V).symm i))) := by
  simpa only [SheafTools.moduleLocalFrameRestriction_eq_geometric] using
    vertexTwistSheafChartFrameRestriction_factors R V a σ W hW

end BPFixedPoints.ProjectiveLine
