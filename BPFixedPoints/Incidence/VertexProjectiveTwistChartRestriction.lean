import BPFixedPoints.Incidence.SchemeModuleLocalFrameRestriction
import BPFixedPoints.Incidence.VertexProjectiveTwistLocalFrames

/-! # Original vertex-twist chart coefficients and actual restrictions

The coefficient functions use the previously specified actual chart frames.
They retain the original module and structure-ring restriction maps. Equality
with the original pair frames is proved in VertexProjectiveTwistPairChartComparison.
Comparison with the coefficient face atlas remains.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original multi-twist chart frame gives linear coefficients on each actual subopen. -/
noncomputable def vertexTwistSheafChartCoefficient (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    Γ(vertexTwistSheaf R V a, W) →ₗ[Γ(vertexScheme R V, W)] Γ(vertexScheme R V, W) :=
  ((SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
    (vertexChartOpen R V σ) (vertexTwistSheafChartIso R V a σ)).hom.val.app
      (op (Over.mk (homOfLE hW)))).hom

/-- The previously specified chart coefficients preserve the original sheaf and structure-ring restrictions. -/
theorem vertexTwistSheafChartCoefficient_restrict (a : V → ℤ) (σ : V → Fin 2)
    {W U : (vertexScheme R V).Opens} (hWU : W ≤ U) (hU : U ≤ vertexChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a, U)) :
    vertexTwistSheafChartCoefficient R V a σ W (hWU.trans hU)
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE hWU).op x) =
      (vertexScheme R V).presheaf.map (homOfLE hWU).op
        (vertexTwistSheafChartCoefficient R V a σ U hU x) := by
  let S : Over (vertexChartOpen R V σ) := Over.mk (homOfLE (hWU.trans hU))
  let T : Over (vertexChartOpen R V σ) := Over.mk (homOfLE hU)
  let i : S ⟶ T := Over.homMk (homOfLE hWU) (by cat_disch)
  exact SheafTools.moduleLocalFrame_naturality (vertexScheme R V) (vertexChartOpen R V σ)
    (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a σ) (S := S) (T := T) i x

/-- The original multi-twist chart frame restricted to the specified actual subopen. -/
noncomputable def vertexTwistSheafChartFrameRestriction (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    (vertexTwistSheaf R V a).restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  SheafTools.moduleLocalFrameRestriction (vertexScheme R V) (homOfLE hW)
    (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a σ)

/-- Restricting the original multi-twist chart frame is the finite tensor of the originally restricted factor frames. -/
theorem vertexTwistSheafChartFrameRestriction_factors (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    vertexTwistSheafChartFrameRestriction R V a σ W hW =
      SheafTools.moduleTensorFamilyLocalUnitIso (vertexScheme R V) W (Fintype.card V)
        (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)))
        (fun i => SheafTools.moduleLocalFrameRestriction (vertexScheme R V) (homOfLE hW)
          (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)) i)
          (vertexTwistFactorChartIso R V a σ ((Fintype.equivFin V).symm i))) :=
  SheafTools.moduleTensorFamilyLocalUnitIso_restriction _ _ _ _ _

end BPFixedPoints.ProjectiveLine
