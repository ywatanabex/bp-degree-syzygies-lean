import BPFixedPoints.Incidence.VertexProjectiveTwistAddTransitions
import BPFixedPoints.Incidence.SchemeModuleTensorPairTransition

/-! # Original tensor chart frames and the same original additive transitions

Both tensor factors and their sum use the already specified chart and pair
frames. Their original transitions are exactly the same geometric unit.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SheafTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The already specified original twist chart frame, in the native over-site. -/
noncomputable def vertexTwistOverChartIso (a : V → ℤ) (σ : V → Fin 2) :
    (vertexTwistSheaf R V a).over (vertexChartOpen R V σ) ≅
      SheafOfModules.unit ((vertexScheme R V).ringCatSheaf.over (vertexChartOpen R V σ)) :=
  moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a) (vertexChartOpen R V σ)
    (vertexTwistSheafChartIso R V a σ)

/-- The already specified original twist pair frame, in the same native over-site. -/
noncomputable def vertexTwistOverPairIso (a : V → ℤ) (σ τ : V → Fin 2) (right : Bool) :
    (vertexTwistSheaf R V a).over (vertexChartPairOpen R V σ τ) ≅
      SheafOfModules.unit ((vertexScheme R V).ringCatSheaf.over (vertexChartPairOpen R V σ τ)) :=
  moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a) (vertexChartPairOpen R V σ τ)
    (vertexTwistSheafPairIso R V a σ τ right)

/-- The original left chart frame restricts to the specified left pair frame in the original over-site. -/
theorem vertexTwistOverChartIso_left (a : V → ℤ) (σ τ : V → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R V) (homOfLE (show vertexChartPairOpen R V σ τ ≤
      vertexChartOpen R V σ from inf_le_left)) (vertexTwistSheaf R V a) (vertexTwistOverChartIso R V a σ) =
        vertexTwistOverPairIso R V a σ τ false := by
  have h := congrArg (moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
    (vertexChartPairOpen R V σ τ)) (vertexTwistSheafChartFrameRestriction_left_pair R V a σ τ)
  simpa only [vertexTwistSheafChartFrameRestriction,moduleLocalFrameRestriction,
    moduleOverUnitIso_moduleLocalFrameOfOver,vertexTwistOverChartIso,vertexTwistOverPairIso] using h

/-- The original right chart frame restricts to the specified right pair frame in the original over-site. -/
theorem vertexTwistOverChartIso_right (a : V → ℤ) (σ τ : V → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R V) (homOfLE (show vertexChartPairOpen R V σ τ ≤
      vertexChartOpen R V τ from inf_le_right)) (vertexTwistSheaf R V a) (vertexTwistOverChartIso R V a τ) =
        vertexTwistOverPairIso R V a σ τ true := by
  have h := congrArg (moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
    (vertexChartPairOpen R V σ τ)) (vertexTwistSheafChartFrameRestriction_right_pair R V a σ τ)
  simpa only [vertexTwistSheafChartFrameRestriction,moduleLocalFrameRestriction,
    moduleOverUnitIso_moduleLocalFrameOfOver,vertexTwistOverChartIso,vertexTwistOverPairIso] using h

/-- The original over-site pair frames have exactly the original geometric transition. -/
theorem vertexTwistOverPairIso_transition (a : V → ℤ) (σ τ : V → Fin 2) :
    (vertexTwistOverPairIso R V a σ τ false).hom =
      (vertexTwistOverPairIso R V a σ τ true).hom ≫
        moduleOverMultiplication (vertexScheme R V) (vertexChartPairOpen R V σ τ)
          (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme,⊤)) :=
  moduleOverUnitIso_transition _ _ _ _ _ _ (vertexTwistSheafPairIso_transition R V a σ τ)

/-- The original actual tensor chart frame retains the original two factor frames. -/
noncomputable def vertexTwistTensorChartIso (a b : V → ℤ) (σ : V → Fin 2) :
    (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b)).over
      (vertexChartOpen R V σ) ≅
        SheafOfModules.unit ((vertexScheme R V).ringCatSheaf.over (vertexChartOpen R V σ)) :=
  moduleTensorOverUnitIso (vertexScheme R V) _ _ (vertexChartOpen R V σ)
    (vertexTwistOverChartIso R V a σ) (vertexTwistOverChartIso R V b σ)

/-- The original actual tensor pair frame retains the same original two factor frames. -/
noncomputable def vertexTwistTensorPairIso (a b : V → ℤ) (σ τ : V → Fin 2) (right : Bool) :
    (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b)).over
      (vertexChartPairOpen R V σ τ) ≅
        SheafOfModules.unit ((vertexScheme R V).ringCatSheaf.over (vertexChartPairOpen R V σ τ)) :=
  moduleTensorOverUnitIso (vertexScheme R V) _ _ (vertexChartPairOpen R V σ τ)
    (vertexTwistOverPairIso R V a σ τ right) (vertexTwistOverPairIso R V b σ τ right)

/-- Restricting the original tensor chart frame preserves the original left tensor pair frame. -/
theorem vertexTwistTensorChartIso_left (a b : V → ℤ) (σ τ : V → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R V) (homOfLE (show vertexChartPairOpen R V σ τ ≤
      vertexChartOpen R V σ from inf_le_left))
        (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b))
          (vertexTwistTensorChartIso R V a b σ) = vertexTwistTensorPairIso R V a b σ τ false := by
  rw [vertexTwistTensorChartIso,moduleTensorOverUnitIso_restriction,
    vertexTwistOverChartIso_left,vertexTwistOverChartIso_left]
  rfl

/-- Restricting the original tensor chart frame preserves the original right tensor pair frame. -/
theorem vertexTwistTensorChartIso_right (a b : V → ℤ) (σ τ : V → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R V) (homOfLE (show vertexChartPairOpen R V σ τ ≤
      vertexChartOpen R V τ from inf_le_right))
        (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b))
          (vertexTwistTensorChartIso R V a b τ) = vertexTwistTensorPairIso R V a b σ τ true := by
  rw [vertexTwistTensorChartIso,moduleTensorOverUnitIso_restriction,
    vertexTwistOverChartIso_right,vertexTwistOverChartIso_right]
  rfl

/-- The original actual tensor pair transition is exactly the original transition of the sum twist. -/
theorem vertexTwistTensorPairIso_transition (a b : V → ℤ) (σ τ : V → Fin 2) :
    (vertexTwistTensorPairIso R V a b σ τ false).hom =
      (vertexTwistTensorPairIso R V a b σ τ true).hom ≫
        moduleOverMultiplication (vertexScheme R V) (vertexChartPairOpen R V σ τ)
          (vertexTwistSheafPairUnit R V (a+b) σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme,⊤)) := by
  have h := moduleTensorOverFrame_transition (vertexScheme R V) (vertexTwistSheaf R V a)
    (vertexTwistSheaf R V b) (vertexChartPairOpen R V σ τ)
    (vertexTwistOverPairIso R V a σ τ false) (vertexTwistOverPairIso R V a σ τ true)
    (vertexTwistOverPairIso R V b σ τ false) (vertexTwistOverPairIso R V b σ τ true)
    (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme,⊤))
    (vertexTwistSheafPairUnit R V b σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme,⊤))
    (vertexTwistOverPairIso_transition R V a σ τ) (vertexTwistOverPairIso_transition R V b σ τ)
  rw [← Units.val_mul,← vertexTwistSheafPairUnit_add] at h
  exact h

end BPFixedPoints.ProjectiveLine
