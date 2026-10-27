import BPFixedPoints.Incidence.VertexProjectiveTwistTensorFrames

/-! # The original tensor of integral twists is the original sum twist

The global isomorphism glues the specified original chart frame maps.
Actual transition compatibility supplies the gluing equations. Original
pure section coefficients multiply on every original subopen of a chart.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1700000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The specified original chart comparison, retaining the two tensor factors and the sum twist frame. -/
noncomputable def vertexTwistTensorAddLocalIso (a b : V → ℤ) (σ : V → Fin 2) :
    (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b)).over
      (vertexChartOpen R V σ) ≅ (vertexTwistSheaf R V (a+b)).over (vertexChartOpen R V σ) :=
  vertexTwistTensorChartIso R V a b σ ≪≫ (vertexTwistOverChartIso R V (a+b) σ).symm

/-- The original tensor-to-sum chart maps agree on their original actual intersections. -/
theorem vertexTwistTensorAddLocal_hom_compatible (a b : V → ℤ) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R V))
      (moduleHomSheaf (vertexScheme R V)
        (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b))
        (vertexTwistSheaf R V (a+b))).obj (vertexChartOpen R V)
      (fun σ => moduleOverHomSection (vertexScheme R V) _ _ (vertexChartOpen R V σ)
        (vertexTwistTensorAddLocalIso R V a b σ).hom) := by
  intro σ τ
  dsimp only [vertexTwistTensorAddLocalIso,Iso.trans_hom,Iso.symm_hom]
  rw [moduleFrameMap_section_restrict,moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R V σ) (vertexChartOpen R V τ) =
      homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left) := Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R V σ) (vertexChartOpen R V τ) =
      homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right) := Subsingleton.elim _ _
  rw [hL,hR,vertexTwistTensorChartIso_left,vertexTwistTensorChartIso_right,
    vertexTwistOverChartIso_left,vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R V)
    (vertexTwistTensorPairIso R V a b σ τ false) (vertexTwistTensorPairIso R V a b σ τ true)
    (vertexTwistOverPairIso R V (a+b) σ τ false) (vertexTwistOverPairIso R V (a+b) σ τ true) _
    (vertexTwistTensorPairIso_transition R V a b σ τ) (vertexTwistOverPairIso_transition R V (a+b) σ τ)

/-- The original inverse sum-to-tensor chart maps also agree on the same original intersections. -/
theorem vertexTwistTensorAddLocal_inv_compatible (a b : V → ℤ) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R V))
      (moduleHomSheaf (vertexScheme R V) (vertexTwistSheaf R V (a+b))
        (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b))).obj
      (vertexChartOpen R V)
      (fun σ => moduleOverHomSection (vertexScheme R V) _ _ (vertexChartOpen R V σ)
        (vertexTwistTensorAddLocalIso R V a b σ).inv) := by
  intro σ τ
  dsimp only [vertexTwistTensorAddLocalIso,Iso.trans_inv,Iso.symm_inv]
  rw [moduleFrameMap_section_restrict,moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R V σ) (vertexChartOpen R V τ) =
      homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left) := Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R V σ) (vertexChartOpen R V τ) =
      homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right) := Subsingleton.elim _ _
  rw [hL,hR,vertexTwistTensorChartIso_left,vertexTwistTensorChartIso_right,
    vertexTwistOverChartIso_left,vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R V)
    (vertexTwistOverPairIso R V (a+b) σ τ false) (vertexTwistOverPairIso R V (a+b) σ τ true)
    (vertexTwistTensorPairIso R V a b σ τ false) (vertexTwistTensorPairIso R V a b σ τ true) _
    (vertexTwistOverPairIso_transition R V (a+b) σ τ) (vertexTwistTensorPairIso_transition R V a b σ τ)

/-- The actual original tensor sheaf of two integral multi-twists is the original sum twist, by the specified frame comparisons. -/
noncomputable def vertexTwistTensorAddIso (a b : V → ℤ) :
    moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) ≅
      vertexTwistSheaf R V (a+b) :=
  moduleFrameGlueIso (vertexScheme R V) _ _ (vertexChartOpen R V) (vertexChartOpen_iSup_top R V)
    (vertexTwistTensorAddLocalIso R V a b) (vertexTwistTensorAddLocal_hom_compatible R V a b)
      (vertexTwistTensorAddLocal_inv_compatible R V a b)

/-- The actual global tensor-addition isomorphism retains the specified original chart isomorphism itself. -/
theorem vertexTwistTensorAddIso_over (a b : V → ℤ) (σ : V → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R V).ringCatSheaf (vertexChartOpen R V σ)).mapIso
      (vertexTwistTensorAddIso R V a b) = vertexTwistTensorAddLocalIso R V a b σ :=
  moduleFrameGlueIso_over (vertexScheme R V) _ _ (vertexChartOpen R V) (vertexChartOpen_iSup_top R V)
    (vertexTwistTensorAddLocalIso R V a b) (vertexTwistTensorAddLocal_hom_compatible R V a b)
      (vertexTwistTensorAddLocal_inv_compatible R V a b) σ

/-- The original target frame after multiplication is exactly the originally specified tensor frame. -/
theorem vertexTwistTensorAddIso_chart (a b : V → ℤ) (σ : V → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R V).ringCatSheaf (vertexChartOpen R V σ)).map
      (vertexTwistTensorAddIso R V a b).hom ≫ (vertexTwistOverChartIso R V (a+b) σ).hom =
        (vertexTwistTensorChartIso R V a b σ).hom := by
  rw [← Functor.mapIso_hom,vertexTwistTensorAddIso_over]
  simp only [vertexTwistTensorAddLocalIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    Iso.inv_hom_id,Category.comp_id]

/-- On every original subopen of every original chart, actual pure sections multiply their original coefficients. -/
theorem vertexTwistTensorAddIso_pure (a b : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    vertexTwistSheafChartCoefficient R V (a+b) σ W hW
      ((vertexTwistTensorAddIso R V a b).hom.app W
        (moduleTensorPureSection (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) W x y)) =
      vertexTwistSheafChartCoefficient R V a σ W hW x *
        vertexTwistSheafChartCoefficient R V b σ W hW y := by
  let S : Over (vertexChartOpen R V σ) := Over.mk (homOfLE hW)
  have h := congrArg (fun f => (f.val.app (op S)).hom
      (moduleTensorPureSection (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) W x y))
    (vertexTwistTensorAddIso_chart R V a b σ)
  exact h.trans (moduleTensorOverUnitIso_pure (vertexScheme R V) _ _ (vertexChartOpen R V σ)
    (vertexTwistOverChartIso R V a σ) (vertexTwistOverChartIso R V b σ) S x y)

end BPFixedPoints.ProjectiveLine
