import BPFixedPoints.Incidence.VertexProjectiveTwistTensorAdd
import BPFixedPoints.Incidence.VertexProjectiveFaceSections
import BPFixedPoints.Incidence.SchemeModuleTensorBaseLinearity

/-! # Actual products of original twist sections retain their original coefficients

The pairing is induced by the actual tensor sheaf and its specified
tensor-addition isomorphism. It is defined before any cohomology or state
comparison and preserves the original actual restrictions and geometric scalars.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct Opposite SheafTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The actual original section pairing, linear over the original structure ring in both variables. -/
noncomputable def vertexTwistSectionProduct (a b : V → ℤ) (W : (vertexScheme R V).Opens) :
    Γ(vertexTwistSheaf R V a,W) →ₗ[Γ(vertexScheme R V,W)]
      Γ(vertexTwistSheaf R V b,W) →ₗ[Γ(vertexScheme R V,W)] Γ(vertexTwistSheaf R V (a+b),W) :=
  (moduleTensorSectionBilinear (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) W).compr₂
    ((vertexTwistTensorAddIso R V a b).hom.val.app (op W)).hom

/-- The actual section product is the original pure tensor followed by the specified original geometric pairing. -/
theorem vertexTwistSectionProduct_apply (a b : V → ℤ) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    vertexTwistSectionProduct R V a b W x y =
      (vertexTwistTensorAddIso R V a b).hom.app W
        (moduleTensorPureSection (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) W x y) := rfl

/-- The actual section pairing retains precisely the original native sheaf restrictions. -/
theorem vertexTwistSectionProduct_restrict (a b : V → ℤ)
    {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Γ(vertexTwistSheaf R V a,U)) (y : Γ(vertexTwistSheaf R V b,U)) :
    (vertexTwistSheaf R V (a+b)).presheaf.map i.op (vertexTwistSectionProduct R V a b U x y) =
      vertexTwistSectionProduct R V a b W
        ((vertexTwistSheaf R V a).presheaf.map i.op x) ((vertexTwistSheaf R V b).presheaf.map i.op y) := by
  have h := PresheafOfModulesOfCommRing.naturality_apply (vertexTwistTensorAddIso R V a b).hom.val i.op
    (moduleTensorPureSection (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) U x y)
  exact h.symm.trans (congrArg ((vertexTwistTensorAddIso R V a b).hom.app W)
    (moduleTensorPureSection_restrict (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) i x y))

/-- Actual chart coefficients of the original section pairing are the original product of coefficients. -/
theorem vertexTwistSectionProduct_chart (a b : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    vertexTwistSheafChartCoefficient R V (a+b) σ W hW (vertexTwistSectionProduct R V a b W x y) =
      vertexTwistSheafChartCoefficient R V a σ W hW x * vertexTwistSheafChartCoefficient R V b σ W hW y :=
  vertexTwistTensorAddIso_pure R V a b σ W hW x y

/-- The original geometric base action makes the same actual section product bilinear over the original coefficient ring. -/
noncomputable def vertexTwistSectionBaseProduct (a b : V → ℤ) (W : (vertexScheme R V).Opens) :
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a) W
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V b) W
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V (a+b)) W
    Γ(vertexTwistSheaf R V a,W) →ₗ[R] Γ(vertexTwistSheaf R V b,W) →ₗ[R] Γ(vertexTwistSheaf R V (a+b),W) := by
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a) W
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V b) W
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V (a+b)) W
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V)
    (moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b)) W
  let g : Γ(moduleTensor (vertexScheme R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b),W) →ₗ[R]
      Γ(vertexTwistSheaf R V (a+b),W) :=
    { toFun := (vertexTwistTensorAddIso R V a b).hom.app W
      map_add' := map_add _
      map_smul' := fun r x => ((vertexTwistTensorAddIso R V a b).hom.val.app (op W)).hom.map_smul
        (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) W r) x }
  exact (moduleTensorBaseSectionBilinear (vertexToBase R V) (vertexTwistSheaf R V a) (vertexTwistSheaf R V b) W).compr₂ g

/-- Base bilinearity uses the same original geometric section pairing. -/
theorem vertexTwistSectionBaseProduct_apply (a b : V → ℤ) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    vertexTwistSectionBaseProduct R V a b W x y = vertexTwistSectionProduct R V a b W x y := rfl

variable [DecidableEq V]

/-- Every original mixed polynomial/Laurent face coefficient multiplies by its original ring multiplication. -/
theorem vertexTwistSectionProduct_face (a b : V → ℤ) (q : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a,SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q))
    (y : Γ(vertexTwistSheaf R V b,SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V (a+b) q
      (vertexTwistSectionProduct R V a b (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) x y) =
      vertexTwistSheafFaceSectionsEquiv R V a q x * vertexTwistSheafFaceSectionsEquiv R V b q y := by
  simp only [vertexTwistSheafFaceSectionsEquiv_apply,vertexTwistSectionProduct_chart,map_mul]

end BPFixedPoints.ProjectiveLine
