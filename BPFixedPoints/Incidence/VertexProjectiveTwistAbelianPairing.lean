import BPFixedPoints.Incidence.AbelianSheafPairing
import BPFixedPoints.Incidence.VertexProjectiveTwistSectionProduct
import BPFixedPoints.Incidence.VertexProjectiveTwistCechAcyclic

/-! # The original geometric twist product is an actual abelian-sheaf tensor map

Extend the original geometric section pairing through the native integer
sheaf tensor. Evaluation on the native pure sections retains the original
geometric product, restrictions, and every chart and mixed-face coefficient.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite SheafTools
open SheafTools.AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- Forget only scalar linearity in the already specified original geometric section product. -/
def vertexTwistAbelianSectionPairing (a b : V → ℤ) :
    SectionPairing (vertexTwistAbelianSheaf R V a) (vertexTwistAbelianSheaf R V b)
      (vertexTwistAbelianSheaf R V (a+b)) where
  pairing W := by
    change Γ(vertexTwistSheaf R V a,W) →+
      Γ(vertexTwistSheaf R V b,W) →+ Γ(vertexTwistSheaf R V (a+b),W)
    exact LinearMap.toAddMonoidHom'.comp (vertexTwistSectionProduct R V a b W).toAddMonoidHom
  restrict i x y := vertexTwistSectionProduct_restrict R V a b i x y

/-- The original geometric twist product as a morphism from the actual native integer sheaf tensor. -/
def vertexTwistAbelianProduct (a b : V → ℤ) :
    vertexTwistAbelianSheaf R V a ⊗ vertexTwistAbelianSheaf R V b ⟶
      vertexTwistAbelianSheaf R V (a+b) :=
  (vertexTwistAbelianSectionPairing R V a b).sheafMap

/-- Native pure-section evaluation gives the original geometric twist section product itself. -/
theorem vertexTwistAbelianProduct_pure (a b : V → ℤ) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    (vertexTwistAbelianProduct R V a b).hom.app (op W)
      (sheafPureSection (vertexTwistAbelianSheaf R V a) (vertexTwistAbelianSheaf R V b) W x y) =
        vertexTwistSectionProduct R V a b W x y :=
  (vertexTwistAbelianSectionPairing R V a b).sheafMap_pure W x y

/-- The actual integer-tensor map retains every original chart coefficient product. -/
theorem vertexTwistAbelianProduct_chart (a b : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)
    (x : Γ(vertexTwistSheaf R V a,W)) (y : Γ(vertexTwistSheaf R V b,W)) :
    vertexTwistSheafChartCoefficient R V (a+b) σ W hW
      ((vertexTwistAbelianProduct R V a b).hom.app (op W)
        (sheafPureSection (vertexTwistAbelianSheaf R V a) (vertexTwistAbelianSheaf R V b) W x y)) =
      vertexTwistSheafChartCoefficient R V a σ W hW x * vertexTwistSheafChartCoefficient R V b σ W hW y := by
  rw [vertexTwistAbelianProduct_pure,vertexTwistSectionProduct_chart]

variable [DecidableEq V]

/-- Every original mixed-face product coefficient is retained in the actual native integer tensor category. -/
theorem vertexTwistAbelianProduct_face (a b : V → ℤ) (q : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a,SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q))
    (y : Γ(vertexTwistSheaf R V b,SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V (a+b) q
      ((vertexTwistAbelianProduct R V a b).hom.app _
        (sheafPureSection (vertexTwistAbelianSheaf R V a) (vertexTwistAbelianSheaf R V b) _ x y)) =
      vertexTwistSheafFaceSectionsEquiv R V a q x * vertexTwistSheafFaceSectionsEquiv R V b q y := by
  rw [vertexTwistAbelianProduct_pure,vertexTwistSectionProduct_face]

end
end BPFixedPoints.ProjectiveLine
