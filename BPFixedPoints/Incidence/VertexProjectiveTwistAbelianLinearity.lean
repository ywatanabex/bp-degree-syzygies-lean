import BPFixedPoints.Incidence.VertexProjectiveTwistAbelianPairing
import BPFixedPoints.Incidence.AbelianSheafTensorEvaluation

/-! # The actual integer-sheaf tensor pairing retains the original geometric base action

These are equations of actual sheaf morphisms, using the scalar
endomorphisms defined from the original map to the coefficient scheme.
No scalar action is transported from a cohomology or state-space target.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite SheafTools
open SheafTools.AbelianTensor SchemeTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The actual tensor pairing is linear in its original left geometric base action. -/
theorem vertexTwistAbelianProduct_left_scalar (a b : V → ℤ) (r : R) :
    (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r ⊗ₘ
      𝟙 (vertexTwistAbelianSheaf R V b)) ≫ vertexTwistAbelianProduct R V a b =
      vertexTwistAbelianProduct R V a b ≫
        schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r := by
  apply sheafTensor_hom_ext
  intro W x y
  change (vertexTwistAbelianProduct R V a b).hom.app (op W)
    ((schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r ⊗ₘ
      𝟙 (vertexTwistAbelianSheaf R V b)).hom.app (op W) (sheafPureSection _ _ W x y)) = _
  rw [sheafPureSection_map]
  change (vertexTwistAbelianProduct R V a b).hom.app (op W)
    (sheafPureSection _ _ W ((schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r).hom.app (op W) x) y) =
      (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r).hom.app (op W)
        ((vertexTwistAbelianProduct R V a b).hom.app (op W) (sheafPureSection _ _ W x y))
  rw [vertexTwistAbelianProduct_pure,vertexTwistAbelianProduct_pure]
  exact (vertexTwistSectionProduct R V a b W).map_smul₂ _ x y

/-- The actual tensor pairing is linear in its original right geometric base action. -/
theorem vertexTwistAbelianProduct_right_scalar (a b : V → ℤ) (r : R) :
    (𝟙 (vertexTwistAbelianSheaf R V a) ⊗ₘ
      schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) ≫
        vertexTwistAbelianProduct R V a b = vertexTwistAbelianProduct R V a b ≫
          schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r := by
  apply sheafTensor_hom_ext
  intro W x y
  change (vertexTwistAbelianProduct R V a b).hom.app (op W)
    ((𝟙 (vertexTwistAbelianSheaf R V a) ⊗ₘ
      schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r).hom.app (op W)
        (sheafPureSection _ _ W x y)) = _
  rw [sheafPureSection_map]
  change (vertexTwistAbelianProduct R V a b).hom.app (op W)
    (sheafPureSection _ _ W x ((schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r).hom.app (op W) y)) =
      (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r).hom.app (op W)
        ((vertexTwistAbelianProduct R V a b).hom.app (op W) (sheafPureSection _ _ W x y))
  rw [vertexTwistAbelianProduct_pure,vertexTwistAbelianProduct_pure]
  exact (vertexTwistSectionProduct R V a b W x).map_smul _ y

/-- The two original geometric base actions balance on the actual integer-sheaf tensor pairing. -/
theorem vertexTwistAbelianProduct_balanced (a b : V → ℤ) (r : R) :
    (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r ⊗ₘ
      𝟙 (vertexTwistAbelianSheaf R V b)) ≫ vertexTwistAbelianProduct R V a b =
        (𝟙 (vertexTwistAbelianSheaf R V a) ⊗ₘ
          schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) ≫
            vertexTwistAbelianProduct R V a b :=
  (vertexTwistAbelianProduct_left_scalar R V a b r).trans
    (vertexTwistAbelianProduct_right_scalar R V a b r).symm

end
end BPFixedPoints.ProjectiveLine
