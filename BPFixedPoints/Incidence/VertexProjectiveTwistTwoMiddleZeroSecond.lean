import BPFixedPoints.Incidence.CechTwoMiddleZeroSecondProjection
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1All

/-! # Native gluing and connecting classes of every full middle cocycle with zero second twist -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SchemeTools Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]
noncomputable local instance middleZeroSecondHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Glue the original corrected corner coefficients to an actual section on the original outer overlap. -/
noncomputable def vertexTwistTwoMiddleOverlapSection (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    twoMiddleCycles R d →ₗ[R] vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) 2 :=
  (vertexTwistRowSectionKernelEquiv R (fun v => -(d v : ℤ)) 2).symm.toLinearMap.comp
    (twoMiddleCorrectedKernel R d hd)

/-- Both actual corner restrictions of the glued section retain the original primitive correction. -/
theorem vertexTwistTwoMiddleOverlapSection_corners (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) :
    vertexTwistRowCornerCoordinates R (fun v => -(d v : ℤ)) 2
      (schemeBaseSquareSectionPair (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoRowSquare R 2)
          (vertexTwistTwoMiddleOverlapSection R d hd c)) = twoMiddleCorrectedCorners R d c.val := by
  change ((vertexTwistRowSectionKernelEquiv R (fun v => -(d v : ℤ)) 2)
    ((vertexTwistRowSectionKernelEquiv R (fun v => -(d v : ℤ)) 2).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual glued overlap section retains the original horizontal-overlap right constant coefficient. -/
theorem vertexTwistTwoMiddleOverlapSection_base (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) :
    vertexTwistRowSectionBaseEquiv R d hd 2 (vertexTwistTwoMiddleOverlapSection R d hd c) =
      twoRowFaceCoordinates R 2 1 (faceEquiv R c.val ![2,1]) 0 := by
  have hc := congrArg Prod.snd (vertexTwistTwoMiddleOverlapSection_corners R d hd c)
  change vertexTwistTwoRectangleCoordinates R (fun v => -(d v : ℤ)) 2 1
    ((vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))).presheaf.map (homOfLE inf_le_left).op
      (vertexTwistTwoMiddleOverlapSection R d hd c)) = (twoMiddleCorrectedCorners R d c.val).2 at hc
  rw [vertexTwistRowSectionBaseEquiv_apply,hc]
  exact twoMiddleCorrectedCorners_constant R d hd c.val

/-- The actual class defined by original row primitives, native sheaf gluing and the original outer connecting map.
The definition uses no full state projection or transported coefficient action. -/
noncomputable def vertexTwistTwoMiddleZeroSecondToH1 (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    twoMiddleCycles R d →ₗ[R] vertexTwistTwoH1Module R d := by
  letI := schemeBaseLocalCohomologyModule (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) ⊤ 1
  letI := schemeBaseCohomologyModule (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1
  exact (schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1).toLinearMap.comp
      ((schemeBaseSectionConnectingLinear (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R)).comp
          (vertexTwistTwoMiddleOverlapSection R d hd))

/-- Every original full cocycle is sent to the native outer connecting class of its specified glued overlap section. -/
theorem vertexTwistTwoMiddleZeroSecondToH1_connecting (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) :
    vertexTwistTwoMiddleZeroSecondToH1 R d hd c =
      schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1
        (SheafTools.mayerVietorisSectionConnecting (vertexTwoOuterSquare R)
          (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ)))
            (vertexTwistTwoMiddleOverlapSection R d hd c)) := rfl

variable [IsNoetherianRing R]

/-- The specified native cocycle map agrees with the existing original outer coefficient representative. -/
theorem vertexTwistTwoMiddleZeroSecondToH1_coefficient (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) :
    vertexTwistTwoMiddleZeroSecondToH1 R d hd c =
      vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd
        (Submodule.Quotient.mk (vertexTwistRowSectionBaseEquiv R d hd 2
          (vertexTwistTwoMiddleOverlapSection R d hd c))) := by
  rw [vertexTwistTwoZeroSecondCoefficientH1Equiv_mk,LinearEquiv.symm_apply_apply]
  rfl

/-- For every original full middle cocycle with zero second twist, the actual state coordinate is its original full contraction projection. -/
theorem vertexTwistTwoMiddleZeroSecondToH1_projection (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoMiddleZeroSecondToH1 R d hd c) =
      twoMiddleStateProjection R d c := by
  rw [vertexTwistTwoH1StateEquiv_of_zero R d hd]
  change twoBaseH1MiddleStateEquiv R d hd
    (vertexTwistTwoZeroSecondLineH1Equiv R d hd (vertexTwistTwoMiddleZeroSecondToH1 R d hd c)) = _
  rw [vertexTwistTwoMiddleZeroSecondToH1_coefficient,vertexTwistTwoZeroSecondLineH1Equiv_representative]
  exact twoMiddleZeroSecond_projection R d hd c _ (vertexTwistTwoMiddleOverlapSection_base R d hd c)

end BPFixedPoints.ProjectiveLine
