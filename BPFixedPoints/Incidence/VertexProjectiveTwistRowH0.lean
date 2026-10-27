import BPFixedPoints.Incidence.SchemeModuleSectionKernel
import BPFixedPoints.Incidence.VertexProjectiveTwistRowStateFormula
import BPFixedPoints.Incidence.ProjectiveLineTwistH0

/-! # Original row sections and the original one-factor degree-zero states -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]

/-- Original row coordinates preserve exactly the original one-factor matching kernel. -/
theorem twoRowZeroCoordinates_map_ker (d : Fin 2 → ℕ) (b : Fin 3) :
    (LinearMap.ker (twoRowBoundary R (fun v => -(d v : ℤ)) b)).map
      (twoRowZeroCoordinates R b).toLinearMap =
        LinearMap.ker ((CechLine.differential (TwoRowBase R b) (d 1)).restrictScalars R) := by
  have hm (x : FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :
      CechLine.differential (TwoRowBase R b) (d 1) (twoRowZeroCoordinates R b x) = 0 ↔
        twoRowBoundary R (fun v => -(d v : ℤ)) b x = 0 := by
    have he := twoRowCoordinates_boundary R d b x
    constructor
    · intro hx
      apply (twoRowOneCoordinates R b).injective
      rw [he,hx,neg_zero,LinearEquiv.map_zero]
    · intro hx
      rw [hx,LinearEquiv.map_zero] at he
      exact neg_eq_zero.mp he.symm
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hm x).mpr hx
  · intro hz
    change CechLine.differential (TwoRowBase R b) (d 1) z = 0 at hz
    refine ⟨(twoRowZeroCoordinates R b).symm z,?_,LinearEquiv.apply_symm_apply _ _⟩
    apply (hm _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hz

/-- The original row section kernel equals the original one-factor degree-zero states over the first face ring. -/
noncomputable def twoRowKernelStateEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    LinearMap.ker (twoRowBoundary R (fun v => -(d v : ℤ)) b) ≃ₗ[R]
      CechLine.H0 (TwoRowBase R b) (d 1) :=
  ((twoRowZeroCoordinates R b).ofSubmodules _ _ (twoRowZeroCoordinates_map_ker R d b)).trans
    ((ProjectiveLine.cechLineKernelH0Equiv (TwoRowBase R b) (d 1)).restrictScalars R)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

noncomputable local instance rowH0HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual sections on an original row, with the independently defined geometric base action. -/
noncomputable def vertexTwistRowSectionModule (a : Fin 2 → ℤ) (b : Fin 3) : ModuleCat R :=
  SchemeTools.schemeBaseOpenSectionModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
    (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b)

/-- Original corner coefficients carry precisely the native matching kernel to the original coefficient kernel. -/
theorem vertexTwistRowCornerCoordinates_map_ker (a : Fin 2 → ℤ) (b : Fin 3) :
    (LinearMap.ker (SchemeTools.schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b))).map
        (vertexTwistRowCornerCoordinates R a b).toLinearMap = LinearMap.ker (twoRowBoundary R a b) := by
  have hm (s : vertexTwistTwoRectangleSections R a b 0 × vertexTwistTwoRectangleSections R a b 1) :
      twoRowBoundary R a b (vertexTwistRowCornerCoordinates R a b s) = 0 ↔
        SchemeTools.schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
          (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b) s = 0 := by
    rw [← vertexTwistRowCoordinates_boundary]
    exact (vertexTwistTwoRectangleCoordinates R a b 2).map_eq_zero_iff
  ext z
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact (hm s).mpr hs
  · intro hz
    change twoRowBoundary R a b z = 0 at hz
    refine ⟨(vertexTwistRowCornerCoordinates R a b).symm z,?_,LinearEquiv.apply_symm_apply _ _⟩
    apply (hm _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hz

/-- Native row sections are the original coefficient matching kernel; the inverse is original sheaf gluing. -/
noncomputable def vertexTwistRowSectionKernelEquiv (a : Fin 2 → ℤ) (b : Fin 3) :
    vertexTwistRowSectionModule R a b ≃ₗ[R] LinearMap.ker (twoRowBoundary R a b) :=
  (SchemeTools.schemeBaseSquareSectionKernelEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) a) (vertexTwoRowSquare R b)).trans
      ((vertexTwistRowCornerCoordinates R a b).ofSubmodules _ _ (vertexTwistRowCornerCoordinates_map_ker R a b))

/-- Actual row sections equal the original one-factor degree-zero states for the original geometric base action. -/
noncomputable def vertexTwistRowSectionStateEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b ≃ₗ[R]
      CechLine.H0 (TwoRowBase R b) (d 1) :=
  (vertexTwistRowSectionKernelEquiv R (fun v => -(d v : ℤ)) b).trans (twoRowKernelStateEquiv R d b)

/-- The row comparison retains the original restrictions, corner coefficients and one-factor projection. -/
theorem vertexTwistRowSectionStateEquiv_apply (d : Fin 2 → ℕ) (b : Fin 3)
    (s : vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b) :
    vertexTwistRowSectionStateEquiv R d b s = CechLine.projectionZero (TwoRowBase R b) (d 1)
      (twoRowZeroCoordinates R b (vertexTwistRowCornerCoordinates R (fun v => -(d v : ℤ)) b
        (SchemeTools.schemeBaseSquareSectionPair (vertexToBase R (Fin 2))
          (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoRowSquare R b) s))) := rfl

/-- Every negative second twist has no sections on any original row, without Noetherianity. -/
theorem vertexTwistRowSection_eq_zero_of_pos (d : Fin 2 → ℕ) (b : Fin 3) (hd : 0 < d 1)
    (s : vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) b) : s = 0 := by
  apply (vertexTwistRowSectionStateEquiv R d b).injective
  rw [map_zero]
  apply Finsupp.ext
  intro k
  have hk := k.isLt
  simp only [ite_eq_right (Nat.ne_of_gt hd)] at hk
  omega

/-- Actual Ext-defined row H0 equals the original degree-zero states for the independently defined geometric action. -/
noncomputable def vertexTwistRowH0StateLinearEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    SchemeTools.schemeBaseLocalCohomologyObject (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b) 0 ≃ₗ[R]
        CechLine.H0 (TwoRowBase R b) (d 1) :=
  (SchemeTools.schemeBaseLocalH0LinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b)).trans
        (vertexTwistRowSectionStateEquiv R d b)

/-- The actual row H0 comparison uses precisely the original Ext evaluation and native section comparison. -/
theorem vertexTwistRowH0StateLinearEquiv_apply (d : Fin 2 → ℕ) (b : Fin 3)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H' 0
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b)) :
    vertexTwistRowH0StateLinearEquiv R d b x = vertexTwistRowSectionStateEquiv R d b
      (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ)))
        (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b) x) := rfl

end BPFixedPoints.ProjectiveLine
