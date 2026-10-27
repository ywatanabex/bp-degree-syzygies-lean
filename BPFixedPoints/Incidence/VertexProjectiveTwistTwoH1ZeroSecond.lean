import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1Kernel
import BPFixedPoints.Incidence.VertexProjectiveTwistRowH0Restriction
import BPFixedPoints.Incidence.CechTwoBaseH1
import BPFixedPoints.Incidence.CechTwoMiddleStatePiece

/-! # Actual two-vertex H1 states when the second twist is zero -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SchemeTools Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R]
noncomputable local instance zeroSecondH1HasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original two row-section coefficient comparisons with zero second twist. -/
noncomputable def vertexTwistTwoBasePairCoordinates (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    (vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) 0 ×
      vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) 1) ≃ₗ[R]
        (TwoRowBase R 0 × TwoRowBase R 1) :=
  (vertexTwistRowSectionBaseEquiv R d hd 0).prodCongr (vertexTwistRowSectionBaseEquiv R d hd 1)

/-- The actual outer section difference is precisely the original first-coordinate coefficient difference. -/
theorem vertexTwistTwoBasePairCoordinates_difference (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (x : vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) 0 ×
      vertexTwistRowSectionModule R (fun v => -(d v : ℤ)) 1) :
    vertexTwistRowSectionBaseEquiv R d hd 2
      (schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) x) =
      twoBaseDifference R d (vertexTwistTwoBasePairCoordinates R d hd x) := by
  change vertexTwistRowSectionBaseEquiv R d hd 2
    (vertexTwistRowSectionRestriction R d (b := 0) (c := 2) (Or.inr rfl) x.1 -
      vertexTwistRowSectionRestriction R d (b := 1) (c := 2) (Or.inr rfl) x.2) = _
  rw [map_sub,vertexTwistRowSectionBaseEquiv_restrict,vertexTwistRowSectionBaseEquiv_restrict]
  rfl

/-- The original row coefficient comparison preserves precisely the native outer boundary image. -/
theorem vertexTwistTwoBasePairCoordinates_range (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    (LinearMap.range (schemeBaseSquareSectionDifference (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R))).map
        (vertexTwistRowSectionBaseEquiv R d hd 2).toLinearMap = LinearMap.range (twoBaseDifference R d) := by
  ext z
  constructor
  · rintro ⟨y,⟨x,rfl⟩,rfl⟩
    exact ⟨vertexTwistTwoBasePairCoordinates R d hd x,(vertexTwistTwoBasePairCoordinates_difference R d hd x).symm⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨s,rfl⟩ := (vertexTwistTwoBasePairCoordinates R d hd).surjective x
    exact ⟨_,⟨s,rfl⟩,vertexTwistTwoBasePairCoordinates_difference R d hd s⟩

variable [IsNoetherianRing R]

/-- The original outer coefficient cokernel computes actual global H1 with zero second twist. -/
noncomputable def vertexTwistTwoZeroSecondCoefficientH1Equiv (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    (TwoRowBase R 2 ⧸ LinearMap.range (twoBaseDifference R d)) ≃ₗ[R] vertexTwistTwoH1Module R d := by
  let : Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))).H' 1 (vertexTwoOuterSquare R).X₂) :=
      ⟨fun x y => (vertexTwistRowH1_eq_zero_of_le_one R d 0 (by omega) x).trans
        (vertexTwistRowH1_eq_zero_of_le_one R d 0 (by omega) y).symm⟩
  let : Subsingleton (((SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ)))).H' 1 (vertexTwoOuterSquare R).X₃) :=
      ⟨fun x y => (vertexTwistRowH1_eq_zero_of_le_one R d 1 (by omega) x).trans
        (vertexTwistRowH1_eq_zero_of_le_one R d 1 (by omega) y).symm⟩
  exact (Submodule.Quotient.equiv _ _ (vertexTwistRowSectionBaseEquiv R d hd 2)
    (vertexTwistTwoBasePairCoordinates_range R d hd)).symm.trans
      ((schemeBaseSquareSectionH1LinearEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R)).trans
          (schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
            (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1))

/-- Every original coefficient representative uses the original frame, native connecting map and whole-space Ext comparison. -/
theorem vertexTwistTwoZeroSecondCoefficientH1Equiv_mk (d : Fin 2 → ℕ) (hd : d 1 = 0) (z : TwoRowBase R 2) :
    vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd (Submodule.Quotient.mk z) =
      schemeBaseLocalTopLinearEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 1
        (SheafTools.mayerVietorisSectionConnecting (vertexTwoOuterSquare R)
          (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ)))
            ((vertexTwistRowSectionBaseEquiv R d hd 2).symm z)) := rfl

/-- Actual global H1 with zero second twist is the original first-factor Laurent state module. -/
noncomputable def vertexTwistTwoZeroSecondLineH1Equiv (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    vertexTwistTwoH1Module R d ≃ₗ[R] CechLine.H1 R (d 0) :=
  (vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd).symm.trans (twoBaseQuotientStateEquiv R d)

/-- Every original outer connecting representative retains the original first-factor Laurent projection. -/
theorem vertexTwistTwoZeroSecondLineH1Equiv_representative (d : Fin 2 → ℕ) (hd : d 1 = 0) (z : TwoRowBase R 2) :
    vertexTwistTwoZeroSecondLineH1Equiv R d hd
      (vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd (Submodule.Quotient.mk z)) =
        twoBaseStateProjection R d z := by
  change twoBaseQuotientStateEquiv R d
    ((vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd).symm
      (vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd (Submodule.Quotient.mk z))) = _
  rw [LinearEquiv.symm_apply_apply,twoBaseQuotientStateEquiv_mk]

/-- Each original first-coordinate Laurent gap connecting class maps to its specified original state. -/
theorem vertexTwistTwoZeroSecondLineH1Equiv_gap (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (k : Fin (d 0-1)) (r : R) :
    vertexTwistTwoZeroSecondLineH1Equiv R d hd
      (vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd
        (Submodule.Quotient.mk (AddMonoidAlgebra.single (-(k : ℤ)-1) r))) = Finsupp.single k r := by
  rw [vertexTwistTwoZeroSecondLineH1Equiv_representative]
  change CechLine.projectionOne R (d 0) (Finsupp.single (-(k : ℤ)-1) r) = _
  rw [← CechLine.inclusionOne_single]
  exact LinearMap.congr_fun (CechLine.projectionOne_inclusionOne R (d 0)) _

/-- Every original first-factor state has its original inclusion, native section frame and connecting class as inverse. -/
theorem vertexTwistTwoZeroSecondLineH1Equiv_inverse (d : Fin 2 → ℕ) (hd : d 1 = 0) (s : CechLine.H1 R (d 0)) :
    (vertexTwistTwoZeroSecondLineH1Equiv R d hd).symm s =
      vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd
        (Submodule.Quotient.mk ((twoBaseOverlapCoefficients R).symm (CechLine.inclusionOne R (d 0) s))) := by
  change vertexTwistTwoZeroSecondCoefficientH1Equiv R d hd ((twoBaseQuotientStateEquiv R d).symm s) = _
  rw [twoBaseQuotientStateEquiv_symm]

/-- Actual H1 with zero second twist equals the original degree-one state piece. -/
noncomputable def vertexTwistTwoH1ZeroSecondStateEquiv (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    vertexTwistTwoH1Module R d ≃ₗ[R] twoMiddleStatePiece R d :=
  (vertexTwistTwoZeroSecondLineH1Equiv R d hd).trans (twoBaseH1MiddleStateEquiv R d hd)

end BPFixedPoints.ProjectiveLine
