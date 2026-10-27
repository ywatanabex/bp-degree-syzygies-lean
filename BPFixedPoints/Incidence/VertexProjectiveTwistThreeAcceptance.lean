import BPFixedPoints.Incidence.VertexProjectiveTwistCohomologyRanks
import BPFixedPoints.Incidence.CechMinusTwoBasis

/-! # Actual Ext acceptance examples for the all-degree state comparison

The examples go through the actual sheaf Ext comparison. They retain
three negative factors, a zero middle factor and a minus-one factor.
The all-minus-two representative retains its original Laurent exponents.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]
local instance threeMinusTwoStateBasisSubsingleton : Subsingleton (HBasis (fun _ : Fin 3 => 2)) := by
  change Subsingleton (Fin 3 → Fin 1)
  infer_instance
noncomputable local instance threeAcceptanceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 3))) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original scalar state for the three minus-two factors. -/
noncomputable def threeMinusTwoState (r : R) : stateDegreePiece R (fun _ : Fin 3 => 2) 3 :=
  ⟨single (fun _ => gapZero) r,by
    intro κ _
    norm_num [cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ]⟩

/-- The original degree-three state coordinate is its original unique coefficient. -/
noncomputable def threeMinusTwoStateEquiv : stateDegreePiece R (fun _ : Fin 3 => 2) 3 ≃ₗ[R] R :=
  (LinearEquiv.ofTop _ (by
    simp [stateDegreePiece,cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ])).trans
      (Finsupp.uniqueLinearEquiv R R (fun _ => gapZero))

/-- The original all-overlap face for the three minus-two factors. -/
def threeOverlapFace : Fin 3 → Fin 3 := fun _ => 2

/-- Its originally specified Laurent monomial has exponent minus one in every original coordinate. -/
def threeGapExponent : FaceMonoid threeOverlapFace := fun _ => (-1 : ℤ)

/-- The original coefficient representative is exactly the original three-factor Laurent gap monomial. -/
theorem threeMinusTwoInclusion_coefficient (r : R) :
    (vertexTwistCellCoefficientEquiv R (Fin 3) (fun _ => 2) 3
      (vertexTwistCellStateInclusion R (Fin 3) (fun _ => 2) 3 (threeMinusTwoState R r)).val).val =
        single (embedFace threeOverlapFace threeGapExponent) r := by
  rw [vertexTwistCellStateInclusion_coefficient]
  exact contraction_two_i_single R r

/-- In the original unsigned frame the same representative has its required degree-three minus sign. -/
theorem threeMinusTwoInclusion_native (r : R) :
    vertexTwistSheafFaceSectionsEquiv R (Fin 3) (fun _ => -((2 : ℕ) : ℤ)) threeOverlapFace
      ((vertexTwistCellNativeEquiv R (Fin 3) (fun _ => -((2 : ℕ) : ℤ)) 3
        (vertexTwistCellStateInclusion R (Fin 3) (fun _ => 2) 3 (threeMinusTwoState R r)).val).val
          threeOverlapFace) = -AddMonoidAlgebra.single threeGapExponent r := by
  have h := congrArg (fun x => faceEquiv R x threeOverlapFace) (threeMinusTwoInclusion_coefficient R r)
  change faceEquiv R (vertexTwistCubicalChainEquiv R (Fin 3) (fun _ => 2)
    (vertexTwistCellNativeEquiv R (Fin 3) _ 3 _).val) threeOverlapFace = _ at h
  rw [vertexTwistCubicalChainEquiv_face,faceEquiv_single_same] at h
  have hd : faceDegree threeOverlapFace = 3 := by
    norm_num [faceDegree,threeOverlapFace,Fin.sum_univ_succ]
  rw [hd] at h
  simpa only [pow_succ,pow_zero,mul_one,neg_one_mul,neg_neg,one_mul,neg_one_smul] using
    congrArg Neg.neg h

variable [IsNoetherianRing R]

/-- The actual Ext-defined H3 of the three minus-two factors is the original base module. -/
noncomputable def threeMinusTwoActualEquiv :
    letI := vertexTwistStateCohomologyModule R (Fin 3) (fun _ => 2) 3
    (vertexTwistAbelianSheaf R (Fin 3) (fun _ => -((2 : ℕ) : ℤ))).H 3 ≃ₗ[R] R :=
  (vertexTwistStateLinearEquiv R (Fin 3) (fun _ => 2) 3).trans (threeMinusTwoStateEquiv R)

/-- The actual specified connecting representative of the original three-factor Laurent gap has exactly its original scalar. -/
theorem threeMinusTwoActualEquiv_representative (r : R) :
    letI := vertexTwistStateCohomologyModule R (Fin 3) (fun _ => 2) 3
    letI := vertexTwistCellModule R (Fin 3) (fun _ => -((2 : ℕ) : ℤ)) 2
    threeMinusTwoActualEquiv R
      (vertexTwistCellActualLinearEquiv R (Fin 3) (fun _ => -((2 : ℕ) : ℤ)) 2
        (QuotientAddGroup.mk (vertexTwistCellStateInclusion R (Fin 3) (fun _ => 2) 3
          (threeMinusTwoState R r)))) = r := by
  letI := vertexTwistStateCohomologyModule R (Fin 3) (fun _ => 2) 3
  letI := vertexTwistCellModule R (Fin 3) (fun _ => -((2 : ℕ) : ℤ)) 2
  change threeMinusTwoStateEquiv R (vertexTwistPositiveStateLinearEquiv R (Fin 3) (fun _ => 2) 2 _) = r
  rw [vertexTwistPositiveStateLinearEquiv_representative,vertexTwistCellCycleProjection_inclusion]
  exact Finsupp.single_eq_same

/-- The original twist with a zero middle factor and two distinct Laurent gaps. -/
def threeMixedDegree : Fin 3 → ℕ := ![2,0,3]

/-- Actual H2 of twist (-2,0,-3) is finite free over the original base. -/
theorem threeMixedActual_free :
    letI := vertexTwistStateCohomologyModule R (Fin 3) threeMixedDegree 2
    Module.Free R ((vertexTwistAbelianSheaf R (Fin 3) (fun v => -(threeMixedDegree v : ℤ))).H 2) :=
  vertexTwistCohomology_free R (Fin 3) threeMixedDegree 2

/-- The same actual H2 is finite over the original base ring. -/
theorem threeMixedActual_finite :
    letI := vertexTwistStateCohomologyModule R (Fin 3) threeMixedDegree 2
    Module.Finite R ((vertexTwistAbelianSheaf R (Fin 3) (fun v => -(threeMixedDegree v : ℤ))).H 2) :=
  vertexTwistCohomology_finite R (Fin 3) threeMixedDegree 2

/-- Over a nontrivial base the actual H2 of twist (-2,0,-3) has rank two. -/
theorem threeMixedActual_finrank [Nontrivial R] :
    letI := vertexTwistStateCohomologyModule R (Fin 3) threeMixedDegree 2
    Module.finrank R ((vertexTwistAbelianSheaf R (Fin 3) (fun v => -(threeMixedDegree v : ℤ))).H 2) = 2 := by
  letI := vertexTwistStateCohomologyModule R (Fin 3) threeMixedDegree 2
  rw [vertexTwistCohomology_finrank]
  norm_num [cohomologyDegree,lineCohomologyDegree,threeMixedDegree,Fin.sum_univ_succ,Fin.prod_univ_succ,phi]

/-- Every other actual degree of twist (-2,0,-3) vanishes. -/
theorem threeMixedActual_eq_zero (j : ℕ) (hj : j ≠ 2)
    (x : (vertexTwistAbelianSheaf R (Fin 3) (fun v => -(threeMixedDegree v : ℤ))).H j) : x = 0 := by
  apply vertexTwistCohomology_eq_zero_off_degree R (Fin 3) threeMixedDegree j _ x
  have hd : cohomologyDegree threeMixedDegree = 2 := by
    norm_num [cohomologyDegree,lineCohomologyDegree,threeMixedDegree,Fin.sum_univ_succ]
  exact hd ▸ hj.symm

/-- Actual cohomology of twist (-1,0,-2) vanishes in every degree. -/
theorem threeOneZeroTwoActual_eq_zero (j : ℕ)
    (x : (vertexTwistAbelianSheaf R (Fin 3) (fun v => -((![1,0,2] : Fin 3 → ℕ) v : ℤ))).H j) : x = 0 :=
  vertexTwistCohomology_eq_zero_of_one R (Fin 3) ![1,0,2] 0 rfl j x

end BPFixedPoints.ProjectiveLine
