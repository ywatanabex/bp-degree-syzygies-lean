import BPFixedPoints.Incidence.CechCubicalCellDiagonalSupport

/-! # The original tensor cell boundary in its original pair coordinates

The two cell boundaries are combined with the original left overlap parity.
The specified diagonal is a chain map into this actual tensor differential.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp GradedContraction CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable (R : Type*) [CommRing R] (V : Type) [Fintype V]

/-- Original pairs of the original cubical cells. -/
abbrev CellPairs := ((V → Fin 3) × (V → Fin 3)) →₀ R

/-- The original tensor differential in the original free pair coordinates. -/
noncomputable def pairBoundary : Module.End R (CellPairs R V) :=
  (pairCoordinates R V).toLinearMap.comp
    (((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).d.comp
      (pairCoordinates R V).symm.toLinearMap)

/-- The original specified diagonal in its original free pair coordinates. -/
noncomputable def flatDiagonal : Cells R V →ₗ[R] CellPairs R V :=
  (pairCoordinates R V).toLinearMap.comp (diagonal R V).map

@[simp] theorem pairBoundary_apply (x : CellPairs R V) :
    pairBoundary R V x = pairCoordinates R V
      (((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).d
        ((pairCoordinates R V).symm x)) := rfl

/-- The original pair differential squares to zero. -/
theorem pairBoundary_square : (pairBoundary R V).comp (pairBoundary R V) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,pairBoundary_apply,LinearEquiv.symm_apply_apply]
  have h := LinearMap.congr_fun
    ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).d_sq
      ((pairCoordinates R V).symm x)
  change _ = pairCoordinates R V 0
  exact congrArg (pairCoordinates R V) h

/-- The specified original cell diagonal preserves the actual tensor differential. -/
theorem flatDiagonal_boundary (x : Cells R V) :
    pairBoundary R V (flatDiagonal R V x) = flatDiagonal R V ((contraction R (fun _ : V => 0)).d x) := by
  simp only [flatDiagonal,LinearMap.comp_apply,pairBoundary_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,diagonal_boundary]

variable [DecidableEq V]

/-- Every endpoint coefficient of the original tensor differential, including the full right-factor sign. -/
theorem pairBoundary_single (p q : V → Fin 3) (r : R) :
    pairBoundary R V (single (p,q) r) =
      (∑ v, (single (Function.update p v 0,q)
        (((-1 : R)^faceBoundaryPrefix p v)*((if p v = 2 then 1 else 0)*r)) -
        single (Function.update p v 1,q)
          (((-1 : R)^faceBoundaryPrefix p v)*((if p v = 2 then 1 else 0)*r)))) +
      (∑ v, (single (p,Function.update q v 0)
        (((-1 : R)^(faceDegree p+faceBoundaryPrefix q v))*((if q v = 2 then 1 else 0)*r)) -
        single (p,Function.update q v 1)
          (((-1 : R)^(faceDegree p+faceBoundaryPrefix q v))*((if q v = 2 then 1 else 0)*r)))) := by
  rw [pairBoundary_apply]
  change finsuppTensorFinsupp' R _ _
    (((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).d
      ((finsuppTensorFinsupp' R _ _).symm (single (p,q) r))) = _
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  simp only [GradedContraction.tensor,tensorD,LinearMap.add_apply,TensorProduct.map_tmul,
    Module.End.one_apply,contraction_d_single,contraction_sign_single,
    TensorProduct.sum_tmul,TensorProduct.sub_tmul,TensorProduct.tmul_sum,TensorProduct.tmul_sub,
    ← TensorProduct.smul_tmul',map_add,map_sum,map_sub,map_smul,
    finsuppTensorFinsupp'_single_tmul_single,mul_one,one_mul,Finsupp.smul_single,smul_eq_mul,
    smul_sum,smul_sub]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    by_cases h : p v = 2 <;> simp [h]
  · apply Finset.sum_congr rfl
    intro v _
    simp only [pow_add,mul_assoc]

end BPFixedPoints.CechCubicalCell
