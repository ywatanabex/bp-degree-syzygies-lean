import BPFixedPoints.Incidence.CechCubicalCellDiagonalAugmentation
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # The original component diagonal is the native tensor unit identification -/

namespace BPFixedPoints.CechCubicalCell
open Finsupp
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable (R : Type*) [CommRing R] (V : Type*) [Fintype V]

/-- The unique original component generator identifies its native tensor square with itself. -/
def componentTensorFold : Components R V ⊗[R] Components R V ≃ₗ[R] Components R V :=
  let e := Finsupp.uniqueLinearEquiv R R (fun _ : V => (0 : Fin 1))
  (TensorProduct.congr e e).trans ((TensorProduct.lid R R).trans e.symm)

/-- The inverse native tensor unit identification is precisely the already specified component diagonal. -/
theorem componentTensorFold_symm :
    (componentTensorFold R V).symm.toLinearMap = componentDiagonal R (V := V) := by
  apply Finsupp.lhom_ext
  intro s r
  have hs : s=(fun _ : V => (0 : Fin 1)) := Subsingleton.elim _ _
  subst s
  simp [componentTensorFold,componentDiagonal,Finsupp.llift_apply,TensorProduct.congr_symm,
    TensorProduct.smul_tmul']
  have hr : (single (fun _ : V => (0 : Fin 1)) r : Components R V) =
      r • single (fun _ => 0) 1 := by simp
  rw [hr,TensorProduct.tmul_smul,TensorProduct.smul_tmul']

/-- The original component diagonal is bijective, including over the zero ring and for no vertices. -/
theorem componentDiagonal_bijective : Function.Bijective (componentDiagonal R (V := V)) := by
  rw [← componentTensorFold_symm R V]
  exact (componentTensorFold R V).symm.bijective

end
end BPFixedPoints.CechCubicalCell
