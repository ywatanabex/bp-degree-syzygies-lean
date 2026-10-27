import BPFixedPoints.Incidence.CechCubicalCellDiagonalStep
import BPFixedPoints.Incidence.CechCubicalCellBoundary
import BPFixedPoints.Incidence.CechCubicalCellMaps

/-! # The specified diagonal on the original finite cubical cell complex

The interval Alexander--Whitney diagonal is tensored with its actual Koszul
crossing and transported through the original fixed cell enumeration.
The original differential and original parity are retained in every degree.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp GradedContraction CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000

section Transport
variable {R D K D' K' : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup K] [Module R K]
  [AddCommGroup D'] [Module R D'] [AddCommGroup K'] [Module R K']
  {a : GradedContraction R D K}

/-- A specified original diagonal retains its maps under the specified original coordinates. -/
noncomputable def Diagonal.congr (f : Diagonal a) (u : D ≃ₗ[R] D') (v : K ≃ₗ[R] K') :
    Diagonal (a.congr u v) where
  map := (TensorProduct.map u.toLinearMap u.toLinearMap).comp (f.map.comp u.symm.toLinearMap)
  boundary x := by
    have he : ((a.congr u v).tensor (a.congr u v)).d.comp (TensorProduct.map u.toLinearMap u.toLinearMap) =
        (TensorProduct.map u.toLinearMap u.toLinearMap).comp (a.tensor a).d := by
      apply TensorProduct.ext'
      intro y z
      simp [GradedContraction.tensor,tensorD,congr_d_apply,congr_sign_apply]
    change ((a.congr u v).tensor (a.congr u v)).d
      (TensorProduct.map u.toLinearMap u.toLinearMap (f.map (u.symm x))) = _
    have hh := LinearMap.congr_fun he (f.map (u.symm x))
    simp only [LinearMap.comp_apply] at hh
    rw [hh,f.boundary]
    simp only [LinearMap.comp_apply,congr_d_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  parity x := by
    have he : ((a.congr u v).tensor (a.congr u v)).sign.comp (TensorProduct.map u.toLinearMap u.toLinearMap) =
        (TensorProduct.map u.toLinearMap u.toLinearMap).comp (a.tensor a).sign := by
      apply TensorProduct.ext'
      intro y z
      simp [GradedContraction.tensor,congr_sign_apply]
    change ((a.congr u v).tensor (a.congr u v)).sign
      (TensorProduct.map u.toLinearMap u.toLinearMap (f.map (u.symm x))) = _
    have hh := LinearMap.congr_fun he (f.map (u.symm x))
    simp only [LinearMap.comp_apply] at hh
    rw [hh,f.parity]
    simp only [LinearMap.comp_apply,congr_sign_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

@[simp] theorem Diagonal.congr_map (f : Diagonal a) (u : D ≃ₗ[R] D') (v : K ≃ₗ[R] K') (x : D') :
    (f.congr u v).map x = TensorProduct.map u.toLinearMap u.toLinearMap (f.map (u.symm x)) := rfl
end Transport

variable (R : Type*) [CommRing R]

/-- The diagonal of the empty cube preserves its original single component. -/
noncomputable def emptyDiagonal : Diagonal (empty R) where
  map := Finsupp.llift _ R R _ fun q => single q 1 ⊗ₜ[R] single q 1
  boundary x := by simp [empty,GradedContraction.tensor,tensorD]
  parity x := by simp [empty,GradedContraction.tensor]

/-- Iterate the specified interval diagonal in the original ordered cell coordinates. -/
noncomputable def finDiagonal : (n : ℕ) → Diagonal (finContraction R n (fun _ => 0))
  | 0 => emptyDiagonal R
  | n+1 => (diagonalStep (finContraction R n (fun _ => 0)) (finDiagonal n)).congr
      (consEquiv R fun _ : Fin (n+1) => Fin 3) (consEquiv R fun _ : Fin (n+1) => Fin 1)

/-- Keep exactly the fixed vertex enumeration used by the original native complex. -/
noncomputable def diagonal (V : Type*) [Fintype V] : Diagonal (contraction R (fun _ : V => 0)) :=
  let e := (Fintype.equivFin V).symm
  (finDiagonal R (Fintype.card V)).congr
    (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 3))))
    (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 1))))

/-- The specified many-vertex diagonal preserves the original boundary, including every Koszul crossing. -/
theorem diagonal_boundary {V : Type*} [Fintype V] (x : Cells R V) :
    ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).d ((diagonal R V).map x) =
      (diagonal R V).map ((contraction R (fun _ : V => 0)).d x) := (diagonal R V).boundary x

/-- The same specified many-vertex diagonal preserves the original overlap parity. -/
theorem diagonal_parity {V : Type*} [Fintype V] (x : Cells R V) :
    ((contraction R (fun _ : V => 0)).tensor (contraction R (fun _ : V => 0))).sign ((diagonal R V).map x) =
      (diagonal R V).map ((contraction R (fun _ : V => 0)).sign x) := (diagonal R V).parity x

/-- The empty diagonal retains the original coefficient only once. -/
theorem emptyDiagonal_single (q : Fin 0 → Fin 3) (r : R) :
    (emptyDiagonal R).map (single q r) = r • (single q 1 ⊗ₜ[R] single q 1) := by
  simp [emptyDiagonal,Finsupp.llift_apply]

/-- The actual recursive generator formula, retaining the specified original head term and tail. -/
theorem finDiagonal_single_cons (n : ℕ) (k : Fin 3) (q : Fin n → Fin 3) (r : R) :
    (finDiagonal R (n+1)).map (single (Fin.cons k q) r) =
      TensorProduct.map (consEquiv R (fun _ : Fin (n+1) => Fin 3)).toLinearMap
        (consEquiv R (fun _ : Fin (n+1) => Fin 3)).toLinearMap
          (headDiagonalTerm (finContraction R n (fun _ => 0)) k ((finDiagonal R n).map (single q r))) := by
  rw [finDiagonal,Diagonal.congr_map,consEquiv_symm_single]
  simp only [Fin.cons_zero,Fin.tail_cons,diagonalStep,diagonalStepMap_head]

end BPFixedPoints.CechCubicalCell
