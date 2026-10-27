import BPFixedPoints.Incidence.CechProductProjectionCoefficients
import BPFixedPoints.Incidence.CechTwoRowKernelStates

/-! # Original state monomials in the original mixed face coordinates -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- A zero-twist state reads the original right-chart constant monomial. -/
theorem lineProjectionMonomial_zero (k : Fin (phi 0)) :
    lineProjectionMonomial 0 k = Sum.inr (Sum.inl 0) := by
  unfold lineProjectionMonomial
  cases (lineStateIndexEquiv 0).symm k with
  | inl _ => rfl
  | inr j => exact Fin.elim0 j

/-- A negative-twist state reads the original Laurent exponent minus its original index minus one. -/
theorem lineProjectionMonomial_pos (d : ℕ) (hd : 0 < d) (k : Fin (phi d)) :
    lineProjectionMonomial d k = Sum.inr (Sum.inr (-(k : ℤ)-1)) := by
  unfold lineProjectionMonomial
  cases he : (lineStateIndexEquiv d).symm k with
  | inl j =>
    have hj := j.isLt
    simp only [ite_eq_right (Nat.ne_of_gt hd)] at hj
    omega
  | inr j =>
    have hh := congrArg Fin.val ((lineStateIndexEquiv d).apply_symm_apply k)
    rw [he] at hh
    change (if d = 0 then 1 else 0)+j.val = k.val at hh
    rw [ite_eq_right (Nat.ne_of_gt hd),zero_add] at hh
    exact congrArg (fun n : ℕ => (Sum.inr (Sum.inr (-(n : ℤ)-1)) : Basis)) hh

/-- Currying the original face coefficients retains exactly each original mixed monomial coefficient. -/
theorem twoRowFaceCoordinates_coefficient (b c : Fin 3) (x : FaceRing R (![b,c] : Fin 2 → Fin 3))
    (n : FaceExponent c) (m : FaceExponent b) :
    (twoRowFaceCoordinates R b c x n).coeff m =
      x.coeff ((twoRowExponentEquiv b c).symm (n,m)) := by
  change (AddMonoidAlgebra.coeffLinearEquiv R)
    ((AddMonoidAlgebra.coeffLinearEquiv R).symm
      ((mapDomain (twoRowExponentEquiv b c) (AddMonoidAlgebra.coeffLinearEquiv R x)).curry n)) m = _
  rw [LinearEquiv.apply_symm_apply]
  change mapDomain (twoRowExponentEquiv b c) (AddMonoidAlgebra.coeffLinearEquiv R x) (n,m) = _
  rw [mapDomain_equiv_apply]
  rfl

end BPFixedPoints.CechProduct
