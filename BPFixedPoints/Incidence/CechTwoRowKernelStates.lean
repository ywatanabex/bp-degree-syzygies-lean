import BPFixedPoints.Incidence.CechTwoRowH1Kernel

/-! # Original first-factor H0 states of the original row H1 matching kernel -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- Read both original first-coordinate coefficient polynomials at every original second-factor gap. -/
noncomputable def twoRowH1PairCoefficients (d : Fin 2 → ℕ) :
    (CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1)) ≃ₗ[R]
      (Fin (d 1-1) → CechLine.C0 R) where
  toFun x k := (AddMonoidAlgebra.coeffLinearEquiv R (x.1 k),AddMonoidAlgebra.coeffLinearEquiv R (x.2 k))
  invFun y :=
    ((Finsupp.linearEquivFunOnFinite R (TwoRowBase R 0) _).symm
      (fun k => (AddMonoidAlgebra.coeffLinearEquiv R).symm (y k).1),
    (Finsupp.linearEquivFunOnFinite R (TwoRowBase R 1) _).symm
      (fun k => (AddMonoidAlgebra.coeffLinearEquiv R).symm (y k).2))
  left_inv x := by
    apply Prod.ext
    · apply Finsupp.ext
      intro k
      exact (AddMonoidAlgebra.coeffLinearEquiv R).symm_apply_apply (x.1 k)
    · apply Finsupp.ext
      intro k
      exact (AddMonoidAlgebra.coeffLinearEquiv R).symm_apply_apply (x.2 k)
  right_inv y := by
    funext k
    exact Prod.ext ((AddMonoidAlgebra.coeffLinearEquiv R).apply_symm_apply (y k).1)
      ((AddMonoidAlgebra.coeffLinearEquiv R).apply_symm_apply (y k).2)
  map_add' x y := by
    funext k
    exact Prod.ext ((AddMonoidAlgebra.coeffLinearEquiv R).map_add (x.1 k) (y.1 k))
      ((AddMonoidAlgebra.coeffLinearEquiv R).map_add (x.2 k) (y.2 k))
  map_smul' r x := by
    funext k
    exact Prod.ext ((AddMonoidAlgebra.coeffLinearEquiv R).map_smul r (x.1 k))
      ((AddMonoidAlgebra.coeffLinearEquiv R).map_smul r (x.2 k))

/-- The original row-state matching equation is exactly the original first-factor cocycle equation at every gap. -/
theorem twoRowH1PairCoefficients_closed_iff (d : Fin 2 → ℕ)
    (x : CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1)) :
    twoRowStateDifference R d x = 0 ↔
      ∀ k, CechLine.differential R (d 0) (twoRowH1PairCoefficients R d x k) = 0 := by
  constructor
  · intro hx k
    have he := twoRowStateDifference_apply_gap R d x k
    rw [hx,Finsupp.zero_apply,map_zero] at he
    exact neg_eq_zero.mp he.symm
  · intro hx
    apply Finsupp.ext
    intro k
    apply (AddMonoidAlgebra.coeffLinearEquiv R).injective
    rw [twoRowStateDifference_apply_gap]
    change -CechLine.differential R (d 0) (twoRowH1PairCoefficients R d x k) = _
    rw [hx,neg_zero]
    rfl

/-- The original row-state matching kernel is the original first-factor Cech kernel at each original gap. -/
noncomputable def twoRowKernelGapEquiv (d : Fin 2 → ℕ) :
    LinearMap.ker (twoRowStateDifference R d) ≃ₗ[R]
      (Fin (d 1-1) → LinearMap.ker (CechLine.differential R (d 0))) where
  toFun x k := ⟨twoRowH1PairCoefficients R d x.val k,
    (twoRowH1PairCoefficients_closed_iff R d x.val).mp x.property k⟩
  invFun y := ⟨(twoRowH1PairCoefficients R d).symm (fun k => (y k).val),by
    apply (twoRowH1PairCoefficients_closed_iff R d _).mpr
    intro k
    rw [LinearEquiv.apply_symm_apply]
    exact (y k).property⟩
  left_inv x := Subtype.ext ((twoRowH1PairCoefficients R d).symm_apply_apply x.val)
  right_inv y := by
    funext k
    apply Subtype.ext
    change (twoRowH1PairCoefficients R d) ((twoRowH1PairCoefficients R d).symm _) k = _
    rw [LinearEquiv.apply_symm_apply]
  map_add' x y := by
    funext k
    apply Subtype.ext
    exact congrFun ((twoRowH1PairCoefficients R d).map_add x.val y.val) k
  map_smul' r x := by
    funext k
    apply Subtype.ext
    exact congrFun ((twoRowH1PairCoefficients R d).map_smul r x.val) k

/-- The original row H1 kernel is the original first-factor H0 state family, with its original projection. -/
noncomputable def twoRowKernelH0Equiv (d : Fin 2 → ℕ) :
    LinearMap.ker (twoRowStateDifference R d) ≃ₗ[R]
      Fin (d 1-1) →₀ CechLine.H0 R (d 0) :=
  (twoRowKernelGapEquiv R d).trans
    ((LinearEquiv.piCongrRight fun _ => ProjectiveLine.cechLineKernelH0Equiv R (d 0)).trans
      (Finsupp.linearEquivFunOnFinite R (CechLine.H0 R (d 0)) _).symm)

/-- Every original matching pair retains the original first-factor projection at every original second-factor gap. -/
theorem twoRowKernelH0Equiv_apply (d : Fin 2 → ℕ)
    (x : LinearMap.ker (twoRowStateDifference R d)) (k : Fin (d 1-1)) :
    twoRowKernelH0Equiv R d x k = CechLine.projectionZero R (d 0) (twoRowH1PairCoefficients R d x.val k) := rfl

/-- The original inverse first-factor state family keeps the original one-factor inclusion at every gap. -/
theorem twoRowKernelH0Equiv_inverse (d : Fin 2 → ℕ)
    (s : Fin (d 1-1) →₀ CechLine.H0 R (d 0)) (k : Fin (d 1-1)) :
    twoRowH1PairCoefficients R d ((twoRowKernelH0Equiv R d).symm s).val k =
      CechLine.inclusionZero R (d 0) (s k) := by
  change twoRowH1PairCoefficients R d ((twoRowH1PairCoefficients R d).symm _) k = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end BPFixedPoints.CechProduct
