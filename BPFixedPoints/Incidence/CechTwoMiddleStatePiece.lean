import BPFixedPoints.Incidence.CechTwoRowKernelStates
import BPFixedPoints.Incidence.CechTwoTopStatePiece

/-! # The original degree-one state piece when the second twist is negative -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- The degree-one piece of the original two-vertex state module. -/
abbrev twoMiddleStatePiece (d : Fin 2 → ℕ) : Submodule R (H R d) :=
  supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = 1}

/-- With negative second twist, original state degree one is equivalent to a zero first twist. -/
theorem two_cohomologyDegree_one_iff (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    cohomologyDegree d = 1 ↔ d 0 = 0 := by
  simp [cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ,Nat.ne_of_gt hd]

/-- Original gap and first H0 indices are exactly the original degree-one state indices. -/
noncomputable def twoRowMiddleIndexEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    (Fin (d 1-1) × CechLine.H0Index (d 0)) ≃
      {κ : HBasis d // (cohomologyDegree d : ℤ) = 1} := by
  by_cases h0 : d 0 = 0
  · let e0 : CechLine.H0Index (d 0) ≃ Fin (phi (d 0)) :=
      finCongr (by simp [CechLine.H0Index,h0])
    let e1 : Fin (d 1-1) ≃ Fin (phi (d 1)) := finCongr (phi_of_pos hd).symm
    have he : (cohomologyDegree d : ℤ) = 1 := by
      exact_mod_cast (two_cohomologyDegree_one_iff d hd).mpr h0
    exact
      { toFun := fun p => ⟨(piFinTwoEquiv fun v => Fin (phi (d v))).symm (e0 p.2,e1 p.1),he⟩
        invFun := fun κ => (e1.symm (κ.val 1),e0.symm (κ.val 0))
        left_inv := fun p => by
          change (e1.symm (e1 p.1),e0.symm (e0 p.2)) = p
          rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
        right_inv := fun κ => by
          apply Subtype.ext
          apply (piFinTwoEquiv fun v => Fin (phi (d v))).injective
          change (e0 (e0.symm (κ.val 0)),e1 (e1.symm (κ.val 1))) = (κ.val 0,κ.val 1)
          rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] }
  · letI : IsEmpty (CechLine.H0Index (d 0)) := by
      dsimp only [CechLine.H0Index]
      rw [ite_eq_right h0]
      infer_instance
    letI : IsEmpty {κ : HBasis d // (cohomologyDegree d : ℤ) = 1} := by
      refine ⟨fun κ => h0 ?_⟩
      apply (two_cohomologyDegree_one_iff d hd).mp
      exact_mod_cast κ.property
    exact Equiv.equivOfIsEmpty _ _

/-- Original first H0 states at original second Laurent gaps form the original degree-one state piece. -/
noncomputable def twoRowH0MiddleStateEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    (Fin (d 1-1) →₀ CechLine.H0 R (d 0)) ≃ₗ[R] twoMiddleStatePiece R d :=
  (Finsupp.curryLinearEquiv R).symm.trans
    ((Finsupp.mapDomain.linearEquiv R R (twoRowMiddleIndexEquiv d hd)).trans
      (supportedEquivFinsupp (R := R) (M := R) _).symm)

/-- The specified original row matching kernel equals the original degree-one state piece. -/
noncomputable def twoRowKernelMiddleStateEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    LinearMap.ker (twoRowStateDifference R d) ≃ₗ[R] twoMiddleStatePiece R d :=
  (twoRowKernelH0Equiv R d).trans (twoRowH0MiddleStateEquiv R d hd)

/-- With zero second twist, original state degree one means a negative first twist. -/
theorem two_cohomologyDegree_one_zero_second_iff (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    cohomologyDegree d = 1 ↔ 0 < d 0 := by
  by_cases h0 : d 0 = 0 <;>
    simp [cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ,hd,h0,Nat.pos_iff_ne_zero]

/-- Original first-factor Laurent gaps are exactly the original degree-one states with zero second twist. -/
noncomputable def twoBaseMiddleIndexEquiv (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    Fin (d 0-1) ≃ {κ : HBasis d // (cohomologyDegree d : ℤ) = 1} := by
  by_cases h0 : 0 < d 0
  · let e0 : Fin (d 0-1) ≃ Fin (phi (d 0)) := finCongr (phi_of_pos h0).symm
    let e1 : Fin 1 ≃ Fin (phi (d 1)) := finCongr (by simp [hd])
    have he : (cohomologyDegree d : ℤ) = 1 := by
      exact_mod_cast (two_cohomologyDegree_one_zero_second_iff d hd).mpr h0
    exact
      { toFun := fun k => ⟨(piFinTwoEquiv fun v => Fin (phi (d v))).symm (e0 k,e1 0),he⟩
        invFun := fun κ => e0.symm (κ.val 0)
        left_inv := fun k => e0.symm_apply_apply k
        right_inv := fun κ => by
          apply Subtype.ext
          apply (piFinTwoEquiv fun v => Fin (phi (d v))).injective
          apply Prod.ext
          · exact e0.apply_symm_apply (κ.val 0)
          · apply e1.symm.injective
            change e1.symm (e1 0) = e1.symm (κ.val 1)
            rw [Equiv.symm_apply_apply]
            exact Subsingleton.elim _ _ }
  · have hz : d 0 = 0 := by omega
    letI : IsEmpty (Fin (d 0-1)) := by rw [hz]; change IsEmpty (Fin 0); infer_instance
    letI : IsEmpty {κ : HBasis d // (cohomologyDegree d : ℤ) = 1} := by
      refine ⟨fun κ => h0 ?_⟩
      apply (two_cohomologyDegree_one_zero_second_iff d hd).mp
      exact_mod_cast κ.property
    exact Equiv.equivOfIsEmpty _ _

/-- Original first-factor Laurent states form exactly the original degree-one state piece with zero second twist. -/
noncomputable def twoBaseH1MiddleStateEquiv (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    CechLine.H1 R (d 0) ≃ₗ[R] twoMiddleStatePiece R d :=
  (Finsupp.mapDomain.linearEquiv R R (twoBaseMiddleIndexEquiv d hd)).trans
    (supportedEquivFinsupp (R := R) (M := R) _).symm

end BPFixedPoints.CechProduct
