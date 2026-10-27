import BPFixedPoints.Incidence.VertexProjectiveTwistRowH0

/-! # The original first-direction kernel on the original row H1 states -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- The original left first-coefficient map is the original one-factor polynomial inclusion. -/
theorem twoRowBaseRestriction_left (d : Fin 2 → ℕ) (x : TwoRowBase R 0) :
    AddMonoidAlgebra.coeffLinearEquiv R (twoRowBaseRestriction R d (b := 0) (c := 2) (Or.inr rfl) x) =
      CechLine.leftRestriction R (AddMonoidAlgebra.coeffLinearEquiv R x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [(twoRowBaseRestriction R d _).map_zero]
    change (0 : ℤ →₀ R) = CechLine.leftRestriction R (0 : ℕ →₀ R)
    exact (map_zero _).symm
  | add x y hx hy =>
    rw [(twoRowBaseRestriction R d _).map_add,(AddMonoidAlgebra.coeffLinearEquiv R).map_add,
      (AddMonoidAlgebra.coeffLinearEquiv R).map_add,(CechLine.leftRestriction R).map_add,hx,hy]
  | single m r =>
    rw [twoRowBaseRestriction_single]
    change single _ r = CechLine.leftRestriction R (single m r)
    simp [CechLine.leftRestriction]
    rfl

/-- The original right first-coefficient map is the original inverse-coordinate twist restriction. -/
theorem twoRowBaseRestriction_right (d : Fin 2 → ℕ) (x : TwoRowBase R 1) :
    AddMonoidAlgebra.coeffLinearEquiv R (twoRowBaseRestriction R d (b := 1) (c := 2) (Or.inr rfl) x) =
      CechLine.rightRestriction R (d 0) (AddMonoidAlgebra.coeffLinearEquiv R x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [(twoRowBaseRestriction R d _).map_zero]
    change (0 : ℤ →₀ R) = CechLine.rightRestriction R (d 0) (0 : ℕ →₀ R)
    exact (map_zero _).symm
  | add x y hx hy =>
    rw [(twoRowBaseRestriction R d _).map_add,(AddMonoidAlgebra.coeffLinearEquiv R).map_add,
      (AddMonoidAlgebra.coeffLinearEquiv R).map_add,(CechLine.rightRestriction R (d 0)).map_add,hx,hy]
  | single m r =>
    change ℕ at m
    rw [twoRowBaseRestriction_single]
    change single _ r = CechLine.rightRestriction R (d 0) (single m r)
    simp only [CechLine.rightRestriction,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    congr 1
    simp [twoRowFirstExponent,refinementCoordinate,exponentToInt,exponentFromInt]
    change -(m : ℤ) + -(d 0 : ℤ) = _
    ring

/-- The original first-direction difference on the original row H1 states. -/
noncomputable def twoRowStateDifference (d : Fin 2 → ℕ) :
    (CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1)) →ₗ[R]
      CechLine.H1 (TwoRowBase R 2) (d 1) :=
  (twoRowStateRestriction R d (b := 0) (c := 2) (Or.inr rfl)).comp (LinearMap.fst R _ _) -
    (twoRowStateRestriction R d (b := 1) (c := 2) (Or.inr rfl)).comp (LinearMap.snd R _ _)

/-- Each original gap sees precisely the original first-factor matching equation. -/
theorem twoRowStateDifference_apply_gap (d : Fin 2 → ℕ)
    (x : CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1))
    (k : Fin (d 1-1)) :
    AddMonoidAlgebra.coeffLinearEquiv R (twoRowStateDifference R d x k) =
      -CechLine.differential R (d 0)
        (AddMonoidAlgebra.coeffLinearEquiv R (x.1 k),AddMonoidAlgebra.coeffLinearEquiv R (x.2 k)) := by
  change AddMonoidAlgebra.coeffLinearEquiv R ((twoRowStateRestriction R d _ x.1) k -
    (twoRowStateRestriction R d _ x.2) k) = _
  rw [twoRowStateRestriction_pointwise,twoRowStateRestriction_pointwise]
  rw [map_sub]
  change AddMonoidAlgebra.coeffLinearEquiv R (twoRowBaseRestriction R d _ (x.1 k)) -
    AddMonoidAlgebra.coeffLinearEquiv R (twoRowBaseRestriction R d _ (x.2 k)) = _
  rw [twoRowBaseRestriction_left,twoRowBaseRestriction_right]
  simp only [CechLine.differential,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.fst_apply,LinearMap.snd_apply]
  abel

/-- A strictly negative first twist annihilates the original row H1 matching kernel at every gap. -/
theorem twoRowStateDifference_eq_zero_iff_of_pos (d : Fin 2 → ℕ) (hd : 0 < d 0)
    (x : CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1)) :
    twoRowStateDifference R d x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hk (k : Fin (d 1-1)) : x.1 k = 0 ∧ x.2 k = 0 := by
      have he := twoRowStateDifference_apply_gap R d x k
      rw [hx,Finsupp.zero_apply,LinearEquiv.map_zero] at he
      let z : CechLine.C0 R :=
        (AddMonoidAlgebra.coeffLinearEquiv R (x.1 k),AddMonoidAlgebra.coeffLinearEquiv R (x.2 k))
      have hz : CechLine.differential R (d 0) z = 0 := neg_eq_zero.mp he.symm
      have hp : CechLine.projectionZero R (d 0) z = 0 := by
        rw [CechLine.projectionZero_of_ne_zero R (d 0) (Nat.ne_of_gt hd),LinearMap.zero_apply]
      have hc := LinearMap.congr_fun (CechLine.homotopy_differential R (d 0)) z
      change CechLine.homotopy R (d 0) (CechLine.differential R (d 0) z) =
        z - CechLine.inclusionZero R (d 0) (CechLine.projectionZero R (d 0) z) at hc
      rw [hz,hp,map_zero,map_zero,sub_zero] at hc
      have hf := congrArg Prod.fst hc
      have hg := congrArg Prod.snd hc
      exact ⟨(AddMonoidAlgebra.coeffLinearEquiv R).injective (hf.symm.trans (map_zero _).symm),
        (AddMonoidAlgebra.coeffLinearEquiv R).injective (hg.symm.trans (map_zero _).symm)⟩
    exact Prod.ext (Finsupp.ext fun k => (hk k).1) (Finsupp.ext fun k => (hk k).2)
  · rintro rfl
    exact map_zero _

end BPFixedPoints.CechProduct
