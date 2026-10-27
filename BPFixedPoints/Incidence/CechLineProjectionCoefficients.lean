import BPFixedPoints.Incidence.CechProductDegree

/-! # The original one-factor state projections read the original monomial coefficients -/

namespace BPFixedPoints.CechLine
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]

/-- The original degree-one projection reads exactly the original Laurent gap coefficient. -/
theorem projectionOne_apply (d : ℕ) (x : C1 R) (k : H1Index d) :
    projectionOne R d x k = x (-(k : ℤ)-1) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; rfl
  | add x y hx hy => rw [map_add,Finsupp.add_apply,hx,hy]; rfl
  | single z r =>
    by_cases hz : z = -(k : ℤ)-1
    · subst z
      calc
        _ = projectionOne R d (inclusionOne R d (single k r)) k := by rw [inclusionOne_single]
        _ = single k r k := congrArg (fun f : H1 R d => f k)
          (LinearMap.congr_fun (projectionOne_inclusionOne R d) (single k r))
        _ = r := Finsupp.single_eq_same
        _ = single (-(k : ℤ)-1) r (-(k : ℤ)-1) := Finsupp.single_eq_same.symm
    · rw [Finsupp.single_eq_of_ne (Ne.symm hz)]
      simp only [projectionOne,Finsupp.lsum_single]
      split_ifs with hg
      · change Finsupp.single _ r k = 0
        apply Finsupp.single_eq_of_ne
        intro he
        have hh := congrArg Fin.val he
        change k.val = (-z-1).toNat at hh
        have hk := k.isLt
        omega
      · rfl

/-- Every original degree-zero state reads the right chart's original constant coefficient. -/
theorem projectionZero_apply (d : ℕ) (x : C0 R) (k : H0Index d) :
    projectionZero R d x k = x.2 0 := by
  have hd : d = 0 := by
    by_contra hd
    have hk := k.isLt
    simp only [ite_eq_right hd] at hk
    omega
  subst d
  have hk : k = (⟨0,by decide⟩ : H0Index 0) := by
    apply Fin.ext
    change k.val = 0
    have h := k.isLt
    change k.val < 1 at h
    omega
  rw [hk,projectionZero_zero_apply]
  exact Finsupp.single_eq_same

end BPFixedPoints.CechLine

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]

/-- Precisely the original finite index equivalence used by the original one-factor state basis. -/
def lineStateIndexEquiv (d : ℕ) : CechLine.H0Index d ⊕ CechLine.H1Index d ≃ Fin (phi d) :=
  finSumFinEquiv.trans (finCongr (by cases d <;> simp [phi]))

/-- The original one-factor state basis reads its original zero- or one-degree component. -/
theorem lineHBasisEquiv_apply (d : ℕ) (x : LineH R d) (k : Fin (phi d)) :
    lineHBasisEquiv R d x k = match (lineStateIndexEquiv d).symm k with
      | Sum.inl j => x.1 j
      | Sum.inr j => x.2 j := by
  change mapDomain (lineStateIndexEquiv d) (x.1.sumElim x.2) k = _
  rw [mapDomain_equiv_apply]
  cases (lineStateIndexEquiv d).symm k <;> rfl

/-- The original chart or Laurent monomial read by an original one-factor state coordinate. -/
def lineProjectionMonomial (d : ℕ) (k : Fin (phi d)) : Basis :=
  match (lineStateIndexEquiv d).symm k with
  | Sum.inl _ => Sum.inr (Sum.inl 0)
  | Sum.inr j => Sum.inr (Sum.inr (-(j : ℤ)-1))

/-- The original one-factor projection reads exactly its specified original monomial coefficient. -/
theorem lineFree_p_coefficient (d : ℕ) (x : Basis →₀ R) (k : Fin (phi d)) :
    (lineFree R d).p x k = x (lineProjectionMonomial d k) := by
  change lineHBasisEquiv R d (lineP R d (lineBasisEquiv R x)) k = _
  rw [lineHBasisEquiv_apply]
  unfold lineProjectionMonomial
  cases (lineStateIndexEquiv d).symm k with
  | inl j =>
    change CechLine.projectionZero R d (lineBasisEquiv R x).1 j = _
    rw [CechLine.projectionZero_apply]
    rfl
  | inr j =>
    change CechLine.projectionOne R d (lineBasisEquiv R x).2 j = _
    rw [CechLine.projectionOne_apply]
    rfl

end BPFixedPoints.CechProduct
