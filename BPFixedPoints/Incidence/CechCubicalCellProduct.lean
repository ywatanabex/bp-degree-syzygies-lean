import BPFixedPoints.Incidence.CechCubicalCellInterval
import BPFixedPoints.Incidence.CechProductBasis
import BPFixedPoints.Incidence.CechFaces

/-! # The specified finite tensor contraction of the original cubical cells

The original `Fintype.equivFin` enumeration is retained. The differential is
homological: an overlap edge is replaced by its oriented endpoint boundary.
Only the existing strong-contraction tensor construction is used.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable (R : Type*) [CommRing R]

/-- Free original cells, independently of a chosen base vertex. -/
abbrev Cells (V : Type*) := (V → Fin 3) →₀ R

/-- The single component of the original cube, including the empty cube. -/
abbrev Components (V : Type*) := (V → Fin 1) →₀ R

/-- The empty original cube is its single degree-zero component. -/
noncomputable def empty : GradedContraction R (Cells R (Fin 0)) (Components R (Fin 0)) := by
  let e : Cells R (Fin 0) ≃ₗ[R] Components R (Fin 0) :=
    Finsupp.mapDomain.linearEquiv R R (Equiv.ofUnique _ _)
  exact
    { d := 0, h := 0, i := e.symm.toLinearMap, p := e.toLinearMap, sign := 1, signH := 1
      d_sq := by simp
      h_sq := by simp
      d_i := by simp
      p_d := by simp
      p_i := by ext; simp
      h_i := by simp
      p_h := by simp
      homotopy := by ext; simp
      sign_sq := by simp
      signH_sq := by simp
      sign_d := by ext; simp
      sign_h := by ext; simp
      sign_i := by ext; simp
      p_sign := by ext; simp }

/-- Tensor the original interval contractions in the specified coordinate order. -/
noncomputable def finContraction : (n : ℕ) → (b : Fin n → Fin 2) →
    GradedContraction R (Cells R (Fin n)) (Components R (Fin n))
  | 0, _ => empty R
  | n+1, b =>
    ((interval R (b 0)).tensor (finContraction n (Fin.tail b))).congr
      (consEquiv R fun _ => Fin 3) (consEquiv R fun _ => Fin 1)

/-- Retain precisely the enumeration already used for the original coefficient complex. -/
noncomputable def contraction {V : Type*} [Fintype V] (b : V → Fin 2) :
    GradedContraction R (Cells R V) (Components R V) :=
  let e := (Fintype.equivFin V).symm
  (finContraction R (Fintype.card V) (fun i => b (e i))).congr
    (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 3))))
    (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 1))))

/-- The original endpoint and overlap parities on a single interval. -/
theorem interval_sign_single_pow (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).sign (single k r) = (-1 : R)^(if k = 2 then 1 else 0) • single k r := by
  fin_cases k <;> simp [interval_sign_single]

/-- Original overlap degree splits into the original head and tail degrees. -/
theorem faceDegree_cons {n : ℕ} (k : Fin 3) (p : Fin n → Fin 3) :
    faceDegree (Fin.cons k p) = (if k = 2 then 1 else 0) + faceDegree p := by
  simp only [faceDegree,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

/-- The actual tensor parity is exactly the degree of the original cubical face. -/
theorem finContraction_sign_single (n : ℕ) (b : Fin n → Fin 2) (p : Fin n → Fin 3) (r : R) :
    (finContraction R n b).sign (single p r) = (-1 : R)^faceDegree p • single p r := by
  induction n with
  | zero => simp [finContraction,empty,faceDegree]
  | succ n ih =>
    rw [finContraction,GradedContraction.congr_sign_apply,consEquiv_symm_single]
    change consEquiv R (fun _ => Fin 3)
      (TensorProduct.map (interval R (b 0)).sign (finContraction R n (Fin.tail b)).sign
        (single (p 0) 1 ⊗ₜ[R] single (Fin.tail p) r)) = _
    rw [TensorProduct.map_tmul,interval_sign_single_pow,ih,
      TensorProduct.smul_tmul_smul,map_smul,consEquiv_single_tmul_single,one_mul]
    have hdeg : faceDegree p = (if p 0 = 2 then 1 else 0)+faceDegree (Fin.tail p) := by
      simpa only [Fin.cons_self_tail] using faceDegree_cons (p 0) (Fin.tail p)
    rw [← pow_add,← hdeg,Fin.cons_self_tail]

/-- Reindexing retains the original count of overlap coordinates. -/
theorem faceDegree_arrowCongr {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (p : V → Fin 3) :
    faceDegree (e.arrowCongr (Equiv.refl (Fin 3)) p) = faceDegree p := by
  unfold faceDegree
  apply (Fintype.sum_equiv e _ _ ?_).symm
  intro v
  simp

/-- The specified labelled contraction has exactly the original face-degree parity. -/
theorem contraction_sign_single {V : Type*} [Fintype V]
    (b : V → Fin 2) (p : V → Fin 3) (r : R) :
    (contraction R b).sign (single p r) = (-1 : R)^faceDegree p • single p r := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  change (Finsupp.mapDomain.linearEquiv R R ep)
    ((finContraction R (Fintype.card V) (fun i => b (e i))).sign
      ((Finsupp.mapDomain.linearEquiv R R ep).symm (single p r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain ep ((finContraction R (Fintype.card V) (fun i => b (e i))).sign
    (mapDomain ep.symm (single p r))) = _
  rw [mapDomain_single,finContraction_sign_single,Finsupp.mapDomain_smul,
    mapDomain_single,Equiv.apply_symm_apply]
  have hdeg : faceDegree (ep.symm p) = faceDegree p := by
    simpa only [← show e.arrowCongr (Equiv.refl (Fin 3)) = ep from rfl,
      Equiv.apply_symm_apply] using (faceDegree_arrowCongr e (ep.symm p)).symm
  rw [hdeg]

end BPFixedPoints.CechCubicalCell
