import BPFixedPoints.Incidence.CechCubicalCellMaps
import BPFixedPoints.Incidence.CechProductDegree

/-! # Original overlap degrees and positive cell primitives

The existing tensor degree machinery is applied with negative overlap degree,
so its cochain grading describes the original homological cell boundary.
Primitives are the specified original tensor prism, not arbitrary preimages.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type*) [CommRing R]

/-- Negative homological dimension, for the existing cochain degree API. -/
def intervalCellDegree (k : Fin 3) : ℤ := if k = 2 then -1 else 0

/-- Original overlap count, with the sign required by the existing degree API. -/
def cellDegree {V : Type*} [Fintype V] (p : V → Fin 3) : ℤ := -(faceDegree p : ℤ)

theorem intervalCellDegree_eq_neg (k : Fin 3) :
    intervalCellDegree k = -((if k = 2 then 1 else 0 : ℕ) : ℤ) := by
  fin_cases k <;> simp [intervalCellDegree]

/-- The actual interval boundary lowers original overlap dimension by one. -/
theorem interval_d_degree (b : Fin 2) :
    HasDegree intervalCellDegree intervalCellDegree 1 (interval R b).d := by
  apply HasDegree.of_single
  intro k r
  fin_cases k <;> dsimp only
  · rw [interval_d_single,ite_eq_right (by decide)]
    exact Submodule.zero_mem _
  · rw [interval_d_single,ite_eq_right (by decide)]
    exact Submodule.zero_mem _
  · rw [interval_d_single,ite_eq_left (by decide)]
    exact Submodule.sub_mem _ (single_mem_supported R r (by decide))
      (single_mem_supported R r (by decide))

/-- The specified interval prism raises original overlap dimension by one. -/
theorem interval_h_degree (b : Fin 2) :
    HasDegree intervalCellDegree intervalCellDegree (-1) (interval R b).h := by
  apply HasDegree.of_single
  intro k r
  fin_cases k <;> dsimp only
  · rw [interval_h_single]
    exact single_mem_supported R _ (by decide)
  · rw [interval_h_single]
    exact single_mem_supported R _ (by decide)
  · have hz : prismCoefficient R b 2 = 0 := by fin_cases b <;> simp [prismCoefficient]
    rw [interval_h_single]
    change single (2 : Fin 3) (prismCoefficient R b 2*r) ∈
      supported R R {q | intervalCellDegree q = (-2 : ℤ)}
    rw [hz,zero_mul,Finsupp.single_zero]
    exact Submodule.zero_mem _

/-- The original base endpoint is in original overlap dimension zero. -/
theorem interval_i_degree (b : Fin 2) :
    HasDegree (fun _ : Fin 1 => (0 : ℤ)) intervalCellDegree 0 (interval R b).i := by
  apply HasDegree.of_single
  intro k r
  rw [interval_i_single]
  apply single_mem_supported R r
  fin_cases b <;> decide

/-- The original augmentation preserves degree and kills all positive dimensions. -/
theorem interval_p_degree (b : Fin 2) :
    HasDegree intervalCellDegree (fun _ : Fin 1 => (0 : ℤ)) 0 (interval R b).p := by
  apply HasDegree.of_single
  intro k r
  fin_cases k <;> dsimp only
  · rw [interval_p_single,ite_eq_right (by decide)]
    exact single_mem_supported R r (by decide)
  · rw [interval_p_single,ite_eq_right (by decide)]
    exact single_mem_supported R r (by decide)
  · rw [interval_p_single,ite_eq_left (by decide)]
    exact Submodule.zero_mem _

/-- The original parity retains each original cell's degree. -/
theorem interval_sign_degree (b : Fin 2) :
    HasDegree intervalCellDegree intervalCellDegree 0 (interval R b).sign := by
  apply HasDegree.of_single
  intro k r
  rw [interval_sign_single]
  exact Submodule.smul_mem _ _ (single_mem_supported R r (by simp))

/-- All degree conditions of the original interval contraction. -/
theorem interval_degrees (b : Fin 2) :
    ContractionDegrees R (interval R b) intervalCellDegree (fun _ => 0) :=
  ⟨interval_d_degree R b,interval_h_degree R b,interval_i_degree R b,
    interval_p_degree R b,interval_sign_degree R b⟩

/-- Existing finite tensor degree preservation, applied to the original homological cells. -/
theorem finContraction_degrees (n : ℕ) (b : Fin n → Fin 2) :
    ContractionDegrees R (finContraction R n b) cellDegree (fun _ => 0) := by
  induction n with
  | zero =>
    have hs : (cellDegree : (Fin 0 → Fin 3) → ℤ) = fun _ => 0 := by
      funext p
      simp [cellDegree,faceDegree]
    simp only [finContraction,hs]
    constructor
    · exact HasDegree.zero _ _ _
    · exact HasDegree.zero _ _ _
    · exact HasDegree.constant (empty R).i 0
    · exact HasDegree.constant (empty R).p 0
    · exact HasDegree.id _
  | succ n ih =>
    rw [finContraction]
    exact (interval_degrees R (b 0)).tensor_congr (ih (Fin.tail b))
      (Fin.consEquiv fun _ : Fin (n+1) => Fin 3) (Fin.consEquiv fun _ : Fin (n+1) => Fin 1)
      cellDegree (fun _ => 0)
      (fun ⟨k,p⟩ => by
        change -(faceDegree (Fin.cons k p) : ℤ) = intervalCellDegree k+cellDegree p
        rw [faceDegree_cons,Nat.cast_add,neg_add,← intervalCellDegree_eq_neg]
        rfl)
      (fun _ => by simp)

/-- All original degree conditions retain precisely the original finite enumeration. -/
theorem contraction_degrees {V : Type*} [Fintype V] (b : V → Fin 2) :
    ContractionDegrees R (contraction R b) cellDegree (fun _ => 0) := by
  classical
  let e := (Fintype.equivFin V).symm
  exact (finContraction_degrees R (Fintype.card V) (fun i => b (e i))).congr
    (e.arrowCongr (Equiv.refl (Fin 3))) (e.arrowCongr (Equiv.refl (Fin 1))) cellDegree (fun _ => 0)
    (fun p => congrArg (fun n : ℕ => -(n : ℤ)) (faceDegree_arrowCongr e p)) (fun _ => rfl)

/-- The original overlap dimension never exceeds the original number of coordinates. -/
theorem faceDegree_le_card {V : Type*} [Fintype V] (p : V → Fin 3) : faceDegree p ≤ Fintype.card V := by
  calc
    faceDegree p ≤ ∑ _ : V, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    _ = Fintype.card V := by simp

/-- Every positive homogeneous original cell cycle has its specified prism primitive in the next original degree. -/
theorem contraction_positive_primitive {V : Type*} [Fintype V] (b : V → Fin 2)
    (n : ℕ) (hn : 0 < n) (x : Cells R V)
    (hx : x ∈ supported R R {p | cellDegree p = -(n : ℤ)})
    (hd : (contraction R b).d x = 0) :
    (contraction R b).h x ∈ supported R R {p | cellDegree p = -((n+1 : ℕ) : ℤ)} ∧
      (contraction R b).d ((contraction R b).h x) = x := by
  constructor
  · have he : -(n : ℤ)+(-1) = -((n+1 : ℕ) : ℤ) := by push_cast; ring
    simpa only [he] using (contraction_degrees R b).h (-(n : ℤ)) x hx
  · have hp : (contraction R b).p x = 0 :=
      (contraction_degrees R b).p.eq_zero_of_const hx (by omega)
    have he := LinearMap.congr_fun (contraction R b).homotopy x
    simpa only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.comp_apply,
      Module.End.one_apply,hd,hp,map_zero,add_zero] using he

end BPFixedPoints.CechCubicalCell
