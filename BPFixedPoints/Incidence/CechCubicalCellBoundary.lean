import BPFixedPoints.Incidence.CechCubicalCellProduct
import BPFixedPoints.Incidence.CechCubicalFaceDifferential

/-! # The cell boundary retains the original cubical faces and prefix signs

The boundary lowers overlap degree. Its coefficient is the coefficient of
the original native restriction differential in the opposite direction.
The same enumeration as the original coefficient complex is retained.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type*) [CommRing R]

/-- Original overlap prefix in the ordered tensor coordinates. -/
def finPrefix {n : ℕ} (p : Fin n → Fin 3) (v : Fin n) : ℕ :=
  ∑ w, if w < v then (if p w = 2 then 1 else 0) else 0

@[simp] theorem finPrefix_zero {n : ℕ} (p : Fin (n+1) → Fin 3) : finPrefix p 0 = 0 := by
  simp [finPrefix]

@[simp] theorem finPrefix_succ {n : ℕ} (p : Fin (n+1) → Fin 3) (v : Fin n) :
    finPrefix p v.succ = (if p 0 = 2 then 1 else 0)+finPrefix (Fin.tail p) v := by
  simp [finPrefix,Fin.sum_univ_succ,Fin.tail]

private theorem update_zero {n : ℕ} (p : Fin (n+1) → Fin 3) (k : Fin 3) :
    Function.update p 0 k = Fin.cons k (Fin.tail p) := by
  rw [← Fin.cons_self_tail p,Fin.update_cons_zero]
  rfl

private theorem update_succ {n : ℕ} (p : Fin (n+1) → Fin 3) (v : Fin n) (k : Fin 3) :
    Function.update p v.succ k = Fin.cons (p 0) (Function.update (Fin.tail p) v k) := by
  rw [← Fin.cons_self_tail p,← Fin.cons_update]
  rfl

/-- A uniform endpoint formula, with zero weight for non-overlap inputs. -/
theorem interval_d_single_uniform (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).d (single k r) =
      single 0 ((if k = 2 then (1 : R) else 0)*r) -
        single 1 ((if k = 2 then (1 : R) else 0)*r) := by
  fin_cases k <;> simp [interval_d_single]

/-- The actual ordered cell differential is the original signed sum of endpoint faces. -/
theorem finContraction_d_single (n : ℕ) (b : Fin n → Fin 2) (p : Fin n → Fin 3) (r : R) :
    (finContraction R n b).d (single p r) =
      ∑ v, (single (Function.update p v 0)
        (((-1 : R)^finPrefix p v)*((if p v = 2 then 1 else 0)*r)) -
        single (Function.update p v 1)
          (((-1 : R)^finPrefix p v)*((if p v = 2 then 1 else 0)*r))) := by
  induction n with
  | zero => simp [finContraction,empty]
  | succ n ih =>
    rw [finContraction,GradedContraction.congr_d_apply,consEquiv_symm_single,
      tensor_d_apply,TensorProduct.map_tmul,TensorProduct.map_tmul,
      interval_d_single_uniform,interval_sign_single_pow,Module.End.one_apply,ih]
    simp only [TensorProduct.sub_tmul,← TensorProduct.smul_tmul',TensorProduct.tmul_sum,
      TensorProduct.tmul_sub,map_add,map_sub,map_sum,map_smul,consEquiv_single_tmul_single,
      mul_one,one_mul,Fin.sum_univ_succ,finPrefix_zero,pow_zero,
      update_zero,update_succ,finPrefix_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    simp only [smul_sub,Finsupp.smul_single,smul_eq_mul,pow_add,mul_assoc]
    rfl

private theorem prefix_enumeration {V : Type} [Fintype V] (p : V → Fin 3)
    (j : Fin (Fintype.card V)) :
    finPrefix (fun i => p ((Fintype.equivFin V).symm i)) j =
      faceBoundaryPrefix p ((Fintype.equivFin V).symm j) := by
  unfold finPrefix faceBoundaryPrefix
  apply Fintype.sum_equiv (Fintype.equivFin V).symm
  intro i
  simp

private theorem update_enumeration {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 3) (j : Fin (Fintype.card V)) (k : Fin 3) :
    ((Fintype.equivFin V).symm.arrowCongr (Equiv.refl (Fin 3)))
      (Function.update (fun i => p ((Fintype.equivFin V).symm i)) j k) =
      Function.update p ((Fintype.equivFin V).symm j) k := by
  funext v
  by_cases hv : v = (Fintype.equivFin V).symm j
  · subst v
    simp
  · have hj : Fintype.equivFin V v ≠ j := by
      intro h
      exact hv (by simpa using congrArg (Fintype.equivFin V).symm h)
    simp [Function.update_of_ne hv,Function.update_of_ne hj]

/-- The labelled cell boundary uses precisely the original labelled face prefix and endpoint orientations. -/
theorem contraction_d_single {V : Type} [Fintype V] [DecidableEq V]
    (b : V → Fin 2) (p : V → Fin 3) (r : R) :
    (contraction R b).d (single p r) =
      ∑ v, (single (Function.update p v 0)
        (((-1 : R)^faceBoundaryPrefix p v)*((if p v = 2 then 1 else 0)*r)) -
        single (Function.update p v 1)
          (((-1 : R)^faceBoundaryPrefix p v)*((if p v = 2 then 1 else 0)*r))) := by
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  change (Finsupp.mapDomain.linearEquiv R R ep)
    ((finContraction R (Fintype.card V) (fun i => b (e i))).d
      ((Finsupp.mapDomain.linearEquiv R R ep).symm (single p r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain ep ((finContraction R (Fintype.card V) (fun i => b (e i))).d
    (mapDomain ep.symm (single p r))) = _
  rw [mapDomain_single,finContraction_d_single,Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_sub,mapDomain_single]
  apply Fintype.sum_equiv e
  intro j
  rw [show ep.symm p = (fun i => p (e i)) from rfl]
  rw [update_enumeration p j 0,update_enumeration p j 1,prefix_enumeration p j]

/-- Only the prism depends on the chosen base vertex; the original boundary does not. -/
theorem contraction_d_eq {V : Type} [Fintype V] [DecidableEq V] (b c : V → Fin 2) :
    (contraction R b).d = (contraction R c).d := by
  apply Finsupp.lhom_ext
  intro p r
  rw [contraction_d_single,contraction_d_single]

/-- Replacing the active coordinate leaves precisely the original preceding-overlap prefix. -/
theorem faceBoundaryPrefix_update {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 3) (v : V) (k : Fin 3) :
    faceBoundaryPrefix (Function.update p v k) v = faceBoundaryPrefix p v := by
  unfold faceBoundaryPrefix
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = v
  · subst w
    simp
  · simp only [Function.update_of_ne hw]

/-- The native restriction coefficient is exactly the original transposed cell-boundary coefficient. -/
theorem native_endpoint_boundary_sign (S : Type) [CommRing S]
    {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 3) (v : V) (k : Fin 2) :
    -faceBoundarySign S (Function.update p v k.castSucc) v =
      (-1 : S)^faceBoundaryPrefix p v * (if k = 0 then 1 else -1) := by
  fin_cases k <;> simp [faceBoundarySign,faceBoundaryPrefix_update]

/-- The original native face step returns to precisely the original source overlap face. -/
theorem endpoint_faceStep {V : Type} [DecidableEq V]
    (p : V → Fin 3) (v : V) (hp : p v = 2) (k : Fin 2) :
    faceStep (Function.update p v k.castSucc) v = p := by
  rw [faceStep,Function.update_idem,← hp,Function.update_eq_self]

end BPFixedPoints.CechCubicalCell
