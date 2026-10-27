import BPFixedPoints.Incidence.CechBoundary

/-! # The full tensor Cech differential as the original signed vertex boundary

The tensor contraction and its original enumeration are retained. This formula
covers every face degree, including input vertices already in overlap degree.
-/

namespace BPFixedPoints.CechProduct
open Finsupp
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

/-- The original one-vertex boundary monomial; an overlap contributes zero coefficient. -/
def boundaryStep (d : ℕ) : Basis → Basis
  | Sum.inl k => Sum.inr (Sum.inr (k : ℤ))
  | Sum.inr (Sum.inl k) => Sum.inr (Sum.inr (-(d : ℤ)-k))
  | Sum.inr (Sum.inr k) => Sum.inr (Sum.inr k)

/-- Original right-minus-left coefficients, with no contribution from overlap inputs. -/
def boundaryCoefficient (R : Type*) [CommRing R] : Basis → R
  | Sum.inl _ => -1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 0

/-- Prefix degree in the original ordered tensor factors. -/
def finBoundaryPrefix {n : ℕ} (b : Fin n → Basis) (v : Fin n) : ℕ :=
  ∑ w, if w < v then lineDegree (b w) else 0

@[simp] theorem finBoundaryPrefix_zero {n : ℕ} (b : Fin (n+1) → Basis) :
    finBoundaryPrefix b 0 = 0 := by simp [finBoundaryPrefix]

@[simp] theorem finBoundaryPrefix_succ {n : ℕ} (b : Fin (n+1) → Basis) (v : Fin n) :
    finBoundaryPrefix b v.succ = lineDegree (b 0) + finBoundaryPrefix (Fin.tail b) v := by
  simp [finBoundaryPrefix, Fin.sum_univ_succ, Fin.tail]

variable (R : Type*) [CommRing R]

/-- Uniform original one-factor differential formula on all three kinds of monomial. -/
theorem lineFree_d_single (d : ℕ) (b : Basis) (r : R) :
    (lineFree R d).d (single b r) = single (boundaryStep d b) (boundaryCoefficient R b * r) := by
  rcases b with k | k | k <;> simp [boundaryStep, boundaryCoefficient, Finsupp.single_neg]

private theorem update_zero {n : ℕ} (b : Fin (n+1) → Basis) (x : Basis) :
    Function.update b 0 x = Fin.cons x (Fin.tail b) := by
  rw [← Fin.cons_self_tail b, Fin.update_cons_zero]
  rfl

private theorem update_succ {n : ℕ} (b : Fin (n+1) → Basis) (v : Fin n) (x : Basis) :
    Function.update b v.succ x = Fin.cons (b 0) (Function.update (Fin.tail b) v x) := by
  rw [← Fin.cons_self_tail b, ← Fin.cons_update]
  rfl

/-- The actual ordered tensor differential is its full signed vertex sum. -/
theorem finProduct_d_single (n : ℕ) (d : Fin n → ℕ) (b : Fin n → Basis) (r : R) :
    (finProduct R n d).d (single b r) =
      ∑ v, single (Function.update b v (boundaryStep (d v) (b v)))
        (((-1 : R) ^ finBoundaryPrefix b v) * (boundaryCoefficient R (b v) * r)) := by
  induction n with
  | zero => simp [finProduct, empty]
  | succ n ih =>
    rw [finProduct, GradedContraction.congr_d_apply, consEquiv_symm_single,
      tensor_d_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      lineFree_d_single, lineFree_sign_single, Module.End.one_apply, ih,
      map_add, consEquiv_single_tmul_single, ← TensorProduct.smul_tmul',
      map_smul, TensorProduct.tmul_sum, map_sum]
    simp only [consEquiv_single_tmul_single, one_mul, Fin.sum_univ_succ,
      finBoundaryPrefix_zero, finBoundaryPrefix_succ, pow_zero, one_mul,
      update_zero, update_succ, Fin.tail]
    congr 1
    · congr 1
      ring
    · rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finsupp.smul_single, smul_eq_mul, pow_add]
      congr 1
      ring

/-- Prefix degree using precisely the enumeration of the original finite contraction. -/
noncomputable def boundaryPrefix {V : Type*} [Fintype V] (b : V → Basis) (v : V) : ℕ :=
  ∑ w, if Fintype.equivFin V w < Fintype.equivFin V v then lineDegree (b w) else 0

private theorem prefix_enumeration {V : Type*} [Fintype V] (b : V → Basis)
    (j : Fin (Fintype.card V)) :
    finBoundaryPrefix (fun i => b ((Fintype.equivFin V).symm i)) j =
      boundaryPrefix b ((Fintype.equivFin V).symm j) := by
  unfold finBoundaryPrefix boundaryPrefix
  apply (Fintype.sum_equiv (Fintype.equivFin V).symm _ _ ?_)
  intro i
  simp

private theorem update_enumeration {V : Type*} [Fintype V] [DecidableEq V]
    (b : V → Basis) (j : Fin (Fintype.card V)) (x : Basis) :
    ((Fintype.equivFin V).symm.arrowCongr (Equiv.refl Basis))
      (Function.update (fun i => b ((Fintype.equivFin V).symm i)) j x) =
      Function.update b ((Fintype.equivFin V).symm j) x := by
  funext v
  by_cases hv : v = (Fintype.equivFin V).symm j
  · subst v
    simp
  · have hj : Fintype.equivFin V v ≠ j := by
      intro h
      exact hv (by simpa using congrArg (Fintype.equivFin V).symm h)
    simp [Function.update_of_ne hv, Function.update_of_ne hj]

/-- The original labelled contraction has the same full boundary formula in its original enumeration. -/
theorem contraction_d_single {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (b : V → Basis) (r : R) :
    (contraction R d).d (single b r) =
      ∑ v, single (Function.update b v (boundaryStep (d v) (b v)))
        (((-1 : R) ^ boundaryPrefix b v) * (boundaryCoefficient R (b v) * r)) := by
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  change (Finsupp.mapDomain.linearEquiv R R eb)
    ((finProduct R (Fintype.card V) (fun i => d (e i))).d
      ((Finsupp.mapDomain.linearEquiv R R eb).symm (single b r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain eb ((finProduct R (Fintype.card V) (fun i => d (e i))).d
    (mapDomain eb.symm (single b r))) = _
  rw [mapDomain_single, finProduct_d_single, Finsupp.mapDomain_finsetSum]
  simp only [mapDomain_single]
  apply Fintype.sum_equiv e
  intro j
  rw [show eb.symm b = (fun i => b (e i)) from rfl]
  rw [update_enumeration b j, prefix_enumeration b j]

end BPFixedPoints.CechProduct
