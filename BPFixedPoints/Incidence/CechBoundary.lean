import BPFixedPoints.Incidence.CechProductSign
import BPFixedPoints.Incidence.CechProductDegree

/-!
# Explicit boundary from Čech degree zero to one

The boundary of a degree-zero chart monomial sums its restrictions to adjacent
overlap faces. Right-chart restrictions have positive sign and left-chart
restrictions negative sign.
-/

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

def vertexChartBasis (b : Bool) (k : ℕ) : Basis :=
  if b then Sum.inr (Sum.inl k) else Sum.inl k

def chartBasis {V : Type*} (σ : V → Bool) (k : V → ℕ) : V → Basis :=
  fun v => vertexChartBasis (σ v) (k v)

def restrictionExponent (d : ℕ) (b : Bool) (k : ℕ) : ℤ :=
  if b then -(d : ℤ) - k else k

def boundaryBasis {V : Type*} [DecidableEq V]
    (d : V → ℕ) (σ : V → Bool) (k : V → ℕ) (v : V) : V → Basis :=
  Function.update (chartBasis σ k) v
    (Sum.inr (Sum.inr (restrictionExponent (d v) (σ v) (k v))))

@[simp] theorem boundaryBasis_zero {n : ℕ}
    (d : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → Bool) (k : Fin (n + 1) → ℕ) :
    boundaryBasis d σ k 0 =
      Fin.cons (Sum.inr (Sum.inr (restrictionExponent (d 0) (σ 0) (k 0))))
        (chartBasis (Fin.tail σ) (Fin.tail k)) := by
  unfold boundaryBasis
  rw [← Fin.cons_self_tail (chartBasis σ k), Fin.update_cons_zero]
  rfl

@[simp] theorem boundaryBasis_succ {n : ℕ}
    (d : Fin (n + 1) → ℕ) (σ : Fin (n + 1) → Bool) (k : Fin (n + 1) → ℕ) (v : Fin n) :
    boundaryBasis d σ k v.succ =
      Fin.cons (vertexChartBasis (σ 0) (k 0))
        (boundaryBasis (Fin.tail d) (Fin.tail σ) (Fin.tail k) v) := by
  unfold boundaryBasis
  rw [← Fin.cons_self_tail (chartBasis σ k), ← Fin.cons_update]
  rfl

variable (R : Type*) [CommRing R]

@[simp] theorem lineFree_d_chart (d : ℕ) (b : Bool) (k : ℕ) (r : R) :
    (lineFree R d).d (single (vertexChartBasis b k) r) =
      single (Sum.inr (Sum.inr (restrictionExponent d b k))) (if b then r else -r) := by
  cases b <;> simp [vertexChartBasis, restrictionExponent, Finsupp.single_neg]

@[simp] theorem lineFree_sign_chart (d : ℕ) (b : Bool) (k : ℕ) (r : R) :
    (lineFree R d).sign (single (vertexChartBasis b k) r) =
      single (vertexChartBasis b k) r := by
  cases b <;> simp [vertexChartBasis]

theorem finProduct_d_chart_single (n : ℕ) (d : Fin n → ℕ)
    (σ : Fin n → Bool) (k : Fin n → ℕ) (r : R) :
    (finProduct R n d).d (single (chartBasis σ k) r) =
      ∑ v, single (boundaryBasis d σ k v) (if σ v then r else -r) := by
  induction n with
  | zero => simp [finProduct, empty]
  | succ n ih =>
    rw [finProduct, GradedContraction.congr_d_apply, consEquiv_symm_single]
    rw [tensor_d_apply, TensorProduct.map_tmul, TensorProduct.map_tmul]
    change consEquiv R (fun _ : Fin (n + 1) => Basis)
      (((lineFree R (d 0)).d (single (vertexChartBasis (σ 0) (k 0)) 1) ⊗ₜ[R]
          (1 : Module.End R (C R (Fin n))) (single (chartBasis (Fin.tail σ) (Fin.tail k)) r)) +
        ((lineFree R (d 0)).sign (single (vertexChartBasis (σ 0) (k 0)) 1) ⊗ₜ[R]
          (finProduct R n (Fin.tail d)).d (single (chartBasis (Fin.tail σ) (Fin.tail k)) r))) = _
    rw [
      lineFree_d_chart, lineFree_sign_chart, Module.End.one_apply, ih,
      map_add, consEquiv_single_tmul_single, TensorProduct.tmul_sum, map_sum]
    simp only [consEquiv_single_tmul_single, one_mul, Fin.sum_univ_succ,
      boundaryBasis_zero, boundaryBasis_succ, Fin.tail]
    congr 1
    cases σ 0 <;> simp

theorem chartBasis_arrowCongr {V W : Type*} (e : V ≃ W)
    (σ : W → Bool) (k : W → ℕ) :
    e.arrowCongr (Equiv.refl Basis) (chartBasis (fun v => σ (e v)) (fun v => k (e v))) =
      chartBasis σ k := by
  funext w
  simp [chartBasis]

theorem boundaryBasis_arrowCongr {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (d : W → ℕ) (σ : W → Bool) (k : W → ℕ) (v : V) :
    e.arrowCongr (Equiv.refl Basis)
      (boundaryBasis (fun i => d (e i)) (fun i => σ (e i)) (fun i => k (e i)) v) =
      boundaryBasis d σ k (e v) := by
  funext w
  by_cases hw : w = e v
  · subst w
    simp [boundaryBasis]
  · have hw' : e.symm w ≠ v := by intro h; exact hw (by simpa using congrArg e h)
    simp [boundaryBasis, Function.update_of_ne hw, Function.update_of_ne hw', chartBasis]

/-- The boundary of a degree-zero chart monomial is the difference of adjacent-chart restrictions. -/
theorem contraction_d_chart_single {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) (σ : V → Bool) (k : V → ℕ) (r : R) :
    (contraction R d).d (single (chartBasis σ k) r) =
      ∑ v, single (boundaryBasis d σ k v) (if σ v then r else -r) := by
  classical
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  change (Finsupp.mapDomain.linearEquiv R R eb)
    ((finProduct R (Fintype.card V) (fun i => d (e i))).d
      ((Finsupp.mapDomain.linearEquiv R R eb).symm (single (chartBasis σ k) r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain eb
    ((finProduct R (Fintype.card V) (fun i => d (e i))).d
      (mapDomain eb.symm (single (chartBasis σ k) r))) = _
  rw [mapDomain_single]
  have hc : eb.symm (chartBasis σ k) = chartBasis (fun i => σ (e i)) (fun i => k (e i)) := rfl
  rw [hc, finProduct_d_chart_single, Finsupp.mapDomain_finsetSum]
  simp only [mapDomain_single, eb, boundaryBasis_arrowCongr]
  exact Fintype.sum_equiv e _ _ (fun v => rfl)

end BPFixedPoints.CechProduct
