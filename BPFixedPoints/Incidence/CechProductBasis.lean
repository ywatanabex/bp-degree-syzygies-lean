import BPFixedPoints.Incidence.CechProduct

/-!
# Monomial presentation of the product Čech complex

Relate the tensor construction to formulas in chart Laurent monomials.
-/

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

variable (R : Type*) [CommRing R]

@[simp] theorem lineBasisEquiv_left (k : ℕ) (r : R) :
    lineBasisEquiv R (single (Sum.inl k) r) = ((single k r, 0), 0) := by
  ext j <;> simp [lineBasisEquiv, LinearEquiv.prodAssoc, Finsupp.sumFinsuppLEquivProdFinsupp,
    Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]

@[simp] theorem lineBasisEquiv_right (k : ℕ) (r : R) :
    lineBasisEquiv R (single (Sum.inr (Sum.inl k)) r) = ((0, single k r), 0) := by
  ext j <;> simp [lineBasisEquiv, LinearEquiv.prodAssoc, Finsupp.sumFinsuppLEquivProdFinsupp,
    Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]

@[simp] theorem lineBasisEquiv_overlap (k : ℤ) (r : R) :
    lineBasisEquiv R (single (Sum.inr (Sum.inr k)) r) = ((0, 0), single k r) := by
  ext j <;> simp [lineBasisEquiv, LinearEquiv.prodAssoc, Finsupp.sumFinsuppLEquivProdFinsupp,
    Finsupp.sumFinsuppAddEquivProdFinsupp, Finsupp.sumFinsuppEquivProdFinsupp]

@[simp] theorem lineFree_d_left (d k : ℕ) (r : R) :
    (lineFree R d).d (single (Sum.inl k) r) =
      -single (Sum.inr (Sum.inr (k : ℤ))) r := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineD, CechLine.differential_left_single]
  rfl

@[simp] theorem lineFree_d_right (d k : ℕ) (r : R) :
    (lineFree R d).d (single (Sum.inr (Sum.inl k)) r) =
      single (Sum.inr (Sum.inr (-(d : ℤ) - k))) r := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineD, CechLine.differential_right_single]
  rfl

@[simp] theorem lineFree_d_overlap (d : ℕ) (k : ℤ) (r : R) :
    (lineFree R d).d (single (Sum.inr (Sum.inr k)) r) = 0 := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineD]
  exact map_zero (CechLine.differential R d)

@[simp] theorem lineFree_sign_left (d k : ℕ) (r : R) :
    (lineFree R d).sign (single (Sum.inl k) r) = single (Sum.inl k) r := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineSign]

@[simp] theorem lineFree_sign_right (d k : ℕ) (r : R) :
    (lineFree R d).sign (single (Sum.inr (Sum.inl k)) r) =
      single (Sum.inr (Sum.inl k)) r := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineSign]

@[simp] theorem lineFree_sign_overlap (d : ℕ) (k : ℤ) (r : R) :
    (lineFree R d).sign (single (Sum.inr (Sum.inr k)) r) =
      -single (Sum.inr (Sum.inr k)) r := by
  apply (lineBasisEquiv R).injective
  simp [lineFree, line, lineSign]

@[simp] theorem consEquiv_single_tmul_single {n : ℕ} (B : Fin (n + 1) → Type*)
    (x : B 0) (f : (i : Fin n) → B i.succ) (r s : R) :
    consEquiv R B (single x r ⊗ₜ[R] single f s) = single (Fin.cons x f) (r * s) := by
  change mapDomain (Fin.consEquiv B)
    (finsuppTensorFinsupp' R _ _ (single x r ⊗ₜ[R] single f s)) = _
  rw [finsuppTensorFinsupp'_single_tmul_single, mapDomain_single]
  rfl

theorem consEquiv_symm_single {n : ℕ} (B : Fin (n + 1) → Type*)
    (f : (i : Fin (n + 1)) → B i) (r : R) :
    (consEquiv R B).symm (single f r) = single (f 0) 1 ⊗ₜ[R] single (Fin.tail f) r := by
  apply (consEquiv R B).injective
  simp

/-- One-vertex Čech degree. -/
def lineDegree : Basis → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr _) => 1

/-- Product Čech degree counts the vertices in overlap terms. -/
def cechDegree {V : Type*} [Fintype V] (b : V → Basis) : ℕ :=
  ∑ v, lineDegree (b v)

@[simp] theorem cechDegree_cons {n : ℕ} (x : Basis) (b : Fin n → Basis) :
    cechDegree (Fin.cons x b) = lineDegree x + cechDegree b := by
  simp [cechDegree, Fin.sum_univ_succ]

/-- One-vertex homogeneous monomial action, where a,b are the two homogeneous-coordinate exponents. -/
def shift (a b : ℕ) : Basis → Basis
  | Sum.inl k => Sum.inl (k + a)
  | Sum.inr (Sum.inl k) => Sum.inr (Sum.inl (k + b))
  | Sum.inr (Sum.inr k) => Sum.inr (Sum.inr (k + a))

@[simp] theorem lineDegree_shift (a b : ℕ) (x : Basis) :
    lineDegree (shift a b x) = lineDegree x := by
  rcases x with k | k | k <;> rfl

@[simp] theorem shift_zero (x : Basis) : shift 0 0 x = x := by
  rcases x with k | k | k <;> simp [shift]

theorem shift_comp (a b a' b' : ℕ) (x : Basis) :
    shift a b (shift a' b' x) = shift (a + a') (b + b') x := by
  rcases x with k | k | k <;> simp [shift, add_assoc, add_comm, add_left_comm]

end BPFixedPoints.CechProduct
