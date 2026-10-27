import BPFixedPoints.Incidence.CechProductBasis

/-! # Parity action on the product Čech basis -/

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

variable (R : Type*) [CommRing R]

theorem lineFree_sign_single (d : ℕ) (a : Basis) (r : R) :
    (lineFree R d).sign (single a r) = (-1 : R) ^ lineDegree a • single a r := by
  rcases a with k | k | k <;> simp [lineDegree]

theorem finProduct_sign_single (n : ℕ) (d : Fin n → ℕ) (b : Fin n → Basis) (r : R) :
    (finProduct R n d).sign (single b r) = (-1 : R) ^ cechDegree b • single b r := by
  induction n with
  | zero => simp [finProduct, empty, cechDegree]
  | succ n ih =>
    rw [finProduct, GradedContraction.congr_sign_apply, consEquiv_symm_single]
    change consEquiv R (fun _ => Basis)
      (TensorProduct.map (lineFree R (d 0)).sign (finProduct R n (Fin.tail d)).sign
        (single (b 0) 1 ⊗ₜ[R] single (Fin.tail b) r)) = _
    rw [TensorProduct.map_tmul, lineFree_sign_single, ih]
    rw [TensorProduct.smul_tmul_smul, map_smul,
      consEquiv_single_tmul_single, one_mul]
    have hdeg : cechDegree b = lineDegree (b 0) + cechDegree (Fin.tail b) := by
      simpa only [Fin.cons_self_tail] using cechDegree_cons (b 0) (Fin.tail b)
    rw [← pow_add, ← hdeg, Fin.cons_self_tail]

theorem cechDegree_arrowCongr {U V : Type*} [Fintype U] [Fintype V]
    (e : U ≃ V) (b : U → Basis) :
    cechDegree ((e.arrowCongr (Equiv.refl Basis)) b) = cechDegree b := by
  unfold cechDegree
  apply (Fintype.sum_equiv e _ _ ?_).symm
  intro u
  simp

theorem contraction_sign_single {V : Type*} [Fintype V]
    (d : V → ℕ) (b : V → Basis) (r : R) :
    (contraction R d).sign (single b r) = (-1 : R) ^ cechDegree b • single b r := by
  classical
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  change (Finsupp.mapDomain.linearEquiv R R eb)
    ((finProduct R (Fintype.card V) (fun i => d (e i))).sign
      ((Finsupp.mapDomain.linearEquiv R R eb).symm (single b r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change Finsupp.mapDomain eb
    ((finProduct R (Fintype.card V) (fun i => d (e i))).sign
      (Finsupp.mapDomain eb.symm (single b r))) = _
  rw [Finsupp.mapDomain_single, finProduct_sign_single, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_single, Equiv.apply_symm_apply]
  have hdeg : cechDegree (eb.symm b) = cechDegree b := by
    simpa only [← show e.arrowCongr (Equiv.refl Basis) = eb from rfl,
      Equiv.apply_symm_apply] using
      (cechDegree_arrowCongr e (eb.symm b)).symm
  rw [hdeg]

end BPFixedPoints.CechProduct
