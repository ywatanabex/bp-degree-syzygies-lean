import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-! # Strict derivative of multivariate polynomial evaluation -/

section MvPolynomialDeriv

open MvPolynomial

variable {σ 𝕜 : Type*} [Fintype σ] [DecidableEq σ] [NontriviallyNormedField 𝕜]

/-- Gradient v↦sum_j ∂_j p(x) v_j. -/
noncomputable def MvPolynomial.gradCLM (p : MvPolynomial σ 𝕜) (x : σ → 𝕜) : (σ → 𝕜) →L[𝕜] 𝕜 :=
  ∑ j, eval x (pderiv j p) • ContinuousLinearMap.proj j

omit [DecidableEq σ] in
theorem MvPolynomial.gradCLM_apply (p : MvPolynomial σ 𝕜) (x v : σ → 𝕜) :
    p.gradCLM x v = ∑ j, eval x (pderiv j p) * v j := by
  simp [gradCLM]

/-- Strong derivative of polynomial evaluation. -/
theorem MvPolynomial.hasStrictFDerivAt_eval (p : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasStrictFDerivAt (fun z => eval z p) (p.gradCLM x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : (C a : MvPolynomial σ 𝕜).gradCLM x = 0 :=
      ContinuousLinearMap.ext fun v => by simp [gradCLM_apply]
    rw [h]; simpa only [eval_C] using hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : (p + q).gradCLM x = p.gradCLM x + q.gradCLM x :=
      ContinuousLinearMap.ext fun v => by
        simp [gradCLM_apply, add_mul, Finset.sum_add_distrib]
    rw [h, show (fun z => eval z (p + q)) = (fun z => eval z p) + (fun z => eval z q) by
      ext z; simp]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasStrictFDerivAt (fun z : σ → 𝕜 => z n)
        (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) n) x :=
      hasStrictFDerivAt_apply n x
    have h : (p * X n).gradCLM x =
        eval x p • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) n +
          x n • p.gradCLM x :=
      ContinuousLinearMap.ext fun v => by
        simp [gradCLM_apply, Derivation.leibniz, pderiv_X, Pi.single_apply, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_eq_single n (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
        rw [ite_eq_left rfl]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [h, show (fun z => eval z (p * X n)) = (fun z => eval z p) * (fun z => z n) by
      ext z; simp]
    exact hp.mul hX


end MvPolynomialDeriv
