import BPFixedPoints.Incidence.Koszul
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Local exactness of the independent polynomial-variable Koszul complex

Use divided differences and exterior insertion to turn positive-degree cycles
into boundaries. The coefficient ring is arbitrary, including Laurent rings
of Čech charts.
-/

namespace BPFixedPoints.Koszul

set_option linter.unusedSectionVars false

open MvPolynomial

variable {E σ R : Type*} [LinearOrder E] [DecidableEq σ] [CommRing R]

/-- Linear map dividing monomials by a variable once when divisible, and discarding the rest. -/
noncomputable def coeffDiv (i : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun p := p.divMonomial (Finsupp.single i 1)
  map_add' p q := add_divMonomial p q _
  map_smul' a p := by
    ext m
    simp [coeff_divMonomial]

/-- Linear projection setting one variable to zero. -/
noncomputable def coeffProj (i : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  LinearMap.id - (LinearMap.mulLeft R (X i)).comp (coeffDiv i)

@[simp] theorem coeffDiv_coeff (i : σ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (coeffDiv i p).coeff m = p.coeff (Finsupp.single i 1 + m) := rfl

@[simp] theorem coeffDiv_X_mul (i : σ) (p : MvPolynomial σ R) :
    coeffDiv i (X i * p) = p := X_mul_divMonomial i p

theorem coeffDiv_X_mul_of_ne {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R) :
    coeffDiv i (X j * p) = X j * coeffDiv i p := by
  ext m
  simp only [coeffDiv_coeff, coeff_X_mul', Finsupp.mem_support_iff,
    Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm hij), zero_add]
  split_ifs with hm
  · congr 1
    ext k
    by_cases hki : k = i
    · subst k; simp [Finsupp.single_eq_of_ne hij]
    · simp [Finsupp.single_eq_of_ne hki]
  · rfl

@[simp] theorem coeffProj_coeff (i : σ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (coeffProj i p).coeff m = if m i = 0 then p.coeff m else 0 := by
  change (p - X i * coeffDiv i p).coeff m = _
  rw [coeff_sub, coeff_X_mul']
  by_cases hm : m i = 0
  · simp [Finsupp.mem_support_iff, hm]
  · have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      omega
    simp [Finsupp.mem_support_iff, hm, coeffDiv_coeff,
      add_tsub_cancel_of_le hle]

theorem X_mul_coeffDiv_add_coeffProj (i : σ) (p : MvPolynomial σ R) :
    X i * coeffDiv i p + coeffProj i p = p := by
  change X i * coeffDiv i p + (p - X i * coeffDiv i p) = p
  abel

theorem coeffDiv_sign_mul (i : σ) (S : Finset E) (e : E) (p : MvPolynomial σ R) :
    coeffDiv i (sign S e * p) = sign S e * coeffDiv i p := by
  unfold sign
  generalize index S e = n
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ, mul_assoc] using congrArg Neg.neg ih

/-- One-variable Koszul homotopy. -/
noncomputable def homotopyOne (ι : E → σ) (e : E) :
    Space E (MvPolynomial σ R) →ₗ[R] Space E (MvPolynomial σ R) :=
  (insert e).restrictScalars R ∘ₗ Finsupp.mapRange.linearMap (coeffDiv (ι e))

/-- Set one variable to zero and kill terms containing its exterior factor. -/
noncomputable def projectOne (ι : E → σ) (e : E) :
    Space E (MvPolynomial σ R) →ₗ[R] Space E (MvPolynomial σ R) :=
  Finsupp.lsum R fun S => if e ∈ S then 0 else
    (Finsupp.lsingle S).comp (coeffProj (ι e))

@[simp] theorem homotopyOne_single (ι : E → σ) (e : E)
    (S : Finset E) (p : MvPolynomial σ R) :
    homotopyOne ι e (Finsupp.single S p) =
      if e ∈ S then 0 else
        Finsupp.single (Insert.insert e S) (sign S e * coeffDiv (ι e) p) := by
  simp [homotopyOne, Finsupp.mapRange.linearMap_apply]

@[simp] theorem projectOne_single (ι : E → σ) (e : E)
    (S : Finset E) (p : MvPolynomial σ R) :
    projectOne ι e (Finsupp.single S p) =
      if e ∈ S then 0 else Finsupp.single S (coeffProj (ι e) p) := by
  simp only [projectOne, Finsupp.lsum_single]
  split_ifs <;> simp

/-- One Koszul term with coefficient action by variable multiplication. -/
noncomputable def variableTerm (ι : E → σ) (e : E) :
    Module.End R (Space E (MvPolynomial σ R)) :=
  ((X (ι e) : MvPolynomial σ R) •
    (erase e : Module.End (MvPolynomial σ R) (Space E (MvPolynomial σ R)))).restrictScalars R

@[simp] theorem variableTerm_single (ι : E → σ) (e : E)
    (S : Finset E) (p : MvPolynomial σ R) :
    variableTerm ι e (Finsupp.single S p) =
      if e ∈ S then Finsupp.single (S.erase e) (sign S e * (X (ι e) * p)) else 0 := by
  simp only [variableTerm, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
    erase_single]
  split_ifs <;> simp [Finsupp.smul_single, mul_left_comm]

theorem variableTerm_homotopyOne (ι : E → σ) (hι : Function.Injective ι) (e j : E) :
    variableTerm (R := R) ι j * homotopyOne ι e + homotopyOne ι e * variableTerm ι j =
      if j = e then LinearMap.id - projectOne ι e else 0 := by
  apply Finsupp.lhom_ext
  intro S p
  simp only [LinearMap.add_apply, Module.End.mul_apply]
  by_cases hje : j = e
  · subst j
    by_cases he : e ∈ S
    · simp [he, variableTerm_single, homotopyOne_single, coeffDiv_sign_mul,
        coeffDiv_X_mul, ← mul_assoc]
      rw [mul_assoc (sign S e) (X (ι e)) p, coeffDiv_sign_mul, coeffDiv_X_mul,
        ← mul_assoc, sign_mul_self, one_mul]
    · simp only [he, ↓reduceIte, variableTerm_single, homotopyOne_single,
        Finset.mem_insert_self, Finset.erase_insert he, sign_insert_self,
        map_zero, add_zero, LinearMap.sub_apply, LinearMap.id_apply, projectOne_single]
      rw [← Finsupp.single_sub]
      congr 1
      rw [mul_left_comm (X (ι e)), ← mul_assoc, sign_mul_self, one_mul]
      exact (eq_sub_iff_add_eq.mpr (X_mul_coeffDiv_add_coeffProj (ι e) p))
  · by_cases he : e ∈ S <;> by_cases hj : j ∈ S
    · simp [he, hj, hje, Ne.symm hje, variableTerm_single, homotopyOne_single]
    · simp [he, hj, hje, Ne.symm hje, variableTerm_single, homotopyOne_single]
    · simp only [he, hj, hje, ↓reduceIte, variableTerm_single, homotopyOne_single,
        Finset.mem_insert, Finset.mem_erase]
      simp only [hje, Ne.symm hje, false_or, true_and, and_false,
        not_false_eq_true, ↓reduceIte, LinearMap.zero_apply]
      rw [Finset.erase_insert_of_ne (Ne.symm hje), ← Finsupp.single_add,
        Finsupp.single_eq_zero]
      rw [coeffDiv_sign_mul, coeffDiv_X_mul_of_ne (fun h => hje (hι h).symm)]
      have h := sign_insert_erase_anticomm (A := MvPolynomial σ R) he hj (Ne.symm hje)
      calc
        sign (Insert.insert e S) j * (X (ι j) * (sign S e * coeffDiv (ι e) p)) +
            sign (S.erase j) e * (sign S j * (X (ι j) * coeffDiv (ι e) p))
            = (sign S e * sign (Insert.insert e S) j +
                sign S j * sign (S.erase j) e) * (X (ι j) * coeffDiv (ι e) p) := by ring
        _ = 0 := by rw [h, neg_add_cancel, zero_mul]
    · simp [he, hj, hje, Ne.symm hje, variableTerm_single, homotopyOne_single]

section Fintype

variable [Fintype E]

/-- Regard the full Koszul differential as a map over the original coefficient ring. -/
noncomputable def variableDifferential (ι : E → σ) :
    Module.End R (Space E (MvPolynomial σ R)) :=
  (differential (fun e => X (ι e))).restrictScalars R

theorem variableDifferential_eq_sum (ι : E → σ) :
    variableDifferential (R := R) ι = ∑ e, variableTerm ι e := by
  apply LinearMap.ext
  intro x
  simp [variableDifferential, differential, variableTerm]

@[simp] theorem variableDifferential_sq (ι : E → σ) :
    variableDifferential (R := R) ι * variableDifferential ι = 0 := by
  apply LinearMap.ext
  intro x
  exact differential_differential (fun e => (X (ι e) : MvPolynomial σ R)) x

/-- One-variable contraction identity. -/
theorem variableDifferential_homotopyOne (ι : E → σ) (hι : Function.Injective ι) (e : E) :
    variableDifferential (R := R) ι * homotopyOne ι e + homotopyOne ι e * variableDifferential ι =
      LinearMap.id - projectOne (R := R) ι e := by
  rw [variableDifferential_eq_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simp_rw [variableTerm_homotopyOne ι hι e]
  simp

end Fintype

end BPFixedPoints.Koszul
