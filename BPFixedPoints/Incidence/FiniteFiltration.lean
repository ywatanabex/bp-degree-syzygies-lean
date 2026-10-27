import BPFixedPoints.Incidence.Perturbation
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Tactic

/-! # Filtration-lowering operators and finite geometric series -/

namespace BPFixedPoints.IncidencePerturbation

section Ring

variable {A : Type*} [Ring A]

theorem swapped_mul_pow (a b : A) (n : ℕ) :
    (a * b) ^ (n + 1) = a * (b * a) ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; simp [mul_assoc]

theorem nilpotent_mul_swap (a b : A) (h : IsNilpotent (a * b)) :
    IsNilpotent (b * a) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [swapped_mul_pow, hn, mul_zero, zero_mul]⟩

/-- For a nilpotent operator, the inverse is a finite sum; formal power series are unnecessary. -/
theorem inverse_one_add_eq_sum (a : A) (n : ℕ) (ha : a ^ n = 0) :
    Ring.inverse (1 + a) = ∑ k ∈ Finset.range n, (-a) ^ k := by
  have hu : IsUnit (1 + a) := (show IsNilpotent a from ⟨n, ha⟩).isUnit_one_add
  apply hu.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ hu]
  have he := mul_neg_geom_sum (-a) n
  have hn : (-a) ^ n = 0 := by rw [neg_pow, ha, mul_zero]
  simpa only [sub_neg_eq_add, hn, sub_zero] using he.symm

theorem correction_eq_sum (δ h : A) (n : ℕ) (hn : (δ * h) ^ n = 0) :
    correction δ h = ∑ k ∈ Finset.range n, (-(δ * h)) ^ k * δ := by
  rw [correction, inverse_one_add_eq_sum _ _ hn, Finset.sum_mul]

end Ring

section Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem end_isUnit_one_add_of_pow_eq_zero (f : Module.End R M) (n : ℕ)
    (hf : f ^ n = 0) : IsUnit (1 + f) :=
  (show IsNilpotent f from ⟨n, hf⟩).isUnit_one_add

theorem end_isUnit_one_add_mul_swap (a b : Module.End R M) (n : ℕ)
    (hf : (a * b) ^ n = 0) : IsUnit (1 + b * a) :=
  (nilpotent_mul_swap a b ⟨n, hf⟩).isUnit_one_add

/-- An operator lowering a filtration with F 0=0 and F n=M is nilpotent of exponent n. -/
theorem pow_eq_zero_of_filtration (f : Module.End R M) (F : ℕ → Submodule R M)
    (n : ℕ) (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hdrop : ∀ k x, x ∈ F (k + 1) → f x ∈ F k) : f ^ n = 0 := by
  have hz : ∀ k x, x ∈ F k → (f ^ k) x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [hzero, Submodule.mem_bot] at hx
      simpa using hx
    | succ k ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply]
      exact ih (f x) (hdrop k x hx)
  ext x
  exact hz n x (by rw [htop]; trivial)

end Module

section FreeModule

variable {R B : Type*} [CommRing R]

/-- Nilpotence of a map strictly lowering basis height. -/
theorem nilpotent_of_lowers_basis (f : Module.End R (B →₀ R)) (height : B → ℕ)
    (n : ℕ) (hbound : ∀ b, height b < n)
    (hlower : ∀ b, f (Finsupp.single b 1) ∈
      Finsupp.supported R R {c | height c < height b}) : IsNilpotent f := by
  classical
  let F : ℕ → Submodule R (B →₀ R) :=
    fun k => Finsupp.supported R R {b | height b < k}
  refine ⟨n, pow_eq_zero_of_filtration f F n ?_ ?_ ?_⟩
  · simp [F]
  · have hs : {b | height b < n} = Set.univ := by ext b; simp [hbound b]
    simp [F, hs]
  · intro k x hx
    have hspan : F (k + 1) ≤ (F k).comap f := by
      change Finsupp.supported R R {b | height b < k + 1} ≤ (F k).comap f
      rw [Finsupp.supported_eq_span_single]
      apply Submodule.span_le.mpr
      rintro _ ⟨b, hb, rfl⟩
      change f (Finsupp.single b 1) ∈ F k
      apply Finsupp.supported_mono (s := {c | height c < height b}) ?_ (hlower b)
      intro c hc
      change height b < k + 1 at hb
      change height c < height b at hc
      change height c < k
      omega
    exact hspan hx

end FreeModule

section FinsuppModule

variable {R B M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Explicit nilpotence exponent for a map lowering state height in a finitely supported direct sum. -/
theorem pow_eq_zero_of_lowers_support (f : Module.End R (B →₀ M)) (height : B → ℕ)
    (n : ℕ) (hbound : ∀ b, height b < n)
    (hlower : ∀ b m, f (Finsupp.single b m) ∈
      Finsupp.supported M R {c | height c < height b}) : f ^ n = 0 := by
  classical
  let F : ℕ → Submodule R (B →₀ M) :=
    fun k => Finsupp.supported M R {b | height b < k}
  apply pow_eq_zero_of_filtration f F n
  · simp [F]
  · have hs : {b | height b < n} = Set.univ := by ext b; simp [hbound b]
    simp [F, hs]
  · intro k x hx
    rw [← x.sum_single, map_finsuppSum]
    apply Submodule.sum_mem
    intro b hb
    have hbk : height b < k + 1 := (Finsupp.mem_supported R x).mp hx hb
    apply Finsupp.supported_mono (s := {c | height c < height b}) ?_ (hlower b (x b))
    intro c hc
    change height c < k
    change height c < height b at hc
    omega

end FinsuppModule

end BPFixedPoints.IncidencePerturbation
