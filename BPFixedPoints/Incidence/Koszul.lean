import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Koszul differential indexed by finite sets

Represent exterior bases by finite subsets; prove contraction/insertion maps
and their anticommutation relations. Use the same signs in local incidence
Koszul complexes and the total Čech complex.
-/

namespace BPFixedPoints.Koszul

variable {E A : Type*} [LinearOrder E] [CommRing A]

/-- Free module combining all exterior degrees. -/
abbrev Space (E A : Type*) [DecidableEq E] [Zero A] := (Finset E) →₀ A

/-- Number of selected edges preceding e. -/
def index (S : Finset E) (e : E) : ℕ := (S.filter (· < e)).card

/-- Sign for removing e from an increasingly ordered exterior basis. -/
def sign (S : Finset E) (e : E) : A := (-1) ^ index S e

@[simp] theorem index_erase_self (S : Finset E) (e : E) :
    index (S.erase e) e = index S e := by
  unfold index
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp

@[simp] theorem index_insert_self (S : Finset E) (e : E) :
    index (insert e S) e = index S e := by
  simp [index, Finset.filter_insert]

theorem index_erase_of_le (S : Finset E) {e f : E} (h : f ≤ e) :
    index (S.erase e) f = index S f := by
  unfold index
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp [not_lt_of_ge h]

theorem index_erase_of_lt {S : Finset E} {e f : E} (he : e ∈ S) (h : e < f) :
    index (S.erase e) f + 1 = index S f := by
  unfold index
  rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨he, h⟩)]
  have : 0 < (S.filter (· < f)).card := Finset.card_pos.mpr ⟨e, by simp [he, h]⟩
  omega

theorem index_insert_of_le (S : Finset E) {e f : E} (h : f ≤ e) :
    index (Insert.insert e S) f = index S f := by
  simp [index, Finset.filter_insert, not_lt_of_ge h]

theorem index_insert_of_lt {S : Finset E} {e f : E} (he : e ∉ S) (h : e < f) :
    index (Insert.insert e S) f = index S f + 1 := by
  simp [index, Finset.filter_insert, h, he]

@[simp] theorem sign_erase_self (S : Finset E) (e : E) :
    sign (A := A) (S.erase e) e = sign S e := by simp [sign]

@[simp] theorem sign_insert_self (S : Finset E) (e : E) :
    sign (A := A) (insert e S) e = sign S e := by simp [sign]

@[simp] theorem sign_mul_self (S : Finset E) (e : E) :
    sign (A := A) S e * sign S e = 1 := by
  rw [sign, ← mul_pow]
  simp

theorem sign_erase_anticomm {S : Finset E} {e f : E}
    (he : e ∈ S) (hf : f ∈ S) (hef : e ≠ f) :
    sign (A := A) S e * sign (S.erase e) f =
      -(sign S f * sign (S.erase f) e) := by
  rcases lt_or_gt_of_ne hef with h | h
  · have h₁ := index_erase_of_lt he h
    have h₂ := index_erase_of_le S (le_of_lt h)
    unfold sign
    rw [← h₁, pow_succ, h₂]
    ring

  · have h₁ := index_erase_of_lt hf h
    have h₂ := index_erase_of_le S (le_of_lt h)
    unfold sign
    rw [← h₁, pow_succ, h₂]
    ring

theorem sign_insert_erase_anticomm {S : Finset E} {e f : E}
    (he : e ∉ S) (hf : f ∈ S) (hef : e ≠ f) :
    sign (A := A) S e * sign (Insert.insert e S) f =
      -(sign S f * sign (S.erase f) e) := by
  rcases lt_or_gt_of_ne hef with h | h
  · have h₁ := index_insert_of_lt he h
    have h₂ := index_erase_of_le S (le_of_lt h)
    unfold sign
    rw [h₁, pow_succ, h₂]
    ring
  · have h₁ := index_erase_of_lt hf h
    have h₂ := index_insert_of_le S (le_of_lt h)
    unfold sign
    rw [h₂, ← h₁, pow_succ]
    ring

/-- Left contraction: remove an edge. -/
noncomputable def erase (e : E) : Space E A →ₗ[A] Space E A :=
  Finsupp.linearCombination A fun S =>
    if e ∈ S then Finsupp.single (S.erase e) (sign S e) else 0

/-- Left exterior multiplication: add an edge. -/
noncomputable def insert (e : E) : Space E A →ₗ[A] Space E A :=
  Finsupp.linearCombination A fun S =>
    if e ∈ S then 0 else Finsupp.single (Insert.insert e S) (sign S e)

@[simp] theorem erase_single (e : E) (S : Finset E) (a : A) :
    erase e (Finsupp.single S a) =
      if e ∈ S then Finsupp.single (S.erase e) (sign S e * a) else 0 := by
  simp only [erase, Finsupp.linearCombination_single]
  split_ifs <;> simp [Finsupp.smul_single, mul_comm]

@[simp] theorem insert_single (e : E) (S : Finset E) (a : A) :
    insert e (Finsupp.single S a) =
      if e ∈ S then 0 else Finsupp.single (Insert.insert e S) (sign S e * a) := by
  simp only [insert, Finsupp.linearCombination_single]
  split_ifs <;> simp [Finsupp.smul_single, mul_comm]

@[simp] theorem erase_sq (e : E) :
    (erase e : Module.End A (Space E A)) * erase e = 0 := by
  apply Finsupp.lhom_ext
  intro S a
  simp only [Module.End.mul_apply, erase_single,
    LinearMap.zero_apply]
  split_ifs <;> simp [erase_single]

theorem erase_anticomm (e f : E) :
    (erase e : Module.End A (Space E A)) * erase f = -(erase f * erase e) := by
  by_cases hef : e = f
  · subst f; rw [erase_sq]; ext x S; simp
  apply Finsupp.lhom_ext
  intro S a
  simp only [Module.End.mul_apply, LinearMap.neg_apply, erase_single]
  by_cases he : e ∈ S <;> by_cases hf : f ∈ S
  · simp only [he, hf, ↓reduceIte, erase_single, Finset.mem_erase]
    rw [ite_eq_left ⟨hef, trivial⟩, ite_eq_left ⟨Ne.symm hef, trivial⟩]
    rw [Finset.erase_right_comm, ← Finsupp.single_neg, ← mul_assoc, ← mul_assoc]
    congr 1
    rw [mul_comm (sign (S.erase f) e) (sign S f),
      sign_erase_anticomm hf he (Ne.symm hef)]
    ring
  · simp [he, hf, erase_single]

  · simp [he, hf, erase_single]
  · simp [he, hf, erase_single]

theorem erase_insert_add_insert_erase (e f : E) :
    (erase e : Module.End A (Space E A)) * insert f + insert f * erase e =
      if e = f then 1 else 0 := by
  apply Finsupp.lhom_ext
  intro S a
  simp only [Module.End.mul_apply, LinearMap.add_apply]
  by_cases hef : e = f
  · subst f
    by_cases he : e ∈ S
    · simp [he, erase_single, insert_single, sign_mul_self, ← mul_assoc]
    · simp [he, erase_single, insert_single, sign_mul_self, ← mul_assoc]
  · by_cases he : e ∈ S <;> by_cases hf : f ∈ S
    · simp [he, hf, hef, Ne.symm hef, erase_single, insert_single]
    · simp only [he, hf, hef, Ne.symm hef, ↓reduceIte, erase_single, insert_single,
        Finset.mem_insert, Finset.mem_erase, false_or, true_and, and_true,
        not_false_eq_true, ↓reduceIte, LinearMap.zero_apply]
      simp only [and_false, ↓reduceIte]
      rw [Finset.erase_insert_of_ne (Ne.symm hef), ← Finsupp.single_add]
      congr 1
      have h := sign_insert_erase_anticomm (A := A) hf he (Ne.symm hef)
      rw [← mul_assoc, ← mul_assoc, mul_comm (sign (Insert.insert f S) e),
        mul_comm (sign (S.erase e) f), h]
      ring_nf
      simp
    · simp [he, hf, hef, Ne.symm hef, erase_single, insert_single]
    · simp [he, hf, hef, Ne.symm hef, erase_single, insert_single]

section Differential

variable [Fintype E]

/-- Koszul differential for a given sequence. -/
noncomputable def differential (f : E → A) : Module.End A (Space E A) :=
  ∑ e, f e • erase e

theorem differential_sq (f : E → A) :
    differential f * differential f = 0 := by
  have h : ∀ T : Finset E,
      (∑ e ∈ T, f e • (erase e : Module.End A (Space E A))) *
        (∑ e ∈ T, f e • erase e) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert e T he ih =>
      rw [Finset.sum_insert he]
      rw [add_mul, mul_add, mul_add, ih, add_zero]
      have hsq : (f e • (erase e : Module.End A (Space E A))) * (f e • erase e) = 0 := by
        rw [smul_mul_smul_comm, erase_sq, smul_zero]
      rw [hsq, zero_add]
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j hj
      rw [smul_mul_smul_comm, smul_mul_smul_comm, erase_anticomm]
      ext x S
      simp [mul_comm]
  exact h Finset.univ

@[simp] theorem differential_differential (f : E → A) (x : Space E A) :
    differential f (differential f x) = 0 := by
  exact LinearMap.congr_fun (differential_sq f) x

end Differential

end BPFixedPoints.Koszul
