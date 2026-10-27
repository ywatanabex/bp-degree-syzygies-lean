import BPFixedPoints.Incidence.KoszulPolynomial
import BPFixedPoints.Incidence.PerturbationNormalization
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Contraction of a polynomial-variable Koszul complex to its degree-zero quotient

Compose finitely many one-variable divided-difference contractions, without
using general regular-sequence theory.
-/

namespace BPFixedPoints.Koszul

set_option linter.unusedSectionVars false

open MvPolynomial

variable {E σ R : Type*} [LinearOrder E] [DecidableEq σ] [CommRing R]

noncomputable def coeffZeroHom (i : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun j => if j = i then 0 else X j

@[simp] theorem coeffZeroHom_X (i j : σ) :
    coeffZeroHom (R := R) i (X j) = if j = i then 0 else X j := by
  simp [coeffZeroHom]

@[simp] theorem coeffDiv_C (i : σ) (r : R) : coeffDiv i (C r) = 0 := by
  ext m
  have hm : Finsupp.single i 1 + m ≠ 0 := by
    intro h
    have := congrArg (fun d : σ →₀ ℕ => d i) h
    simp at this
  simp [coeffDiv_coeff, coeff_C, hm, Ne.symm hm]

@[simp] theorem coeffProj_C (i : σ) (r : R) : coeffProj i (C r) = C r := by
  simp [coeffProj]

@[simp] theorem coeffProj_X_mul (i : σ) (p : MvPolynomial σ R) :
    coeffProj i (X i * p) = 0 := by
  simp [coeffProj]

theorem coeffProj_X_mul_of_ne {i j : σ} (hij : i ≠ j) (p : MvPolynomial σ R) :
    coeffProj i (X j * p) = X j * coeffProj i p := by
  change X j * p - X i * coeffDiv i (X j * p) = X j * (p - X i * coeffDiv i p)
  rw [coeffDiv_X_mul_of_ne hij]
  ring

theorem coeffProj_eq_coeffZeroHom (i : σ) (p : MvPolynomial σ R) :
    coeffProj i p = coeffZeroHom i p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [coeffZeroHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [mul_comm p, map_mul (coeffZeroHom i), coeffZeroHom_X]
    by_cases hij : i = j
    · subst j; simp
    · rw [coeffProj_X_mul_of_ne hij, hp]
      simp [Ne.symm hij]

/-- Set pivot variables to zero in a specified order. -/
noncomputable def coeffZeroList (ι : E → σ) : List E →
    (MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
  | [] => AlgHom.id R _
  | e :: L => (coeffZeroHom (ι e)).comp (coeffZeroList ι L)

/-- Remove a specified exterior edge and set the matching coefficient variable to zero. -/
noncomputable def projectList (ι : E → σ) : List E →
    Module.End R (Space E (MvPolynomial σ R))
  | [] => 1
  | e :: L => projectOne ι e * projectList ι L

/-- Finite telescoping sum joining one-variable contractions by projections. -/
noncomputable def homotopyList (ι : E → σ) : List E →
    Module.End R (Space E (MvPolynomial σ R))
  | [] => 0
  | e :: L => homotopyOne ι e + projectOne ι e * homotopyList ι L

theorem projectList_single (ι : E → σ) (L : List E)
    (S : Finset E) (p : MvPolynomial σ R) :
    projectList ι L (Finsupp.single S p) =
      if ∀ e ∈ L, e ∉ S then Finsupp.single S (coeffZeroList ι L p) else 0 := by
  induction L with
  | nil => simp [projectList, coeffZeroList]
  | cons e L ih =>
    simp only [projectList, Module.End.mul_apply, ih, List.forall_mem_cons]
    by_cases hL : ∀ j ∈ L, j ∉ S
    · rw [ite_eq_left hL]
      by_cases he : e ∈ S
      · rw [ite_eq_right (fun h => h.1 he)]
        simp only [projectOne_single, ite_eq_left he]
      · rw [ite_eq_left ⟨he, hL⟩]
        simp only [projectOne_single, ite_eq_right he, coeffZeroList,
          AlgHom.comp_apply, coeffProj_eq_coeffZeroHom]
    · rw [ite_eq_right hL, ite_eq_right (fun h => hL h.2), map_zero]

@[simp] theorem coeffZeroList_coeff (ι : E → σ) (L : List E)
    (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (coeffZeroList ι L p).coeff m =
      if ∀ e ∈ L, m (ι e) = 0 then p.coeff m else 0 := by
  induction L with
  | nil => simp [coeffZeroList]
  | cons e L ih =>
    simp only [coeffZeroList, AlgHom.comp_apply, ← coeffProj_eq_coeffZeroHom,
      coeffProj_coeff, ih]
    by_cases he : m (ι e) = 0 <;> by_cases hL : ∀ j ∈ L, m (ι j) = 0 <;>
      simp [he, hL]

@[simp] theorem coeffZeroList_idem (ι : E → σ) (L : List E) (p : MvPolynomial σ R) :
    coeffZeroList ι L (coeffZeroList ι L p) = coeffZeroList ι L p := by
  ext m
  simp only [coeffZeroList_coeff]
  split_ifs <;> rfl

@[simp] theorem projectList_idem (ι : E → σ) (L : List E) :
    projectList (R := R) ι L * projectList ι L = projectList ι L := by
  apply Finsupp.lhom_ext
  intro S p
  simp only [Module.End.mul_apply, projectList_single]
  by_cases hS : ∀ e ∈ L, e ∉ S
  · rw [ite_eq_left hS, projectList_single, ite_eq_left hS, coeffZeroList_idem]
  · rw [ite_eq_right hS, map_zero]

private theorem projection_commutes {A : Type*} [Ring A] (d h P : A)
    (hc : d * h + h * d = 1 - P) (hd : d * d = 0) : d * P = P * d := by
  linear_combination (norm := noncomm_ring) d * hc - hc * d - hd * h + h * hd

private theorem telescope_step {A : Type*} [Ring A] (d h H P Q : A)
    (hc : d * h + h * d = 1 - P) (hH : d * H + H * d + Q = 1)
    (hP : d * P = P * d) :
    d * (h + P * H) + (h + P * H) * d + P * Q = 1 := by
  linear_combination (norm := noncomm_ring) hc + P * hH + hP * H

section Fintype

variable [Fintype E]

theorem variableDifferential_projectOne (ι : E → σ) (hι : Function.Injective ι) (e : E) :
    variableDifferential (R := R) ι * projectOne ι e =
      projectOne ι e * variableDifferential ι := by
  exact projection_commutes (variableDifferential (R := R) ι)
    (homotopyOne (R := R) ι e) (projectOne (R := R) ι e)
    (variableDifferential_homotopyOne ι hι e) (variableDifferential_sq ι)

/-- Weak contraction identity eliminating finitely many independent variables. -/
theorem variableDifferential_homotopyList (ι : E → σ) (hι : Function.Injective ι) (L : List E) :
    variableDifferential (R := R) ι * homotopyList ι L +
      homotopyList ι L * variableDifferential ι + projectList (R := R) ι L = 1 := by
  induction L with
  | nil => simp [homotopyList, projectList]
  | cons e L ih =>
    simp only [homotopyList, projectList]
    exact telescope_step (variableDifferential (R := R) ι)
      (homotopyOne (R := R) ι e) (homotopyList (R := R) ι L)
      (projectOne (R := R) ι e) (projectList (R := R) ι L)
      (variableDifferential_homotopyOne ι hι e) ih (variableDifferential_projectOne ι hι e)

/-- After eliminating all pivots, the projection image is concentrated in the empty exterior state. -/
theorem projectList_univ_apply (ι : E → σ) (x : Space E (MvPolynomial σ R)) :
    projectList ι (Finset.univ.toList) x =
      Finsupp.single ∅ (coeffZeroList ι (Finset.univ.toList) (x ∅)) := by
  let f : Space E (MvPolynomial σ R) →ₗ[R] Space E (MvPolynomial σ R) :=
    (Finsupp.lsingle ∅).comp
      ((coeffZeroList ι Finset.univ.toList).toLinearMap.comp (Finsupp.lapply ∅))
  have hf : projectList ι Finset.univ.toList = f := by
    apply Finsupp.lhom_ext
    intro S p
    rw [projectList_single]
    by_cases hS : S = ∅
    · subst S; simp [f]
    · have hn : ¬ ∀ e ∈ Finset.univ.toList, e ∉ S := by
        intro h
        exact hS (Finset.eq_empty_iff_forall_notMem.mpr (fun e => h e (by simp)))
      rw [ite_eq_right hn]
      simp [f, Ne.symm hS]
  exact LinearMap.congr_fun hf x

theorem variableDifferential_projectList_univ (ι : E → σ) :
    variableDifferential (R := R) ι * projectList ι Finset.univ.toList = 0 := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, projectList_univ_apply]
  simp [variableDifferential, differential]

theorem variableDifferential_projectList (ι : E → σ) (hι : Function.Injective ι) (L : List E) :
    variableDifferential (R := R) ι * projectList ι L =
      projectList ι L * variableDifferential ι := by
  induction L with
  | nil => simp [projectList]
  | cons e L ih =>
    simp only [projectList]
    rw [← mul_assoc, variableDifferential_projectOne ι hι, mul_assoc, ih, ← mul_assoc]

/-- Ideal generated by the pivot variables. -/
noncomputable def variableIdeal (ι : E → σ) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun e => X (ι e))

abbrev VariableQuotient (ι : E → σ) := MvPolynomial σ R ⧸ variableIdeal (R := R) ι

@[simp] theorem variableQuotient_mk_X (ι : E → σ) (e : E) :
    Ideal.Quotient.mk (variableIdeal (R := R) ι) (X (ι e)) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)

theorem coeffZeroList_X_of_mem (ι : E → σ) (L : List E) {e : E} (he : e ∈ L) :
    coeffZeroList (R := R) ι L (X (ι e)) = 0 := by
  ext m
  rw [coeffZeroList_coeff]
  split_ifs with hm
  · have hne : Finsupp.single (ι e) 1 ≠ m := by
      intro h
      have hzero := hm e he
      rw [← h] at hzero
      simpa using hzero
    simp [coeff_X, hne]
  · rfl

theorem variableQuotient_mk_coeffZeroHom (ι : E → σ) (e : E) (p : MvPolynomial σ R) :
    Ideal.Quotient.mk (variableIdeal ι) (coeffZeroHom (ι e) p) =
      Ideal.Quotient.mk (variableIdeal ι) p := by
  have h : (Ideal.Quotient.mkₐ R (variableIdeal ι)).comp (coeffZeroHom (ι e)) =
      Ideal.Quotient.mkₐ R (variableIdeal ι) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, coeffZeroHom_X]
    by_cases hj : j = ι e
    · subst j; simp
    · simp [hj]
  exact AlgHom.congr_fun h p

theorem variableQuotient_mk_coeffZeroList (ι : E → σ) (L : List E) (p : MvPolynomial σ R) :
    Ideal.Quotient.mk (variableIdeal ι) (coeffZeroList ι L p) =
      Ideal.Quotient.mk (variableIdeal ι) p := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [coeffZeroList, AlgHom.comp_apply, variableQuotient_mk_coeffZeroHom, ih]

/-- Lift a degree-zero quotient element to a representative without pivot variables. -/
noncomputable def variableQuotientSection (ι : E → σ) :
    VariableQuotient (R := R) ι →ₐ[R] MvPolynomial σ R :=
  Ideal.Quotient.liftₐ _ (coeffZeroList ι Finset.univ.toList) <| by
    intro p hp
    have hle : variableIdeal ι ≤
        RingHom.ker (coeffZeroList (R := R) ι Finset.univ.toList).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨e, rfl⟩
      exact coeffZeroList_X_of_mem ι _ (by simp)
    exact hle hp

@[simp] theorem variableQuotientSection_mk (ι : E → σ) (p : MvPolynomial σ R) :
    variableQuotientSection ι (Ideal.Quotient.mk (variableIdeal ι) p) =
      coeffZeroList ι Finset.univ.toList p := rfl

/-- Koszul augmentation: send the empty exterior coefficient to the degree-zero quotient. -/
noncomputable def variableAugmentation (ι : E → σ) :
    Space E (MvPolynomial σ R) →ₗ[R] VariableQuotient (R := R) ι :=
  (Ideal.Quotient.mkₐ R (variableIdeal ι)).toLinearMap.comp (Finsupp.lapply ∅)

/-- Linear section from the degree-zero quotient to the empty exterior state. -/
noncomputable def variableSection (ι : E → σ) :
    VariableQuotient (R := R) ι →ₗ[R] Space E (MvPolynomial σ R) :=
  (Finsupp.lsingle ∅).comp (variableQuotientSection ι).toLinearMap

@[simp] theorem variableAugmentation_section (ι : E → σ) :
    (variableAugmentation (R := R) ι).comp (variableSection ι) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Quotient.inductionOn' with
  | h p =>
    simp only [variableAugmentation, variableSection, LinearMap.comp_apply,
      Finsupp.lsingle_apply, Finsupp.lapply_apply, Finsupp.single_eq_same,
      AlgHom.toLinearMap_apply, LinearMap.id_apply]
    change Ideal.Quotient.mk (variableIdeal ι)
      (variableQuotientSection ι (Ideal.Quotient.mk (variableIdeal ι) p)) =
      Ideal.Quotient.mk (variableIdeal ι) p
    rw [variableQuotientSection_mk, variableQuotient_mk_coeffZeroList]

theorem variableSection_augmentation (ι : E → σ) :
    (variableSection (R := R) ι).comp (variableAugmentation ι) =
      projectList ι Finset.univ.toList := by
  apply LinearMap.ext
  intro x
  simp [variableSection, variableAugmentation, projectList_univ_apply]

@[simp] theorem variableDifferential_section (ι : E → σ) :
    (variableDifferential (R := R) ι).comp (variableSection ι) = 0 := by
  apply LinearMap.ext
  intro q
  simp [variableSection, variableDifferential, differential]

@[simp] theorem variableAugmentation_differential (ι : E → σ) (hι : Function.Injective ι) :
    (variableAugmentation (R := R) ι).comp (variableDifferential ι) = 0 := by
  have hleft : Function.LeftInverse (variableAugmentation (R := R) ι)
      (variableSection ι) := fun q =>
    LinearMap.congr_fun (variableAugmentation_section (R := R) ι) q
  have hi := hleft.injective
  have hP : projectList (R := R) ι Finset.univ.toList * variableDifferential ι = 0 := by
    rw [← variableDifferential_projectList ι hι, variableDifferential_projectList_univ]
  apply LinearMap.ext
  intro x
  apply hi
  have hx := LinearMap.congr_fun hP x
  simpa only [← variableSection_augmentation, LinearMap.comp_apply,
    Module.End.mul_apply, LinearMap.zero_apply, map_zero] using hx

/-- Weak contraction to the degree-zero quotient for chart-local exactness. -/
theorem variable_weakContraction (ι : E → σ) (hι : Function.Injective ι) :
    variableDifferential (R := R) ι * homotopyList ι Finset.univ.toList +
      homotopyList ι Finset.univ.toList * variableDifferential ι +
      (variableSection ι).comp (variableAugmentation ι) = 1 := by
  rw [variableSection_augmentation]
  exact variableDifferential_homotopyList ι hι _

/-- Actual strong contraction of the independent-variable Koszul complex to its degree-zero quotient. -/
noncomputable def variableContraction (ι : E → σ) (hι : Function.Injective ι) :
    IncidencePerturbation.Contraction R (Space E (MvPolynomial σ R))
      (VariableQuotient (R := R) ι) :=
  IncidencePerturbation.Contraction.ofHomotopy
    (variableDifferential ι) (variableSection ι) (variableAugmentation ι)
    (homotopyList ι Finset.univ.toList)
    (variableDifferential_sq ι) (variableDifferential_section ι)
    (variableAugmentation_differential ι hι) (variableAugmentation_section ι)
    (variable_weakContraction ι hι)

@[simp] theorem variableContraction_d (ι : E → σ) (hι : Function.Injective ι) :
    (variableContraction (R := R) ι hι).d = variableDifferential ι := rfl

@[simp] theorem variableContraction_p (ι : E → σ) (hι : Function.Injective ι) :
    (variableContraction (R := R) ι hι).p = variableAugmentation ι := rfl

end Fintype

end BPFixedPoints.Koszul
