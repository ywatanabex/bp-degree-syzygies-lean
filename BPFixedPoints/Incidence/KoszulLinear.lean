import BPFixedPoints.Incidence.Koszul

/-!
# Koszul differentials from commuting module operators

Allow coefficients to act by commuting linear operators, rather than only by
ring elements. Edge sections act directly on the Čech Laurent-monomial module.
-/

namespace BPFixedPoints.Koszul

variable {E R W : Type*} [LinearOrder E] [CommRing R]
  [AddCommGroup W] [Module R W]

/-- One-edge Koszul term: apply the coefficient operator after signed exterior removal. -/
noncomputable def linearTerm (e : E) (f : Module.End R W) :
    Module.End R (Space E W) :=
  Finsupp.lsum R fun S => if e ∈ S then
    sign (A := R) S e • (Finsupp.lsingle (S.erase e)).comp f else 0

@[simp] theorem linearTerm_single (e : E) (f : Module.End R W)
    (S : Finset E) (w : W) :
    linearTerm e f (Finsupp.single S w) =
      if e ∈ S then Finsupp.single (S.erase e) (sign (A := R) S e • f w) else 0 := by
  simp only [linearTerm, Finsupp.lsum_single]
  split_ifs <;> simp [Finsupp.smul_single]

@[simp] theorem linearTerm_sq (e : E) (f : Module.End R W) :
    linearTerm e f * linearTerm e f = 0 := by
  apply Finsupp.lhom_ext
  intro S w
  simp only [Module.End.mul_apply, linearTerm_single, LinearMap.zero_apply]
  split_ifs <;> simp

theorem linearTerm_anticomm (e j : E) (f g : Module.End R W)
    (hfg : Commute f g) :
    linearTerm e f * linearTerm j g = -(linearTerm j g * linearTerm e f) := by
  by_cases hej : e = j
  · subst j
    apply Finsupp.lhom_ext
    intro S w
    simp only [Module.End.mul_apply, LinearMap.neg_apply, linearTerm_single]
    split_ifs <;> simp
  apply Finsupp.lhom_ext
  intro S w
  simp only [Module.End.mul_apply, LinearMap.neg_apply, linearTerm_single]
  by_cases he : e ∈ S <;> by_cases hj : j ∈ S
  · simp only [he, hj, ↓reduceIte, linearTerm_single, Finset.mem_erase]
    rw [ite_eq_left ⟨hej, trivial⟩, ite_eq_left ⟨Ne.symm hej, trivial⟩]
    rw [Finset.erase_right_comm, ← Finsupp.single_neg]
    congr 1
    simp only [map_smul, smul_smul]
    have hcomm : f (g w) = g (f w) := LinearMap.congr_fun hfg.eq w
    rw [hcomm, mul_comm (sign (A := R) (S.erase j) e),
      mul_comm (sign (A := R) (S.erase e) j),
      sign_erase_anticomm hj he (Ne.symm hej), neg_smul]
  · simp [he, hj]
  · simp [he, hj]
  · simp [he, hj]

section Differential

variable [Fintype E]

/-- Koszul differential from commuting coefficient actions. -/
noncomputable def differentialLinear (f : E → Module.End R W) :
    Module.End R (Space E W) := ∑ e, linearTerm e (f e)

theorem differentialLinear_sq (f : E → Module.End R W)
    (hf : ∀ e j, Commute (f e) (f j)) :
    differentialLinear f * differentialLinear f = 0 := by
  have h : ∀ T : Finset E,
      (∑ e ∈ T, linearTerm e (f e)) * (∑ e ∈ T, linearTerm e (f e)) = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert e T he ih =>
      rw [Finset.sum_insert he, add_mul, mul_add, mul_add,
        linearTerm_sq, ih, zero_add, add_zero]
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro j hj
      rw [linearTerm_anticomm e j (f e) (f j) (hf e j)]
      ext x S
      simp
  exact h Finset.univ

@[simp] theorem differentialLinear_differentialLinear (f : E → Module.End R W)
    (hf : ∀ e j, Commute (f e) (f j)) (x : Space E W) :
    differentialLinear f (differentialLinear f x) = 0 :=
  LinearMap.congr_fun (differentialLinear_sq f hf) x

theorem differentialLinear_single (f : E → Module.End R W)
    (S : Finset E) (w : W) :
    differentialLinear f (Finsupp.single S w) =
      ∑ e ∈ S, Finsupp.single (S.erase e) (sign (A := R) S e • f e w) := by
  simp only [differentialLinear, LinearMap.sum_apply, linearTerm_single]
  rw [← Finset.sum_filter]
  simp

end Differential

end BPFixedPoints.Koszul
