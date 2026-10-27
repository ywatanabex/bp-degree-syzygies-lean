import BPFixedPoints.Incidence.KoszulLaurent
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Laurent polynomial evaluation at units -/

namespace BPFixedPoints.IncidenceLaurent

set_option linter.unusedSectionVars false

variable {σ R A : Type*} [CommRing R] [CommRing A]

/-- An integer-exponent monomial is a unit in the Laurent ring. -/
noncomputable def monomialUnit (m : σ → ℤ) : (LaurentRing σ R)ˣ where
  val := AddMonoidAlgebra.single m 1
  inv := AddMonoidAlgebra.single (-m) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

@[simp] theorem monomialUnit_val (m : σ → ℤ) :
    (monomialUnit (R := R) m : LaurentRing σ R) = AddMonoidAlgebra.single m 1 := rfl

noncomputable def monomialUnitHom : Multiplicative (σ → ℤ) →* (LaurentRing σ R)ˣ where
  toFun m := monomialUnit m.toAdd
  map_one' := by apply Units.ext; rfl
  map_mul' m n := by
    apply Units.ext
    simp [monomialUnit, AddMonoidAlgebra.single_mul_single]

section Finite

variable [Fintype σ]

/-- Multiply coordinatewise integer powers of units. -/
noncomputable def unitMonomial (u : σ → Aˣ) : Multiplicative (σ → ℤ) →* Aˣ where
  toFun m := ∏ i, u i ^ m.toAdd i
  map_one' := by simp
  map_mul' m n := by
    change (∏ i, u i ^ (m.toAdd i + n.toAdd i)) =
      (∏ i, u i ^ m.toAdd i) * ∏ i, u i ^ n.toAdd i
    simp only [zpow_add, Finset.prod_mul_distrib]

@[simp] theorem unitMonomial_single [DecidableEq σ] (u : σ → Aˣ) (i : σ) (k : ℤ) :
    unitMonomial u (Multiplicative.ofAdd (Pi.single i k)) = u i ^ k := by
  simp [unitMonomial, Pi.single_apply]

/-- A group homomorphism from an integer lattice is determined by its standard coordinate images. -/
theorem unitMonomial_of_hom [DecidableEq σ]
    (F : Multiplicative (σ → ℤ) →* Aˣ) (m : σ → ℤ) :
    unitMonomial (fun i => F (Multiplicative.ofAdd (Pi.single i 1)))
      (Multiplicative.ofAdd m) = F (Multiplicative.ofAdd m) := by
  change (∏ i, F (Multiplicative.ofAdd (Pi.single i 1)) ^ m i) = _
  simp only [← map_zpow, ← map_prod]
  congr 1
  apply Multiplicative.toAdd.injective
  change (∑ i, m i • Pi.single i (1 : ℤ)) = m
  exact (pi_eq_sum_univ' m).symm

variable [Algebra R A]

/-- Laurent polynomial evaluation homomorphism substituting units in every coordinate. -/
noncomputable def evaluate (u : σ → Aˣ) : LaurentRing σ R →ₐ[R] A :=
  AddMonoidAlgebra.lift R A (σ → ℤ) ((Units.coeHom A).comp (unitMonomial u))

@[simp] theorem evaluate_single (u : σ → Aˣ) (m : σ → ℤ) (r : R) :
    evaluate u (AddMonoidAlgebra.single m r) =
      r • (unitMonomial u (Multiplicative.ofAdd m) : A) := by
  simp [evaluate]

theorem natExponent_single [DecidableEq σ] (i : σ) :
    natExponent (Finsupp.single i 1) = Pi.single i (1 : ℤ) := by
  funext j
  by_cases h : j = i
  · subst j; simp [natExponent]
  · simp [natExponent, h]

@[simp] theorem evaluate_polynomialMap_X [DecidableEq σ] (u : σ → Aˣ) (i : σ) :
    evaluate (R := R) u (polynomialMap (R := R) (MvPolynomial.X i)) = (u i : A) := by
  rw [polynomialMap_X, natExponent_single, evaluate_single, unitMonomial_single]
  simp

theorem evaluate_comp_polynomialMap [DecidableEq σ] (u : σ → Aˣ) :
    (evaluate (R := R) u).comp (polynomialMap (R := R)) =
      MvPolynomial.aeval (R := R) (fun i => (u i : A)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, evaluate_polynomialMap_X, MvPolynomial.aeval_X]

end Finite

end BPFixedPoints.IncidenceLaurent
