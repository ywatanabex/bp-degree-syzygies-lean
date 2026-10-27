import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Common Laurent ring comparing polynomials and localizations

Use the monoid ring of integer exponents as a common target. Injectivity of
polynomials follows coefficientwise, without a denominator-clearing argument.
-/

namespace BPFixedPoints.IncidenceLaurent

variable {σ R : Type*} [CommRing R]

abbrev LaurentRing (σ R : Type*) [CommRing R] := AddMonoidAlgebra R (σ → ℤ)

/-- Embed finite nonnegative exponent vectors into integer exponent vectors. -/
def natExponent : (σ →₀ ℕ) →+ (σ → ℤ) where
  toFun m i := (m i : ℤ)
  map_zero' := by funext i; simp
  map_add' m n := by funext i; simp

theorem natExponent_injective : Function.Injective (natExponent (σ := σ)) := by
  intro m n h
  ext i
  exact Int.ofNat_inj.mp (congrFun h i)

/-- Coefficient-preserving map from multivariate polynomials to the integer-exponent Laurent ring. -/
noncomputable def polynomialMap : MvPolynomial σ R →ₐ[R] LaurentRing σ R :=
  AddMonoidAlgebra.mapDomainAlgHom R R natExponent

theorem polynomialMap_injective : Function.Injective (polynomialMap (σ := σ) (R := R)) :=
  AddMonoidAlgebra.mapDomain_injective natExponent_injective

@[simp] theorem polynomialMap_monomial (m : σ →₀ ℕ) (r : R) :
    polynomialMap (MvPolynomial.monomial m r) = AddMonoidAlgebra.single (natExponent m) r := by
  simp [polynomialMap, MvPolynomial.monomial]

@[simp] theorem polynomialMap_X (i : σ) :
    polynomialMap (R := R) (MvPolynomial.X i) =
      AddMonoidAlgebra.single (natExponent (Finsupp.single i 1)) 1 := by
  exact polynomialMap_monomial _ _

theorem polynomialMap_X_unit (i : σ) : IsUnit (polynomialMap (R := R) (MvPolynomial.X i)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-(natExponent (Finsupp.single i 1))) 1, ?_⟩
  rw [polynomialMap_X, AddMonoidAlgebra.single_mul_single]
  simp [AddMonoidAlgebra.one_def]

/-- Extend a map from a localization when every inverted polynomial becomes a Laurent unit. -/
noncomputable def localizationMap (s : MvPolynomial σ R)
    (hs : IsUnit (polynomialMap s)) : Localization.Away s →ₐ[R] LaurentRing σ R :=
  IsLocalization.Away.liftAlgHom s hs

@[simp] theorem localizationMap_algebraMap (s : MvPolynomial σ R)
    (hs : IsUnit (polynomialMap s)) (p : MvPolynomial σ R) :
    localizationMap s hs (algebraMap (MvPolynomial σ R) (Localization.Away s) p) =
      polynomialMap p :=
  IsLocalization.Away.lift_eq s hs p

end BPFixedPoints.IncidenceLaurent
