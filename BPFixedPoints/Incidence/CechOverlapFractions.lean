import BPFixedPoints.Incidence.CechRestrictionTorus
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Clearing the single Laurent coordinate of an adjacent-chart overlap

Each overlap monomial becomes a chart monomial after multiplication by a power
of the coordinate inverted on that overlap. Both chart orientations are covered.
-/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V]

/-- Exponents away from overlap coordinates are nonnegative. -/
theorem exponentToInt_nonneg_of_ne_two (q : Fin 3) (hq : q ≠ 2) (m : FaceExponent q) :
    0 ≤ exponentToInt q m := by
  fin_cases q <;> simp_all [exponentToInt, FaceExponent]

/-- Every monomial on an adjacent overlap admits a denominator that is a power
of the corresponding coordinate of either chosen source chart. -/
theorem overlapExponent_clear (σ : V → Bool) (v : V) (b : Bool)
    (m : FaceMonoid (overlapFace σ v)) :
    ∃ (n : ℕ) (k : V → ℕ),
      m + n • overlapExponent σ v b (Pi.single v 1) = overlapExponent σ v b k := by
  let z := faceToInt (overlapFace σ v) m v
  let n := if b then z.toNat else (-z).toNat
  let k : V → ℕ := fun w => if w = v then (if b then (-z).toNat else z.toNat)
    else (faceToInt (overlapFace σ v) m w).toNat
  refine ⟨n, k, ?_⟩
  apply faceToInt_injective
  ext w
  simp only [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, faceToInt_overlapExponent]
  by_cases hw : w = v
  · subst w
    simp only [ite_true, Pi.single_eq_same, k, z, n]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, neg_one_mul,
      nsmul_eq_mul] <;> omega
  · have hn : 0 ≤ faceToInt (overlapFace σ v) m w :=
      exponentToInt_nonneg_of_ne_two _
        ((overlapFace_ne σ v w hw) ▸ chartFace_ne_two σ w) (m w)
    simp only [ite_eq_right hw, Pi.single_eq_of_ne hw, Nat.cast_zero, nsmul_zero,
      add_zero, k]
    omega

/-- The monomials corresponding to opposite chart coordinates are mutual inverses. -/
theorem overlapExponent_opposite (σ : V → Bool) (v : V) (b : Bool) :
    overlapExponent σ v b (Pi.single v 1) +
      overlapExponent σ v (!b) (Pi.single v 1) = 0 := by
  apply faceToInt_injective
  ext w
  simp only [map_add, map_zero, Pi.add_apply, Pi.zero_apply, faceToInt_overlapExponent]
  by_cases hw : w = v
  · subst w
    cases b <;> simp
  · simp [hw]

/-- Each oriented chart exponent map is injective. -/
theorem overlapExponent_injective (σ : V → Bool) (v : V) (b : Bool) :
    Function.Injective (overlapExponent σ v b) := by
  intro k l h
  funext w
  have hw := congrFun (congrArg (faceToInt (overlapFace σ v)) h) w
  simp only [faceToInt_overlapExponent] at hw
  by_cases hv : w = v
  · subst w
    cases b <;> simp only [ite_true, Bool.false_eq_true, ↓reduceIte] at hw <;> omega
  · simp only [ite_eq_right hv] at hw
    omega

/-- The actual restriction exponent map is injective in either orientation. -/
theorem chartRestrictionExponent_injective (σ : V → Bool) (v : V) (b : Bool) :
    Function.Injective (chartRestrictionExponent σ v b) :=
  (overlapExponent_injective σ v b).comp (chartMonoidEquiv (Function.update σ v b)).symm.injective

variable (R : Type*) [CommRing R]

/-- The actual monomial for the source-chart coordinate inverted on the overlap. -/
noncomputable def overlapDen (σ : V → Bool) (v : V) (b : Bool) :
    FaceRing R (chartFace (Function.update σ v b)) :=
  AddMonoidAlgebra.single (chartMonoidEquiv (Function.update σ v b) (Pi.single v 1)) 1

/-- The chart coordinate becomes a unit on the actual overlap coordinate ring. -/
theorem chartRestriction_overlapDen_isUnit (σ : V → Bool) (v : V) (b : Bool) :
    IsUnit (chartRestriction R σ v b (overlapDen R σ v b)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (overlapExponent σ v (!b) (Pi.single v 1)) 1, ?_⟩
  rw [overlapDen, chartRestriction_single, AddMonoidAlgebra.single_mul_single,
    overlapExponent_opposite, mul_one]
  rfl

/-- Actual chart restriction is injective on the full polynomial/Laurent ring. -/
theorem chartRestriction_injective (σ : V → Bool) (v : V) (b : Bool) :
    Function.Injective (chartRestriction R σ v b) :=
  AddMonoidAlgebra.mapDomain_injective (R := R) (chartRestrictionExponent_injective σ v b)

/-- Every actual overlap section has a denominator that is a power of one chart coordinate. -/
theorem chartRestriction_fraction (σ : V → Bool) (v : V) (b : Bool)
    (f : FaceRing R (overlapFace σ v)) :
    ∃ (n : ℕ) (a : FaceRing R (chartFace (Function.update σ v b))),
      f * (chartRestriction R σ v b (overlapDen R σ v b)) ^ n = chartRestriction R σ v b a := by
  let χ := chartRestriction R σ v b
  let d := overlapDen R σ v b
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      refine ⟨n+m, a*d^m+c*d^n, ?_⟩
      change (x+y)*(χ d)^(n+m) = χ (a*d^m+c*d^n)
      calc
        _ = (x*(χ d)^n)*(χ d)^m + (y*(χ d)^m)*(χ d)^n := by rw [pow_add]; ring
        _ = χ a*(χ d)^m + χ c*(χ d)^n := by rw [ha, hc]
        _ = _ := by rw [map_add, map_mul, map_mul, map_pow, map_pow]
  | single m r =>
      obtain ⟨n, k, hk⟩ := overlapExponent_clear σ v b m
      refine ⟨n, AddMonoidAlgebra.single (chartMonoidEquiv (Function.update σ v b) k) r, ?_⟩
      simp only [overlapDen, chartRestriction_single, AddMonoidAlgebra.single_pow,
        one_pow, AddMonoidAlgebra.single_mul_single, mul_one, hk]

/-- The adjacent overlap ring is the actual localization of either chart ring
at its selected vertex coordinate. -/
theorem chartRestriction_isLocalization (σ : V → Bool) (v : V) (b : Bool) :
    letI := (chartRestriction R σ v b).toRingHom.toAlgebra
    IsLocalization.Away (overlapDen R σ v b) (FaceRing R (overlapFace σ v)) := by
  letI := (chartRestriction R σ v b).toRingHom.toAlgebra
  apply IsLocalization.Away.mk
  · exact chartRestriction_overlapDen_isUnit R σ v b
  · exact chartRestriction_fraction R σ v b
  · intro x y h
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using chartRestriction_injective R σ v b h

end BPFixedPoints.CechProduct
