import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases

/-! # Standard affine charts of Mathlib's projective line

This file compares the genuine degree-zero homogeneous localizations in Proj
with ordinary polynomial charts. The pivot is either of the two original
homogeneous variables; no independently glued replacement for Proj is used.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (R : Type*) [CommRing R]

abbrev CoxRing := MvPolynomial (Fin 2) R
abbrev grading := homogeneousSubmodule (Fin 2) R

noncomputable instance coxGradedAlgebra : GradedAlgebra (grading R) := MvPolynomial.gradedAlgebra

/-- The projective line supplied by the existing Proj construction. -/
noncomputable def projectiveLine : Scheme := Proj (grading R)

/-- The actual homogeneous localization for either standard Proj open. -/
abbrev ChartRing (i : Fin 2) := HomogeneousLocalization.Away (grading R) (X i)

/-- Normalize the selected original coordinate to one. -/
noncomputable def normalize (i : Fin 2) : CoxRing R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

@[simp] theorem normalize_pivot (i : Fin 2) : normalize R i (X i) = 1 := by
  simp [normalize]

@[simp] theorem normalize_opposite (i : Fin 2) :
    normalize R i (X i.rev) = Polynomial.X := by
  fin_cases i <;> simp [normalize]

/-- Normalization extends to the ordinary localization because the pivot maps to one. -/
noncomputable def normalizeAway (i : Fin 2) : Localization.Away (X i : CoxRing R) →+* Polynomial R :=
  IsLocalization.Away.lift (X i) (g := normalize R i) (by simp)

@[simp] theorem normalizeAway_algebraMap (i : Fin 2) (a : CoxRing R) :
    normalizeAway R i (algebraMap (CoxRing R) _ a) = normalize R i a :=
  IsLocalization.Away.lift_eq _ _ _

/-- Restrict normalization to the genuine degree-zero homogeneous localization. -/
noncomputable def toPolynomial (i : Fin 2) : ChartRing R i →+* Polynomial R :=
  (normalizeAway R i).comp (algebraMap (ChartRing R i) (Localization.Away (X i : CoxRing R)))

/-- Evaluation of a genuine homogeneous fraction after normalization. -/
theorem toPolynomial_mk (i : Fin 2) (n : ℕ) (a : CoxRing R)
    (ha : a ∈ grading R (n • (1 : ℕ))) :
    toPolynomial R i (HomogeneousLocalization.Away.mk (grading R) (isHomogeneous_X R i) n a ha) =
      normalize R i a := by
  dsimp only [toPolynomial, RingHom.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  have h := congrArg (normalizeAway R i)
    (IsLocalization.mk'_spec (M := Submonoid.powers (X i : CoxRing R))
      (Localization.Away (X i : CoxRing R)) a
      ⟨X i ^ n, ⟨n, rfl⟩⟩)
  simpa only [map_mul, normalizeAway_algebraMap, map_pow, normalize_pivot, one_pow, mul_one] using h

/-- Constants in the degree-zero homogeneous component. -/
noncomputable def constantsToZero : R →+* grading R 0 where
  toFun r := ⟨C r, isHomogeneous_C (Fin 2) r⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' r s := by ext; simp
  map_mul' r s := by ext; simp

/-- The original scalar action on the actual Proj chart. -/
noncomputable def constants (i : Fin 2) : R →+* ChartRing R i :=
  (HomogeneousLocalization.fromZeroRingHom (grading R) _).comp (constantsToZero R)

/-- The genuine projective coordinate ratio. -/
noncomputable def ratio (i : Fin 2) : ChartRing R i :=
  HomogeneousLocalization.Away.mk (grading R) (isHomogeneous_X R i) 1 (X i.rev)
    (by simpa using isHomogeneous_X (R := R) i.rev)

/-- The polynomial chart maps to Proj using the actual coordinate ratio. -/
noncomputable def fromPolynomial (i : Fin 2) : Polynomial R →+* ChartRing R i :=
  Polynomial.eval₂RingHom (constants R i) (ratio R i)

@[simp] theorem toPolynomial_ratio (i : Fin 2) :
    toPolynomial R i (ratio R i) = Polynomial.X := by
  rw [ratio, toPolynomial_mk, normalize_opposite]

@[simp] theorem toPolynomial_constants (i : Fin 2) (r : R) :
    toPolynomial R i (constants R i r) = Polynomial.C r := by
  change toPolynomial R i
    (HomogeneousLocalization.Away.mk (grading R) (isHomogeneous_X R i) 0 (C r)
      (by simpa using isHomogeneous_C (σ := Fin 2) r)) = _
  rw [toPolynomial_mk]
  simp [normalize]

/-- One inverse identity follows from the original constant and ratio coordinates. -/
theorem toPolynomial_fromPolynomial (i : Fin 2) (p : Polynomial R) :
    toPolynomial R i (fromPolynomial R i p) = p := by
  have h : (toPolynomial R i).comp (fromPolynomial R i) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [fromPolynomial]
    · simp [fromPolynomial]
  exact congrArg (fun f : Polynomial R →+* Polynomial R => f p) h

/-- The homogeneous scaling identity needed for the two projective coordinates. -/
private theorem homogeneous_eval_scale {S : Type*} [CommRing S]
    (f : R →+* S) (p : CoxRing R) {n : ℕ} (hp : p.IsHomogeneous n)
    (c : S) (x : Fin 2 → S) :
    eval₂ f (fun j => c * x j) p = c ^ n * eval₂ f x p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp.degree_eq_sum_deg_support hd]
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  ring

@[simp] theorem constants_val (i : Fin 2) (r : R) :
    (constants R i r).val =
      algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R)) (C r) := by
  change Localization.mk (C r) (1 : Submonoid.powers (X i : CoxRing R)) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]

/-- The ratio is defined by the original homogeneous numerator and pivot. -/
theorem pivot_mul_ratio_val (i : Fin 2) :
    algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R)) (X i) *
        (ratio R i).val =
      algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R)) (X i.rev) := by
  rw [ratio, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  simpa only [pow_one] using
    (IsLocalization.mk'_spec' (M := Submonoid.powers (X i : CoxRing R))
      (Localization.Away (X i : CoxRing R)) (X i.rev) ⟨X i ^ 1, ⟨1, rfl⟩⟩)

/-- Normalizing a degree-n polynomial and restoring the pivot recovers the
original polynomial in the actual localization. -/
private theorem homogeneous_normalize_restore (i : Fin 2) (p : CoxRing R) {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (fromPolynomial R i (normalize R i p)).val *
        (algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R)) (X i)) ^ n =
      algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R)) p := by
  let φ := algebraMap (CoxRing R) (Localization.Away (X i : CoxRing R))
  let ψ := algebraMap (ChartRing R i) (Localization.Away (X i : CoxRing R))
  let x : Fin 2 → Localization.Away (X i : CoxRing R) :=
    fun j => if j = i then 1 else (ratio R i).val
  have heval : ψ.comp ((fromPolynomial R i).comp (normalize R i)) =
      eval₂Hom (φ.comp C) x := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [normalize, fromPolynomial, ψ, φ]
    · intro j
      by_cases hj : j = i <;> simp [normalize, fromPolynomial, x, ψ, hj]
  have hcoords : (fun j => φ (X i) * x j) = fun j => φ (X j) := by
    funext j
    fin_cases i <;> fin_cases j
    · simp [x]
    · simpa [x, φ] using pivot_mul_ratio_val R 0
    · simpa [x, φ] using pivot_mul_ratio_val R 1
    · simp [x]
  have hscale := homogeneous_eval_scale R (φ.comp C) p hp (φ (X i)) x
  rw [hcoords] at hscale
  have heta : eval₂ (φ.comp C) (fun j => φ (X j)) p = φ p := by
    exact (eval₂_comp_left φ C X p).symm.trans (congrArg φ (eval₂_eta p))
  rw [heta] at hscale
  have hn := congrArg (fun f : CoxRing R →+* Localization.Away (X i : CoxRing R) => f p) heval
  change ψ (fromPolynomial R i (normalize R i p)) = eval₂ (φ.comp C) x p at hn
  change ψ (fromPolynomial R i (normalize R i p)) * φ (X i) ^ n = φ p
  rw [hn]
  exact (mul_comm _ _).trans hscale.symm

/-- The second inverse identity holds for every genuine homogeneous fraction. -/
theorem fromPolynomial_toPolynomial (i : Fin 2) (z : ChartRing R i) :
    fromPolynomial R i (toPolynomial R i z) = z := by
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (grading R) (isHomogeneous_X R i) z
  rw [toPolynomial_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  symm
  apply (IsLocalization.mk'_eq_iff_eq_mul (M := Submonoid.powers (X i : CoxRing R))).2
  simpa only [smul_eq_mul, mul_one, map_pow] using
    (homogeneous_normalize_restore R i p (by simpa using hp)).symm

/-- The actual standard affine Proj chart is the ordinary polynomial ring. -/
noncomputable def chartEquiv (i : Fin 2) : ChartRing R i ≃+* Polynomial R :=
  { toPolynomial R i with
    invFun := fromPolynomial R i
    left_inv := fromPolynomial_toPolynomial R i
    right_inv := toPolynomial_fromPolynomial R i }

end BPFixedPoints.ProjectiveLine
