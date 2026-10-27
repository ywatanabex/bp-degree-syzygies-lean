import BPFixedPoints.Incidence.ProjectiveLineGeometry
import Mathlib.Algebra.Polynomial.Laurent

/-! # The genuine projective-line overlap is the Laurent chart

Mathlib's homogeneous-localization theorem identifies the intersection as a
localization at the coordinate ratio. Uniqueness of localization then compares
it with the existing Laurent polynomial ring, including the original maps.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (R : Type*) [CommRing R]

abbrev OverlapRing := HomogeneousLocalization.Away (grading R) (X (0 : Fin 2) * X 1)

private theorem product_eq (i : Fin 2) :
    (X 0 * X 1 : CoxRing R) = X i * X i.rev := by
  fin_cases i <;> simp [mul_comm]

/-- The actual homogeneous restriction to the intersection of the two Proj opens. -/
noncomputable def overlapMap (i : Fin 2) : ChartRing R i →+* OverlapRing R :=
  HomogeneousLocalization.awayMap (grading R) (isHomogeneous_X R i.rev) (product_eq R i)

/-- The genuine restriction determines the scalar structure used in localization. -/
@[instance_reducible]
noncomputable def overlapAlgebra (i : Fin 2) : Algebra (ChartRing R i) (OverlapRing R) :=
  (overlapMap R i).toAlgebra

/-- Mathlib's existing localization theorem applied to the coordinate ratio. -/
theorem overlap_isLocalization (i : Fin 2) :
    letI := overlapAlgebra R i
    IsLocalization.Away (ratio R i) (OverlapRing R) := by
  letI := overlapAlgebra R i
  have hr : HomogeneousLocalization.Away.isLocalizationElem
      (isHomogeneous_X R i) (isHomogeneous_X R i.rev) = ratio R i := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.isLocalizationElem, ratio,
      HomogeneousLocalization.Away.val_mk, pow_one]
  rw [← hr]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (isHomogeneous_X R i) (isHomogeneous_X R i.rev) (product_eq R i) (by decide)

private theorem ratio_powers_map (i : Fin 2) :
    (Submonoid.powers (ratio R i)).map (chartEquiv R i).toMonoidHom =
      Submonoid.powers (Polynomial.X : Polynomial R) := by
  rw [Submonoid.map_powers]
  change Submonoid.powers (toPolynomial R i (ratio R i)) = _
  rw [toPolynomial_ratio]

/-- The actual Proj intersection ring is the existing Laurent polynomial ring. -/
noncomputable def overlapEquiv (i : Fin 2) : OverlapRing R ≃+* LaurentPolynomial R := by
  letI := overlapAlgebra R i
  haveI := overlap_isLocalization R i
  exact IsLocalization.ringEquivOfRingEquiv (OverlapRing R) (LaurentPolynomial R)
    (chartEquiv R i) (ratio_powers_map R i)

/-- The comparison retains the original chart restriction, rather than merely
identifying abstract isomorphic rings. -/
theorem overlapEquiv_map (i : Fin 2) (a : ChartRing R i) :
    overlapEquiv R i (overlapMap R i a) = Polynomial.toLaurent (chartEquiv R i a) := by
  letI := overlapAlgebra R i
  haveI := overlap_isLocalization R i
  exact IsLocalization.ringEquivOfRingEquiv_eq (S := OverlapRing R) (Q := LaurentPolynomial R)
    (ratio_powers_map R i) a

/-- The coordinate ratio restricts to the original Laurent parameter. -/
@[simp] theorem overlapEquiv_ratio (i : Fin 2) :
    overlapEquiv R i (overlapMap R i (ratio R i)) = LaurentPolynomial.T 1 := by
  rw [overlapEquiv_map]
  change Polynomial.toLaurent (toPolynomial R i (ratio R i)) = _
  rw [toPolynomial_ratio, Polynomial.toLaurent_X]

/-- Both original charts carry exactly the same coefficient restriction. -/
theorem overlapMap_constants (i : Fin 2) (r : R) :
    overlapMap R i (constants R i r) =
      HomogeneousLocalization.fromZeroRingHom (grading R) _ (constantsToZero R r) :=
  HomogeneousLocalization.awayMap_fromZeroRingHom (grading R)
    (isHomogeneous_X R i.rev) (product_eq R i) (constantsToZero R r)

/-- The two genuine coordinate ratios are reciprocal on the original overlap. -/
theorem overlap_ratios_mul :
    overlapMap R 0 (ratio R 0) * overlapMap R 1 (ratio R 1) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    overlapMap, ratio, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, Fin.reduceRev, pow_one,
    Localization.mk_eq_mk']
  rw [← IsLocalization.mk'_mul]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  simp only [Submonoid.coe_mul, map_mul, one_mul]
  ring

/-- In the left Laurent coordinate, the original right ratio is the inverse parameter. -/
theorem overlapEquiv_opposite_ratio :
    overlapEquiv R 0 (overlapMap R 1 (ratio R 1)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (overlapEquiv R 0) (overlap_ratios_mul R)
  rw [map_mul, map_one, overlapEquiv_ratio] at h
  apply (LaurentPolynomial.isUnit_T (R := R) 1).mul_right_inj.mp
  simpa only [← LaurentPolynomial.T_add, Int.reduceAdd, LaurentPolynomial.T_zero] using h

/-- The original right polynomial chart restricts by sending its variable to
the inverse Laurent parameter, with the same coefficient map. -/
theorem overlapEquiv_right_polynomial (p : Polynomial R) :
    overlapEquiv R 0 (overlapMap R 1 (fromPolynomial R 1 p)) =
      Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) p := by
  have h : (overlapEquiv R 0).toRingHom.comp
      ((overlapMap R 1).comp (fromPolynomial R 1)) =
      Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, fromPolynomial, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      have hc : overlapMap R 1 (constants R 1 r) = overlapMap R 0 (constants R 0 r) := by
        rw [overlapMap_constants, overlapMap_constants]
      calc
        _ = overlapEquiv R 0 (overlapMap R 0 (constants R 0 r)) :=
          congrArg (overlapEquiv R 0) hc
        _ = Polynomial.toLaurent (toPolynomial R 0 (constants R 0 r)) :=
          overlapEquiv_map R 0 (constants R 0 r)
        _ = LaurentPolynomial.C r :=
          (congrArg Polynomial.toLaurent (toPolynomial_constants R 0 r)).trans
            (Polynomial.toLaurent_C r)
    · simp only [RingHom.comp_apply, fromPolynomial, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      exact overlapEquiv_opposite_ratio R
  exact congrArg (fun f : Polynomial R →+* LaurentPolynomial R => f p) h

/-- The original left polynomial chart restricts by the usual Laurent inclusion. -/
theorem overlapEquiv_left_polynomial (p : Polynomial R) :
    overlapEquiv R 0 (overlapMap R 0 (fromPolynomial R 0 p)) = Polynomial.toLaurent p := by
  rw [overlapEquiv_map]
  change Polynomial.toLaurent (toPolynomial R 0 (fromPolynomial R 0 p)) = _
  rw [toPolynomial_fromPolynomial]

/-- The genuine intersection open in Proj. -/
noncomputable def overlapOpen : (projectiveLine R).Opens :=
  Proj.basicOpen (grading R) (X (0 : Fin 2) * X 1)

/-- It is exactly the intersection of the two original standard opens. -/
theorem overlapOpen_eq : overlapOpen R = standardOpen R 0 ⊓ standardOpen R 1 := by
  exact Proj.basicOpen_mul (grading R) (X 0) (X 1)

/-- The actual restricted Proj scheme is the affine Laurent scheme. -/
noncomputable def overlapOpenIso (i : Fin 2) :
    (overlapOpen R).toScheme ≅ Spec (CommRingCat.of (LaurentPolynomial R)) :=
  Proj.basicOpenIsoSpec (grading R) (X (0 : Fin 2) * X 1)
      ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide) ≪≫
    Scheme.Spec.mapIso (overlapEquiv R i).toCommRingCatIso.symm.op

/-- Existence form of the actual restricted Proj scheme comparison. -/
theorem overlapOpen_comparison :
    Nonempty ((overlapOpen R).toScheme ≅ Spec (CommRingCat.of (LaurentPolynomial R))) :=
  ⟨overlapOpenIso R 0⟩

end BPFixedPoints.ProjectiveLine
