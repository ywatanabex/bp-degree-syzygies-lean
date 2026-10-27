import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDiagram

/-! # Existing twist face restrictions on the original mixed monomials -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

omit [Fintype V] in
/-- Read the distinguished coordinate of an original face monomial. -/
@[simp] theorem faceToInt_single_same (q : V → Fin 3) (v : V) (m : FaceExponent (q v)) :
    faceToInt q (Pi.single v m) v = exponentToInt (q v) m := by
  change exponentToInt (q v) ((Pi.single v m : FaceMonoid q) v) = _
  rw [Pi.single_eq_same]

omit [Fintype V] in
/-- Every integer power of the original Laurent unit has its specified monomial exponent. -/
theorem faceLaurentUnit_zpow (q : V → Fin 3) (v : V) (hv : q v = 2) (z : ℤ) :
    (faceLaurentUnit R q v hv ^ z : (FaceRing R q)ˣ) =
      (AddMonoidAlgebra.single (Pi.single v (exponentFromInt (q v) z)) 1 : FaceRing R q) := by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
      change (AddMonoidAlgebra.single (Pi.single v (faceOneExponent (q v)) : FaceMonoid q) (1 : R)) ^ n = _
      rw [AddMonoidAlgebra.single_pow, one_pow]
      congr 1
      apply faceToInt_injective
      ext w
      by_cases hw : w = v
      · subst w
        rw [map_nsmul]
        change n • (faceToInt q (Pi.single v (faceOneExponent (q v))) v) = _
        rw [faceToInt_single_same, faceToInt_single_same]
        rw [exponentToInt_one, exponentToInt_fromInt]
        · simp
        · intro hn
          exact (hn hv).elim
      · simp [faceToInt, hw]
  | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      change (AddMonoidAlgebra.single (Pi.single v (exponentFromInt (q v) (-1)) : FaceMonoid q) (1 : R)) ^ (n+1) = _
      rw [AddMonoidAlgebra.single_pow, one_pow]
      congr 1
      apply faceToInt_injective
      ext w
      by_cases hw : w = v
      · subst w
        rw [map_nsmul]
        change (n+1) • (faceToInt q (Pi.single v (exponentFromInt (q v) (-1))) v) = _
        rw [faceToInt_single_same, faceToInt_single_same]
        rw [exponentToInt_fromInt, exponentToInt_fromInt]
        · simp
          omega
        · intro hn
          exact (hn hv).elim
        · intro hn
          exact (hn hv).elim
      · simp [faceToInt, hw]

/-- The monomial shift for section coefficients, the inverse of the existing frame unit. -/
noncomputable def twistRestrictionShift {q r : V → Fin 3} (_h : FaceRefines q r) (a : V → ℤ) :
    FaceMonoid r := fun v => if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (a v) else 0

/-- The original inverse frame unit is exactly its coordinatewise mixed monomial. -/
theorem multiTwistTransition_inv_monomial {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    (↑((multiTwistTransition R h a)⁻¹) : FaceRing R r) =
      AddMonoidAlgebra.single (twistRestrictionShift h a) 1 := by
  have he : twistRestrictionShift h a =
      ∑ v, Pi.single v (if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (a v) else 0) := by
    ext w
    simp [twistRestrictionShift]
  rw [he, multiTwistTransition, ← Finset.prod_inv_distrib, Units.coe_prod]
  have hf (v : V) : (↑((faceTransitionUnit R h v ^ a v)⁻¹) : FaceRing R r) =
      AddMonoidAlgebra.single
        (Pi.single v (if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (a v) else 0)) 1 := by
    by_cases hv : q v = 1 ∧ r v = 2
    · simp only [faceTransitionUnit, dite_eq_left hv, inv_zpow, inv_inv, ite_eq_left hv]
      exact faceLaurentUnit_zpow R r v hv.2 (a v)
    · simp [faceTransitionUnit, hv]
      rfl
  simp only [hf, AddMonoidAlgebra.prod_single, Finset.prod_const_one]

/-- Every original coefficient restriction acts by the original exponent refinement and twist shift. -/
theorem multiTwistFaceRestriction_single {q r : V → Fin 3} (h : FaceRefines q r)
    (a : V → ℤ) (m : FaceMonoid q) (c : R) :
    multiTwistFaceRestriction R h a (AddMonoidAlgebra.single m c) =
      AddMonoidAlgebra.single (refinementExponent h m + twistRestrictionShift h a) c := by
  rw [multiTwistFaceRestriction_apply, faceRefinementMap_single, multiTwistTransition_inv_monomial,
    AddMonoidAlgebra.single_mul_single, mul_one]

end BPFixedPoints.CechProduct
