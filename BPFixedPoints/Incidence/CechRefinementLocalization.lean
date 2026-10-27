import BPFixedPoints.Incidence.CechFaceRefinement
import BPFixedPoints.Incidence.CechOverlapFractions

/-! # All higher Čech intersections are actual face localizations

A refinement inverts exactly the vertex coordinates newly changed to Laurent
coordinates. One monomial, the product of those coordinates, clears every
fraction. Coordinates already Laurent require no additional denominators.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Convert an integer to a face exponent, truncating only polynomial coordinates. -/
def exponentFromInt : (q : Fin 3) → ℤ → FaceExponent q
  | 0, z => z.toNat
  | 1, z => z.toNat
  | 2, z => z

theorem exponentToInt_fromInt (q : Fin 3) (z : ℤ) (hz : q ≠ 2 → 0 ≤ z) :
    exponentToInt q (exponentFromInt q z) = z := by
  fin_cases q
  · change (z.toNat : ℤ) = z
    exact Int.toNat_of_nonneg (hz (by decide))
  · change (z.toNat : ℤ) = z
    exact Int.toNat_of_nonneg (hz (by decide))
  · rfl

/-- Source exponent of the product of all newly inverted coordinates. -/
noncomputable def refinementDenExponent (q r : V → Fin 3) : FaceMonoid q := fun v =>
  if q v = r v then 0 else faceOneExponent (q v)

@[simp] theorem refinementDenExponent_toInt (q r : V → Fin 3) (v : V) :
    faceToInt q (refinementDenExponent q r) v = if q v = r v then 0 else 1 := by
  change exponentToInt (q v) (if q v = r v then 0 else faceOneExponent (q v)) = _
  split_ifs <;> simp

/-- Every exponent in a higher overlap has one common monomial denominator. -/
theorem refinementExponent_clear {q r : V → Fin 3} (h : FaceRefines q r)
    (m : FaceMonoid r) :
    ∃ (n : ℕ) (k : FaceMonoid q),
      m + n • refinementExponent h (refinementDenExponent q r) = refinementExponent h k := by
  let z : V → ℤ := fun v =>
    if q v = 1 ∧ r v = 2 then -(faceToInt r m v) else faceToInt r m v
  let n : ℕ := ∑ v, (-z v).toNat
  have hn (v : V) : (-z v).toNat ≤ n := by
    exact Finset.single_le_sum (f := fun w => (-z w).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  let k : FaceMonoid q := fun v => exponentFromInt (q v)
    (z v + if q v = r v then 0 else (n : ℤ))
  have hk (v : V) : faceToInt q k v = z v + if q v = r v then 0 else (n : ℤ) := by
    apply exponentToInt_fromInt
    intro hq
    by_cases he : q v = r v
    · have hr : r v ≠ 2 := by simpa [← he] using hq
      have hm := exponentToInt_nonneg_of_ne_two (r v) hr (m v)
      simpa [z, he, hr, faceToInt] using hm
    · have hb := hn v
      simp only [ite_eq_right he]
      omega
  refine ⟨n, k, ?_⟩
  apply faceToInt_injective
  ext v
  simp only [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply,
    faceToInt_refinement, refinementDenExponent_toInt, hk]
  by_cases he : q v = r v
  · have hs : ¬(r v = 1 ∧ r v = 2) := by omega
    simp [he, hs, z]
  · have hr : r v = 2 := (h v).resolve_left he
    by_cases hq : q v = 1 <;> simp [he, hr, hq, z, nsmul_eq_mul] <;> ring

/-- Every refinement exponent map is injective, including mixed Laurent faces. -/
theorem refinementExponent_injective {q r : V → Fin 3} (h : FaceRefines q r) :
    Function.Injective (refinementExponent h) := by
  intro m n he
  apply faceToInt_injective
  funext v
  have hv := congrFun (congrArg (faceToInt r) he) v
  simp only [faceToInt_refinement] at hv
  split_ifs at hv <;> omega

/-- Every newly inverted source coordinate is a unit in the target face monoid algebra. -/
theorem refinementDenExponent_opposite {q r : V → Fin 3} (h : FaceRefines q r) :
    ∃ t : FaceMonoid r, refinementExponent h (refinementDenExponent q r) + t = 0 := by
  let t : FaceMonoid r := fun v => exponentFromInt (r v)
    (-(faceToInt r (refinementExponent h (refinementDenExponent q r)) v))
  refine ⟨t, ?_⟩
  apply faceToInt_injective
  ext v
  simp only [map_add, map_zero, Pi.add_apply, Pi.zero_apply]
  have ht : faceToInt r t v =
      -(faceToInt r (refinementExponent h (refinementDenExponent q r)) v) := by
    apply exponentToInt_fromInt
    intro hr
    have he : q v = r v := (h v).resolve_right hr
    simp [faceToInt_refinement, refinementDenExponent_toInt, he, hr]
  rw [ht, add_neg_cancel]

variable (R : Type*) [CommRing R]

/-- The product of exactly those vertex coordinates inverted by a refinement. -/
noncomputable def refinementDen (q r : V → Fin 3) : FaceRing R q :=
  AddMonoidAlgebra.single (refinementDenExponent q r) 1

theorem faceRefinement_den_isUnit {q r : V → Fin 3} (h : FaceRefines q r) :
    IsUnit (faceRefinementMap R h (refinementDen R q r)) := by
  obtain ⟨t, ht⟩ := refinementDenExponent_opposite h
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single t 1, ?_⟩
  rw [refinementDen, faceRefinementMap_single, AddMonoidAlgebra.single_mul_single,
    ht, mul_one]
  rfl

theorem faceRefinement_injective {q r : V → Fin 3} (h : FaceRefines q r) :
    Function.Injective (faceRefinementMap R h) :=
  AddMonoidAlgebra.mapDomain_injective (R := R) (refinementExponent_injective h)

/-- A genuine fraction normal form for every section on every higher intersection. -/
theorem faceRefinement_fraction {q r : V → Fin 3} (h : FaceRefines q r) (f : FaceRing R r) :
    ∃ (n : ℕ) (a : FaceRing R q),
      f * (faceRefinementMap R h (refinementDen R q r))^n = faceRefinementMap R h a := by
  let χ := faceRefinementMap R h
  let d := refinementDen R q r
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
  | single m c =>
      obtain ⟨n, k, hk⟩ := refinementExponent_clear h m
      refine ⟨n, AddMonoidAlgebra.single k c, ?_⟩
      simp only [refinementDen, faceRefinementMap_single, AddMonoidAlgebra.single_pow,
        one_pow, AddMonoidAlgebra.single_mul_single, mul_one, hk]

/-- Every higher face is the localization of its parent at the product of the
newly inverted vertex coordinates. -/
theorem faceRefinement_isLocalization {q r : V → Fin 3} (h : FaceRefines q r) :
    letI := (faceRefinementMap R h).toRingHom.toAlgebra
    IsLocalization.Away (refinementDen R q r) (FaceRing R r) := by
  letI := (faceRefinementMap R h).toRingHom.toAlgebra
  apply IsLocalization.Away.mk
  · exact faceRefinement_den_isUnit R h
  · exact faceRefinement_fraction R h
  · intro x y he
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using faceRefinement_injective R h he

end BPFixedPoints.CechProduct
