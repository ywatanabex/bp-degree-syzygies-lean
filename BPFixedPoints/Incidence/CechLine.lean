import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic

/-!
# Explicit contraction of the one-vertex two-chart Čech complex

Write O(−d) over R as R[ℕ]×R[ℕ]→R[ℤ], with differential right restriction
minus left restriction. The kth right monomial has exponent −d−k.
Degree-zero cohomology consists of constants when d=0; degree-one cohomology
has Laurent basis −d<z<0. All maps and contraction identities are explicit
over any commutative ring, allowing extension to polynomial coefficients.
-/

namespace BPFixedPoints.CechLine

open Finsupp

variable (R : Type*) [CommRing R]

abbrev C0 := (ℕ →₀ R) × (ℕ →₀ R)
abbrev C1 := ℤ →₀ R

abbrev H0Index (d : ℕ) := Fin (if d = 0 then 1 else 0)
abbrev H1Index (d : ℕ) := Fin (d - 1)
abbrev H0 (d : ℕ) := H0Index d →₀ R
abbrev H1 (d : ℕ) := H1Index d →₀ R

noncomputable def leftRestriction : (ℕ →₀ R) →ₗ[R] C1 R :=
  Finsupp.lmapDomain R R (fun k : ℕ => (k : ℤ))

noncomputable def rightRestriction (d : ℕ) : (ℕ →₀ R) →ₗ[R] C1 R :=
  Finsupp.lmapDomain R R (fun k : ℕ => -(d : ℤ) - k)

noncomputable def differential (d : ℕ) : C0 R →ₗ[R] C1 R :=
  (rightRestriction R d).comp (LinearMap.snd R _ _) -
    (leftRestriction R).comp (LinearMap.fst R _ _)

noncomputable def inclusionZero (d : ℕ) : H0 R d →ₗ[R] C0 R :=
  Finsupp.lsum R fun _ => (Finsupp.lsingle 0).prod (Finsupp.lsingle 0)

noncomputable def projectionZero (d : ℕ) : C0 R →ₗ[R] H0 R d :=
  if hd : d = 0 then
    (Finsupp.lsingle (⟨0, by simp [hd]⟩ : H0Index d)).comp
      ((Finsupp.lapply 0).comp (LinearMap.snd R _ _))
  else 0

noncomputable def inclusionOne (d : ℕ) : H1 R d →ₗ[R] C1 R :=
  Finsupp.lmapDomain R R fun k => -(k : ℤ) - 1

private def gapIndex (d : ℕ) (z : ℤ) (hz : -(d : ℤ) < z ∧ z < 0) : H1Index d :=
  ⟨(-z - 1).toNat, by omega⟩

noncomputable def projectionOne (d : ℕ) : C1 R →ₗ[R] H1 R d :=
  Finsupp.lsum R fun z =>
    if hz : -(d : ℤ) < z ∧ z < 0 then Finsupp.lsingle (gapIndex d z hz) else 0

noncomputable def homotopy (d : ℕ) : C1 R →ₗ[R] C0 R :=
  Finsupp.lsum R fun z =>
    if 0 ≤ z then (-Finsupp.lsingle z.toNat).prod 0
    else if z ≤ -(d : ℤ) then (0 : R →ₗ[R] ℕ →₀ R).prod
      (Finsupp.lsingle (- (d : ℤ) - z).toNat)
    else 0

@[simp] theorem differential_left_single (d k : ℕ) (r : R) :
    differential R d (single k r, 0) = -single (k : ℤ) r := by
  simp [differential, leftRestriction, rightRestriction]

@[simp] theorem differential_right_single (d k : ℕ) (r : R) :
    differential R d (0, single k r) = single (-(d : ℤ) - k) r := by
  simp [differential, leftRestriction, rightRestriction]

@[simp] theorem inclusionZero_single (d : ℕ) (k : H0Index d) (r : R) :
    inclusionZero R d (single k r) = (single 0 r, single 0 r) := by
  simp [inclusionZero, Finsupp.lsum_single]

@[simp] theorem inclusionOne_single (d : ℕ) (k : H1Index d) (r : R) :
    inclusionOne R d (single k r) = single (-(k : ℤ) - 1) r := by
  simp [inclusionOne]

theorem homotopy_single (d : ℕ) (z : ℤ) (r : R) :
    homotopy R d (single z r) =
      if 0 ≤ z then (-single z.toNat r, 0)
      else if z ≤ -(d : ℤ) then (0, single (-(d : ℤ) - z).toNat r)
      else 0 := by
  simp only [homotopy, Finsupp.lsum_single]
  split_ifs <;> rfl

theorem projectionOne_single_of_not_gap (d : ℕ) (z : ℤ) (r : R)
    (hz : ¬ (-(d : ℤ) < z ∧ z < 0)) :
    projectionOne R d (single z r) = 0 := by
  simp only [projectionOne, Finsupp.lsum_single, dite_eq_right hz, LinearMap.zero_apply]

private theorem projectionOne_single_of_gap (d : ℕ) (z : ℤ) (r : R)
    (hz : -(d : ℤ) < z ∧ z < 0) :
    projectionOne R d (single z r) = single (gapIndex d z hz) r := by
  simp only [projectionOne, Finsupp.lsum_single, dite_eq_left hz, Finsupp.lsingle_apply]

theorem homotopy_single_nonneg (d : ℕ) (z : ℤ) (r : R) (hz : 0 ≤ z) :
    homotopy R d (single z r) = (-single z.toNat r, 0) := by
  rw [homotopy_single, ite_eq_left hz]

theorem homotopy_single_nonpos (d : ℕ) (z : ℤ) (r : R)
    (hz : z < 0) (hd : z ≤ -(d : ℤ)) :
    homotopy R d (single z r) = (0, single (-(d : ℤ) - z).toNat r) := by
  rw [homotopy_single, ite_eq_right (by omega), ite_eq_left hd]

theorem homotopy_single_gap (d : ℕ) (z : ℤ) (r : R)
    (hz : -(d : ℤ) < z ∧ z < 0) : homotopy R d (single z r) = 0 := by
  rw [homotopy_single, ite_eq_right (by omega), ite_eq_right (by omega)]

@[simp] theorem projectionZero_zero_apply (a : C0 R) :
    projectionZero R 0 a = single (⟨0, by simp⟩ : H0Index 0) (a.2 0) := by
  unfold projectionZero
  split
  · rfl
  · contradiction

@[simp] theorem projectionZero_left (d : ℕ) (a : ℕ →₀ R) :
    projectionZero R d (a, 0) = 0 := by
  by_cases hd : d = 0 <;> simp [projectionZero, hd]

theorem projectionZero_right_single_ne (d k : ℕ) (r : R) (hk : k ≠ 0) :
    projectionZero R d (0, single k r) = 0 := by
  by_cases hd : d = 0 <;> simp [projectionZero, hd, Finsupp.single_eq_of_ne hk.symm]

theorem projectionZero_of_ne_zero (d : ℕ) (hd : d ≠ 0) : projectionZero R d = 0 := by
  rw [projectionZero, dite_eq_right hd]

private theorem zeroIndex_degree {d : ℕ} (k : H0Index d) : d = 0 := by
  by_contra h
  simpa [H0Index, h] using k.isLt

@[simp] theorem projectionOne_inclusionOne (d : ℕ) :
    (projectionOne R d).comp (inclusionOne R d) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro k r
  have hz : -(d : ℤ) < -(k : ℤ) - 1 ∧ -(k : ℤ) - 1 < 0 := by
    have := k.isLt
    omega
  simp only [LinearMap.comp_apply, inclusionOne_single, projectionOne,
    Finsupp.lsum_single, dite_eq_left hz, Finsupp.lsingle_apply, LinearMap.id_apply]
  congr 1
  apply Fin.ext
  simp [gapIndex]

@[simp] theorem projectionZero_inclusionZero (d : ℕ) :
    (projectionZero R d).comp (inclusionZero R d) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro k r
  obtain rfl := zeroIndex_degree k
  have hk : k = (⟨0, by simp⟩ : H0Index 0) := by
    apply Fin.ext
    change k.val = 0
    have h : k.val < 1 := by simpa only [H0Index, ite_true] using k.isLt
    omega
  change projectionZero R 0 (inclusionZero R 0 (single k r)) = single k r
  rw [inclusionZero_single, projectionZero_zero_apply, Finsupp.single_eq_same, hk]

@[simp] theorem differential_inclusionZero (d : ℕ) :
    (differential R d).comp (inclusionZero R d) = 0 := by
  apply Finsupp.lhom_ext
  intro k r
  obtain rfl := zeroIndex_degree k
  simp [differential, leftRestriction, rightRestriction]

@[simp] theorem projectionOne_differential (d : ℕ) :
    (projectionOne R d).comp (differential R d) = 0 := by
  apply LinearMap.prod_ext <;> apply Finsupp.lhom_ext <;> intro k r
  · have hz : ¬ (-(d : ℤ) < (k : ℤ) ∧ (k : ℤ) < 0) := by omega
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, differential_left_single,
      map_neg, projectionOne_single_of_not_gap R d k r hz, neg_zero,
      LinearMap.zero_apply]
  · have hz : ¬ (-(d : ℤ) < -(d : ℤ) - k ∧ -(d : ℤ) - k < 0) := by omega
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, differential_right_single,
      projectionOne_single_of_not_gap R d (-(d : ℤ) - k) r hz, LinearMap.zero_apply]

@[simp] theorem homotopy_inclusionOne (d : ℕ) :
    (homotopy R d).comp (inclusionOne R d) = 0 := by
  apply Finsupp.lhom_ext
  intro k r
  have hk := k.isLt
  have hz : -(d : ℤ) < -(k : ℤ) - 1 ∧ -(k : ℤ) - 1 < 0 := by omega
  simpa only [LinearMap.comp_apply, inclusionOne_single, LinearMap.zero_apply] using
    homotopy_single_gap R d (-(k : ℤ) - 1) r hz

@[simp] theorem projectionZero_homotopy (d : ℕ) :
    (projectionZero R d).comp (homotopy R d) = 0 := by
  apply Finsupp.lhom_ext
  intro z r
  by_cases hd : d = 0
  · subst d
    by_cases hz : 0 ≤ z
    · simp only [LinearMap.comp_apply, homotopy_single_nonneg R 0 z r hz,
        projectionZero_left, LinearMap.zero_apply]
    · have hz' : z < 0 := by omega
      have hn : (-z).toNat ≠ 0 := by omega
      simp only [LinearMap.comp_apply,
        homotopy_single_nonpos R 0 z r hz' (by omega), Nat.cast_zero, neg_zero, zero_sub,
        projectionZero_right_single_ne R 0 (-z).toNat r hn, LinearMap.zero_apply]
  · rw [projectionZero_of_ne_zero R d hd]
    simp

/-- Degree-one part of the contraction. -/
theorem differential_homotopy (d : ℕ) :
    (differential R d).comp (homotopy R d) =
      LinearMap.id - (inclusionOne R d).comp (projectionOne R d) := by
  apply Finsupp.lhom_ext
  intro z r
  change differential R d (homotopy R d (single z r)) =
    single z r - inclusionOne R d (projectionOne R d (single z r))
  by_cases hpos : 0 ≤ z
  · have hgap : ¬ (-(d : ℤ) < z ∧ z < 0) := by omega
    have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hpos
    rw [homotopy_single_nonneg R d z r hpos,
      projectionOne_single_of_not_gap R d z r hgap, map_zero, sub_zero]
    have hpair : (-single z.toNat r, (0 : ℕ →₀ R)) = -(single z.toNat r, 0) := by simp
    rw [hpair, map_neg, differential_left_single, neg_neg, hz]
  · by_cases hneg : z ≤ -(d : ℤ)
    · have hgap : ¬ (-(d : ℤ) < z ∧ z < 0) := by omega
      have hn : (0 : ℤ) ≤ -(d : ℤ) - z := by omega
      have hz : -(d : ℤ) - ((-(d : ℤ) - z).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg hn]
        omega
      rw [homotopy_single_nonpos R d z r (by omega) hneg,
        projectionOne_single_of_not_gap R d z r hgap, map_zero, sub_zero,
        differential_right_single, hz]
    · have hgap : -(d : ℤ) < z ∧ z < 0 := by omega
      have hz : -(gapIndex d z hgap : ℤ) - 1 = z := by
        simp only [gapIndex]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [homotopy_single_gap R d z r hgap, map_zero,
        projectionOne_single_of_gap R d z r hgap, inclusionOne_single, hz, sub_self]

/-- Degree-zero part of the contraction. -/
theorem homotopy_differential (d : ℕ) :
    (homotopy R d).comp (differential R d) =
      LinearMap.id - (inclusionZero R d).comp (projectionZero R d) := by
  apply LinearMap.prod_ext <;> apply Finsupp.lhom_ext <;> intro k r
  · change homotopy R d (differential R d (single k r, 0)) =
      (single k r, 0) - inclusionZero R d (projectionZero R d (single k r, 0))
    rw [differential_left_single, map_neg,
      homotopy_single_nonneg R d k r (by omega), projectionZero_left, map_zero]
    simp
  · change homotopy R d (differential R d (0, single k r)) =
      (0, single k r) - inclusionZero R d (projectionZero R d (0, single k r))
    rw [differential_right_single]
    by_cases hz : -(d : ℤ) - k = 0
    · have hd : d = 0 := by omega
      have hk : k = 0 := by omega
      subst d k
      rw [homotopy_single_nonneg R 0 _ r (by norm_num)]
      rw [projectionZero_zero_apply, Finsupp.single_eq_same, inclusionZero_single]
      simp
    · have hpos : ¬ 0 ≤ -(d : ℤ) - k := by omega
      have hneg : -(d : ℤ) - k ≤ -(d : ℤ) := by omega
      have hcast : (-(d : ℤ) - (-(d : ℤ) - k)).toNat = k := by omega
      rw [homotopy_single_nonpos R d _ r (by omega) hneg, hcast]
      by_cases hd : d = 0
      · have hk : k ≠ 0 := by omega
        rw [projectionZero_right_single_ne R d k r hk, map_zero, sub_zero]
      · rw [projectionZero_of_ne_zero R d hd]
        simp

/-! ## Multiplication by homogeneous monomials -/

/-- Homogeneous monomial shifting left degree by a and right degree by b. -/
noncomputable def multiplyZero (a b : ℕ) : C0 R →ₗ[R] C0 R :=
  (Finsupp.lmapDomain R R fun k : ℕ => k + a).prodMap
    (Finsupp.lmapDomain R R fun k : ℕ => k + b)

/-- Use the left exponent on the common torus. -/
noncomputable def multiplyOne (a : ℕ) : C1 R →ₗ[R] C1 R :=
  Finsupp.lmapDomain R R fun z : ℤ => z + a

@[simp] theorem multiplyZero_left_single (a b k : ℕ) (r : R) :
    multiplyZero R a b (single k r, 0) = (single (k + a) r, 0) := by
  simp [multiplyZero]

@[simp] theorem multiplyZero_right_single (a b k : ℕ) (r : R) :
    multiplyZero R a b (0, single k r) = (0, single (k + b) r) := by
  simp [multiplyZero]

@[simp] theorem multiplyOne_single (a : ℕ) (z : ℤ) (r : R) :
    multiplyOne R a (single z r) = single (z + a) r := by
  simp [multiplyOne]

/-- If a+b≤d, a homogeneous monomial induces a Čech map O(−d)→O(−(d−a−b)). -/
theorem multiply_chainMap (d a b : ℕ) (hab : a + b ≤ d) :
    (differential R (d - (a + b))).comp (multiplyZero R a b) =
      (multiplyOne R a).comp (differential R d) := by
  apply LinearMap.prod_ext <;> apply Finsupp.lhom_ext <;> intro k r
  · simp only [LinearMap.comp_apply, LinearMap.inl_apply, multiplyZero_left_single,
      differential_left_single, map_neg, multiplyOne_single, Nat.cast_add]
  · have hcast : -((d - (a + b) : ℕ) : ℤ) - (k + b) = -(d : ℤ) - k + a := by omega
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, multiplyZero_right_single,
      differential_right_single, multiplyOne_single, Nat.cast_add, hcast]

@[simp] theorem multiplyZero_zero : multiplyZero R 0 0 = LinearMap.id := by
  apply LinearMap.prod_ext <;> apply Finsupp.lhom_ext <;> intro k r <;> simp

@[simp] theorem multiplyOne_zero : multiplyOne R 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z r
  simp

theorem multiplyZero_comp (a b a' b' : ℕ) :
    (multiplyZero R a b).comp (multiplyZero R a' b') =
      multiplyZero R (a + a') (b + b') := by
  apply LinearMap.prod_ext <;> apply Finsupp.lhom_ext <;> intro k r <;>
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem multiplyOne_comp (a a' : ℕ) :
    (multiplyOne R a).comp (multiplyOne R a') = multiplyOne R (a + a') := by
  apply Finsupp.lhom_ext
  intro z r
  simp [add_assoc, add_comm, add_left_comm]

theorem multiplyZero_commute (a b a' b' : ℕ) :
    (multiplyZero R a b).comp (multiplyZero R a' b') =
      (multiplyZero R a' b').comp (multiplyZero R a b) := by
  rw [multiplyZero_comp, multiplyZero_comp, Nat.add_comm a a', Nat.add_comm b b']

theorem multiplyOne_commute (a a' : ℕ) :
    (multiplyOne R a).comp (multiplyOne R a') =
      (multiplyOne R a').comp (multiplyOne R a) := by
  rw [multiplyOne_comp, multiplyOne_comp, Nat.add_comm]

end BPFixedPoints.CechLine
