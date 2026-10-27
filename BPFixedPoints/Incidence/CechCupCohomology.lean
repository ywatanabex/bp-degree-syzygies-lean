import BPFixedPoints.Incidence.CechCup

/-!
# Descent of the cup product to explicit Čech cohomology

Project products of cocycles using the existing contraction `line`. Prove that
products with boundaries project to zero and are independent of representatives.
This is the product for O(−d) on one vertex; it does not assert comparison
with multi-vertex Koszul–Čech products or the derived incidence Tor product.
-/

namespace BPFixedPoints.CechLine

open CechProduct

variable {R : Type*} [CommRing R]

theorem lineP_lineD (d : ℕ) (x : LineC R) : lineP R d (lineD R d x) = 0 :=
  LinearMap.congr_fun (line R d).p_d x

theorem lineD_lineI (d : ℕ) (x : LineH R d) : lineD R d (lineI R d x) = 0 :=
  LinearMap.congr_fun (line R d).d_i x

theorem lineP_lineI (d : ℕ) (x : LineH R d) : lineP R d (lineI R d x) = x :=
  LinearMap.congr_fun (line R d).p_i x

theorem lineP_heq {d e : ℕ} (h : d = e) (x : LineC R) :
    HEq (lineP R d x) (lineP R e x) := by
  subst e
  rfl

theorem lineD_lineSign (d : ℕ) (x : LineC R) :
    lineD R d (lineSign R x) = -lineSign R (lineD R d x) := by
  simp [lineD_apply, lineSign_apply]

theorem lineSign_lineSign (x : LineC R) : lineSign R (lineSign R x) = x := by
  simp [lineSign_apply]

/-- A product of a cocycle and a boundary is a boundary. -/
theorem cup_boundary_left (d e : ℕ) (x : LineC R) {y : LineC R}
    (hy : lineD R e y = 0) :
    cup d e (lineD R d x) y = lineD R (d + e) (cup d e x y) := by
  rw [cup_leibniz, hy, cup_zero_right, add_zero]

theorem cup_boundary_right (d e : ℕ) {x : LineC R} (y : LineC R)
    (hx : lineD R d x = 0) :
    cup d e x (lineD R e y) = lineD R (d + e) (cup d e (lineSign R x) y) := by
  rw [cup_leibniz, lineD_lineSign, hx, map_zero, neg_zero, cup_zero_left,
    zero_add, lineSign_lineSign]

theorem lineP_cup_boundary_left (d e : ℕ) (x : LineC R) {y : LineC R}
    (hy : lineD R e y = 0) : lineP R (d + e) (cup d e (lineD R d x) y) = 0 := by
  rw [cup_boundary_left d e x hy, lineP_lineD]

theorem lineP_cup_boundary_right (d e : ℕ) {x : LineC R} (y : LineC R)
    (hx : lineD R d x = 0) : lineP R (d + e) (cup d e x (lineD R e y)) = 0 := by
  rw [cup_boundary_right d e y hx, lineP_lineD]

/-- Decompose a cocycle into a boundary and its chosen representative using the contraction identity. -/
theorem line_cycle_decomposition (d : ℕ) {x : LineC R} (hx : lineD R d x = 0) :
    x = lineD R d (lineH R d x) + lineI R d (lineP R d x) := by
  have h := LinearMap.congr_fun (line R d).homotopy x
  change lineD R d (lineH R d x) + lineH R d (lineD R d x) +
    lineI R d (lineP R d x) = x at h
  simpa only [hx, map_zero, add_zero] using h.symm

/-- Cup product descending to the existing finite basis. -/
noncomputable def cohomologyCup (d e : ℕ) (x : LineH R d) (y : LineH R e) :
    LineH R (d + e) := lineP R (d + e) (cup d e (lineI R d x) (lineI R e y))

/-- Every cocycle representative gives the same cohomology product. -/
theorem cohomologyCup_projection (d e : ℕ) {x y : LineC R}
    (hx : lineD R d x = 0) (hy : lineD R e y = 0) :
    cohomologyCup d e (lineP R d x) (lineP R e y) =
      lineP R (d + e) (cup d e x y) := by
  have hleft : lineP R (d + e) (cup d e x y) =
      lineP R (d + e) (cup d e (lineI R d (lineP R d x)) y) := by
    nth_rw 1 [line_cycle_decomposition d hx]
    rw [cup_add_left, map_add, lineP_cup_boundary_left d e _ hy, zero_add]
  rw [hleft]
  unfold cohomologyCup
  nth_rw 2 [line_cycle_decomposition e hy]
  rw [cup_add_right, map_add,
    lineP_cup_boundary_right d e _ (lineD_lineI d _), zero_add]

/-- Cocycles in the same cohomology classes give equal products. -/
theorem lineP_cup_eq_of_same_class (d e : ℕ) {x x' y y' : LineC R}
    (hx : lineD R d x = 0) (hx' : lineD R d x' = 0)
    (hy : lineD R e y = 0) (hy' : lineD R e y' = 0)
    (hxx : lineP R d x = lineP R d x') (hyy : lineP R e y = lineP R e y') :
    lineP R (d + e) (cup d e x y) = lineP R (d + e) (cup d e x' y') := by
  rw [← cohomologyCup_projection d e hx hy, ← cohomologyCup_projection d e hx' hy',
    hxx, hyy]

/-- The cup product of degree-one cohomology classes is zero. -/
theorem cohomologyCup_one_one (d e : ℕ) (x : H1 R d) (y : H1 R e) :
    cohomologyCup d e (0, x) (0, y) = 0 := by
  simp [cohomologyCup, lineI_apply]

/-- Cohomological associativity, including the type identification for adding twists. -/
theorem cohomologyCup_assoc (d e f : ℕ) (x : LineH R d) (y : LineH R e)
    (z : LineH R f) :
    HEq (cohomologyCup (d + e) f (cohomologyCup d e x y) z)
      (cohomologyCup d (e + f) x (cohomologyCup e f y z)) := by
  have hl := cohomologyCup_projection (d + e) f
    (cup_cycles d e (lineD_lineI d x) (lineD_lineI e y)) (lineD_lineI f z)
  have hr := cohomologyCup_projection d (e + f)
    (lineD_lineI d x) (cup_cycles e f (lineD_lineI e y) (lineD_lineI f z))
  simp only [lineP_lineI] at hl hr
  change cohomologyCup (d + e) f (cohomologyCup d e x y) z = _ at hl
  change cohomologyCup d (e + f) x (cohomologyCup e f y z) = _ at hr
  rw [hl, hr]
  rw [cup_assoc]
  exact lineP_heq (Nat.add_assoc d e f) _

/-- The cohomology unit is the class of the actual constant section. -/
noncomputable def cohomologyCupUnit : LineH R 0 := lineP R 0 cupUnit

theorem lineI_cohomologyCupUnit : lineI R 0 (cohomologyCupUnit (R := R)) = cupUnit := by
  change (inclusionZero R 0 (projectionZero R 0 (Finsupp.single 0 1, Finsupp.single 0 1)),
    inclusionOne R 0 (projectionOne R 0 0)) = _
  rw [projectionZero_zero_apply, Finsupp.single_eq_same, inclusionZero_single]
  simp only [map_zero]
  rfl

theorem cohomologyCup_unit_left (d : ℕ) (x : LineH R d) :
    HEq (cohomologyCup 0 d cohomologyCupUnit x) x := by
  simp only [cohomologyCup, lineI_cohomologyCupUnit, cup_unit_left]
  exact (lineP_heq (Nat.zero_add d) _).trans (heq_of_eq (lineP_lineI d x))

theorem cohomologyCup_unit_right (d : ℕ) (x : LineH R d) :
    cohomologyCup d 0 x cohomologyCupUnit = x := by
  simp only [cohomologyCup, lineI_cohomologyCupUnit, cup_unit_right]
  exact lineP_lineI d x

/-- If both twists are positive at a vertex, the local cup product vanishes: the local part of the multi-vertex overlap-vanishing rule. -/
theorem cohomologyCup_eq_zero_of_pos (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (x : LineH R d) (y : LineH R e) : cohomologyCup d e x y = 0 := by
  have hx0 : x.1 = 0 := by
    ext i
    have hi := i.isLt
    simp only [ite_eq_right (Nat.ne_of_gt hd)] at hi
    omega
  have hy0 : y.1 = 0 := by
    ext i
    have hi := i.isLt
    simp only [ite_eq_right (Nat.ne_of_gt he)] at hi
    omega
  have hx : x = (0, x.2) := Prod.ext hx0 rfl
  have hy : y = (0, y.2) := Prod.ext hy0 rfl
  rw [hx, hy, cohomologyCup_one_one]

end BPFixedPoints.CechLine
