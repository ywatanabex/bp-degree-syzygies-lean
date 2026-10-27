import BPFixedPoints.Incidence.CechProduct
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Cup product on the two-chart Čech complex

Equip the existing O(−d) complex with the Alexander–Whitney product. Mixed
degree-zero/one terms use different left and right restrictions. It is
associative at chain level and satisfies signed Leibniz for the existing
differential. Products of two degree-one chains vanish because there is no
Čech degree-two term.
-/

namespace BPFixedPoints.CechLine

open Finsupp

variable {R : Type*} [CommRing R]

/-- Convolution of monomial coefficients, rather than pointwise multiplication. -/
noncomputable def convolution {M : Type*} [AddCommMonoid M]
    (x y : M →₀ R) : M →₀ R :=
  (AddMonoidAlgebra.ofCoeff x * AddMonoidAlgebra.ofCoeff y).coeff

section Convolution

variable {M : Type*} [AddCommMonoid M] (x y z : M →₀ R)

@[simp] theorem convolution_zero_left : convolution (0 : M →₀ R) x = 0 := by
  simp [convolution]
@[simp] theorem convolution_zero_right : convolution x (0 : M →₀ R) = 0 := by
  simp [convolution]
theorem convolution_add_left : convolution (x + y) z = convolution x z + convolution y z := by
  simp [convolution, add_mul]
theorem convolution_add_right : convolution x (y + z) = convolution x y + convolution x z := by
  simp [convolution, mul_add]
theorem convolution_sub_left : convolution (x - y) z = convolution x z - convolution y z := by
  simp [convolution, sub_mul]
theorem convolution_sub_right : convolution x (y - z) = convolution x y - convolution x z := by
  simp [convolution, mul_sub]
@[simp] theorem convolution_neg_left : convolution (-x) y = -convolution x y := by
  simp [convolution]
@[simp] theorem convolution_neg_right : convolution x (-y) = -convolution x y := by
  simp [convolution]
theorem convolution_smul_left (r : R) : convolution (r • x) y = r • convolution x y := by
  simp [convolution]
theorem convolution_smul_right (r : R) : convolution x (r • y) = r • convolution x y := by
  simp [convolution]
theorem convolution_assoc : convolution (convolution x y) z = convolution x (convolution y z) := by
  simp only [convolution, AddMonoidAlgebra.ofCoeff_coeff, mul_assoc]
theorem convolution_comm : convolution x y = convolution y x := by
  simp only [convolution, mul_comm]
@[simp] theorem convolution_single (m n : M) (r s : R) :
    convolution (single m r) (single n s) = single (m + n) (r * s) := by
  simp [convolution, AddMonoidAlgebra.single_mul_single]
@[simp] theorem convolution_one_left : convolution (single 0 1) x = x := by
  simp [convolution, ← AddMonoidAlgebra.one_def]
@[simp] theorem convolution_one_right : convolution x (single 0 1) = x := by
  rw [convolution_comm, convolution_one_left]

end Convolution

/-- Left restriction preserves the convolution product. -/
theorem leftRestriction_convolution (x y : ℕ →₀ R) :
    leftRestriction R (convolution x y) =
      convolution (leftRestriction R x) (leftRestriction R y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp [convolution_add_left, hx, hx']
  | single m r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp [convolution_add_right, hy, hy']
    | single n s =>
      simp only [convolution_single, leftRestriction, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, Nat.cast_add]

/-- The twist in right restriction is additive under products. -/
theorem rightRestriction_convolution (d e : ℕ) (x y : ℕ →₀ R) :
    rightRestriction R (d + e) (convolution x y) =
      convolution (rightRestriction R d x) (rightRestriction R e y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp [convolution_add_left, hx, hx']
  | single m r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp [convolution_add_right, hy, hy']
    | single n s =>
      simp only [convolution_single, rightRestriction, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single, Nat.cast_add]
      congr 1
      ring

/-- Čech cup product O(−d)⊗O(−e)→O(−(d+e)). Use the left endpoint when the right input has degree one, and the right endpoint when the left input has degree one. -/
noncomputable def cup (_d e : ℕ) (x y : CechProduct.LineC R) : CechProduct.LineC R :=
  ((convolution x.1.1 y.1.1, convolution x.1.2 y.1.2),
    convolution (leftRestriction R x.1.1) y.2 +
      convolution x.2 (rightRestriction R e y.1.2))

@[simp] theorem cup_zero_left (d e : ℕ) (x : CechProduct.LineC R) : cup d e 0 x = 0 := by
  simp [cup]
@[simp] theorem cup_zero_right (d e : ℕ) (x : CechProduct.LineC R) : cup d e x 0 = 0 := by
  simp [cup]
theorem cup_add_left (d e : ℕ) (x y z : CechProduct.LineC R) :
    cup d e (x + y) z = cup d e x z + cup d e y z := by
  simp only [cup, Prod.fst_add, Prod.snd_add, map_add, convolution_add_left,
    Prod.mk_add_mk]
  congr 1
  abel
theorem cup_add_right (d e : ℕ) (x y z : CechProduct.LineC R) :
    cup d e x (y + z) = cup d e x y + cup d e x z := by
  simp only [cup, Prod.fst_add, Prod.snd_add, map_add, convolution_add_right,
    Prod.mk_add_mk]
  congr 1
  abel

/-- The cup product is linear in both inputs. -/
noncomputable def cupLinear (d e : ℕ) :
    CechProduct.LineC R →ₗ[R] CechProduct.LineC R →ₗ[R] CechProduct.LineC R where
  toFun x :=
    { toFun := cup d e x
      map_add' := cup_add_right d e x
      map_smul' := by
        intro r y
        simp [cup, convolution_smul_right, smul_add] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact cup_add_left d e x y z
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change cup d e (r • x) y = r • cup d e x y
    simp [cup, convolution_smul_left, smul_add]

/-- Signed Leibniz rule for the existing Čech differential. -/
theorem cup_leibniz (d e : ℕ) (x y : CechProduct.LineC R) :
    CechProduct.lineD R (d + e) (cup d e x y) =
      cup d e (CechProduct.lineD R d x) y +
        cup d e (CechProduct.lineSign R x) (CechProduct.lineD R e y) := by
  simp only [CechProduct.lineD_apply, CechProduct.lineSign_apply, cup,
    differential, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, rightRestriction_convolution, leftRestriction_convolution,
    Prod.fst_zero, Prod.snd_zero, map_zero, convolution_zero_left, convolution_zero_right,
    zero_add, add_zero, convolution_sub_left, convolution_sub_right, Prod.mk_add_mk]
  congr 1
  abel

/-- Chain-level associativity, including twists. -/
theorem cup_assoc (d e f : ℕ) (x y z : CechProduct.LineC R) :
    cup (d + e) f (cup d e x y) z = cup d (e + f) x (cup e f y z) := by
  simp only [cup, leftRestriction_convolution, rightRestriction_convolution,
    convolution_add_left, convolution_add_right, convolution_assoc]
  congr 1
  abel

/-- Constant section of the trivial bundle. -/
noncomputable def cupUnit : CechProduct.LineC R := ((single 0 1, single 0 1), 0)

@[simp] theorem cup_unit_left (d : ℕ) (x : CechProduct.LineC R) : cup 0 d cupUnit x = x := by
  simp [cup, cupUnit, leftRestriction]
@[simp] theorem cup_unit_right (d : ℕ) (x : CechProduct.LineC R) : cup d 0 x cupUnit = x := by
  simp [cup, cupUnit, rightRestriction]

/-- Products of degree-one Čech classes vanish already at chain level. -/
@[simp] theorem cup_one_one (d e : ℕ) (x y : C1 R) :
    cup d e (0, x) (0, y) = 0 := by simp [cup]

/-- Products of cocycles are cocycles. -/
theorem cup_cycles (d e : ℕ) {x y : CechProduct.LineC R}
    (hx : CechProduct.lineD R d x = 0) (hy : CechProduct.lineD R e y = 0) :
    CechProduct.lineD R (d + e) (cup d e x y) = 0 := by
  rw [cup_leibniz, hx, hy, cup_zero_left, cup_zero_right, add_zero]

end BPFixedPoints.CechLine
