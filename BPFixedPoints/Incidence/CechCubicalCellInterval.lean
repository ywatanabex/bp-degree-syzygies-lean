import BPFixedPoints.Incidence.CechTensor
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # The original binary-cover cell boundary and its endpoint contraction

Cells 0 and 1 are the original endpoints; cell 2 is their overlap edge.
The boundary is left minus right, dual to the original native restriction
difference. The base endpoint is specified explicitly. No sheaf cohomology
or desired state dimension is used in this elementary cell contraction.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable (R : Type*) [CommRing R]

/-- Free cells of the original interval. -/
abbrev Interval := Fin 3 →₀ R

/-- The free module on its single connected component. -/
abbrev Point := Fin 1 →₀ R

/-- The specified original left-minus-right cell boundary. -/
noncomputable def intervalD : Module.End R (Interval R) :=
  ((lsingle 0 : R →ₗ[R] Interval R) - lsingle 1).comp (lapply 2)

/-- The base endpoint is supplied as part of the contraction. -/
noncomputable def intervalI (b : Fin 2) : Point R →ₗ[R] Interval R :=
  (lsingle b.castSucc).comp (lapply 0)

/-- Augmentation is the original sum of endpoint coefficients. -/
noncomputable def intervalP : Interval R →ₗ[R] Point R :=
  (lsingle 0).comp (lapply 0 + lapply 1)

/-- The specified endpoint contraction fills the difference from that endpoint. -/
noncomputable def intervalH (b : Fin 2) : Module.End R (Interval R) :=
  (lsingle 2).comp (if b = 0 then -lapply 1 else lapply 0)

/-- Endpoint cells are even and the original overlap edge is odd. -/
noncomputable def intervalSign : Module.End R (Interval R) :=
  LinearMap.id - (2 : R) • ((lsingle 2).comp (lapply 2))

@[simp] theorem intervalD_apply (x : Interval R) :
    intervalD R x = single 0 (x 2) - single 1 (x 2) := rfl
@[simp] theorem intervalI_apply (b : Fin 2) (x : Point R) :
    intervalI R b x = single b.castSucc (x 0) := rfl
@[simp] theorem intervalP_apply (x : Interval R) :
    intervalP R x = single 0 (x 0+x 1) := rfl
@[simp] theorem intervalH_apply (b : Fin 2) (x : Interval R) :
    intervalH R b x = single 2 (if b = 0 then -(x 1) else x 0) := by
  fin_cases b <;> simp [intervalH]
@[simp] theorem intervalSign_apply (x : Interval R) :
    intervalSign R x = x - single 2 (2*x 2) := by simp [intervalSign]

/-- The original free interval has the specified strong contraction to its component. -/
noncomputable def interval (b : Fin 2) : GradedContraction R (Interval R) (Point R) where
  d := intervalD R
  h := intervalH R b
  i := intervalI R b
  p := intervalP R
  sign := intervalSign R
  signH := 1
  d_sq := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k <;> simp
  h_sq := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k <;> simp
  d_i := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp
  p_d := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k; simp
  p_i := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp
  h_i := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp
  p_h := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k; simp
  homotopy := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp <;> ring
  sign_sq := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k <;> simp <;> ring
  signH_sq := by simp
  sign_d := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k <;> simp <;> ring
  sign_h := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp <;> ring
  sign_i := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases b <;> fin_cases k <;> simp
  p_sign := by
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro k
    fin_cases k; simp

/-- The boundary of every original cell, with the original endpoint orientation. -/
theorem interval_d_single (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).d (single k r) =
      if k = 2 then single 0 r-single 1 r else 0 := by
  fin_cases k <;> simp [interval]

/-- Every original cell has its original overlap parity. -/
theorem interval_sign_single (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).sign (single k r) =
      (if k = 2 then (-1 : R) else 1) • single k r := by
  fin_cases k <;> ext j <;> fin_cases j <;> simp [interval] <;> ring

/-- The original component projection kills every positive-dimensional interval cell. -/
theorem interval_p_edge (b : Fin 2) (r : R) :
    (interval R b).p (single 2 r) = 0 := by simp [interval]

end BPFixedPoints.CechCubicalCell
