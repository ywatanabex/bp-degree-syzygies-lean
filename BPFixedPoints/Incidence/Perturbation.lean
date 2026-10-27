import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic identities for finite homological perturbation

Lemmas for adding a Koszul differential to a strong Čech contraction.
When perturbation composed with homotopy is nilpotent, the inverse is a finite
sum. First prove the identities in any possibly noncommutative ring.
-/

namespace BPFixedPoints.IncidencePerturbation

section Ring

variable {A : Type*} [Ring A]

/-- Operator equal to the finite perturbation geometric series. -/
noncomputable def correction (δ h : A) : A := Ring.inverse (1 + δ * h) * δ

theorem correction_left (δ h : A) (hu : IsUnit (1 + δ * h)) :
    (1 + δ * h) * correction δ h = δ := by
  rw [correction, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]

theorem correction_right (δ h : A) (hu : IsUnit (1 + δ * h)) :
    correction δ h * (1 + h * δ) = δ := by
  apply hu.mul_left_cancel
  calc
    (1 + δ * h) * (correction δ h * (1 + h * δ)) =
        ((1 + δ * h) * correction δ h) * (1 + h * δ) := by simp [mul_assoc]
    _ = δ * (1 + h * δ) := by rw [correction_left δ h hu]
    _ = (1 + δ * h) * δ := by noncomm_ring

theorem correction_eq_add_left (δ h : A) (hu : IsUnit (1 + δ * h)) :
    correction δ h + δ * h * correction δ h = δ := by
  simpa only [add_mul, one_mul] using correction_left δ h hu

theorem correction_eq_add_right (δ h : A) (hu : IsUnit (1 + δ * h)) :
    correction δ h + correction δ h * h * δ = δ := by
  simpa only [mul_add, mul_one, mul_assoc] using correction_right δ h hu

/-- Perturbed Maurer–Cartan identity. -/
theorem correction_identity (d h e δ : A)
    (hd : d * d = 0) (hD : (d + δ) * (d + δ) = 0)
    (hc : d * h + h * d + e = 1)
    (hu : IsUnit (1 + δ * h)) (hv : IsUnit (1 + h * δ)) :
    d * correction δ h + correction δ h * d +
      correction δ h * e * correction δ h = 0 := by
  apply hu.mul_left_cancel
  apply hv.mul_right_cancel
  calc
    (1 + δ * h) * (d * correction δ h + correction δ h * d +
        correction δ h * e * correction δ h) * (1 + h * δ) =
      (1 + δ * h) * d * (correction δ h * (1 + h * δ)) +
        ((1 + δ * h) * correction δ h) * d * (1 + h * δ) +
        ((1 + δ * h) * correction δ h) * e *
          (correction δ h * (1 + h * δ)) := by noncomm_ring
    _ = (1 + δ * h) * d * δ + δ * d * (1 + h * δ) + δ * e * δ := by
      rw [correction_left δ h hu, correction_right δ h hu]
    _ = d * δ + δ * d + δ * (d * h + h * d + e) * δ := by noncomm_ring
    _ = (d + δ) * (d + δ) - d * d := by rw [hc]; noncomm_ring
    _ = (1 + δ * h) * 0 * (1 + h * δ) := by rw [hD, hd]; simp

theorem perturb_inclusion_identity (d h e δ a : A)
    (hc : d * h + h * d + e = 1)
    (ha : a + δ * h * a = δ)
    (hm : d * a + a * d + a * e * a = 0) :
    (d + δ) * (1 - h * a) = (1 - h * a) * (d + e * a) := by
  linear_combination (norm := noncomm_ring) -ha - hc * a + h * hm

theorem perturb_projection_identity (d h e δ a : A)
    (hc : d * h + h * d + e = 1)
    (ha : a + a * h * δ = δ)
    (hm : d * a + a * d + a * e * a = 0) :
    (1 - a * h) * (d + δ) = (d + a * e) * (1 - a * h) := by
  linear_combination (norm := noncomm_ring) -ha - a * hc + hm * h

theorem perturb_homotopy_identity (d h e δ a : A)
    (hc : d * h + h * d + e = 1)
    (hal : a + δ * h * a = δ)
    (har : a + a * h * δ = δ)
    (hm : d * a + a * d + a * e * a = 0) :
    (d + δ) * (h - h * a * h) + (h - h * a * h) * (d + δ) +
      (1 - h * a) * e * (1 - a * h) = 1 := by
  linear_combination (norm := noncomm_ring)
    hc - hc * a * h - h * a * hc - hal * h - h * har + h * hm * h

end Ring

/-! ## Application to linear maps -/

/-- Strong contraction to a zero-differential module, with convention dh+hd=1−ip. -/
structure Contraction (R M H : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] where
  d : Module.End R M
  i : H →ₗ[R] M
  p : M →ₗ[R] H
  h : Module.End R M
  d_sq : d * d = 0
  d_i : d.comp i = 0
  p_d : p.comp d = 0
  p_i : p.comp i = LinearMap.id
  homotopy : d * h + h * d + i.comp p = 1
  h_sq : h * h = 0
  h_i : h.comp i = 0
  p_h : p.comp h = 0

namespace Contraction

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  (C : Contraction R M H) (δ : Module.End R M)

noncomputable def transfer : Module.End R H :=
  C.p.comp ((correction δ C.h).comp C.i)

noncomputable def inclusion : H →ₗ[R] M :=
  (1 - C.h * correction δ C.h).comp C.i

noncomputable def projection : M →ₗ[R] H :=
  C.p.comp (1 - correction δ C.h * C.h)

noncomputable def contractingHomotopy : Module.End R M :=
  C.h - C.h * correction δ C.h * C.h

theorem p_d_comp {N : Type*} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    C.p.comp (C.d.comp f) = 0 := by
  rw [← LinearMap.comp_assoc, C.p_d, LinearMap.zero_comp]

theorem p_h_comp {N : Type*} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    C.p.comp (C.h.comp f) = 0 := by
  rw [← LinearMap.comp_assoc, C.p_h, LinearMap.zero_comp]

theorem h_h_comp {N : Type*} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) :
    C.h.comp (C.h.comp f) = 0 := by
  rw [← LinearMap.comp_assoc]
  change (C.h * C.h).comp f = 0
  rw [C.h_sq, LinearMap.zero_comp]

variable (hD : (C.d + δ) * (C.d + δ) = 0)
  (hu : IsUnit (1 + δ * C.h)) (hv : IsUnit (1 + C.h * δ))

include hD hu hv in
theorem transfer_sq : C.transfer δ * C.transfer δ = 0 := by
  have hm := correction_identity C.d C.h (C.i.comp C.p) δ
    C.d_sq hD C.homotopy hu hv
  have he := congrArg (fun f : Module.End R M => C.p.comp (f.comp C.i)) hm
  simpa only [transfer, Module.End.mul_eq_comp, LinearMap.add_comp,
    LinearMap.comp_add, LinearMap.comp_assoc, C.p_d_comp, C.d_i,
    LinearMap.comp_zero, LinearMap.zero_comp, add_zero, zero_add] using he

include hD hu hv in
theorem inclusion_chain :
    (C.d + δ).comp (C.inclusion δ) = (C.inclusion δ).comp (C.transfer δ) := by
  have hm := correction_identity C.d C.h (C.i.comp C.p) δ
    C.d_sq hD C.homotopy hu hv
  have hi := perturb_inclusion_identity C.d C.h (C.i.comp C.p) δ (correction δ C.h)
    C.homotopy (correction_eq_add_left δ C.h hu) hm
  have he := congrArg (fun f : Module.End R M => f.comp C.i) hi
  simpa only [inclusion, transfer, Module.End.mul_eq_comp, LinearMap.add_comp,
    LinearMap.comp_add, LinearMap.comp_assoc, C.d_i, LinearMap.comp_zero,
    zero_add] using he

include hD hu hv in
theorem projection_chain :
    (C.projection δ).comp (C.d + δ) = (C.transfer δ).comp (C.projection δ) := by
  have hm := correction_identity C.d C.h (C.i.comp C.p) δ
    C.d_sq hD C.homotopy hu hv
  have hp := perturb_projection_identity C.d C.h (C.i.comp C.p) δ (correction δ C.h)
    C.homotopy (correction_eq_add_right δ C.h hu) hm
  have he := congrArg (fun f : Module.End R M => C.p.comp f) hp
  simpa only [projection, transfer, Module.End.mul_eq_comp, LinearMap.add_comp,
    LinearMap.comp_add, LinearMap.comp_assoc, C.p_d_comp, zero_add] using he

theorem projection_inclusion :
    (C.projection δ).comp (C.inclusion δ) = LinearMap.id := by
  simp only [projection, inclusion, Module.End.mul_eq_comp, Module.End.one_eq_id,
    LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc,
    LinearMap.id_comp, LinearMap.comp_id, C.h_i, C.p_h_comp, C.h_h_comp,
    LinearMap.comp_zero, sub_zero, C.p_i]

include hD hu hv in
theorem perturbed_homotopy :
    (C.d + δ) * C.contractingHomotopy δ + C.contractingHomotopy δ * (C.d + δ) +
      (C.inclusion δ).comp (C.projection δ) = 1 := by
  have hm := correction_identity C.d C.h (C.i.comp C.p) δ
    C.d_sq hD C.homotopy hu hv
  have hh := perturb_homotopy_identity C.d C.h (C.i.comp C.p) δ (correction δ C.h)
    C.homotopy (correction_eq_add_left δ C.h hu)
    (correction_eq_add_right δ C.h hu) hm
  simpa only [contractingHomotopy, inclusion, projection,
    Module.End.mul_eq_comp, LinearMap.comp_assoc] using hh

end Contraction

end BPFixedPoints.IncidencePerturbation
