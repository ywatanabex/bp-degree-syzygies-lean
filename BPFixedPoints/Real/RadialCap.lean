import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Radial map to a sphere, smooth near the origin

A smooth map equal to radial projection onto the radius-R sphere outside a
positive δ, and linear near the origin.
-/

namespace BPFixedPoints

open Metric Set Filter Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def radialCap (R δ : ℝ) (hδ : 0 < δ) (x : E) : E :=
  let χ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, by linarith⟩
  (R * (χ x / δ + (1 - χ x) / ‖x‖)) • x

theorem radialCap_eq_of_le {R δ : ℝ} (hδ : 0 < δ) {x : E} (hx : δ ≤ ‖x‖) :
    radialCap R δ hδ x = (R / ‖x‖) • x := by
  let χ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, by linarith⟩
  have hχ : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
  simp only [radialCap, show
    (⟨δ / 2, δ, half_pos hδ, by linarith⟩ : ContDiffBump (0 : E)) = χ from rfl, hχ]
  simp [div_eq_mul_inv]

theorem norm_radialCap_of_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) {x : E}
    (hx : δ ≤ ‖x‖) : ‖radialCap R δ hδ x‖ = R := by
  have hx0 : ‖x‖ ≠ 0 := (hδ.trans_le hx).ne'
  rw [radialCap_eq_of_le hδ hx, norm_smul, Real.norm_eq_abs,
    abs_div, abs_of_nonneg hR, abs_norm, div_mul_cancel₀ _ hx0]

theorem norm_radialCap_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (x : E) :
    ‖radialCap R δ hδ x‖ ≤ R := by
  by_cases hx : δ ≤ ‖x‖
  · exact (norm_radialCap_of_le hR hδ hx).le
  have hxδ : ‖x‖ ≤ δ := (not_le.1 hx).le
  let χ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, by linarith⟩
  change ‖(R * (χ x / δ + (1 - χ x) / ‖x‖)) • x‖ ≤ R
  have hχ0 : 0 ≤ χ x := χ.nonneg
  have hχ1 : χ x ≤ 1 := χ.le_one
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hx0 : ‖x‖ = 0
  · simp [hx0, hR]
  have heq : R * (χ x / δ + (1 - χ x) / ‖x‖) * ‖x‖ =
      R * (χ x * (‖x‖ / δ) + (1 - χ x)) := by field_simp
  rw [heq]
  have hratio : ‖x‖ / δ ≤ 1 := (div_le_one hδ).2 hxδ
  have hprod : χ x * (‖x‖ / δ) ≤ χ x := by simpa using mul_le_mul_of_nonneg_left hratio hχ0
  calc R * (χ x * (‖x‖ / δ) + (1 - χ x)) ≤ R * 1 := by gcongr; linarith
    _ = R := mul_one _

theorem contDiff_radialCap (R : ℝ) {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ n (radialCap (E := E) R δ hδ) := by
  let χ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, by linarith⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hloc : radialCap (E := E) R δ hδ =ᶠ[𝓝 0] fun x => (R / δ) • x := by
      filter_upwards [χ.eventuallyEq_one] with y hy
      change (R * (χ y / δ + (1 - χ y) / ‖y‖)) • y = (R / δ) • y
      simp only [hy, Pi.one_apply, sub_self, zero_div, add_zero]
      congr 1
      ring
    exact (contDiffAt_const.smul contDiffAt_id).congr_of_eventuallyEq hloc
  · change ContDiffAt ℝ n (fun y => (R * (χ y / δ + (1 - χ y) / ‖y‖)) • y) x
    exact (contDiffAt_const.mul ((χ.contDiffAt.div_const δ).add
      ((contDiffAt_const.sub χ.contDiffAt).div (contDiffAt_norm ℝ hx)
        (norm_ne_zero_iff.2 hx)))).smul contDiffAt_id

/-- A map with locally constant positive norm has singular derivative. -/
theorem det_fderiv_eq_zero_of_norm_eventually_const {r : E → E} {R : ℝ} {x : E}
    (hR : 0 < R) (hr : DifferentiableAt ℝ r x) (hnorm : ∀ᶠ y in 𝓝 x, ‖r y‖ = R) :
    (fderiv ℝ r x).det = 0 := by
  set L := fderiv ℝ r x with hL
  have hd : HasFDerivAt r L x := hr.hasFDerivAt
  have hinner := hd.inner ℝ hd
  have hconst : (fun y => ⟪r y, r y⟫_ℝ) =ᶠ[𝓝 x] fun _ => R ^ 2 := by
    filter_upwards [hnorm] with y hy
    rw [real_inner_self_eq_norm_sq, hy]
  have hinner0 : HasFDerivAt (fun y => ⟪r y, r y⟫_ℝ) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (R ^ 2) x).congr_of_eventuallyEq hconst
  have h0 := hinner.unique hinner0
  have horth : ∀ v, ⟪r x, L v⟫_ℝ = 0 := by
    intro v
    have := congrArg (fun T : E →L[ℝ] ℝ => T v) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, zero_apply] at this
    have hc := real_inner_comm (L v) (r x)
    linarith
  by_contra hdet
  have hunit : IsUnit (L : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨v, hv⟩ := ((Module.End.isUnit_iff _).1 hunit).2 (r x)
  have h1 := horth v
  change ⟪r x, (L : E →ₗ[ℝ] E) v⟫_ℝ = 0 at h1
  rw [hv, real_inner_self_eq_norm_sq, hnorm.self_of_nhds] at h1
  have : R ^ 2 > 0 := by positivity
  linarith

theorem det_fderiv_radialCap_eq_zero {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) {x : E}
    (hx : δ < ‖x‖) : (fderiv ℝ (radialCap (E := E) R δ hδ) x).det = 0 := by
  apply det_fderiv_eq_zero_of_norm_eventually_const hR
    ((contDiff_radialCap (n := 1) R hδ).differentiable one_ne_zero x)
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
  exact norm_radialCap_of_le hR.le hδ hy.le

end BPFixedPoints
