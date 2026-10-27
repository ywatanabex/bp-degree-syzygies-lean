import BPFixedPoints.Real.RegularFiber

/-!
# Odd regular fibers of bounded perturbations of the identity

Cut off the bounded perturbation outside a ball. The fiber and its nearby
derivatives remain unchanged; a signed determinant integral for maps fixing
the boundary gives odd cardinality of a regular fiber.
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A regular fiber of a bounded C¹ perturbation has odd cardinality. -/
theorem odd_card_fiber_sub_of_bounded {B : E → E} (hB : ContDiff ℝ 1 B) {M : ℝ}
    (hM : ∀ x, ‖B x‖ ≤ M) (y : E)
    (hnd : ∀ x, x - B x = y → Function.Injective (fderiv ℝ (fun x => x - B x) x)) :
    Odd (Nat.card {x : E // x - B x = y}) := by
  classical
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simp [H])
  let B' : H → H := fun x => e (B (e.symm x))
  have hB' : ContDiff ℝ 1 B' := e.contDiff.comp (hB.comp e.symm.contDiff)
  let M' : ℝ := ‖e.toContinuousLinearMap‖ * max M 0
  have hM' : ∀ x, ‖B' x‖ ≤ M' := fun x =>
    (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hM _).trans (le_max_left _ _)) (norm_nonneg _))
  have hM'0 : 0 ≤ M' := mul_nonneg (norm_nonneg _) (le_max_right _ _)
  let ρ : ℝ := ‖e y‖ + M' + 1
  have hρ : 0 < ρ := by positivity
  let χ : ContDiffBump (0 : H) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let φ : H → H := fun x => x - (χ x) • (B' x + e y)
  have hφ : ContDiff ℝ 1 φ :=
    contDiff_id.sub (χ.contDiff.smul (hB'.add contDiff_const))
  have hout : ∀ x, 2 * ρ ≤ ‖x‖ → φ x = x := by
    intro x hx
    have hc : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    simp only [φ, hc, zero_smul, sub_zero]
  have hbound : ∀ x, φ x = 0 → ‖x‖ < ρ := by
    intro x hx
    have hx' : x = (χ x) • (B' x + e y) := sub_eq_zero.1 hx
    have hb : ‖B' x + e y‖ ≤ M' + ‖e y‖ :=
      (norm_add_le _ _).trans (add_le_add (hM' x) le_rfl)
    have hxle : ‖x‖ ≤ M' + ‖e y‖ := by
      rw [hx', norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      exact (mul_le_mul χ.le_one hb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    dsimp only [ρ]
    linarith
  have heq : ∀ x, φ x = 0 ↔ x - B' x = e y := by
    intro x
    constructor
    · intro hx
      have hc : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (hbound x hx).le)
      simpa only [φ, hc, one_smul, sub_add_eq_sub_sub, sub_eq_zero] using hx
    · intro hx
      have hx' : x = B' x + e y := by rw [← hx]; abel
      have hxle : ‖x‖ ≤ M' + ‖e y‖ := by
        calc ‖x‖ = ‖B' x + e y‖ := congrArg norm hx'
          _ ≤ ‖B' x‖ + ‖e y‖ := norm_add_le _ _
          _ ≤ M' + ‖e y‖ := add_le_add (hM' x) le_rfl
      have hc : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (by
        change ‖x‖ ≤ ‖e y‖ + M' + 1
        linarith))
      simp only [φ, hc, one_smul, sub_eq_zero]
      exact hx'
  have hφnd : ∀ z, φ z = 0 → (fderiv ℝ φ z).det ≠ 0 := by
    intro z hz
    let x := e.symm z
    have hx : x - B x = y := by
      apply e.injective
      simpa only [x, map_sub, ContinuousLinearEquiv.apply_symm_apply, B'] using (heq z).1 hz
    have hloc : φ =ᶠ[𝓝 z] fun w => w - B' w - e y := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (mem_ball_zero_iff.2 (hbound z hz))] with w hw
      simp only [φ, hw, Pi.one_apply, one_smul]
      abel
    have hd : HasFDerivAt (fun w : E => w - B w - y)
        (fderiv ℝ (fun w => w - B w) x) x :=
      (((contDiff_id.sub hB).differentiable one_ne_zero x).hasFDerivAt).sub_const y
    have hd' : HasFDerivAt (fun w : H => w - B' w - e y)
        (e.toContinuousLinearMap.comp
          ((fderiv ℝ (fun w => w - B w) x).comp e.symm.toContinuousLinearMap)) z := by
      have hh : HasFDerivAt (fun w : H => e (e.symm w - B (e.symm w) - y))
          (e.toContinuousLinearMap.comp
            ((fderiv ℝ (fun w => w - B w) x).comp e.symm.toContinuousLinearMap)) z :=
        e.hasFDerivAt.comp z (hd.comp z e.symm.hasFDerivAt)
      have hfun : (fun w : H => e (e.symm w - B (e.symm w) - y)) =
          (fun w => w - B' w - e y) := by
        funext w
        simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, B']
      rw [hfun] at hh
      exact hh
    have hinj : Function.Injective (fderiv ℝ φ z).toLinearMap := by
      rw [hloc.fderiv_eq, hd'.fderiv]
      exact e.injective.comp ((hnd x hx).comp e.symm.injective)
    have hunit : IsUnit ((fderiv ℝ φ z) : H →ₗ[ℝ] H) :=
      (Module.End.isUnit_iff _).2
        (LinearEquiv.ofInjectiveEndo (fderiv ℝ φ z).toLinearMap hinj).bijective
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  have hodd := odd_card_regular_fiber_of_eq_id_outside hφ (by linarith : 0 < 2 * ρ) hout hφnd
  let equiv : {z : H // φ z = 0} ≃ {x : E // x - B x = y} := {
    toFun := fun z => ⟨e.symm z.1, by
      apply e.injective
      simpa only [map_sub, ContinuousLinearEquiv.apply_symm_apply, B'] using (heq z.1).1 z.2⟩
    invFun := fun x => ⟨e x.1, (heq (e x.1)).2 (by
      simp only [B', ContinuousLinearEquiv.symm_apply_apply, ← map_sub, x.2])⟩
    left_inv := fun z => Subtype.ext (e.apply_symm_apply z.1)
    right_inv := fun x => Subtype.ext (e.symm_apply_apply x.1) }
  rwa [Nat.card_congr equiv] at hodd

end BPFixedPoints
