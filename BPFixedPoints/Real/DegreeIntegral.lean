import BPFixedPoints.Real.BoundedPerturbation

/-!
# Determinant integral for maps fixing a ball boundary

A C¹ self-map r of the closed ball, equal to identity on its boundary, has
derivative determinant integral equal to the ball volume. For small t,
(1−t)id+tr is a diffeomorphism; the integral is polynomial in t.
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Determinant integral for a C¹ self-map of a closed ball fixing its boundary. -/
theorem integral_det_fderiv_eq_of_boundary [MeasurableSpace E] [BorelSpace E]
    {r : E → E} (hr : ContDiff ℝ 1 r) {R : ℝ} (hR : 0 < R)
    (hball : ∀ x ∈ closedBall (0 : E) R, ‖r x‖ ≤ R)
    (hrsph : ∀ x, ‖x‖ = R → r x = x) :
    ∫ x in ball (0 : E) R, (fderiv ℝ r x).det ∂Measure.addHaar =
      (Measure.addHaar (ball (0 : E) R)).toReal := by
  classical
  set μ : Measure E := Measure.addHaar
  -- ψ = r − id
  set ψ : E → E := fun x => r x - x with hψ_def
  have hψ : ContDiff ℝ 1 ψ := hr.sub contDiff_id
  have hψdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hψd : ∀ x, HasFDerivAt ψ (fderiv ℝ ψ x) x := fun x => (hψdiff x).hasFDerivAt
  have hfdψ : ∀ x, 1 + fderiv ℝ ψ x = fderiv ℝ r x := by
    intro x
    have h1 : HasFDerivAt ψ (fderiv ℝ r x - ContinuousLinearMap.id ℝ E) x :=
      ((hr.differentiable one_ne_zero x).hasFDerivAt).sub (hasFDerivAt_id x)
    rw [(hψd x).unique h1, ContinuousLinearMap.one_def]
    abel
  have hψsph : ∀ x, ‖x‖ = R → ψ x = 0 := fun x hx => by simp [hψ_def, hrsph x hx]
  have hAc : Continuous fun x => fderiv ℝ ψ x := hψ.continuous_fderiv one_ne_zero
  -- Derivative bound on the closed ball.
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hAc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self hR.le))
  have hlip : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R, ‖ψ y - ψ x‖ ≤ C * ‖y - x‖ :=
    fun x hx y hy => (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hψdiff z) hC hx hy
  set t₀ : ℝ := 1 / (C + 1)
  have ht₀ : 0 < t₀ := by positivity
  -- Volume equality for small t.
  have hvol : ∀ t ∈ Ioo (0 : ℝ) t₀,
      ∫ x in ball (0 : E) R, (1 + t • fderiv ℝ ψ x).det ∂μ = (μ (ball (0 : E) R)).toReal := by
    intro t ht
    have ht1 : t < 1 := by
      have : t₀ ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith [ht.2]
    have htC : t * C < 1 := by
      have : t * (C + 1) < 1 := by
        have := ht.2; rw [lt_div_iff₀ (by positivity)] at this; linarith
      nlinarith [ht.1]
    have hsmall : ∀ x ∈ closedBall (0 : E) R, ‖t • fderiv ℝ ψ x‖ < 1 := by
      intro x hx
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖fderiv ℝ ψ x‖ ≤ t * C := mul_le_mul_of_nonneg_left (hC x hx) ht.1.le
        _ < 1 := htC
    set F : E → E := fun x => x + t • ψ x with hF_def
    have hF' : ∀ x, HasFDerivAt F (1 + t • fderiv ℝ ψ x) x := by
      intro x
      have := (hasFDerivAt_id x).add ((hψd x).const_smul t)
      rw [← ContinuousLinearMap.one_def] at this
      exact this
    have hFc : ContDiff ℝ 1 F := contDiff_id.add (contDiff_const.smul hψ)
    have hFcont : Continuous F := hFc.continuous
    have hFsph : ∀ x, ‖x‖ = R → F x = x := fun x hx => by simp [hF_def, hψsph x hx]
    have hFball : ∀ x ∈ ball (0 : E) R, F x ∈ ball (0 : E) R := by
      intro x hx
      rw [mem_ball_zero_iff] at hx ⊢
      have : F x = (1 - t) • x + t • r x := by
        simp only [hF_def, hψ_def, smul_sub, sub_smul, one_smul]
        abel
      rw [this]
      calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
        _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by linarith), abs_of_pos ht.1]
        _ ≤ (1 - t) * ‖x‖ + t * R :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (hball x (mem_closedBall_zero_iff.2 hx.le)) ht.1.le)
        _ < (1 - t) * R + t * R := by gcongr
        _ = R := by ring
    have hinj : InjOn F (ball (0 : E) R) := by
      intro x hx y hy hxy
      have hx' := ball_subset_closedBall hx
      have hy' := ball_subset_closedBall hy
      have h1 : y - x = t • (ψ x - ψ y) := by
        simp only [hF_def] at hxy
        rw [smul_sub, sub_eq_sub_iff_add_eq_add, add_comm (t • ψ x) x]
        exact hxy.symm
      have h2 : ‖y - x‖ ≤ t * C * ‖y - x‖ := by
        calc ‖y - x‖ = t * ‖ψ x - ψ y‖ := by rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
          _ ≤ t * (C * ‖x - y‖) := mul_le_mul_of_nonneg_left (hlip y hy' x hx') ht.1.le
          _ = t * C * ‖y - x‖ := by rw [norm_sub_rev]; ring
      have h3 : ‖y - x‖ = 0 := by
        have := norm_nonneg (y - x)
        nlinarith
      exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm
    have himage : F '' ball (0 : E) R = ball (0 : E) R := by
      apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hFball x hx
      · have hopen : IsOpen (F '' ball (0 : E) R) := by
          rw [isOpen_iff_mem_nhds]
          rintro _ ⟨x, hx, rfl⟩
          obtain ⟨e, he⟩ := exists_equiv_one_add (hsmall x (ball_subset_closedBall hx))
          have hstrict : HasStrictFDerivAt F (e : E →L[ℝ] E) x := by
            rw [he]
            have := (hFc.contDiffAt (x := x)).hasStrictFDerivAt one_ne_zero
            rwa [(hF' x).fderiv] at this
          rw [← hstrict.map_nhds_eq_of_equiv]
          exact image_mem_map (isOpen_ball.mem_nhds hx)
        have hne' : (ball (0 : E) R ∩ F '' ball (0 : E) R).Nonempty :=
          ⟨F 0, hFball 0 (mem_ball_self hR), mem_image_of_mem F (mem_ball_self hR)⟩
        have hclos : closure (F '' ball (0 : E) R) ∩ ball (0 : E) R ⊆ F '' ball (0 : E) R := by
          rintro z ⟨hz, hzb⟩
          have hcl : closure (F '' ball (0 : E) R) ⊆ F '' closedBall (0 : E) R :=
            ((isCompact_closedBall (0 : E) R).image hFcont).isClosed.closure_subset_iff.2
              (image_mono ball_subset_closedBall)
          obtain ⟨x, hx, rfl⟩ := hcl hz
          rw [mem_closedBall_zero_iff] at hx
          rcases hx.lt_or_eq with hlt | heq
          · exact mem_image_of_mem F (mem_ball_zero_iff.2 hlt)
          · rw [hFsph x heq, mem_ball_zero_iff] at hzb
            exact absurd heq hzb.ne
        exact (convex_ball (0 : E) R).isPreconnected.subset_of_closure_inter_subset hopen hne' hclos
    have hpos : ∀ x ∈ ball (0 : E) R, 0 < (1 + t • fderiv ℝ ψ x).det :=
      fun x hx => det_one_add_pos (hsmall x (ball_subset_closedBall hx))
    have hcv := lintegral_abs_det_fderiv_eq_addHaar_image μ measurableSet_ball
      (fun x _ => (hF' x).hasFDerivWithinAt) hinj
    rw [himage] at hcv
    have hcv' : ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (1 + t • fderiv ℝ ψ x).det ∂μ =
        μ (ball (0 : E) R) := by
      rw [← hcv]
      refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
      rw [abs_of_pos (hpos x hx)]
    have hcont : Continuous fun x => (1 + t • fderiv ℝ ψ x).det :=
      ContinuousLinearMap.continuous_det.comp (continuous_const.add (hAc.const_smul t))
    rw [integral_eq_lintegral_of_nonneg_ae, hcv']
    · exact (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => (hpos x hx).le)
    · exact hcont.aestronglyMeasurable
  -- Polynomial identity.
  obtain ⟨p, hp⟩ := exists_poly_integral_det μ hAc (isCompact_closedBall (0 : E) R)
    ball_subset_closedBall
  have hpC : p = Polynomial.C (μ (ball (0 : E) R)).toReal := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Ioo (0 : ℝ) t₀)
    · intro t ht
      simp [Polynomial.IsRoot, hp t, hvol t ht]
    · exact Set.Ioo_infinite ht₀
  have h1 := hp 1
  rw [hpC, Polynomial.eval_C] at h1
  simpa only [one_smul, hfdψ] using h1.symm

end BPFixedPoints
