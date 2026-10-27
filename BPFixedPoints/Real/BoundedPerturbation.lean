import Mathlib
import BPFixedPoints.StrongField.StateMatrix

/-!
# Surjectivity of bounded C¹ perturbations of the identity

For `real:sector-degree`, the paper uses Brouwer degree ±1 of
𝔥_S(u)=D_Su−Z_S(u), with Z_S bounded. Instead prove the needed surjectivity
directly, since Mathlib has no Brouwer degree or Brouwer fixed-point theorem.

`exists_eq_zero_of_eq_id_outside`: a C¹ map φ on a finite-dimensional real
inner-product space, equal to identity outside radius R, attains zero.
Otherwise r=Rφ/‖φ‖ is a C¹ retraction from the closed ball to its sphere.
For small t, F_t=id+t(r−id) is injective on the open ball and onto it, by the
inverse function theorem and connectedness. Change of variables gives
∫_B det DF_t=vol(B). Principal-minor expansion makes this polynomial in t,
so it also holds at t=1, contradicting det Dr=0 from constant norm.
`surjective_of_eq_id_outside` follows by translation.
`surjective_sub_of_bounded` proves x↦x−B(x) surjective for bounded C¹ B on a
finite-dimensional real normed space: use a smooth cutoff and transfer to
an inner-product space by a linear isomorphism.
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology
open scoped InnerProductSpace

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A map of constant norm R>0 has singular derivative, det Dr=0. -/
theorem det_fderiv_eq_zero_of_norm_const {r : E → E} {R : ℝ} (hR : 0 < R) (hr : Differentiable ℝ r)
    (hnorm : ∀ x, ‖r x‖ = R) (x : E) : (fderiv ℝ r x).det = 0 := by
  set L := fderiv ℝ r x with hL
  have hd : HasFDerivAt r L x := (hr x).hasFDerivAt
  have hinner := hd.inner ℝ hd
  have hconst : (fun y => ⟪r y, r y⟫_ℝ) = fun _ => R ^ 2 := by
    funext y
    rw [real_inner_self_eq_norm_sq, hnorm y]
  rw [hconst] at hinner
  have h0 := hinner.unique (hasFDerivAt_const (R ^ 2) x)
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
  rw [hv, real_inner_self_eq_norm_sq, hnorm x] at h1
  have : R ^ 2 > 0 := by positivity
  linarith

/-- If ‖A‖<1, then 1+A is a continuous linear equivalence. -/
theorem exists_equiv_one_add {A : E →L[ℝ] E} (hA : ‖A‖ < 1) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = 1 + A := by
  have hA' : ‖-A‖ < 1 := by rwa [norm_neg]
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ E (Units.oneSub (-A) hA'), ?_⟩
  ext v
  simp [ContinuousLinearEquiv.unitsEquiv_apply, Units.val_oneSub, sub_neg_eq_add]

/-- If ‖A‖<1, then det(1+A)>0. -/
theorem det_one_add_pos {A : E →L[ℝ] E} (hA : ‖A‖ < 1) : 0 < (1 + A).det := by
  set g : ℝ → ℝ := fun s => (1 + s • A).det with hg
  have hgc : Continuous g :=
    ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ 0 := by
    intro s hs
    have hs' : ‖-(s • A)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖A‖ ≤ 1 * ‖A‖ := by gcongr; exact hs.2
        _ < 1 := by rw [one_mul]; exact hA
    set u := Units.oneSub (-(s • A)) hs'
    have hu : (u : E →L[ℝ] E) = 1 + s • A := by
      simp [u, Units.val_oneSub, sub_neg_eq_add]
    set e : E ≃L[ℝ] E := ContinuousLinearEquiv.unitsEquiv ℝ E u
    have he : (e : E →L[ℝ] E) = 1 + s • A := by
      ext v; simp [e, ContinuousLinearEquiv.unitsEquiv_apply, hu]
    change (1 + s • A).det ≠ 0
    rw [← he]
    exact (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  by_contra hle
  push Not at hle
  have h0 : g 0 = 1 := by
    change LinearMap.det ((1 + (0 : ℝ) • A : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1
    simp
  have hle' : g 1 ≤ 0 := by simp only [hg, one_smul]; exact hle
  have hmem : (0 : ℝ) ∈ Icc (g 1) (g 0) := ⟨hle', by rw [h0]; norm_num⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hgc.continuousOn hmem
  exact hne s hs hs0

/-- The integral of det(1+tA(x)) is polynomial in t by principal-minor expansion, for continuous A over a domain contained in a compact set. -/
theorem exists_poly_integral_det [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] {A : E → E →L[ℝ] E} (hA : Continuous A) {s K : Set E}
    (hK : IsCompact K) (hsK : s ⊆ K) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ, p.eval t = ∫ x in s, (1 + t • A x).det ∂μ := by
  classical
  set b := Module.finBasis ℝ E
  set M : E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun x => LinearMap.toMatrix b b (A x : E →ₗ[ℝ] E) with hM
  have hMc : Continuous M := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [hM, LinearMap.toMatrix_apply]
    have h1 : Continuous fun x => (A x) (b j) := (ContinuousLinearMap.apply ℝ E (b j)).continuous.comp hA
    have h2 : Continuous fun v : E => b.repr v i :=
      (LinearMap.continuous_of_finiteDimensional (b.coord i))
    exact h2.comp h1
  have hdet : ∀ t x, (1 + t • A x).det =
      ∑ u : Finset (Fin (Module.finrank ℝ E)),
        t ^ u.card * ((M x).submatrix (Subtype.val : u → _) Subtype.val).det := by
    intro t x
    change LinearMap.det ((1 + t • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
    rw [← LinearMap.det_toMatrix b]
    have : LinearMap.toMatrix b b ((1 + t • A x : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 + t • M x := by
      simp [hM, map_add, map_smul]
    rw [this, det_one_add_eq_sum_det_submatrix]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [show (t • M x).submatrix (Subtype.val : u → _) Subtype.val =
      t • (M x).submatrix Subtype.val Subtype.val from rfl, Matrix.det_smul, Fintype.card_coe]
  have hint : ∀ u : Finset (Fin (Module.finrank ℝ E)),
      IntegrableOn (fun x => ((M x).submatrix (Subtype.val : u → _) Subtype.val).det) s μ := by
    intro u
    have hc : Continuous fun x => ((M x).submatrix (Subtype.val : u → _) Subtype.val).det :=
      (hMc.matrix_submatrix _ _).matrix_det
    exact (hc.continuousOn.integrableOn_compact hK).mono_set hsK
  refine ⟨∑ u : Finset (Fin (Module.finrank ℝ E)),
    Polynomial.C (∫ x in s, ((M x).submatrix (Subtype.val : u → _) Subtype.val).det ∂μ) *
      Polynomial.X ^ u.card, fun t => ?_⟩
  simp_rw [hdet t]
  rw [integral_finsetSum _ fun u _ => (hint u).const_mul _]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_const_mul, mul_comm]

/-- **A C¹ map equal to identity outside a ball attains zero.** Otherwise r=Rφ/‖φ‖ retracts the closed ball onto its sphere. The determinant integral of F_t=id+t(r−id) equals vol(B) for all t, contradicting det Dr=0. -/
theorem exists_eq_zero_of_eq_id_outside {φ : E → E} (hφ : ContDiff ℝ 1 φ) {R : ℝ} (hR : 0 < R)
    (hout : ∀ x, R ≤ ‖x‖ → φ x = x) : ∃ x, φ x = 0 := by
  classical
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  by_contra hne
  push Not at hne
  -- Retraction onto the sphere.
  set r : E → E := fun x => (R * ‖φ x‖⁻¹) • φ x with hr_def
  have hφn : ∀ x, ‖φ x‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (hne x)
  have hr : ContDiff ℝ 1 r :=
    (contDiff_const.mul ((hφ.norm ℝ hne).inv hφn)).smul hφ
  have hrnorm : ∀ x, ‖r x‖ = R := by
    intro x
    simp only [hr_def, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hR, abs_inv, abs_norm]
    field_simp [hφn x]
  have hrsph : ∀ x, ‖x‖ = R → r x = x := by
    intro x hx
    simp only [hr_def, hout x hx.ge, hx, mul_inv_cancel₀ hR.ne', one_smul]
  have hdetr : ∀ x, (fderiv ℝ r x).det = 0 :=
    det_fderiv_eq_zero_of_norm_const hR (hr.differentiable one_ne_zero) hrnorm
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
        _ = (1 - t) * ‖x‖ + t * R := by
          rw [norm_smul, norm_smul, hrnorm, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by linarith), abs_of_pos ht.1]
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
  have h2 : ∫ x in ball (0 : E) R, (1 + (1 : ℝ) • fderiv ℝ ψ x).det ∂μ = 0 := by
    simp only [one_smul, hfdψ, hdetr, integral_zero]
  rw [h2] at h1
  have hμpos : 0 < (μ (ball (0 : E) R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hR).ne' measure_ball_lt_top.ne
  linarith

/-- A C¹ map equal to identity outside a ball is surjective. -/
theorem surjective_of_eq_id_outside {φ : E → E} (hφ : ContDiff ℝ 1 φ) {R : ℝ}
    (hout : ∀ x, R ≤ ‖x‖ → φ x = x) : Function.Surjective φ := by
  intro y
  set R' : ℝ := max (R + ‖y‖) 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hψ : ContDiff ℝ 1 fun x => φ (x + y) - y :=
    (hφ.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  obtain ⟨x, hx⟩ := exists_eq_zero_of_eq_id_outside hψ hR' fun x hx => by
    have : R ≤ ‖x + y‖ := by
      have h1 : ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
        have := norm_sub_le (x + y) y
        rw [add_sub_cancel_right] at this
        linarith
      have h2 : R + ‖y‖ ≤ ‖x‖ := (le_max_left _ _).trans hx
      linarith
    simp [hout _ this]
  exact ⟨x + y, sub_eq_zero.1 hx⟩

end InnerProduct

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Surjectivity of a bounded C¹ perturbation.** In a finite-dimensional real normed space, bounded C¹ B gives a surjective map x↦x−B(x). -/
theorem surjective_sub_of_bounded {B : E → E} (hB : ContDiff ℝ 1 B) {M : ℝ}
    (hM : ∀ x, ‖B x‖ ≤ M) : Function.Surjective fun x => x - B x := by
  -- Transfer to the inner-product space EuclideanSpace.
  set e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  set B' : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun x => e (B (e.symm x))
  have hB' : ContDiff ℝ 1 B' := e.contDiff.comp (hB.comp e.symm.contDiff)
  set M' : ℝ := ‖e.toContinuousLinearMap‖ * max M 0
  have hM' : ∀ x, ‖B' x‖ ≤ M' := fun x =>
    (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hM _).trans (le_max_left _ _)) (norm_nonneg _))
  have hM'0 : 0 ≤ M' := mul_nonneg (norm_nonneg _) (le_max_right _ _)
  suffices hs : Function.Surjective fun x => x - B' x by
    intro y
    obtain ⟨x, hx⟩ := hs (e y)
    refine ⟨e.symm x, ?_⟩
    apply e.injective
    simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply]
    exact hx
  intro y
  -- Use a cutoff to make the map identity outside a ball.
  set ρ : ℝ := ‖y‖ + M' + 1
  have hρ : 0 < ρ := by positivity
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ⟨ρ, 2 * ρ, hρ, by linarith⟩
  set φ := fun x => x - (χ x) • B' x
  have hφ : ContDiff ℝ 1 φ := contDiff_id.sub ((χ.contDiff).smul hB')
  have hout : ∀ x, 2 * ρ ≤ ‖x‖ → φ x = x := by
    intro x hx
    have : χ x = 0 := χ.zero_of_le_dist (by rw [dist_zero_right]; exact hx)
    simp [φ, this]
  obtain ⟨x, hx⟩ := surjective_of_eq_id_outside hφ hout y
  have hxρ : ‖x‖ ≤ ρ := by
    by_contra hlt
    push Not at hlt
    have h1 : ‖(χ x) • B' x‖ ≤ M' := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      calc χ x * ‖B' x‖ ≤ 1 * M' := mul_le_mul χ.le_one (hM' x) (norm_nonneg _) zero_le_one
        _ = M' := one_mul _
    have h2 : ‖x‖ - ‖(χ x) • B' x‖ ≤ ‖y‖ := by
      rw [← hx]
      have := norm_sub_norm_le x ((χ x) • B' x)
      linarith
    linarith
  have h1 : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hxρ)
  refine ⟨x, ?_⟩
  simpa [φ, h1] using hx

end Normed

end BPFixedPoints
