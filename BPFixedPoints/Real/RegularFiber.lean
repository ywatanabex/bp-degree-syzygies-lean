import BPFixedPoints.Real.DegreeIntegral
import BPFixedPoints.Real.RadialCap

/-!
# Regular fibers of maps equal to identity outside the boundary

For a C¹ map f equal to the identity outside a ball, whose zeros are nondegenerate, the zero
fiber is finite and Σ_{f(z)=0} sign det Df(z) = 1
(`finsum_sign_det_regular_fiber_of_eq_id_outside`). In particular the number of zeros is odd
(`odd_card_regular_fiber_of_eq_id_outside`).
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology Function
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_positive_lower_bound {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (hg : ∀ i, 0 < g i) : ∃ δ > 0, ∀ i, δ ≤ g i := by
  classical
  let T : Finset ℝ := insert 1 (Finset.univ.image g)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, ?_, fun i =>
    T.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (Finset.mem_univ i)))⟩
  show 0 < T.min' hT
  rw [Finset.lt_min'_iff]
  intro y hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact one_pos
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
    exact hg i

theorem exists_hasStrictFDerivAt_equiv_of_det_ne_zero {f : E → E} (hf : ContDiff ℝ 1 f)
    {x : E} (hx : (fderiv ℝ f x).det ≠ 0) :
    ∃ e : E ≃L[ℝ] E, HasStrictFDerivAt f (e : E →L[ℝ] E) x := by
  let L := fderiv ℝ f x
  have hunit : IsUnit (L : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hx)
  have hinj : Function.Injective (L : E →ₗ[ℝ] E) := ((Module.End.isUnit_iff _).1 hunit).1
  let e := (LinearEquiv.ofInjectiveEndo (L : E →ₗ[ℝ] E) hinj).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = L := by
    ext v
    simp [e, LinearEquiv.coe_ofInjectiveEndo]
  refine ⟨e, ?_⟩
  rw [he]
  exact hf.contDiffAt.hasStrictFDerivAt one_ne_zero

theorem isCompact_fiber_of_eq_id_outside {f : E → E} (hf : Continuous f) {R : ℝ}
    (hout : ∀ x, R ≤ ‖x‖ → f x = x) : IsCompact {x : E | f x = 0} := by
  have hc : IsClosed {x : E | f x = 0} := isClosed_eq hf continuous_const
  refine (isCompact_closedBall (0 : E) (max R 0)).of_isClosed_subset hc ?_
  intro x hx
  rw [mem_closedBall_zero_iff]
  by_contra h
  have hR : R ≤ ‖x‖ := (le_max_left R 0).trans (not_le.1 h).le
  have hx0 : x = 0 := (hout x hR).symm.trans hx
  simp only [hx0, norm_zero] at h
  exact h (le_max_right R 0)

theorem finite_regular_fiber_of_eq_id_outside {f : E → E} (hf : ContDiff ℝ 1 f) {R : ℝ}
    (hout : ∀ x, R ≤ ‖x‖ → f x = x)
    (hnd : ∀ x, f x = 0 → (fderiv ℝ f x).det ≠ 0) :
    {x : E | f x = 0}.Finite := by
  classical
  let Z := {x : E | f x = 0}
  have hc : IsCompact Z := isCompact_fiber_of_eq_id_outside hf.continuous hout
  have hloc : ∀ x : Z, ∃ U : Set E, IsOpen U ∧ x.1 ∈ U ∧ InjOn f U := by
    intro x
    obtain ⟨e, he⟩ := exists_hasStrictFDerivAt_equiv_of_det_ne_zero hf (hnd x.1 x.2)
    let g := he.toOpenPartialHomeomorph f
    exact ⟨g.source, g.open_source, he.mem_toOpenPartialHomeomorph_source, g.injOn⟩
  choose U hU hxU hUinj using hloc
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  refine (t.finite_toSet.image (Subtype.val : Z → E)).subset ?_
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (ht hx)
  exact ⟨z, hz, (hUinj z hxz (hxU z) (hx.trans z.2.symm)).symm⟩

/-- The preimage of a small regular-value ball splits into disjoint inverse charts around each zero. -/
theorem exists_regular_fiber_charts {f : E → E} (hf : ContDiff ℝ 1 f) {R : ℝ} (hR : 0 < R)
    (hout : ∀ x, R ≤ ‖x‖ → f x = x)
    (hnd : ∀ x, f x = 0 → (fderiv ℝ f x).det ≠ 0) :
    ∃ ε > 0, ε < R ∧ ∃ U : {x : E // f x = 0} → Set E,
      (∀ z, IsOpen (U z) ∧ U z ⊆ ball (0 : E) R ∧ InjOn f (U z) ∧
        f '' U z = ball (0 : E) ε ∧
        ∀ x ∈ U z, 0 < (fderiv ℝ f z.1).det * (fderiv ℝ f x).det) ∧
      Pairwise (Disjoint on U) ∧ f ⁻¹' ball (0 : E) ε = ⋃ z, U z := by
  classical
  let Z := {x : E // f x = 0}
  have hfin := finite_regular_fiber_of_eq_id_outside hf hout hnd
  let : Finite Z := hfin.to_subtype
  let : Fintype Z := Fintype.ofFinite Z
  have hzR : ∀ z : Z, ‖z.1‖ < R := by
    intro z
    by_contra h
    have hz0 : z.1 = 0 := (hout z.1 (not_lt.1 h)).symm.trans z.2
    exact h (by simpa [hz0] using hR)
  obtain ⟨O, hO, hdisj⟩ := hfin.t2_separation
  have hlocal : ∀ z : Z, ∃ W : Set E, IsOpen W ∧ z.1 ∈ W ∧ W ⊆ O z.1 ∧
      W ⊆ ball (0 : E) R ∧ InjOn f W ∧ f '' W ∈ 𝓝 (0 : E) ∧
      ∀ x ∈ W, 0 < (fderiv ℝ f z.1).det * (fderiv ℝ f x).det := by
    intro z
    obtain ⟨e, he⟩ := exists_hasStrictFDerivAt_equiv_of_det_ne_zero hf (hnd z.1 z.2)
    let g := he.toOpenPartialHomeomorph f
    let A := {x : E | 0 < (fderiv ℝ f z.1).det * (fderiv ℝ f x).det}
    have hA : IsOpen A := isOpen_lt continuous_const
      (continuous_const.mul (ContinuousLinearMap.continuous_det.comp
        (hf.continuous_fderiv one_ne_zero)))
    have hzA : z.1 ∈ A := mul_self_pos.2 (hnd z.1 z.2)
    let W := O z.1 ∩ g.source ∩ ball (0 : E) R ∩ A
    have hW : IsOpen W := (((hO z.1).2.inter g.open_source).inter isOpen_ball).inter hA
    have hzW : z.1 ∈ W :=
      ⟨⟨⟨(hO z.1).1, he.mem_toOpenPartialHomeomorph_source⟩,
        mem_ball_zero_iff.2 (hzR z)⟩, hzA⟩
    refine ⟨W, hW, hzW, fun x hx => hx.1.1.1, fun x hx => hx.1.2,
      g.injOn.mono (fun x hx => hx.1.1.2), ?_, fun x hx => hx.2⟩
    rw [← z.2, ← he.map_nhds_eq_of_equiv]
    exact image_mem_map (hW.mem_nhds hzW)
  choose W hW hzW hWO hWR hWinj hfW hWsign using hlocal
  have hbigW : IsOpen (⋃ z : Z, W z) := isOpen_iUnion hW
  let K := closedBall (0 : E) R \ ⋃ z : Z, W z
  have hK : IsCompact K := (isCompact_closedBall (0 : E) R).diff hbigW
  have h0K : (0 : E) ∉ f '' K := by
    rintro ⟨x, hx, hx0⟩
    exact hx.2 (mem_iUnion.2 ⟨⟨x, hx0⟩, hzW ⟨x, hx0⟩⟩)
  have hcompl : (f '' K)ᶜ ∈ 𝓝 (0 : E) :=
    (hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds h0K
  obtain ⟨ε₀, hε₀, hε₀K⟩ := Metric.mem_nhds_iff.1 hcompl
  have htargets : ∀ z : Z, ∃ δ > 0, ball (0 : E) δ ⊆ f '' W z :=
    fun z => Metric.mem_nhds_iff.1 (hfW z)
  choose δ hδ hδW using htargets
  obtain ⟨ε₁, hε₁, hε₁δ⟩ := exists_positive_lower_bound δ hδ
  let ε := min (R / 2) (min ε₀ ε₁)
  have hε : 0 < ε := lt_min (half_pos hR) (lt_min hε₀ hε₁)
  have hεR : ε < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεK : ε ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hεδ : ∀ z, ε ≤ δ z := fun z =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hε₁δ z)
  let U : Z → Set E := fun z => W z ∩ f ⁻¹' ball (0 : E) ε
  refine ⟨ε, hε, hεR, U, ?_, ?_, ?_⟩
  · intro z
    refine ⟨(hW z).inter (isOpen_ball.preimage hf.continuous),
      fun x hx => hWR z hx.1, (hWinj z).mono inter_subset_left, ?_,
      fun x hx => hWsign z x hx.1⟩
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hxW, hxy⟩ := hδW z (ball_subset_ball (hεδ z) hy)
      exact ⟨x, ⟨hxW, by change f x ∈ ball (0 : E) ε; rwa [hxy]⟩, hxy⟩
  · intro z w hzw
    exact (hdisj z.2 w.2 (fun h => hzw (Subtype.ext h))).mono
      (fun x hx => hWO z hx.1) (fun x hx => hWO w hx.1)
  · apply Subset.antisymm
    · intro x hx
      have hxf : ‖f x‖ < ε := mem_ball_zero_iff.1 hx
      have hxR : ‖x‖ < R := by
        by_contra h
        rw [hout x (not_lt.1 h)] at hxf
        linarith
      have hxW : x ∈ ⋃ z : Z, W z := by
        by_contra h
        have hxK : x ∈ K := ⟨mem_closedBall_zero_iff.2 hxR.le, h⟩
        have hfnot := hε₀K (mem_ball_zero_iff.2 (hxf.trans_le hεK))
        exact hfnot (mem_image_of_mem f hxK)
      obtain ⟨z, hz⟩ := mem_iUnion.1 hxW
      exact mem_iUnion.2 ⟨z, hz, hx⟩
    · rintro x hx
      obtain ⟨z, hz⟩ := mem_iUnion.1 hx
      exact hz.2

section Count

variable [MeasurableSpace E] [BorelSpace E]

/-- **Signed count of a regular zero fiber.** A C¹ map equal to identity outside a ball, with
nondegenerate zeros, satisfies Σ_{f(z)=0} sign det Df(z) = 1. Each zero contributes ±vol(ball ε)
to the determinant integral of the map composed with a radial cap, and that integral equals the
volume of the ball by `integral_det_fderiv_eq_of_boundary`. -/
theorem finsum_sign_det_regular_fiber_of_eq_id_outside {f : E → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (hout : ∀ x, R ≤ ‖x‖ → f x = x)
    (hnd : ∀ x, f x = 0 → (fderiv ℝ f x).det ≠ 0) :
    ∑ᶠ x ∈ {x : E | f x = 0}, (SignType.sign (fderiv ℝ f x).det : ℤ) = 1 := by
  classical
  let Z := {x : E // f x = 0}
  let : Finite Z := (finite_regular_fiber_of_eq_id_outside hf hout hnd).to_subtype
  let : Fintype Z := Fintype.ofFinite Z
  obtain ⟨ε, hε, hεR, U, hU, hdisj, hcover⟩ := exists_regular_fiber_charts hf hR hout hnd
  let μ : Measure E := Measure.addHaar
  let C : ℝ := (μ (ball (0 : E) R)).toReal
  have hC : 0 < C :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hR).ne' measure_ball_lt_top.ne
  let p : E → E := radialCap R (ε / 2) (half_pos hε)
  let r : E → E := p ∘ f
  have hp : ContDiff ℝ 1 p := contDiff_radialCap R (half_pos hε)
  have hr : ContDiff ℝ 1 r := hp.comp hf
  have hpbound : ∀ x, ‖p x‖ ≤ R := norm_radialCap_le hR.le (half_pos hε)
  have hpsph : ∀ x, ‖x‖ = R → p x = x := by
    intro x hx
    change radialCap R (ε / 2) (half_pos hε) x = x
    rw [radialCap_eq_of_le (half_pos hε) (by rw [hx]; linarith), hx,
      div_self hR.ne', one_smul]
  have hrsph : ∀ x, ‖x‖ = R → r x = x := by
    intro x hx
    change p (f x) = x
    rw [hout x hx.ge, hpsph x hx]
  let q : E → ℝ := fun x => (fderiv ℝ p x).det
  let j : E → ℝ := fun x => (fderiv ℝ r x).det
  have hvolp : ∫ x in ball (0 : E) R, q x ∂μ = C :=
    integral_det_fderiv_eq_of_boundary hp hR (fun x _ => hpbound x) hpsph
  have hvolr : ∫ x in ball (0 : E) R, j x ∂μ = C :=
    integral_det_fderiv_eq_of_boundary hr hR (fun x _ => hpbound (f x)) hrsph
  have hqzero : ∀ x, ε ≤ ‖x‖ → q x = 0 := by
    intro x hx
    exact det_fderiv_radialCap_eq_zero hR (half_pos hε) (by linarith)
  have hj : ∀ x, j x = q (f x) * (fderiv ℝ f x).det := by
    intro x
    dsimp only [j, q, r]
    rw [fderiv_comp x (hp.differentiable one_ne_zero (f x))
      (hf.differentiable one_ne_zero x)]
    exact LinearMap.det_comp _ _
  have hjzero : ∀ x, ε ≤ ‖f x‖ → j x = 0 := by
    intro x hx
    rw [hj x, hqzero (f x) hx, zero_mul]
  have hvolq : ∫ x in ball (0 : E) ε, q x ∂μ = C := by
    rw [← hvolp]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
      (ball_subset_ball hεR.le)
    intro x hx
    exact hqzero x (not_lt.1 (by simpa only [mem_ball_zero_iff] using hx.2))
  have hUball : (⋃ z : Z, U z) ⊆ ball (0 : E) R := by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.1 hx
    exact (hU z).2.1 hz
  have hvolj : ∫ x in ⋃ z : Z, U z, j x ∂μ = C := by
    rw [← hvolr]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hUball
    intro x hx
    apply hjzero x
    by_contra h
    have hsmall : x ∈ f ⁻¹' ball (0 : E) ε := mem_ball_zero_iff.2 (not_le.1 h)
    rw [hcover] at hsmall
    exact hx.2 hsmall
  have hjc : Continuous j :=
    ContinuousLinearMap.continuous_det.comp (hr.continuous_fderiv one_ne_zero)
  have hjint : ∀ z : Z, IntegrableOn j (U z) μ := fun z =>
    (hjc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)).mono_set
      (fun x hx => ball_subset_closedBall ((hU z).2.1 hx))
  have hcontrib : ∀ z : Z, ∫ x in U z, j x ∂μ =
      (if 0 < (fderiv ℝ f z.1).det then 1 else -1) * C := by
    intro z
    have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ (hU z).1.measurableSet
      (fun x _ => (hf.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt)
      (hU z).2.2.1 q
    rw [(hU z).2.2.2.1, hvolq] at hcv
    simp only [smul_eq_mul] at hcv
    by_cases hzpos : 0 < (fderiv ℝ f z.1).det
    · have hxpos : ∀ x ∈ U z, 0 < (fderiv ℝ f x).det := by
        intro x hx
        have hsign := (hU z).2.2.2.2 x hx
        exact (mul_pos_iff_of_pos_left hzpos).1 hsign
      rw [ite_eq_left hzpos, one_mul]
      rw [hcv]
      apply setIntegral_congr_fun (hU z).1.measurableSet
      intro x hx
      change j x = |(fderiv ℝ f x).det| * q (f x)
      rw [hj x, abs_of_pos (hxpos x hx), mul_comm]
    · have hzneg : (fderiv ℝ f z.1).det < 0 :=
        lt_of_le_of_ne (not_lt.1 hzpos) (hnd z.1 z.2)
      have hxneg : ∀ x ∈ U z, (fderiv ℝ f x).det < 0 := by
        intro x hx
        have hsign := (hU z).2.2.2.2 x hx
        by_contra h
        have hnonpos := mul_nonpos_of_nonpos_of_nonneg hzneg.le (not_lt.1 h)
        linarith
      rw [ite_eq_right hzpos, neg_one_mul, hcv, ← integral_neg]
      apply setIntegral_congr_fun (hU z).1.measurableSet
      intro x hx
      change j x = -(|(fderiv ℝ f x).det| * q (f x))
      rw [hj x, abs_of_neg (hxneg x hx)]
      ring
  have hsum : (∑ z : Z, if 0 < (fderiv ℝ f z.1).det then (1 : ℝ) else -1) = 1 := by
    have htot := integral_iUnion_fintype (fun z => (hU z).1.measurableSet) hdisj hjint
    rw [hvolj] at htot
    simp_rw [hcontrib] at htot
    rw [← Finset.sum_mul] at htot
    apply mul_right_cancel₀ hC.ne'
    simpa only [one_mul] using htot.symm
  have hsign : ∀ z : Z, (((SignType.sign (fderiv ℝ f z.1).det : ℤ)) : ℝ) =
      if 0 < (fderiv ℝ f z.1).det then 1 else -1 := by
    intro z
    by_cases hz : 0 < (fderiv ℝ f z.1).det
    · simp [hz, sign_pos hz]
    · simp [hz, sign_neg (lt_of_le_of_ne (not_lt.1 hz) (hnd z.1 z.2))]
  have hsumZ : ∑ z : Z, (SignType.sign (fderiv ℝ f z.1).det : ℤ) = 1 := by
    have hcast : ((∑ z : Z, (SignType.sign (fderiv ℝ f z.1).det : ℤ) : ℤ) : ℝ) = 1 := by
      rw [Int.cast_sum]
      simp_rw [hsign]
      exact hsum
    exact_mod_cast hcast
  rw [← finsum_set_coe_eq_finsum_mem]
  change ∑ᶠ z : Z, (SignType.sign (fderiv ℝ f z.1).det : ℤ) = 1
  rw [finsum_eq_sum_of_fintype]
  exact hsumZ

/-- A C¹ map equal to identity outside the boundary has an odd number of nondegenerate zeros. -/
theorem odd_card_regular_fiber_of_eq_id_outside {f : E → E} (hf : ContDiff ℝ 1 f)
    {R : ℝ} (hR : 0 < R) (hout : ∀ x, R ≤ ‖x‖ → f x = x)
    (hnd : ∀ x, f x = 0 → (fderiv ℝ f x).det ≠ 0) :
    Odd (Nat.card {x : E // f x = 0}) := by
  classical
  have hfin := finite_regular_fiber_of_eq_id_outside hf hout hnd
  have hsum := finsum_sign_det_regular_fiber_of_eq_id_outside hf hR hout hnd
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  -- Each sign is ±1, so the signed count has the parity of the cardinality.
  have heven : Even (∑ x ∈ hfin.toFinset, (1 - (SignType.sign (fderiv ℝ f x).det : ℤ))) := by
    apply Finset.even_sum
    intro x hx
    rcases lt_or_gt_of_ne (hnd x (hfin.mem_toFinset.1 hx)) with h | h
    · rw [sign_neg h]
      exact ⟨1, by simp⟩
    · rw [sign_pos h]
      simp
  have hcard : ((hfin.toFinset.card : ℕ) : ℤ) =
      (∑ x ∈ hfin.toFinset, (1 - (SignType.sign (fderiv ℝ f x).det : ℤ))) + 1 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hodd : Odd ((hfin.toFinset.card : ℕ) : ℤ) := by
    rw [hcard]
    exact heven.add_one
  change Odd (Nat.card {x : E | f x = 0})
  rw [Nat.card_eq_card_finite_toFinset hfin]
  exact (Int.odd_coe_nat _).1 hodd

end Count

end BPFixedPoints
