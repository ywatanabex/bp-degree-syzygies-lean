import BPFixedPoints.Real.ProperDegree

/-!
# The determinant-integral form of the degree

For a proper C¹ self-map g of a finite-dimensional real normed space with an additive Haar
measure μ, and a continuous compactly supported ψ, the signed area formula

  ∫ ψ(g x) det Dg(x) dμ(x) = ∫ N(y) ψ(y) dμ(y),   N(y) = Σ_{g(x)=y} sign det Dg(x),

holds (`integral_comp_mul_det_eq_integral_signedFiberCount`). The nondegenerate locus is a
countable disjoint union of measurable pieces on which g is injective with constant sign
(`exists_injOn_cover_of_det_ne_zero`); change of variables on each piece and Sard's theorem, which
makes almost every value regular, give the formula.

For a C¹ map f at bounded distance from an invertible linear map, N = deg f at every regular
value, so ∫ ψ(f x) det Df(x) dμ(x) = deg f · ∫ ψ dμ
(`integral_comp_mul_det_eq_brouwerDegree_mul`). Hence the determinant-integral degree
`degreeIntegral` against any normalized test function equals `brouwerDegree`, whatever the support
of the test function, also around critical values (`degreeIntegral_eq_brouwerDegree`,
`exists_degreeIntegral_eq_brouwerDegree_ball`).
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology Function
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The nondegenerate locus {det Dg ≠ 0} of a C¹ map is a countable union of open sets on each of
which g is injective and det Dg has constant sign. -/
theorem exists_injOn_cover_of_det_ne_zero {g : E → E} (hg : ContDiff ℝ 1 g) :
    ∃ U : ℕ → Set E, (∀ n, IsOpen (U n)) ∧ (∀ n, InjOn g (U n)) ∧
      (∀ n, (∀ x ∈ U n, 0 < (fderiv ℝ g x).det) ∨ (∀ x ∈ U n, (fderiv ℝ g x).det < 0)) ∧
      ⋃ n, U n = {x | (fderiv ℝ g x).det ≠ 0} := by
  classical
  have hDc : Continuous fun x => (fderiv ℝ g x).det :=
    ContinuousLinearMap.continuous_det.comp (hg.continuous_fderiv one_ne_zero)
  let 𝒰 : Set (Set E) := {U | IsOpen U ∧ InjOn g U ∧
    ((∀ x ∈ U, 0 < (fderiv ℝ g x).det) ∨ (∀ x ∈ U, (fderiv ℝ g x).det < 0)) ∧
    U ⊆ {x | (fderiv ℝ g x).det ≠ 0}}
  have hcov : ⋃₀ 𝒰 = {x | (fderiv ℝ g x).det ≠ 0} := by
    apply Subset.antisymm
    · rintro x ⟨U, hU, hx⟩
      exact hU.2.2.2 hx
    · intro x hx
      have hx' : (fderiv ℝ g x).det ≠ 0 := hx
      obtain ⟨e, he⟩ := exists_equiv_hasStrictFDerivAt_of_det_ne_zero hg hx'
      let h := he.toOpenPartialHomeomorph g
      let A : Set E := {x' | 0 < (fderiv ℝ g x).det * (fderiv ℝ g x').det}
      have hA : IsOpen A := isOpen_lt continuous_const (continuous_const.mul hDc)
      refine ⟨h.source ∩ A, ⟨h.open_source.inter hA, h.injOn.mono inter_subset_left, ?_, ?_⟩,
        he.mem_toOpenPartialHomeomorph_source, mul_self_pos.2 hx'⟩
      · rcases lt_or_gt_of_ne hx' with hneg | hpos
        · right
          intro x' hx''
          have hprod : 0 < (fderiv ℝ g x).det * (fderiv ℝ g x').det := hx''.2
          by_contra hc
          have hnn : 0 ≤ (fderiv ℝ g x').det := not_lt.1 hc
          have := mul_nonpos_of_nonpos_of_nonneg hneg.le hnn
          linarith
        · left
          intro x' hx''
          exact (mul_pos_iff_of_pos_left hpos).1 hx''.2
      · intro x' hx'' h0
        have hprod : 0 < (fderiv ℝ g x).det * (fderiv ℝ g x').det := hx''.2
        rw [show (fderiv ℝ g x').det = 0 from h0, mul_zero] at hprod
        exact lt_irrefl 0 hprod
  obtain ⟨T, hTc, hT𝒰, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒰 fun U hU => hU.1
  obtain ⟨U, hU⟩ := (hTc.insert ∅).exists_eq_range (insert_nonempty ∅ T)
  have hmem : ∀ n, U n = ∅ ∨ U n ∈ 𝒰 := by
    intro n
    have h : U n ∈ insert ∅ T := by
      rw [hU]
      exact mem_range_self n
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (hT𝒰 h)
  refine ⟨U, fun n => ?_, fun n => ?_, fun n => ?_, ?_⟩
  · rcases hmem n with h | h
    · rw [h]
      exact isOpen_empty
    · exact h.1
  · rcases hmem n with h | h
    · rw [h]
      exact injOn_empty g
    · exact h.2.1
  · rcases hmem n with h | h
    · left
      rw [h]
      intro x hx
      exact absurd hx (notMem_empty x)
    · exact h.2.2.1
  · rw [← hcov, ← hTU, ← sUnion_range, ← hU, sUnion_insert, empty_union]

section Integral

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Signed area formula.** For a proper C¹ self-map g and a continuous compactly supported ψ,
∫ ψ(g x) det Dg(x) dμ(x) = ∫ N(y) ψ(y) dμ(y), where N(y) = Σ_{g(x)=y} sign det Dg(x) is the
signed fiber count. -/
theorem integral_comp_mul_det_eq_integral_signedFiberCount {g : E → E} (hg : ContDiff ℝ 1 g)
    (hprop : ∀ K, IsCompact K → IsCompact (g ⁻¹' K)) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ∫ x, ψ (g x) * (fderiv ℝ g x).det ∂μ = ∫ y, (signedFiberCount g y : ℝ) * ψ y ∂μ := by
  classical
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hDc : Continuous fun x => (fderiv ℝ g x).det :=
    ContinuousLinearMap.continuous_det.comp (hg.continuous_fderiv one_ne_zero)
  obtain ⟨U, hUo, hUinj, hUsign, hUcov⟩ := exists_injOn_cover_of_det_ne_zero hg
  -- Disjoint measurable pieces of the nondegenerate locus.
  let P : ℕ → Set E := disjointed U
  have hPm : ∀ n, MeasurableSet (P n) := MeasurableSet.disjointed fun n => (hUo n).measurableSet
  have hPU : ∀ n, P n ⊆ U n := disjointed_subset U
  have hPd : Pairwise (Disjoint on P) := disjoint_disjointed U
  have hPcov : ⋃ n, P n = {x | (fderiv ℝ g x).det ≠ 0} := by
    rw [iUnion_disjointed]
    exact hUcov
  have hPinj : ∀ n, InjOn g (P n) := fun n => (hUinj n).mono (hPU n)
  have hderiv : ∀ (s : Set E), ∀ x ∈ s, HasFDerivWithinAt g (fderiv ℝ g x) s x :=
    fun _ x _ => (hgd x).hasFDerivAt.hasFDerivWithinAt
  -- The constant sign on each piece.
  let σ : ℕ → ℝ := fun n => if ∀ x ∈ U n, 0 < (fderiv ℝ g x).det then 1 else -1
  have hσD : ∀ n, ∀ x ∈ U n, (fderiv ℝ g x).det = σ n * |(fderiv ℝ g x).det| := by
    intro n x hx
    by_cases hpos : ∀ x ∈ U n, 0 < (fderiv ℝ g x).det
    · rw [show σ n = 1 from ite_eq_left hpos, one_mul, abs_of_pos (hpos x hx)]
    · have hneg := (hUsign n).resolve_left hpos
      rw [show σ n = -1 from ite_eq_right hpos, abs_of_neg (hneg x hx)]
      ring
  have hσsign : ∀ n, ∀ x ∈ U n,
      (((SignType.sign (fderiv ℝ g x).det : ℤ)) : ℝ) = σ n := by
    intro n x hx
    by_cases hpos : ∀ x ∈ U n, 0 < (fderiv ℝ g x).det
    · rw [show σ n = 1 from ite_eq_left hpos, sign_pos (hpos x hx)]
      simp
    · have hneg := (hUsign n).resolve_left hpos
      rw [show σ n = -1 from ite_eq_right hpos, sign_neg (hneg x hx)]
      simp
  have hσ1 : ∀ n, ‖σ n‖ₑ = 1 := by
    intro n
    simp only [σ]
    split_ifs <;> simp
  -- The integrand is continuous with compact support.
  let F : E → ℝ := fun x => ψ (g x) * (fderiv ℝ g x).det
  have hFc : Continuous F := (hψ.comp hg.continuous).mul hDc
  have hFs : HasCompactSupport F := HasCompactSupport.intro (hprop _ hψs) fun x hx => by
    simp only [F, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hFi : Integrable F μ := hFc.integrable_of_hasCompactSupport hFs
  -- Step 1: the integral splits over the pieces.
  have h1 : ∫ x, F x ∂μ = ∑' n, ∫ x in P n, F x ∂μ := by
    rw [← integral_iUnion hPm hPd hFi.integrableOn]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [hPcov] at hx
    have hx0 : (fderiv ℝ g x).det = 0 := not_not.1 hx
    simp only [F, hx0, mul_zero]
  -- Step 2: change of variables on each piece.
  let f : ℕ → E → ℝ := fun n => (g '' P n).indicator fun y => σ n * ψ y
  have hgPm : ∀ n, MeasurableSet (g '' P n) := fun n =>
    measurable_image_of_fderivWithin (hPm n) (hderiv _) (hPinj n)
  have h2 : ∀ n, ∫ x in P n, F x ∂μ = ∫ y, f n y ∂μ := by
    intro n
    rw [integral_indicator (hgPm n), integral_const_mul,
      integral_image_eq_integral_abs_det_fderiv_smul μ (hPm n) (hderiv _) (hPinj n),
      ← integral_const_mul]
    refine setIntegral_congr_fun (hPm n) fun x hx => ?_
    simp only [F, smul_eq_mul]
    conv_lhs => rw [hσD n x (hPU n hx)]
    ring
  -- Step 3: exchange of the sum and the integral.
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    (continuous_const.mul hψ).aestronglyMeasurable.indicator (hgPm n)
  have hfn : ∀ n y, ‖f n y‖ₑ = (g '' P n).indicator (fun y => ‖ψ y‖ₑ) y := by
    intro n y
    by_cases hy : y ∈ g '' P n
    · simp only [f, indicator_of_mem hy, enorm_mul, hσ1, one_mul]
    · simp only [f, indicator_of_notMem hy, enorm_zero]
  have hle : ∀ n, ∫⁻ y, ‖f n y‖ₑ ∂μ = ∫⁻ x in P n, ‖F x‖ₑ ∂μ := by
    intro n
    simp_rw [hfn n]
    rw [lintegral_indicator (hgPm n),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ (hPm n) (hderiv _) (hPinj n)]
    refine lintegral_congr fun x => ?_
    simp only [F, enorm_mul, Real.enorm_eq_ofReal_abs, mul_comm]
  have hfb : ∑' n, ∫⁻ y, ‖f n y‖ₑ ∂μ ≠ ⊤ := by
    simp_rw [hle]
    rw [← lintegral_iUnion hPm hPd]
    exact ne_top_of_le_ne_top hFi.hasFiniteIntegral.ne (setLIntegral_le_lintegral _ _)
  have h3 : ∑' n, ∫ y, f n y ∂μ = ∫ y, ∑' n, f n y ∂μ := (integral_tsum hfm hfb).symm
  -- Step 4: at a regular value the series is the signed count times ψ.
  have h4 : ∀ y, IsRegularValue g y → ∑' n, f n y = (signedFiberCount g y : ℝ) * ψ y := by
    intro y hy
    have hfin : (g ⁻¹' {y}).Finite :=
      finite_fiber_of_isCompact hg (hprop _ isCompact_singleton) hy
    have hex : ∀ x, (fderiv ℝ g x).det ≠ 0 → ∃ n, x ∈ P n := by
      intro x hx
      have hx' : x ∈ ⋃ n, P n := by
        rw [hPcov]
        exact hx
      exact mem_iUnion.1 hx'
    let idx : E → ℕ := fun x => if h : ∃ n, x ∈ P n then Classical.choose h else 0
    have hidx : ∀ x, (fderiv ℝ g x).det ≠ 0 → x ∈ P (idx x) := by
      intro x hx
      have h := hex x hx
      simp only [idx, h]
      exact Classical.choose_spec h
    have huniq : ∀ x n m, x ∈ P n → x ∈ P m → n = m := by
      intro x n m hn hm
      by_contra hne
      exact Set.disjoint_left.1 (hPd hne) hn hm
    let N : Set ℕ := {n | y ∈ g '' P n}
    have hbij : BijOn idx (g ⁻¹' {y}) N := by
      refine ⟨fun x hx => ⟨x, hidx x (hy x hx), hx⟩, fun x hx x' hx' hxx' => ?_, fun n hn => ?_⟩
      · have hx1 := hidx x (hy x hx)
        have hx2 := hidx x' (hy x' hx')
        rw [hxx'] at hx1
        exact hPinj (idx x') hx1 hx2
          ((show g x = y from hx).trans (show g x' = y from hx').symm)
      · obtain ⟨x, hxP, hxy⟩ := hn
        have hxD : (fderiv ℝ g x).det ≠ 0 := by
          have hx' : x ∈ ⋃ n, P n := mem_iUnion.2 ⟨n, hxP⟩
          rw [hPcov] at hx'
          exact hx'
        exact ⟨x, hxy, huniq x _ _ (hidx x hxD) hxP⟩
    have hNfin : N.Finite := by
      rw [← hbij.image_eq]
      exact hfin.image idx
    have hsum : ∑' n, f n y = (∑ᶠ n ∈ N, σ n) * ψ y := by
      rw [tsum_eq_sum (s := hNfin.toFinset) ?_, finsum_mem_eq_finite_toFinset_sum _ hNfin,
        Finset.sum_mul]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn' : y ∈ g '' P n := hNfin.mem_toFinset.1 hn
        simp only [f, indicator_of_mem hn']
      · intro n hn
        have hn' : y ∉ g '' P n := fun h => hn (hNfin.mem_toFinset.2 h)
        simp only [f, indicator_of_notMem hn']
    rw [hsum]
    congr 1
    have hcast := AddMonoidHom.map_finsum_mem
      (fun x => (SignType.sign (fderiv ℝ g x).det : ℤ)) (Int.castAddHom ℝ) hfin
    simp only [Int.coe_castAddHom] at hcast
    unfold signedFiberCount
    rw [hcast]
    exact (finsum_mem_eq_of_bijOn idx hbij fun x hx =>
      hσsign (idx x) x (hPU _ (hidx x (hy x hx)))).symm
  have h5 : (fun y => ∑' n, f n y) =ᵐ[μ] fun y => (signedFiberCount g y : ℝ) * ψ y := by
    filter_upwards [ae_isRegularValue μ hgd] with y hy
    exact h4 y hy
  calc ∫ x, ψ (g x) * (fderiv ℝ g x).det ∂μ = ∫ x, F x ∂μ := rfl
    _ = ∑' n, ∫ x in P n, F x ∂μ := h1
    _ = ∑' n, ∫ y, f n y ∂μ := tsum_congr h2
    _ = ∫ y, ∑' n, f n y ∂μ := h3
    _ = ∫ y, (signedFiberCount g y : ℝ) * ψ y ∂μ := integral_congr_ae h5

/-- **Determinant-integral formula for the degree.** For a C¹ map f at bounded distance from an
invertible linear map and every continuous compactly supported ψ,
∫ ψ(f x) det Df(x) dμ(x) = deg f · ∫ ψ dμ. -/
theorem integral_comp_mul_det_eq_brouwerDegree_mul {f : E → E} (hf : ContDiff ℝ 1 f)
    (A : E ≃L[ℝ] E) {M : ℝ} (hM : ∀ x, ‖f x - A x‖ ≤ M) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ∫ x, ψ (f x) * (fderiv ℝ f x).det ∂μ = (brouwerDegree f : ℝ) * ∫ y, ψ y ∂μ := by
  rw [integral_comp_mul_det_eq_integral_signedFiberCount μ hf
    (fun K hK => isCompact_preimage_of_bounded hf.continuous A hM hK) hψ hψs,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_isRegularValue μ (hf.differentiable one_ne_zero)] with y hy
  rw [signedFiberCount_eq_brouwerDegree_of_bounded A hf hM hy]

/-- The determinant-integral degree ∫ ψ(f x) det Df(x) dμ(x) of f against a test function ψ. -/
noncomputable def degreeIntegral (f : E → E) (ψ : E → ℝ) : ℝ :=
  ∫ x, ψ (f x) * (fderiv ℝ f x).det ∂μ

/-- **Independence of the test function.** For a C¹ map at bounded distance from an invertible
linear map, the determinant-integral degree against any continuous compactly supported ψ with
∫ ψ dμ = 1 equals the Brouwer degree, wherever the support of ψ lies. -/
theorem degreeIntegral_eq_brouwerDegree {f : E → E} (hf : ContDiff ℝ 1 f) (A : E ≃L[ℝ] E)
    {M : ℝ} (hM : ∀ x, ‖f x - A x‖ ≤ M) {ψ : E → ℝ} (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψ1 : ∫ y, ψ y ∂μ = 1) :
    degreeIntegral μ f ψ = brouwerDegree f := by
  rw [degreeIntegral, integral_comp_mul_det_eq_brouwerDegree_mul μ hf A hM hψ hψs, hψ1, mul_one]

/-- **The degree at an arbitrary value.** Around every value h, regular or critical, and for
every ε > 0, there is a smooth test function supported in the ball of radius ε about h with
∫ ψ dμ = 1, and the determinant-integral degree against it is the Brouwer degree. -/
theorem exists_degreeIntegral_eq_brouwerDegree_ball {f : E → E} (hf : ContDiff ℝ 1 f)
    (A : E ≃L[ℝ] E) {M : ℝ} (hM : ∀ x, ‖f x - A x‖ ≤ M) (h : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ closedBall h ε ∧
      ∫ y, ψ y ∂μ = 1 ∧ degreeIntegral μ f ψ = brouwerDegree f := by
  let φ : ContDiffBump h := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨φ.normed μ, φ.contDiff_normed, φ.hasCompactSupport_normed, ?_, φ.integral_normed,
    degreeIntegral_eq_brouwerDegree μ hf A hM φ.continuous_normed φ.hasCompactSupport_normed
      φ.integral_normed⟩
  rw [φ.tsupport_normed_eq]

end Integral

end BPFixedPoints
