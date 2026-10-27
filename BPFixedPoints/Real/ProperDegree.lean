import BPFixedPoints.Real.ProperDegreeCount

/-!
# Brouwer degree of bounded perturbations of invertible linear maps

Mathlib has no Brouwer degree. On a finite-dimensional real normed space E, define the degree of
f : E → E as the signed count Σ_{f(x)=y} sign det Df(x) at a regular value y (`brouwerDegree`).
The value y is chosen by `Classical.epsilon`. Sard's theorem in equal dimensions
(`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` in Mathlib) gives regular values in every
ball (`exists_isRegularValue_mem_ball`), and almost every value is regular (`ae_isRegularValue`).

For a C¹ map f at bounded distance from an invertible linear map A, the count does not depend on
the regular value (`signedFiberCount_eq_brouwerDegree_of_bounded`), and

  deg f = sign det A   (`brouwerDegree_eq_sign_det_of_bounded`).

This gives the normalization deg A = sign det A (`brouwerDegree_continuousLinearEquiv`),
surjectivity (`surjective_of_bounded`), and invariance under the homotopies H_t = A − tB with B
bounded and C¹ (`brouwerDegree_linear_sub_smul_eq`), which are uniformly proper for t ∈ [0,1]
(`norm_le_of_linear_sub_smul_eq`). More generally the degree is unchanged by a C¹ perturbation at
bounded distance (`brouwerDegree_eq_of_bounded_sub`), the straight-line proper homotopy case.
These invariance statements follow from the computation of the degree of every map of the
homotopy, not from a general homotopy theorem for proper maps. The degree is a property of the
map, not of a value: it is the signed count at the regular values arbitrarily close to every
critical value, and `ProperDegreeIntegral` identifies it with the determinant integral against
any test function.
-/

namespace BPFixedPoints

open MeasureTheory Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Sard

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Sard's theorem in equal dimensions.** The critical values of a differentiable self-map of
a finite-dimensional real normed space form a Haar-null set. -/
theorem addHaar_image_criticalPoints_eq_zero {f : E → E} (hf : Differentiable ℝ f) :
    μ (f '' {x | (fderiv ℝ f x).det = 0}) = 0 :=
  addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x _ => (hf x).hasFDerivAt.hasFDerivWithinAt) (fun _ hx => hx)

/-- Almost every value of a differentiable self-map is regular. -/
theorem ae_isRegularValue {f : E → E} (hf : Differentiable ℝ f) :
    ∀ᵐ y ∂μ, IsRegularValue f y := by
  rw [ae_iff]
  refine measure_mono_null ?_ (addHaar_image_criticalPoints_eq_zero μ hf)
  intro y hy
  simp only [IsRegularValue, not_forall, not_not] at hy
  obtain ⟨x, hx, hdet⟩ := hy
  exact ⟨x, hdet, hx⟩

end Sard

/-- Every ball contains a regular value of a differentiable self-map. In particular regular values
exist arbitrarily close to every critical value. -/
theorem exists_isRegularValue_mem_ball {f : E → E} (hf : Differentiable ℝ f) (h : E) {ε : ℝ}
    (hε : 0 < ε) : ∃ y ∈ ball h ε, IsRegularValue f y := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let μ : Measure E := Measure.addHaar
  have hpos : 0 < μ (ball h ε) := measure_ball_pos μ h hε
  by_contra hne
  push Not at hne
  have hsub : ball h ε ⊆ {y | ¬ IsRegularValue f y} := fun y hy => hne y hy
  have hnull : μ {y | ¬ IsRegularValue f y} = 0 := ae_iff.1 (ae_isRegularValue μ hf)
  exact hpos.ne' (measure_mono_null hsub hnull)

/-- Every differentiable self-map of a finite-dimensional real normed space has a regular value. -/
theorem exists_isRegularValue {f : E → E} (hf : Differentiable ℝ f) :
    ∃ y, IsRegularValue f y := by
  obtain ⟨y, _, hy⟩ := exists_isRegularValue_mem_ball hf 0 one_pos
  exact ⟨y, hy⟩

/-- The **Brouwer degree** of f : E → E: the signed count Σ_{f(x)=y} sign det Df(x) at a regular
value y chosen by `Classical.epsilon`. Regular values exist by Sard (`exists_isRegularValue`).
For the maps treated here the count is the same at every regular value
(`signedFiberCount_eq_brouwerDegree_of_bounded`), so the choice does not matter. -/
noncomputable def brouwerDegree (f : E → E) : ℤ :=
  signedFiberCount f (Classical.epsilon (IsRegularValue f))

/-- If the signed count equals d at every regular value, the degree is d. -/
theorem brouwerDegree_eq_of_forall {f : E → E} (hf : Differentiable ℝ f) {d : ℤ}
    (h : ∀ y, IsRegularValue f y → signedFiberCount f y = d) : brouwerDegree f = d :=
  h _ (Classical.epsilon_spec (exists_isRegularValue hf))

section Bounded

variable (A : E ≃L[ℝ] E) {M : ℝ}

/-- **Degree of a bounded perturbation.** A C¹ map at bounded distance from an invertible linear
map A has degree sign det A. -/
theorem brouwerDegree_eq_sign_det_of_bounded {f : E → E} (hf : ContDiff ℝ 1 f)
    (hM : ∀ x, ‖f x - A x‖ ≤ M) : brouwerDegree f = SignType.sign (A : E →L[ℝ] E).det :=
  brouwerDegree_eq_of_forall (hf.differentiable one_ne_zero) fun _ hy =>
    signedFiberCount_eq_sign_det_of_bounded hf A hM hy

/-- **Independence of the regular value.** At every regular value the signed count of a C¹ map
at bounded distance from an invertible linear map equals its degree. -/
theorem signedFiberCount_eq_brouwerDegree_of_bounded {f : E → E} (hf : ContDiff ℝ 1 f)
    (hM : ∀ x, ‖f x - A x‖ ≤ M) {y : E} (hy : IsRegularValue f y) :
    signedFiberCount f y = brouwerDegree f := by
  rw [signedFiberCount_eq_sign_det_of_bounded hf A hM hy,
    brouwerDegree_eq_sign_det_of_bounded A hf hM]

/-- **Normalization.** An invertible linear map A has degree sign det A. -/
theorem brouwerDegree_continuousLinearEquiv :
    brouwerDegree (A : E → E) = SignType.sign (A : E →L[ℝ] E).det :=
  brouwerDegree_eq_sign_det_of_bounded A A.contDiff (M := 0) fun x => by simp

/-- The identity has degree one. -/
theorem brouwerDegree_id : brouwerDegree (id : E → E) = 1 := by
  have h := brouwerDegree_continuousLinearEquiv (ContinuousLinearEquiv.refl ℝ E)
  have hdet : ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E).det = 1 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact LinearMap.det_id
  rw [hdet, sign_one] at h
  exact h

/-- **Degree is invariant under bounded perturbation.** If f₀ is C¹ at bounded distance from an
invertible linear map and f₁ is C¹ at bounded distance from f₀, then deg f₀ = deg f₁. This is
homotopy invariance for the proper straight-line homotopy f₀ + t(f₁ − f₀). -/
theorem brouwerDegree_eq_of_bounded_sub {f₀ f₁ : E → E} (hf₀ : ContDiff ℝ 1 f₀)
    (hf₁ : ContDiff ℝ 1 f₁) (hM : ∀ x, ‖f₀ x - A x‖ ≤ M) {N : ℝ}
    (hN : ∀ x, ‖f₁ x - f₀ x‖ ≤ N) : brouwerDegree f₀ = brouwerDegree f₁ := by
  have hM₁ : ∀ x, ‖f₁ x - A x‖ ≤ N + M := fun x =>
    calc ‖f₁ x - A x‖ = ‖(f₁ x - f₀ x) + (f₀ x - A x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖f₁ x - f₀ x‖ + ‖f₀ x - A x‖ := norm_add_le _ _
      _ ≤ N + M := add_le_add (hN x) (hM x)
  rw [brouwerDegree_eq_sign_det_of_bounded A hf₀ hM,
    brouwerDegree_eq_sign_det_of_bounded A hf₁ hM₁]

omit [FiniteDimensional ℝ E] in
/-- A value outside the range is a regular value with signed count zero. -/
theorem signedFiberCount_eq_zero_of_notMem_range {f : E → E} {y : E} (hy : y ∉ Set.range f) :
    IsRegularValue f y ∧ signedFiberCount f y = 0 := by
  have hempty : f ⁻¹' {y} = ∅ := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun hx => hy ⟨x, hx⟩
  refine ⟨fun x hx => absurd ⟨x, hx⟩ hy, ?_⟩
  unfold signedFiberCount
  rw [hempty, finsum_mem_empty]

/-- **Existence from the degree.** A C¹ map at bounded distance from an invertible linear map is
surjective, since its degree sign det A is nonzero. -/
theorem surjective_of_bounded {f : E → E} (hf : ContDiff ℝ 1 f) (hM : ∀ x, ‖f x - A x‖ ≤ M) :
    Function.Surjective f := by
  intro y
  by_contra hy
  have hy' : y ∉ Set.range f := fun ⟨x, hx⟩ => hy ⟨x, hx⟩
  obtain ⟨hreg, hzero⟩ := signedFiberCount_eq_zero_of_notMem_range hy'
  rw [signedFiberCount_eq_sign_det_of_bounded hf A hM hreg] at hzero
  have hdet : (A : E →L[ℝ] E).det ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  rcases lt_or_gt_of_ne hdet with h | h
  · rw [sign_neg h] at hzero
    simp at hzero
  · rw [sign_pos h] at hzero
    simp at hzero

variable {B : E → E}

omit [FiniteDimensional ℝ E] in
/-- **Uniform properness of H_t = A − tB.** For ‖B‖ ≤ M and t ∈ [0,1], every solution of
A u − t B(u) = h satisfies ‖u‖ ≤ ‖A⁻¹‖ (‖h‖ + M). -/
theorem norm_le_of_linear_sub_smul_eq (hB : ∀ x, ‖B x‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {u h : E} (hu : A u - t • B u = h) : ‖u‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (‖h‖ + M) := by
  have htB : ‖t • B u‖ ≤ M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖B u‖ ≤ 1 * ‖B u‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hB u
  have hAu : ‖A u‖ ≤ ‖h‖ + M := by
    calc ‖A u‖ = ‖h + t • B u‖ := by rw [← hu, sub_add_cancel]
      _ ≤ ‖h‖ + ‖t • B u‖ := norm_add_le _ _
      _ ≤ ‖h‖ + M := add_le_add le_rfl htB
  calc ‖u‖ = ‖A.symm (A u)‖ := by rw [A.symm_apply_apply]
    _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A u‖ := (A.symm : E →L[ℝ] E).le_opNorm _
    _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (‖h‖ + M) := mul_le_mul_of_nonneg_left hAu (norm_nonneg _)

/-- Every map H_t = A − tB of the homotopy, B bounded and C¹, has degree sign det A. -/
theorem brouwerDegree_linear_sub_smul (hB : ContDiff ℝ 1 B) (hBM : ∀ x, ‖B x‖ ≤ M) (t : ℝ) :
    brouwerDegree (fun u => A u - t • B u) = SignType.sign (A : E →L[ℝ] E).det := by
  refine brouwerDegree_eq_sign_det_of_bounded A (M := |t| * M)
    (A.contDiff.sub (contDiff_const.smul hB)) fun x => ?_
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hBM x) (abs_nonneg t)

/-- **Homotopy invariance along H_t = A − tB.** For bounded C¹ B the degree of A u − t B(u) does
not depend on t. In particular deg (A − B) = deg A = sign det A. -/
theorem brouwerDegree_linear_sub_smul_eq (hB : ContDiff ℝ 1 B) (hBM : ∀ x, ‖B x‖ ≤ M)
    (s t : ℝ) :
    brouwerDegree (fun u => A u - s • B u) = brouwerDegree (fun u => A u - t • B u) := by
  rw [brouwerDegree_linear_sub_smul A hB hBM, brouwerDegree_linear_sub_smul A hB hBM]

end Bounded

end BPFixedPoints
