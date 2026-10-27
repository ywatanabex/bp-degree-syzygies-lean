import BPFixedPoints.Real.RegularFiber

/-!
# Signed fiber counts of bounded perturbations of invertible linear maps

Let E be a finite-dimensional real normed space, A : E ≃L[ℝ] E, and f : E → E a C¹ map with
sup_x ‖f x − A x‖ < ∞. Then f is proper (`isCompact_preimage_of_bounded`), every regular value y
has a finite fiber (`finite_fiber_of_bounded`), and

  Σ_{f(x)=y} sign det Df(x) = sign det A   (`signedFiberCount_eq_sign_det_of_bounded`).

In the form f = A − B with B bounded and C¹ this is `signedFiberCount_linear_sub_of_bounded`.
For A = id on an inner-product space, a cutoff agrees with f − y near the fiber and with the
identity outside a ball, so `finsum_sign_det_regular_fiber_of_eq_id_outside` applies. A linear
isomorphism with a Euclidean space transports the count to normed spaces
(`signedFiberCount_conj`), and composing with A⁻¹ reduces the general case to A = id.
-/

namespace BPFixedPoints

open Metric Set Filter Topology Function

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `y` is a regular value of `f` if `det Df(x) ≠ 0` at every point `x` of the fiber over `y`. -/
def IsRegularValue (f : E → E) (y : E) : Prop :=
  ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0

/-- The signed count Σ_{f(x)=y} sign det Df(x) of the fiber over `y`. As a finite sum it is zero
when the fiber meets the nondegenerate locus in an infinite set. -/
noncomputable def signedFiberCount (f : E → E) (y : E) : ℤ :=
  ∑ᶠ x ∈ f ⁻¹' {y}, (SignType.sign (fderiv ℝ f x).det : ℤ)

end Defs

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative determinant is invariant under conjugation by a linear isomorphism. -/
theorem det_fderiv_conj (e : E ≃L[ℝ] F) {f : E → E} {x : E} (hf : DifferentiableAt ℝ f x) :
    (fderiv ℝ (fun z => e (f (e.symm z))) (e x)).det = (fderiv ℝ f x).det := by
  have h1 : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
    rw [e.symm_apply_apply]
    exact hf.hasFDerivAt
  have hd : HasFDerivAt (fun z => e (f (e.symm z)))
      ((e : E →L[ℝ] F).comp ((fderiv ℝ f x).comp (e.symm : F →L[ℝ] E))) (e x) :=
    e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hd.fderiv]
  exact LinearMap.det_conj (fderiv ℝ f x : E →ₗ[ℝ] E) e.toLinearEquiv

/-- Regular values correspond under conjugation by a linear isomorphism. -/
theorem isRegularValue_conj_iff (e : E ≃L[ℝ] F) {f : E → E} (hf : Differentiable ℝ f) (y : E) :
    IsRegularValue (fun z => e (f (e.symm z))) (e y) ↔ IsRegularValue f y := by
  constructor
  · intro h x hx
    have h' := h (e x) (by simp [hx])
    rwa [det_fderiv_conj e (hf x)] at h'
  · intro h z hz
    have hz' : f (e.symm z) = y := e.injective hz
    have hdet := det_fderiv_conj e (hf (e.symm z))
    rw [e.apply_symm_apply] at hdet
    rw [hdet]
    exact h _ hz'

/-- The signed fiber count is invariant under conjugation by a linear isomorphism. -/
theorem signedFiberCount_conj (e : E ≃L[ℝ] F) {f : E → E} (hf : Differentiable ℝ f) (y : E) :
    signedFiberCount (fun z => e (f (e.symm z))) (e y) = signedFiberCount f y := by
  unfold signedFiberCount
  symm
  apply finsum_mem_eq_of_bijOn e
  · refine ⟨fun x hx => ?_, e.injective.injOn, fun z hz => ?_⟩
    · change e (f (e.symm (e x))) = e y
      rw [e.symm_apply_apply, show f x = y from hx]
    · exact ⟨e.symm z, e.injective hz, e.apply_symm_apply z⟩
  · intro x _
    rw [det_fderiv_conj e (hf x)]

end Conj

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- At a point with nonzero derivative determinant, a C¹ map has a strict derivative which is a
continuous linear equivalence. -/
theorem exists_equiv_hasStrictFDerivAt_of_det_ne_zero {f : E → E} (hf : ContDiff ℝ 1 f)
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

/-- A compact fiber over a regular value of a C¹ map is finite. -/
theorem finite_fiber_of_isCompact {f : E → E} (hf : ContDiff ℝ 1 f) {y : E}
    (hc : IsCompact (f ⁻¹' {y})) (hy : IsRegularValue f y) : (f ⁻¹' {y}).Finite := by
  classical
  let Z := f ⁻¹' {y}
  have hloc : ∀ x : Z, ∃ U : Set E, IsOpen U ∧ x.1 ∈ U ∧ InjOn f U := by
    intro x
    obtain ⟨e, he⟩ := exists_equiv_hasStrictFDerivAt_of_det_ne_zero hf (hy x.1 x.2)
    let g := he.toOpenPartialHomeomorph f
    exact ⟨g.source, g.open_source, he.mem_toOpenPartialHomeomorph_source, g.injOn⟩
  choose U hU hxU hUinj using hloc
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  refine (t.finite_toSet.image (Subtype.val : Z → E)).subset ?_
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (ht hx)
  exact ⟨z, hz, (hUinj z hxz (hxU z)
    ((show f x = y from hx).trans (show f z.1 = y from z.2).symm)).symm⟩

/-- A continuous map at bounded distance from an invertible linear map is proper: preimages of
compact sets are compact. -/
theorem isCompact_preimage_of_bounded {f : E → E} (hf : Continuous f) (A : E ≃L[ℝ] E) {M : ℝ}
    (hM : ∀ x, ‖f x - A x‖ ≤ M) {K : Set E} (hK : IsCompact K) : IsCompact (f ⁻¹' K) := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E)
  refine (isCompact_closedBall (0 : E) (‖(A.symm : E →L[ℝ] E)‖ * (r + M))).of_isClosed_subset
    (hK.isClosed.preimage hf) ?_
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hfx : ‖f x‖ ≤ r := mem_closedBall_zero_iff.1 (hr hx)
  have hAx : ‖A x‖ ≤ r + M := by
    calc ‖A x‖ = ‖f x - (f x - A x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖f x‖ + ‖f x - A x‖ := norm_sub_le _ _
      _ ≤ r + M := add_le_add hfx (hM x)
  calc ‖x‖ = ‖A.symm (A x)‖ := by rw [A.symm_apply_apply]
    _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * ‖A x‖ := (A.symm : E →L[ℝ] E).le_opNorm _
    _ ≤ ‖(A.symm : E →L[ℝ] E)‖ * (r + M) := mul_le_mul_of_nonneg_left hAx (norm_nonneg _)

/-- A regular value of a C¹ map at bounded distance from an invertible linear map has a finite
fiber. -/
theorem finite_fiber_of_bounded {f : E → E} (hf : ContDiff ℝ 1 f) (A : E ≃L[ℝ] E) {M : ℝ}
    (hM : ∀ x, ‖f x - A x‖ ≤ M) {y : E} (hy : IsRegularValue f y) : (f ⁻¹' {y}).Finite :=
  finite_fiber_of_isCompact hf
    (isCompact_preimage_of_bounded hf.continuous A hM isCompact_singleton) hy

end Normed

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- On an inner-product space, a C¹ map at bounded distance from the identity has signed count
one at every regular value. -/
theorem signedFiberCount_eq_one_of_bounded_inner {g : H → H} (hg : ContDiff ℝ 1 g) {M : ℝ}
    (hM : ∀ x, ‖g x - x‖ ≤ M) {y : H} (hy : IsRegularValue g y) : signedFiberCount g y = 1 := by
  classical
  let _ : MeasurableSpace H := borel H
  have _ : BorelSpace H := ⟨rfl⟩
  let M' : ℝ := max M 0
  have hM' : ∀ x, ‖x - g x‖ ≤ M' := fun x => by
    rw [norm_sub_rev]
    exact (hM x).trans (le_max_left _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  let ρ : ℝ := ‖y‖ + M' + 1
  have hρ : 0 < ρ := by positivity
  let χ : ContDiffBump (0 : H) := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  -- The cutoff equals g − y on the ball of radius ρ and the identity outside radius 2ρ.
  let φ : H → H := fun x => x - (χ x) • (x - g x + y)
  have hφ : ContDiff ℝ 1 φ :=
    contDiff_id.sub (χ.contDiff.smul ((contDiff_id.sub hg).add contDiff_const))
  have hout : ∀ x, 2 * ρ ≤ ‖x‖ → φ x = x := by
    intro x hx
    have hc : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    simp only [φ, hc, zero_smul, sub_zero]
  have hbound : ∀ x, ‖φ x‖ < 1 → ‖x‖ < ρ := by
    intro x hx
    have h1 : ‖(χ x) • (x - g x + y)‖ ≤ M' + ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
      calc χ x * ‖x - g x + y‖ ≤ 1 * (M' + ‖y‖) :=
            mul_le_mul χ.le_one ((norm_add_le _ _).trans (add_le_add (hM' x) le_rfl))
              (norm_nonneg _) zero_le_one
        _ = M' + ‖y‖ := one_mul _
    have h2 : ‖x‖ ≤ ‖φ x‖ + ‖(χ x) • (x - g x + y)‖ := by
      calc ‖x‖ = ‖φ x + (χ x) • (x - g x + y)‖ := by simp only [φ, sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp only [ρ]
    linarith
  have hloc : ∀ z, ‖z‖ < ρ → φ =ᶠ[𝓝 z] fun w => g w - y := by
    intro z hz
    filter_upwards [χ.eventuallyEq_one_of_mem_ball (mem_ball_zero_iff.2 hz)] with w hw
    simp only [φ, hw, Pi.one_apply, one_smul]
    abel
  have hfib : ∀ x, g x = y → ‖x‖ < ρ := by
    intro x hx
    have h1 : ‖x‖ ≤ ‖g x‖ + ‖x - g x‖ := by
      calc ‖x‖ = ‖g x + (x - g x)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 := hM' x
    have h3 : ‖g x‖ = ‖y‖ := by rw [hx]
    dsimp only [ρ]
    linarith
  have hset : g ⁻¹' {y} = {x : H | φ x = 0} := by
    ext x
    constructor
    · intro hx
      change φ x = 0
      rw [(hloc x (hfib x hx)).self_of_nhds]
      exact sub_eq_zero.2 hx
    · intro hx
      have hx0 : φ x = 0 := hx
      have hxρ : ‖x‖ < ρ := hbound x (by rw [hx0, norm_zero]; exact one_pos)
      have hφx := (hloc x hxρ).self_of_nhds
      change g x = y
      exact sub_eq_zero.1 (hφx.symm.trans hx0)
  have hdet : ∀ x, g x = y → (fderiv ℝ φ x).det = (fderiv ℝ g x).det := by
    intro x hx
    rw [(hloc x (hfib x hx)).fderiv_eq, fderiv_sub_const]
  have hnd : ∀ x, φ x = 0 → (fderiv ℝ φ x).det ≠ 0 := by
    intro x hx
    have hx' : x ∈ g ⁻¹' {y} := by
      rw [hset]
      exact hx
    rw [hdet x hx']
    exact hy x hx'
  have h1 := finsum_sign_det_regular_fiber_of_eq_id_outside hφ (by linarith : 0 < 2 * ρ) hout hnd
  unfold signedFiberCount
  refine (finsum_mem_congr hset fun x hx => ?_).trans h1
  have hx' : x ∈ g ⁻¹' {y} := by
    rw [hset]
    exact hx
  rw [hdet x hx']

end Inner

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A C¹ map at bounded distance from the identity has signed count one at every regular value. -/
theorem signedFiberCount_eq_one_of_bounded {g : E → E} (hg : ContDiff ℝ 1 g) {M : ℝ}
    (hM : ∀ x, ‖g x - x‖ ≤ M) {y : E} (hy : IsRegularValue g y) : signedFiberCount g y = 1 := by
  let H := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e : E ≃L[ℝ] H := ContinuousLinearEquiv.ofFinrankEq (by simp [H])
  have hd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hg' : ContDiff ℝ 1 (fun z => e (g (e.symm z))) :=
    e.contDiff.comp (hg.comp e.symm.contDiff)
  have hM' : ∀ z, ‖e (g (e.symm z)) - z‖ ≤ ‖(e : E →L[ℝ] H)‖ * M := by
    intro z
    have hz : e (g (e.symm z)) - z = e (g (e.symm z) - e.symm z) := by
      rw [map_sub, e.apply_symm_apply]
    rw [hz]
    exact ((e : E →L[ℝ] H).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
  rw [← signedFiberCount_conj e hd]
  exact signedFiberCount_eq_one_of_bounded_inner hg' hM' ((isRegularValue_conj_iff e hd y).2 hy)

/-- **Signed count for a bounded perturbation of an invertible linear map.** If f is C¹ with
‖f x − A x‖ ≤ M for all x, then Σ_{f(x)=y} sign det Df(x) = sign det A at every regular value y. -/
theorem signedFiberCount_eq_sign_det_of_bounded {f : E → E} (hf : ContDiff ℝ 1 f)
    (A : E ≃L[ℝ] E) {M : ℝ} (hM : ∀ x, ‖f x - A x‖ ≤ M) {y : E} (hy : IsRegularValue f y) :
    signedFiberCount f y = SignType.sign (A : E →L[ℝ] E).det := by
  let g : E → E := fun x => A.symm (f x)
  have hg : ContDiff ℝ 1 g := A.symm.contDiff.comp hf
  have hgM : ∀ x, ‖g x - x‖ ≤ ‖(A.symm : E →L[ℝ] E)‖ * M := by
    intro x
    have hx : g x - x = A.symm (f x - A x) := by
      simp only [g, map_sub, A.symm_apply_apply]
    rw [hx]
    exact ((A.symm : E →L[ℝ] E).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _))
  have hdf : ∀ x, (fderiv ℝ f x).det = (A : E →L[ℝ] E).det * (fderiv ℝ g x).det := by
    intro x
    have hfun : f = fun x => A (g x) := by
      funext x
      simp only [g, A.apply_symm_apply]
    have h : HasFDerivAt (fun x => A (g x)) ((A : E →L[ℝ] E).comp (fderiv ℝ g x)) x :=
      A.hasFDerivAt.comp x ((hg.differentiable one_ne_zero) x).hasFDerivAt
    conv_lhs => rw [hfun, h.fderiv]
    exact LinearMap.det_comp _ _
  have hset : g ⁻¹' {A.symm y} = f ⁻¹' {y} := by
    ext x
    simp only [g, mem_preimage, mem_singleton_iff, A.symm.injective.eq_iff]
  have hgy : IsRegularValue g (A.symm y) := by
    intro x hx
    have hfx : f x = y := by
      have hx' : x ∈ f ⁻¹' {y} := by
        rw [← hset]
        exact hx
      exact hx'
    have hne := hy x hfx
    rw [hdf x] at hne
    exact right_ne_zero_of_mul hne
  have h1 := signedFiberCount_eq_one_of_bounded hg hgM hgy
  unfold signedFiberCount at h1 ⊢
  rw [hset] at h1
  have hterm : ∀ x, (SignType.sign (fderiv ℝ f x).det : ℤ) =
      (SignType.sign (A : E →L[ℝ] E).det : ℤ) * (SignType.sign (fderiv ℝ g x).det : ℤ) := by
    intro x
    rw [hdf x, sign_mul, SignType.coe_mul]
  simp_rw [hterm]
  rw [← mul_finsum_mem, h1, mul_one]

/-- **Signed count for A − B.** For A invertible linear and B C¹ with ‖B x‖ ≤ M, at every
regular value y of f = A − B, Σ_{f(z)=y} sign det Df(z) = sign det A. -/
theorem signedFiberCount_linear_sub_of_bounded (A : E ≃L[ℝ] E) {B : E → E}
    (hB : ContDiff ℝ 1 B) {M : ℝ} (hM : ∀ x, ‖B x‖ ≤ M) {y : E}
    (hy : IsRegularValue (fun x => A x - B x) y) :
    signedFiberCount (fun x => A x - B x) y = SignType.sign (A : E →L[ℝ] E).det :=
  signedFiberCount_eq_sign_det_of_bounded (A.contDiff.sub hB) A
    (fun x => by rw [sub_sub_cancel_left, norm_neg]; exact hM x) hy

end Normed

end BPFixedPoints
