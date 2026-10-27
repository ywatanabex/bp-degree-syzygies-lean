import BPFixedPoints.Real.EdgeBranches

/-!
# Real analyticity and edge Jacobians of the two real edge branches (`real:edge-branches`)

This module completes the analytic part of `real:edge-branches` / `supp:edge-branches`.
Fix a>0. For prescribed endpoint total fields F_h,F_t>0 the edge equations
(E1) p(F_t+aq)=aF_t+q, (E2) q(F_h+ap)=aF_h+p in the incoming messages p=y_{t→h},
q=y_{h→t} have the positive branch `posBranch a (F_h,F_t) = (p⁺,q⁺)` and the negative
branch `negBranch a (F_h,F_t) = (−F_h/p⁺,−F_t/q⁺)` (`BP.posMsg_edge`, `BP.negMsg_edge`).

Proved here:
* the positive message `posMsg` is C^ω, hence real analytic, at every point of the open
  positive quadrant (`contDiffAt_posMsg`, `analyticAt_posMsg`), so both branches are real
  analytic on the open positive quadrant (`analyticOnNhd_posBranch`,
  `analyticOnNhd_negBranch`); in logarithmic coordinates F=e^{2u}, z⁺ is real analytic on all
  of ℝ² (`contDiff_omega_zPlus`, `analyticOnNhd_zPlus`);
* the edge residual `edgeMap a F_h F_t` has strict derivative `edgeJacCLM`, whose matrix in
  the standard basis is the 2×2 edge Jacobian `edgeJacobian` (`hasStrictFDerivAt_edgeMap`,
  `det_edgeJacCLM`);
* on every solution of (E1)–(E2) with F_h+ap≠0, the Jacobian determinant equals the derivative
  of the eliminated p-quadratic `msgQuad` (`det_edgeJacobian_eq_deriv_msgQuad`); consequently
  the determinant equals the square root of the discriminant, hence is positive, on the positive
  branch (`det_edgeJacobian_posBranch`, `det_edgeJacobian_posBranch_pos`), and is negative on
  the negative branch (`det_edgeJacobian_negBranch_neg`), for every a>0;
* so the edge Jacobian is invertible on both branches, as a matrix and as a continuous linear
  equivalence that is the strict derivative of the edge residual
  (`isUnit_edgeJacobian_posBranch`, `isUnit_edgeJacobian_negBranch`,
  `hasStrictFDerivAt_edgeMap_posBranch`, `hasStrictFDerivAt_edgeMap_negBranch`), and the
  linearized edge equations have only the trivial solution (`edge_linear_eq_zero`);
* the bundled statement `edgeBranches_analytic_jacobian`.

The Jacobian is that of the cleared-denominator equations (E1)–(E2) used throughout the Lean
development. At an admissible point the update denominators F_t+aq and F_h+ap are nonzero
(`edgeDenoms_posBranch_ne_zero`, and `edgeDenoms_negBranch_ne_zero` for a≠1), and there the
Jacobian of the rational form p=(aF_t+q)/(F_t+aq), q=(aF_h+p)/(F_h+ap) differs from it by the
invertible factor diag(F_t+aq,F_h+ap); that rational-form Jacobian is not formalized separately.
The implicit-function description of the branches (that they are the local solution germs near
each solution) is not formalized here; the global uniqueness `BP.eq_posMsg_of_pos` and
`BP.eq_negMsg_of_neg` already identifies every solution with a branch.
-/

namespace BPFixedPoints

namespace BP

open Real Set
open scoped ContDiff

section Analytic

variable {a : ℝ}

/-- **The positive branch is C^n for every n ≤ ω** on the open positive quadrant, as a function
of (F_h,F_t): it is a root of a quadratic with nonvanishing leading coefficient and positive
discriminant. -/
theorem contDiffAt_posMsg (ha : 0 < a) {F : ℝ × ℝ} (h1 : 0 < F.1) (h2 : 0 < F.2)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (fun F : ℝ × ℝ => posMsg a F.1 F.2) F := by
  unfold posMsg quadPosRoot
  have hD : (F.1 * F.2 + a ^ 2 * (F.1 - F.2) - 1) ^ 2 +
      4 * (a * (1 + F.2)) * (a * F.1 * (1 + F.2)) ≠ 0 := by positivity
  apply ContDiffAt.div
  · apply ContDiffAt.add
    · fun_prop
    · exact ContDiffAt.sqrt (f := fun x : ℝ × ℝ => (x.1 * x.2 + a ^ 2 * (x.1 - x.2) - 1) ^ 2 +
        4 * (a * (1 + x.2)) * (a * x.1 * (1 + x.2))) (by fun_prop) hD
  · fun_prop
  · positivity

/-- **Real analyticity of the positive message** at every point of the open positive
quadrant. -/
theorem analyticAt_posMsg (ha : 0 < a) {F : ℝ × ℝ} (h1 : 0 < F.1) (h2 : 0 < F.2) :
    AnalyticAt ℝ (fun F : ℝ × ℝ => posMsg a F.1 F.2) F :=
  (contDiffAt_posMsg ha h1 h2 (n := ω)).analyticAt

/-- The reverse positive message F ↦ posMsg a F_t F_h is real analytic on the open positive
quadrant. -/
theorem analyticAt_posMsg_swap (ha : 0 < a) {F : ℝ × ℝ} (h1 : 0 < F.1) (h2 : 0 < F.2) :
    AnalyticAt ℝ (fun F : ℝ × ℝ => posMsg a F.2 F.1) F := by
  have h := analyticAt_posMsg ha (F := (F.2, F.1)) h2 h1
  have hs : AnalyticAt ℝ (fun F : ℝ × ℝ => (F.2, F.1)) F :=
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt F).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt F)
  show AnalyticAt ℝ ((fun F : ℝ × ℝ => posMsg a F.1 F.2) ∘ (fun F : ℝ × ℝ => (F.2, F.1))) F
  exact AnalyticAt.comp (f := fun F : ℝ × ℝ => (F.2, F.1)) (x := F) h hs

/-- Positive edge branch (p⁺,q⁺)=(y⁺_{t→h},y⁺_{h→t}) as a function of F=(F_h,F_t). -/
noncomputable def posBranch (a : ℝ) (F : ℝ × ℝ) : ℝ × ℝ :=
  (posMsg a F.1 F.2, posMsg a F.2 F.1)

/-- Negative edge branch (p⁻,q⁻)=(−F_h/p⁺,−F_t/q⁺) as a function of F=(F_h,F_t). -/
noncomputable def negBranch (a : ℝ) (F : ℝ × ℝ) : ℝ × ℝ :=
  (-F.1 / posMsg a F.1 F.2, -F.2 / posMsg a F.2 F.1)

/-- **`real:edge-branches` (analyticity, positive branch).** The positive branch is real
analytic on the open positive quadrant. -/
theorem analyticOnNhd_posBranch (ha : 0 < a) :
    AnalyticOnNhd ℝ (posBranch a) (Ioi 0 ×ˢ Ioi 0) := by
  rintro F ⟨h1, h2⟩
  exact (analyticAt_posMsg ha h1 h2).prod (analyticAt_posMsg_swap ha h1 h2)

/-- **`real:edge-branches` (analyticity, negative branch).** The negative branch is real
analytic on the open positive quadrant. -/
theorem analyticOnNhd_negBranch (ha : 0 < a) :
    AnalyticOnNhd ℝ (negBranch a) (Ioi 0 ×ˢ Ioi 0) := by
  rintro F ⟨h1, h2⟩
  have hp := posMsg_pos ha (show 0 < F.1 from h1) (show 0 < F.2 from h2)
  have hq := posMsg_pos ha (show 0 < F.2 from h2) (show 0 < F.1 from h1)
  refine AnalyticAt.prod ?_ ?_
  · exact (((ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt F).neg).div
      (analyticAt_posMsg ha h1 h2) hp.ne'
  · exact (((ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt F).neg).div
      (analyticAt_posMsg_swap ha h1 h2) hq.ne'

/-- **z⁺ is C^ω in logarithmic coordinates.** The map u ↦ z⁺(u)=½log posMsg(a,e^{2u_h},e^{2u_t})
is C^ω on ℝ², strengthening `contDiff_zPlus` (stated for finite smoothness orders). -/
theorem contDiff_omega_zPlus (ha : 0 < a) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun u : ℝ × ℝ => zPlus a u.1 u.2 := by
  rw [contDiff_iff_contDiffAt]
  intro u
  unfold zPlus
  have hE : ContDiffAt ℝ n (fun u : ℝ × ℝ => (Real.exp (2 * u.1), Real.exp (2 * u.2))) u := by
    fun_prop
  have hP : ContDiffAt ℝ n (fun F : ℝ × ℝ => posMsg a F.1 F.2)
      (Real.exp (2 * u.1), Real.exp (2 * u.2)) :=
    contDiffAt_posMsg ha (Real.exp_pos _) (Real.exp_pos _)
  have hc := hP.comp u hE
  refine (hc.log ?_).div_const 2
  exact (posMsg_pos ha (Real.exp_pos _) (Real.exp_pos _)).ne'

/-- **z⁺ is real analytic on all of ℝ².** -/
theorem analyticOnNhd_zPlus (ha : 0 < a) :
    AnalyticOnNhd ℝ (fun u : ℝ × ℝ => zPlus a u.1 u.2) univ :=
  (contDiff_omega_zPlus ha (n := ω)).analyticOnNhd

end Analytic

section Jacobian

variable {a Fh Ft p q : ℝ}

/-- Edge residual (E1,E2) in the messages m=(p,q)=(y_{t→h},y_{h→t}), for fixed F_h,F_t:
(p(F_t+aq)−(aF_t+q), q(F_h+ap)−(aF_h+p)). -/
def edgeMap (a Fh Ft : ℝ) (m : ℝ × ℝ) : ℝ × ℝ :=
  (m.1 * (Ft + a * m.2) - (a * Ft + m.2), m.2 * (Fh + a * m.1) - (a * Fh + m.1))

/-- Edge Jacobian ∂(E1,E2)/∂(p,q) at (p,q). -/
def edgeJacobian (a Fh Ft p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Ft + a * q, a * p - 1; a * q - 1, Fh + a * p]

/-- The edge Jacobian as a continuous linear map on ℝ×ℝ, through the standard basis. -/
noncomputable def edgeJacCLM (a Fh Ft p q : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ) (edgeJacobian a Fh Ft p q)).toContinuousLinearMap

/-- Explicit action of the edge Jacobian on a tangent vector (v₁,v₂). -/
theorem edgeJacCLM_apply (v : ℝ × ℝ) :
    edgeJacCLM a Fh Ft p q v = ((Ft + a * q) * v.1 + (a * p - 1) * v.2,
      (a * q - 1) * v.1 + (Fh + a * p) * v.2) := by
  unfold edgeJacCLM edgeJacobian
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp

/-- **The edge residual has strict derivative given by the edge Jacobian.** -/
theorem hasStrictFDerivAt_edgeMap (a Fh Ft p q : ℝ) :
    HasStrictFDerivAt (edgeMap a Fh Ft) (edgeJacCLM a Fh Ft p q) (p, q) := by
  have h1 : HasStrictFDerivAt (fun m : ℝ × ℝ => m.1 * (Ft + a * m.2) - (a * Ft + m.2))
      ((Ft + a * q) • ContinuousLinearMap.fst ℝ ℝ ℝ + (a * p - 1) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (p, q) := by
    have := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).mul
      (((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).const_mul a).const_add Ft)
    convert this.sub ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).const_add
      (a * Ft)) using 1
    ext <;> simp [mul_comm]
  have h2 : HasStrictFDerivAt (fun m : ℝ × ℝ => m.2 * (Fh + a * m.1) - (a * Fh + m.1))
      ((a * q - 1) • ContinuousLinearMap.fst ℝ ℝ ℝ + (Fh + a * p) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (p, q) := by
    have := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).mul
      (((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).const_mul a).const_add Fh)
    convert this.sub ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((p, q) : ℝ × ℝ))).const_add
      (a * Fh)) using 1
    ext <;> simp [mul_comm]
  unfold edgeJacCLM edgeJacobian
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  exact h1.prodMk h2

/-- The edge-Jacobian determinant (F_t+aq)(F_h+ap)−(ap−1)(aq−1). -/
theorem det_edgeJacobian (a Fh Ft p q : ℝ) :
    (edgeJacobian a Fh Ft p q).det = (Ft + a * q) * (Fh + a * p) - (a * p - 1) * (a * q - 1) := by
  simp [edgeJacobian, Matrix.det_fin_two_of]

/-- The determinant of the derivative of the edge residual is the edge-Jacobian determinant. -/
theorem det_edgeJacCLM (a Fh Ft p q : ℝ) :
    (edgeJacCLM a Fh Ft p q).det = (edgeJacobian a Fh Ft p q).det := by
  unfold edgeJacCLM
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin]

/-- On a solution with F_h+ap≠0, the edge-Jacobian determinant equals the derivative
2a(1+F_t)p+(F_hF_t+a²(F_h−F_t)−1) of the eliminated quadratic `msgQuad` at p. -/
theorem det_edgeJacobian_eq_deriv_msgQuad (h1 : p * (Ft + a * q) = a * Ft + q)
    (h2 : q * (Fh + a * p) = a * Fh + p) (hden : Fh + a * p ≠ 0) :
    (edgeJacobian a Fh Ft p q).det =
      2 * (a * (1 + Ft)) * p + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) := by
  rw [det_edgeJacobian]
  apply mul_left_cancel₀ hden
  linear_combination (a * (1 + Fh) + a * (a * p - 1)) * h2 - a * (Fh + a * p) * h1

/-- At the positive root r of Ax²+Bx−C, the derivative 2Ar+B is the square root of the
discriminant. -/
theorem two_mul_quadPosRoot_add {A B C : ℝ} (hA : 0 < A) :
    2 * A * quadPosRoot A B C + B = √(B ^ 2 + 4 * A * C) := by
  unfold quadPosRoot
  field_simp
  ring

/-- **The edge Jacobian determinant on the positive branch** is the square root of the
discriminant of `msgQuad`. -/
theorem det_edgeJacobian_posBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (edgeJacobian a Fh Ft (posMsg a Fh Ft) (posMsg a Ft Fh)).det =
      √((Fh * Ft + a ^ 2 * (Fh - Ft) - 1) ^ 2 + 4 * (a * (1 + Ft)) * (a * Fh * (1 + Ft))) := by
  obtain ⟨h1, h2⟩ := posMsg_edge ha hFh hFt
  have hp := posMsg_pos ha hFh hFt
  rw [det_edgeJacobian_eq_deriv_msgQuad h1 h2 (by positivity)]
  exact two_mul_quadPosRoot_add (by positivity)

/-- **The edge Jacobian determinant is positive on the positive branch.** -/
theorem det_edgeJacobian_posBranch_pos (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    0 < (edgeJacobian a Fh Ft (posMsg a Fh Ft) (posMsg a Ft Fh)).det := by
  rw [det_edgeJacobian_posBranch ha hFh hFt]
  exact Real.sqrt_pos.2 (by positivity)

/-- On the negative branch, the derivative of `msgQuad` at p⁻=−F_h/p⁺ is negative: it is
minus the square root of the discriminant. -/
theorem deriv_msgQuad_negBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    2 * (a * (1 + Ft)) * (-Fh / posMsg a Fh Ft) + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) < 0 := by
  have hA : 0 < a * (1 + Ft) := by positivity
  obtain ⟨hQ, hp⟩ := posMsg_spec ha hFh hFt
  have hroot := two_mul_quadPosRoot_add (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1)
    (C := a * Fh * (1 + Ft)) hA
  have hD : 0 < √((Fh * Ft + a ^ 2 * (Fh - Ft) - 1) ^ 2 + 4 * (a * (1 + Ft)) *
      (a * Fh * (1 + Ft))) := Real.sqrt_pos.2 (by positivity)
  change 2 * (a * (1 + Ft)) * posMsg a Fh Ft + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) = _ at hroot
  set r := posMsg a Fh Ft
  unfold msgQuad at hQ
  have key : 2 * (a * (1 + Ft)) * (-Fh / r) + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) =
      -(2 * (a * (1 + Ft)) * r + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1)) := by
    field_simp
    linear_combination 2 * hQ
  rw [key, hroot]
  linarith

/-- **The edge Jacobian determinant is negative on the negative branch**, for every a>0. -/
theorem det_edgeJacobian_negBranch_neg (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (edgeJacobian a Fh Ft (-Fh / posMsg a Fh Ft) (-Ft / posMsg a Ft Fh)).det < 0 := by
  obtain ⟨h1, h2⟩ := negMsg_edge ha hFh hFt
  set p := -Fh / posMsg a Fh Ft
  set q := -Ft / posMsg a Ft Fh
  by_cases hph : Fh + a * p = 0
  · by_cases hqt : Ft + a * q = 0
    · -- Both denominators vanish: det = −(ap−1)(aq−1) = −(1+F_h)(1+F_t).
      rw [det_edgeJacobian, hph, hqt]
      have hap : a * p = -Fh := by linarith
      have haq : a * q = -Ft := by linarith
      rw [hap, haq]
      nlinarith
    · -- Use the symmetric identity at the other endpoint.
      have h := det_edgeJacobian_eq_deriv_msgQuad (a := a) (Fh := Ft) (Ft := Fh) (p := q) (q := p)
        h2 h1 hqt
      have hsym : (edgeJacobian a Ft Fh q p).det = (edgeJacobian a Fh Ft p q).det := by
        rw [det_edgeJacobian, det_edgeJacobian]; ring
      rw [← hsym, h]
      exact deriv_msgQuad_negBranch ha hFt hFh
  · rw [det_edgeJacobian_eq_deriv_msgQuad h1 h2 hph]
    exact deriv_msgQuad_negBranch ha hFh hFt

/-- The edge-Jacobian determinant is nonzero on the positive branch. -/
theorem det_edgeJacobian_posBranch_ne_zero (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (edgeJacobian a Fh Ft (posMsg a Fh Ft) (posMsg a Ft Fh)).det ≠ 0 :=
  (det_edgeJacobian_posBranch_pos ha hFh hFt).ne'

/-- The edge-Jacobian determinant is nonzero on the negative branch. -/
theorem det_edgeJacobian_negBranch_ne_zero (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (edgeJacobian a Fh Ft (-Fh / posMsg a Fh Ft) (-Ft / posMsg a Ft Fh)).det ≠ 0 :=
  (det_edgeJacobian_negBranch_neg ha hFh hFt).ne

/-- **The edge Jacobian is invertible on the positive branch.** -/
theorem isUnit_edgeJacobian_posBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    IsUnit (edgeJacobian a Fh Ft (posMsg a Fh Ft) (posMsg a Ft Fh)) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2
    (det_edgeJacobian_posBranch_ne_zero ha hFh hFt))

/-- **The edge Jacobian is invertible on the negative branch.** -/
theorem isUnit_edgeJacobian_negBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    IsUnit (edgeJacobian a Fh Ft (-Fh / posMsg a Fh Ft) (-Ft / posMsg a Ft Fh)) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2
    (det_edgeJacobian_negBranch_ne_zero ha hFh hFt))

/-- The edge Jacobian as a continuous linear equivalence, when its determinant is nonzero. -/
noncomputable def edgeJacEquiv (a Fh Ft p q : ℝ) (h : (edgeJacobian a Fh Ft p q).det ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (edgeJacCLM a Fh Ft p q).toContinuousLinearEquivOfDetNeZero (by rwa [det_edgeJacCLM])

/-- The underlying linear map of `edgeJacEquiv` is the edge Jacobian. -/
@[simp] theorem coe_edgeJacEquiv (h : (edgeJacobian a Fh Ft p q).det ≠ 0) :
    ((edgeJacEquiv a Fh Ft p q h : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ) =
      edgeJacCLM a Fh Ft p q := by
  ext <;> rfl

/-- **On the positive branch the edge residual has an invertible strict derivative.** -/
theorem hasStrictFDerivAt_edgeMap_posBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    HasStrictFDerivAt (edgeMap a Fh Ft)
      ((edgeJacEquiv a Fh Ft _ _ (det_edgeJacobian_posBranch_ne_zero ha hFh hFt) :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (posBranch a (Fh, Ft)) := by
  rw [coe_edgeJacEquiv]
  exact hasStrictFDerivAt_edgeMap a Fh Ft _ _

/-- **On the negative branch the edge residual has an invertible strict derivative.** -/
theorem hasStrictFDerivAt_edgeMap_negBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    HasStrictFDerivAt (edgeMap a Fh Ft)
      ((edgeJacEquiv a Fh Ft _ _ (det_edgeJacobian_negBranch_ne_zero ha hFh hFt) :
        (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) : ℝ × ℝ →L[ℝ] ℝ × ℝ)
      (negBranch a (Fh, Ft)) := by
  rw [coe_edgeJacEquiv]
  exact hasStrictFDerivAt_edgeMap a Fh Ft _ _

/-- The positive branch is a zero of the edge residual. -/
theorem edgeMap_posBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    edgeMap a Fh Ft (posBranch a (Fh, Ft)) = 0 := by
  obtain ⟨h1, h2⟩ := posMsg_edge ha hFh hFt
  simp only [edgeMap, posBranch, h1, h2, sub_self, Prod.mk_zero_zero]

/-- The negative branch is a zero of the edge residual. -/
theorem edgeMap_negBranch (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    edgeMap a Fh Ft (negBranch a (Fh, Ft)) = 0 := by
  obtain ⟨h1, h2⟩ := negMsg_edge ha hFh hFt
  simp only [edgeMap, negBranch, h1, h2, sub_self, Prod.mk_zero_zero]

/-- **Linearized edge equations.** If the edge-Jacobian determinant is nonzero, the
linearized system J(v,w)=0 has only the trivial solution. -/
theorem edge_linear_eq_zero {v w : ℝ} (hdet : (edgeJacobian a Fh Ft p q).det ≠ 0)
    (h1 : (Ft + a * q) * v + (a * p - 1) * w = 0)
    (h2 : (a * q - 1) * v + (Fh + a * p) * w = 0) : v = 0 ∧ w = 0 := by
  rw [det_edgeJacobian] at hdet
  constructor
  · have : ((Ft + a * q) * (Fh + a * p) - (a * p - 1) * (a * q - 1)) * v = 0 := by
      linear_combination (Fh + a * p) * h1 - (a * p - 1) * h2
    exact (mul_eq_zero.1 this).resolve_left hdet
  · have : ((Ft + a * q) * (Fh + a * p) - (a * p - 1) * (a * q - 1)) * w = 0 := by
      linear_combination (Ft + a * q) * h2 - (a * q - 1) * h1
    exact (mul_eq_zero.1 this).resolve_left hdet

/-- The update denominators are positive on the positive branch. -/
theorem edgeDenoms_posBranch_ne_zero (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    Ft + a * posMsg a Ft Fh ≠ 0 ∧ Fh + a * posMsg a Fh Ft ≠ 0 := by
  have hp := posMsg_pos ha hFh hFt
  have hq := posMsg_pos ha hFt hFh
  exact ⟨by positivity, by positivity⟩

/-- For a≠1 the update denominators are nonzero on the negative branch. -/
theorem edgeDenoms_negBranch_ne_zero (ha : 0 < a) (ha1 : a ≠ 1) (hFh : 0 < Fh)
    (hFt : 0 < Ft) :
    Ft + a * (-Ft / posMsg a Ft Fh) ≠ 0 ∧ Fh + a * (-Fh / posMsg a Fh Ft) ≠ 0 := by
  have hp := posMsg_pos ha hFh hFt
  have hq := posMsg_pos ha hFt hFh
  have hpa := posMsg_ne ha ha1 hFh hFt
  have hqa := posMsg_ne ha ha1 hFt hFh
  constructor
  · intro h
    apply hqa
    field_simp at h
    nlinarith
  · intro h
    apply hpa
    field_simp at h
    nlinarith

/-- **`real:edge-branches` (analytic part).** For a>0, both real edge branches are real
analytic on the open positive quadrant of (F_h,F_t), they solve the edge equations, and their
edge Jacobians are invertible (determinant positive on the positive branch and negative on the
negative branch). -/
theorem edgeBranches_analytic_jacobian (ha : 0 < a) :
    AnalyticOnNhd ℝ (posBranch a) (Ioi 0 ×ˢ Ioi 0) ∧
      AnalyticOnNhd ℝ (negBranch a) (Ioi 0 ×ˢ Ioi 0) ∧
      ∀ F ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        edgeMap a F.1 F.2 (posBranch a F) = 0 ∧ edgeMap a F.1 F.2 (negBranch a F) = 0 ∧
        0 < (edgeJacobian a F.1 F.2 (posBranch a F).1 (posBranch a F).2).det ∧
        (edgeJacobian a F.1 F.2 (negBranch a F).1 (negBranch a F).2).det < 0 := by
  refine ⟨analyticOnNhd_posBranch ha, analyticOnNhd_negBranch ha, ?_⟩
  rintro ⟨Fh, Ft⟩ ⟨hFh, hFt⟩
  exact ⟨edgeMap_posBranch ha hFh hFt, edgeMap_negBranch ha hFh hFt,
    det_edgeJacobian_posBranch_pos ha hFh hFt, det_edgeJacobian_negBranch_neg ha hFh hFt⟩

end Jacobian

end BP

end BPFixedPoints
