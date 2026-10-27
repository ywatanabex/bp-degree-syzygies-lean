import BPFixedPoints.Real.SectorCompactness
import BPFixedPoints.Real.ImplicitRegularity

/-!
# Transfer BP nondegeneracy to the vertex map

Write b_i=exp(2h_i). The sector vertex and message maps satisfy BP, and the
pair has left inverse u_i=log(F_i)/2. Differentiate these identities: at an
invertible BP Jacobian, the vertex derivative is injective, hence invertible.
-/

namespace BPFixedPoints.Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  {G : Multigraph V E} {a : E → ℝ}

/-- BP polynomial simplicity is equivalent to injectivity of the real Fréchet derivative. -/
theorem fderiv_bpPoly_injective_of_isSimpleSolution {b : V → ℝ} {y : Dart E → ℝ}
    (hnd : G.IsSimpleSolution a b y) :
    Function.Injective (fderiv ℝ (fun z => G.bpPoly a b z) y) := by
  let L : (Dart E → ℝ) →L[ℝ] (Dart E → ℝ) :=
    ContinuousLinearMap.pi fun α => (G.bpMvPoly a b α).gradCLM y
  have hL : ∀ w, L w = (G.jacobian a b y).mulVec w := by
    intro w
    funext α
    exact MvPolynomial.gradCLM_apply _ _ _
  have hd : HasFDerivAt (fun z => G.bpPoly a b z) L y := by
    have h := (hasStrictFDerivAt_pi.2 fun α =>
      (G.bpMvPoly a b α).hasStrictFDerivAt_eval y).hasFDerivAt
    simpa only [G.eval_bpMvPoly] using h
  rw [hd.fderiv]
  have hunit : IsUnit (G.jacobian a b y) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hnd)
  intro v w hvw
  apply Matrix.mulVec_injective_iff_isUnit.2 hunit
  rw [← hL, ← hL]
  exact hvw

/-- The BP residual is differentiable in both external fields and messages. -/
theorem differentiable_bpPoly_parameters (a : E → ℝ) :
    Differentiable ℝ (fun p : (V → ℝ) × (Dart E → ℝ) => G.bpPoly a p.1 p.2) := by
  intro p
  apply differentiableAt_pi.2
  intro α
  unfold bpPoly cavity
  fun_prop

/-- The vertex derivative at a point corresponding to a nondegenerate BP solution is injective. -/
theorem fderiv_sectorField_injective_of_isSimpleSolution
    (hG : G.Loopless) (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
    {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2)
    (hnd : G.IsSimpleSolution a b (G.sectorMsg a S u)) :
    Function.Injective (fderiv ℝ (G.sectorField a S) u) := by
  let B : (V → ℝ) → V → ℝ := fun h i => Real.exp (2 * h i)
  let F : (V → ℝ) × (Dart E → ℝ) → Dart E → ℝ :=
    fun p => G.bpPoly a (B p.1) p.2
  let r : (V → ℝ) × (Dart E → ℝ) → V → ℝ :=
    fun p i => Real.log (G.totalField (B p.1) p.2 i) / 2
  have hB : Differentiable ℝ B := by dsimp [B]; fun_prop
  have hF : Differentiable ℝ F :=
    (differentiable_bpPoly_parameters (G := G) a).comp
      ((hB.comp differentiable_fst).prodMk differentiable_snd)
  have hb' (x : V → ℝ) (i : V) : 0 < B (G.sectorField a S x) i := Real.exp_pos _
  have hfield (x : V → ℝ) (i : V) :
      G.sectorField a S x i = Real.log (B (G.sectorField a S x) i) / 2 := by
    simp [B]
  have htotal (x : V → ℝ) (i : V) :
      G.totalField (B (G.sectorField a S x)) (G.sectorMsg a S x) i =
        Real.exp (2 * x i) :=
    (totalField_sectorMsg_iff ha hG hS (hb' x) i).2 (hfield x i)
  have hzero (x : V → ℝ) : F (G.sectorField a S x, G.sectorMsg a S x) = 0 := by
    funext α
    exact (isAdmissibleSolution_sectorMsg ha ha1 hG hS (hb' x) (hfield x)).1 α
  have hleft (x : V → ℝ) : r (G.sectorField a S x, G.sectorMsg a S x) = x := by
    funext i
    dsimp [r]
    rw [htotal, Real.log_exp]
    ring
  have hr : DifferentiableAt ℝ r (G.sectorField a S u, G.sectorMsg a S u) := by
    apply differentiableAt_pi.2
    intro i
    change DifferentiableAt ℝ
      (fun p : (V → ℝ) × (Dart E → ℝ) => Real.log (G.totalField (B p.1) p.2 i) / 2) _
    simp only [div_eq_mul_inv]
    apply DifferentiableAt.mul_const
    apply DifferentiableAt.log
    · dsimp [B, totalField]
      fun_prop
    · change G.totalField (B (G.sectorField a S u)) (G.sectorMsg a S u) i ≠ 0
      rw [htotal]
      exact Real.exp_ne_zero _
  have hBu : B (G.sectorField a S u) = b := by
    funext i
    dsimp [B]
    rw [hu]
    convert Real.exp_log (hb i) using 1 <;> congr 1 <;> ring
  apply fderiv_injective_of_implicit_leftInverse
    ((contDiff_sectorField (n := 1) ha S).differentiable one_ne_zero u)
    ((contDiff_sectorMsg (n := 1) ha S).differentiable one_ne_zero u)
    (hF _) hr hzero hleft
  change Function.Injective
    (fderiv ℝ (fun y => G.bpPoly a (B (G.sectorField a S u)) y) (G.sectorMsg a S u))
  rw [hBu]
  exact fderiv_bpPoly_injective_of_isSimpleSolution hnd

/-- At a nondegenerate BP solution, the vertex Jacobian determinant is nonzero. -/
theorem det_fderiv_sectorField_ne_zero
    (hG : G.Loopless) (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
    {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2)
    (hnd : G.IsSimpleSolution a b (G.sectorMsg a S u)) :
    (fderiv ℝ (G.sectorField a S) u).toLinearMap.det ≠ 0 := by
  let L := (fderiv ℝ (G.sectorField a S) u).toLinearMap
  have hinj : Function.Injective L :=
    fderiv_sectorField_injective_of_isSimpleSolution hG ha ha1 hb hS hu hnd
  exact (LinearEquiv.isUnit_det' (LinearEquiv.ofInjectiveEndo L hinj)).ne_zero

end BPFixedPoints.Multigraph
