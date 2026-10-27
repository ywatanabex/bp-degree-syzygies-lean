import BPFixedPoints.Real.EdgeBranchAnalytic
import BPFixedPoints.Real.SectorOddness

/-!
# Real-analytic vertex coordinates on a real sign sector (`real:vertex-map`)

This module completes the local statement of `real:vertex-map` / `supp:vertex-map`.
Fix a_e>0, a_e≠1, b_i>0 and an Eulerian edge set S, and put h_i=½log b_i. The point bijection
between the vertex fiber 𝔥_S(u)=h and the admissible real BP solutions with negative-edge
set S is `sectorFieldFiberEquiv` (from `isAdmissibleSolution_sectorMsg`,
`negSupport_sectorMsg`, `eq_sectorMsg`). It is given by u ↦ `sectorMsg a S u` and
y ↦ `vertexCoord b y` = (½log F_i(y))_i.

Proved here:
* the vertex map 𝔥_S and the sector-message map u ↦ y are C^ω, hence real analytic, on all
  of ℝ^V (`contDiff_omega_sectorField`, `contDiff_omega_sectorMsg`,
  `analyticOnNhd_sectorField`, `analyticOnNhd_sectorMsg`);
* the inverse y ↦ `vertexCoord b y` is real analytic on the open set `posFieldSet b` of message
  vectors with all total fields positive (`isOpen_posFieldSet`, `analyticOnNhd_vertexCoord`),
  which contains every admissible real solution (`mem_posFieldSet_of_isAdmissibleSolution`);
  the two maps restrict to mutually inverse bijections between the vertex fiber and the
  sector (`sectorFieldFiberEquiv_apply_coe`, `sectorFieldFiberEquiv_symm_apply_coe`);
* **nondegeneracy is preserved in both directions**: at a point u of the fiber, the BP Jacobian
  determinant at `sectorMsg a S u` is nonzero iff the derivative of 𝔥_S at u is injective, iff
  its determinant is nonzero (`isSimpleSolution_sectorMsg_iff`,
  `isSimpleSolution_sectorMsg_iff_det`), and correspondingly for every admissible real solution
  (`isSimpleSolution_iff_fderiv_sectorField_injective`). The implication from BP to the vertex
  map is `fderiv_sectorField_injective_of_isSimpleSolution`; the converse, proved here
  (`fderiv_bpPoly_injective_sectorMsg`, which needs only a_e>0, loopless G and b_i>0),
  eliminates the messages through the invertible edge
  Jacobians of `real:edge-branches` (`BP.det_edgeJacobian_posBranch_ne_zero`,
  `BP.det_edgeJacobian_negBranch_ne_zero`) by the chain-rule lemma
  `fderiv_injective_of_edge_elimination`;
* the bundled statement `sectorVertexMap_analytic`.

Thus "the correspondence preserves the local real analytic solution spaces" is formalized as:
the two solution sets are identified by restrictions of real-analytic maps defined on open
neighbourhoods (all of ℝ^V, and `posFieldSet b`), mutually inverse on the solution sets. It is
not formalized as an isomorphism of analytic space germs with their (possibly nonreduced)
structure sheaves, and no statement about multiplicities at degenerate solutions is made.
-/

namespace BPFixedPoints

open Set
open scoped ContDiff

section Elimination

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Chain-rule elimination of edge messages.** Let Φ parametrize messages by vertex
coordinates, with E(Φ z,Ex z)=0 (edge equations at the fields Ex z) and K(𝔥 z,Φ z)=Ex z
(consistency of the total fields at the external field 𝔥 z). Suppose every message direction
killed by DP is killed by the derivative of y ↦ E(y,K(𝔥 u,y)), the partial derivative of E in
the messages is injective (invertible edge Jacobians), DEx is surjective, the partial derivative
of K in the external field is injective, and D𝔥 is injective. Then DP is injective at Φ u. -/
theorem fderiv_injective_of_edge_elimination
    {Φ : X → Y} {Ex 𝔥 : X → X} {E : Y × X → Y} {K : X × Y → X} {P : Y → Y} {u : X}
    (hΦ : DifferentiableAt 𝕜 Φ u) (hEx : DifferentiableAt 𝕜 Ex u)
    (h𝔥 : DifferentiableAt 𝕜 𝔥 u)
    (hE : DifferentiableAt 𝕜 E (Φ u, Ex u)) (hK : DifferentiableAt 𝕜 K (𝔥 u, Φ u))
    (hEΦ : ∀ z, E (Φ z, Ex z) = 0) (hKΦ : ∀ z, K (𝔥 z, Φ z) = Ex z)
    (hEP : ∀ v, fderiv 𝕜 P (Φ u) v = 0 →
      fderiv 𝕜 (fun y => E (y, K (𝔥 u, y))) (Φ u) v = 0)
    (hEinj : Function.Injective (fderiv 𝕜 (fun y => E (y, Ex u)) (Φ u)))
    (hExsurj : Function.Surjective (fderiv 𝕜 Ex u))
    (hKinj : Function.Injective (fderiv 𝕜 (fun h => K (h, Φ u)) (𝔥 u)))
    (h𝔥inj : Function.Injective (fderiv 𝕜 𝔥 u)) :
    Function.Injective (fderiv 𝕜 P (Φ u)) := by
  set E' := fderiv 𝕜 E (Φ u, Ex u)
  set K' := fderiv 𝕜 K (𝔥 u, Φ u)
  set Φ' := fderiv 𝕜 Φ u
  set Ex' := fderiv 𝕜 Ex u
  set 𝔥' := fderiv 𝕜 𝔥 u
  -- Partial derivatives.
  have hEy : fderiv 𝕜 (fun y => E (y, Ex u)) (Φ u) = E'.comp (ContinuousLinearMap.inl 𝕜 Y X) :=
    (hE.hasFDerivAt.comp (Φ u) (hasFDerivAt_prodMk_left (Φ u) (Ex u))).fderiv
  have hKh : fderiv 𝕜 (fun h => K (h, Φ u)) (𝔥 u) = K'.comp (ContinuousLinearMap.inl 𝕜 X Y) :=
    (hK.hasFDerivAt.comp (𝔥 u) (hasFDerivAt_prodMk_left (𝔥 u) (Φ u))).fderiv
  have hpt : (Φ u, K (𝔥 u, Φ u)) = (Φ u, Ex u) := by rw [hKΦ u]
  have hT : fderiv 𝕜 (fun y => E (y, K (𝔥 u, y))) (Φ u) =
      E'.comp ((ContinuousLinearMap.id 𝕜 Y).prod (K'.comp (ContinuousLinearMap.inr 𝕜 X Y))) := by
    have hin : HasFDerivAt (fun y => (y, K (𝔥 u, y)))
        ((ContinuousLinearMap.id 𝕜 Y).prod (K'.comp (ContinuousLinearMap.inr 𝕜 X Y))) (Φ u) :=
      (hasFDerivAt_id (Φ u)).prodMk
        (hK.hasFDerivAt.comp (Φ u) (hasFDerivAt_prodMk_right (𝔥 u) (Φ u)))
    have hE2 : HasFDerivAt E E' (Φ u, K (𝔥 u, Φ u)) := by
      rw [hpt]; exact hE.hasFDerivAt
    exact (hE2.comp (Φ u) hin).fderiv
  -- Differentiated identities.
  have hD1 : E'.comp (Φ'.prod Ex') = 0 := by
    have h := hE.hasFDerivAt.comp u (hΦ.hasFDerivAt.prodMk hEx.hasFDerivAt)
    have heq : (fun z => E (Φ z, Ex z)) = fun _ => (0 : Y) := funext hEΦ
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.unique (hasFDerivAt_const _ _)
  have hD2 : K'.comp (𝔥'.prod Φ') = Ex' := by
    have h := hK.hasFDerivAt.comp u (h𝔥.hasFDerivAt.prodMk hΦ.hasFDerivAt)
    have heq : (fun z => K (𝔥 z, Φ z)) = Ex := funext hKΦ
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.unique hEx.hasFDerivAt
  rw [injective_iff_map_eq_zero]
  intro d hd
  set dF := K' (0, d)
  obtain ⟨z, hz⟩ := hExsurj dF
  have h1 : E' (d, dF) = 0 := by
    have := hEP d hd
    rw [hT] at this
    simpa using this
  have h2 : E' (Φ' z, dF) = 0 := by
    have := congrArg (fun L : X →L[𝕜] Y => L z) hD1
    simpa [hz] using this
  have h3 : d = Φ' z := by
    rw [← sub_eq_zero]
    apply (injective_iff_map_eq_zero _).1 hEinj
    rw [hEy]
    have : ((d, dF) - (Φ' z, dF) : Y × X) = (d - Φ' z, 0) := by simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    rw [← this, map_sub, h1, h2, sub_zero]
  have h4 : K' (𝔥' z, 0) = 0 := by
    have h5 := congrArg (fun L : X →L[𝕜] X => L z) hD2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply] at h5
    have : ((𝔥' z, Φ' z) - (0, d) : X × Y) = (𝔥' z, 0) := by simp [h3]
    rw [← this, map_sub, h5, hz, sub_self]
  have h6 : 𝔥' z = 0 := by
    apply (injective_iff_map_eq_zero _).1 hKinj
    rw [hKh]
    simpa using h4
  have h7 : z = 0 := (injective_iff_map_eq_zero _).1 h𝔥inj z h6
  rw [h3, h7, map_zero]

end Elimination

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  {G : Multigraph V E} {a : E → ℝ}

section Analytic

/-- The positive branch z⁺_α(u) is C^ω in the vertex coordinates. -/
theorem contDiff_omega_zP (ha : ∀ e, 0 < a e) (α : Dart E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun u : V → ℝ => G.zP a u α) := by
  have h1 : ContDiff ℝ n (fun u : V → ℝ => (u (G.head α), u (G.tail α))) :=
    (contDiff_apply ℝ (fun _ : V => ℝ) (G.head α)).prodMk
      (contDiff_apply ℝ (fun _ : V => ℝ) (G.tail α))
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2) :=
    contDiff_omega_zPlus (ha α.1)
  have hfun : (fun u : V → ℝ => G.zP a u α) =
      (fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2) ∘
        (fun u : V → ℝ => (u (G.head α), u (G.tail α))) := rfl
  rw [hfun]
  exact h2.comp h1

/-- The vertex map 𝔥_S is C^ω on ℝ^V. -/
theorem contDiff_omega_sectorField (ha : ∀ e, 0 < a e) (S : Finset E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (G.sectorField a S) := by
  refine contDiff_pi.2 fun i => ?_
  exact (contDiff_const.mul (contDiff_apply ℝ (fun _ : V => ℝ) i)).sub
    (ContDiff.sum fun α _ => contDiff_const.mul (contDiff_omega_zP ha α))

/-- The sector-message map u ↦ y is C^ω on ℝ^V. -/
theorem contDiff_omega_sectorMsg (ha : ∀ e, 0 < a e) (S : Finset E) {n : WithTop ℕ∞} :
    ContDiff ℝ n (G.sectorMsg a S) := by
  refine contDiff_pi.2 fun α => ?_
  have hexp : (fun u : V → ℝ => G.sectorMsg a S u α) =
      fun u => sgnS S α * Real.exp (2 *
        (if α.1 ∈ S then u (G.head α) - G.zP a u α else G.zP a u α)) :=
    funext fun u => sectorMsg_eq_exp (G := G) (S := S) (u := u) ha α
  rw [hexp]
  apply ContDiff.mul contDiff_const
  apply ContDiff.exp
  apply ContDiff.mul contDiff_const
  split_ifs
  · exact (contDiff_apply ℝ (fun _ : V => ℝ) (G.head α)).sub (contDiff_omega_zP ha α)
  · exact contDiff_omega_zP ha α

/-- **The vertex map 𝔥_S is real analytic on ℝ^V.** -/
theorem analyticOnNhd_sectorField (ha : ∀ e, 0 < a e) (S : Finset E) :
    AnalyticOnNhd ℝ (G.sectorField a S) univ :=
  (contDiff_omega_sectorField ha S (n := ω)).analyticOnNhd

/-- **The sector-message map u ↦ y is real analytic on ℝ^V.** -/
theorem analyticOnNhd_sectorMsg (ha : ∀ e, 0 < a e) (S : Finset E) :
    AnalyticOnNhd ℝ (G.sectorMsg a S) univ :=
  (contDiff_omega_sectorMsg ha S (n := ω)).analyticOnNhd

variable (G)

/-- Vertex coordinates of a message vector: u_i=½log F_i, with F_i=b_i∏_{α→i}y_α. -/
noncomputable def vertexCoord (b : V → ℝ) (y : Dart E → ℝ) : V → ℝ :=
  fun i => Real.log (G.totalField b y i) / 2

/-- Message vectors with all total fields positive. -/
def posFieldSet (b : V → ℝ) : Set (Dart E → ℝ) := {y | ∀ i, 0 < G.totalField b y i}

variable {G}

/-- The set of message vectors with positive total fields is open. -/
theorem isOpen_posFieldSet (b : V → ℝ) : IsOpen (G.posFieldSet b) := by
  have : G.posFieldSet b = ⋂ i, (fun y : Dart E → ℝ => G.totalField b y i) ⁻¹' Ioi 0 := by
    ext y; simp [posFieldSet]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_Ioi.preimage (by unfold totalField; fun_prop)

/-- Every admissible real solution (a,b>0) lies in `posFieldSet b`. -/
theorem mem_posFieldSet_of_isAdmissibleSolution (ha : ∀ e, 0 < a e) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) {y : Dart E → ℝ} (hy : G.IsAdmissibleSolution a b y) :
    y ∈ G.posFieldSet b :=
  fun i => totalField_pos ha hb hy i

/-- The vertex coordinates are C^n for every n ≤ ω near every message vector with positive
total fields. -/
theorem contDiffAt_vertexCoord {b : V → ℝ} {y : Dart E → ℝ} (hy : y ∈ G.posFieldSet b)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (G.vertexCoord b) y := by
  refine contDiffAt_pi.2 fun i => ?_
  have hT : ContDiff ℝ n (fun y : Dart E → ℝ => G.totalField b y i) := by
    unfold totalField; fun_prop
  exact (hT.contDiffAt.log (hy i).ne').div_const 2

/-- **The inverse coordinates y ↦ ½log F(y) are real analytic** on the open set of message
vectors with positive total fields. -/
theorem analyticOnNhd_vertexCoord (b : V → ℝ) :
    AnalyticOnNhd ℝ (G.vertexCoord b) (G.posFieldSet b) :=
  fun _ hy => (contDiffAt_vertexCoord hy (n := ω)).analyticAt

/-- The point bijection `sectorFieldFiberEquiv` is the restriction of `sectorMsg`. -/
theorem sectorFieldFiberEquiv_apply_coe (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S) (u : {u : V → ℝ // G.sectorField a S u = fun i => Real.log (b i) / 2}) :
    (sectorFieldFiberEquiv hG ha ha1 hb hS u : Dart E → ℝ) = G.sectorMsg a S u :=
  rfl

/-- The inverse of `sectorFieldFiberEquiv` is the restriction of `vertexCoord`. -/
theorem sectorFieldFiberEquiv_symm_apply_coe (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S)
    (y : {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = S}) :
    ((sectorFieldFiberEquiv hG ha ha1 hb hS).symm y : V → ℝ) = G.vertexCoord b y :=
  rfl

end Analytic

section Nondegeneracy

variable (G) in
/-- Edge equations (E1) with prescribed vertex fields F, one for every dart α:
y_α(F_{t(α)}+a y_ᾱ)−(aF_{t(α)}+y_ᾱ). -/
def edgeResidual (a : E → ℝ) (p : (Dart E → ℝ) × (V → ℝ)) : Dart E → ℝ :=
  fun α => p.1 α * (p.2 (G.tail α) + a α.1 * p.1 (rev α)) - (a α.1 * p.2 (G.tail α) + p.1 (rev α))

variable (G) in
/-- Total fields for the external fields b_i=e^{2h_i}. -/
noncomputable def expTotalField (p : (V → ℝ) × (Dart E → ℝ)) : V → ℝ :=
  G.totalField (fun i => Real.exp (2 * p.1 i)) p.2

/-- Sector messages satisfy the edge equations at the fields F_i=e^{2u_i}, for every u. -/
theorem edgeResidual_sectorMsg (ha : ∀ e, 0 < a e) (S : Finset E) (u : V → ℝ) :
    G.edgeResidual a (G.sectorMsg a S u, fun i => Real.exp (2 * u i)) = 0 := by
  funext α
  have hFh := Real.exp_pos (2 * u (G.head α))
  have hFt := Real.exp_pos (2 * u (G.tail α))
  simp only [edgeResidual, Pi.zero_apply]
  rw [sub_eq_zero]
  simp only [sectorMsg, rev_fst, head_rev, tail_rev]
  split_ifs with h
  · exact (negMsg_edge (ha α.1) hFh hFt).1
  · exact (posMsg_edge (ha α.1) hFh hFt).1

/-- Consistency of total fields: with external field e^{2𝔥_S(u)}, the sector messages have
total fields e^{2u}, for every u. -/
theorem expTotalField_sectorField (hG : G.Loopless) (ha : ∀ e, 0 < a e) {S : Finset E}
    (hS : G.IsEvenSet S) (u : V → ℝ) :
    G.expTotalField (G.sectorField a S u, G.sectorMsg a S u) = fun i => Real.exp (2 * u i) := by
  funext i
  exact (totalField_sectorMsg_iff ha hG hS (fun i => Real.exp_pos _) i).2 (by simp)

/-- The edge equations at the actual total fields are the BP equations times y_ᾱ. -/
theorem edgeResidual_totalField (b : V → ℝ) (y : Dart E → ℝ) :
    G.edgeResidual a (y, G.totalField b y) = fun α => y (rev α) * G.bpPoly a b y α := by
  funext α
  simp only [edgeResidual, bpPoly]
  rw [totalField_tail_eq]
  ring

/-- Derivative of the edge equations in the messages, at fixed fields. -/
theorem hasFDerivAt_edgeResidual_msg (F : V → ℝ) (y₀ : Dart E → ℝ) :
    HasFDerivAt (fun y => G.edgeResidual a (y, F))
      (ContinuousLinearMap.pi fun α =>
        (F (G.tail α) + a α.1 * y₀ (rev α)) • (ContinuousLinearMap.proj α : (Dart E → ℝ) →L[ℝ] ℝ) +
          (a α.1 * y₀ α - 1) • (ContinuousLinearMap.proj (rev α) : (Dart E → ℝ) →L[ℝ] ℝ)) y₀ := by
  rw [hasFDerivAt_pi']
  intro α
  have h := ((hasFDerivAt_apply (𝕜 := ℝ) α y₀).mul
    (((hasFDerivAt_apply (𝕜 := ℝ) (rev α) y₀).const_mul (a α.1)).const_add
      (F (G.tail α)))).sub ((hasFDerivAt_apply (𝕜 := ℝ) (rev α) y₀).const_add
        (a α.1 * F (G.tail α)))
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

/-- The 2×2 edge Jacobian at a sector message is invertible. -/
theorem det_edgeJacobian_sectorMsg_ne_zero (ha : ∀ e, 0 < a e) (S : Finset E) (u : V → ℝ)
    (α : Dart E) :
    (edgeJacobian (a α.1) (Real.exp (2 * u (G.head α))) (Real.exp (2 * u (G.tail α)))
      (G.sectorMsg a S u α) (G.sectorMsg a S u (rev α))).det ≠ 0 := by
  have hFh := Real.exp_pos (2 * u (G.head α))
  have hFt := Real.exp_pos (2 * u (G.tail α))
  simp only [sectorMsg, rev_fst, head_rev, tail_rev]
  split_ifs with h
  · exact det_edgeJacobian_negBranch_ne_zero (ha α.1) hFh hFt
  · exact det_edgeJacobian_posBranch_ne_zero (ha α.1) hFh hFt

/-- **Invertible edge Jacobians.** At sector messages, the derivative of the edge equations in
the messages (fields F=e^{2u} fixed) is injective. -/
theorem fderiv_edgeResidual_sectorMsg_injective (ha : ∀ e, 0 < a e) (S : Finset E)
    (u : V → ℝ) :
    Function.Injective (fderiv ℝ (fun y => G.edgeResidual a (y, fun i => Real.exp (2 * u i)))
      (G.sectorMsg a S u)) := by
  rw [(hasFDerivAt_edgeResidual_msg _ _).fderiv, injective_iff_map_eq_zero]
  intro d hd
  funext α
  have e1 : (Real.exp (2 * u (G.tail α)) + a α.1 * G.sectorMsg a S u (rev α)) * d α +
      (a α.1 * G.sectorMsg a S u α - 1) * d (rev α) = 0 := congrFun hd α
  have e2 : (Real.exp (2 * u (G.tail (rev α))) + a (rev α).1 * G.sectorMsg a S u (rev (rev α))) *
      d (rev α) + (a (rev α).1 * G.sectorMsg a S u (rev α) - 1) * d (rev (rev α)) = 0 :=
    congrFun hd (rev α)
  simp only [rev_rev, rev_fst, tail_rev] at e2
  exact (edge_linear_eq_zero (det_edgeJacobian_sectorMsg_ne_zero ha S u α) e1
    (by linarith)).1

/-- The derivative of u ↦ e^{2u} is surjective. -/
theorem fderiv_expTwo_surjective (u : V → ℝ) :
    Function.Surjective (fderiv ℝ (fun u : V → ℝ => fun i => Real.exp (2 * u i)) u) := by
  have hd : HasFDerivAt (fun u : V → ℝ => fun i => Real.exp (2 * u i))
      (ContinuousLinearMap.pi fun i =>
        (Real.exp (2 * u i) * 2) • (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ)) u := by
    rw [hasFDerivAt_pi']
    intro i
    have h := ((hasFDerivAt_apply (𝕜 := ℝ) i u).const_mul 2).exp
    refine h.congr_fderiv ?_
    ext v
    simp
    ring
  rw [hd.fderiv]
  intro w
  refine ⟨fun i => w i / (Real.exp (2 * u i) * 2), ?_⟩
  funext i
  change Real.exp (2 * u i) * 2 * (w i / (Real.exp (2 * u i) * 2)) = w i
  field_simp

/-- At message vectors with nonzero vertex products, the derivative of the total fields in the
external field h (b=e^{2h}) is injective. -/
theorem fderiv_expTotalField_field_injective (h₀ : V → ℝ) {y₀ : Dart E → ℝ}
    (hy₀ : ∀ i, ∏ α ∈ G.inDarts i, y₀ α ≠ 0) :
    Function.Injective (fderiv ℝ (fun h => G.expTotalField (h, y₀)) h₀) := by
  have hd : HasFDerivAt (fun h => G.expTotalField (h, y₀))
      (ContinuousLinearMap.pi fun i =>
        (Real.exp (2 * h₀ i) * 2 * ∏ α ∈ G.inDarts i, y₀ α) •
          (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ)) h₀ := by
    rw [hasFDerivAt_pi']
    intro i
    have h := (((hasFDerivAt_apply (𝕜 := ℝ) i h₀).const_mul 2).exp).mul_const
      (∏ α ∈ G.inDarts i, y₀ α)
    refine h.congr_fderiv ?_
    ext v
    simp
    ring
  rw [hd.fderiv, injective_iff_map_eq_zero]
  intro w hw
  funext i
  have hi : Real.exp (2 * h₀ i) * 2 * (∏ α ∈ G.inDarts i, y₀ α) * w i = 0 := congrFun hw i
  have hc : Real.exp (2 * h₀ i) * 2 * ∏ α ∈ G.inDarts i, y₀ α ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Real.exp_ne_zero _) two_ne_zero) (hy₀ i)
  exact (mul_eq_zero.1 hi).resolve_left hc

/-- A message vector with injective derivative of the BP polynomials is a simple solution. -/
theorem isSimpleSolution_of_fderiv_bpPoly_injective {b : V → ℝ} {y : Dart E → ℝ}
    (hinj : Function.Injective (fderiv ℝ (fun z => G.bpPoly a b z) y)) :
    G.IsSimpleSolution a b y := by
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
  rw [hd.fderiv] at hinj
  have hmv : Function.Injective (G.jacobian a b y).mulVec := by
    intro v w hvw
    apply hinj
    rw [hL, hL]
    exact hvw
  have hunit := Matrix.mulVec_injective_iff_isUnit.1 hmv
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero

/-- **Vertex nondegeneracy implies BP nondegeneracy.** If 𝔥_S(u)=½log b and the derivative of
𝔥_S at u is injective, then the derivative of the BP polynomials at the sector messages is
injective. Only a_e>0 is needed. -/
theorem fderiv_bpPoly_injective_sectorMsg (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2)
    (hinj : Function.Injective (fderiv ℝ (G.sectorField a S) u)) :
    Function.Injective (fderiv ℝ (fun y => G.bpPoly a b y) (G.sectorMsg a S u)) := by
  have hbu : (fun i => Real.exp (2 * G.sectorField a S u i)) = b := by
    funext i
    rw [hu i, mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hb i)]
  have hy0 : ∀ α, G.sectorMsg a S u α ≠ 0 := sectorMsg_ne_zero ha
  have hKΦ : ∀ z, G.expTotalField (G.sectorField a S z, G.sectorMsg a S z) =
      fun i => Real.exp (2 * z i) := expTotalField_sectorField hG ha hS
  have hEΦ : ∀ z, G.edgeResidual a (G.sectorMsg a S z, fun i => Real.exp (2 * z i)) = 0 :=
    edgeResidual_sectorMsg ha S
  have hKu : ∀ y, G.expTotalField (G.sectorField a S u, y) = G.totalField b y := by
    intro y
    change G.totalField (fun i => Real.exp (2 * G.sectorField a S u i)) y = _
    rw [hbu]
  -- The sector messages solve BP at b.
  have hP0 : G.bpPoly a b (G.sectorMsg a S u) = 0 := by
    funext α
    have h1 := congrFun (edgeResidual_totalField (G := G) (a := a) b (G.sectorMsg a S u)) α
    rw [← hKu, hKΦ u, hEΦ u] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (hy0 (rev α))
  have hPd : Differentiable ℝ (fun y => G.bpPoly a b y) := by
    intro y
    apply differentiableAt_pi.2
    intro α
    unfold bpPoly cavity
    fun_prop
  have hEP : ∀ v, fderiv ℝ (fun y => G.bpPoly a b y) (G.sectorMsg a S u) v = 0 →
      fderiv ℝ (fun y => G.edgeResidual a (y, G.expTotalField (G.sectorField a S u, y)))
        (G.sectorMsg a S u) v = 0 := by
    intro v hv
    let M : (Dart E → ℝ) →L[ℝ] (Dart E → ℝ) :=
      ContinuousLinearMap.pi fun α => (ContinuousLinearMap.proj (rev α) : (Dart E → ℝ) →L[ℝ] ℝ)
    have hfun : (fun y => G.edgeResidual a (y, G.expTotalField (G.sectorField a S u, y))) =
        ⇑M * fun y => G.bpPoly a b y := by
      funext y
      rw [hKu]
      exact edgeResidual_totalField b y
    have hd := M.hasFDerivAt.mul' (hPd (G.sectorMsg a S u)).hasFDerivAt
    rw [hfun, hd.fderiv]
    simp [hv, hP0]
  have hΦd : DifferentiableAt ℝ (G.sectorMsg a S) u :=
    (contDiff_omega_sectorMsg ha S (n := 1)).differentiable one_ne_zero u
  have h𝔥d : DifferentiableAt ℝ (G.sectorField a S) u :=
    (contDiff_omega_sectorField ha S (n := 1)).differentiable one_ne_zero u
  have hExd : DifferentiableAt ℝ (fun u : V → ℝ => fun i => Real.exp (2 * u i)) u := by
    fun_prop
  have hEd : DifferentiableAt ℝ (G.edgeResidual a)
      (G.sectorMsg a S u, fun i => Real.exp (2 * u i)) := by
    apply differentiableAt_pi.2
    intro α
    unfold edgeResidual
    fun_prop
  have hKd : DifferentiableAt ℝ G.expTotalField (G.sectorField a S u, G.sectorMsg a S u) := by
    apply differentiableAt_pi.2
    intro i
    unfold expTotalField totalField
    fun_prop
  have hprod : ∀ i, ∏ α ∈ G.inDarts i, G.sectorMsg a S u α ≠ 0 :=
    fun i => Finset.prod_ne_zero_iff.2 fun α _ => hy0 α
  exact fderiv_injective_of_edge_elimination hΦd hExd h𝔥d hEd hKd hEΦ hKΦ hEP
    (fderiv_edgeResidual_sectorMsg_injective ha S u) (fderiv_expTwo_surjective u)
    (fderiv_expTotalField_field_injective (G.sectorField a S u) hprod) hinj

/-- **Vertex nondegeneracy implies BP nondegeneracy** (determinant form). -/
theorem isSimpleSolution_sectorMsg_of_fderiv_injective (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2)
    (hinj : Function.Injective (fderiv ℝ (G.sectorField a S) u)) :
    G.IsSimpleSolution a b (G.sectorMsg a S u) :=
  isSimpleSolution_of_fderiv_bpPoly_injective
    (fderiv_bpPoly_injective_sectorMsg hG ha hb hS hu hinj)

/-- **`real:vertex-map` (nondegeneracy is preserved).** On the vertex fiber 𝔥_S(u)=½log b, the
BP solution `sectorMsg a S u` is nondegenerate iff the derivative of 𝔥_S at u is injective. -/
theorem isSimpleSolution_sectorMsg_iff (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2) :
    G.IsSimpleSolution a b (G.sectorMsg a S u) ↔
      Function.Injective (fderiv ℝ (G.sectorField a S) u) :=
  ⟨fderiv_sectorField_injective_of_isSimpleSolution hG ha ha1 hb hS hu,
    isSimpleSolution_sectorMsg_of_fderiv_injective hG ha hb hS hu⟩

/-- Determinant form of `isSimpleSolution_sectorMsg_iff`: the BP Jacobian determinant is
nonzero iff the vertex Jacobian determinant is nonzero. -/
theorem isSimpleSolution_sectorMsg_iff_det (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    {u : V → ℝ} (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2) :
    G.IsSimpleSolution a b (G.sectorMsg a S u) ↔
      (fderiv ℝ (G.sectorField a S) u).toLinearMap.det ≠ 0 := by
  rw [isSimpleSolution_sectorMsg_iff hG ha ha1 hb hS hu]
  set L := (fderiv ℝ (G.sectorField a S) u).toLinearMap
  change Function.Injective L ↔ _
  constructor
  · intro hinj
    exact (LinearEquiv.isUnit_det' (LinearEquiv.ofInjectiveEndo L hinj)).ne_zero
  · intro hdet
    have hu' : IsUnit L := (LinearMap.isUnit_iff_isUnit_det L).2 (isUnit_iff_ne_zero.2 hdet)
    exact (Module.End.isUnit_iff L).1 hu' |>.1

/-- **Nondegeneracy at an arbitrary admissible real solution.** For an admissible real solution
y with negative-edge set S, y is nondegenerate iff the derivative of 𝔥_S at its vertex
coordinates ½log F(y) is injective. -/
theorem isSimpleSolution_iff_fderiv_sectorField_injective (hG : G.Loopless)
    (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i)
    {y : Dart E → ℝ} (hy : G.IsAdmissibleSolution a b y) :
    G.IsSimpleSolution a b y ↔
      Function.Injective (fderiv ℝ (G.sectorField a (negSupport y)) (G.vertexCoord b y)) := by
  obtain ⟨hyeq, hu⟩ := eq_sectorMsg ha ha1 hG hb hy
  have hS := isEvenSet_negSupport hG ha hb hy
  have h := isSimpleSolution_sectorMsg_iff hG ha ha1 hb hS hu
  rw [← hyeq] at h
  exact h

end Nondegeneracy

/-- **`real:vertex-map` (local real-analytic form).** Fix a_e>0, a_e≠1, b_i>0, an Eulerian set
S, and h_i=½log b_i. Then:
* u ↦ `sectorMsg a S u` is real analytic on ℝ^V, and so is 𝔥_S;
* y ↦ `vertexCoord b y`=½log F(y) is real analytic on the open set `posFieldSet b`, which
  contains every admissible real solution;
* these maps send the fiber 𝔥_S⁻¹(h) into the admissible real solutions with negative-edge set
  S and back, and are mutually inverse there;
* at every point of the fiber, BP nondegeneracy is equivalent to injectivity of the derivative
  of 𝔥_S. -/
theorem sectorVertexMap_analytic (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S) :
    AnalyticOnNhd ℝ (G.sectorMsg a S) univ ∧
      AnalyticOnNhd ℝ (G.sectorField a S) univ ∧
      IsOpen (G.posFieldSet b) ∧
      AnalyticOnNhd ℝ (G.vertexCoord b) (G.posFieldSet b) ∧
      (∀ u, G.sectorField a S u = (fun i => Real.log (b i) / 2) →
        G.IsAdmissibleSolution a b (G.sectorMsg a S u) ∧
          negSupport (G.sectorMsg a S u) = S ∧
          G.sectorMsg a S u ∈ G.posFieldSet b ∧
          G.vertexCoord b (G.sectorMsg a S u) = u ∧
          (G.IsSimpleSolution a b (G.sectorMsg a S u) ↔
            Function.Injective (fderiv ℝ (G.sectorField a S) u))) ∧
      (∀ y, G.IsAdmissibleSolution a b y → negSupport y = S →
        y ∈ G.posFieldSet b ∧
          G.sectorField a S (G.vertexCoord b y) = (fun i => Real.log (b i) / 2) ∧
          G.sectorMsg a S (G.vertexCoord b y) = y) := by
  refine ⟨analyticOnNhd_sectorMsg ha S, analyticOnNhd_sectorField ha S,
    isOpen_posFieldSet b, analyticOnNhd_vertexCoord b, ?_, ?_⟩
  · intro u hu
    have hadm := isAdmissibleSolution_sectorMsg ha ha1 hG hS hb (congrFun hu)
    refine ⟨hadm, negSupport_sectorMsg ha ha1, mem_posFieldSet_of_isAdmissibleSolution ha hb hadm,
      ?_, isSimpleSolution_sectorMsg_iff hG ha ha1 hb hS (congrFun hu)⟩
    exact congrArg Subtype.val ((sectorFieldFiberEquiv hG ha ha1 hb hS).left_inv ⟨u, hu⟩)
  · intro y hy hyS
    refine ⟨mem_posFieldSet_of_isAdmissibleSolution ha hb hy, ?_, ?_⟩
    · exact ((sectorFieldFiberEquiv hG ha ha1 hb hS).symm ⟨y, hy, hyS⟩).2
    · exact congrArg Subtype.val ((sectorFieldFiberEquiv hG ha ha1 hb hS).right_inv ⟨y, hy, hyS⟩)

end Multigraph

end BPFixedPoints
