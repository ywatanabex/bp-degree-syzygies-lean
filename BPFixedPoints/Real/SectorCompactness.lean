import BPFixedPoints.Real.SectorBox
import BPFixedPoints.Degree.Jacobian
import BPFixedPoints.Degree.PolynomialDerivative

/-!
# Compact real sectors and finiteness of nondegenerate fibers

The box bound makes the admissible BP solution set of a fixed Eulerian sector
compact. A nonzero BP Jacobian determinant makes a root isolated by the inverse
function theorem; if all roots in the sector are nondegenerate, there are
finitely many. No degree theory or vertex-Jacobian comparison is needed.
-/

namespace BPFixedPoints

open Filter Topology Set

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  {G : Multigraph V E} {a : E → ℝ}

theorem contDiff_zP (ha : ∀ e, 0 < a e) (α : Dart E) {n : ℕ∞} :
    ContDiff ℝ n (fun u : V → ℝ => G.zP a u α) := by
  have h1 : ContDiff ℝ n (fun u : V → ℝ => (u (G.head α), u (G.tail α))) :=
    (contDiff_apply ℝ (fun _ : V => ℝ) (G.head α)).prodMk
      (contDiff_apply ℝ (fun _ : V => ℝ) (G.tail α))
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2) :=
    contDiff_zPlus (n := n) (ha α.1)
  have hfun : (fun u : V → ℝ => G.zP a u α) =
      (fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2) ∘
        (fun u : V → ℝ => (u (G.head α), u (G.tail α))) := rfl
  rw [hfun]
  exact h2.comp h1

theorem contDiff_sectorField (ha : ∀ e, 0 < a e) (S : Finset E) {n : ℕ∞} :
    ContDiff ℝ n (G.sectorField a S) := by
  refine contDiff_pi.2 fun i => ?_
  exact (contDiff_const.mul (contDiff_apply ℝ (fun _ : V => ℝ) i)).sub
    (ContDiff.sum fun α _ => contDiff_const.mul (contDiff_zP ha α))

theorem contDiff_sectorMsg (ha : ∀ e, 0 < a e) (S : Finset E) {n : ℕ∞} :
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
  · exact (contDiff_apply ℝ (fun _ : V => ℝ) (G.head α)).sub (contDiff_zP ha α)
  · exact contDiff_zP ha α

/-- Each Eulerian fiber of the vertex map is compact. -/
theorem isCompact_sectorField_fiber (ha : ∀ e, 0 < a e) {S : Finset E}
    (hS : G.IsEvenSet S) (h : V → ℝ) :
    IsCompact {u : V → ℝ | G.sectorField a S u = h} := by
  let C : V → ℝ := fun i => |h i| + ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2
  have hclosed : IsClosed {u : V → ℝ | G.sectorField a S u = h} :=
    isClosed_eq (contDiff_sectorField (n := 1) ha S).continuous continuous_const
  refine (isCompact_Icc : IsCompact (Icc (-C) C)).of_isClosed_subset hclosed ?_
  intro u hu
  have hu' : ∀ i, G.sectorField a S u i = h i := congrFun hu
  have hbound : ∀ i, |u i| ≤ C i := fun i => abs_le_of_sectorField_eq ha hS hu' i
  exact ⟨fun i => (abs_le.1 (hbound i)).1, fun i => (abs_le.1 (hbound i)).2⟩

/-- The image of the vertex-coordinate fiber is the admissible BP solution set in that sign sector. -/
theorem sectorMsg_image_fiber (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S) :
    G.sectorMsg a S '' {u : V → ℝ | G.sectorField a S u = fun i => Real.log (b i) / 2} =
      {y : Dart E → ℝ | G.IsAdmissibleSolution a b y ∧ negSupport y = S} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨isAdmissibleSolution_sectorMsg ha ha1 hG hS hb (congrFun hu),
      negSupport_sectorMsg ha ha1⟩
  · rintro ⟨hy, hyS⟩
    obtain ⟨hyEq, hu⟩ := eq_sectorMsg ha ha1 hG hb hy
    rw [hyS] at hyEq hu
    exact ⟨fun i => Real.log (G.totalField b y i) / 2, funext hu, hyEq.symm⟩

/-- The admissible BP solution set of a fixed Eulerian sector is compact. -/
theorem isCompact_sector_solutions (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S) :
    IsCompact {y : Dart E → ℝ | G.IsAdmissibleSolution a b y ∧ negSupport y = S} := by
  rw [← sectorMsg_image_fiber hG ha ha1 hb hS]
  exact (isCompact_sectorField_fiber ha hS _).image
    (contDiff_sectorMsg (n := 1) ha S).continuous

/-- A nondegenerate zero of the BP polynomials is isolated among all fixed points. -/
theorem exists_isolating_open_of_isSimpleSolution {b : V → ℝ} {y : Dart E → ℝ}
    (hy : G.IsFixedPoint a b y) (hnd : G.IsSimpleSolution a b y) :
    ∃ U : Set (Dart E → ℝ), IsOpen U ∧ y ∈ U ∧
      ∀ z ∈ U, G.IsFixedPoint a b z → z = y := by
  classical
  let F : (Dart E → ℝ) → (Dart E → ℝ) := fun z α =>
    MvPolynomial.eval z (G.bpMvPoly a b α)
  let L : (Dart E → ℝ) →L[ℝ] (Dart E → ℝ) :=
    ContinuousLinearMap.pi fun α => (G.bpMvPoly a b α).gradCLM y
  have hL : ∀ w, L w = (G.jacobian a b y).mulVec w := by
    intro w
    funext α
    exact MvPolynomial.gradCLM_apply _ _ _
  have hd : HasStrictFDerivAt F L y :=
    hasStrictFDerivAt_pi.2 fun α => (G.bpMvPoly a b α).hasStrictFDerivAt_eval y
  have hunit : IsUnit (G.jacobian a b y) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hnd)
  have hinj : Function.Injective L.toLinearMap := by
    intro w w' hww
    apply (Matrix.mulVec_injective_iff_isUnit.2 hunit)
    rw [← hL, ← hL]
    exact hww
  let e := (LinearEquiv.ofInjectiveEndo L.toLinearMap hinj).toContinuousLinearEquiv
  have he : (e : (Dart E → ℝ) →L[ℝ] (Dart E → ℝ)) = L := by
    ext w
    simp [e, LinearEquiv.coe_ofInjectiveEndo]
  rw [← he] at hd
  let f := hd.toOpenPartialHomeomorph F
  have hyf : y ∈ f.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨f.source, f.open_source, hyf, fun z hz hzf => ?_⟩
  apply f.injOn hz hyf
  change F z = F y
  funext α
  exact ((G.isFixedPoint_iff_eval a b z).1 hzf α).trans
    ((G.isFixedPoint_iff_eval a b y).1 hy α).symm

/-- If all admissible real solutions in a sector are nondegenerate, the set is finite. -/
theorem finite_sector_solutions_of_nondegenerate (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S)
    (hnd : ∀ y, G.IsAdmissibleSolution a b y → negSupport y = S →
      G.IsSimpleSolution a b y) :
    {y : Dart E → ℝ | G.IsAdmissibleSolution a b y ∧ negSupport y = S}.Finite := by
  classical
  let T := {y : Dart E → ℝ | G.IsAdmissibleSolution a b y ∧ negSupport y = S}
  have hc : IsCompact T := isCompact_sector_solutions hG ha ha1 hb hS
  have hloc : ∀ y : T, ∃ U : Set (Dart E → ℝ), IsOpen U ∧ y.1 ∈ U ∧
      ∀ z ∈ U, G.IsFixedPoint a b z → z = y.1 := fun y =>
    exists_isolating_open_of_isSimpleSolution y.2.1.1 (hnd y.1 y.2.1 y.2.2)
  choose U hU hyU huniq using hloc
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hU
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩)
  refine (t.finite_toSet.image (Subtype.val : T → Dart E → ℝ)).subset ?_
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (ht hy)
  exact ⟨z, hz, (huniq z y hyz hy.1.1).symm⟩

end Multigraph

end BPFixedPoints
