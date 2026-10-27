import BPFixedPoints.Family.NonnormalizableLocusDominant
import Mathlib.Analysis.Calculus.Implicit

/-!
# Local structure of a regular chart fiber over ℂ

Over ℂ the chart equations form a smooth map Φ(a,·) : ℂ^E → ℂ^V near every chart point
(`contDiffAt_chartFieldMap`), and its Fréchet derivative is the Jacobian matrix `chartJac`
(`hasStrictFDerivAt_chartFieldMap`). At a regular point x (Jacobian of rank |V|) the implicit
function theorem therefore gives an open partial homeomorphism Ψ from a neighbourhood of x in
ℂ^E onto an open subset of ℂ^V × W, where W = ker J(x) has dimension |E| − |V|, and the first
component of Ψ is Φ(a,·) (`exists_openPartialHomeomorph_chartFiber`). Consequently Ψ identifies
the fiber {x' : Φ(a,x') = Φ(a,x)} near x with an open subset of {Φ(a,x)} × W, i.e. near each
regular point the fiber is a complex submanifold of dimension |E| − |V|; for connected G this is
ν(G) − 1 (`finrank_ker_chartJac_eq_nu_sub_one`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP Filter Topology

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Kernel

variable {K : Type*} [Field K]

/-- At a regular point the Jacobian kernel (tangent space of the fiber) has dimension
|E| − |V|. -/
theorem finrank_ker_chartJac {a x : E → K} (hreg : G.IsRegularChartPoint a x) :
    Module.finrank K (LinearMap.ker (G.chartJac a x).mulVecLin) =
      Fintype.card E - Fintype.card V := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.chartJac a x).mulVecLin
  have hr : LinearMap.range (G.chartJac a x).mulVecLin = ⊤ := LinearMap.range_eq_top.mpr hreg
  rw [hr, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- For connected G, ν(G) − 1 = |E| − |V| when ν(G) ≥ 1. -/
theorem nu_sub_one_eq_of_connected (hc : G.Connected) :
    G.nu - 1 = Fintype.card E - Fintype.card V := by
  have h1 := G.numComponents_eq_one_of_connected hc
  unfold nu
  omega

/-- For connected G, the Jacobian kernel at a regular point has dimension ν(G) − 1. -/
theorem finrank_ker_chartJac_eq_nu_sub_one (hc : G.Connected) {a x : E → K}
    (hreg : G.IsRegularChartPoint a x) :
    Module.finrank K (LinearMap.ker (G.chartJac a x).mulVecLin) = G.nu - 1 := by
  rw [G.finrank_ker_chartJac hreg, G.nu_sub_one_eq_of_connected hc]

/-- For connected G, ν(G) ≥ 1 exactly when |V| ≤ |E|. -/
theorem one_le_nu_iff_of_connected (hc : G.Connected) :
    1 ≤ G.nu ↔ Fintype.card V ≤ Fintype.card E := by
  have h1 := G.numComponents_eq_one_of_connected hc
  unfold nu
  omega

end Kernel

section Complex

/-- The chart equations as a map ℂ^E → ℂ^V, x ↦ (Φ_i(a,x))_i. -/
noncomputable def chartFieldMap (a : E → ℂ) (x : E → ℂ) : V → ℂ := fun i => G.chartField a x i

theorem contDiffAt_chartFieldMap {a x : E → ℂ} (hx : IsChartPoint a x) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (G.chartFieldMap a) x := by
  apply contDiffAt_pi'
  intro i
  show ContDiffAt ℂ n (fun x => ∏ e, (if G.fst e = i then x e else 1) *
    (if G.snd e = i then edgeInvolution (a e) (x e) else 1)) x
  have happ : ∀ e, ContDiffAt ℂ n (fun x : E → ℂ => x e) x := fun e =>
    (contDiff_apply (𝕜 := ℂ) (F' := fun _ : E => ℂ) e).contDiffAt
  refine contDiffAt_prod (fun e _ => ?_)
  refine ContDiffAt.mul ?_ ?_
  · split_ifs
    · exact happ e
    · exact contDiffAt_const
  · split_ifs
    · unfold edgeInvolution
      exact ContDiffAt.div (contDiffAt_const.sub (happ e))
        (contDiffAt_const.sub (contDiffAt_const.mul (happ e))) (one_sub_mul_ne_zero (hx e).2.2)
    · exact contDiffAt_const

theorem add_smul_single_eq_update (x : E → ℂ) (e : E) (s : ℂ) :
    x + s • Pi.single e 1 = Function.update x e (x e + s) := by
  funext e'
  by_cases h : e' = e
  · subst h
    simp
  · simp [h]

/-- **The derivative of the chart equations is the Jacobian.** -/
theorem hasStrictFDerivAt_chartFieldMap {a x : E → ℂ} (hx : IsChartPoint a x) :
    HasStrictFDerivAt (G.chartFieldMap a)
      (LinearMap.toContinuousLinearMap (G.chartJac a x).mulVecLin) x := by
  have hS := (G.contDiffAt_chartFieldMap hx 1).hasStrictFDerivAt one_ne_zero
  convert hS using 1
  have hD : HasFDerivAt (G.chartFieldMap a) (fderiv ℂ (G.chartFieldMap a) x) x :=
    hS.hasFDerivAt
  have hcol : ∀ e i, fderiv ℂ (G.chartFieldMap a) x (Pi.single e 1) i = G.chartJac a x i e := by
    intro e i
    have h1 := hasFDerivAt_pi'.mp hD i
    have hγ : HasDerivAt (fun s : ℂ => x + s • Pi.single e (1 : ℂ)) (Pi.single e 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single e (1 : ℂ))).const_add x
    have h1' : HasFDerivAt (fun y => G.chartFieldMap a y i)
        ((ContinuousLinearMap.proj i).comp (fderiv ℂ (G.chartFieldMap a) x))
        (x + (0 : ℂ) • Pi.single e 1) := by
      simpa using h1
    have h2 := h1'.comp_hasDerivAt (0 : ℂ) hγ
    have h3 : HasDerivAt (fun s : ℂ => G.chartFieldMap a (x + s • Pi.single e 1) i)
        (G.chartJac a x i e) 0 := by
      have h4 : (fun s : ℂ => G.chartFieldMap a (x + s • Pi.single e 1) i) =
          fun s => G.chartField a (Function.update x e (x e + s)) i := by
        funext s
        rw [add_smul_single_eq_update]
        rfl
      rw [h4]
      exact HasDerivAt.comp_const_add (x e) 0
        (by rw [add_zero]; exact G.hasDerivAt_chartField_update a x hx i e)
    exact (h2.unique h3)
  refine ContinuousLinearMap.ext fun v => ?_
  conv_lhs => rw [← Finset.univ_sum_single v]
  conv_rhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hsm : Pi.single e (v e) = v e • (Pi.single e (1 : ℂ) : E → ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hsm, map_smul, map_smul]
  congr 1
  funext i
  rw [hcol e i]
  simp

/-- **Local manifold structure of the chart fiber.** At a regular chart point x over ℂ there is
an open partial homeomorphism Ψ from ℂ^E to ℂ^V × W, with W ⊆ ℂ^E a subspace of dimension
|E| − |V|, such that x lies in the source of Ψ, Ψ x = (Φ(a,x), 0), and the first component of Ψ
is Φ(a,·). Thus Ψ maps the fiber {Φ(a,·) = Φ(a,x)} ∩ source bijectively and homeomorphically onto
the open subset ({Φ(a,x)} × W) ∩ target of {Φ(a,x)} × W ≅ W. -/
theorem exists_openPartialHomeomorph_chartFiber {a x : E → ℂ} (hx : IsChartPoint a x)
    (hreg : G.IsRegularChartPoint a x) :
    ∃ (W : Submodule ℂ (E → ℂ)) (Ψ : OpenPartialHomeomorph (E → ℂ) ((V → ℂ) × W)),
      Module.finrank ℂ W = Fintype.card E - Fintype.card V ∧ x ∈ Ψ.source ∧
        Ψ x = (G.chartFieldMap a x, 0) ∧ ∀ x', (Ψ x').1 = G.chartFieldMap a x' := by
  have hS := G.hasStrictFDerivAt_chartFieldMap hx
  have hrange : (LinearMap.toContinuousLinearMap (G.chartJac a x).mulVecLin).range = ⊤ := by
    exact LinearMap.range_eq_top.mpr hreg
  refine ⟨_, hS.implicitToOpenPartialHomeomorph _ _ hrange, ?_,
    hS.mem_implicitToOpenPartialHomeomorph_source hrange,
    hS.implicitToOpenPartialHomeomorph_self hrange,
    fun x' => hS.implicitToOpenPartialHomeomorph_fst hrange x'⟩
  exact G.finrank_ker_chartJac hreg

end Complex

end Multigraph

end BPFixedPoints
