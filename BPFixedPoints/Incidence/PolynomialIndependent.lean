import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Algebraic independence from an invertible derivative

The inverse function theorem puts an open set in the evaluation map's image.
A polynomial vanishing on that set vanishes on a box with infinite coordinate
sets and hence is zero. This applies to evaluation through arbitrary parameter
presentations, including fixing some variables.
-/

namespace BPFixedPoints

open Filter Topology Metric MvPolynomial

theorem algebraicIndependent_of_hasStrictFDerivAt_eval
    {k σ ι : Type*} [NontriviallyNormedField k] [CompleteSpace k] [Fintype ι]
    (p : ι → MvPolynomial σ k) (Φ : (ι → k) → σ → k) {x : ι → k}
    (L : (ι → k) ≃L[k] (ι → k))
    (hd : HasStrictFDerivAt (fun z i => eval (Φ z) (p i)) (L : _ →L[k] _) x) :
    AlgebraicIndependent k p := by
  classical
  let F : (ι → k) → ι → k := fun z i => eval (Φ z) (p i)
  have hrange : Set.range F ∈ 𝓝 (F x) := by
    rw [← hd.map_nhds_eq_of_equiv]
    apply Filter.mem_map.mpr
    exact Filter.Eventually.of_forall fun z => ⟨z, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hrange
  rw [algebraicIndependent_iff_injective_aeval]
  intro P Q hPQ
  apply MvPolynomial.funext_set (fun i => ball (F x i) ε)
    (fun i => infinite_of_mem_nhds (F x i) (ball_mem_nhds _ hε))
  intro y hy
  have hyball : y ∈ ball (F x) ε := by
    rw [ball_pi _ hε]
    exact hy
  obtain ⟨z, rfl⟩ := hball hyball
  have h := congrArg (fun q => aeval (Φ z) q) hPQ
  simpa only [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval] using h

end BPFixedPoints
