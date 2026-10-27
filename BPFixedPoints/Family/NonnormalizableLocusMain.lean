import BPFixedPoints.Family.NonnormalizableLocusNonempty
import BPFixedPoints.Family.NonnormalizableLocusManifold

/-!
# `supp:nonnormalizable-dim`: the generic non-normalizable locus

Let G be connected. For parameters (a,b) the *non-normalizable locus* is the set of message
vectors y with `IsFixedPoint a b y`, nonzero messages, nonzero update denominators and F_i = −1
at every vertex (`IsNonnormalizableSolution`). By the edge chart (`nonnormalizableChartEquiv`),
for a_e² ≠ 1 it is identified, via x_e = y_{(e,false)}, with the chart fiber

  {x ∈ U_a : Φ_i(a,x) = −1/b_i for all i},  U_a = {x : x_e ≠ 0, a_e, 1/a_e},

i.e. with the zero set of |V| equations in the open set U_a ⊆ K^E.

**Formalization of "smooth of pure dimension ν − 1".** At every point x of the locus the
|V| × |E| Jacobian ∂Φ/∂x (`chartJac`, whose entries are the partial derivatives by
`hasDerivAt_chartField_update`) has rank |V| (`IsRegularChartPoint`). By the Jacobian criterion
this means the locus is smooth of pure dimension |E| − |V| = ν(G) − 1. We also record the
dimension of the tangent space ker ∂Φ/∂x, which is ν(G) − 1, and over ℂ the local chart given by
the implicit function theorem: an open partial homeomorphism of ℂ^E onto an open subset of
ℂ^V × W, dim W = ν(G) − 1, whose first component is Φ(a,·), so that near x the locus is
homeomorphic to an open subset of W.

**Formalization of "generic".** Generic means outside the zero set of one nonzero polynomial in
the |E| + |V| parameters (a,b):

* `supp_nonnormalizable_dim_tree`: if G is a tree (ν(G) = 0) there is a nonzero P ∈ ℤ[a,b] such
  that for every field K and all a, b ∈ K with a_e² ≠ 1 and P(a,b) ≠ 0 the locus is empty.
* `supp_nonnormalizable_dim_cyclic`: if ν(G) ≥ 1 there is a nonzero P ∈ ℂ[a,b] such that for all
  complex a, b with P(a,b) ≠ 0 we have a_e² ≠ 1, the locus is nonempty, and at every point of
  the locus the Jacobian has rank |V|, the tangent space has dimension ν(G) − 1, and the
  implicit-function chart above exists.
* `nonnormalizable_regular` (in `NonnormalizableLocusSmooth`) gives the smoothness half over an
  arbitrary field with a nonzero P ∈ ℤ[a,b].

**Not formalized.** Irreducibility or connectedness of the generic locus is not claimed (the
paper does not claim it either). The polynomials are proved to exist; they are not computed.
Nonemptiness is proved over ℂ (it uses the Nullstellensatz, so it needs an algebraically closed
field, and the dominance step uses the complex inverse function theorem); regularity and the
tree case hold over every field. The scheme-theoretic statement (smoothness of the morphism of
schemes) is not formalized; the Jacobian criterion is used as the definition of smoothness.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- **`supp:nonnormalizable-dim`, tree case.** If G is a tree, there is a nonzero P ∈ ℤ[a,b] such
that for every field K and all a, b with a_e² ≠ 1 and P(a,b) ≠ 0 the non-normalizable locus at
(a,b) is empty. -/
theorem supp_nonnormalizable_dim_tree (hc : G.Connected) (hν : G.nu = 0) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (K : Type*) [Field K] (a : E → K) (b : V → K), (∀ e, a e ^ 2 ≠ 1) →
        eval (Sum.elim a b) (map (Int.castRingHom K) P) ≠ 0 →
          ∀ y, ¬ G.IsNonnormalizableSolution a b y :=
  G.nonnormalizable_empty_of_tree hc hν

/-- **`supp:nonnormalizable-dim`, ν(G) ≥ 1.** If G is connected with ν(G) ≥ 1, there is a
nonzero P ∈ ℂ[a,b] such that for all complex a, b with P(a,b) ≠ 0:
* a_e² ≠ 1 for every edge;
* the non-normalizable locus at (a,b) is nonempty;
* at every point y of the locus, with chart coordinates x_e = y_{(e,false)}, the Jacobian of the
  chart equations has rank |V|, its kernel has dimension ν(G) − 1, and the implicit function
  theorem gives an open partial homeomorphism Ψ of ℂ^E onto an open subset of ℂ^V × W with
  dim W = ν(G) − 1, x in its source, Ψ x = (Φ(a,x), 0) and first component Φ(a,·). -/
theorem supp_nonnormalizable_dim_cyclic (hc : G.Connected) (hν : 1 ≤ G.nu) :
    ∃ P : MvPolynomial (E ⊕ V) ℂ, P ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), eval (Sum.elim a b) P ≠ 0 →
        (∀ e, a e ^ 2 ≠ 1) ∧ (∃ y, G.IsNonnormalizableSolution a b y) ∧
          ∀ y, G.IsNonnormalizableSolution a b y →
            G.IsRegularChartPoint a (fun e => y (e, false)) ∧
            Module.finrank ℂ (LinearMap.ker (G.chartJac a (fun e => y (e, false))).mulVecLin) =
              G.nu - 1 ∧
            ∃ (W : Submodule ℂ (E → ℂ)) (Ψ : OpenPartialHomeomorph (E → ℂ) ((V → ℂ) × W)),
              Module.finrank ℂ W = G.nu - 1 ∧ (fun e => y (e, false)) ∈ Ψ.source ∧
                Ψ (fun e => y (e, false)) = (G.chartFieldMap a (fun e => y (e, false)), 0) ∧
                ∀ x', (Ψ x').1 = G.chartFieldMap a x' := by
  have hcard := (G.one_le_nu_iff_of_connected hc).mp hν
  obtain ⟨g, hg, hne⟩ := G.exists_poly_nonnormalizable_nonempty hc hcard
  obtain ⟨Q, hQ, hreg⟩ := G.nonnormalizable_regular hc
  have hQ' : map (Int.castRingHom ℂ) Q ≠ 0 := fun h =>
    hQ (map_injective (Int.castRingHom ℂ) (RingHom.injective_int _) (h.trans (map_zero _).symm))
  refine ⟨g * map (Int.castRingHom ℂ) Q, mul_ne_zero hg hQ', fun a b hab => ?_⟩
  rw [eval_mul] at hab
  obtain ⟨ha, hy⟩ := hne a b (left_ne_zero_of_mul hab)
  refine ⟨ha, hy, fun y hy' => ?_⟩
  have hr := hreg ℂ a b ha (right_ne_zero_of_mul hab) y hy'
  have hx := (G.chart_of_isNonnormalizableSolution hy').2.1
  refine ⟨hr, G.finrank_ker_chartJac_eq_nu_sub_one hc hr, ?_⟩
  obtain ⟨W, Ψ, hW, hs, hself, hfst⟩ := G.exists_openPartialHomeomorph_chartFiber hx hr
  exact ⟨W, Ψ, hW.trans (G.nu_sub_one_eq_of_connected hc).symm, hs, hself, hfst⟩

end Multigraph

end BPFixedPoints
