import BPFixedPoints.Incidence.CoxNormalizedCharts
import BPFixedPoints.Incidence.IncidenceAffineCharts
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Independent homogeneous zero equations recover the original incidence charts

Start with the universal bilinear equations in two homogeneous variables per
vertex. Normalize the chosen coordinate to one, then impose those original
equations. The resulting quotient is naturally isomorphic to the original
incidence chart quotient. A global product-Proj construction is not assumed.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Original universal bilinear equation in homogeneous coordinates. -/
noncomputable def incCoxHomogeneousEquation (e : E) : IncCoxRing V E :=
  ∑ α : Fin 2, ∑ β : Fin 2, X (Sum.inr (e, α, β)) *
    X (Sum.inl (G.fst e, α)) * X (Sum.inl (G.snd e, β))

/-- Multihomogeneous weight belonging to a single projective vertex factor. -/
def incCoxVertexWeight (v : V) : IncCoxVar V E → ℕ
  | Sum.inl (w, _) => if w = v then 1 else 0
  | Sum.inr _ => 0

/-- Each original equation has precisely the endpoint degree in every projective
factor, with both occurrences counted for a loop. Coefficients have degree zero. -/
theorem incCoxHomogeneousEquation_vertex_degree (e : E) (v : V) :
    IsWeightedHomogeneous (incCoxVertexWeight (E := E) v) (G.incCoxHomogeneousEquation e)
      ((if G.fst e = v then 1 else 0) + (if G.snd e = v then 1 else 0)) := by
  apply IsWeightedHomogeneous.sum
  intro α _
  apply IsWeightedHomogeneous.sum
  intro β _
  have hc := isWeightedHomogeneous_X (R := ℂ) (incCoxVertexWeight (E := E) v) (Sum.inr (e, α, β))
  have hu := isWeightedHomogeneous_X (R := ℂ) (incCoxVertexWeight (E := E) v) (Sum.inl (G.fst e, α))
  have hv := isWeightedHomogeneous_X (R := ℂ) (incCoxVertexWeight (E := E) v) (Sum.inl (G.snd e, β))
  simpa only [incCoxVertexWeight, zero_add] using (hc.mul hu).mul hv

/-- Dehomogenizing the original homogeneous equation gives exactly the existing chart equation. -/
theorem incCoxHomogeneousEquation_dehomogenize (σ : V → Bool) (e : E) :
    incCoxDehomogenize σ (G.incCoxHomogeneousEquation e) = G.incChartEq σ e := by
  simp only [incCoxHomogeneousEquation, incCoxDehomogenize, map_sum, map_mul, aeval_X,
    incCoxNormalizedValue, incChartEq]

/-- Original homogeneous zero ideal on the independently normalized coordinate chart. -/
noncomputable def incNormalizedCoxZeroIdeal (σ : V → Bool) :
    Ideal (IncNormalizedCoxRing (E := E) σ) :=
  Ideal.span (Set.range (fun e => Ideal.Quotient.mk (incCoxNormalizationIdeal (E := E) σ)
    (G.incCoxHomogeneousEquation e)))

/-- The normalized original homogeneous zero ideal maps to the actual incidence chart ideal. -/
theorem incNormalizedCoxZeroIdeal_map (σ : V → Bool) :
    (G.incNormalizedCoxZeroIdeal σ).map (incNormalizedCoxChartEquiv (E := E) σ).toRingHom =
      Ideal.span (Set.range (G.incChartEq σ)) := by
  rw [incNormalizedCoxZeroIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext e
  exact G.incCoxHomogeneousEquation_dehomogenize σ e

/-- The normalized homogeneous zero ring, defined independently of the original incidence quotient. -/
abbrev IncNormalizedCoxZeroRing (σ : V → Bool) :=
  IncNormalizedCoxRing (E := E) σ ⧸ G.incNormalizedCoxZeroIdeal σ

/-- Natural comparison of the independent homogeneous zero chart with the original incidence chart. -/
noncomputable def incNormalizedCoxZeroEquiv (σ : V → Bool) :
    G.IncNormalizedCoxZeroRing σ ≃ₐ[ℂ] G.IncChartRing σ :=
  Ideal.quotientEquivAlg _ _ (incNormalizedCoxChartEquiv σ)
    (G.incNormalizedCoxZeroIdeal_map σ).symm

/-- Actual scheme isomorphism on each normalized homogeneous zero chart. -/
noncomputable def incidenceNormalizedCoxZeroIso (σ : V → Bool) :
    G.incidenceAffineChart σ ≅ Spec (CommRingCat.of (G.IncNormalizedCoxZeroRing σ)) :=
  { hom := Spec.map (G.incNormalizedCoxZeroEquiv σ).toRingEquiv.toCommRingCatIso.hom
    inv := Spec.map (G.incNormalizedCoxZeroEquiv σ).toRingEquiv.toCommRingCatIso.inv
    hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]; rfl
    inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id] }

/-- The universal homogeneous zero ideal, defined before choosing any chart. -/
noncomputable def incCoxHomogeneousZeroIdeal : Ideal (IncCoxRing V E) :=
  Ideal.span (Set.range G.incCoxHomogeneousEquation)

/-- The normalization of the homogeneous zero scheme, as one quotient of the
original homogeneous ambient ring by the sum of the two actual ideals. -/
abbrev IncCoxZeroSliceRing (σ : V → Bool) :=
  IncCoxRing V E ⧸ (incCoxNormalizationIdeal (E := E) σ ⊔ G.incCoxHomogeneousZeroIdeal)

theorem incCoxHomogeneousZeroIdeal_normalize (σ : V → Bool) :
    G.incCoxHomogeneousZeroIdeal.map
      (Ideal.Quotient.mkₐ ℂ (incCoxNormalizationIdeal (E := E) σ)).toRingHom =
        G.incNormalizedCoxZeroIdeal σ := by
  rw [incCoxHomogeneousZeroIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

/-- Direct homogeneous-equation normalization recovers the original incidence
chart, independently of the previously glued incidence scheme. -/
noncomputable def incCoxZeroSliceEquiv (σ : V → Bool) :
    G.IncCoxZeroSliceRing σ ≃ₐ[ℂ] G.IncChartRing σ :=
  ((DoubleQuot.quotQuotEquivQuotSupₐ ℂ
    (incCoxNormalizationIdeal (E := E) σ) G.incCoxHomogeneousZeroIdeal).symm.trans
      (Ideal.quotientEquivAlgOfEq ℂ (G.incCoxHomogeneousZeroIdeal_normalize σ))).trans
    (G.incNormalizedCoxZeroEquiv σ)

/-- Existence form of the actual homogeneous-zero chart comparison. -/
theorem incidenceHomogeneousZeroCharts (σ : V → Bool) :
    Nonempty (G.IncCoxZeroSliceRing σ ≃ₐ[ℂ] G.IncChartRing σ) :=
  ⟨G.incCoxZeroSliceEquiv σ⟩

end BPFixedPoints.Multigraph
