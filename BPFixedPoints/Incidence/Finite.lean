import BPFixedPoints.Incidence.Integral
import BPFixedPoints.Incidence.FiniteTools

/-!
# Finiteness of the universal incidence ring

Noether-normalize the coefficient image and use finiteness of its integral
closure in the fraction field of the common torus. Valuation-theoretic
integrality embeds the incidence ring as a submodule of this finite module.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable (G : Multigraph V E)

/-- The universal incidence ring is a finite module over the coefficient ring. -/
theorem coeffHom_finite : G.coeffHom.toRingHom.Finite := by
  let K := FractionRing G.IncTorusRing
  let g : G.IncidenceRing →ₐ[ℂ] K :=
    (Algebra.algHom ℂ G.IncTorusRing K).comp G.IncidenceRing.val
  have hg : Function.Injective g :=
    (IsFractionRing.injective G.IncTorusRing K).comp Subtype.val_injective
  let f : G.coeffHom.range →ₐ[ℂ] G.IncidenceRing := G.coeffHom.range.val
  have : Algebra.FiniteType ℂ G.coeffHom.range :=
    Algebra.FiniteType.of_surjective G.coeffHom.rangeRestrict
      G.coeffHom.rangeRestrict_surjective
  have hint : f.toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top G.coeffHom.rangeRestrict.toRingHom f.toRingHom
      G.coeffHom_isIntegral
  have hf : f.toRingHom.Finite :=
    IntegralTools.finite_of_integral_of_field_embedding f g Subtype.val_injective hg hint
  exact hf.comp (RingHom.Finite.of_surjective G.coeffHom.rangeRestrict.toRingHom
    G.coeffHom.rangeRestrict_surjective)

end BPFixedPoints.Multigraph
