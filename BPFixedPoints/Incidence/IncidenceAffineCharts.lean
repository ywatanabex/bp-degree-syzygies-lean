import BPFixedPoints.Incidence.Torus
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties

/-! # Actual affine incidence charts and their common torus open

Construct spectra of the existing chart rings and prove that the existing torus
restriction maps induce open immersions. This supplies actual affine schemes,
but does not glue them along their larger pairwise overlaps.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E) (σ : V → Bool)

/-- The original polynomial chart ring is an integral domain. -/
instance incChartRing_isDomain : IsDomain (G.IncChartRing σ) :=
  (G.incChartEquiv σ).injective.isDomain (G.incChartEquiv σ).toRingHom

/-- Product of all vertex coordinates on the given actual chart. -/
noncomputable def incChartTorusDen : G.IncChartRing σ :=
  (G.incChartEquiv σ).symm (incFreeDen (V := V) (E := E))

/-- Upgrade the known torus equivalence to an equivalence over free chart coordinates. -/
noncomputable def incTorusEquivOverFree :
    letI : Algebra (IncFreeRing V E) G.IncTorusRing := (G.incFreeToTorus σ).toRingHom.toAlgebra
    G.IncTorusRing ≃ₐ[IncFreeRing V E] IncLocalRing V E := by
  letI : Algebra (IncFreeRing V E) G.IncTorusRing := (G.incFreeToTorus σ).toRingHom.toAlgebra
  refine { (G.incTorusEquiv σ).toRingEquiv with commutes' := ?_ }
  intro r
  change G.incTorusToLocal σ (G.incFreeToTorus σ r) = algebraMap _ _ r
  change G.incTorusToLocal σ (G.incChartMap σ ((G.incChartEquiv σ).symm r)) = _
  rw [G.incTorusToLocal_chart_apply, AlgEquiv.apply_symm_apply]

/-- The original torus map is localization at the actual chart denominator. -/
theorem incTorus_isLocalization_chart :
    letI : Algebra (G.IncChartRing σ) G.IncTorusRing := (G.incChartMap σ).toRingHom.toAlgebra
    IsLocalization.Away (G.incChartTorusDen σ) G.IncTorusRing := by
  letI : Algebra (G.IncChartRing σ) G.IncTorusRing := (G.incChartMap σ).toRingHom.toAlgebra
  letI : Algebra (IncFreeRing V E) G.IncTorusRing := (G.incFreeToTorus σ).toRingHom.toAlgebra
  haveI : IsLocalization.Away (incFreeDen (V := V) (E := E)) G.IncTorusRing :=
    IsLocalization.isLocalization_of_algEquiv _ (G.incTorusEquivOverFree σ).symm
  apply IsLocalization.of_ringEquiv_left
    (M₁ := Submonoid.powers (incFreeDen (V := V) (E := E)))
    (M₂ := Submonoid.powers (G.incChartTorusDen σ)) (G.incChartEquiv σ).toRingEquiv
  · rw [Submonoid.map_powers]
    congr 1
    exact (G.incChartEquiv σ).apply_symm_apply _
  · intro x
    change G.incChartMap σ x = G.incFreeToTorus σ (G.incChartEquiv σ x)
    simp only [incFreeToTorus, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.symm_apply_apply]

/-- The actual affine scheme of an existing incidence chart. -/
noncomputable def incidenceAffineChart : Scheme :=
  Spec (CommRingCat.of (G.IncChartRing σ))

/-- The actual affine common torus scheme. -/
noncomputable def incidenceAffineTorus : Scheme :=
  Spec (CommRingCat.of G.IncTorusRing)

/-- Contravariant scheme map induced by the existing chart restriction. -/
noncomputable def incidenceAffineTorusToChart :
    G.incidenceAffineTorus ⟶ G.incidenceAffineChart σ :=
  Spec.map (CommRingCat.ofHom (G.incChartMap σ).toRingHom)

/-- The actual common torus embeds openly into every incidence chart. -/
theorem incidenceAffineTorusToChart_isOpenImmersion :
    IsOpenImmersion (G.incidenceAffineTorusToChart σ) := by
  letI : Algebra (G.IncChartRing σ) G.IncTorusRing := (G.incChartMap σ).toRingHom.toAlgebra
  haveI := G.incTorus_isLocalization_chart σ
  exact IsOpenImmersion.of_isLocalization (G.incChartTorusDen σ)

instance incidenceAffineChart_isIntegral : IsIntegral (G.incidenceAffineChart σ) := by
  unfold incidenceAffineChart
  infer_instance

instance incidenceAffineTorus_isIntegral : IsIntegral G.incidenceAffineTorus := by
  unfold incidenceAffineTorus
  infer_instance

end BPFixedPoints.Multigraph
