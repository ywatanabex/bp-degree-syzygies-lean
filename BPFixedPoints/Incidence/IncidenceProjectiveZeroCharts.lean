import BPFixedPoints.Incidence.IncidenceProjectiveClosedImmersion
import BPFixedPoints.Incidence.CoxIncidenceZeroCharts

/-! # Independent original zero equations on the actual projective-product charts

The equations are defined before imposing the incidence quotient. They are
the original homogeneous Cox equations dehomogenized on each pivot choice,
in the original vertex polynomial ring over the universal coefficient ring.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original homogeneous edge equation in a genuine projective-product polynomial chart. -/
noncomputable def incidenceProjectiveEquation (σ : V → Bool) (e : E) :
    MvPolynomial V (IncCoeffRing E) :=
  (G.incidenceChartAmbientPolynomialEquiv σ).symm (G.incFaceEquation (chartFace σ) e)

/-- The independent equation retains the original coefficient and vertex polynomial formula. -/
theorem incidenceProjectiveEquation_original (σ : V → Bool) (e : E) :
    G.incidenceProjectiveEquation σ e =
      sumAlgEquiv ℂ V (IncCoeffIdx E) (G.incChartEq σ e) := by
  change sumAlgEquiv ℂ V (IncCoeffIdx E)
    (G.chartFaceAmbientEquiv σ (G.incFaceEquation (chartFace σ) e)) = _
  rw [G.chartFaceAmbientEquiv_equation]

/-- These equations come from the independently defined original homogeneous Cox equations. -/
theorem incidenceProjectiveEquation_from_homogeneous (σ : V → Bool) (e : E) :
    sumAlgEquiv ℂ V (IncCoeffIdx E)
      (incCoxDehomogenize σ (G.incCoxHomogeneousEquation e)) =
        G.incidenceProjectiveEquation σ e := by
  rw [G.incCoxHomogeneousEquation_dehomogenize, G.incidenceProjectiveEquation_original]

/-- The independently specified full zero ideal in the original polynomial chart. -/
noncomputable def incidenceProjectiveChartIdeal (σ : V → Bool) :
    Ideal (MvPolynomial V (IncCoeffRing E)) :=
  Ideal.span (Set.range (G.incidenceProjectiveEquation σ))

theorem incidenceProjectiveChartIdeal_map (σ : V → Bool) :
    G.incFaceIdeal (chartFace σ) = (G.incidenceProjectiveChartIdeal σ).map
      (G.incidenceChartAmbientPolynomialEquiv σ).toRingHom := by
  rw [incFaceIdeal, incidenceProjectiveChartIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext e
  exact ((G.incidenceChartAmbientPolynomialEquiv σ).apply_symm_apply _).symm

/-- The independent original zero ring, with nilpotents and multiplicities retained. -/
abbrev IncidenceProjectiveZeroChartRing (σ : V → Bool) :=
  MvPolynomial V (IncCoeffRing E) ⧸ G.incidenceProjectiveChartIdeal σ

/-- The original quotient face is isomorphic to this independently defined zero ring. -/
noncomputable def incidenceProjectiveZeroChartEquiv (σ : V → Bool) :
    G.IncidenceProjectiveZeroChartRing σ ≃ₐ[ℂ] G.IncFaceRing (chartFace σ) :=
  Ideal.quotientEquivAlg _ _ (G.incidenceChartAmbientPolynomialEquiv σ)
    (G.incidenceProjectiveChartIdeal_map σ)

@[simp] theorem incidenceProjectiveZeroChartEquiv_mk (σ : V → Bool)
    (p : MvPolynomial V (IncCoeffRing E)) :
    G.incidenceProjectiveZeroChartEquiv σ (Ideal.Quotient.mk _ p) =
      G.incidenceChartPolynomialHom σ p := rfl

/-- The independently specified zero chart as an actual affine scheme. -/
noncomputable def incidenceProjectiveZeroChart (σ : V → Bool) : Scheme :=
  Spec (CommRingCat.of (G.IncidenceProjectiveZeroChartRing σ))

/-- Its actual morphism into the independently defined projective product. -/
noncomputable def incidenceProjectiveZeroChartι (σ : V → Bool) :
    G.incidenceProjectiveZeroChart σ ⟶ ProjectiveLine.vertexScheme (IncCoeffRing E) V :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ))) ≫
    ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ)

/-- Scheme comparison retaining the original quotient rather than only its set of zeros. -/
noncomputable def incidenceProjectiveZeroChartIso (σ : V → Bool) :
    G.incidenceAffineFace (chartFace σ) ≅ G.incidenceProjectiveZeroChart σ :=
  Scheme.Spec.mapIso (G.incidenceProjectiveZeroChartEquiv σ).toRingEquiv.toCommRingCatIso.op

/-- The independently constructed zero chart has the original actual projective morphism. -/
@[reassoc] theorem incidenceProjectiveZeroChartIso_hom_ι (σ : V → Bool) :
    (G.incidenceProjectiveZeroChartIso σ).hom ≫ G.incidenceProjectiveZeroChartι σ =
      G.incidenceFaceι (chartFace σ) ≫ G.incidenceProjectiveMorphism := by
  rw [← G.incidenceProjectiveMorphism_chart]
  dsimp only [incidenceProjectiveZeroChartIso, incidenceProjectiveZeroChartι,
    Functor.mapIso_hom, Scheme.Spec_map, Iso.op_hom, Quiver.Hom.unop_op]
  rw [← Spec.map_comp_assoc]
  rfl

end BPFixedPoints.Multigraph
