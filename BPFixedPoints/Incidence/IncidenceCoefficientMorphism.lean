import BPFixedPoints.Incidence.IncidenceGluedIntersections
import BPFixedPoints.Incidence.CoefficientModule

/-! # The genuine incidence scheme over the original coefficient space

The projection is glued from the original coefficient variables on every face.
It is not defined by transporting the existing incidence-ring coefficient action
through the global-section equivalence.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original universal coefficient variables on each actual quotient face. -/
noncomputable def incidenceFaceCoefficientHom (q : V → Fin 3) :
    IncCoeffRing E →ₐ[ℂ] G.IncFaceRing q :=
  aeval (fun (c : IncCoeffIdx E) => Ideal.Quotient.mk (G.incFaceIdeal q) (X c))

@[simp] theorem incidenceFaceCoefficientHom_X (q : V → Fin 3) (c : IncCoeffIdx E) :
    G.incidenceFaceCoefficientHom q (X c) = Ideal.Quotient.mk _ (X c) := by
  simp [incidenceFaceCoefficientHom]

/-- Refinement fixes the original coefficient variables. -/
theorem incidenceFaceCoefficientHom_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    (G.incFaceRefinement h).comp (G.incidenceFaceCoefficientHom q) =
      G.incidenceFaceCoefficientHom r := by
  apply MvPolynomial.algHom_ext
  intro c
  simp only [AlgHom.comp_apply, G.incidenceFaceCoefficientHom_X, G.incFaceRefinement_X]

/-- Coefficient projections on the actual affine faces are a compatible cocone. -/
noncomputable def incidenceCoefficientCocone : Cocone G.incidenceFaceDiagram where
  pt := Spec (CommRingCat.of (IncCoeffRing E))
  ι.app q := Spec.map (CommRingCat.ofHom (G.incidenceFaceCoefficientHom q.ofDual.coord).toRingHom)
  ι.naturality q r f := by
    dsimp [incidenceFaceDiagram, incidenceFaceMap]
    rw [← Spec.map_comp, Category.comp_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (G.incidenceFaceCoefficientHom_refinement (leOfHom f))

/-- Projection to the original affine coefficient space, obtained from the
actual universal coefficient maps on the original quotient atlas. -/
noncomputable def incidenceCoefficientMorphism :
    G.incidenceGluedScheme ⟶ Spec (CommRingCat.of (IncCoeffRing E)) :=
  colimit.desc G.incidenceFaceDiagram G.incidenceCoefficientCocone

/-- The geometric projection has its original coefficient formula on every face. -/
theorem incidenceFaceι_coefficient (q : V → Fin 3) :
    G.incidenceFaceι q ≫ G.incidenceCoefficientMorphism =
      Spec.map (CommRingCat.ofHom (G.incidenceFaceCoefficientHom q).toRingHom) :=
  colimit.ι_desc G.incidenceCoefficientCocone (OrderDual.toDual ⟨q⟩)

/-- The all-Laurent presentation also uses the original torus coefficient map. -/
theorem incidenceFaceCoefficientHom_torus :
    (G.incFaceToTorus (fun _ => 2)).comp (G.incidenceFaceCoefficientHom (fun _ => 2)) =
      G.incTorusCoeffHom := by
  apply MvPolynomial.algHom_ext
  intro c
  rw [AlgHom.comp_apply, G.incidenceFaceCoefficientHom_X, G.incFaceToTorus_X]
  exact (G.incTorusCoeffHom_X c).symm

/-- The coefficient-space projection restricts to the original torus projection. -/
theorem incidenceTorusι_coefficient :
    G.incidenceTorusι ≫ G.incidenceCoefficientMorphism =
      Spec.map (CommRingCat.ofHom G.incTorusCoeffHom.toRingHom) := by
  unfold incidenceTorusι
  rw [Category.assoc, G.incidenceFaceι_coefficient, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom G.incidenceFaceCoefficientHom_torus

/-- The coefficient action on actual global functions induced by the actual
geometric projection to coefficient space. -/
noncomputable def incidenceGlobalCoefficientHom :
    IncCoeffRing E →+* Γ(G.incidenceGluedScheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (IncCoeffRing E))).inv ≫
    G.incidenceCoefficientMorphism.appTop).hom

end BPFixedPoints.Multigraph
