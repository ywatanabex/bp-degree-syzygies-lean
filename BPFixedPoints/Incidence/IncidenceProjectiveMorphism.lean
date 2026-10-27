import BPFixedPoints.Incidence.ProjectiveLineEvaluation
import BPFixedPoints.Incidence.ProjectivePowerCoordinates
import BPFixedPoints.Incidence.IncidenceCoefficientMorphism
import BPFixedPoints.Incidence.CechFaceTransitionUnits

/-! # The original incidence scheme maps into the actual projective product

Every original face supplies its original polynomial coordinate at each vertex.
The Laurent transition proves compatibility as actual scheme morphisms.
The maps are glued by the existing face colimit, over the original coefficient
space, and assembled using the full projective-product universal property.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original vertex coordinate in the actual incidence face quotient. -/
noncomputable def incidenceFaceVertexCoordinate (q : V → Fin 3) (v : V) : G.IncFaceRing q :=
  Ideal.Quotient.mk _ (C (faceVariable ℂ q v))

/-- On a Laurent face the original coordinate retains its actual inverse. -/
noncomputable def incidenceFaceVertexUnit (q : V → Fin 3) (v : V) (hv : q v = 2) :
    (G.IncFaceRing q)ˣ :=
  Units.map (((Ideal.Quotient.mk (G.incFaceIdeal q)).comp C).toMonoidHom)
    (faceLaurentUnit ℂ q v hv)

@[simp] theorem incidenceFaceVertexUnit_val (q : V → Fin 3) (v : V) (hv : q v = 2) :
    (G.incidenceFaceVertexUnit q v hv : G.IncFaceRing q) =
      G.incidenceFaceVertexCoordinate q v := rfl

/-- Original quotient coordinates restrict by identity or the actual inverse monomial. -/
theorem incidenceFaceVertexCoordinate_refinement {q r : V → Fin 3}
    (h : FaceRefines q r) (v : V) :
    G.incFaceRefinement h (G.incidenceFaceVertexCoordinate q v) =
      if hf : q v = 1 ∧ r v = 2 then (↑((G.incidenceFaceVertexUnit r v hf.2)⁻¹) : G.IncFaceRing r)
      else G.incidenceFaceVertexCoordinate r v := by
  rw [incidenceFaceVertexCoordinate, G.incFaceRefinement_C, faceRefinement_variable]
  split_ifs <;> rfl

/-- Choose the original right chart only for a right face; an overlap uses the left chart. -/
def incidenceFaceVertexPivot (q : Fin 3) : Fin 2 := if q = 1 then 1 else 0

/-- The original vertex coordinate gives an actual morphism into Mathlib's Proj. -/
noncomputable def incidenceFaceVertexMorphism (q : V → Fin 3) (v : V) :
    G.incidenceAffineFace q ⟶ ProjectiveLine.projectiveLine (IncCoeffRing E) :=
  ProjectiveLine.evaluationChart (G.incidenceFaceCoefficientHom q).toRingHom
    (G.incidenceFaceVertexCoordinate q v) (incidenceFaceVertexPivot (q v))

/-- All original face restrictions give the same actual projective coordinate. -/
@[reassoc] theorem incidenceFaceVertexMorphism_refinement {q r : V → Fin 3}
    (h : FaceRefines q r) (v : V) :
    G.incidenceFaceMap h ≫ G.incidenceFaceVertexMorphism q v =
      G.incidenceFaceVertexMorphism r v := by
  dsimp only [incidenceFaceMap, incidenceFaceVertexMorphism]
  rw [ProjectiveLine.evaluationChart_natural]
  have hc : (G.incFaceRefinement h).toRingHom.comp
      (G.incidenceFaceCoefficientHom q).toRingHom =
        (G.incidenceFaceCoefficientHom r).toRingHom :=
    congrArg AlgHom.toRingHom (G.incidenceFaceCoefficientHom_refinement h)
  rw [hc]
  change ProjectiveLine.evaluationChart (G.incidenceFaceCoefficientHom r).toRingHom
    (G.incFaceRefinement h (G.incidenceFaceVertexCoordinate q v))
      (incidenceFaceVertexPivot (q v)) =
    ProjectiveLine.evaluationChart (G.incidenceFaceCoefficientHom r).toRingHom
      (G.incidenceFaceVertexCoordinate r v) (incidenceFaceVertexPivot (r v))
  rw [G.incidenceFaceVertexCoordinate_refinement]
  split_ifs with hf
  · simp only [incidenceFaceVertexPivot, hf.1, hf.2, ite_true, Fin.reduceEq, ite_false]
    have ht := (ProjectiveLine.evaluationChart_unit_transition
      (R := IncCoeffRing E) (A := G.IncFaceRing r)
      (G.incidenceFaceCoefficientHom r).toRingHom (G.incidenceFaceVertexUnit r v hf.2)).symm
    simpa only [incidenceFaceVertexUnit_val] using ht
  · have hp : incidenceFaceVertexPivot (q v) = incidenceFaceVertexPivot (r v) := by
      rcases h v with he | he
      · rw [he]
      · have hq : q v ≠ 1 := fun hh => hf ⟨hh, he⟩
        simp [incidenceFaceVertexPivot, hq, he]
    rw [hp]

/-- The projective-coordinate cocone is defined by the original quotient variables. -/
noncomputable def incidenceVertexCocone (v : V) : Cocone G.incidenceFaceDiagram where
  pt := ProjectiveLine.projectiveLine (IncCoeffRing E)
  ι.app q := G.incidenceFaceVertexMorphism q.ofDual.coord v
  ι.naturality q r f := by
    change G.incidenceFaceMap (leOfHom f) ≫
      G.incidenceFaceVertexMorphism r.ofDual.coord v =
        G.incidenceFaceVertexMorphism q.ofDual.coord v ≫ 𝟙 _
    rw [Category.comp_id]
    exact G.incidenceFaceVertexMorphism_refinement (leOfHom f) v

/-- The genuine incidence scheme's original vertex projection to the actual Proj line. -/
noncomputable def incidenceVertexMorphism (v : V) :
    G.incidenceGluedScheme ⟶ ProjectiveLine.projectiveLine (IncCoeffRing E) :=
  colimit.desc G.incidenceFaceDiagram (G.incidenceVertexCocone v)

@[reassoc] theorem incidenceFaceι_vertex (q : V → Fin 3) (v : V) :
    G.incidenceFaceι q ≫ G.incidenceVertexMorphism v = G.incidenceFaceVertexMorphism q v :=
  colimit.ι_desc (G.incidenceVertexCocone v) (OrderDual.toDual ⟨q⟩)

/-- Every glued projective coordinate retains the original geometric coefficient map. -/
@[reassoc] theorem incidenceVertexMorphism_toBase (v : V) :
    G.incidenceVertexMorphism v ≫ ProjectiveLine.toSpecBase (IncCoeffRing E) =
      G.incidenceCoefficientMorphism := by
  apply colimit.hom_ext
  intro q
  rw [← Category.assoc, show colimit.ι G.incidenceFaceDiagram q =
    G.incidenceFaceι q.ofDual.coord from rfl, G.incidenceFaceι_vertex,
    G.incidenceFaceι_coefficient]
  exact ProjectiveLine.evaluationChart_toSpecBase _ _ _

/-- The original geometric incidence scheme as an object over coefficient space. -/
noncomputable def incidenceOverCoefficientBase : Over (Spec (CommRingCat.of (IncCoeffRing E))) :=
  Over.mk G.incidenceCoefficientMorphism

/-- The actual vertex projection is a morphism over the original coefficient base. -/
noncomputable def incidenceVertexOver (v : V) :
    G.incidenceOverCoefficientBase ⟶ ProjectiveLine.overBase (IncCoeffRing E) :=
  Over.homMk (G.incidenceVertexMorphism v) (G.incidenceVertexMorphism_toBase v)

/-- Assemble the original vertex coordinates by the actual product universal property. -/
noncomputable def incidenceProjectiveOver :
    G.incidenceOverCoefficientBase ⟶ ProjectiveLine.vertexOverBase (IncCoeffRing E) V :=
  (ProjectiveLine.vertexIsProduct (IncCoeffRing E) V).lift
    (Fan.mk G.incidenceOverCoefficientBase G.incidenceVertexOver)

/-- The actual map from the original incidence scheme into the projective product. -/
noncomputable def incidenceProjectiveMorphism :
    G.incidenceGluedScheme ⟶ ProjectiveLine.vertexScheme (IncCoeffRing E) V :=
  G.incidenceProjectiveOver.left

/-- The map into the actual projective product has precisely the original vertex coordinates. -/
@[reassoc] theorem incidenceProjectiveMorphism_projection (v : V) :
    G.incidenceProjectiveMorphism ≫
        (ProjectiveLine.vertexProjectionOver (IncCoeffRing E) V v).left =
      G.incidenceVertexMorphism v := by
  exact congrArg Over.Hom.left
    ((ProjectiveLine.vertexIsProduct (IncCoeffRing E) V).fac
      (Fan.mk G.incidenceOverCoefficientBase G.incidenceVertexOver) ⟨v⟩)

/-- The map into the actual projective product preserves the geometric coefficient projection. -/
@[reassoc] theorem incidenceProjectiveMorphism_toBase :
    G.incidenceProjectiveMorphism ≫ ProjectiveLine.vertexToBase (IncCoeffRing E) V =
      G.incidenceCoefficientMorphism :=
  G.incidenceProjectiveOver.w

/-- On every original face, all coordinates of the global projective map retain their formulas. -/
@[reassoc] theorem incidenceFaceι_projective_projection (q : V → Fin 3) (v : V) :
    G.incidenceFaceι q ≫ G.incidenceProjectiveMorphism ≫
        (ProjectiveLine.vertexProjectionOver (IncCoeffRing E) V v).left =
      G.incidenceFaceVertexMorphism q v := by
  rw [G.incidenceProjectiveMorphism_projection, G.incidenceFaceι_vertex]

end BPFixedPoints.Multigraph
