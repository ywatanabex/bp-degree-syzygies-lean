import BPFixedPoints.Incidence.IncidenceRefinementLocalization
import Mathlib.AlgebraicGeometry.Gluing

/-! # The genuine open-immersion diagram of all incidence faces

Objects are spectra of the original incidence face quotient rings. The order
records passage to higher intersections, and all arrows are actual localization
open immersions. The cocycle law is inherited from the quotient restrictions.
-/

namespace BPFixedPoints.CechProduct

/-- Face indices with the refinement order, independent of the numerical order on `Fin 3`. -/
@[ext] structure FaceIndex (V : Type*) where
  coord : V → Fin 3

instance {V : Type*} : PartialOrder (FaceIndex V) where
  le q r := FaceRefines q.coord r.coord
  le_refl q := faceRefines_refl q.coord
  le_trans _ _ _ := faceRefines_trans
  le_antisymm q r hqr hrq := by
    apply FaceIndex.ext
    funext v
    by_cases he : q.coord v = r.coord v
    · exact he
    · have hr := (hqr v).resolve_left he
      have hq := (hrq v).resolve_left (Ne.symm he)
      exact hq.trans hr.symm

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Scheme map from a higher incidence intersection to its parent face. -/
noncomputable def incidenceFaceMap {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceAffineFace r ⟶ G.incidenceAffineFace q :=
  Spec.map (CommRingCat.ofHom (G.incFaceRefinement h).toRingHom)

instance incidenceFaceMap_isOpenImmersion {q r : V → Fin 3} (h : FaceRefines q r) :
    IsOpenImmersion (G.incidenceFaceMap h) := by
  letI := G.incidenceRefinementAlgebra h
  haveI := G.incidenceRefinement_isLocalization h
  exact IsOpenImmersion.of_isLocalization (G.incidenceRefinementDen h)

/-- The complete original-face diagram, with arrows from higher intersections to charts. -/
noncomputable def incidenceFaceDiagram : (FaceIndex V)ᵒᵈ ⥤ Scheme where
  obj q := G.incidenceAffineFace q.ofDual.coord
  map f := G.incidenceFaceMap (leOfHom f)
  map_id q := by
    dsimp [incidenceFaceMap]
    rw [G.incFaceRefinement_refl]
    exact Spec.map_id _
  map_comp f g := by
    dsimp [incidenceFaceMap]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom
      (G.incFaceRefinement_comp (leOfHom g) (leOfHom f)).symm

instance incidenceFaceDiagram_map_isOpenImmersion {q r : (FaceIndex V)ᵒᵈ} (f : q ⟶ r) :
    IsOpenImmersion (G.incidenceFaceDiagram.map f) :=
  G.incidenceFaceMap_isOpenImmersion (leOfHom f)

end BPFixedPoints.Multigraph
