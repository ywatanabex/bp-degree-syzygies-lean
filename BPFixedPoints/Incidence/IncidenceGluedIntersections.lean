import BPFixedPoints.Incidence.IncidenceGluedGlobalSections

/-! # Higher incidence faces are the actual intersections in the glued scheme

This identifies the overlap opens after gluing, rather than just exhibiting
maps of face rings. In particular it rules out gluing only along the common
torus: all points of the prescribed higher incidence faces are retained.
-/

namespace BPFixedPoints.CechProduct

/-- The join is the least common refinement, for arbitrary faces. -/
theorem faceRefines_of_join {V : Type*} {q r s : V → Fin 3}
    (hq : FaceRefines q s) (hr : FaceRefines r s) : FaceRefines (faceJoin q r) s := by
  intro v
  by_cases he : q v = r v
  · simpa [faceJoin, he] using hq v
  · have ha := hq v
    have hb := hr v
    exact Or.inr (by omega)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Images of full higher faces are exactly the actual intersections of the
original face opens in the constructed scheme. -/
theorem incidenceFaceι_join_range (q r : V → Fin 3) :
    Set.range (G.incidenceFaceι (faceJoin q r)) =
      Set.range (G.incidenceFaceι q) ∩ Set.range (G.incidenceFaceι r) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · refine ⟨G.incidenceFaceMap (faceRefines_join_left q r) y, ?_⟩
      rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]
    · refine ⟨G.incidenceFaceMap (faceRefines_join_right q r) y, ?_⟩
      rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]
  · rintro ⟨⟨y, rfl⟩, z, hz⟩
    have he : colimit.ι G.incidenceFaceDiagram (OrderDual.toDual (FaceIndex.mk q)) y =
        colimit.ι G.incidenceFaceDiagram (OrderDual.toDual (FaceIndex.mk r)) z := hz.symm
    obtain ⟨s, fq, fr, w, hwq, hwr⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff G.incidenceFaceDiagram).mp he
    let hsq : FaceRefines q s.ofDual.coord := leOfHom fq
    let hsr : FaceRefines r s.ofDual.coord := leOfHom fr
    let hs : FaceRefines (faceJoin q r) s.ofDual.coord := faceRefines_of_join hsq hsr
    refine ⟨G.incidenceFaceMap hs w, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]
    have hn := congrArg (fun f : G.incidenceAffineFace s.ofDual.coord ⟶ G.incidenceGluedScheme => f w)
      (G.incidenceFaceι_naturality hsq)
    change G.incidenceFaceι s.ofDual.coord w = G.incidenceFaceι q y
    rw [← hn]
    change G.incidenceFaceι q (G.incidenceFaceDiagram.map fq w) = G.incidenceFaceι q y
    rw [hwq]

end BPFixedPoints.Multigraph
