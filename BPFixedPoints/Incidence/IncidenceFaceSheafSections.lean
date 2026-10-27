import BPFixedPoints.Incidence.SheafLocalCohomologyZero
import BPFixedPoints.Incidence.IncidenceGluedIntersections

/-! # Actual sheaf sections on every incidence face and their restrictions

All higher face opens are affine. Their section rings are the original quotient
rings, and every actual sheaf restriction is the original refinement map. This
identifies the entire face diagram, not only Boolean charts and the common torus.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory SheafTools CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The genuine open associated with any polynomial/Laurent incidence face. -/
noncomputable def incidenceFaceOpen (q : V → Fin 3) : G.incidenceGluedScheme.Opens :=
  (G.incidenceFaceι q).opensRange

theorem incidenceFaceOpen_isAffine (q : V → Fin 3) : IsAffineOpen (G.incidenceFaceOpen q) := by
  letI : IsAffine (G.incidenceAffineFace q) := by
    unfold incidenceAffineFace
    infer_instance
  exact isAffineOpen_opensRange (G.incidenceFaceι q)

/-- Every refinement is the corresponding actual inclusion of face opens. -/
theorem incidenceFaceOpen_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceFaceOpen r ≤ G.incidenceFaceOpen q := by
  rintro x ⟨y, rfl⟩
  refine ⟨G.incidenceFaceMap h y, ?_⟩
  rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]

/-- Genuine intersection of arbitrary higher face opens. -/
theorem incidenceFaceOpen_join (q r : V → Fin 3) :
    G.incidenceFaceOpen (faceJoin q r) = G.incidenceFaceOpen q ⊓ G.incidenceFaceOpen r := by
  apply TopologicalSpace.Opens.ext
  exact G.incidenceFaceι_join_range q r

/-- Coordinate identification from actual affine-open structure-sheaf maps. -/
noncomputable def incidenceFaceSectionsEquiv (q : V → Fin 3) :
    Γ(G.incidenceGluedScheme, G.incidenceFaceOpen q) ≃+* G.IncFaceRing q :=
  (affineOpenSectionsIso (CommRingCat.of (G.IncFaceRing q))
    (G.incidenceFaceι q)).commRingCatIsoToRingEquiv

/-- The whole actual face-section diagram agrees with the original quotient-ring diagram. -/
theorem incidenceFaceSections_restrict {q r : V → Fin 3} (h : FaceRefines q r)
    (s : Γ(G.incidenceGluedScheme, G.incidenceFaceOpen q)) :
    G.incidenceFaceSectionsEquiv r
      (sectionRestrict G.incidenceGluedScheme.sheaf (G.incidenceFaceOpen_refinement h) s) =
        G.incFaceRefinement h (G.incidenceFaceSectionsEquiv q s) := by
  have hn := affineOpenSectionsIso_naturality
    (CommRingCat.ofHom (R := G.IncFaceRing q) (S := G.IncFaceRing r) (G.incFaceRefinement h).toRingHom)
    (G.incidenceFaceι q) (G.incidenceFaceι r)
    (G.incidenceFaceι_naturality h) (G.incidenceFaceOpen_refinement h)
  exact congrArg (fun f => f.hom s) hn

/-- Degree-zero genuine local Ext cohomology on every higher face has the
original quotient ring as its additive group. -/
noncomputable def incidenceFaceLocalH0Equiv (q : V → Fin 3) :
    structureSheafLocalCohomology G.incidenceGluedScheme 0 (G.incidenceFaceOpen q) ≃+
      G.IncFaceRing q :=
  (localSheafH0Equiv (structureAbelianSheaf G.incidenceGluedScheme) (G.incidenceFaceOpen q)).trans
    (G.incidenceFaceSectionsEquiv q).toAddEquiv

end BPFixedPoints.Multigraph
