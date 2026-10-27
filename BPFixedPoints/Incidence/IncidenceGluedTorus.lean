import BPFixedPoints.Incidence.IncidenceGluedAtlas
import BPFixedPoints.Incidence.IncidenceLaurentFace

/-! # The original common torus in the genuine incidence atlas

The embeddings into the original Boolean charts agree after gluing. Their
compatibility is proved from the existing coefficient and vertex restriction
maps, through the natural all-Laurent face equivalence.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Original common torus embedding into the actually constructed incidence scheme. -/
noncomputable def incidenceTorusι : G.incidenceAffineTorus ⟶ G.incidenceGluedScheme :=
  Spec.map (G.incLaurentFaceEquiv.toRingEquiv.toCommRingCatIso.hom) ≫
    G.incidenceFaceι (fun _ => 2)

instance incidenceTorusι_isOpenImmersion : IsOpenImmersion G.incidenceTorusι := by
  unfold incidenceTorusι
  infer_instance

/-- The common torus map factors through each original chart with the prescribed
original coefficient-ring map. -/
theorem incidenceTorusι_factor (σ : V → Bool) :
    G.incidenceAffineTorusToChart σ ≫ G.incidenceChartι σ = G.incidenceTorusι := by
  let h : FaceRefines (chartFace σ) (fun _ => 2) := fun _ => Or.inr rfl
  have he : (G.incFaceChartEquiv σ).toRingEquiv.toCommRingCatIso.hom ≫
      CommRingCat.ofHom (G.incChartMap σ).toRingHom =
        CommRingCat.ofHom (R := G.IncFaceRing (chartFace σ))
          (S := G.IncFaceRing (fun _ => 2)) (G.incFaceRefinement h).toRingHom ≫
          CommRingCat.ofHom (R := G.IncFaceRing (fun _ => 2)) (S := G.IncTorusRing)
            (G.incFaceToTorus (fun _ => 2)).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change G.incChartMap σ (G.incFaceChartEquiv σ x) =
      G.incFaceToTorus (fun _ => 2) (G.incFaceRefinement h x)
    rw [G.incFaceToTorus_refinement, G.incFaceToTorus_chartFace_apply]
  change Spec.map (CommRingCat.ofHom (G.incChartMap σ).toRingHom) ≫
    (Spec.map (G.incFaceChartEquiv σ).toRingEquiv.toCommRingCatIso.hom ≫
      G.incidenceFaceι (chartFace σ)) = _
  rw [← Category.assoc, ← Spec.map_comp, he, Spec.map_comp, Category.assoc]
  change Spec.map (G.incLaurentFaceEquiv.toRingEquiv.toCommRingCatIso.hom) ≫
    (G.incidenceFaceMap h ≫ G.incidenceFaceι (chartFace σ)) = G.incidenceTorusι
  rw [G.incidenceFaceι_naturality]
  rfl

/-- The actual common torus open in the constructed incidence scheme. -/
noncomputable def incidenceTorusOpen : G.incidenceGluedScheme.Opens :=
  G.incidenceTorusι.opensRange

instance incidenceTorusOpen_nonempty : Nonempty G.incidenceTorusOpen := by
  obtain ⟨x⟩ := (inferInstance : Nonempty G.incidenceAffineTorus)
  exact ⟨⟨G.incidenceTorusι x, x, rfl⟩⟩

/-- The actual torus open lies in every original chart open. -/
theorem incidenceTorusOpen_le_chart (σ : V → Bool) :
    G.incidenceTorusOpen ≤ G.incidenceChartOpen σ := by
  rintro x ⟨y, rfl⟩
  refine ⟨G.incidenceAffineTorusToChart σ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, G.incidenceTorusι_factor]

end BPFixedPoints.Multigraph
