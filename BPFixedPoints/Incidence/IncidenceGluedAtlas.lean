import BPFixedPoints.Incidence.IncidenceFaceGluing
import BPFixedPoints.Incidence.KoszulFaceChartTorus

/-! # Original Boolean incidence charts cover the genuinely glued scheme

Every face lies in one of its parent Boolean charts. Thus the original charts,
not just the larger family of mixed polynomial/Laurent faces, form an open cover.
-/

namespace BPFixedPoints.CechProduct

/-- Choose the left chart at an overlap coordinate and retain each other orientation. -/
theorem chartFace_refines_face {V : Type*} (q : V → Fin 3) :
    FaceRefines (chartFace (faceOrientation q)) q := by
  intro v
  have h := (q v).isLt
  simp only [chartFace, faceOrientation]
  by_cases hq : q v = 1
  · simp [hq]
  · by_cases hz : q v = 0
    · simp [hz]
    · exact Or.inr (by omega)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The existing original chart spectrum maps to its quotient-face presentation. -/
noncomputable def incidenceChartFaceIso (σ : V → Bool) :
    G.incidenceAffineChart σ ≅ G.incidenceAffineFace (chartFace σ) :=
  { hom := Spec.map (G.incFaceChartEquiv σ).toRingEquiv.toCommRingCatIso.hom
    inv := Spec.map (G.incFaceChartEquiv σ).toRingEquiv.toCommRingCatIso.inv
    hom_inv_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]; rfl
    inv_hom_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]; rfl }

/-- Actual original-chart embedding into the glued incidence scheme. -/
noncomputable def incidenceChartι (σ : V → Bool) :
    G.incidenceAffineChart σ ⟶ G.incidenceGluedScheme :=
  (G.incidenceChartFaceIso σ).hom ≫ G.incidenceFaceι (chartFace σ)

instance incidenceChartι_isOpenImmersion (σ : V → Bool) :
    IsOpenImmersion (G.incidenceChartι σ) := by
  unfold incidenceChartι
  infer_instance

/-- The original Boolean charts cover every point of the glued scheme. -/
theorem incidenceChartι_jointly_surjective (x : G.incidenceGluedScheme) :
    ∃ (σ : V → Bool) (y : G.incidenceAffineChart σ), G.incidenceChartι σ y = x := by
  obtain ⟨q, y, rfl⟩ := G.incidenceFaceι_jointly_surjective x
  let σ := faceOrientation q
  let h := chartFace_refines_face q
  refine ⟨σ, (G.incidenceChartFaceIso σ).inv (G.incidenceFaceMap h y), ?_⟩
  change ((G.incidenceChartFaceIso σ).hom ≫ G.incidenceFaceι (chartFace σ))
    ((G.incidenceChartFaceIso σ).inv (G.incidenceFaceMap h y)) = _
  rw [Scheme.Hom.comp_apply]
  have hi := congrArg
    (fun f : G.incidenceAffineFace (chartFace σ) ⟶ G.incidenceAffineFace (chartFace σ) =>
      f (G.incidenceFaceMap h y)) (G.incidenceChartFaceIso σ).inv_hom_id
  simp only [Scheme.Hom.comp_apply] at hi
  rw [hi]
  change G.incidenceFaceι (chartFace σ) (G.incidenceFaceMap h y) = _
  rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]

/-- The original Boolean chart opens in the actually constructed incidence scheme. -/
noncomputable def incidenceChartOpen (σ : V → Bool) : G.incidenceGluedScheme.Opens :=
  (G.incidenceChartι σ).opensRange

/-- A proof of the actual atlas cover condition used by the global-section comparison. -/
theorem incidenceChartOpen_cover : (⊤ : G.incidenceGluedScheme.Opens) ≤ iSup G.incidenceChartOpen := by
  intro x _
  obtain ⟨σ, y, hy⟩ := G.incidenceChartι_jointly_surjective x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨σ, y, hy⟩

end BPFixedPoints.Multigraph
