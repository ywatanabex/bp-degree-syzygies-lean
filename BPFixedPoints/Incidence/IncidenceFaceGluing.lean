import BPFixedPoints.Incidence.IncidenceFaceIntersection

/-! # Gluing the original incidence faces along their genuine overlaps

The full face diagram is locally directed because its higher faces realize the
actual intersections of localization opens. Mathlib therefore glues it to a
scheme with the original faces as an open cover.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The actual face diagram satisfies the geometric intersection condition
required for scheme gluing. -/
instance incidenceFaceDiagram_isLocallyDirected :
    (G.incidenceFaceDiagram ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj he
  let hq : FaceRefines k.ofDual.coord i.ofDual.coord := leOfHom fi
  let hr : FaceRefines k.ofDual.coord j.ofDual.coord := leOfHom fj
  let s : (FaceIndex V)ᵒᵈ := OrderDual.toDual ⟨faceJoin i.ofDual.coord j.ofDual.coord⟩
  let fsi : s ⟶ i := homOfLE (faceRefines_join_left _ _)
  let fsj : s ⟶ j := homOfLE (faceRefines_join_right _ _)
  have hx : G.incidenceFaceMap hq xi ∈
      Set.range (G.incidenceFaceMap (faceRefines_join hq hr)) := by
    rw [G.incidenceFaceMap_join_range hq hr]
    exact ⟨⟨xi, rfl⟩, ⟨xj, he.symm⟩⟩
  obtain ⟨x, hx⟩ := hx
  refine ⟨s, fsi, fsj, x, ?_, ?_⟩
  · apply (G.incidenceFaceMap hq).isOpenEmbedding.injective
    change (G.incidenceFaceDiagram.map fi) (G.incidenceFaceDiagram.map fsi x) = _
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    exact hx
  · apply (G.incidenceFaceMap hr).isOpenEmbedding.injective
    change (G.incidenceFaceDiagram.map fj) (G.incidenceFaceDiagram.map fsj x) = _
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    exact hx.trans he

/-- The incidence scheme obtained from the original quotient faces and their
full localization overlaps. -/
noncomputable def incidenceGluedScheme : Scheme := colimit G.incidenceFaceDiagram

/-- Actual open cover of the glued scheme by the spectra of incidence face rings. -/
noncomputable def incidenceFaceOpenCover : G.incidenceGluedScheme.OpenCover :=
  Scheme.IsLocallyDirected.openCover G.incidenceFaceDiagram

/-- Every original incidence face maps openly into the glued incidence scheme. -/
noncomputable def incidenceFaceι (q : V → Fin 3) :
    G.incidenceAffineFace q ⟶ G.incidenceGluedScheme :=
  colimit.ι G.incidenceFaceDiagram (OrderDual.toDual ⟨q⟩)

instance incidenceFaceι_isOpenImmersion (q : V → Fin 3) :
    IsOpenImmersion (G.incidenceFaceι q) := by
  unfold incidenceFaceι
  infer_instance

/-- The glued scheme genuinely glues the prescribed quotient restriction maps. -/
theorem incidenceFaceι_naturality {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceFaceMap h ≫ G.incidenceFaceι q = G.incidenceFaceι r :=
  colimit.w G.incidenceFaceDiagram
    (show OrderDual.toDual (FaceIndex.mk r) ⟶ OrderDual.toDual (FaceIndex.mk q) from homOfLE h)

/-- The original face spectra jointly cover every point, including boundary points. -/
theorem incidenceFaceι_jointly_surjective (x : G.incidenceGluedScheme) :
    ∃ (q : V → Fin 3) (y : G.incidenceAffineFace q), G.incidenceFaceι q y = x := by
  obtain ⟨q, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective G.incidenceFaceDiagram x
  exact ⟨q.ofDual.coord, y, hy⟩

instance incidenceGluedScheme_isReduced : IsReduced G.incidenceGluedScheme := by
  haveI : ∀ i, IsReduced (G.incidenceFaceOpenCover.X i) := fun i => by
    change IsReduced (G.incidenceAffineFace i.ofDual.coord)
    infer_instance
  exact IsReduced.of_openCover G.incidenceGluedScheme G.incidenceFaceOpenCover

/-- The common Laurent face is dense in the glued scheme, with density proved
using every actual face open rather than assumed as atlas data. -/
theorem incidenceLaurentFace_denseRange :
    DenseRange (G.incidenceFaceι (fun _ => 2)) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUn
  obtain ⟨x, hx⟩ := hUn
  obtain ⟨q, y, rfl⟩ := G.incidenceFaceι_jointly_surjective x
  let ht : FaceRefines q (fun _ => 2) := fun _ => Or.inr rfl
  have hpre : IsOpen ((G.incidenceFaceι q) ⁻¹' U) :=
    hU.preimage (G.incidenceFaceι q).continuous
  obtain ⟨z, hz, w, hw⟩ := nonempty_preirreducible_inter hpre
    (G.incidenceFaceMap ht).isOpenEmbedding.isOpen_range ⟨y, hx⟩
    (Set.range_nonempty (G.incidenceFaceMap ht))
  refine ⟨G.incidenceFaceι (fun _ => 2) w, ?_, ⟨w, rfl⟩⟩
  have hn := congrArg (fun f : G.incidenceAffineFace (fun _ => 2) ⟶ G.incidenceGluedScheme => f w)
    (G.incidenceFaceι_naturality ht)
  rw [← hn]
  change G.incidenceFaceι q (G.incidenceFaceMap ht w) ∈ U
  rw [hw]
  exact hz

instance incidenceGluedScheme_isIntegral : IsIntegral G.incidenceGluedScheme := by
  have hi := (IrreducibleSpace.isIrreducible_univ
    (G.incidenceAffineFace (fun _ => 2))).image (G.incidenceFaceι (fun _ => 2))
      (G.incidenceFaceι (fun _ => 2)).continuous.continuousOn
  rw [Set.image_univ] at hi
  have hir : IrreducibleSpace G.incidenceGluedScheme :=
    (irreducibleSpace_def _).mpr (by
      simpa only [G.incidenceLaurentFace_denseRange.closure_range, Set.top_eq_univ] using hi.closure)
  exact (isIntegral_iff_irreducibleSpace_and_isReduced G.incidenceGluedScheme).mpr
    ⟨hir, inferInstance⟩

end BPFixedPoints.Multigraph
