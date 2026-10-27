import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDifferences
import BPFixedPoints.Incidence.IncidenceKernelBundleTransitions
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # The face cover of `(ℙ¹)^V` is locally directed

The faces `q : V → Fin 3` (the standard charts and all their intersections) give an open cover
`vertexFaceCover R V` of `vertexScheme R V` by the spectra of the face rings `FaceRing R q`, through
the existing open immersions `vertexFaceι R V q`, indexed by `(FaceIndex V)ᵒᵈ`. With the
transition maps `Spec (faceRefinementMap R h)` it is a locally directed open cover in Mathlib's
sense (`vertexFaceCover_locallyDirected`): two faces meet exactly in the face of their join
(`vertexBinaryFaceOpen_join`), and a point of the pullback of two face charts is determined by its
image. Consequently `(ℙ¹)^V` is the colimit of its faces (`vertexFaceCover_isColimit`), morphisms
out of `(ℙ¹)^V` can be glued face by face (`Scheme.OpenCover.glueMorphismsOfLocallyDirected`),
and Mathlib's relative gluing over a locally directed cover applies; both are used in
`IncidenceRelativeSpec.lean`.

The refinement maps of a face to itself are the identity (`refinementExponent_refl`,
`faceRefinementMap_refl`).

Not proved here: anything specific to the incidence scheme; this file only concerns `(ℙ¹)^V`.
-/

namespace BPFixedPoints.CechProduct

set_option backward.isDefEq.respectTransparency false

/-- The exponent map of the trivial refinement is the identity. -/
theorem refinementExponent_refl {V : Type*} (q : V → Fin 3) (m : FaceMonoid q) :
    refinementExponent (faceRefines_refl q) m = m := by
  apply faceToInt_injective
  funext v
  rw [faceToInt_refinement]
  by_cases h : q v = 1 <;> simp [h]

/-- The ring map of the trivial refinement is the identity. -/
theorem faceRefinementMap_refl (R : Type*) [CommRing R] {V : Type*} (q : V → Fin 3) :
    faceRefinementMap R (faceRefines_refl q) = AlgHom.id R (FaceRing R q) := by
  apply AlgHom.ext
  intro x
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c => rw [faceRefinementMap_single, refinementExponent_refl]; rfl

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- **The face cover of `(ℙ¹)^V`.** The open cover of `vertexScheme R V` by the spectra of all
face rings `FaceRing R q` (charts and all their intersections), indexed by the faces with the
refinement order reversed, so that arrows go from smaller opens to larger ones. -/
noncomputable def vertexFaceCover : (vertexScheme R V).OpenCover where
  I₀ := (FaceIndex V)ᵒᵈ
  X q := Spec (CommRingCat.of (FaceRing R q.ofDual.coord))
  f q := vertexFaceι R V q.ofDual.coord
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨σ, y, hy⟩ := vertexChart_covers R V x
      refine ⟨OrderDual.toDual ⟨chartFace (fun v => decide (σ v = 1))⟩, ?_⟩
      have hσ : vertexBooleanPivot V (fun v => decide (σ v = 1)) = σ := by
        have hb : ∀ i : Fin 2, (if decide (i = 1) = true then (1 : Fin 2) else 0) = i := by
          decide
        funext v
        exact hb (σ v)
      have hx : x ∈ (vertexFaceι R V (chartFace (fun v => decide (σ v = 1)))).opensRange := by
        rw [vertexFaceι_chart_opensRange, hσ]
        exact ⟨y, hy⟩
      exact hx
    · intro q
      change IsOpenImmersion (vertexFaceι R V q.ofDual.coord)
      infer_instance

/-- The refinement order on the faces of the face cover. -/
instance vertexFaceCover_preorder : Preorder (vertexFaceCover R V).I₀ :=
  inferInstanceAs (Preorder (FaceIndex V)ᵒᵈ)

/-- The face cover is locally directed: two faces meet exactly in their join. -/
noncomputable instance vertexFaceCover_locallyDirected : (vertexFaceCover R V).LocallyDirected where
  trans {i j} f := Spec.map (CommRingCat.ofHom (faceRefinementMap R (leOfHom f)).toRingHom)
  trans_id i := by
    change Spec.map (CommRingCat.ofHom
      (faceRefinementMap R (faceRefines_refl i.ofDual.coord)).toRingHom) = 𝟙 _
    rw [faceRefinementMap_refl]
    exact Spec.map_id _
  trans_comp {i j k} f g := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (Multigraph.overlapFaceRefinementMap_trans R (leOfHom g) (leOfHom f) x).symm
  w {i j} f := vertexFaceι_refinement R V (leOfHom f)
  directed {i j} x := by
    let k : (vertexFaceCover R V).I₀ :=
      OrderDual.toDual ⟨faceJoin i.ofDual.coord j.ofDual.coord⟩
    have hki : k ⟶ i := homOfLE (faceRefines_join_left i.ofDual.coord j.ofDual.coord)
    have hkj : k ⟶ j := homOfLE (faceRefines_join_right i.ofDual.coord j.ofDual.coord)
    refine ⟨k, hki, hkj, ?_⟩
    let z := (pullback.fst (vertexFaceι R V i.ofDual.coord) (vertexFaceι R V j.ofDual.coord) ≫
      vertexFaceι R V i.ofDual.coord) x
    have hz : z ∈ (vertexFaceι R V (faceJoin i.ofDual.coord j.ofDual.coord)).opensRange := by
      rw [vertexFaceι_opensRange, vertexBinaryFaceOpen_join, ← vertexFaceι_opensRange,
        ← vertexFaceι_opensRange]
      refine ⟨⟨_, rfl⟩, ?_⟩
      change (pullback.fst (vertexFaceι R V i.ofDual.coord) (vertexFaceι R V j.ofDual.coord) ≫
        vertexFaceι R V i.ofDual.coord) x ∈ Set.range (vertexFaceι R V j.ofDual.coord)
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := hz
    refine ⟨y, ?_⟩
    apply (pullback.fst ((vertexFaceCover R V).f i) ((vertexFaceCover R V).f j) ≫
      (vertexFaceCover R V).f i).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    have h2 := vertexFaceι_refinement R V (faceRefines_join_left i.ofDual.coord j.ofDual.coord)
    exact (congrArg (fun m : Spec (CommRingCat.of (FaceRing R
      (faceJoin i.ofDual.coord j.ofDual.coord))) ⟶ vertexScheme R V => m y) h2).trans hy
  property_trans f := vertexFaceRefinement_isOpenImmersion R V (leOfHom f)

/-- The transition maps of the face cover are the spectra of the face refinement maps. -/
theorem vertexFaceCover_trans {i j : (vertexFaceCover R V).I₀} (f : i ⟶ j) :
    (vertexFaceCover R V).trans f =
      Spec.map (CommRingCat.ofHom (faceRefinementMap R (leOfHom f)).toRingHom) :=
  rfl

/-- **`(ℙ¹)^V` is the colimit of its faces**, along the face refinement maps. -/
noncomputable def vertexFaceCover_isColimit :
    IsColimit (vertexFaceCover R V).coconeOfLocallyDirected :=
  Scheme.OpenCover.isColimitCoconeOfLocallyDirected (vertexFaceCover R V)

end BPFixedPoints.ProjectiveLine
