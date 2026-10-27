import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDiagram

/-! # Native section and degree-zero Ext differences in original face coordinates

The actual intersection is the existing face join. The native difference
retains its left-minus-right sign and both original twist restriction maps.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The existing face join is the actual intersection of the original rectangular opens. -/
theorem vertexBinaryFaceOpen_join (q r : V → Fin 3) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (faceJoin q r) =
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q ⊓
        SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r := by
  have hf (v : V) :
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (faceJoin q r v) =
        SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v) ⊓
          SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (r v) := by
    unfold faceJoin
    generalize q v = i
    generalize r v = j
    fin_cases i <;> fin_cases j <;> simp [SheafTools.binaryCoverFaceFactor, inf_comm]
  simp only [SheafTools.binaryCoverFaceOpen, hf]
  apply le_antisymm
  · exact le_inf (le_iInf fun v => (iInf_le _ v).trans inf_le_left)
      (le_iInf fun v => (iInf_le _ v).trans inf_le_right)
  · exact le_iInf fun v => le_inf
      (inf_le_left.trans (iInf_le _ v)) (inf_le_right.trans (iInf_le _ v))

/-- Every native two-open section difference has the original mixed-coordinate twist formula. -/
theorem vertexTwistSheafFaceSections_difference (a : V → ℤ) (q r : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q))
    (y : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r)) :
    vertexTwistSheafFaceSectionsEquiv R V a (faceJoin q r)
      ((vertexTwistSheaf R V a).presheaf.map (eqToHom (vertexBinaryFaceOpen_join R V q r)).op
        (SheafTools.twoOpenSectionDifference (vertexTwistAbelianSheaf R V a)
          (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
          (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r) (x,y))) =
      multiTwistFaceRestriction R (faceRefines_join_left q r) a (vertexTwistSheafFaceSectionsEquiv R V a q x) -
        multiTwistFaceRestriction R (faceRefines_join_right q r) a (vertexTwistSheafFaceSectionsEquiv R V a r y) := by
  dsimp only [vertexTwistAbelianSheaf]
  rw [SheafTools.moduleTwoOpenSectionDifference_apply, map_sub, map_sub]
  rw [← (vertexTwistSheaf R V a).presheaf.map_comp_apply,
    ← (vertexTwistSheaf R V a).presheaf.map_comp_apply]
  exact congrArg₂ (fun s t : FaceRing R (faceJoin q r) => s-t)
    (vertexTwistSheafFaceSections_restrict R V a (faceRefines_join_left q r) x)
    (vertexTwistSheafFaceSections_restrict R V a (faceRefines_join_right q r) y)

noncomputable local instance vertexFaceDifferenceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The actual degree-zero Ext Mayer--Vietoris difference has the same original coefficient formula. -/
theorem vertexTwistSheafFaceH0_difference (a : V → ℤ) (q r : V → Fin 3)
    (x : (vertexTwistAbelianSheaf R V a).H' 0 (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q))
    (y : (vertexTwistAbelianSheaf R V a).H' 0 (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r)) :
    vertexTwistSheafFaceH0LinearEquiv R V a (faceJoin q r)
      (((vertexTwistAbelianSheaf R V a).cohomologyPresheaf 0).map
        (eqToHom (vertexBinaryFaceOpen_join R V q r)).op
        ((Opens.mayerVietorisSquare
          (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
          (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r)).fromBiprod
          (vertexTwistAbelianSheaf R V a) 0 ((AddCommGrpCat.biprodIsoProd _ _).inv (x,y)))) =
      multiTwistFaceRestriction R (faceRefines_join_left q r) a (vertexTwistSheafFaceH0LinearEquiv R V a q x) -
        multiTwistFaceRestriction R (faceRefines_join_right q r) a (vertexTwistSheafFaceH0LinearEquiv R V a r y) := by
  change vertexTwistSheafFaceSectionsEquiv R V a (faceJoin q r)
    (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R V a) _
      (((vertexTwistAbelianSheaf R V a).cohomologyPresheaf 0).map _ _)) = _
  rw [SheafTools.localSheafH0Equiv_naturality, SheafTools.localSheafH0_fromBiprod]
  exact vertexTwistSheafFaceSections_difference R V a q r _ _

end BPFixedPoints.ProjectiveLine
