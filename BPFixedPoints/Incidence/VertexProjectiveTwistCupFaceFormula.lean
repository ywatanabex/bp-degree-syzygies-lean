import BPFixedPoints.Incidence.BinaryCoverCellCupDiagonalEvaluation
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCup
import BPFixedPoints.Incidence.VertexProjectiveTwistCellNative

/-! # The full original face-coordinate formula for the actual twist cup

Retain the original chart frames, all original cochain representatives,
the native geometric product, and the full original diagonal crossing.
The comparison with the tensor coefficient cup and canonical derived Ext
cup is separate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CechProduct CechCubicalCell SheafTools SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original unsigned face coefficient of the original cell cochain, extended by zero outside its degree. -/
def vertexTwistCellFaceCoefficient (a : V → ℤ) (i : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (p : V → Fin 3) : FaceRing R p :=
  vertexTwistSheafFaceSectionsEquiv R V a p
    (cellCochainValue (vertexCoordinateOpen R V) i f
      (binaryCoverFaceOpen (vertexCoordinateOpen R V) p) p le_rfl)

/-- These are exactly the original unsigned native cochain coordinates, with no extra sign. -/
theorem vertexTwistCellFaceCoefficient_native (a : V → ℤ) (i : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (p : V → Fin 3) :
    vertexTwistCellFaceCoefficient R V a i f p =
      vertexTwistCubicalCoordinates R V a (vertexTwistCellNativeEquiv R V a i f).val p := by
  by_cases hi : faceDegree p=i
  · let q : FaceIndex (V := V) i := ⟨p,by change -(faceDegree p : ℤ) = -(i : ℤ); rw [hi]⟩
    have e := vertexTwistCellNativeEquiv_apply R V a i f q
    change (vertexTwistCellNativeEquiv R V a i f).val p = _ at e
    rw [vertexTwistCellFaceCoefficient,cellCochainValue,dite_eq_left hi]
    change _ = vertexTwistSheafFaceSectionsEquiv R V a p ((vertexTwistCellNativeEquiv R V a i f).val p)
    rw [e,sectionsEquiv_cellSheafSection]
  · have hz := vertexTwistCellNativeEquiv_apply_ne R V a i f p (by omega)
    simp only [vertexTwistCellFaceCoefficient,cellCochainValue,dite_eq_right hi,map_zero,
      vertexTwistCubicalCoordinates,LinearEquiv.piCongrRight_apply,hz]

/-- Restricting the original cell representative is the original coefficient refinement and inverse frame unit. -/
theorem vertexTwistCellFaceCoefficient_restrict (a : V → ℤ) (i : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    {p s : V → Fin 3} (h : FaceRefines p s) :
    vertexTwistSheafFaceSectionsEquiv R V a s
      (cellCochainValue (vertexCoordinateOpen R V) i f
        (binaryCoverFaceOpen (vertexCoordinateOpen R V) s) p
          (vertexBinaryFaceOpen_refinement R V h)) =
      multiTwistFaceRestriction R h a (vertexTwistCellFaceCoefficient R V a i f p) := by
  by_cases hi : faceDegree p=i
  · let q : FaceIndex (V := V) i := ⟨p,by change -(faceDegree p : ℤ) = -(i : ℤ); rw [hi]⟩
    have e := cellSheafSection_cochain (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a)
      i f q (binaryCoverFaceOpen (vertexCoordinateOpen R V) s) (vertexBinaryFaceOpen_refinement R V h)
    simp only [cellCochainValue,dite_eq_left hi]
    rw [e]
    have er := vertexTwistSheafFaceSections_restrict R V a h
      (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) i f q)
    refine er.trans ?_
    congr 1
    rw [vertexTwistCellFaceCoefficient,cellCochainValue,dite_eq_left hi]
    exact congrArg (vertexTwistSheafFaceSectionsEquiv R V a p)
      (sectionsEquiv_cellSheafSection (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) i f q)
  · simp only [cellCochainValue,dite_eq_right hi,map_zero,vertexTwistCellFaceCoefficient]

/-- Every original actual cup cochain has the original full mixed-face coefficient formula. -/
theorem vertexTwistCellCupAt_face (a b : V → ℤ) (n i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b)
    (s : FaceIndex (V := V) n) :
    vertexTwistSheafFaceSectionsEquiv R V (a+b) s.val
      (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V (a+b)) n
        (vertexTwistCellCupAt R V a b n i j f g) s) =
      ∑ z : PairCellIndex (vertexCoordinateOpen R V)
          (binaryCoverFaceOpen (vertexCoordinateOpen R V) s.val) n,
        if hz : DiagonalShape s.val z.val.1 z.val.2 then
          (-1 : ℤ)^diagonalCross z.val.1 z.val.2 •
            (multiTwistFaceRestriction R hz.left_refines a (vertexTwistCellFaceCoefficient R V a i f z.val.1) *
              multiTwistFaceRestriction R hz.right_refines b (vertexTwistCellFaceCoefficient R V b j g z.val.2))
        else 0 := by
  classical
  have hc := actualCellCupAt_sections (vertexCoordinateOpen R V)
    (vertexTwistAbelianSectionPairing R V a b) n i j f g s
  refine (congrArg (vertexTwistSheafFaceSectionsEquiv R V (a+b) s.val) hc).trans ?_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : DiagonalShape s.val z.val.1 z.val.2
  · rw [ite_eq_left hz,dite_eq_left hz,map_zsmul]
    have e := vertexTwistSectionProduct_face R V a b s.val
      (cellCochainValue (vertexCoordinateOpen R V) i f
        (binaryCoverFaceOpen (vertexCoordinateOpen R V) s.val) z.val.1 z.property.1)
      (cellCochainValue (vertexCoordinateOpen R V) j g
        (binaryCoverFaceOpen (vertexCoordinateOpen R V) s.val) z.val.2 z.property.2.1)
    refine congrArg (fun x : FaceRing R s.val => (-1 : ℤ)^diagonalCross z.val.1 z.val.2 • x) (e.trans ?_)
    rw [vertexTwistCellFaceCoefficient_restrict R V a i f hz.left_refines,
      vertexTwistCellFaceCoefficient_restrict R V b j g hz.right_refines]
  · simp only [ite_eq_right hz,dite_eq_right hz,zero_smul,map_zero]

end
end BPFixedPoints.ProjectiveLine
