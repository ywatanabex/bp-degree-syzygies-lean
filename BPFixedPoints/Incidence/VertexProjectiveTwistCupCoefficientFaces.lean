import BPFixedPoints.Incidence.BinaryCoverCoefficientCup
import BPFixedPoints.Incidence.VertexProjectiveTwistCupFaceFormula
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCoefficients
import BPFixedPoints.Incidence.CechCupDegree

/-! # Original geometric cup and coefficient cup on every original output face -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct CechCubicalCell SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Coefficients in the original degree evaluate the original specified section coordinate. -/
theorem vertexTwistCellFaceCoefficient_sections (a : V → ℤ) (n : ℕ)
    (f : (vertexTwistCupSource R V).X n ⟶ vertexTwistAbelianSheaf R V a)
    (s : FaceIndex (V := V) n) :
    vertexTwistCellFaceCoefficient R V a n f s.val =
      vertexTwistSheafFaceSectionsEquiv R V a s.val
        (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) n f s) := by
  have hs : faceDegree s.val=n := by have h := s.property; change -(faceDegree s.val : ℤ) = -(n : ℤ) at h; omega
  rw [vertexTwistCellFaceCoefficient,cellCochainValue,dite_eq_left hs,sectionsEquiv_cellSheafSection]

/-- Equality transport of the original target twist leaves its original face coefficients unchanged. -/
theorem vertexTwistCellFaceCoefficient_eqToHom (a b : V → ℤ) (h : a=b) (n : ℕ)
    (f : (vertexTwistCupSource R V).X n ⟶ vertexTwistAbelianSheaf R V a) (s : V → Fin 3) :
    vertexTwistCellFaceCoefficient R V b n
      (f ≫ eqToHom (congrArg (vertexTwistAbelianSheaf R V) h)) s =
        vertexTwistCellFaceCoefficient R V a n f s := by
  subst b
  simp only [eqToHom_refl,Category.comp_id]

/-- The existing signed coefficient comparison retains its original degree parity on every face. -/
theorem vertexTwistCellCoefficientEquiv_face (d : V → ℕ) (n : ℕ)
    (f : (vertexTwistCupSource R V).X n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)))
    (s : V → Fin 3) :
    faceEquiv R (vertexTwistCellCoefficientEquiv R V d n f).val s =
      (-1 : R)^faceDegree s • vertexTwistCellFaceCoefficient R V (fun v => -(d v : ℤ)) n f s := by
  change faceEquiv R (vertexTwistCubicalChainEquiv R V d (vertexTwistCellNativeEquiv R V _ n f).val) s = _
  rw [vertexTwistCubicalChainEquiv_face,vertexTwistCellFaceCoefficient_native]
  rfl

/-- The original actual cup has exactly the independently specified coefficient cup formula in its original output degree. -/
theorem vertexTwistCellCup_coefficient_face (d e : V → ℕ) (n i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)))
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ)))
    (s : FaceIndex (V := V) n) :
    vertexTwistCellFaceCoefficient R V ((fun v => -(d v : ℤ))+(fun v => -(e v : ℤ))) n
      (vertexTwistCellCupAt R V _ _ n i j f g) s.val =
        faceCupAt R d e s.val
          (vertexTwistCellFaceCoefficient R V (fun v => -(d v : ℤ)) i f)
          (vertexTwistCellFaceCoefficient R V (fun v => -(e v : ℤ)) j g) := by
  rw [vertexTwistCellFaceCoefficient_sections,vertexTwistCellCupAt_face,faceCupAt_availablePairs (vertexCoordinateOpen R V)]
  apply Finset.sum_congr rfl
  intro z _
  exact (faceCupTerm_apply R d e s.val z.val.1 z.val.2 _ _).symm

end
end BPFixedPoints.ProjectiveLine
