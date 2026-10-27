import BPFixedPoints.Incidence.VertexProjectiveTwistCupCoefficientFaces

/-! # The original geometric cell cup is the original signed tensor coefficient cup

Compare all original Hom representatives, retaining the original degree
parity in the existing native-to-coefficient equivalence. The target twist
is changed only by the elementary equality of the two integer sums.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct CechCubicalCell SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Adding the two original negative twists is the negative of their original sum. -/
theorem vertexTwistNegativeAdd (d e : V → ℕ) :
    ((fun v => -(d v : ℤ))+(fun v => -(e v : ℤ))) = (fun v => -((d+e) v : ℤ)) := by
  ext v
  simp only [Pi.add_apply,Nat.cast_add]
  omega

/-- The original actual cup, with only its target integer twist sum identified by equality. -/
def vertexTwistNegativeCellCup (d e : V → ℕ) (i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)))
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) :
    (vertexTwistCupSource R V).X (i+j) ⟶ vertexTwistAbelianSheaf R V (fun v => -((d+e) v : ℤ)) :=
  vertexTwistCellCup R V _ _ i j f g ≫
    eqToHom (congrArg (vertexTwistAbelianSheaf R V) (vertexTwistNegativeAdd V d e))

/-- Every original face coefficient is zero outside its original cell cochain degree. -/
theorem vertexTwistCellFaceCoefficient_zero_degree (a : V → ℤ) (n : ℕ)
    (f : (vertexTwistCupSource R V).X n ⟶ vertexTwistAbelianSheaf R V a)
    (s : V → Fin 3) (hs : faceDegree s≠n) :
    vertexTwistCellFaceCoefficient R V a n f s=0 := by
  rw [vertexTwistCellFaceCoefficient,cellCochainValue,dite_eq_right hs,map_zero]

/-- On every original Hom representative, the actual geometric cup is precisely the existing signed tensor cup. -/
theorem vertexTwistNegativeCellCup_coefficient (d e : V → ℕ) (i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)))
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V (fun v => -(e v : ℤ))) :
    (vertexTwistCellCoefficientEquiv R V (d+e) (i+j) (vertexTwistNegativeCellCup R V d e i j f g)).val =
      chainCup R d e (vertexTwistCellCoefficientEquiv R V d i f).val
        (vertexTwistCellCoefficientEquiv R V e j g).val := by
  apply (faceEquiv R).injective
  funext s
  rw [vertexTwistCellCoefficientEquiv_face]
  unfold vertexTwistNegativeCellCup
  rw [vertexTwistCellFaceCoefficient_eqToHom R V _ _ (vertexTwistNegativeAdd V d e)]
  by_cases hs : faceDegree s=i+j
  · let q : FaceIndex (V := V) (i+j) := ⟨s,by change -(faceDegree s : ℤ) = -((i+j : ℕ) : ℤ); rw [hs]⟩
    have hf : faceEquiv R (vertexTwistCellCoefficientEquiv R V d i f).val =
        fun p => (-1 : R)^faceDegree p • vertexTwistCellFaceCoefficient R V (fun v => -(d v : ℤ)) i f p := by
      funext p
      exact vertexTwistCellCoefficientEquiv_face R V d i f p
    have hg : faceEquiv R (vertexTwistCellCoefficientEquiv R V e j g).val =
        fun p => (-1 : R)^faceDegree p • vertexTwistCellFaceCoefficient R V (fun v => -(e v : ℤ)) j g p := by
      funext p
      exact vertexTwistCellCoefficientEquiv_face R V e j g p
    rw [faceEquiv_chainCup_full,hf,hg,faceCupAt_parity]
    congr 1
    exact vertexTwistCellCup_coefficient_face R V d e (i+j) i j f g q
  · rw [vertexTwistCellFaceCoefficient_zero_degree R V _ (i+j) _ s hs,smul_zero]
    have hc := chainCup_degree R d e (i : ℤ) (j : ℤ)
      (vertexTwistCellCoefficientEquiv R V d i f).property
      (vertexTwistCellCoefficientEquiv R V e j g).property
    exact (faceEquiv_eq_zero_of_degree R hc s (by omega)).symm

end
end BPFixedPoints.ProjectiveLine
