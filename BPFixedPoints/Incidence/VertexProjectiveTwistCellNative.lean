import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalComponent
import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalDegree
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology

/-! # Original cell Hom cochains are the previously specified native cochains

The degreewise original face-section comparison is extended by zero only
outside its original overlap degree. It retains the actual original face
sections and intertwines the previously specified full native differential.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct CechCubicalCell SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original negative cell-degree convention is exactly the original positive overlap degree. -/
theorem faceIndex_degree {n : ℕ} (q : FaceIndex (V := V) n) : (faceDegree q.val : ℤ) = n := by
  have h := q.property
  dsimp only [cellDegree] at h
  omega

/-- The original face equipped with its original overlap degree. -/
def faceIndexOfDegree (n : ℕ) (q : V → Fin 3) (h : (faceDegree q : ℤ) = n) :
    FaceIndex (V := V) n := ⟨q,congrArg (fun z : ℤ => -z) h⟩

/-- Native degreewise cochains are exactly their original degree-indexed face sections. -/
noncomputable def vertexTwistDegreeSectionsEquiv (a : V → ℤ) (n : ℕ) :
    vertexTwistCubicalDegree R V a (n : ℤ) ≃ₗ[R]
      ((q : FaceIndex (V := V) n) → vertexTwistCubicalFace R V a q.val) where
  toFun x q := x.val q.val
  invFun s := ⟨fun q => if h : (faceDegree q : ℤ) = n then
    s (faceIndexOfDegree V n q h) else 0,by
      intro q hq
      exact dite_eq_right hq⟩
  left_inv x := by
    apply Subtype.ext
    funext q
    change (if _h : (faceDegree q : ℤ) = n then x.val q else 0) = x.val q
    by_cases hq : (faceDegree q : ℤ) = n
    · exact dite_eq_left hq
    · exact (dite_eq_right hq).trans (x.property q hq).symm
  right_inv s := by
    funext q
    exact dite_eq_left (faceIndex_degree V q)
  map_add' x y := by funext q; rfl
  map_smul' r x := by funext q; rfl

/-- Original cell Hom cochains and original native homogeneous cochains have the specified actual-section equivalence. -/
noncomputable def vertexTwistCellNativeEquiv (a : V → ℤ) (n : ℕ) :
    (sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a) ≃+
      vertexTwistCubicalDegree R V a (n : ℤ) :=
  (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) n).trans
    (vertexTwistDegreeSectionsEquiv R V a n).symm.toAddEquiv

/-- Every actual face in the original degree retains precisely its originally specified section coordinate. -/
theorem vertexTwistCellNativeEquiv_apply (a : V → ℤ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a)
    (q : FaceIndex (V := V) n) :
    (vertexTwistCellNativeEquiv R V a n f).val q.val =
      sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) n f q := by
  exact dite_eq_left (faceIndex_degree V q)

/-- The original homogeneous extension has no components outside its original overlap degree. -/
theorem vertexTwistCellNativeEquiv_apply_ne (a : V → ℤ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a)
    (q : V → Fin 3) (hq : (faceDegree q : ℤ) ≠ n) :
    (vertexTwistCellNativeEquiv R V a n f).val q = 0 :=
  (vertexTwistCellNativeEquiv R V a n f).property q hq

/-- The original Hom differential is exactly the independently defined full native section differential. -/
theorem vertexTwistCellNativeEquiv_d (d : V → ℕ) (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) :
    (vertexTwistCellNativeEquiv R V _ (n+1) ((sheafComplex (vertexCoordinateOpen R V)).d (n+1) n ≫ f)).val =
      vertexTwistCubicalD R V _ (vertexTwistCellNativeEquiv R V _ n f).val := by
  funext p
  by_cases hp : (faceDegree p : ℤ) = (n+1 : ℕ)
  · let q : FaceIndex (V := V) (n+1) := ⟨p,by dsimp only [cellDegree]; omega⟩
    change (vertexTwistCellNativeEquiv R V _ (n+1) _).val q.val = _
    rw [vertexTwistCellNativeEquiv_apply,sectionsEquiv_boundary,vertexTwistCubicalD_component]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : p v = 2
    · rw [dite_eq_left hv,dite_eq_left hv]
      have h₀ := vertexTwistCellNativeEquiv_apply R V _ n f (endpoint q v hv 0)
      have h₁ := vertexTwistCellNativeEquiv_apply R V _ n f (endpoint q v hv 1)
      change (vertexTwistCellNativeEquiv R V _ n f).val (Function.update p v 0) = _ at h₀
      change (vertexTwistCellNativeEquiv R V _ n f).val (Function.update p v 1) = _ at h₁
      rw [h₀,h₁]
      let s : vertexTwistCubicalFace R V (fun v => -(d v : ℤ)) p :=
        vertexTwistCubicalRestriction R V _
          (endpoint_refines (faceRefines_refl p) v hv (0 : Fin 3))
          (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V _) n f (endpoint q v hv 0)) -
        vertexTwistCubicalRestriction R V _
          (endpoint_refines (faceRefines_refl p) v hv (1 : Fin 3))
          (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V _) n f (endpoint q v hv 1))
      change (-1 : ℤ)^faceBoundaryPrefix p v • s = (-1 : R)^faceBoundaryPrefix p v • s
      rw [← Int.cast_smul_eq_zsmul (R := R)]
      simp only [Int.cast_pow,Int.cast_neg,Int.cast_one]
    · rw [dite_eq_right hv,dite_eq_right hv]
  · rw [vertexTwistCellNativeEquiv_apply_ne R V _ (n+1) _ p hp]
    symm
    apply vertexTwistCubicalD_degree R V d n _ (vertexTwistCellNativeEquiv R V _ n f).property p
    simpa only [Nat.cast_add,Nat.cast_one] using hp

end BPFixedPoints.ProjectiveLine
