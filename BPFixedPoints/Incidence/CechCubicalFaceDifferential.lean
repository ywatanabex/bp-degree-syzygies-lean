import BPFixedPoints.Incidence.CechCubicalBoundary
import BPFixedPoints.Incidence.CechTwistRestrictionMonomials

/-! # Signed cubical face differential using the original coefficient restrictions -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

/-- Replace one original chart coordinate by its overlap. -/
def faceStep (q : V → Fin 3) (v : V) : V → Fin 3 := Function.update q v 2

omit [Fintype V] in
/-- The original face refines to the corresponding overlap in one direction. -/
theorem faceStep_refines (q : V → Fin 3) (v : V) : FaceRefines q (faceStep q v) := by
  intro w
  by_cases hw : w = v <;> simp [faceStep, hw]

/-- Prefix overlap degree in precisely the original tensor enumeration. -/
noncomputable def faceBoundaryPrefix (q : V → Fin 3) (v : V) : ℕ :=
  ∑ w, if Fintype.equivFin V w < Fintype.equivFin V v then (if q w = 2 then 1 else 0) else 0

/-- Original right-minus-left incidence sign, including the tensor prefix parity. -/
noncomputable def faceBoundarySign (q : V → Fin 3) (v : V) : R :=
  (-1 : R) ^ faceBoundaryPrefix q v * (if q v = 1 then 1 else -1)

private theorem lineDegree_vertexFace (i : Fin 3) (m : FaceExponent i) :
    lineDegree (vertexFaceEquiv.symm ⟨i,m⟩) = if i = 2 then 1 else 0 := by
  fin_cases i <;> rfl

private theorem boundaryCoefficient_vertexFace (i : Fin 3) (m : FaceExponent i) :
    boundaryCoefficient R (vertexFaceEquiv.symm ⟨i,m⟩) =
      if i = 2 then 0 else if i = 1 then 1 else -1 := by
  fin_cases i <;> rfl

private theorem boundaryStep_vertexFace (d : ℕ) (i : Fin 3) (m : FaceExponent i) :
    boundaryStep d (vertexFaceEquiv.symm ⟨i,m⟩) =
      Sum.inr (Sum.inr (if i = 1 then -(d : ℤ)-exponentToInt i m else exponentToInt i m)) := by
  fin_cases i <;> rfl

private theorem vertexFace_overlap (i : Fin 3) (hi : i = 2) (m : FaceExponent i) :
    vertexFaceEquiv.symm ⟨i,m⟩ = Sum.inr (Sum.inr (exponentToInt i m)) := by
  subst i
  rfl

private theorem vertexFace_ext {i j : Fin 3} (hij : i = j) (m : FaceExponent i) (n : FaceExponent j)
    (h : exponentToInt i m = exponentToInt j n) :
    vertexFaceEquiv.symm ⟨i,m⟩ = vertexFaceEquiv.symm ⟨j,n⟩ := by
  subst j
  exact congrArg (fun z => vertexFaceEquiv.symm ⟨i,z⟩) (exponentToInt_injective i h)

omit [DecidableEq V] in
/-- The original basis prefix is exactly the overlap prefix of its face. -/
theorem boundaryPrefix_embedFace (q : V → Fin 3) (m : FaceMonoid q) (v : V) :
    boundaryPrefix (embedFace q m) v = faceBoundaryPrefix q v := by
  unfold boundaryPrefix faceBoundaryPrefix
  apply Finset.sum_congr rfl
  intro w _
  change (if _ then lineDegree (vertexFaceEquiv.symm ⟨q w,m w⟩) else 0) = _
  rw [lineDegree_vertexFace]

omit [Fintype V] [DecidableEq V] in
/-- Integer exponents of the coefficient shift are the original twist degrees in precisely the changed right directions. -/
theorem faceToInt_twistRestrictionShift {q r : V → Fin 3} (h : FaceRefines q r)
    (a : V → ℤ) (v : V) :
    faceToInt r (twistRestrictionShift h a) v = if q v = 1 ∧ r v = 2 then a v else 0 := by
  change exponentToInt (r v) (if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (a v) else 0) = _
  by_cases hv : q v = 1 ∧ r v = 2
  · rw [ite_eq_left hv, ite_eq_left hv, exponentToInt_fromInt]
    intro hn
    exact (hn hv.2).elim
  · simp [hv]

omit [Fintype V] in
/-- The actual negative-twist coefficient restriction has exactly the boundary monomial of the original tensor complex. -/
theorem embedFace_step (d : V → ℕ) (q : V → Fin 3) (m : FaceMonoid q) (v : V) :
    embedFace (faceStep q v)
      (refinementExponent (faceStep_refines q v) m +
        twistRestrictionShift (faceStep_refines q v) (fun w => -(d w : ℤ))) =
      Function.update (embedFace q m) v (boundaryStep (d v) (embedFace q m v)) := by
  funext w
  by_cases hw : w = v
  · subst w
    rw [Function.update_self]
    change vertexFaceEquiv.symm ⟨faceStep q v v, _⟩ = boundaryStep (d v) (vertexFaceEquiv.symm ⟨q v,m v⟩)
    rw [vertexFace_overlap _ (by simp [faceStep]), boundaryStep_vertexFace]
    congr 2
    change faceToInt (faceStep q v) (_ + _) v = _
    rw [map_add, Pi.add_apply, faceToInt_refinement, faceToInt_twistRestrictionShift]
    simp only [faceStep, Function.update_self, and_true]
    have hx : faceToInt q m v = exponentToInt (q v) (m v) := rfl
    rw [hx]
    split_ifs <;> omega
  · rw [Function.update_of_ne hw]
    apply vertexFace_ext (by simp [faceStep, hw])
    change faceToInt (faceStep q v) (_ + _) w = faceToInt q m w
    rw [map_add, Pi.add_apply, faceToInt_refinement, faceToInt_twistRestrictionShift]
    have hn : ¬(q w = 1 ∧ q w = 2) := by omega
    simp [faceStep, hw, hn]

/-- One independently defined cubical edge on the original face modules. -/
noncomputable def cubicalCoefficientEdge (a : V → ℤ) (q : V → Fin 3) (v : V) :
    Module.End R ((r : V → Fin 3) → FaceRing R r) :=
  if q v = 2 then 0 else
    (faceBoundarySign R q v) •
      ((LinearMap.single R (fun r => FaceRing R r) (faceStep q v)).comp
        ((multiTwistFaceRestriction R (faceStep_refines q v) a).comp (LinearMap.proj q)))

/-- The signed sum of the existing coefficient restrictions over all original cubical edges. -/
noncomputable def cubicalCoefficientD (a : V → ℤ) : Module.End R ((q : V → Fin 3) → FaceRing R q) :=
  ∑ q, ∑ v, cubicalCoefficientEdge R a q v

/-- Only the selected source face contributes when the input is supported on one face. -/
theorem cubicalCoefficientD_single (a : V → ℤ) (q : V → Fin 3) (x : FaceRing R q) :
    cubicalCoefficientD R a (Pi.single q x) =
      ∑ v, if q v = 2 then 0 else
        Pi.single (faceStep q v) (faceBoundarySign R q v •
          multiTwistFaceRestriction R (faceStep_refines q v) a x) := by
  simp only [cubicalCoefficientD, LinearMap.sum_apply]
  rw [Finset.sum_eq_single q]
  · apply Finset.sum_congr rfl
    intro v _
    by_cases hv : q v = 2 <;> simp [cubicalCoefficientEdge, hv, ← Pi.single_smul]
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : r v = 2 <;> simp [cubicalCoefficientEdge, hv, Pi.single_eq_of_ne hr]
  · simp

omit [DecidableEq V] in
/-- The original face decomposition sends a monomial to precisely its face component. -/
theorem faceEquiv_single_face (q : V → Fin 3) (m : FaceMonoid q) (c : R) :
    faceEquiv R (single (embedFace q m) c) = Pi.single q (AddMonoidAlgebra.single m c) := by
  ext r
  by_cases hr : r = q
  · subst r
    simp
  · rw [faceEquiv_single_ne R hr, Pi.single_eq_of_ne hr]

/-- The original tensor differential and the signed sum of original face restrictions agree on every monomial. -/
theorem faceEquiv_d_single (d : V → ℕ) (q : V → Fin 3) (m : FaceMonoid q) (c : R) :
    faceEquiv R ((contraction R d).d (single (embedFace q m) c)) =
      cubicalCoefficientD R (fun v => -(d v : ℤ))
        (faceEquiv R (single (embedFace q m) c)) := by
  rw [contraction_d_single, map_sum, faceEquiv_single_face, cubicalCoefficientD_single]
  apply Finset.sum_congr rfl
  intro v _
  have hb : boundaryCoefficient R (embedFace q m v) =
      if q v = 2 then 0 else if q v = 1 then 1 else -1 :=
    boundaryCoefficient_vertexFace R (q v) (m v)
  rw [hb, boundaryPrefix_embedFace]
  by_cases hv : q v = 2
  · simp [hv]
  · rw [ite_eq_right hv, ite_eq_right hv, ← embedFace_step,
      faceEquiv_single_face, multiTwistFaceRestriction_single]
    simp only [faceBoundarySign, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_assoc]

/-- In every degree, the original tensor differential is the original cubical coefficient differential. -/
theorem faceEquiv_d (d : V → ℕ) (x : C R V) :
    faceEquiv R ((contraction R d).d x) =
      cubicalCoefficientD R (fun v => -(d v : ℤ)) (faceEquiv R x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single b c =>
      obtain ⟨⟨q,m⟩,rfl⟩ := faceBasisEquiv.symm.surjective b
      exact faceEquiv_d_single R d q m c

/-- The independently defined coefficient differential squares to zero for the original negative twists. -/
theorem cubicalCoefficientD_square (d : V → ℕ) (x : (q : V → Fin 3) → FaceRing R q) :
    cubicalCoefficientD R (fun v => -(d v : ℤ))
      (cubicalCoefficientD R (fun v => -(d v : ℤ)) x) = 0 := by
  obtain ⟨y,rfl⟩ := (faceEquiv R).surjective x
  have hd : (contraction R d).d ((contraction R d).d y) = 0 :=
    LinearMap.congr_fun (contraction R d).d_sq y
  rw [← faceEquiv_d, ← faceEquiv_d, hd, map_zero]

end BPFixedPoints.CechProduct
