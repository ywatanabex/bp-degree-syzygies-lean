import BPFixedPoints.Incidence.CechRefinementLocalization

/-! # Transition units for the actual polynomial and Laurent face coordinates

These units record the change of a homogeneous-coordinate trivialization from
the right chart to a Laurent overlap. They are defined in the ambient face
rings, before imposing any incidence equation.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V]

theorem faceLaurentExponents_cancel (q : V → Fin 3) (v : V) (hv : q v = 2) :
    Pi.single v (faceOneExponent (q v)) +
      Pi.single v (exponentFromInt (q v) (-1)) = (0 : FaceMonoid q) := by
  rw [← Pi.single_add]
  have he : faceOneExponent (q v) + exponentFromInt (q v) (-1) = 0 := by
    apply exponentToInt_injective (q v)
    rw [map_add, exponentToInt_one, map_zero, exponentToInt_fromInt]
    · norm_num
    · intro hn
      exact (hn hv).elim
  rw [he, Pi.single_zero]

variable (R : Type*) [CommRing R]

/-- The actual Laurent variable, together with its inverse monomial. -/
noncomputable def faceLaurentUnit (q : V → Fin 3) (v : V) (hv : q v = 2) : (FaceRing R q)ˣ where
  val := faceVariable R q v
  inv := AddMonoidAlgebra.single (Pi.single v (exponentFromInt (q v) (-1))) 1
  val_inv := by
    rw [faceVariable, AddMonoidAlgebra.single_mul_single, faceLaurentExponents_cancel q v hv,
      mul_one]
    rfl
  inv_val := by
    rw [mul_comm, faceVariable, AddMonoidAlgebra.single_mul_single,
      faceLaurentExponents_cancel q v hv, mul_one]
    rfl

@[simp] theorem faceLaurentUnit_val (q : V → Fin 3) (v : V) (hv : q v = 2) :
    (faceLaurentUnit R q v hv : FaceRing R q) = faceVariable R q v := rfl

/-- Unit changing a source homogeneous-coordinate trivialization to its refined face. -/
noncomputable def faceTransitionUnit {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    (FaceRing R r)ˣ :=
  if hf : q v = 1 ∧ r v = 2 then (faceLaurentUnit R r v hf.2)⁻¹ else 1

/-- A source vertex exponent restricts to the positive target exponent, except
when passing from a right chart to an overlap, where it becomes negative. -/
theorem refinementExponent_vertex {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    refinementExponent h (Pi.single v (faceOneExponent (q v))) =
      Pi.single v (if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (-1)
        else faceOneExponent (r v)) := by
  apply faceToInt_injective
  ext w
  rw [faceToInt_refinement, faceToInt_vertex]
  by_cases hw : w = v
  · subst w
    change (if q v = 1 ∧ r v = 2 then -((Pi.single v (1 : ℤ) : V → ℤ) v) else (Pi.single v (1 : ℤ) : V → ℤ) v) =
      exponentToInt (r v) ((Pi.single v _ : FaceMonoid r) v)
    rw [Pi.single_eq_same, Pi.single_eq_same]
    change (if q v = 1 ∧ r v = 2 then -(1 : ℤ) else 1) =
      exponentToInt (r v) (if q v = 1 ∧ r v = 2 then exponentFromInt (r v) (-1)
        else faceOneExponent (r v))
    split_ifs with hf
    · rw [exponentToInt_fromInt]
      intro hr
      exact (hr hf.2).elim
    · simp
  · simp [faceToInt, hw]

/-- Coordinate restriction in the original ambient face rings. -/
theorem faceRefinement_variable {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    faceRefinementMap R h (faceVariable R q v) =
      if hf : q v = 1 ∧ r v = 2 then (↑((faceLaurentUnit R r v hf.2)⁻¹) : FaceRing R r)
      else faceVariable R r v := by
  rw [faceVariable, faceRefinementMap_single, refinementExponent_vertex]
  split_ifs <;> rfl

end BPFixedPoints.CechProduct
