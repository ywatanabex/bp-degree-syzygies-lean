import BPFixedPoints.Incidence.CechRefinementLocalization

/-! # Intersections in the full incidence face diagram

The join of two faces allows every coordinate inverted by either face. The
localization denominator is the product of the corresponding vertex variables.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Coordinate description of the overlap of any two chart faces. -/
def faceJoin (q r : V → Fin 3) : V → Fin 3 := fun v => if q v = r v then q v else 2

theorem faceRefines_join_left (q r : V → Fin 3) : FaceRefines q (faceJoin q r) := by
  intro v
  by_cases he : q v = r v <;> simp [faceJoin, he]

theorem faceRefines_join_right (q r : V → Fin 3) : FaceRefines r (faceJoin q r) := by
  intro v
  by_cases he : q v = r v <;> simp [faceJoin, he]

theorem faceRefines_join {p q r : V → Fin 3} (hq : FaceRefines p q) (hr : FaceRefines p r) :
    FaceRefines p (faceJoin q r) :=
  faceRefines_trans hq (faceRefines_join_left q r)

/-- Under a common parent, a coordinate remains unchanged exactly when both
faces leave it unchanged. -/
theorem faceJoin_eq_parent_iff {p q r : V → Fin 3}
    (hq : FaceRefines p q) (hr : FaceRefines p r) (v : V) :
    p v = faceJoin q r v ↔ p v = q v ∧ p v = r v := by
  by_cases he : q v = r v
  · simp [faceJoin, he]
  · have ha := hq v
    have hb := hr v
    simp only [faceJoin, ite_eq_right he]
    constructor
    · intro hp
      constructor <;> omega
    · rintro ⟨hp, hp'⟩
      exact (he (hp.symm.trans hp')).elim

/-- Product form of the denominator used to realize every higher intersection. -/
theorem refinementDen_eq_prod (R : Type*) [CommRing R] (q r : V → Fin 3) :
    refinementDen R q r = ∏ v, if q v = r v then 1 else faceVariable R q v := by
  have he : refinementDenExponent q r =
      ∑ v, Pi.single v (if q v = r v then 0 else faceOneExponent (q v)) := by
    funext w
    simp [refinementDenExponent]
  rw [refinementDen, he]
  calc
    _ = ∏ v, AddMonoidAlgebra.single
        (Pi.single v (if q v = r v then 0 else faceOneExponent (q v))) (1 : R) := by
      rw [AddMonoidAlgebra.prod_single]
      simp only [Finset.prod_const_one]
    _ = _ := ?_
  · apply Finset.prod_congr rfl
    intro v _
    by_cases hv : q v = r v
    · simp only [hv, ite_true, Pi.single_zero]
      rfl
    · simp only [hv, ite_false]
      rfl

end BPFixedPoints.CechProduct
