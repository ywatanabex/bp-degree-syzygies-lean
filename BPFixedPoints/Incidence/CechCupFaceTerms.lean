import BPFixedPoints.Incidence.CechCupFaceMonomials

/-! # Original coefficient tensor cup evaluated on each original face pair -/

namespace BPFixedPoints.CechProduct
open Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

/-- The original face-pair term uses only the original coefficient restrictions and diagonal crossing. -/
def faceCupTerm (d e : V → ℕ) (s p q : V → Fin 3) :
    FaceRing R p →ₗ[R] FaceRing R q →ₗ[R] FaceRing R s :=
  if h : DiagonalShape s p q then (-1 : ℤ)^diagonalCross p q •
    (LinearMap.mul R (FaceRing R s)).compl₁₂
      (multiTwistFaceRestriction R h.left_refines (fun v => -(d v : ℤ)))
      (multiTwistFaceRestriction R h.right_refines (fun v => -(e v : ℤ))) else 0

/-- Every original face-pair term retains the original integer Koszul coefficient. -/
theorem faceCupTerm_apply (d e : V → ℕ) (s p q : V → Fin 3)
    (x : FaceRing R p) (y : FaceRing R q) :
    faceCupTerm R d e s p q x y = if h : DiagonalShape s p q then
      (-1 : ℤ)^diagonalCross p q •
        (multiTwistFaceRestriction R h.left_refines (fun v => -(d v : ℤ)) x *
          multiTwistFaceRestriction R h.right_refines (fun v => -(e v : ℤ)) y) else 0 := by
  unfold faceCupTerm
  split_ifs <;> rfl

/-- The original exponent refinements give exactly the original coefficient monomial product. -/
theorem faceCupTerm_single (d e : V → ℕ) {s p q : V → Fin 3} (h : DiagonalShape s p q)
    (m : FaceMonoid p) (k : FaceMonoid q) (r t : R) :
    faceCupTerm R d e s p q (AddMonoidAlgebra.single m r) (AddMonoidAlgebra.single k t) =
      AddMonoidAlgebra.single (cupFaceExponent d e h m k) ((-1 : R)^diagonalCross p q * (r*t)) := by
  rw [faceCupTerm_apply,dite_eq_left h,multiTwistFaceRestriction_single,multiTwistFaceRestriction_single,
    AddMonoidAlgebra.single_mul_single, ← Int.cast_smul_eq_zsmul R]
  simp only [Int.cast_pow,Int.cast_neg,Int.cast_one,AddMonoidAlgebra.smul_single,smul_eq_mul]
  rfl

/-- The existing tensor cup and original face-pair formula agree on all original monomial representatives. -/
theorem faceEquiv_chainCup_embedFace (d e : V → ℕ) (s p q : V → Fin 3)
    (m : FaceMonoid p) (k : FaceMonoid q) (r t : R) :
    faceEquiv R (chainCup R d e (single (embedFace p m) r) (single (embedFace q k) t)) s =
      faceCupTerm R d e s p q (AddMonoidAlgebra.single m r) (AddMonoidAlgebra.single k t) := by
  classical
  rw [chainCup_single]
  by_cases h : DiagonalShape s p q
  · rw [cupBasis_embedFace d e h,Option.elim,faceEquiv_single_same,cupCross_embedFace,
      faceCupTerm_single R d e h]
  · rw [faceCupTerm_apply,dite_eq_right h]
    cases hc : cupBasis e (embedFace p m) (embedFace q k) with
    | none => simp
    | some z =>
      have hz : (faceBasisEquiv z).1 ≠ s := by
        intro hz
        have hs := cupBasis_output_shape e hc
        exact h (by simpa only [hz,faceBasisEquiv_embedFace] using hs)
      obtain ⟨⟨u,l⟩,rfl⟩ := faceBasisEquiv.symm.surjective z
      have hu : u ≠ s := by simpa only [Equiv.apply_symm_apply] using hz
      exact faceEquiv_single_ne R (Ne.symm hu) l _

end
end BPFixedPoints.CechProduct
