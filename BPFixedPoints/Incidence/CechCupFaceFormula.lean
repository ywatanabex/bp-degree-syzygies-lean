import BPFixedPoints.Incidence.CechCupFaceTerms

/-! # All representatives of the existing tensor cup have the original face formula -/

namespace BPFixedPoints.CechProduct
open Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

/-- Sum the independently specified original coefficient face-pair terms at one original output face. -/
def faceCupAt (d e : V → ℕ) (s : V → Fin 3) :
    ((p : V → Fin 3) → FaceRing R p) →ₗ[R]
      ((q : V → Fin 3) → FaceRing R q) →ₗ[R] FaceRing R s :=
  ∑ p, ∑ q, (faceCupTerm R d e s p q).compl₁₂ (LinearMap.proj p) (LinearMap.proj q)

/-- An original single face pair contributes precisely its original summand. -/
theorem faceCupAt_single (d e : V → ℕ) (s p q : V → Fin 3)
    (x : FaceRing R p) (y : FaceRing R q) :
    faceCupAt R d e s (Pi.single p x) (Pi.single q y) = faceCupTerm R d e s p q x y := by
  classical
  simp only [faceCupAt,LinearMap.sum_apply,LinearMap.compl₁₂_apply,LinearMap.proj_apply]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · simp only [Pi.single_eq_same]
    · intro a _ ha
      simp only [Pi.single_eq_of_ne ha,map_zero]
    · simp
  · intro a _ ha
    simp only [Pi.single_eq_of_ne ha,map_zero,LinearMap.zero_apply,Finset.sum_const_zero]
  · simp

/-- The old tensor cup and the independently specified original coefficient face formula agree on every cochain. -/
theorem faceEquiv_chainCup_full (d e : V → ℕ) (x y : C R V) (s : V → Fin 3) :
    faceEquiv R (chainCup R d e x y) s = faceCupAt R d e s (faceEquiv R x) (faceEquiv R y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add,Pi.add_apply,LinearMap.add_apply,hx,hx']
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add,Pi.add_apply,hy,hy']
    | single b t =>
      obtain ⟨⟨p,m⟩,rfl⟩ := faceBasisEquiv.symm.surjective a
      obtain ⟨⟨q,k⟩,rfl⟩ := faceBasisEquiv.symm.surjective b
      change faceEquiv R (chainCup R d e (single (embedFace p m) r) (single (embedFace q k) t)) s =
        faceCupAt R d e s (faceEquiv R (single (embedFace p m) r)) (faceEquiv R (single (embedFace q k) t))
      rw [faceEquiv_single_face,faceEquiv_single_face,faceCupAt_single]
      exact faceEquiv_chainCup_embedFace R d e s p q m k r t

/-- The two original input parity factors multiply to the original output face parity. -/
theorem faceCupTerm_parity (d e : V → ℕ) (s p q : V → Fin 3)
    (x : FaceRing R p) (y : FaceRing R q) :
    faceCupTerm R d e s p q ((-1 : R)^faceDegree p • x) ((-1 : R)^faceDegree q • y) =
      (-1 : R)^faceDegree s • faceCupTerm R d e s p q x y := by
  by_cases h : DiagonalShape s p q
  · simp only [map_smul,LinearMap.smul_apply,smul_smul]
    rw [← pow_add,Nat.add_comm,h.degree]
  · simp only [faceCupTerm,dite_eq_right h,LinearMap.zero_apply,smul_zero]

/-- The original degree-sign comparison is multiplicative on the full face formula. -/
theorem faceCupAt_parity (d e : V → ℕ) (s : V → Fin 3)
    (x y : (p : V → Fin 3) → FaceRing R p) :
    faceCupAt R d e s (fun p => (-1 : R)^faceDegree p • x p)
      (fun q => (-1 : R)^faceDegree q • y q) =
        (-1 : R)^faceDegree s • faceCupAt R d e s x y := by
  simp only [faceCupAt,LinearMap.sum_apply,LinearMap.compl₁₂_apply,LinearMap.proj_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact faceCupTerm_parity R d e s p q (x p) (y q)

end
end BPFixedPoints.CechProduct
