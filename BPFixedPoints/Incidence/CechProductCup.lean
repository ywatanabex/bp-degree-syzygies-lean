import BPFixedPoints.Incidence.CechTensorCup
import BPFixedPoints.Incidence.CechProductDegree

/-!
# Čech cohomology product for any finite vertex set

Tensor the vertexwise Alexander–Whitney products in the same order as the
existing product Čech complex. Moving the right head past the left tail gives
sign (−1)^(deg(left tail)*deg(right head)).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

noncomputable def lineCyclePairing (d e : ℕ) :
    CyclePairing (lineFree R (d + e)) (Fin (phi d) →₀ R) (Fin (phi e) →₀ R) :=
  (CechLine.cyclePairing d e).congr (lineHBasisEquiv R d) (lineHBasisEquiv R e)
    (lineBasisEquiv R).symm (lineHBasisEquiv R (d + e))

/-- For the empty vertex set, the product is ordinary coefficient multiplication. -/
noncomputable def emptyCohomologyCup (d e : Fin 0 → ℕ) :
    H R d →ₗ[R] H R e →ₗ[R] H R (d + e) :=
  Finsupp.llift _ R R _ fun _ =>
    Finsupp.llift _ R R _ fun _ => single (fun i => Fin.elim0 i) 1

noncomputable def emptyCyclePairing (d e : Fin 0 → ℕ) :
    CyclePairing (empty R (d + e)) (H R d) (H R e) where
  representative := (emptyCohomologyCup R d e).compr₂ (empty R (d + e)).i
  closed x y := LinearMap.congr_fun (empty R (d + e)).d_i (emptyCohomologyCup R d e x y)

/-- Cocycle representative of the cup product in the actual finite-vertex Čech complex. -/
noncomputable def finCyclePairing : (n : ℕ) → (d e : Fin n → ℕ) →
    CyclePairing (finProduct R n (d + e)) (H R d) (H R e)
  | 0, d, e => emptyCyclePairing R d e
  | n + 1, d, e =>
    ((lineCyclePairing R (d 0) (e 0)).tensor
      (finCyclePairing n (Fin.tail d) (Fin.tail e))
      ((-1 : R) ^ (cohomologyDegree (Fin.tail d) * lineCohomologyDegree (e 0)))).congr
        (consEquiv R fun i => Fin (phi (d i)))
        (consEquiv R fun i => Fin (phi (e i)))
        (consEquiv R fun _ => Basis)
        (consEquiv R fun i => Fin (phi ((d + e) i)))

/-- Return to an arbitrary finite vertex set with the same enumeration as the existing contraction. -/
noncomputable def cyclePairing {V : Type*} [Fintype V] (d e : V → ℕ) :
    CyclePairing (contraction R (d + e)) (H R d) (H R e) :=
  let v := (Fintype.equivFin V).symm
  (finCyclePairing R (Fintype.card V) (fun i => d (v i)) (fun i => e (v i))).congr
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi (d i))) v))
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi (e i))) v))
    (Finsupp.mapDomain.linearEquiv R R (v.arrowCongr (Equiv.refl Basis)))
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi ((d + e) i))) v))

/-- Multi-vertex cup product: project the actual product of cocycle representatives by the existing contraction. -/
noncomputable def cohomologyCup {V : Type*} [Fintype V] (d e : V → ℕ) :
    H R d →ₗ[R] H R e →ₗ[R] H R (d + e) := (cyclePairing R d e).cup

theorem cyclePairing_closed {V : Type*} [Fintype V] (d e : V → ℕ)
    (x : H R d) (y : H R e) :
    (contraction R (d + e)).d ((cyclePairing R d e).representative x y) = 0 :=
  (cyclePairing R d e).closed x y

theorem cohomologyCup_projection {V : Type*} [Fintype V] (d e : V → ℕ)
    (x : H R d) (y : H R e) :
    cohomologyCup R d e x y =
      (contraction R (d + e)).p ((cyclePairing R d e).representative x y) := rfl

/-- Exact comparison between local and multi-vertex products on pure tensors. -/
theorem finCyclePairing_cup_cons {n : ℕ} (d e : Fin (n + 1) → ℕ)
    (x : Fin (phi (d 0)) →₀ R) (x' : H R (Fin.tail d))
    (y : Fin (phi (e 0)) →₀ R) (y' : H R (Fin.tail e)) :
    (finCyclePairing R (n + 1) d e).cup
      (consEquiv R _ (x ⊗ₜ[R] x')) (consEquiv R _ (y ⊗ₜ[R] y')) =
    consEquiv R _ (((-1 : R) ^
        (cohomologyDegree (Fin.tail d) * lineCohomologyDegree (e 0))) •
      ((lineCyclePairing R (d 0) (e 0)).cup x y ⊗ₜ[R]
        (finCyclePairing R n (Fin.tail d) (Fin.tail e)).cup x' y')) := by
  erw [finCyclePairing, CyclePairing.congr_cup_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, CyclePairing.tensor_cup_tmul]
  rfl

theorem lineCyclePairing_cup_eq_zero (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (lineCyclePairing R d e).cup = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [lineCyclePairing, CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup,
    CechLine.cohomologyCup_eq_zero_of_pos d e hd he, map_zero]
  rfl

/-- If both twists are positive at a common vertex, the multi-vertex cup product vanishes. -/
theorem finCyclePairing_cup_eq_zero_of_overlap (n : ℕ) (d e : Fin n → ℕ)
    (v : Fin n) (hd : 0 < d v) (he : 0 < e v) : (finCyclePairing R n d e).cup = 0 := by
  induction n with
  | zero => exact Fin.elim0 v
  | succ n ih =>
    apply (LinearMap.compl₁₂_inj
      (consEquiv R (fun i => Fin (phi (d i)))).surjective
      (consEquiv R (fun i => Fin (phi (e i)))).surjective).mp
    apply TensorProduct.ext'
    intro x x'
    apply TensorProduct.ext'
    intro y y'
    change (finCyclePairing R (n + 1) d e).cup
      (consEquiv R _ (x ⊗ₜ[R] x')) (consEquiv R _ (y ⊗ₜ[R] y')) = 0
    rw [finCyclePairing_cup_cons]
    cases v using Fin.cases with
    | zero => rw [lineCyclePairing_cup_eq_zero R (d 0) (e 0) hd he]; simp; exact (consEquiv R _).map_zero
    | succ v => rw [ih (Fin.tail d) (Fin.tail e) v hd he]; simp; exact (consEquiv R _).map_zero

theorem cohomologyCup_eq_zero_of_overlap {V : Type*} [Fintype V] (d e : V → ℕ)
    (v : V) (hd : 0 < d v) (he : 0 < e v) : cohomologyCup R d e = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  unfold cohomologyCup cyclePairing
  rw [CyclePairing.congr_cup_apply]
  have hz := finCyclePairing_cup_eq_zero_of_overlap R (Fintype.card V)
    (fun i => d ((Fintype.equivFin V).symm i))
    (fun i => e ((Fintype.equivFin V).symm i)) ((Fintype.equivFin V) v)
    (by simpa using hd) (by simpa using he)
  rw [hz]
  simp

end BPFixedPoints.CechProduct
