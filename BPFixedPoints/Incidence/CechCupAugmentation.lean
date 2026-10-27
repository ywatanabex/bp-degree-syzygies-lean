import BPFixedPoints.Incidence.CechCupFormula
import BPFixedPoints.Incidence.CechFaces

/-! # Evaluation on the all-left chart preserves the Čech product -/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.CechProduct

open Finsupp

theorem lineCupBasis_face_zero {e : ℕ} {x y z : Basis}
    (h : lineCupBasis e x y = some z) (hz : (vertexFaceEquiv z).1 = 0) :
    (vertexFaceEquiv x).1 = 0 ∧ (vertexFaceEquiv y).1 = 0 := by
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    simp only [lineCupBasis, Option.some.injEq, reduceCtorEq] at h <;>
    cases h <;> simp_all [vertexFaceEquiv]

theorem finCupCross_zero_of_degree_zero (n : ℕ) (x y : Fin n → Basis)
    (h : ∀ v, lineDegree (y v) = 0) : finCupCross n x y = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finCupCross, h 0, mul_zero, zero_add]
    exact ih _ _ (fun v => h v.succ)

variable {V : Type*} [Fintype V]

theorem cupBasis_face_zero {e : V → ℕ} {x y z : V → Basis}
    (h : cupBasis e x y = some z) (hz : (faceBasisEquiv z).1 = 0) :
    (faceBasisEquiv x).1 = 0 ∧ (faceBasisEquiv y).1 = 0 := by
  have hv (v : V) := lineCupBasis_face_zero ((cupBasis_some_iff _ _ _ _).mp h v)
    (congrFun hz v)
  exact ⟨funext (fun v => (hv v).1), funext (fun v => (hv v).2)⟩

theorem cupBasis_left (e : V → ℕ) (a b : FaceMonoid (0 : V → Fin 3)) :
    cupBasis e (embedFace 0 a) (embedFace 0 b) = some (embedFace 0 (a + b)) := by
  apply (cupBasis_some_iff _ _ _ _).mpr
  intro v
  rfl

theorem cupCross_left (x : V → Basis) (b : FaceMonoid (0 : V → Fin 3)) :
    cupCross x (embedFace 0 b) = 0 :=
  finCupCross_zero_of_degree_zero _ _ _ (fun _ => rfl)

variable (R : Type*) [CommRing R]

theorem faceEquiv_single_zero_of_not_left (x : V → Basis) (r : R)
    (hx : (faceBasisEquiv x).1 ≠ 0) : faceEquiv R (single x r) 0 = 0 := by
  have he : x = embedFace (faceBasisEquiv x).1 (faceBasisEquiv x).2 :=
    (faceBasisEquiv.symm_apply_apply x).symm
  rw [he]
  exact faceEquiv_single_ne R (Ne.symm hx) _ r

theorem faceEquiv_cup_zero_of_not_left (d e : V → ℕ) (x y : V → Basis) (r s : R)
    (h : ¬ ((faceBasisEquiv x).1 = 0 ∧ (faceBasisEquiv y).1 = 0)) :
    faceEquiv R (chainCup R d e (single x r) (single y s)) 0 = 0 := by
  rw [chainCup_single]
  cases hc : cupBasis e x y with
  | none => simp
  | some z =>
    exact faceEquiv_single_zero_of_not_left R z _ (fun hz => h (cupBasis_face_zero hc hz))

theorem faceEquiv_cup_single (d e : V → ℕ) (x y : V → Basis) (r s : R) :
    faceEquiv R (chainCup R d e (single x r) (single y s)) 0 =
      faceEquiv R (single x r) 0 * faceEquiv R (single y s) 0 := by
  classical
  by_cases h : (faceBasisEquiv x).1 = 0 ∧ (faceBasisEquiv y).1 = 0
  · obtain ⟨a, ha⟩ : ∃ a : FaceMonoid (0 : V → Fin 3), x = embedFace 0 a := by
      have he := faceBasisEquiv.symm_apply_apply x
      generalize hg : faceBasisEquiv x = q at *
      obtain ⟨q, a⟩ := q
      dsimp only at h he
      obtain rfl := h.1
      exact ⟨a, he.symm⟩
    obtain ⟨b, hb⟩ : ∃ b : FaceMonoid (0 : V → Fin 3), y = embedFace 0 b := by
      have he := faceBasisEquiv.symm_apply_apply y
      generalize hg : faceBasisEquiv y = q at *
      obtain ⟨q, b⟩ := q
      dsimp only at h he
      obtain rfl := h.2
      exact ⟨b, he.symm⟩
    subst x y
    rw [chainCup_single, cupBasis_left, cupCross_left]
    simp only [Option.elim, pow_zero, one_mul, faceEquiv_single_same,
      AddMonoidAlgebra.single_mul_single]
  · rw [faceEquiv_cup_zero_of_not_left R d e x y r s h]
    by_cases hx : (faceBasisEquiv x).1 = 0
    · have hy : (faceBasisEquiv y).1 ≠ 0 := fun hy => h ⟨hx, hy⟩
      rw [faceEquiv_single_zero_of_not_left R y s hy, mul_zero]
    · rw [faceEquiv_single_zero_of_not_left R x r hx, zero_mul]

theorem faceEquiv_chainCup (d e : V → ℕ) (x y : C R V) :
    faceEquiv R (chainCup R d e x y) 0 = faceEquiv R x 0 * faceEquiv R y 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx, hx', add_mul]
  | single x r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, Pi.add_apply, hy, hy', mul_add]
    | single y s => exact faceEquiv_cup_single R d e x y r s

end BPFixedPoints.CechProduct
