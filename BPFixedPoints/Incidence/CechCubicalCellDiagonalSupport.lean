import BPFixedPoints.Incidence.CechCubicalCellDiagonalCoefficients
import BPFixedPoints.Incidence.CechCubicalCellSubface

/-! # The original diagonal retains actual face support and total degree

Each of its two output faces refines the original face, and their original
overlap counts add to the source count. These are the precise support
conditions needed to restrict the diagonal to the original cell presheaves.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable {V : Type*}

/-- The first output face is an original subface of the source. -/
theorem DiagonalShape.left_refines {s p q : V → Fin 3} (h : DiagonalShape s p q) : FaceRefines p s := by
  intro v
  have hv := h v
  generalize s v = k at hv ⊢
  fin_cases k <;> simp only [intervalDiagonalShape] at hv <;> simp_all

/-- The second output face is an original subface of the same source. -/
theorem DiagonalShape.right_refines {s p q : V → Fin 3} (h : DiagonalShape s p q) : FaceRefines q s := by
  intro v
  have hv := h v
  generalize s v = k at hv ⊢
  fin_cases k <;> simp only [intervalDiagonalShape] at hv <;> simp_all

/-- Original output overlap dimensions add to the original source dimension. -/
theorem DiagonalShape.degree [Fintype V] {s p q : V → Fin 3} (h : DiagonalShape s p q) :
    faceDegree p+faceDegree q = faceDegree s := by
  unfold faceDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv := h v
  generalize s v = k at hv ⊢
  generalize p v = i at hv ⊢
  generalize q v = j at hv ⊢
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp_all [intervalDiagonalShape]

/-- An original vertex has precisely its own original repeated face pair. -/
theorem diagonalShape_vertex_iff {s p q : V → Fin 3} (hs : ∀ v, s v ≠ 2) :
    DiagonalShape s p q ↔ p = s ∧ q = s := by
  constructor
  · intro h
    exact ⟨funext fun v => (h.left_refines v).resolve_right (hs v),
      funext fun v => (h.right_refines v).resolve_right (hs v)⟩
  · rintro ⟨hp,hq⟩
    rw [hp,hq]
    intro v
    have hv := hs v
    generalize s v = k at hv ⊢
    fin_cases k <;> simp_all [intervalDiagonalShape]

/-- No right overlap means no original tensor crossing. -/
theorem finDiagonalCross_eq_zero (n : ℕ) (p q : Fin n → Fin 3) (hq : ∀ v, q v ≠ 2) :
    finDiagonalCross n p q = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finDiagonalCross,hq 0,ite_false,mul_zero,zero_add]; exact ih _ _ (fun v => hq v.succ)

/-- A labelled original endpoint family has no original crossing. -/
theorem diagonalCross_eq_zero [Fintype V] (p q : V → Fin 3) (hq : ∀ v, q v ≠ 2) : diagonalCross p q = 0 :=
  finDiagonalCross_eq_zero _ _ _ (fun v => hq _)

variable (R : Type*) [CommRing R] [Fintype V]

/-- The specified diagonal sends the original vertex to that same original vertex twice, with coefficient once. -/
theorem diagonal_vertex (s : V → Fin 3) (hs : ∀ v, s v ≠ 2) (r : R) :
    (diagonal R V).map (single s r) = single s 1 ⊗ₜ[R] single s r := by
  apply (pairCoordinates R V).injective
  ext z
  rcases z with ⟨p,q⟩
  rw [diagonal_coefficient]
  simp only [pairCoordinates,finsuppTensorFinsupp'_single_tmul_single]
  by_cases hp : p = s
  · subst p
    by_cases hq : q = s
    · subst q
      simp [diagonalShape_vertex_iff hs,diagonalCross_eq_zero s s hs]
    · simp [diagonalShape_vertex_iff hs,hq,Ne.symm hq,Finsupp.single_apply]
  · simp [diagonalShape_vertex_iff hs,hp,Ne.symm hp,Finsupp.single_apply]

/-- Only the original subface pairs of the source occur, in exactly the original total degree. -/
theorem diagonal_single_support (s : V → Fin 3) (r : R) :
    pairCoordinates R V ((diagonal R V).map (single s r)) ∈
      supported R R {z | FaceRefines z.1 s ∧ FaceRefines z.2 s ∧
        faceDegree z.1+faceDegree z.2 = faceDegree s} := by
  intro z hz
  have hc := Finsupp.mem_support_iff.mp hz
  rw [diagonal_coefficient] at hc
  have hs : DiagonalShape s z.1 z.2 := by
    by_contra hs
    exact hc (if_neg hs)
  exact ⟨hs.left_refines,hs.right_refines,hs.degree⟩

/-- The specified diagonal retains every original ambient face support. -/
theorem diagonal_subfaces (s : V → Fin 3) (x : Cells R V) (hx : x ∈ subfaces R s) :
    pairCoordinates R V ((diagonal R V).map x) ∈
      supported R R {z | FaceRefines z.1 s ∧ FaceRefines z.2 s} := by
  rw [← x.sum_single,map_finsuppSum,map_finsuppSum]
  apply Submodule.sum_mem
  intro p hp
  have hs := diagonal_single_support R p (x p)
  intro z hz
  have h := hs hz
  exact ⟨faceRefines_trans h.1 (hx hp),faceRefines_trans h.2.1 (hx hp)⟩

/-- The original homogeneous cell degree is the sum of the two original output degrees. -/
theorem diagonal_degree (n : ℕ) (x : Cells R V)
    (hx : x ∈ supported R R {s | cellDegree s = -(n : ℤ)}) :
    pairCoordinates R V ((diagonal R V).map x) ∈
      supported R R {z | faceDegree z.1+faceDegree z.2 = n} := by
  rw [← x.sum_single,map_finsuppSum,map_finsuppSum]
  apply Submodule.sum_mem
  intro p hp
  have hs := diagonal_single_support R p (x p)
  have hd : faceDegree p = n := by
    have h := hx hp
    change -(faceDegree p : ℤ) = -(n : ℤ) at h
    omega
  intro z hz
  exact (hs hz).2.2.trans hd

end BPFixedPoints.CechCubicalCell
