import BPFixedPoints.Incidence.CechCupFaceFormula
import BPFixedPoints.Incidence.BinaryCoverCellCupDiagonalEvaluation

/-! # The original coefficient cup retains precisely the available original face pairs -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory TopologicalSpace CechProduct CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

/-- Every original allowed diagonal pair is available on its original output face in the same degree. -/
theorem diagonalShape_pairAvailable (n : ℕ) (s : FaceIndex (V := V) n)
    {p q : V → Fin 3} (h : DiagonalShape s.val p q) :
    binaryCoverFaceOpen U s.val ≤ binaryCoverFaceOpen U p ∧
      binaryCoverFaceOpen U s.val ≤ binaryCoverFaceOpen U q ∧ faceDegree p+faceDegree q=n := by
  refine ⟨faceOpen_refinement_le U h.left_refines,faceOpen_refinement_le U h.right_refines,?_⟩
  have hs := s.property
  change -(faceDegree s.val : ℤ) = -(n : ℤ) at hs
  have hd := h.degree
  omega

/-- The original full coefficient face sum equals the same original available-pair sum as the actual cup. -/
theorem faceCupAt_availablePairs (d e : V → ℕ) (n : ℕ) (s : FaceIndex (V := V) n)
    (x y : (p : V → Fin 3) → FaceRing R p) :
    faceCupAt R d e s.val x y =
      ∑ z : PairCellIndex U (binaryCoverFaceOpen U s.val) n,
        faceCupTerm R d e s.val z.val.1 z.val.2 (x z.val.1) (y z.val.2) := by
  classical
  let P (z : (V → Fin 3) × (V → Fin 3)) : Prop :=
    binaryCoverFaceOpen U s.val ≤ binaryCoverFaceOpen U z.1 ∧
      binaryCoverFaceOpen U s.val ≤ binaryCoverFaceOpen U z.2 ∧ faceDegree z.1+faceDegree z.2=n
  let f (z : (V → Fin 3) × (V → Fin 3)) := faceCupTerm R d e s.val z.1 z.2 (x z.1) (y z.2)
  have hzero (z : (V → Fin 3) × (V → Fin 3)) (hz : ¬ P z) : f z=0 := by
    have hn : ¬ DiagonalShape s.val z.1 z.2 := fun h => hz (diagonalShape_pairAvailable U n s h)
    exact (faceCupTerm_apply R d e s.val z.1 z.2 _ _).trans (dite_eq_right hn)
  have he : (∑ z ∈ Finset.univ.filter P, f z) = ∑ z, f z := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z _ hz
    exact hzero z (by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hz)
  have hs : (∑ z ∈ Finset.univ.filter P, f z) =
      ∑ z : PairCellIndex U (binaryCoverFaceOpen U s.val) n, f z.val :=
    Finset.sum_subtype _ (by simp [P]) f
  rw [← hs,he,Fintype.sum_prod_type]
  simp only [faceCupAt,LinearMap.sum_apply,LinearMap.compl₁₂_apply,LinearMap.proj_apply,f]

end
end BPFixedPoints.SheafTools.BinaryCells
