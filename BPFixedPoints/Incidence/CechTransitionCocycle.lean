import BPFixedPoints.Incidence.CechFaceTransitionUnits

/-! # Cocycle law for the original homogeneous-coordinate transition units

These are explicit units in the ambient face rings. The cocycle is proved from
actual refinement of Laurent variables, before passing to any quotient or sheaf.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V] (R : Type*) [CommRing R]

/-- A Laurent coordinate stays the same unit under every further refinement. -/
theorem faceLaurentUnit_refinement {q r : V → Fin 3} (h : FaceRefines q r) (v : V)
    (hq : q v = 2) (hr : r v = 2) :
    Units.map (faceRefinementMap R h).toMonoidHom (faceLaurentUnit R q v hq) =
      faceLaurentUnit R r v hr := by
  apply Units.ext
  change faceRefinementMap R h (faceVariable R q v) = faceVariable R r v
  rw [faceRefinement_variable, dif_neg (by omega)]

/-- Original homogeneous-coordinate trivializations satisfy the cocycle law
on every triple of actual polynomial/Laurent face refinements. -/
theorem faceTransitionUnit_cocycle {q r s : V → Fin 3}
    (hqr : FaceRefines q r) (hrs : FaceRefines r s) (v : V) :
    Units.map (faceRefinementMap R hrs).toMonoidHom (faceTransitionUnit R hqr v) *
      faceTransitionUnit R hrs v = faceTransitionUnit R (faceRefines_trans hqr hrs) v := by
  have h₁ := hqr v
  have h₂ := hrs v
  by_cases hf : q v = 1 ∧ r v = 2
  · have hs : s v = 2 := by omega
    have hn : ¬(r v = 1 ∧ s v = 2) := by omega
    have ht : q v = 1 ∧ s v = 2 := ⟨hf.1, hs⟩
    simp only [faceTransitionUnit, dif_pos hf, dif_neg hn, dif_pos ht,
      map_inv, mul_one]
    rw [faceLaurentUnit_refinement R hrs v hf.2 hs]
  · by_cases hg : r v = 1 ∧ s v = 2
    · have hq : q v = 1 := by omega
      have ht : q v = 1 ∧ s v = 2 := ⟨hq, hg.2⟩
      simp only [faceTransitionUnit, dif_neg hf, dif_pos hg, dif_pos ht, map_one, one_mul]
    · have ht : ¬(q v = 1 ∧ s v = 2) := by omega
      simp only [faceTransitionUnit, dif_neg hf, dif_neg hg, dif_neg ht, map_one, one_mul]

end BPFixedPoints.CechProduct
