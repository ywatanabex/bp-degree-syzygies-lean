import BPFixedPoints.Incidence.CechCubicalPairContraction

/-! # The original tensor prism stays inside the original face pairs -/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct GradedContraction
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type*) [CommRing R] {V : Type} [Fintype V]

/-- Original pairs of subfaces of the same original rectangular face. -/
def pairSubfaces (s : V → Fin 3) : Submodule R (CellPairs R V) :=
  supported R R {z | FaceRefines z.1 s ∧ FaceRefines z.2 s}

/-- Native tensor pair coordinates retain exactly the original support of both factors. -/
theorem pairCoordinates_tmul_subfaces (s : V → Fin 3) (x y : Cells R V)
    (hx : x ∈ subfaces R s) (hy : y ∈ subfaces R s) :
    pairCoordinates R V (x ⊗ₜ[R] y) ∈ pairSubfaces R s := by
  intro z hz
  have hc := Finsupp.mem_support_iff.mp hz
  rw [show pairCoordinates R V (x ⊗ₜ[R] y) z = x z.1*y z.2 from
    finsuppTensorFinsupp'_apply_apply R _ _ x y z.1 z.2] at hc
  exact ⟨hx (Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hc)),
    hy (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hc))⟩

/-- On each original pair generator, both terms of the original tensor prism stay in the same original face. -/
theorem pairContraction_h_single_subfaces (b : V → Fin 2) (s p q : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) s) (hp : FaceRefines p s) (hq : FaceRefines q s) (r : R) :
    (pairContraction R V b).h (single (p,q) r) ∈ pairSubfaces R s := by
  rw [pairContraction,GradedContraction.congr_h_apply]
  change pairCoordinates R V (((contraction R b).tensor (contraction R b)).h
    ((finsuppTensorFinsupp' R _ _).symm (single (p,q) r))) ∈ _
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul,tensor_h_apply,TensorProduct.map_tmul,
    TensorProduct.map_tmul,Module.End.one_apply,map_add]
  apply Submodule.add_mem
  · exact pairCoordinates_tmul_subfaces R s _ _
      (contraction_h_single_subfaces R b s p 1 hb hp) (single_mem_supported R r hq)
  · apply pairCoordinates_tmul_subfaces R s
    · change (contraction R b).i ((contraction R b).p ((contraction R b).sign (single p 1))) ∈ subfaces R s
      exact contraction_i_subfaces R b s hb _
    · exact contraction_h_single_subfaces R b s q r hb hq

/-- The original tensor prism preserves every original face-supported pair chain. -/
theorem pairContraction_h_subfaces (b : V → Fin 2) (s : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) s) (x : CellPairs R V) (hx : x ∈ pairSubfaces R s) :
    (pairContraction R V b).h x ∈ pairSubfaces R s := by
  rw [← x.sum_single,map_finsuppSum]
  apply Submodule.sum_mem
  intro z hz
  exact pairContraction_h_single_subfaces R b s z.1 z.2 hb (hx hz).1 (hx hz).2 (x z)

end
end BPFixedPoints.CechCubicalCell
