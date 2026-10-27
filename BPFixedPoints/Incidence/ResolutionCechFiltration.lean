import BPFixedPoints.Incidence.ResolutionDegree

/-!
# Nilpotence of Čech-degree-raising operators

Every monomial's Čech degree lies between zero and the vertex count, so an
operator raising it by one vanishes after vertex count plus one iterations.
Complex linearity suffices.
-/

namespace BPFixedPoints.Multigraph

open CechProduct IncidencePerturbation ResolutionTools Finsupp

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

theorem incEnd_pow_zero_of_raises_cech
    (f : Module.End ℂ (IncTotalModule (V := V) (E := E)))
    (hf : Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E)) (fun n => (incCechPiece (V := V) (E := E) n).restrictScalars ℂ)
      (fun n => (incCechPiece (V := V) (E := E) n).restrictScalars ℂ) 1 f) :
    f ^ (Fintype.card V + 1) = 0 := by
  apply Finsupp.lhom_ext'
  intro S
  apply Finsupp.lhom_ext
  intro b r
  have hx : single S (single b r) ∈
      (incCechPiece (V := V) (E := E) (cechDegree b : ℤ)).restrictScalars ℂ :=
    incCechPiece_single S _ (single_mem_supported _ r rfl)
  have h := hf.pow (Fintype.card V + 1) (cechDegree b : ℤ)
    (single S (single b r)) hx
  have hbound : (Fintype.card V : ℤ) <
      (cechDegree b : ℤ) + ((Fintype.card V + 1 : ℕ) : ℤ) * 1 := by omega
  dsimp only at h
  rw [incCechPiece_eq_bot_of_gt_card hbound] at h
  exact h

end BPFixedPoints.Multigraph
