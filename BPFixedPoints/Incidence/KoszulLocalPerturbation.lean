import BPFixedPoints.Incidence.KoszulLocalDegree
import BPFixedPoints.Incidence.ResolutionCechFiltration
import BPFixedPoints.Incidence.ResolutionHomotopy

/-!
# Finite perturbation to the Čech complex of local quotients

Add the Čech differential to the Koszul strong contraction. Local homotopy
preserves faces while the Čech differential raises face degree by one, so
perturbation terminates by the vertex count. Projection remains the original
map taking the empty exterior coefficient to its quotient.
-/

namespace BPFixedPoints.Multigraph

open CechProduct IncidencePerturbation ResolutionTools Finsupp

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable def incCechPerturbation :
    Module.End ℂ (IncTotalModule (V := V) (E := E)) :=
  G.incCechContraction.d.restrictScalars ℂ

theorem incLocalTotalDifferential :
    G.incKoszulContraction.d + G.incCechPerturbation =
      G.incTotalDifferential.restrictScalars ℂ := by
  rw [G.incKoszulContraction_d]
  apply LinearMap.ext
  intro x
  change G.incKoszulPerturbation x + G.incCechContraction.d x =
    G.incCechContraction.d x + G.incKoszulPerturbation x
  exact add_comm _ _

theorem incLocalTotalDifferential_sq :
    (G.incKoszulContraction.d + G.incCechPerturbation) *
      (G.incKoszulContraction.d + G.incCechPerturbation) = 0 := by
  rw [G.incLocalTotalDifferential]
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun G.incTotalDifferential_sq x

theorem incCechPerturbation_h_nilpotent :
    (G.incCechPerturbation * G.incKoszulContraction.h) ^ (Fintype.card V + 1) = 0 := by
  apply incEnd_pow_zero_of_raises_cech
  simpa only [Module.End.mul_eq_comp, zero_add, incCechPerturbation] using
    (G.incCechContraction_d_cechShifts.restrictScalars (K := ℂ)).comp
      G.incKoszulContraction_h_cechShifts

theorem incCechPerturbation_unit_left :
    IsUnit (1 + G.incCechPerturbation * G.incKoszulContraction.h) := by
  letI : Ring (Module.End ℂ (IncTotalModule (V := V) (E := E))) :=
    Module.End.instRing (R := ℂ) (N₁ := IncTotalModule (V := V) (E := E))
  exact (show IsNilpotent (G.incCechPerturbation * G.incKoszulContraction.h)
    from ⟨_, G.incCechPerturbation_h_nilpotent⟩).isUnit_one_add

theorem incCechPerturbation_unit_right :
    IsUnit (1 + G.incKoszulContraction.h * G.incCechPerturbation) := by
  letI : Ring (Module.End ℂ (IncTotalModule (V := V) (E := E))) :=
    Module.End.instRing (R := ℂ) (N₁ := IncTotalModule (V := V) (E := E))
  have hn : IsNilpotent (G.incKoszulContraction.h * G.incCechPerturbation) :=
    nilpotent_mul_swap G.incCechPerturbation G.incKoszulContraction.h
      ⟨_, G.incCechPerturbation_h_nilpotent⟩
  exact hn.isUnit_one_add

/-- Empty-exterior projection kills the Čech differential after local homotopy. -/
theorem incKoszulContraction_p_cech_h :
    G.incKoszulContraction.p.comp
      (G.incCechPerturbation.comp G.incKoszulContraction.h) = 0 := by
  apply LinearMap.ext
  intro x
  funext q
  change G.incKoszulContraction.p
    (G.incCechContraction.d (G.incKoszulContraction.h x)) q = 0
  rw [G.incKoszulContraction_p, G.incCechContraction_d_apply,
    G.incKoszulContraction_h_empty, map_zero, map_zero]
  rfl

noncomputable def incQuotientDifferential : Module.End ℂ G.IncQuotientCechModule :=
  G.incKoszulContraction.transfer G.incCechPerturbation

noncomputable def incQuotientInclusion :
    G.IncQuotientCechModule →ₗ[ℂ] IncTotalModule (V := V) (E := E) :=
  G.incKoszulContraction.inclusion G.incCechPerturbation

noncomputable def incQuotientProjection :
    IncTotalModule (V := V) (E := E) →ₗ[ℂ] G.IncQuotientCechModule :=
  G.incKoszulContraction.projection G.incCechPerturbation

noncomputable def incQuotientHomotopy :
    Module.End ℂ (IncTotalModule (V := V) (E := E)) :=
  G.incKoszulContraction.contractingHomotopy G.incCechPerturbation

theorem incQuotientProjection_eq :
    G.incQuotientProjection = G.incKoszulContraction.p :=
  G.incKoszulContraction.projection_eq_of_perturbation_homotopy_zero
    G.incCechPerturbation G.incCechPerturbation_unit_left G.incKoszulContraction_p_cech_h

theorem incQuotientDifferential_eq :
    G.incQuotientDifferential = G.incKoszulContraction.p.comp
      (G.incCechPerturbation.comp G.incKoszulContraction.i) :=
  G.incKoszulContraction.transfer_eq_of_perturbation_homotopy_zero
    G.incCechPerturbation G.incCechPerturbation_unit_left G.incKoszulContraction_p_cech_h

theorem incQuotientDifferential_sq :
    G.incQuotientDifferential * G.incQuotientDifferential = 0 :=
  G.incKoszulContraction.transfer_sq G.incCechPerturbation
    G.incLocalTotalDifferential_sq G.incCechPerturbation_unit_left
    G.incCechPerturbation_unit_right

theorem incQuotientInclusion_chain :
    (G.incTotalDifferential.restrictScalars ℂ).comp G.incQuotientInclusion =
      G.incQuotientInclusion.comp G.incQuotientDifferential := by
  rw [← G.incLocalTotalDifferential]
  exact G.incKoszulContraction.inclusion_chain G.incCechPerturbation
    G.incLocalTotalDifferential_sq G.incCechPerturbation_unit_left
    G.incCechPerturbation_unit_right

theorem incQuotientProjection_chain :
    G.incQuotientProjection.comp (G.incTotalDifferential.restrictScalars ℂ) =
      G.incQuotientDifferential.comp G.incQuotientProjection := by
  rw [← G.incLocalTotalDifferential]
  exact G.incKoszulContraction.projection_chain G.incCechPerturbation
    G.incLocalTotalDifferential_sq G.incCechPerturbation_unit_left
    G.incCechPerturbation_unit_right

theorem incQuotientProjection_inclusion :
    G.incQuotientProjection.comp G.incQuotientInclusion = LinearMap.id :=
  G.incKoszulContraction.projection_inclusion G.incCechPerturbation

theorem incQuotientHomotopy_identity :
    (G.incTotalDifferential.restrictScalars ℂ).comp G.incQuotientHomotopy +
      G.incQuotientHomotopy.comp (G.incTotalDifferential.restrictScalars ℂ) +
      G.incQuotientInclusion.comp G.incQuotientProjection = LinearMap.id := by
  rw [← G.incLocalTotalDifferential]
  exact G.incKoszulContraction.perturbed_homotopy G.incCechPerturbation
    G.incLocalTotalDifferential_sq G.incCechPerturbation_unit_left
    G.incCechPerturbation_unit_right

theorem incQuotientInclusion_shifts :
    Shifts (R := ℂ) (M := G.IncQuotientCechModule)
      (N := IncTotalModule (V := V) (E := E)) G.incQuotientPiece
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      0 G.incQuotientInclusion :=
  G.incKoszulContraction.inclusion_shifts G.incCechPerturbation
    (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ) G.incQuotientPiece
    (G.incCechContraction_d_shifts.restrictScalars (K := ℂ))
    G.incKoszulContraction_h_shifts G.incKoszulContraction_i_shifts
    ⟨_, G.incCechPerturbation_h_nilpotent⟩

theorem incQuotientProjection_shifts :
    Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := G.IncQuotientCechModule)
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      G.incQuotientPiece 0 G.incQuotientProjection := by
  rw [G.incQuotientProjection_eq]
  exact G.incKoszulContraction_p_shifts

theorem incQuotientHomotopy_shifts :
    Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      1 G.incQuotientHomotopy :=
  G.incKoszulContraction.contractingHomotopy_shifts G.incCechPerturbation
    (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
    (G.incCechContraction_d_shifts.restrictScalars (K := ℂ))
    G.incKoszulContraction_h_shifts ⟨_, G.incCechPerturbation_h_nilpotent⟩

end BPFixedPoints.Multigraph
