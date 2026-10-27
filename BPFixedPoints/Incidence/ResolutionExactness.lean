import BPFixedPoints.Incidence.KoszulLocalPerturbation

/-!
# Positive-degree exactness of the actual finite free model

The second contraction to local quotients has no positive-degree target,
so positive-degree total cycles are boundaries. Transfer this exactness to
the finite free model by the first chain retraction.
-/

namespace BPFixedPoints.Multigraph

open IncidencePerturbation ResolutionTools Finsupp

set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- A cycle killed by local-quotient projection is a homogeneous boundary. -/
theorem incTotalDifferential_exact_of_projection_zero (n : ℤ)
    (x : IncTotalModule (V := V) (E := E)) (hx : x ∈ incTotalPiece n)
    (hDx : G.incTotalDifferential x = 0) (hpx : G.incKoszulContraction.p x = 0) :
    ∃ y, y ∈ incTotalPiece (n + 1) ∧ G.incTotalDifferential y = x := by
  refine ⟨G.incQuotientHomotopy x, G.incQuotientHomotopy_shifts n x hx, ?_⟩
  have hp' : G.incQuotientProjection x = 0 := by
    rw [G.incQuotientProjection_eq]
    exact hpx
  have he := LinearMap.congr_fun G.incQuotientHomotopy_identity x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.id_apply, hDx, hp', map_zero, add_zero] using he

/-- The total Koszul–Čech complex is exact in positive total degrees. -/
theorem incTotalDifferential_exact {n : ℤ} (hn : 0 < n)
    (x : IncTotalModule (V := V) (E := E)) (hx : x ∈ incTotalPiece n)
    (hDx : G.incTotalDifferential x = 0) :
    ∃ y, y ∈ incTotalPiece (n + 1) ∧ G.incTotalDifferential y = x := by
  apply G.incTotalDifferential_exact_of_projection_zero n x hx hDx
  have hp := G.incKoszulContraction_p_shifts n x hx
  change G.incKoszulContraction.p x ∈ G.incQuotientPiece (n + 0) at hp
  rw [add_zero, G.incQuotientPiece_eq_bot_of_positive hn] at hp
  exact hp

/-- Chain map from the finite free model to the total complex. -/
noncomputable def incResolutionInclusion :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
      IncTotalModule (V := V) (E := E) :=
  G.incCechContraction.inclusion G.incKoszulPerturbation

/-- Chain projection from the total complex to the finite free model. -/
noncomputable def incResolutionProjection :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E]
      (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  G.incCechContraction.projection G.incKoszulPerturbation

noncomputable def incResolutionHomotopy :
    Module.End (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) :=
  G.incCechContraction.contractingHomotopy G.incKoszulPerturbation

theorem incResolutionInclusion_chain :
    G.incTotalDifferential.comp G.incResolutionInclusion =
      G.incResolutionInclusion.comp G.incResolutionDifferential :=
  G.incCechContraction.inclusion_chain G.incKoszulPerturbation
    G.incTotalDifferential_sq G.incKoszulPerturbation_unit_left
    G.incKoszulPerturbation_unit_right

theorem incResolutionProjection_chain :
    G.incResolutionProjection.comp G.incTotalDifferential =
      G.incResolutionDifferential.comp G.incResolutionProjection :=
  G.incCechContraction.projection_chain G.incKoszulPerturbation
    G.incTotalDifferential_sq G.incKoszulPerturbation_unit_left
    G.incKoszulPerturbation_unit_right

theorem incResolutionProjection_inclusion :
    G.incResolutionProjection.comp G.incResolutionInclusion = LinearMap.id :=
  G.incCechContraction.projection_inclusion G.incKoszulPerturbation

theorem incResolutionHomotopy_identity :
    G.incTotalDifferential.comp G.incResolutionHomotopy +
      G.incResolutionHomotopy.comp G.incTotalDifferential +
      G.incResolutionInclusion.comp G.incResolutionProjection = LinearMap.id :=
  G.incCechContraction.perturbed_homotopy G.incKoszulPerturbation
    G.incTotalDifferential_sq G.incKoszulPerturbation_unit_left
    G.incKoszulPerturbation_unit_right

theorem incResolutionInclusion_degree (n : ℕ)
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    G.incResolutionInclusion x ∈ incTotalPiece (n : ℤ) := by
  have hx' : x ∈ G.incResolutionPiece (n : ℤ) := by
    simpa only [incResolutionPiece, gradedPiece, Int.natCast_inj] using hx
  simpa only [incResolutionInclusion, add_zero] using G.incResolutionInclusion_shifts (n : ℤ) x hx'

theorem incResolutionProjection_degree (n : ℕ)
    (x : IncTotalModule (V := V) (E := E)) (hx : x ∈ incTotalPiece (n : ℤ)) :
    G.incResolutionProjection x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n := by
  have h := G.incResolutionProjection_shifts (n : ℤ) x hx
  simpa only [incResolutionProjection, incResolutionPiece, gradedPiece, add_zero, Int.natCast_inj] using h

/-- The actual differential constructed on the state-cohomology basis is exact in positive degrees. -/
theorem incResolutionDifferential_exact (n : ℕ)
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree (n + 1))
    (hdx : G.incResolutionDifferential x = 0) :
    ∃ y, y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree (n + 2) ∧
      G.incResolutionDifferential y = x := by
  have hix : G.incTotalDifferential (G.incResolutionInclusion x) = 0 := by
    calc
      _ = G.incResolutionInclusion (G.incResolutionDifferential x) :=
        LinearMap.congr_fun G.incResolutionInclusion_chain x
      _ = 0 := by rw [hdx, map_zero]
  obtain ⟨y, hy, hDy⟩ := G.incTotalDifferential_exact (n := ((n + 1 : ℕ) : ℤ)) (by omega)
    (G.incResolutionInclusion x) (G.incResolutionInclusion_degree (n + 1) x hx) hix
  have hy' : y ∈ incTotalPiece ((n + 2 : ℕ) : ℤ) := by
    have hn : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
    simpa only [hn] using hy
  refine ⟨G.incResolutionProjection y, G.incResolutionProjection_degree (n + 2) y hy', ?_⟩
  calc
    _ = G.incResolutionProjection (G.incTotalDifferential y) :=
      (LinearMap.congr_fun G.incResolutionProjection_chain y).symm
    _ = G.incResolutionProjection (G.incResolutionInclusion x) := by rw [hDy]
    _ = x := LinearMap.congr_fun G.incResolutionProjection_inclusion x

end BPFixedPoints.Multigraph
