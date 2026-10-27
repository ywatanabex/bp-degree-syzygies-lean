import BPFixedPoints.Incidence.ResolutionExactness

/-!
# Degree-zero local-quotient cycles and the finite free model

Reduce the degree-zero kernel and surjectivity to local-quotient Čech cycles.
Use only the two constructed contractions here, without assuming coefficient
ring or chart gluing identifications.
-/

namespace BPFixedPoints.Multigraph

open IncidencePerturbation ResolutionTools Finsupp

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Positive-degree free-model terms vanish under chain projection to local quotients. -/
theorem incResolution_toQuotient_eq_zero_of_positive (n : ℕ)
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree (n + 1)) :
    G.incKoszulContraction.p (G.incResolutionInclusion x) = 0 := by
  have hp := G.incKoszulContraction_p_shifts ((n + 1 : ℕ) : ℤ)
    (G.incResolutionInclusion x) (G.incResolutionInclusion_degree (n + 1) x hx)
  change G.incKoszulContraction.p (G.incResolutionInclusion x) ∈
    G.incQuotientPiece (((n + 1 : ℕ) : ℤ) + 0) at hp
  rw [G.incQuotientPiece_eq_bot_of_positive (by omega)] at hp
  exact hp

/-- The degree-zero kernel equals the local-quotient projection kernel. -/
theorem incResolutionDifferential_exact_zero_of_projection_zero
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incKoszulContraction.p (G.incResolutionInclusion x) = 0 ↔
      ∃ y, y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 1 ∧
        G.incResolutionDifferential y = x := by
  constructor
  · intro hp
    have hix : G.incTotalDifferential (G.incResolutionInclusion x) = 0 := by
      calc
        _ = G.incResolutionInclusion (G.incResolutionDifferential x) :=
          LinearMap.congr_fun G.incResolutionInclusion_chain x
        _ = 0 := by rw [G.incResolutionDifferential_zero_degree x hx, map_zero]
    obtain ⟨y, hy, hDy⟩ := G.incTotalDifferential_exact_of_projection_zero 0
      (G.incResolutionInclusion x) (G.incResolutionInclusion_degree 0 x hx) hix hp
    refine ⟨G.incResolutionProjection y, G.incResolutionProjection_degree 1 y hy, ?_⟩
    calc
      _ = G.incResolutionProjection (G.incTotalDifferential y) :=
        (LinearMap.congr_fun G.incResolutionProjection_chain y).symm
      _ = G.incResolutionProjection (G.incResolutionInclusion x) := by rw [hDy]
      _ = x := LinearMap.congr_fun G.incResolutionProjection_inclusion x
  · rintro ⟨y, hy, hDy⟩
    have hp := G.incResolution_toQuotient_eq_zero_of_positive 0 y hy
    have hchain := LinearMap.congr_fun G.incQuotientProjection_chain
      (G.incResolutionInclusion y)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hchain
    have hI : G.incTotalDifferential (G.incResolutionInclusion y) =
        G.incResolutionInclusion (G.incResolutionDifferential y) :=
      LinearMap.congr_fun G.incResolutionInclusion_chain y
    rw [G.incQuotientProjection_eq, hI, hDy, hp, map_zero] at hchain
    exact hchain

/-- Degree-zero cycles in local quotients lift to degree zero of the finite free model. -/
theorem exists_incResolution_lift_quotientCycle
    (q : G.IncQuotientCechModule) (hq : q ∈ G.incQuotientPiece 0)
    (hdq : G.incQuotientDifferential q = 0) :
    ∃ x, x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 ∧
      G.incKoszulContraction.p (G.incResolutionInclusion x) = q := by
  let y := G.incQuotientInclusion q
  have hy : y ∈ incTotalPiece (V := V) (E := E) 0 := by
    simpa only [add_zero, Submodule.restrictScalars_mem] using G.incQuotientInclusion_shifts 0 q hq
  have hDy : G.incTotalDifferential y = 0 := by
    have h := LinearMap.congr_fun G.incQuotientInclusion_chain q
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hdq, map_zero] using h
  have hph : G.incQuotientProjection (G.incResolutionHomotopy y) = 0 := by
    have hh : G.incResolutionHomotopy y ∈ incTotalPiece (V := V) (E := E) 1 :=
      G.incResolutionHomotopy_shifts 0 y hy
    have hp := G.incQuotientProjection_shifts 1 (G.incResolutionHomotopy y) hh
    change G.incQuotientProjection (G.incResolutionHomotopy y) ∈ G.incQuotientPiece (1 + 0) at hp
    rw [G.incQuotientPiece_eq_bot_of_positive (by norm_num)] at hp
    exact hp
  have hpDh : G.incQuotientProjection
      (G.incTotalDifferential (G.incResolutionHomotopy y)) = 0 := by
    have h := LinearMap.congr_fun G.incQuotientProjection_chain (G.incResolutionHomotopy y)
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hph, map_zero] using h
  have hpy : G.incQuotientProjection y = q := by
    have h := LinearMap.congr_fun G.incQuotientProjection_inclusion q
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  refine ⟨G.incResolutionProjection y, G.incResolutionProjection_degree 0 y hy, ?_⟩
  have he := congrArg G.incQuotientProjection
    (LinearMap.congr_fun G.incResolutionHomotopy_identity y)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hDy, map_zero, add_zero, map_add, hpDh, hpy] at he
  rw [G.incQuotientProjection_eq] at he
  funext q'
  have heq := congrArg (fun z : G.IncQuotientCechModule => z q') he
  simpa only [Pi.add_apply, Pi.zero_apply, zero_add] using heq

end BPFixedPoints.Multigraph
