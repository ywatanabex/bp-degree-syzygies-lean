import BPFixedPoints.Incidence.CechZeroDegrees
import BPFixedPoints.Incidence.KoszulLocalPerturbation
import BPFixedPoints.Incidence.KoszulFaceRestriction
import BPFixedPoints.Incidence.KoszulFaceChartTorus
import BPFixedPoints.Incidence.ChartSections

/-!
# Čech degree-zero kernel of local quotients and the original incidence ring

Identify the degree-zero perturbed boundary on local Koszul quotients with
the difference of actual adjacent-chart restrictions. Injectivity into the
common torus makes its kernel exactly the existing compatible chart sections.
-/

namespace BPFixedPoints.Multigraph

open CechProduct Finsupp

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incQuotientDifferential_apply (y : G.IncQuotientCechModule) (q : V → Fin 3) :
    G.incQuotientDifferential y q =
      Ideal.Quotient.mk (G.incFaceIdeal q)
        (polynomialFaceEquiv ℂ (IncCoeffIdx E)
          ((contraction (IncCoeffRing E) (G.deg ∅)).d ((G.incKoszulContraction.i y) ∅)) q) := by
  rw [G.incQuotientDifferential_eq, LinearMap.comp_apply, LinearMap.comp_apply,
    incCechPerturbation, LinearMap.restrictScalars_apply,
    G.incKoszulContraction_p, G.incCechContraction_d_apply]

/-- The quotient Čech differential has no degree-zero chart component. -/
theorem incQuotientDifferential_chartFace (y : G.IncQuotientCechModule) (σ : V → Bool) :
    G.incQuotientDifferential y (chartFace σ) = 0 := by
  rw [G.incQuotientDifferential_apply, polynomialFaceEquiv_contraction_d_chart, map_zero]

theorem incQuotientLift_map (y : G.IncQuotientCechModule) (q : V → Fin 3) :
    Ideal.Quotient.mk (G.incFaceIdeal q)
      (polynomialFaceEquiv ℂ (IncCoeffIdx E) ((G.incKoszulContraction.i y) ∅) q) = y q := by
  have h := congrFun (LinearMap.congr_fun G.incKoszulContraction.p_i y) q
  change G.incKoszulContraction.p (G.incKoszulContraction.i y) q = y q at h
  rw [G.incKoszulContraction_p] at h
  exact h

theorem incQuotientLift_empty_degree_zero (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) :
    (G.incKoszulContraction.i y) ∅ ∈ supported (IncCoeffRing E) (IncCoeffRing E)
      {b | (cechDegree b : ℤ) = 0} := by
  have h := G.incKoszulContraction_i_shifts 0 y hy
  have h0 := h (∅ : Finset E)
  simpa using h0

/-- The boundary of degree-zero quotient sections is the difference of actual adjacent quotient-chart restrictions. -/
theorem incQuotientDifferential_overlap (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) (σ : V → Bool) (v : V) :
    G.incQuotientDifferential y (overlapFace σ v) =
      G.incFaceRestriction σ v true (y (chartFace (Function.update σ v true))) -
        G.incFaceRestriction σ v false (y (chartFace (Function.update σ v false))) := by
  let w := (G.incKoszulContraction.i y) ∅
  have hw := G.incQuotientLift_empty_degree_zero y hy
  have hz := polynomialZeroCharts_reconstruct ℂ (IncCoeffIdx E) w hw
  have hb := polynomialFaceEquiv_d_zeroCharts ℂ (IncCoeffIdx E) σ v
    (fun τ => polynomialFaceEquiv ℂ (IncCoeffIdx E) w (chartFace τ))
  rw [hz] at hb
  have hd : G.deg ∅ = (fun _ : V => 0) := funext (G.deg_empty)
  rw [G.incQuotientDifferential_apply, hd]
  change Ideal.Quotient.mk _
    (polynomialFaceEquiv ℂ (IncCoeffIdx E) ((contraction (IncCoeffRing E) (fun _ => 0)).d w)
      (overlapFace σ v)) = _
  rw [hb, map_sub, ← G.incFaceRestriction_mk, ← G.incFaceRestriction_mk]
  rw [G.incQuotientLift_map, G.incQuotientLift_map]

theorem incQuotientDifferential_zero_mem (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) :
    G.incQuotientDifferential y ∈ G.incQuotientPiece (-1) := by
  have hi := G.incKoszulContraction_i_shifts 0 y hy
  have hd := G.incCechContraction_d_shifts 0 (G.incKoszulContraction.i y) hi
  have hp := G.incKoszulContraction_p_shifts (-1)
    (G.incCechContraction.d (G.incKoszulContraction.i y)) (by simpa using hd)
  simpa only [add_zero, incQuotientDifferential_eq, LinearMap.comp_apply,
    incCechPerturbation, LinearMap.restrictScalars_apply] using hp

noncomputable def incQuotientChartSections (y : G.IncQuotientCechModule) :
    (σ : V → Bool) → G.IncChartRing σ :=
  fun σ => G.incFaceChartEquiv σ (y (chartFace σ))

/-- A degree-zero quotient section is closed iff its original chart sections are compatible. -/
theorem incQuotientDifferential_eq_zero_iff_compatible (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) :
    G.incQuotientDifferential y = 0 ↔ G.incQuotientChartSections y ∈ G.CompatibleCharts := by
  constructor
  · intro h
    apply G.compatibleCharts_of_adjacent
    intro σ v
    have he := congrArg (G.incFaceToTorus (overlapFace σ v)) (congrFun h (overlapFace σ v))
    rw [G.incQuotientDifferential_overlap y hy, map_sub, Pi.zero_apply, map_zero,
      G.incFaceToTorus_restriction, G.incFaceToTorus_restriction,
      G.incFaceToTorus_chartFace_apply, G.incFaceToTorus_chartFace_apply] at he
    exact (sub_eq_zero.mp he).symm
  · intro h
    funext q
    by_cases hq : faceDegree q = 1
    · obtain ⟨σ, v, rfl⟩ := (faceDegree_eq_one_iff q).mp hq
      rw [G.incQuotientDifferential_overlap y hy]
      apply G.incFaceToTorus_injective (overlapFace σ v)
      rw [map_sub, Pi.zero_apply, map_zero, G.incFaceToTorus_restriction, G.incFaceToTorus_restriction,
        G.incFaceToTorus_chartFace_apply, G.incFaceToTorus_chartFace_apply]
      exact sub_eq_zero.mpr (h (Function.update σ v true) (Function.update σ v false))
    · exact (G.incQuotientDifferential_zero_mem y hy) q (by omega)

theorem incQuotientCycle_torus_eq (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) (hdy : G.incQuotientDifferential y = 0)
    (σ τ : V → Bool) :
    G.incFaceToTorus (chartFace σ) (y (chartFace σ)) =
      G.incFaceToTorus (chartFace τ) (y (chartFace τ)) := by
  rw [G.incFaceToTorus_chartFace_apply, G.incFaceToTorus_chartFace_apply]
  exact ((G.incQuotientDifferential_eq_zero_iff_compatible y hy).mp hdy) σ τ

/-- The common value of a degree-zero quotient cycle belongs to the defined incidence ring. -/
theorem incQuotientCycle_torus_mem (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) (hdy : G.incQuotientDifferential y = 0) :
    G.incFaceToTorus (chartFace (fun _ => false)) (y (chartFace (fun _ => false))) ∈
      G.IncidenceRing := by
  rw [IncidenceRing, Algebra.mem_iInf]
  intro σ
  refine ⟨G.incQuotientChartSections y σ, ?_⟩
  change G.incChartMap σ (G.incFaceChartEquiv σ (y (chartFace σ))) = _
  rw [← G.incFaceToTorus_chartFace_apply]
  exact G.incQuotientCycle_torus_eq y hy hdy σ (fun _ => false)

/-- A degree-zero quotient cycle with zero common value is zero. -/
theorem incQuotientCycle_eq_zero_of_torus_eq_zero (y : G.IncQuotientCechModule)
    (hy : y ∈ G.incQuotientPiece 0) (hdy : G.incQuotientDifferential y = 0)
    (h0 : G.incFaceToTorus (chartFace (fun _ => false))
      (y (chartFace (fun _ => false))) = 0) : y = 0 := by
  funext q
  by_cases hq : faceDegree q = 0
  · obtain ⟨σ, rfl⟩ := (faceDegree_eq_zero_iff q).mp hq
    apply G.incFaceToTorus_injective (chartFace σ)
    rw [Pi.zero_apply, map_zero, G.incQuotientCycle_torus_eq y hy hdy σ (fun _ => false), h0]
  · exact hy q (by omega)

/-- Insert a family of degree-zero quotient-chart sections, setting positive-degree faces to zero. -/
noncomputable def incQuotientZeroCharts
    (x : (σ : V → Bool) → G.IncFaceRing (chartFace σ)) : G.IncQuotientCechModule := by
  classical
  exact ∑ σ, Pi.single (chartFace σ) (x σ)

@[simp] theorem incQuotientZeroCharts_chart
    (x : (σ : V → Bool) → G.IncFaceRing (chartFace σ)) (σ : V → Bool) :
    G.incQuotientZeroCharts x (chartFace σ) = x σ := by
  classical
  rw [incQuotientZeroCharts, Finset.sum_apply, Finset.sum_eq_single σ]
  · exact Pi.single_eq_same _ _
  · intro τ _ hτ
    apply Pi.single_eq_of_ne
    intro hh
    exact hτ (chartFace_injective hh.symm)
  · simp

theorem incQuotientZeroCharts_mem
    (x : (σ : V → Bool) → G.IncFaceRing (chartFace σ)) :
    G.incQuotientZeroCharts x ∈ G.incQuotientPiece 0 := by
  intro q hq
  rw [incQuotientZeroCharts, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro σ _
  apply Pi.single_eq_of_ne
  intro hh
  exact hq (by simp [hh])

/-- Each original incidence-ring element is the common value of a degree-zero quotient Čech cycle. -/
theorem exists_incQuotientCycle_of_incidence (u : G.IncidenceRing) :
    ∃ y : G.IncQuotientCechModule, y ∈ G.incQuotientPiece 0 ∧
      G.incQuotientDifferential y = 0 ∧
      G.incFaceToTorus (chartFace (fun _ => false)) (y (chartFace (fun _ => false))) = u.val := by
  let c := G.incidenceRingEquivCompatibleCharts u
  let x := fun σ => (G.incFaceChartEquiv σ).symm (c.val σ)
  let y := G.incQuotientZeroCharts x
  have hy : y ∈ G.incQuotientPiece 0 := G.incQuotientZeroCharts_mem x
  have hc : G.incQuotientChartSections y = c.val := by
    funext σ
    change G.incFaceChartEquiv σ (G.incQuotientZeroCharts x (chartFace σ)) = c.val σ
    rw [G.incQuotientZeroCharts_chart]
    exact AlgEquiv.apply_symm_apply _ _
  refine ⟨y, hy, (G.incQuotientDifferential_eq_zero_iff_compatible y hy).mpr ?_, ?_⟩
  · rw [hc]
    exact c.property
  · rw [G.incFaceToTorus_chartFace_apply]
    change G.incChartMap (fun _ => false) (G.incQuotientChartSections y (fun _ => false)) = u.val
    rw [hc]
    exact G.incidenceRingEquivCompatibleCharts_map u (fun _ => false)

end BPFixedPoints.Multigraph
