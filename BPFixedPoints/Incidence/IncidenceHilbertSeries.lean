import BPFixedPoints.Incidence.GradedResolutionDimensions
import BPFixedPoints.Incidence.HilbertSeriesTools
import BPFixedPoints.Incidence.Omega

/-!
# Hilbert series of the original incidence ring

Define the series from actual dimensions of the natural graded pieces on all
charts. Prove the θ and ω̃ formulas using the degreewise exact free resolution.
-/

namespace BPFixedPoints.Multigraph
open ResolutionTools
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Hilbert series of the original naturally graded ring, defined independently of the dimension formula. -/
noncomputable def incidenceHilbertSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank ℂ (G.incidenceCoefficientPiece n) : ℤ)

noncomputable def incFreeTermHilbertSeries (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank ℂ (G.incFreeTermInternalPiece p n) : ℤ)

theorem incFreeTermHilbertSeries_eq (p : ℕ) :
    G.incFreeTermHilbertSeries p =
      ∑ b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p},
        PowerSeries.X ^ G.incResolutionInternalDegree b.val *
          (PowerSeries.invOneSubPow ℤ (4 * Fintype.card E)).val := by
  have hcard : Fintype.card (IncCoeffIdx E) = 4 * Fintype.card E := by
    simp only [IncCoeffIdx, Fintype.card_prod, Fintype.card_fin]
    omega
  have he : G.incFreeTermHilbertSeries p = PowerSeries.mk (fun n : ℕ =>
      (Module.finrank ℂ (weightedFreePiece (σ := IncCoeffIdx E) (k := ℂ)
        (fun b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p} =>
          G.incResolutionInternalDegree b.val) n) : ℤ)) := by
    ext n
    simp only [incFreeTermHilbertSeries, PowerSeries.coeff_mk]
    rw [(G.incFreeTermInternalEquivWeighted p n).finrank_eq]
  rw [he, weightedFreePiece_hilbert, hcard]

theorem incidenceHilbertSeries_euler :
    G.incidenceHilbertSeries = ∑ p ∈ Finset.range (G.rho + 1),
      PowerSeries.C ((-1 : ℤ) ^ p) * G.incFreeTermHilbertSeries p := by
  ext n
  simp only [incidenceHilbertSeries, incFreeTermHilbertSeries, PowerSeries.coeff_mk,
    map_sum, PowerSeries.coeff_C_mul]
  exact G.incidenceCoefficientPiece_euler n

/-- θ is the alternating numerator obtained from all basis elements of the actual resolution. -/
theorem thetaTwoI_eq_resolution_basis : G.thetaTwoI =
    ∑ b : G.IncResolutionBasis,
      Polynomial.C ((-1 : ℤ) ^ G.incResolutionDegree b) *
        Polynomial.X ^ G.incResolutionInternalDegree b := by
  classical
  rw [G.thetaTwoI_eq_alternating, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  simp only [incResolutionDegree, incResolutionInternalDegree, Finset.sum_const,
    Finset.card_univ, Fintype.card_pi, Fintype.card_fin, nsmul_eq_mul,
    wt, Polynomial.C_mul, map_natCast]
  ring

/-- Hilbert series of the original ring from the degreewise Euler formula of the free resolution. -/
theorem incidenceHilbertSeries_eq_theta : G.incidenceHilbertSeries =
    (G.thetaTwoI : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (4 * Fintype.card E)).val := by
  classical
  rw [G.incidenceHilbertSeries_euler, G.thetaTwoI_eq_resolution_basis]
  simp only [G.incFreeTermHilbertSeries_eq, Finset.mul_sum, ← mul_assoc]
  have hf (p : ℕ) :
      (∑ b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p},
        PowerSeries.C ((-1 : ℤ) ^ p) * PowerSeries.X ^ G.incResolutionInternalDegree b.val *
          (PowerSeries.invOneSubPow ℤ (4 * Fintype.card E)).val) =
      ∑ b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p},
        PowerSeries.C ((-1 : ℤ) ^ G.incResolutionDegree b.val) *
          PowerSeries.X ^ G.incResolutionInternalDegree b.val *
            (PowerSeries.invOneSubPow ℤ (4 * Fintype.card E)).val := by
    apply Finset.sum_congr rfl
    intro b _
    rw [b.property]
  simp_rw [hf]
  rw [sum_finite_weight_fibres G.incResolutionDegree G.rho G.incResolutionDegree_le
    (fun b => PowerSeries.C ((-1 : ℤ) ^ G.incResolutionDegree b) *
      PowerSeries.X ^ G.incResolutionInternalDegree b *
        (PowerSeries.invOneSubPow ℤ (4 * Fintype.card E)).val)]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X, Finset.sum_mul]

/-- Hilbert numerator equality after multiplication by the denominator, including the zero-edge case. -/
theorem incidenceHilbertSeries_numerator :
    (1 - PowerSeries.X : PowerSeries ℤ) ^ (4 * Fintype.card E) * G.incidenceHilbertSeries =
      (G.thetaTwoI : PowerSeries ℤ) := by
  rw [G.incidenceHilbertSeries_eq_theta, mul_left_comm,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  simp

/-- Hilbert-series expression in dimension d_G with the tree-component correction. -/
theorem incidenceHilbertSeries_eq_omegaTilde : G.incidenceHilbertSeries =
    (G.omegaTilde : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ G.dG).val := by
  rw [G.incidenceHilbertSeries_eq_theta, G.thetaTwoI_eq_omegaTilde]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_X]
  rw [mul_right_comm, ← G.dG_add_rho,
    PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
  exact mul_comm _ _

/-- Express the universal ring's Hilbert series using the original ω, including tree components. -/
theorem incidenceHilbertSeries_eq_omega : G.incidenceHilbertSeries =
    (G.omega : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (3 * Fintype.card E + Fintype.card V)).val := by
  have hdim : G.dG + G.tau = 3 * Fintype.card E + Fintype.card V := by
    have ht := G.tau_le_numComponents
    have hc := G.numComponents_le
    unfold dG
    omega
  rw [G.incidenceHilbertSeries_eq_omegaTilde, omega]
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_one, Polynomial.coe_X]
  rw [mul_right_comm, ← hdim,
    PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
  exact mul_comm _ _

@[simp] theorem thetaTwoI_coeff_zero : G.thetaTwoI.coeff 0 = 1 := by
  classical
  rw [G.coeff_thetaTwoI]
  have he : Finset.univ.filter (fun S : Finset E => S.card = 0) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero,
      Finset.mem_singleton]
  rw [he]
  simp

/-- The actual ring component of degree zero is one-dimensional. -/
theorem finrank_incidenceCoefficientPiece_zero :
    Module.finrank ℂ (G.incidenceCoefficientPiece 0) = 1 := by
  have h := congrArg (PowerSeries.coeff 0) G.incidenceHilbertSeries_eq_theta
  simp only [incidenceHilbertSeries, PowerSeries.coeff_mk] at h
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul] at h
  rw [Polynomial.constantCoeff_coe, G.thetaTwoI_coeff_zero, one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_invOneSubPow_multichoose] at h
  simp only [Nat.multichoose_zero_right, Nat.cast_one] at h
  exact_mod_cast h

/-- The degree-zero ring component is the constant line spanned by the original unit. -/
theorem incidenceCoefficientPiece_zero :
    G.incidenceCoefficientPiece 0 = Submodule.span ℂ {(1 : G.IncidenceRing)} :=
  eq_span_singleton_of_mem_of_finrank_eq_one
    G.finrank_incidenceCoefficientPiece_zero G.one_mem_incidenceCoefficientPiece one_ne_zero

/-- Membership in the original ring's degree-zero part is equivalent to being constant. -/
theorem mem_incidenceCoefficientPiece_zero (x : G.IncidenceRing) :
    x ∈ G.incidenceCoefficientPiece 0 ↔ ∃ c : ℂ, algebraMap ℂ G.IncidenceRing c = x := by
  rw [G.incidenceCoefficientPiece_zero, Submodule.mem_span_singleton]
  simp only [Algebra.algebraMap_eq_smul_one]

end BPFixedPoints.Multigraph
