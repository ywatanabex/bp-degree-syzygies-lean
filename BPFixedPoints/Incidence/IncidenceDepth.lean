import BPFixedPoints.Incidence.ResolutionDepth
import BPFixedPoints.Incidence.RegularDepthTools
import BPFixedPoints.Incidence.FiniteAlgebraSupportDimension
import BPFixedPoints.Incidence.ResolutionTor
import BPFixedPoints.Incidence.Dimension

/-!
# Depth of the original incidence module at the coefficient origin

Obtain a depth lower bound from the finite free resolution, bounded above by
the actual support dimension. Construct regular sequences as Mathlib
non-zero-divisors on successive quotients.
-/

namespace BPFixedPoints.Multigraph
open ResolutionTools CategoryTheory RingTheory.Sequence MvPolynomial
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incidenceDepthAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

noncomputable local instance incidenceDepthFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite

/-- Complex point of the original ring setting all zero-chart free coordinates to zero. -/
noncomputable def incidenceOrigin : G.IncidenceRing →ₐ[ℂ] ℂ :=
  (MvPolynomial.aeval (fun _ : IncFreeVar V E => (0 : ℂ))).comp G.incidenceToFree

@[simp] theorem incidenceOrigin_coeffHom (p : IncCoeffRing E) :
    G.incidenceOrigin (G.coeffHom p) = MvPolynomial.constantCoeff p := by
  have he : G.incidenceOrigin.comp G.coeffHom =
      MvPolynomial.aeval (fun _ : IncCoeffIdx E => (0 : ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨e, α, β⟩
    simp only [AlgHom.comp_apply, incidenceOrigin, G.incidenceToFree_coeffHom_X, aeval_X]
    fin_cases α <;> fin_cases β <;> simp [incFreeCoeff]
  have h := congrArg (fun f : IncCoeffRing E →ₐ[ℂ] ℂ => f p) he
  simpa using h

/-- Multiplication by the coefficient-origin ideal does not give the whole original ring. -/
theorem incCoeffAugmentation_smul_lt_top :
    incCoeffAugmentationIdeal E • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) < ⊤ := by
  let K : Submodule (IncCoeffRing E) G.IncidenceRing :=
    (RingHom.ker G.incidenceOrigin.toRingHom).restrictScalars (IncCoeffRing E)
  have hle : incCoeffAugmentationIdeal E • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) ≤ K := by
    apply Submodule.smul_le.mpr
    intro r hr x _
    change G.incidenceOrigin (r • x) = 0
    change G.incidenceOrigin (G.coeffHom r * x) = 0
    rw [map_mul, G.incidenceOrigin_coeffHom]
    change MvPolynomial.constantCoeff r = 0 at hr
    rw [hr, zero_mul]
  have hn : K ≠ ⊤ := by
    intro h
    have hm : (1 : G.IncidenceRing) ∈ K := h ▸ Submodule.mem_top
    change G.incidenceOrigin 1 = 0 at hm
    simpa using hm
  exact hle.trans_lt hn.lt_top

/-- The original ring, as a coefficient module, has support dimension d_G. -/
theorem supportDim_incidenceRing :
    Module.supportDim (IncCoeffRing E) G.IncidenceRing = (G.dG : WithBot ℕ∞) := by
  rw [supportDim_finite_algebra, G.incidenceRing_krullDim]

/-- The existing actual free resolution gives depth at least d_G at the coefficient origin. -/
theorem incidenceDepth_ge :
    (G.dG : ℕ∞) ≤ (incCoeffAugmentationIdeal E).depth
      (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) := by
  let R := IncCoeffRing E
  let I := incCoeffAugmentationIdeal E
  let N := ModuleCat.of R (Shrink (R ⧸ I))
  have hI : I ≠ ⊤ := by
    intro h
    have hm : (1 : R) ∈ I := h ▸ Submodule.mem_top
    change MvPolynomial.constantCoeff (1 : R) = 0 at hm
    simpa using hm
  obtain ⟨rs, hlen, hmem, hreg⟩ := exists_regular_sequence_mvPolynomial ℂ (IncCoeffIdx E)
  have hlen' : rs.length = G.dG + G.rho := by
    rw [hlen, G.dG_add_rho]
    simp only [IncCoeffIdx, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
    omega
  change (G.dG : ℕ∞) ≤ N.depth (ModuleCat.of R G.IncidenceRing)
  apply @depth_ge_of_finite_exact R _ N G.rho G.dG G.IncFreeTerm
    (fun p => inferInstance) (fun p => inferInstance) G.incFreeTermDifferential
    G.IncidenceRing _ _
    G.incResolutionAugmentation G.incResolutionAugmentation_surjective
    G.incFreeTermDifferential_augmentation_exact G.incFreeTermDifferential_exact
  · intro p _
    haveI : Module.Finite R (G.IncFreeTerm p) := Module.Finite.of_basis (G.incFreeTermBasis p)
    have h := length_le_depth_free I hI (G.IncFreeTerm p) rs hmem hreg
    simpa only [hlen', Ideal.depth, N] using h
  · exact ModuleCat.isZero_iff_subsingleton.mp (gradedPiece_isZero (R := R) G.incResolutionDegree
      G.rho G.incResolutionDegree_le (G.rho + 1) (Nat.lt_succ_self _))

/-- Depth at the coefficient origin equals the actual ring's Krull dimension d_G. -/
theorem incidenceDepth_eq :
    (incCoeffAugmentationIdeal E).depth (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) =
      (G.dG : ℕ∞) := by
  apply le_antisymm _ G.incidenceDepth_ge
  exact depth_le_of_supportDim_le (incCoeffAugmentationIdeal E)
    (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) G.incCoeffAugmentation_smul_lt_top
    G.dG (le_of_eq G.supportDim_incidenceRing)

/-- A regular sequence of length d_G exists on the original incidence module. -/
theorem exists_incidence_regular_sequence :
    ∃ rs : List (IncCoeffRing E), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ incCoeffAugmentationIdeal E) ∧ IsRegular G.IncidenceRing rs := by
  apply ((ModuleCat.exists_isRegular_tfae (incCoeffAugmentationIdeal E) G.dG
    (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) G.incCoeffAugmentation_smul_lt_top).out 2 4).mp
  intro i hi
  apply ModuleCat.subsingleton_ext_of_lt_depth
  change (i : ℕ∞) < (incCoeffAugmentationIdeal E).depth
    (ModuleCat.of (IncCoeffRing E) G.IncidenceRing)
  rw [G.incidenceDepth_eq]
  exact_mod_cast hi

end BPFixedPoints.Multigraph
