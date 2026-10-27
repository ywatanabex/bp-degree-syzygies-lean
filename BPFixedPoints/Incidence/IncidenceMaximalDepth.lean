import BPFixedPoints.Incidence.IncidenceDepth
import BPFixedPoints.Incidence.PolynomialMaximalRegular
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Height

/-! # Depth equals dimension at all maximal localizations of the incidence ring -/

namespace BPFixedPoints.Multigraph

open ResolutionTools CategoryTheory RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incMaxDepthAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance incMaxDepthFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite
local instance incMaxDepthNoetherian : IsNoetherianRing G.IncidenceRing :=
  IsNoetherianRing.of_finite (IncCoeffRing E) G.IncidenceRing
local instance incMaxDepthLocalizationFinite (P : Ideal G.IncidenceRing) [P.IsPrime] :
    Module.Finite (Localization.AtPrime P) (Localization.AtPrime P) :=
  Module.Finite.self _

/-- The existing free resolution gives a depth lower bound d_G at every coefficient maximal ideal. -/
theorem incidenceDepth_maximal_ge (I : Ideal (IncCoeffRing E)) [I.IsMaximal] :
    (G.dG : ℕ∞) ≤ I.depth (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) := by
  let R := IncCoeffRing E
  let N := ModuleCat.of R (Shrink (R ⧸ I))
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    exists_regular_sequence_in_maximal_mvPolynomial ℂ (IncCoeffIdx E) I
  have hlen' : rs.length = G.dG + G.rho := by
    rw [hlen, G.dG_add_rho]
    simp only [IncCoeffIdx, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin]
    omega
  change (G.dG : ℕ∞) ≤ N.depth (ModuleCat.of R G.IncidenceRing)
  apply @depth_ge_of_finite_exact R _ N G.rho G.dG G.IncFreeTerm
    (fun p => inferInstance) (fun p => inferInstance) G.incFreeTermDifferential
    G.IncidenceRing _ _ G.incResolutionAugmentation G.incResolutionAugmentation_surjective
    G.incFreeTermDifferential_augmentation_exact G.incFreeTermDifferential_exact
  · intro p _
    have : Module.Finite R (G.IncFreeTerm p) := Module.Finite.of_basis (G.incFreeTermBasis p)
    have h := length_le_depth_free I (Ideal.IsMaximal.ne_top inferInstance) (G.IncFreeTerm p) rs hmem hreg
    simpa only [hlen', Ideal.depth, N] using h
  · exact ModuleCat.isZero_iff_subsingleton.mp (gradedPiece_isZero (R := R)
      G.incResolutionDegree G.rho G.incResolutionDegree_le (G.rho + 1) (Nat.lt_succ_self _))

/-- At each coefficient maximal ideal meeting the support, depth equals d_G. -/
theorem incidenceDepth_maximal_eq (I : Ideal (IncCoeffRing E)) [I.IsMaximal]
    (hproper : I • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) < ⊤) :
    I.depth (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) = (G.dG : ℕ∞) := by
  apply le_antisymm _ (G.incidenceDepth_maximal_ge I)
  exact depth_le_of_supportDim_le I (ModuleCat.of (IncCoeffRing E) G.IncidenceRing)
    hproper G.dG (le_of_eq G.supportDim_incidenceRing)

/-- Extract a length-d_G regular sequence at every coefficient maximal ideal. -/
theorem exists_incidence_regular_sequence_in_maximal
    (I : Ideal (IncCoeffRing E)) [I.IsMaximal]
    (hproper : I • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) < ⊤) :
    ∃ rs : List (IncCoeffRing E), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ I) ∧ IsRegular G.IncidenceRing rs := by
  apply ((ModuleCat.exists_isRegular_tfae I G.dG
    (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) hproper).out 2 4).mp
  intro i hi
  apply ModuleCat.subsingleton_ext_of_lt_depth
  change (i : ℕ∞) < I.depth (ModuleCat.of (IncCoeffRing E) G.IncidenceRing)
  rw [G.incidenceDepth_maximal_eq I hproper]
  exact_mod_cast hi

/-- Every maximal ideal of the incidence ring itself contains a ring-regular sequence of length d_G. -/
theorem exists_incidence_ring_regular_sequence_in_maximal
    (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    ∃ rs : List G.IncidenceRing, rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ P) ∧ IsRegular G.IncidenceRing rs := by
  let I : Ideal (IncCoeffRing E) := P.under (IncCoeffRing E)
  have : I.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hproper : I • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) < ⊤ := by
    have hle : I • (⊤ : Submodule (IncCoeffRing E) G.IncidenceRing) ≤
        P.restrictScalars (IncCoeffRing E) := by
      apply Submodule.smul_le.mpr
      intro r hr x _
      change G.coeffHom r * x ∈ P
      exact P.mul_mem_right x hr
    have hn : P.restrictScalars (IncCoeffRing E) ≠ ⊤ := by
      intro h
      apply (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
      have : (1 : G.IncidenceRing) ∈ P.restrictScalars (IncCoeffRing E) := h ▸ Submodule.mem_top
      exact Ideal.eq_top_of_isUnit_mem P this isUnit_one
    exact hle.trans_lt hn.lt_top
  obtain ⟨rs, hlen, hmem, hreg⟩ := G.exists_incidence_regular_sequence_in_maximal I hproper
  refine ⟨rs.map G.coeffHom, by simpa using hlen, ?_, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact hmem x hx
  · apply (AddEquiv.isRegular_congr (e := AddEquiv.refl G.IncidenceRing) ?_).mp hreg
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    rfl

/-- Every maximal localization has a regular sequence of length d_G. -/
theorem exists_incidence_local_regular_sequence
    (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    ∃ rs : List (Localization.AtPrime P), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P)) ∧
      IsRegular (Localization.AtPrime P) rs := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := G.exists_incidence_ring_regular_sequence_in_maximal P
  refine ⟨rs.map (algebraMap G.IncidenceRing (Localization.AtPrime P)),
    by simpa using hlen, ?_,
    hreg.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem (Localization.AtPrime P) P hmem⟩
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P x).mpr (hmem x hx)

/-- Each maximal localization also has Krull dimension d_G. -/
theorem incidence_local_krullDim (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    ringKrullDim (Localization.AtPrime P) = (G.dG : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
    exact P.height_le_ringKrullDim_of_isPrime.trans (le_of_eq G.incidenceRing_krullDim)
  · obtain ⟨rs, hlen, _, hreg⟩ := G.exists_incidence_local_regular_sequence P
    have h := regular_length_le_supportDim (R := Localization.AtPrime P)
      (Localization.AtPrime P) rs hreg
    simpa only [hlen, Module.supportDim_self_eq_ringKrullDim] using h

/-- Depth at every maximal localization is d_G. -/
theorem incidence_local_depth (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    IsLocalRing.depth (R := Localization.AtPrime P)
      (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) =
      (G.dG : ℕ∞) := by
  rw [IsLocalRing.depth_eq_sSup_length_isRegular (R := Localization.AtPrime P)]
  apply le_antisymm
  · apply sSup_le
    rintro n ⟨rs, hreg, _, rfl⟩
    have h := regular_length_le_supportDim (R := Localization.AtPrime P)
      (Localization.AtPrime P) rs hreg
    rw [Module.supportDim_self_eq_ringKrullDim, G.incidence_local_krullDim P] at h
    exact_mod_cast h
  · obtain ⟨rs, hlen, hmem, hreg⟩ := G.exists_incidence_local_regular_sequence P
    exact le_sSup ⟨rs, hreg, hmem, by simp [hlen]⟩

/-- The standard Cohen–Macaulay depth/dimension equality at all maximal localizations. -/
theorem incidence_cohenMacaulay_at_maximal (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    (IsLocalRing.depth (R := Localization.AtPrime P)
      (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) :
      WithBot ℕ∞) = ringKrullDim (Localization.AtPrime P) := by
  rw [G.incidence_local_depth P, G.incidence_local_krullDim P]
  rfl

/-- The original ring is Noetherian and depth equals dimension at every maximal localization. -/
theorem incidence_cohenMacaulay :
    IsNoetherianRing G.IncidenceRing ∧ ∀ (P : Ideal G.IncidenceRing) [P.IsMaximal],
      (IsLocalRing.depth (R := Localization.AtPrime P)
        (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime P) := by
  refine ⟨inferInstance, ?_⟩
  intro P hP
  exact G.incidence_cohenMacaulay_at_maximal P

end BPFixedPoints.Multigraph
