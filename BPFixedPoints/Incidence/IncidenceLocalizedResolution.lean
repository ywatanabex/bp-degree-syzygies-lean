import BPFixedPoints.Incidence.IncidenceLocalizedResolutionTools
import BPFixedPoints.Incidence.IncidenceMaximalDepth

/-! # Localizing the incidence resolution at a prime of the coefficient ring

This is the localization argument of `supp:cm-localization`, with Mathlib's Ext depth. The
coefficient ring S_G = `IncCoeffRing E` acts on 𝒰_G = `G.IncidenceRing` through `coeffHom`, and
(𝒰_G)_𝔭 is `LocalizedModule 𝔭.primeCompl G.IncidenceRing` over (S_G)_𝔭 =
`Localization.AtPrime 𝔭`.

Proved here:
* every prime localization of S_G has depth equal to its dimension
  (`incCoeffRing_primeDimRegular`);
* localizing the actual free resolution of length ρ (`incFreeResolution`) at any prime 𝔭 of S_G
  gives depth_{(S_G)_𝔭} (𝒰_G)_𝔭 ≥ ht 𝔭 − ρ (`incidence_localized_depth_ge`), by the depth
  lemma along the localized syzygies (`IncidenceLocalizedResolutionTools`);
* (𝒰_G)_𝔭 is nonzero exactly when 𝔭 contains I = ker(S_G → 𝒰_G)
  (`incidence_localized_nontrivial`, `ker_coeffHom_le_of_localized_nontrivial`);
* for such 𝔭, ht 𝔭 − ρ ≤ depth (𝒰_G)_𝔭 ≤ dim (𝒰_G)_𝔭, the dimension being the support dimension
  over (S_G)_𝔭 (`incidence_localized_depth_bounds`).

The supplement's equality ht 𝔭 − ρ = dim (𝒰_G)_𝔭, and with it the module form
"(𝒰_G)_𝔭 is a Cohen–Macaulay (S_G)_𝔭-module", are proved in `IncidenceLocalizedDimension`
(`incidence_localized_supportDim`, `incidence_localized_cohenMacaulay`). Cohen–Macaulayness of the
ring 𝒰_G at every prime is proved by another route in `IncidencePrimeDepth`
(`incidence_cohenMacaulay_all_primes`).
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools CategoryTheory

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incLocResAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance incLocResFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite
local instance incLocResTermFree (p : ℕ) : Module.Free (IncCoeffRing E) (G.IncFreeTerm p) :=
  Module.Free.of_basis (G.incFreeTermBasis p)
local instance incLocResTermFinite (p : ℕ) : Module.Finite (IncCoeffRing E) (G.IncFreeTerm p) :=
  Module.Finite.of_basis (G.incFreeTermBasis p)

omit [LinearOrder E] in
/-- Every prime localization of the coefficient ring S_G has depth equal to its Krull
dimension. -/
theorem incCoeffRing_primeDimRegular [DecidableEq E] : PrimeDimRegular (IncCoeffRing E) :=
  (primeDimRegular_mvPolynomial_fin ℂ (Fintype.card (IncCoeffIdx E))).of_ringEquiv
    (MvPolynomial.renameEquiv ℂ (Fintype.equivFin (IncCoeffIdx E))).symm.toRingEquiv

/-- The term of the incidence resolution in homological degree ρ + 1 is zero. -/
theorem incFreeTerm_rho_succ_subsingleton : Subsingleton (G.IncFreeTerm (G.rho + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp (gradedPiece_isZero (R := IncCoeffRing E)
    G.incResolutionDegree G.rho G.incResolutionDegree_le (G.rho + 1) (Nat.lt_succ_self _))

/-- `supp:cm-localization`: localizing the free resolution of 𝒰_G over S_G at a prime 𝔭 gives
depth_{(S_G)_𝔭} (𝒰_G)_𝔭 ≥ ht 𝔭 − ρ. -/
theorem incidence_localized_depth_ge (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime] :
    𝔭.height - G.rho ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime 𝔭)
      (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) :=
  height_sub_length_le_localizedDepth incCoeffRing_primeDimRegular 𝔭 G.rho G.IncFreeTerm
    G.incFreeTermDifferential G.incResolutionAugmentation G.incResolutionAugmentation_surjective
    G.incFreeTermDifferential_augmentation_exact G.incFreeTermDifferential_exact
    G.incFreeTerm_rho_succ_subsingleton

/-- At a prime 𝔭 containing I = ker(S_G → 𝒰_G), the localization (𝒰_G)_𝔭 is nonzero. -/
theorem incidence_localized_nontrivial (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (h𝔭 : RingHom.ker G.coeffHom ≤ 𝔭) :
    Nontrivial (LocalizedModule 𝔭.primeCompl G.IncidenceRing) := by
  refine ⟨⟨LocalizedModule.mk 1 1, 0, fun h => ?_⟩⟩
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
  obtain ⟨s, hs⟩ := h
  simp only [one_smul, smul_zero] at hs
  apply s.2 (h𝔭 _)
  rw [RingHom.mem_ker]
  rw [Submonoid.smul_def, Algebra.smul_def, mul_one] at hs
  exact hs

/-- Conversely, if (𝒰_G)_𝔭 is nonzero then 𝔭 contains I = ker(S_G → 𝒰_G). -/
theorem ker_coeffHom_le_of_localized_nontrivial (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (h : Nontrivial (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) :
    RingHom.ker G.coeffHom ≤ 𝔭 := by
  intro x hx
  by_contra hx𝔭
  obtain ⟨u, v, huv⟩ := h
  apply huv
  have hzero : ∀ y : LocalizedModule 𝔭.primeCompl G.IncidenceRing, y = 0 := by
    intro y
    induction y using LocalizedModule.induction_on with
    | h m s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨x, hx𝔭⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def]
      rw [RingHom.mem_ker] at hx
      change G.coeffHom x * _ = 0
      rw [hx, zero_mul]
  rw [hzero u, hzero v]

/-- `supp:cm-localization`, bounds at a prime 𝔭 ⊇ I = ker(S_G → 𝒰_G):
ht 𝔭 − ρ ≤ depth_{(S_G)_𝔭} (𝒰_G)_𝔭 ≤ dim (𝒰_G)_𝔭, the dimension being the support dimension over
(S_G)_𝔭. In particular ht 𝔭 − ρ ≤ dim (𝒰_G)_𝔭. -/
theorem incidence_localized_depth_bounds (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (h𝔭 : RingHom.ker G.coeffHom ≤ 𝔭) :
    ((𝔭.height - G.rho : ℕ∞) : WithBot ℕ∞) ≤
        (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime 𝔭)
          (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) : WithBot ℕ∞) ∧
      (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime 𝔭)
          (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) : WithBot ℕ∞) ≤
        Module.supportDim (Localization.AtPrime 𝔭)
          (LocalizedModule 𝔭.primeCompl G.IncidenceRing) := by
  have := G.incidence_localized_nontrivial 𝔭 h𝔭
  exact ⟨WithBot.coe_le_coe.mpr (G.incidence_localized_depth_ge 𝔭),
    localDepth_le_supportDim _⟩

end BPFixedPoints.Multigraph
