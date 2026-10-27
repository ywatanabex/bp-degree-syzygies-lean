import BPFixedPoints.Incidence.PrimaryTorsionInjective
import BPFixedPoints.Incidence.AffineInjectiveBasicSections
import Mathlib.RingTheory.Finiteness.Ideal

/-! # The original affine restriction kernel is supported torsion

Vanishing on an actual open is tested on the original localized values of
the tilde section. The closed complement and the native radical-power
criterion identify the restriction kernel with Mathlib's primary component.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R)

/-- The original ideal cutting out the closed complement of the specified affine open. -/
noncomputable def affineOpenComplementIdeal (U : (Spec R).Opens) : Ideal R :=
  PrimeSpectrum.vanishingIdeal ((U : Set (Spec R))ᶜ)

/-- This ideal has exactly the original closed complement as its zero locus. -/
theorem affineOpenComplementIdeal_zeroLocus (U : (Spec R).Opens) :
    PrimeSpectrum.zeroLocus (affineOpenComplementIdeal R U : Set R) =
      (U : Set (Spec R))ᶜ := by
  rw [affineOpenComplementIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    U.isOpen.isClosed_compl.closure_eq]

/-- Actual affine tilde-section vanishing is the original annihilator-support condition. -/
theorem affineTilde_vanishing_support (U : (Spec R).Opens) (x : M) :
    (tilde.toOpen M U) x = 0 ↔
      PrimeSpectrum.zeroLocus (Ideal.torsionOf R M x : Set R) ⊆
        (U : Set (Spec R))ᶜ := by
  classical
  constructor
  · intro hx p hp hpU
    have he := congrArg (fun s => s.val ⟨p, hpU⟩) hx
    change LocalizedModule.mkLinearMap p.asIdeal.primeCompl M x = 0 at he
    obtain ⟨r, hr⟩ := (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).mp he
    change (r : R) • x = 0 at hr
    change Ideal.torsionOf R M x ≤ p.asIdeal at hp
    exact r.property (hp ((Ideal.mem_torsionOf_iff x (r : R)).mpr hr))
  · intro hx
    apply Subtype.ext
    funext p
    change LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M x = 0
    have hn : ¬ Ideal.torsionOf R M x ≤ p.val.asIdeal := by
      intro h
      exact hx h p.property
    change ¬ ∀ r : R, r ∈ Ideal.torsionOf R M x → r ∈ p.val.asIdeal at hn
    obtain ⟨r, hr⟩ := not_forall.mp hn
    obtain ⟨hrx, hrp⟩ := not_imp.mp hr
    apply (IsLocalizedModule.eq_zero_iff p.val.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M)).mpr
    exact ⟨⟨r, hrp⟩, (Ideal.mem_torsionOf_iff x (r : R)).mp hrx⟩

variable [IsNoetherianRing R]

/-- The actual affine open restriction kernel is the original complement-supported torsion part. -/
theorem affineTilde_kernel_eq_primaryComponent (U : (Spec R).Opens) :
    LinearMap.ker (tilde.toOpen M U).hom = (affineOpenComplementIdeal R U).primaryComponent M := by
  ext x
  rw [LinearMap.mem_ker, affineTilde_vanishing_support,
    ← affineOpenComplementIdeal_zeroLocus R U, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff,
    Ideal.primaryComponent_mem]
  simp only [Submodule.mem_torsionBySet_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h
      (IsNoetherian.noetherian (affineOpenComplementIdeal R U))
    exact ⟨n, fun r => (Ideal.mem_torsionOf_iff x (r : R)).mp (hn r.property)⟩
  · rintro ⟨n, hn⟩ r hr
    refine ⟨n, (Ideal.mem_torsionOf_iff x (r ^ n)).mpr ?_⟩
    exact hn ⟨r ^ n, Ideal.pow_mem_pow hr n⟩

/-- The actual open restriction kernel of an affine injective tilde module is injective. -/
theorem affineInjective_open_kernel_injective [Module.Injective R M] (U : (Spec R).Opens) :
    Module.Injective R (LinearMap.ker (tilde.toOpen M U).hom) := by
  rw [affineTilde_kernel_eq_primaryComponent R M U]
  exact primaryComponent_injective _

end BPFixedPoints.SheafTools
