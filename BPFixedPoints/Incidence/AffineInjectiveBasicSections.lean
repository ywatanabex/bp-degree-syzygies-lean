import BPFixedPoints.Incidence.InjectiveLocalizationSections
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Actual principal-open sections of affine injective tilde modules

Mathlib identifies the original tilde-module maps with localization maps.
The algebraic surjectivity theorem therefore applies to the actual scheme
module's canonical restrictions whenever the target is a principal open.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Injective R M]

/-- Every actual principal-open tilde section comes from the original injective module. -/
theorem affineInjective_toOpen_surjective (r : R) :
    Function.Surjective (tilde.toOpen M (PrimeSpectrum.basicOpen r)) :=
  injective_localizationAway_surjective r (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom

/-- The actual top-to-principal restriction of the original affine tilde module is surjective. -/
theorem affineInjective_basic_restriction_top_surjective (r : R) :
    Function.Surjective ((tilde M).presheaf.map
      (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op) := by
  intro s
  obtain ⟨x, hx⟩ := affineInjective_toOpen_surjective R M r s
  refine ⟨(tilde.toOpen M ⊤) x, ?_⟩
  change (tilde.toOpen M (PrimeSpectrum.basicOpen r)) x = s
  exact hx

/-- Actual restriction from any containing open onto a principal open is surjective. -/
theorem affineInjective_basic_restriction_surjective
    (U : (Spec R).Opens) (r : R) (hr : PrimeSpectrum.basicOpen r ≤ U) :
    Function.Surjective ((tilde M).presheaf.map (homOfLE hr).op) := by
  intro s
  obtain ⟨x, hx⟩ := affineInjective_basic_restriction_top_surjective R M r s
  refine ⟨(tilde M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact hx

/-- These actual principal-target restriction maps are native epimorphisms of abelian groups. -/
theorem affineInjective_basic_restriction_epi
    (U : (Spec R).Opens) (r : R) (hr : PrimeSpectrum.basicOpen r ≤ U) :
    Epi ((tilde M).presheaf.map (homOfLE hr).op) :=
  (AddCommGrpCat.epi_iff_surjective _).2
    (affineInjective_basic_restriction_surjective R M U r hr)

end BPFixedPoints.SheafTools
