import BPFixedPoints.Incidence.AffineInjectiveSectionClearing
import BPFixedPoints.Incidence.SheafFlasqueCohomology

/-! # Native affine injective tilde sheaves are flasque

The original open restriction kernel is injective by Artin-Rees. Uniform
denominator clearing and the supported-localization extension theorem give
surjectivity on every open. This is the native flasqueness property and
therefore gives actual positive Ext-cohomology vanishing.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R)

/-- The actual native abelian sheaf underlying the original affine tilde module. -/
noncomputable def affineTildeAbelianSheaf :
    Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)

variable [IsNoetherianRing R] [Module.Injective R M]

/-- Every actual section on an arbitrary affine open lifts from the original injective module. -/
theorem affineInjective_toOpen_all_surjective (U : (Spec R).Opens) :
    Function.Surjective (tilde.toOpen M U) := by
  have hker : Module.Injective R (LinearMap.ker (StructureSheaf.toOpenₗ R M U)) :=
    affineInjective_open_kernel_injective R M U
  exact supported_localization_surjective (affineOpenComplementIdeal R U)
    (StructureSheaf.toOpenₗ R M U) (affineInjective_section_denominator_power R M U)
      (affineTilde_sections_supported_torsion_zero R M U)

/-- Actual top-to-open restriction is surjective on every open of the original affine scheme. -/
theorem affineInjective_open_restriction_top_surjective (U : (Spec R).Opens) :
    Function.Surjective ((tilde M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  intro s
  obtain ⟨x, hx⟩ := affineInjective_toOpen_all_surjective R M U s
  refine ⟨(tilde.toOpen M ⊤) x, ?_⟩
  change (tilde.toOpen M U) x = s
  exact hx

/-- Every original restriction between arbitrary affine opens is surjective. -/
theorem affineInjective_open_restriction_surjective
    {U V : (Spec R).Opens} (h : V ≤ U) :
    Function.Surjective ((tilde M).presheaf.map (homOfLE h).op) := by
  intro s
  obtain ⟨x, hx⟩ := affineInjective_open_restriction_top_surjective R M V s
  refine ⟨(tilde M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact hx

/-- The original injective tilde sheaf is flasque on all actual affine opens. -/
theorem affineInjective_tilde_isFlasque :
    TopCat.Sheaf.IsFlasque (X := TopCat.of (Spec R)) (affineTildeAbelianSheaf R M) where
  epi {_U _V} i := (AddCommGrpCat.epi_iff_surjective _).2
    (affineInjective_open_restriction_surjective R M (leOfHom i.unop))

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable (R : CommRingCat.{0}) [IsNoetherianRing R]
    (M : ModuleCat.{0} R) [Module.Injective R M]
noncomputable local instance affineInjectiveCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original affine injective tilde sheaf has no positive local Ext cohomology on any open. -/
theorem affineInjective_local_cohomology_eq_zero (U : (Spec R).Opens) (n : ℕ)
    (x : (affineTildeAbelianSheaf R M).H' (n+1) U) : x = 0 := by
  have := affineInjective_tilde_isFlasque R M
  exact flasque_local_cohomology_eq_zero n (affineTildeAbelianSheaf R M) U x

/-- The original affine injective tilde sheaf has no positive genuine global Ext cohomology. -/
theorem affineInjective_global_cohomology_eq_zero (n : ℕ)
    (x : (affineTildeAbelianSheaf R M).H (n+1)) : x = 0 := by
  have := affineInjective_tilde_isFlasque R M
  exact flasque_global_cohomology_eq_zero (affineTildeAbelianSheaf R M) n x

end BPFixedPoints.SheafTools
