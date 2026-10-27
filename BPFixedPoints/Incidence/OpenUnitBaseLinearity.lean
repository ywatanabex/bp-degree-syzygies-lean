import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars
import BPFixedPoints.Incidence.OpenUnitChartSections

/-! # Original geometric base scalars in actual open chart frames

The inverse of the original top-to-chart restriction preserves geometric
base scalars by the module restriction law. Hence original chart-frame
coordinates are linear before applying any polynomial or state comparison.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R))

/-- The original geometric action on the pushed-forward open structure module is its original chart coefficient. -/
theorem openUnitModule_base_smul (U : X.Opens) (r : R)
    (s : Γ(SheafTools.openUnitModule X U, ⊤)) :
    letI := schemeBaseModuleSections f (SheafTools.openUnitModule X U)
    r • s = Mul.mul (α := Γ(U.toScheme, ⊤)) (schemeBaseCoefficientHom (U.ι ≫ f) r) s := by
  letI := schemeBaseModuleSections f (SheafTools.openUnitModule X U)
  exact openUnitProjection_base_smul f (SheafTools.openUnitModule X U) U (𝟙 _) r s

/-- Applying the original top restriction to actual chart coordinates recovers the original module morphism. -/
theorem openUnitChartCoordinates_restrict {M : X.Modules} (U : X.Opens)
    (φ : M ⟶ SheafTools.openUnitModule X U) (s : Γ(M, U)) :
    (SheafTools.openUnitTopRestrictionIso X U).hom (SheafTools.openUnitChartCoordinates X U φ s) =
      φ.app U s := by
  dsimp only [SheafTools.openUnitChartCoordinates]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

/-- The original actual chart-coordinate map preserves geometric base scalars. -/
theorem openUnitChartCoordinates_base_smul {M : X.Modules} (U : X.Opens)
    (φ : M ⟶ SheafTools.openUnitModule X U) (r : R) (s : Γ(M, U)) :
    letI := schemeBaseOpenModuleSections f M U
    letI := schemeBaseModuleSections f (SheafTools.openUnitModule X U)
    SheafTools.openUnitChartCoordinates X U φ (r • s) =
      r • SheafTools.openUnitChartCoordinates X U φ s := by
  letI := schemeBaseOpenModuleSections f M U
  letI := schemeBaseModuleSections f (SheafTools.openUnitModule X U)
  apply (ConcreteCategory.bijective_of_isIso (SheafTools.openUnitTopRestrictionIso X U).hom).injective
  rw [openUnitChartCoordinates_restrict]
  change φ.app U (schemeBaseCoefficientAt f U r • s) =
    (SheafTools.openUnitModule X U).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (schemeBaseCoefficientHom f r • SheafTools.openUnitChartCoordinates X U φ s)
  rw [Scheme.Modules.map_smul]
  have hs := openUnitChartCoordinates_restrict U φ s
  change φ.app U (schemeBaseCoefficientAt f U r • s) =
    schemeBaseCoefficientAt f U r • _
  exact (Scheme.Modules.Hom.app_smul φ _ s).trans
    (congrArg (fun z : Γ(SheafTools.openUnitModule X U, U) =>
      schemeBaseCoefficientAt f U r • z) hs.symm)

end BPFixedPoints.SchemeTools
