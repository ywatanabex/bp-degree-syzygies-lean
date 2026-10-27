import BPFixedPoints.Incidence.SchemeModuleMonoidal
import BPFixedPoints.Incidence.SchemeModuleTensorSections

/-! # The coherent tensor preserves the original morphisms and sections -/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The original tensor comparison is natural for the original factor morphisms. -/
theorem moduleTensorIsoMonoidal_naturality {M₁ M₂ N₁ N₂ : X.Modules}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    moduleTensorMap X f g ≫ (moduleTensorIsoMonoidal X M₂ N₂).hom =
      (moduleTensorIsoMonoidal X M₁ N₁).hom ≫ (f ⊗ₘ g) := by
  simp only [moduleTensorMap, moduleTensorIsoMonoidal, Iso.trans_hom,
    Iso.symm_hom, Monoidal.μIso_inv, tensorIso_hom]
  erw [← OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom]
  have hf := (moduleSheafificationAdjunction X).counit.naturality f
  have hg := (moduleSheafificationAdjunction X).counit.naturality g
  change (moduleSheafification X).map f.val ≫ (moduleSheafificationIso X M₂).hom =
    (moduleSheafificationIso X M₁).hom ≫ f at hf
  change (moduleSheafification X).map g.val ≫ (moduleSheafificationIso X N₂).hom =
    (moduleSheafificationIso X N₁).hom ≫ g at hg
  rw [hf, hg, ← tensorHom_comp_tensorHom, Category.assoc]

/-- The original presheaf symmetry becomes the coherent native braiding. -/
theorem moduleTensorIsoMonoidal_symmetry (M N : X.Modules) :
    (moduleTensorSymmetry X M N).hom ≫ (moduleTensorIsoMonoidal X N M).hom =
      (moduleTensorIsoMonoidal X M N).hom ≫ (β_ M N).hom := by
  simp only [moduleTensorSymmetry, moduleTensorIsoMonoidal, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, Monoidal.μIso_inv, tensorIso_hom]
  rw [Functor.map_braiding]
  simp only [Category.assoc, Monoidal.μ_δ_assoc]
  erw [← BraidedCategory.braiding_naturality]

/-- The localized unit comparison is the original structure-module counit. -/
theorem moduleSheafification_unit_counit :
    (moduleSheafificationIso X (SheafOfModules.unit X.ringCatSheaf)).hom =
      OplaxMonoidal.η (moduleSheafification X) := rfl

/-- The original left unit map agrees with the coherent native left unitor. -/
theorem moduleTensorIsoMonoidal_leftUnit (M : X.Modules) :
    (moduleTensorIsoMonoidal X (SheafOfModules.unit X.ringCatSheaf) M).hom ≫ (λ_ M).hom =
      (moduleTensorLeftUnitIso X M).hom := by
  simp only [moduleTensorIsoMonoidal, moduleTensorLeftUnitIso, Iso.trans_hom,
    Iso.symm_hom, Monoidal.μIso_inv, tensorIso_hom, Functor.mapIso_hom]
  rw [moduleSheafification_unit_counit, tensorHom_def]
  simp only [Category.assoc]
  erw [leftUnitor_naturality]
  simpa only [Category.assoc] using! congrArg
    (fun k => k ≫ (moduleSheafificationIso X M).hom)
    (OplaxMonoidal.left_unitality_hom (moduleSheafification X) (moduleCommPresheaf X M))

/-- The original right unit map agrees with the coherent native right unitor. -/
theorem moduleTensorIsoMonoidal_rightUnit (M : X.Modules) :
    (moduleTensorIsoMonoidal X M (SheafOfModules.unit X.ringCatSheaf)).hom ≫ (ρ_ M).hom =
      (moduleTensorRightUnitIso X M).hom := by
  simp only [moduleTensorIsoMonoidal, moduleTensorRightUnitIso, Iso.trans_hom,
    Iso.symm_hom, Monoidal.μIso_inv, tensorIso_hom, Functor.mapIso_hom]
  rw [moduleSheafification_unit_counit, tensorHom_def']
  simp only [Category.assoc]
  erw [rightUnitor_naturality]
  simpa only [Category.assoc] using! congrArg
    (fun k => k ≫ (moduleSheafificationIso X M).hom)
    (OplaxMonoidal.right_unitality_hom (moduleSheafification X) (moduleCommPresheaf X M))

end BPFixedPoints.SheafTools
