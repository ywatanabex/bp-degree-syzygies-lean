/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in LICENSE-APACHE-2.0.
Adapted from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
See THIRD_PARTY_NOTICES.md for source files and changes.
-/
import BPFixedPoints.Incidence.PublicModuleTensorLocalization
import BPFixedPoints.Incidence.SchemeModuleSheafificationOver
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! # Coherent tensor structure on the original scheme module category

The construction follows the public sheaf-module localization construction
listed in THIRD_PARTY_NOTICES.md, using our original chosen sheafification.
The original tensor object is compared to this coherent tensor below.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The native commutative-presheaf tensor on the original scheme presheaf category. -/
noncomputable instance schemePresheafModulesMonoidal : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{0} X.presheaf))

/-- The native symmetry on the original scheme module presheaves. -/
noncomputable instance schemePresheafModulesSymmetric : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (PresheafOfModulesOfCommRing.{0} X.presheaf))

/-- The original local-equivalence class on module presheaves. -/
abbrev moduleSheafificationW : MorphismProperty (PresheafOfModulesOfCommRing.{0} X.presheaf) :=
  ((Opens.grothendieckTopology X).W (A := AddCommGrpCat.{0})).inverseImage
    (_root_.PresheafOfModules.toPresheaf _)

/-- Tensoring preserves local equivalences of the original module presheaves. -/
instance moduleSheafificationW_isMonoidal : (moduleSheafificationW X).IsMonoidal := by
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  exact BPFixedPoints.PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf
    X.presheaf X.ringCatSheaf (𝟙 _)

/-- The originally chosen sheafification is the same native localization. -/
instance moduleSheafification_isLocalization :
    (moduleSheafification X).IsLocalization (moduleSheafificationW X) := by
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) := inferInstance
  let : (nativeModuleSheafification X).IsLocalization (moduleSheafificationW X) :=
    inferInstanceAs ((_root_.PresheafOfModules.sheafification.{0}
      (J := Opens.grothendieckTopology X) (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).IsLocalization
        (((Opens.grothendieckTopology X).W (A := AddCommGrpCat.{0})).inverseImage
          (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))
  exact Functor.IsLocalization.of_iso (moduleSheafificationW X)
    (moduleSheafificationNativeIso X).symm

/-- The original counit chooses the original structure module as tensor unit. -/
noncomputable def moduleSheafificationUnitIso :
    (moduleSheafification X).obj (𝟙_ (PresheafOfModulesOfCommRing.{0} X.presheaf)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  moduleSheafificationIso X (SheafOfModules.unit X.ringCatSheaf)

/-- Mathlib's localization provides all tensor coherence laws. -/
noncomputable instance schemeModulesMonoidal : MonoidalCategory X.Modules :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal (moduleSheafification X)
    (moduleSheafificationW X) (moduleSheafificationUnitIso X)))

/-- The localized symmetry satisfies Mathlib's symmetry and hexagon laws. -/
noncomputable instance schemeModulesSymmetric : SymmetricCategory X.Modules :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal (moduleSheafification X)
    (moduleSheafificationW X) (moduleSheafificationUnitIso X)))

/-- Original sheafification carries the coherent native monoidal structure. -/
noncomputable instance moduleSheafification_monoidal : (moduleSheafification X).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := moduleSheafification X) (W := moduleSheafificationW X)
    (moduleSheafificationUnitIso X)).Monoidal

/-- Sheafification also preserves the original presheaf braiding. -/
noncomputable instance moduleSheafification_braided : (moduleSheafification X).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := moduleSheafification X) (W := moduleSheafificationW X)
    (moduleSheafificationUnitIso X)).Braided

/-- The coherent tensor unit is the original structure module. -/
theorem schemeModules_tensorUnit : 𝟙_ X.Modules = SheafOfModules.unit X.ringCatSheaf := rfl

/-- Compare the original tensor sheaf, without changing either of its factors. -/
noncomputable def moduleTensorIsoMonoidal (M N : X.Modules) : moduleTensor X M N ≅ M ⊗ N :=
  (Functor.Monoidal.μIso (moduleSheafification X) (moduleCommPresheaf X M)
    (moduleCommPresheaf X N)).symm ≪≫
      (moduleSheafificationIso X M ⊗ᵢ moduleSheafificationIso X N)

end BPFixedPoints.SheafTools
