import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Actual tensor sheaves from the native presheaf tensor and sheafification

The tensor object uses Mathlib's original pointwise module tensor followed
by its native module sheafification. The unit comparisons use the original
presheaf unitors and the native sheafification counit.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The original sheaf module viewed as a presheaf over the original commutative structure rings. -/
noncomputable abbrev moduleCommPresheaf (M : X.Modules) :
    PresheafOfModulesOfCommRing.{0} X.presheaf := M.val

/-- Native sheafification over the original structure-ring sheaf. -/
noncomputable abbrev moduleSheafification :
    PresheafOfModulesOfCommRing.{0} X.presheaf ⥤ X.Modules :=
  (Scheme.Modules.toPresheafOfModules X).leftAdjoint

/-- The native module-sheafification adjunction over the original scheme. -/
noncomputable abbrev moduleSheafificationAdjunction :
    moduleSheafification X ⊣ Scheme.Modules.toPresheafOfModules X :=
  Adjunction.ofIsRightAdjoint (Scheme.Modules.toPresheafOfModules X)

/-- The native sheafification of an actual module sheaf returns that original sheaf. -/
noncomputable def moduleSheafificationIso (M : X.Modules) :
    (moduleSheafification X).obj (moduleCommPresheaf X M) ≅ M := by
  have hi : IsIso ((Adjunction.ofIsRightAdjoint
      (Scheme.Modules.toPresheafOfModules X)).counit.app M) := inferInstance
  exact asIso ((moduleSheafificationAdjunction X).counit.app M)

/-- The native pointwise presheaf tensor of the two original sheaf modules. -/
noncomputable abbrev moduleTensorPresheaf (M N : X.Modules) :
    PresheafOfModulesOfCommRing.{0} X.presheaf :=
  moduleCommPresheaf X M ⊗ moduleCommPresheaf X N

/-- The actual sheaf tensor is the native sheafification of the original pointwise tensor. -/
noncomputable def moduleTensor (M N : X.Modules) : X.Modules :=
  (moduleSheafification X).obj (moduleTensorPresheaf X M N)

/-- Original module morphisms induce the actual tensor-sheaf morphism. -/
noncomputable def moduleTensorMap {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) :
    moduleTensor X M₁ N₁ ⟶ moduleTensor X M₂ N₂ :=
  (moduleSheafification X).map
    ((show moduleCommPresheaf X M₁ ⟶ moduleCommPresheaf X M₂ from f.val) ⊗ₘ
      (show moduleCommPresheaf X N₁ ⟶ moduleCommPresheaf X N₂ from g.val))

/-- The actual tensor of original identity morphisms is the original identity. -/
theorem moduleTensorMap_id (M N : X.Modules) : moduleTensorMap X (𝟙 M) (𝟙 N) = 𝟙 _ := by
  change (moduleSheafification X).map
    ((𝟙 (moduleCommPresheaf X M)) ⊗ₘ (𝟙 (moduleCommPresheaf X N))) = 𝟙 _
  rw [id_tensorHom_id, CategoryTheory.Functor.map_id]

/-- Actual tensor-sheaf morphisms preserve the original composition. -/
theorem moduleTensorMap_comp {M₁ M₂ M₃ N₁ N₂ N₃ : X.Modules}
    (f₁ : M₁ ⟶ M₂) (f₂ : M₂ ⟶ M₃) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    moduleTensorMap X (f₁ ≫ f₂) (g₁ ≫ g₂) =
      moduleTensorMap X f₁ g₁ ≫ moduleTensorMap X f₂ g₂ := by
  dsimp only [moduleTensorMap]
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- Actual tensor-sheaf objects retain the original native presheaf symmetry. -/
noncomputable def moduleTensorSymmetry (M N : X.Modules) :
    moduleTensor X M N ≅ moduleTensor X N M :=
  (moduleSheafification X).mapIso (β_ (moduleCommPresheaf X M) (moduleCommPresheaf X N))

/-- Tensoring the actual structure module on the left returns the original sheaf module. -/
noncomputable def moduleTensorLeftUnitIso (M : X.Modules) :
    moduleTensor X (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (moduleSheafification X).mapIso (λ_ (moduleCommPresheaf X M)) ≪≫ moduleSheafificationIso X M

/-- Tensoring the actual structure module on the right returns the original sheaf module. -/
noncomputable def moduleTensorRightUnitIso (M : X.Modules) :
    moduleTensor X M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (moduleSheafification X).mapIso (ρ_ (moduleCommPresheaf X M)) ≪≫ moduleSheafificationIso X M

end BPFixedPoints.SheafTools
