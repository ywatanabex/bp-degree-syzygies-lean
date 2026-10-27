import BPFixedPoints.Incidence.BinaryCoverActualTensorAugmentedExact
import BPFixedPoints.Incidence.CechCubicalComponentTensorIso
import BPFixedPoints.Incidence.BinaryCoverCellCoverAugmentation

/-! # The original actual tensor complex is an augmented resolution of the original tensor unit -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite CechCubicalCell
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The existing terminal component diagonal is the specified native tensor unit isomorphism. -/
def terminalComponentDiagonalIso : (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ≅
    pairedComponentAbelianPresheaf (V := V) (T := T) :=
  topComponentPresheafIso ≪≫ (toAbelianPresheaf (T := T)).mapIso
    ((Functor.const (Opens T)ᵒᵖ).mapIso (componentTensorFold ℤ V).symm.toModuleIso)

/-- The isomorphism retains the originally defined diagonal, rather than replacing it. -/
theorem terminalComponentDiagonalIso_hom :
    (terminalComponentDiagonalIso (V := V) (T := T)).hom=terminalComponentDiagonal (V := V) (T := T) := by
  change (topComponentPresheafIso (V := V) (T := T)).hom ≫
    (toAbelianPresheaf (T := T)).map ((Functor.const (Opens T)ᵒᵖ).map
      (ModuleCat.ofHom (componentTensorFold ℤ V).symm.toLinearMap)) = _
  rw [componentTensorFold_symm]
  rfl

/-- The original actual terminal free sheaf identifies with the original actual component tensor square. -/
def actualTensorTerminalIso :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ≅
    actualComponentSheaf (T := T) (V := V) ⊗ actualComponentSheaf (T := T) (V := V) :=
  (presheafToSheaf _ AddCommGrpCat).mapIso (terminalComponentDiagonalIso (V := V) (T := T)) ≪≫
    (actualComponentTensorIso (T := T) (V := V)).symm

/-- The native tensor unit isomorphism retains precisely the specified original terminal diagonal. -/
theorem actualTensorTerminalIso_component :
    (actualTensorTerminalIso (V := V) (T := T)).hom ≫
      (actualComponentTensorIso (T := T) (V := V)).hom =
        (presheafToSheaf _ AddCommGrpCat).map (terminalComponentDiagonal (V := V) (T := T)) := by
  simp [actualTensorTerminalIso,terminalComponentDiagonalIso_hom]

/-- The actual diagonal is an augmentation-preserving map of the two original exact complexes. -/
theorem actualTensorDiagonal_augmentation_square :
    (actualTensorDiagonalMap U).f 0 ≫ actualTensorAugmentation U =
      augmentation U ≫ (actualTensorTerminalIso (V := V) (T := T)).hom := by
  apply (cancel_mono (actualComponentTensorIso (T := T) (V := V)).hom).1
  rw [Category.assoc,actualTensorDiagonal_augmentation,Category.assoc,actualTensorTerminalIso_component]

/-- The genuine original chart cover makes the independent native tensor augmentation epic. -/
theorem actualTensorAugmentation_epi (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) :
    Epi (actualTensorAugmentation U) := by
  letI := augmentation_epi U hcover
  exact epi_of_epi_fac (actualTensorDiagonal_augmentation_square U)

end
end BPFixedPoints.SheafTools.BinaryCells
