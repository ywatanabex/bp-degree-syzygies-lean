import BPFixedPoints.Incidence.SchemeModuleFiniteTensor
import BPFixedPoints.Incidence.VertexProjectiveProducts
import BPFixedPoints.Incidence.ProjectiveLineTwistSheaf

/-! # Actual external tensor sheaves on the original vertex projective product

Each factor is pulled back by the original vertex projection, and the actual
finite tensor uses native pointwise tensor and module sheafification. These
are genuine sheaves on the original scheme, not coefficient face modules.
Local frame and derived-cohomology comparisons are further properties.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- Original factor sheaves pulled back along the original vertex-labelled projections. -/
noncomputable def vertexPullbackModuleFamily (M : V → (projectiveLine R).Modules)
    (i : Fin (Fintype.card V)) : (vertexScheme R V).Modules :=
  (Scheme.Modules.pullback (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).obj
    (M ((Fintype.equivFin V).symm i))

/-- Actual external tensor of the original factor sheaves over the original coefficient scheme. -/
noncomputable def vertexExternalTensor (M : V → (projectiveLine R).Modules) : (vertexScheme R V).Modules :=
  SheafTools.moduleTensorFamily (vertexScheme R V) (Fintype.card V) (vertexPullbackModuleFamily R V M)

/-- Original factor maps give an actual morphism of external tensor sheaves. -/
noncomputable def vertexExternalTensorMap (M N : V → (projectiveLine R).Modules)
    (f : ∀ v, M v ⟶ N v) : vertexExternalTensor R V M ⟶ vertexExternalTensor R V N :=
  SheafTools.moduleTensorFamilyMap (vertexScheme R V) (Fintype.card V)
    (vertexPullbackModuleFamily R V M) (vertexPullbackModuleFamily R V N)
      (fun i => (Scheme.Modules.pullback
        (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map
          (f ((Fintype.equivFin V).symm i)))

/-- The actual external tensor preserves the original identity maps. -/
theorem vertexExternalTensorMap_id (M : V → (projectiveLine R).Modules) :
    vertexExternalTensorMap R V M M (fun v => 𝟙 (M v)) = 𝟙 _ := by
  have hf : (fun i : Fin (Fintype.card V) => (Scheme.Modules.pullback
      (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map
        (𝟙 (M ((Fintype.equivFin V).symm i)))) =
      (fun i => 𝟙 (vertexPullbackModuleFamily R V M i)) := by
    funext i
    exact (Scheme.Modules.pullback
      (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map_id _
  dsimp only [vertexExternalTensorMap]
  rw [hf]
  exact SheafTools.moduleTensorFamilyMap_id _ _ _

/-- The actual external tensor preserves original factorwise composition. -/
theorem vertexExternalTensorMap_comp (M N P : V → (projectiveLine R).Modules)
    (f : ∀ v, M v ⟶ N v) (g : ∀ v, N v ⟶ P v) :
    vertexExternalTensorMap R V M P (fun v => f v ≫ g v) =
      vertexExternalTensorMap R V M N f ≫ vertexExternalTensorMap R V N P g := by
  have hf : (fun i : Fin (Fintype.card V) => (Scheme.Modules.pullback
      (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map
        (f ((Fintype.equivFin V).symm i) ≫ g ((Fintype.equivFin V).symm i))) =
      (fun i => (Scheme.Modules.pullback
        (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map
          (f ((Fintype.equivFin V).symm i)) ≫
        (Scheme.Modules.pullback
          (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map
            (g ((Fintype.equivFin V).symm i))) := by
    funext i
    exact (Scheme.Modules.pullback
      (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).map_comp _ _
  dsimp only [vertexExternalTensorMap]
  rw [hf]
  exact SheafTools.moduleTensorFamilyMap_comp _ _ _ _ _ _ _

/-- Original factor isomorphisms induce an actual external tensor-sheaf isomorphism. -/
noncomputable def vertexExternalTensorIso (M N : V → (projectiveLine R).Modules) (e : ∀ v, M v ≅ N v) :
    vertexExternalTensor R V M ≅ vertexExternalTensor R V N :=
  SheafTools.moduleTensorFamilyIso (vertexScheme R V) (Fintype.card V)
    (vertexPullbackModuleFamily R V M) (vertexPullbackModuleFamily R V N)
      (fun i => (Scheme.Modules.pullback
        (vertexProjectionOver R V ((Fintype.equivFin V).symm i)).left).mapIso
          (e ((Fintype.equivFin V).symm i)))

/-- The actual empty external tensor is the original structure module. -/
theorem vertexExternalTensor_empty [IsEmpty V] (M : V → (projectiveLine R).Modules) :
    vertexExternalTensor R V M = SheafOfModules.unit (vertexScheme R V).ringCatSheaf := by
  have hn : Fintype.card V = 0 := by simp
  exact SheafTools.moduleTensorFamily_eq_unit_of_zero _ hn _

/-- Actual integral multi-twist sheaf, as the external tensor of the original factor twists. -/
noncomputable def vertexTwistSheaf (a : V → ℤ) : (vertexScheme R V).Modules :=
  vertexExternalTensor R V (fun v => twistSheaf R (a v))

/-- The actual multi-twist on an empty vertex set is the original structure module. -/
theorem vertexTwistSheaf_empty [IsEmpty V] (a : V → ℤ) :
    vertexTwistSheaf R V a = SheafOfModules.unit (vertexScheme R V).ringCatSheaf :=
  vertexExternalTensor_empty R V _

end BPFixedPoints.ProjectiveLine
