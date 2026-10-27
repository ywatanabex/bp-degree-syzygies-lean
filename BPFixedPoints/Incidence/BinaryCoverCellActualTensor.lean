import BPFixedPoints.Incidence.AbelianSheafTensor
import BPFixedPoints.Incidence.BinaryCoverCellTensorSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Tensor the original cell complexes in the actual abelian-sheaf category

The tensor is the native localized integer tensor. Its bidegrees are
compared by Mathlib's strong monoidal sheafification, and its total terms
by the original finite coproducts. The comparison retains each native
bidegree inclusion; no state-space identification defines the product.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T]

/-- Use the existing small sheaf colimits directly, avoiding instance search through larger universes. -/
local instance actualTensorSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The same original integer forgetting and actual sheafification as in the cell resolution. -/
abbrev integerSheafification : ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ) ⥤
    Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  toAbelianPresheaf ⋙ presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}

/-- The original forgetting and sheafification preserve the native integer tensor. -/
instance integerSheafificationMonoidal : (integerSheafification (T := T)).Monoidal := inferInstance

variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → Opens T)

/-- Mathlib's native tensor totalization of the original actual sheaf complexes. -/
abbrev actualTensorSheafComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ :=
  HomologicalComplex.tensorObj (sheafComplex U) (sheafComplex U)

/-- The specified comparison in each original bidegree is native strong monoidal sheafification. -/
def actualCellTensorIso (i j : ℕ) :
    (sheafComplex U).X i ⊗ (sheafComplex U).X j ≅
      integerSheafification.obj (presheaf U ℤ i ⊗ presheaf U ℤ j) :=
  Functor.Monoidal.μIso integerSheafification (presheaf U ℤ i) (presheaf U ℤ j)

/-- The native inclusion of each actual tensor bidegree. -/
abbrev actualTensorInclusion (i j n : ℕ) (h : i+j=n) :
    (sheafComplex U).X i ⊗ (sheafComplex U).X j ⟶ (actualTensorSheafComplex U).X n :=
  HomologicalComplex.ιTensorObj (sheafComplex U) (sheafComplex U) i j n h

/-- The actual tensor and the sheafified presheaf tensor have the same original total term. -/
def actualTensorTermIso (n : ℕ) :
    (actualTensorSheafComplex U).X n ≅ (tensorSheafComplex U).X n :=
  Sigma.mapIso (fun p : {ij : ℕ × ℕ // ij.1+ij.2=n} => actualCellTensorIso U p.val.1 p.val.2) ≪≫
    (PreservesCoproduct.iso integerSheafification
      (fun p : {ij : ℕ × ℕ // ij.1+ij.2=n} => presheaf U ℤ p.val.1 ⊗ presheaf U ℤ p.val.2)).symm

/-- Each native inclusion is unchanged except for its specified native bidegree tensor comparison. -/
@[reassoc] theorem actualTensorInclusion_comparison (i j n : ℕ) (h : i+j=n) :
    actualTensorInclusion U i j n h ≫ (actualTensorTermIso U n).hom =
      (actualCellTensorIso U i j).hom ≫
        integerSheafification.map (tensorPresheafInclusion ℤ U i j n h) := by
  change Sigma.ι (fun p : {ij : ℕ × ℕ // ij.1+ij.2=n} =>
    (sheafComplex U).X p.val.1 ⊗ (sheafComplex U).X p.val.2) ⟨(i,j),h⟩ ≫
      (actualTensorTermIso U n).hom = _
  rw [actualTensorTermIso,Iso.trans_hom,Iso.symm_hom]
  rw [← Category.assoc,Sigma.ι_mapIso_hom,Category.assoc,PreservesCoproduct.inv_hom]
  rw [ι_comp_sigmaComparison]
  rfl

end
end BPFixedPoints.SheafTools.BinaryCells
