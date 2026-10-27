import BPFixedPoints.Incidence.NegativeSingleTensorPairing
import BPFixedPoints.Incidence.BinaryCoverNativeTensorCocycles

/-! # Original tensor cocycles are the actual integer cochain tensor of input maps

The negative extension comparison is natural in both original cocycle
maps and preserves the original single-degree pairing. Thus the original
chain tensor cocycle retains its actual integer cochain tensor formula.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
local instance negativeTensorCocycleSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (U : V → Fin 2 → Opens T)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)
variable (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
variable (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0)

/-- Tensor the actual original integer cochain representatives and apply the original negative single pairing. -/
def nativeIntegerTensorCocycleMap :
    HomologicalComplex.tensorObj (negativeComplex (sheafComplex U)) (negativeComplex (sheafComplex U)) ⟶
      actualSingleCochain H (-((i+j : ℕ) : ℤ)) :=
  HomologicalComplex.tensorHom (negativeCocycleMap (sheafComplex U) i x hx)
    (negativeCocycleMap (sheafComplex U) j y hy) ≫
      singleCochainTensorPairingMap b (-(i : ℤ)) (-(j : ℤ)) (-((i+j : ℕ) : ℤ))

/-- The original natural tensor cocycle after negative extension is exactly its actual integer cochain tensor formula. -/
theorem negativeTensorClosedMap_native :
    negativeMap (actualTensorSheafComplex U) (nativeTensorClosedMap U b i j x hx y hy) ≫
        (negativeSingleIso (i+j) H).hom =
      (negativeTensorIso (sheafComplex U) (sheafComplex U)).hom ≫
        nativeIntegerTensorCocycleMap U b i j x hx y hy := by
  simp only [nativeTensorClosedMap,negativeMap,extendMap_comp,Category.assoc]
  rw [negativeSingleTensorPairing]
  rw [← Category.assoc,negativeTensorIso_naturality]
  simp only [Category.assoc,nativeIntegerTensorCocycleMap,negativeCocycleMap,
    nativeCochainTensorHom_comp_assoc]

end
end BPFixedPoints.SheafTools.BinaryCells
