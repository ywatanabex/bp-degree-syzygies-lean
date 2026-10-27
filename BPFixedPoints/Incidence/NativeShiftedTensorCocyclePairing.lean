import BPFixedPoints.Incidence.NegativeSingleTensorPairing
import BPFixedPoints.Incidence.NativeSingleTensorShiftComparison

/-! # Native shifted tensor pairings retain the original input cochain maps

The original maps into negative single complexes are shifted into degree
zero before applying Mathlib's ordered tensor shifts. The complete map
has exactly the previously proved Koszul crossing coefficient.
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
variable {T : Type} [TopologicalSpace T]
local instance shiftedTensorCocycleSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)
variable {K L : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ}

/-- Shift the two specified original cochain representatives and apply the native ordered shifted pairing. -/
def nativeShiftedTensorCocyclePairing (i j : ℤ)
    (f : K ⟶ actualSingleCochain F (-i)) (g : L ⟶ actualSingleCochain G (-j)) :
    HomologicalComplex.tensorObj K L ⟶ (actualSingleCochain H 0)⟦i+j⟧ :=
  HomologicalComplex.tensorHom
    (f ≫ ((CochainComplex.singleFunctors _).shiftIso i (-i) 0 (by omega)).inv.app F)
    (g ≫ ((CochainComplex.singleFunctors _).shiftIso j (-j) 0 (by omega)).inv.app G) ≫
      nativeShiftedSinglePairing b i j

/-- The original two cochain maps retain the exact native Koszul crossing coefficient under the standard tensor shifts. -/
theorem nativeShiftedTensorCocyclePairing_eq (i j : ℤ)
    (f : K ⟶ actualSingleCochain F (-i)) (g : L ⟶ actualSingleCochain G (-j)) :
    nativeShiftedTensorCocyclePairing b i j f g =
      (i*j).negOnePow •
        (HomologicalComplex.tensorHom f g ≫ singleCochainTensorPairingMap b (-i) (-j) (-(i+j)) ≫
          ((CochainComplex.singleFunctors _).shiftIso (i+j) (-(i+j)) 0 (by omega)).inv.app H) := by
  apply (cancel_mono (((CochainComplex.singleFunctors _).shiftIso (i+j) (-(i+j)) 0 (by omega)).hom.app H)).mp
  simp only [nativeShiftedTensorCocyclePairing,Linear.units_smul_comp,Category.assoc,
    Iso.inv_hom_id_app,Category.comp_id]
  rw [← nativeCochainTensorHom_comp_assoc]
  have hs := congrArg (fun m => HomologicalComplex.tensorHom f g ≫ m)
    (nativeSingleShiftTensorPairing_eq b i j)
  simpa only [nativeSingleShiftTensorPairing,Category.assoc,Linear.comp_units_smul] using hs

end
end BPFixedPoints.SheafTools.BinaryCells
