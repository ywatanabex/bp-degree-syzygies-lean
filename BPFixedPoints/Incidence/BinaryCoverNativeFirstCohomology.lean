import BPFixedPoints.Incidence.ResolutionNativeFirstYoneda
import BPFixedPoints.Incidence.BinaryCoverNativeCupRoofs
import BPFixedPoints.Incidence.FiniteCubicalActualCohomology

/-! # Native first cubical roofs retain the actual original Yoneda comparison

The source is the original cell Hom quotient. The map is independently
specified by the original native augmentation roof. Its sign relative to
the original iterated Yoneda comparison follows from the actual cone lift.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance nativeFirstCubicalHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance nativeFirstCubicalDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)

/-- The independently specified native augmentation roof on the original first cell Hom quotient. -/
def nativeCubicalFirstComparison : cubicalCohomology U F 0 →+ F.H 1 := by
  letI := augmentation_epi U hcover
  exact (localSheafTopEquiv F 1).toAddMonoidHom.comp
    (nativeCohomologyAtComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F 1)

/-- The native first cubical roof agrees with the negative original actual-cohomology comparison on every quotient class. -/
theorem nativeCubicalFirstComparison_yoneda (ha : ComplexAcyclicAgainst (sheafComplex U) F)
    (x : cubicalCohomology U F 0) :
    nativeCubicalFirstComparison U F hcover x = -finiteCubicalActualEquiv U F hcover ha 0 x := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv F 1
    (nativeCohomologyAtComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F 1 x) = _
  rw [nativeCohomologyAtComparison_first_yoneda, map_neg]
  rfl

/-- Actual relative acyclicity makes the original native first cubical comparison bijective. -/
theorem nativeCubicalFirstComparison_bijective (ha : ComplexAcyclicAgainst (sheafComplex U) F) :
    Function.Bijective (nativeCubicalFirstComparison U F hcover) := by
  have h : (nativeCubicalFirstComparison U F hcover : cubicalCohomology U F 0 → F.H 1) =
      fun x => -(finiteCubicalActualEquiv U F hcover ha 0 x) := by
    funext x
    exact nativeCubicalFirstComparison_yoneda U F hcover ha x
  rw [h]
  exact neg_bijective.comp (finiteCubicalActualEquiv U F hcover ha 0).bijective

/-- The native first cubical comparison retains the actual derived morphism of every original representative. -/
theorem nativeCubicalFirstComparison_representative
    (x : (cubicalTower U).cycles F 1) :
    nativeCubicalFirstComparison U F hcover (QuotientAddGroup.mk x) =
      localSheafTopEquiv F 1 (Ext.homEquiv.symm
        (actualCellNativeRoof U hcover 1 x.val (by
          have h : (cubicalTower U).differential 1 ≫ x.val=0 := x.property
          simpa only [complexTower_differential] using h) ≫
            ((DerivedCategory.singleFunctors _).shiftIso 1 (-1) 0 (by omega)).inv.app F)) := by
  letI := augmentation_epi U hcover
  rfl

end
end BPFixedPoints.SheafTools.BinaryCells
