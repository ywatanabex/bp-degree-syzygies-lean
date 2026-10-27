import BPFixedPoints.Incidence.BinaryCoverActualTensorYoneda
import BPFixedPoints.Incidence.BinaryCoverPairAcyclic
import BPFixedPoints.Incidence.FiniteCubicalCohomologyDegree

/-! # The original actual tensor resolution computes actual cohomology and retains its diagonal -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance tensorCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
variable (ha : ComplexAcyclicAgainst (actualTensorSheafComplex U) F)

/-- The original tensor Hom quotient computes actual cohomology by its original augmentation and native tensor unit. -/
def actualTensorActualAtEquiv (n : ℕ) : (actualTensorTower U).cohomologyAt F n ≃+ F.H n := by
  letI := actualTensorAugmentation_epi U hcover
  exact ((actualTensorTower U).cohomologyAtExtEquiv F (complexTower_acyclic _ _ _ ha) n).trans
    (((((extFunctor n).mapIso
      ((actualTensorTerminalIso (V := V) (T := T)) ≪≫
        (complexAugmentationIso _ (actualTensorAugmentation U) (actualTensorAugmentation_zero U)
          (actualTensorAugmentation_exact U)).symm).op).app F).addCommGroupIsoToAddEquiv).trans
      (localSheafTopEquiv F n))

/-- Every original tensor class keeps its own original augmented Yoneda representative. -/
theorem actualTensorActualAtEquiv_class (n : ℕ) (x : (actualTensorTower U).cycles F n) :
    actualTensorActualAtEquiv U F hcover ha n ((actualTensorTower U).classAt F n x) =
      localSheafTopEquiv F n
        ((Ext.mk₀ (actualTensorTerminalIso (V := V) (T := T)).hom).comp
          (actualTensorCocycleComparison U F hcover n x) (zero_add n)) := by
  letI := actualTensorAugmentation_epi U hcover
  unfold actualTensorActualAtEquiv
  dsimp only [AddEquiv.trans_apply]
  rw [ExactTower.cohomologyAtExtEquiv_class]
  change localSheafTopEquiv F n
    ((Ext.mk₀ ((actualTensorTerminalIso (V := V) (T := T)).hom ≫
      (complexAugmentationIso _ (actualTensorAugmentation U) (actualTensorAugmentation_zero U)
        (actualTensorAugmentation_exact U)).inv)).comp
        ((actualTensorTower U).cocycleComparison F n x) (zero_add n)) = _
  rw [← Ext.mk₀_comp_mk₀_assoc]
  rfl

/-- The specified actual diagonal induces the same original actual cohomology class in every degree. -/
theorem actualTensorDiagonal_actual (haCell : ComplexAcyclicAgainst (sheafComplex U) F)
    (n : ℕ) (x : (actualTensorTower U).cohomologyAt F n) :
    finiteCubicalActualAtEquiv U F hcover haCell n ((actualTensorDiagonalSource U).cohomologyAt F n x) =
      actualTensorActualAtEquiv U F hcover ha n x := by
  obtain ⟨x,rfl⟩ := (actualTensorTower U).classAt_surjective F n x
  rw [ExactTower.SourceMap.cohomologyAt_class,finiteCubicalActualAtEquiv_class,
    actualTensorActualAtEquiv_class]
  letI := augmentation_epi U hcover
  exact congrArg (localSheafTopEquiv F n) (actualTensorDiagonal_cocycleComparison U F hcover n x)

include hcover ha in
/-- With actual local acyclicity the original diagonal induces a bijection on the original Hom quotients. -/
theorem actualTensorDiagonal_cohomology_bijective (haCell : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    Function.Bijective ((actualTensorDiagonalSource U).cohomologyAt F n) := by
  have he : (actualTensorDiagonalSource U).cohomologyAt F n =
      (finiteCubicalActualAtEquiv U F hcover haCell n).symm.toAddMonoidHom.comp
        (actualTensorActualAtEquiv U F hcover ha n).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro x
    apply (finiteCubicalActualAtEquiv U F hcover haCell n).injective
    simpa using actualTensorDiagonal_actual U F hcover ha haCell n x
  rw [he]
  exact (finiteCubicalActualAtEquiv U F hcover haCell n).symm.bijective.comp
    (actualTensorActualAtEquiv U F hcover ha n).bijective

/-- The actual class of the original cup is the original tensor-cocycle class pulled back by the original diagonal. -/
theorem actualTensorCup_actual (haCell : ComplexAcyclicAgainst (sheafComplex U) F)
    {G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (b : AbelianTensor.SectionPairing G H F) (n i j : ℕ)
    (x : (cubicalTower U).cycles G i) (y : (cubicalTower U).cycles H j) :
    finiteCubicalActualAtEquiv U F hcover haCell n
      ((cubicalTower U).classAt F n (cubicalCyclesCupAt U b n i j x y)) =
        actualTensorActualAtEquiv U F hcover ha n
          ((actualTensorTower U).classAt F n (actualTensorCyclesCupAt U b n i j x y)) := by
  rw [← actualTensorDiagonal_cyclesCupAt U b n i j x y,← ExactTower.SourceMap.cohomologyAt_class]
  exact actualTensorDiagonal_actual U F hcover ha haCell n _

end
end BPFixedPoints.SheafTools.BinaryCells
