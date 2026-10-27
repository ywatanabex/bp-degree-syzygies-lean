import BPFixedPoints.Incidence.ResolutionNativeCocycleMaps

/-! # The original augmentation and its square in native integer cochain degrees -/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Native extension of single complexes preserves their original coefficient morphisms. -/
theorem negativeSingleIso_naturality {A B : C} (a : A ⟶ B) (n : ℕ) :
    extendMap ((single C (ComplexShape.down ℕ) n).map a) ComplexShape.embeddingDownNat ≫
      (negativeSingleIso n B).hom = (negativeSingleIso n A).hom ≫
        (CochainComplex.singleFunctor C (-(n : ℤ))).map a := by
  apply to_single_hom_ext
  simp only [comp_f]
  rw [extendMap_f ((single C (ComplexShape.down ℕ) n).map a) ComplexShape.embeddingDownNat
    (i := n) (i' := -(n : ℤ)) (by rfl)]
  simp [negativeSingleIso,extendSingleIso_hom_f,CochainComplex.singleFunctor,
    CochainComplex.singleFunctors,single_map_f_self,Category.assoc]

variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)

/-- The original augmentation in the native negative integer cochain model. -/
def negativeAugmentation : negativeComplex P ⟶ (CochainComplex.singleFunctor C 0).obj A :=
  negativeMap P (augmentationChainMap P π z) ≫ (negativeSingleIso 0 A).hom

/-- Its original degree-zero coefficient is unchanged by native extension and the single-complex identification. -/
theorem negativeAugmentation_component :
    (negativeAugmentation P π z).f 0 =
      (P.extendXIso ComplexShape.embeddingDownNat (by rfl : ComplexShape.embeddingDownNat.f 0=0)).hom ≫
        π ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 A).inv := by
  simp only [negativeAugmentation,negativeMap,comp_f]
  rw [extendMap_f (augmentationChainMap P π z) ComplexShape.embeddingDownNat
    (i := 0) (i' := (0 : ℤ)) (by rfl)]
  simp [negativeSingleIso,extendSingleIso_hom_f,augmentationChainMap_zero,Category.assoc]

/-- This remains precisely the native negative map of the original degree-zero cocycle. -/
theorem negativeAugmentation_eq_cocycleMap :
    negativeAugmentation P π z=negativeCocycleMap P 0 π z := by
  rw [negativeCocycleMap,closedChainMap_zero]
  rfl

/-- Positive exactness and the original exact epic augmentation give the native integer quasi-isomorphism. -/
theorem negativeAugmentation_quasiIso (hP : ∀ n, P.ExactAt (n+1))
    (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] :
    QuasiIso (negativeAugmentation P π z) := by
  haveI := augmentationChainMap_quasiIso P π z e hP
  unfold negativeAugmentation negativeMap
  infer_instance

variable {P} {Q : ChainComplex C ℕ} (f : P ⟶ Q)
variable {B : C} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0) (a : A ⟶ B)

/-- An original augmentation square is the square of the original native chain augmentations. -/
theorem augmentationChainMap_source (h : f.f 0 ≫ πQ=π ≫ a) :
    f ≫ augmentationChainMap Q πQ zQ=augmentationChainMap P π z ≫ (ChainComplex.single₀ C).map a := by
  apply to_single_hom_ext
  simpa [comp_f,augmentationChainMap_zero] using h

/-- The original augmentation square is retained by native negative extension. -/
theorem negativeAugmentation_source (h : f.f 0 ≫ πQ=π ≫ a) :
    negativeMap P f ≫ negativeAugmentation Q πQ zQ =
      negativeAugmentation P π z ≫ (CochainComplex.singleFunctor C 0).map a := by
  simp only [negativeAugmentation,negativeMap]
  rw [← Category.assoc,← extendMap_comp,augmentationChainMap_source π z f πQ zQ a h,
    extendMap_comp,Category.assoc,negativeSingleIso_naturality]
  simp only [Category.assoc]
  rfl

end
end BPFixedPoints.ExtResolutionTools
