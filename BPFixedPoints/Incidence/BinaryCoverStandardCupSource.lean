import BPFixedPoints.Incidence.BinaryCoverStandardCup
import BPFixedPoints.Incidence.FiniteCubicalSourceNaturality

/-! # The standard cup does not depend on the cover along augmentation-preserving maps

The identification of the original terminal sheaf with the actual tensor
unit does not depend on the vertex set: it is the sheafification of the
map sending each original terminal generator to the unit coefficient.
For two original binary cover families on the same space and a supplied
original chain map between their cell complexes that preserves the original
augmentation, the standard external roofs of pulled-back cocycles agree
with the original ones, and the standard products on actual Ext-defined
cohomology computed through the two covers are equal. The comparison chain
map is supplied; its existence is not asserted here.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T]

/-- Each original terminal generator sent to the unit coefficient, with no vertex set involved. -/
def terminalUnitPresheafHom : (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶
    toAbelianPresheaf.obj (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ)) where
  app _ := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun _ => (1 : ℤ)))
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro i
    rfl

/-- The original component identifications compose to this vertex-free generator map. -/
theorem terminalUnitPresheafHom_component {V : Type} [Fintype V] [DecidableEq V] :
    (topComponentPresheafIso (V := V) (T := T)).hom ≫
      toAbelianPresheaf.map (componentModuleUnitIso (T := T) (V := V)).hom = terminalUnitPresheafHom := by
  ext W : 2
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  change componentUnitLinearEquiv (V := V) (topComponentEquiv (V := V) W.unop (FreeAbelianGroup.of i)) =
    FreeAbelianGroup.lift (fun _ => (1 : ℤ)) (FreeAbelianGroup.of i)
  rw [topComponentEquiv_of,componentUnitLinearEquiv_generator,FreeAbelianGroup.lift_apply_of]

/-- The unit identification is the sheafified generator map followed by the native unit of sheafification. -/
theorem actualTerminalUnitIso_hom {V : Type} [Fintype V] [DecidableEq V] :
    (actualTerminalUnitIso (T := T) (V := V)).hom =
      (presheafToSheaf _ AddCommGrpCat).map terminalUnitPresheafHom ≫
        Functor.OplaxMonoidal.η (integerSheafification (T := T)) := by
  rw [actualTerminalUnitIso,Iso.trans_hom,Iso.trans_hom,Iso.symm_hom,Functor.Monoidal.εIso_inv,
    Functor.mapIso_hom,← terminalUnitPresheafHom_component (V := V),Functor.map_comp,Category.assoc]
  rfl

/-- The unit identification does not depend on the vertex set. -/
theorem actualTerminalUnitIso_eq {V V' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] :
    actualTerminalUnitIso (T := T) (V := V) = actualTerminalUnitIso (T := T) (V := V') :=
  Iso.ext (by rw [actualTerminalUnitIso_hom (V := V),actualTerminalUnitIso_hom (V := V')])

local instance standardCupSourceSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
local instance standardCupSourceDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
local instance standardCupSourceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (U : I → Fin 2 → Opens T) (W : J → Fin 2 → Opens T)
variable (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k) (hW : (⊤ : Opens T) ≤ ⨆ k, chartOpen W k)
variable (f : sheafComplex U ⟶ sheafComplex W) (hf : f.f 0 ≫ augmentation W=augmentation U)
include hf

/-- The supplied chain map carries the original terminal input augmentation of the target to that of the source. -/
theorem actualCellNegativeAugmentation_source :
    negativeMap (sheafComplex U) f ≫ actualCellNegativeAugmentation W = actualCellNegativeAugmentation U := by
  have h := negativeAugmentation_source (augmentation U) (augmentation_zero U) f (augmentation W)
    (augmentation_zero W) (𝟙 _) (by rw [hf,Category.comp_id])
  rwa [CategoryTheory.Functor.map_id,Category.comp_id] at h

/-- The same holds for the unit input augmentations. -/
theorem actualUnitNegativeAugmentation_source :
    negativeMap (sheafComplex U) f ≫ actualUnitNegativeAugmentation W = actualUnitNegativeAugmentation U := by
  rw [actualUnitNegativeAugmentation,actualUnitNegativeAugmentation,← Category.assoc,
    actualCellNegativeAugmentation_source U W f hf,actualTerminalUnitIso_eq (V := J) (V' := I)]

/-- The unit input denominator of the source is the tensor of the supplied map followed by that of the target. -/
theorem actualUnitTensorAugmentationIso_source :
    (actualUnitTensorAugmentationIso U hU).hom =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (negativeMap (sheafComplex U) f)
        (negativeMap (sheafComplex U) f)) ≫ (actualUnitTensorAugmentationIso W hW).hom := by
  rw [actualUnitTensorAugmentationIso_hom,actualUnitTensorAugmentationIso_hom,← Functor.map_comp,
    ← actualUnitNegativeAugmentation_source U W f hf,nativeCochainTensorHom_comp_assoc]

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)

/-- The standard external roof of pulled-back cocycles is the standard external roof of the original cocycles. -/
theorem actualStandardTensorRoof_source (i j : ℕ) (x : (sheafComplex W).X i ⟶ F)
    (hx : (sheafComplex W).d (i+1) i ≫ x=0) (y : (sheafComplex W).X j ⟶ G)
    (hy : (sheafComplex W).d (j+1) j ≫ y=0)
    (hfx : (sheafComplex U).d (i+1) i ≫ (f.f i ≫ x)=0) (hfy : (sheafComplex U).d (j+1) j ≫ (f.f j ≫ y)=0) :
    actualStandardTensorRoof U hU b i j (f.f i ≫ x) hfx (f.f j ≫ y) hfy =
      actualStandardTensorRoof W hW b i j x hx y hy := by
  have hp : nativeShiftedTensorCocyclePairing b i j (negativeCocycleMap (sheafComplex U) i (f.f i ≫ x) hfx)
      (negativeCocycleMap (sheafComplex U) j (f.f j ≫ y) hfy) =
        HomologicalComplex.tensorHom (negativeMap (sheafComplex U) f) (negativeMap (sheafComplex U) f) ≫
          nativeShiftedTensorCocyclePairing b i j (negativeCocycleMap (sheafComplex W) i x hx)
            (negativeCocycleMap (sheafComplex W) j y hy) := by
    rw [negativeCocycleMap_source (sheafComplex U) i f x hx hfx,
      negativeCocycleMap_source (sheafComplex U) j f y hy hfy]
    simp only [nativeShiftedTensorCocyclePairing,Category.assoc,nativeCochainTensorHom_comp_assoc]
  have hD : (actualUnitTensorAugmentationIso U hU).inv ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (negativeMap (sheafComplex U) f)
        (negativeMap (sheafComplex U) f)) = (actualUnitTensorAugmentationIso W hW).inv := by
    rw [Iso.inv_comp_eq,actualUnitTensorAugmentationIso_source U W hU hW f hf,Category.assoc,
      Iso.hom_inv_id,Category.comp_id]
  rw [actualStandardTensorRoof,actualStandardTensorRoof,hp,
    Functor.map_comp DerivedCategory.Q (HomologicalComplex.tensorHom (negativeMap (sheafComplex U) f)
      (negativeMap (sheafComplex U) f)),← Category.assoc ((actualUnitTensorAugmentationIso U hU).inv),hD,
    actualTerminalUnitIso_eq (V := I) (V' := J)]

/-- The standard product classes of pulled-back cocycles agree with those of the original cocycles. -/
theorem actualStandardCupClass_source (i j : ℕ) (x : (sheafComplex W).X i ⟶ F)
    (hx : (sheafComplex W).d (i+1) i ≫ x=0) (y : (sheafComplex W).X j ⟶ G)
    (hy : (sheafComplex W).d (j+1) j ≫ y=0)
    (hfx : (sheafComplex U).d (i+1) i ≫ (f.f i ≫ x)=0) (hfy : (sheafComplex U).d (j+1) j ≫ (f.f j ≫ y)=0) :
    actualStandardCupClass U hU b i j (f.f i ≫ x) hfx (f.f j ≫ y) hfy =
      actualStandardCupClass W hW b i j x hx y hy := by
  rw [actualStandardCupClass,actualStandardCupClass,actualStandardCupExt,actualStandardCupExt,
    actualStandardTensorRoof_source U W hU hW f hf]

omit hf in
include hf in
/-- The supplied chain map preserves the original native comparison of every original cubical class. -/
theorem nativeCubicalComparison_source {K : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (aU : ComplexAcyclicAgainst (sheafComplex U) K) (aW : ComplexAcyclicAgainst (sheafComplex W) K)
    (n : ℕ) (x : cubicalCohomologyAt W K n) :
    nativeCubicalComparison U K hU n
      ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cohomologyAt K n x) =
        nativeCubicalComparison W K hW n x := by
  rw [nativeCubicalComparison_yoneda U K hU aU,nativeCubicalComparison_yoneda W K hW aW,
    finiteCubicalActualAtEquiv_source U W K hU hW f hf aU aW]

/-- The standard products on actual Ext-defined cohomology computed through the two covers are equal. -/
theorem actualStandardClassCup_source (aU : ComplexAcyclicAgainst (sheafComplex U) F)
    (aW : ComplexAcyclicAgainst (sheafComplex W) F) (cU : ComplexAcyclicAgainst (sheafComplex U) G)
    (cW : ComplexAcyclicAgainst (sheafComplex W) G) (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hU b aU cU i j a c = actualStandardClassCup W hW b aW cW i j a c := by
  have ha := nativeCubicalCycleRep_spec W hW aW i a
  have hc := nativeCubicalCycleRep_spec W hW cW j c
  set x := nativeCubicalCycleRep W hW aW i a
  set y := nativeCubicalCycleRep W hW cW j c
  have hxU := nativeCubicalComparison_source U W hU hW f hf aU aW i ((cubicalTower W).classAt F i x)
  have hyU := nativeCubicalComparison_source U W hU hW f hf cU cW j ((cubicalTower W).classAt G j y)
  rw [ExactTower.SourceMap.cohomologyAt_class] at hxU hyU
  calc actualStandardClassCup U hU b aU cU i j a c
      = actualStandardClassProduct U hU b aU cU i j
          (nativeCubicalComparison U F hU i ((cubicalTower U).classAt F i
            ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cycles F i x)))
          (nativeCubicalComparison U G hU j ((cubicalTower U).classAt G j
            ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cycles G j y))) := by
        rw [actualStandardClassCup_apply,hxU,hyU,ha,hc]
    _ = actualStandardCupClass W hW b i j x.val (cubicalCycle_closed W i x) y.val (cubicalCycle_closed W j y) := by
        rw [actualStandardClassProduct_representative]
        exact actualStandardCupClass_source U W hU hW f hf b i j x.val (cubicalCycle_closed W i x) y.val
          (cubicalCycle_closed W j y) _ _
    _ = actualStandardClassCup W hW b aW cW i j a c := by
        rw [actualStandardClassCup_apply,← actualStandardClassProduct_representative,ha,hc]
end
end BPFixedPoints.SheafTools.BinaryCells
