import BPFixedPoints.Incidence.ResolutionFirstConeLift
import BPFixedPoints.Incidence.ResolutionNativeExtTarget

/-! # The native first resolution roof and the original Yoneda class

The original differential cokernels and original exact presentations are
retained. The minus sign is forced by Mathlib's mapping-cone triangle.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (P : ChainComplex C ℕ) (hP : ∀ n, P.ExactAt (n+1))

/-- The original first syzygy and original augmentation give the native SES connecting morphism, with its actual sign. -/
theorem nativeFirstSyzygy_connecting :
    DerivedCategory.Q.map (negativeAugmentation P (cokernel.π (P.d 1 0)) (cokernel.condition _)) ≫
      (complexSyzygy_shortExact P 0 (hP 0)).singleδ =
    -(DerivedCategory.Q.map (negativeCocycleMap P 1 (cokernel.π (P.d 2 1)) (cokernel.condition _)) ≫
      ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by omega)).inv.app (complexSyzygy P 1)) := by
  let S := (complexTower P hP).sequence 0
  let a (n : ℕ) := P.extendXIso ComplexShape.embeddingDownNat
    (by rfl : ComplexShape.embeddingDownNat.f n=-(n : ℤ))
  let u := (a 1).hom ≫ cokernel.π (P.d 2 1)
  let v := (a 0).hom
  have hu : (negativeComplex P).d (-2) (-1) ≫ u=0 := by
    dsimp only [u,negativeComplex]
    rw [extend_d_eq P ComplexShape.embeddingDownNat (i := 2) (j := 1) (i' := (-2 : ℤ)) (j' := (-1 : ℤ)) rfl rfl]
    simp only [a,Category.assoc,Iso.inv_hom_id_assoc,cokernel.condition,comp_zero]
  have huv : (negativeComplex P).d (-1) 0 ≫ v=u ≫ S.f := by
    dsimp only [u,v,negativeComplex,S,ExactTower.sequence,complexTower]
    rw [extend_d_eq P ComplexShape.embeddingDownNat (i := 1) (j := 0) (i' := (-1 : ℤ)) (j' := (0 : ℤ)) rfl rfl]
    simp only [a,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    exact (congrArg (fun k => (a 1).hom ≫ k) (complexSyzygy_factor P 0)).symm
  have hA : firstConeAugmentation (negativeComplex P) S u v huv =
      negativeAugmentation P (cokernel.π (P.d 1 0)) (cokernel.condition _) := by
    apply to_single_hom_ext
    simp only [firstConeAugmentation,mkHomToSingle_f,negativeAugmentation_component]
    simp [v,a,S,ExactTower.sequence,complexTower,Category.assoc]
    rfl
  have hU : firstConeSingleMap (negativeComplex P) S u hu =
      negativeCocycleMap P 1 (cokernel.π (P.d 2 1)) (cokernel.condition _) := by
    apply to_single_hom_ext
    change (firstConeSingleMap (negativeComplex P) S u hu).f (-(1 : ℤ)) =
      (negativeCocycleMap P 1 (cokernel.π (P.d 2 1)) (cokernel.condition _)).f (-(1 : ℤ))
    have hc := negativeCocycleMap_component P 1 (cokernel.π (P.d 2 1)) (cokernel.condition _)
    change (negativeCocycleMap P 1 (cokernel.π (P.d 2 1)) (cokernel.condition _)).f (-1) = _ at hc
    rw [hc]
    simp [firstConeSingleMap,u,a,S,ExactTower.sequence,complexTower,Category.assoc]
    rfl
  have h := firstConeAugmentation_singleδ (negativeComplex P) S u hu v huv
    (complexSyzygy_shortExact P 0 (hP 0))
  rw [hA,hU] at h
  exact h

variable [HasExt.{w'} C]

/-- The original first projection represents the negative of the original first Yoneda extension under the native roof convention. -/
theorem nativeCocycleExt_firstProjection :
    nativeCocycleExt P (cokernel.π (P.d 1 0)) (cokernel.condition _)
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
      1 (cokernel.π (P.d 2 1)) (cokernel.condition _) =
    -(complexSyzygy_shortExact P 0 (hP 0)).extClass := by
  apply Ext.ext
  apply (cancel_epi (nativeAugmentationIso P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP).hom).mp
  rw [nativeCocycleExt_hom,Ext.neg_hom,ShortComplex.ShortExact.extClass_hom,nativeCocycleRoof]
  simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp,Preadditive.comp_neg]
  have h := congrArg Neg.neg (nativeFirstSyzygy_connecting P hP)
  simp only [neg_neg] at h
  exact h.symm

/-- Every original first cocycle has the negative of its original Yoneda comparison as its native Ext roof. -/
theorem nativeCycleComparison_first_yoneda (Y : C) (x : (complexTower P hP).cycles Y 1) :
    nativeCycleComparison P (cokernel.π (P.d 1 0)) (cokernel.condition _)
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP Y 1 x =
      -(complexTower P hP).cocycleComparison Y 1 x := by
  let f := (complexTower P hP).cycleEquiv Y 1 x
  have hf : cokernel.π (P.d 2 1) ≫ f=x.val := (complexTower P hP).cycleEquiv_projection Y 1 x
  have hx : P.d 2 1 ≫ x.val=0 := by
    have h : (complexTower P hP).differential 1 ≫ x.val=0 := x.property
    simpa only [complexTower_differential] using h
  have h := nativeCocycleExt_postcomp P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
    1 (cokernel.π (P.d 2 1)) (cokernel.condition _) f (by rw [hf]; exact hx)
  rw [nativeCocycleExt_firstProjection,Ext.neg_comp] at h
  have hy : (complexTower P hP).cocycleComparison Y 1 x =
      (complexSyzygy_shortExact P 0 (hP 0)).extClass.comp (Ext.mk₀ f) (by omega) := by
    simp [ExactTower.cocycleComparison,ExactTower.connecting,ExactTower.step,f]
    rfl
  rw [hy]
  simpa only [hf,nativeCycleComparison,AddMonoidHom.coe_mk,ZeroHom.coe_mk] using h

variable {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π]

/-- The original augmented first cocycle has precisely the negative original Yoneda class as its native Ext representative. -/
theorem nativeCycleComparison_first_augmented_yoneda (Y : C)
    (x : (complexTower P hP).cycles Y 1) :
    nativeCycleComparison P π z e hP Y 1 x =
      -augmentedComplexCocycleComparison P Y hP π z e 1 x := by
  have hx : P.d 2 1 ≫ x.val=0 := by
    have h : (complexTower P hP).differential 1 ≫ x.val=0 := x.property
    simpa only [complexTower_differential] using h
  have hp : (𝟙 P : P ⟶ P).f 0 ≫ cokernel.π (P.d 1 0) = π ≫ (complexAugmentationIso P π z e).inv := by
    rw [HomologicalComplex.id_f,Category.id_comp]
    calc
      _ = (cokernel.π (P.d 1 0) ≫ (complexAugmentationIso P π z e).hom) ≫
          (complexAugmentationIso P π z e).inv := by rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]
      _ = _ := congrArg (fun f => f ≫ (complexAugmentationIso P π z e).inv)
        (complexAugmentationIso_projection P π z e)
  calc
    _ = (Ext.mk₀ (complexAugmentationIso P π z e).inv).comp
        (nativeCycleComparison P (cokernel.π (P.d 1 0)) (cokernel.condition _)
          (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP Y 1 x) (zero_add 1) := by
      have h := nativeCocycleExt_source π z e hP (𝟙 P) (cokernel.π (P.d 1 0)) (cokernel.condition _)
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
        (complexAugmentationIso P π z e).inv hp 1 x.val hx (by simpa using hx)
      simpa [nativeCycleComparison] using h
    _ = _ := by
      rw [nativeCycleComparison_first_yoneda,Ext.comp_neg]
      rfl

/-- Native degree-one cohomology roofs retain the negative original augmented Ext isomorphism on every original quotient class. -/
theorem nativeCohomologyAtComparison_first_yoneda (Y : C) (ha : ComplexAcyclicAgainst P Y)
    (x : (complexTower P hP).cohomologyAt Y 1) :
    nativeCohomologyAtComparison P π z e hP Y 1 x =
      -augmentedComplexExtEquiv P Y hP π z e ha 0 x := by
  obtain ⟨x,rfl⟩ := (complexTower P hP).classAt_surjective Y 1 x
  rw [nativeCohomologyAtComparison_class,nativeCycleComparison_first_augmented_yoneda]
  rfl

/-- Original relative acyclicity makes the native first cohomology roof bijective on the original Hom quotient. -/
theorem nativeCohomologyAtComparison_first_bijective (Y : C) (ha : ComplexAcyclicAgainst P Y) :
    Function.Bijective (nativeCohomologyAtComparison P π z e hP Y 1) := by
  have h : (nativeCohomologyAtComparison P π z e hP Y 1 :
      (complexTower P hP).cohomologyAt Y 1 → Ext.{w'} A Y 1) =
      fun x => -(augmentedComplexExtEquiv P Y hP π z e ha 0 x) := by
    funext x
    exact nativeCohomologyAtComparison_first_yoneda P hP π z e Y ha x
  rw [h]
  exact neg_bijective.comp (augmentedComplexExtEquiv P Y hP π z e ha 0).bijective

end
end BPFixedPoints.ExtResolutionTools
