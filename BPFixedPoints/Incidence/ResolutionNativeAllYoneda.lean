import BPFixedPoints.Incidence.ResolutionNativeYonedaSign

/-! # All original resolution representatives retain their native Yoneda sign

The native augmentation roof and the existing Yoneda comparison are
compared on every original cocycle. The original Hom quotient is retained.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]
variable (P : ChainComplex C ℕ) (hP : ∀ n, P.ExactAt (n+1))

/-- Every original cocycle has the original iterated Yoneda class multiplied by its actual accumulated native cone sign. -/
theorem nativeCycleComparison_yoneda (Y : C) (n : ℕ) (x : (complexTower P hP).cycles Y n) :
    nativeCycleComparison P (cokernel.π (P.d 1 0)) (cokernel.condition _)
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP Y n x =
        nativeYonedaSign n • (complexTower P hP).cocycleComparison Y n x := by
  let f := (complexTower P hP).cycleEquiv Y n x
  have hf : cokernel.π (P.d (n+1) n) ≫ f=x.val := (complexTower P hP).cycleEquiv_projection Y n x
  have hx : P.d (n+1) n ≫ x.val=0 := by
    have h : (complexTower P hP).differential n ≫ x.val=0 := x.property
    simpa only [complexTower_differential] using h
  have h := nativeCocycleExt_postcomp P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
      n (cokernel.π (P.d (n+1) n)) (cokernel.condition _) f (by rw [hf]; exact hx)
  change nativeCocycleExt P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP n
      (cokernel.π (P.d (n+1) n) ≫ f) _ = (nativeProjectionExt P hP n).comp (Ext.mk₀ f) (add_zero n) at h
  rw [nativeProjectionExt_yoneda,nativeExt_units_comp] at h
  have hy : (complexTower P hP).cocycleComparison Y n x =
      ((complexTower P hP).connecting (complexSyzygy P n) n (Ext.mk₀ (𝟙 (complexSyzygy P n)))).comp
        (Ext.mk₀ f) (add_zero n) := by
    have hy0 : (complexTower P hP).cocycleComparison Y n x =
        (complexTower P hP).connecting Y n (Ext.mk₀ f) := by
      simp [ExactTower.cocycleComparison,f]
    exact hy0.trans (ExactTower.connecting_projection_postcomp n (complexTower P hP) f)
  rw [hy]
  simpa only [hf,nativeCycleComparison,AddMonoidHom.coe_mk,ZeroHom.coe_mk] using h

variable {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π]

/-- Every original augmented cocycle retains its original native roof and the signed original augmented Yoneda representative. -/
theorem nativeCycleComparison_augmented_yoneda (Y : C) (n : ℕ)
    (x : (complexTower P hP).cycles Y n) :
    nativeCycleComparison P π z e hP Y n x =
      nativeYonedaSign n • augmentedComplexCocycleComparison P Y hP π z e n x := by
  have hx : P.d (n+1) n ≫ x.val=0 := by
    have h : (complexTower P hP).differential n ≫ x.val=0 := x.property
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
          (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP Y n x) (zero_add n) := by
      have h := nativeCocycleExt_source π z e hP (𝟙 P) (cokernel.π (P.d 1 0)) (cokernel.condition _)
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
        (complexAugmentationIso P π z e).inv hp n x.val hx
          (by simpa only [HomologicalComplex.id_f,Category.id_comp] using hx)
      simpa only [nativeCycleComparison,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
        HomologicalComplex.id_f,Category.id_comp] using h
    _ = _ := by
      rw [nativeCycleComparison_yoneda,nativeExt_comp_units]
      rfl

/-- The native quotient map in every degree retains the original quotient and its signed original augmented Ext isomorphism. -/
theorem nativeCohomologyAtComparison_yoneda (Y : C) (ha : ComplexAcyclicAgainst P Y)
    (n : ℕ) (x : (complexTower P hP).cohomologyAt Y n) :
    nativeCohomologyAtComparison P π z e hP Y n x = nativeYonedaSign n •
      (((((extFunctor n).mapIso (complexAugmentationIso P π z e).symm.op).app Y).addCommGroupIsoToAddEquiv)
        ((complexTower P hP).cohomologyAtExtEquiv Y (complexTower_acyclic P Y hP ha) n x)) := by
  obtain ⟨x,rfl⟩ := (complexTower P hP).classAt_surjective Y n x
  rw [nativeCohomologyAtComparison_class,nativeCycleComparison_augmented_yoneda,
    ExactTower.cohomologyAtExtEquiv_class]
  rfl

/-- The independently specified native Ext roof is bijective on the original Hom quotient in every degree under original relative acyclicity. -/
theorem nativeCohomologyAtComparison_bijective (Y : C) (ha : ComplexAcyclicAgainst P Y) (n : ℕ) :
    Function.Bijective (nativeCohomologyAtComparison P π z e hP Y n) := by
  let old := ((complexTower P hP).cohomologyAtExtEquiv Y (complexTower_acyclic P Y hP ha) n).trans
    ((((extFunctor n).mapIso (complexAugmentationIso P π z e).symm.op).app Y).addCommGroupIsoToAddEquiv)
  have h : (nativeCohomologyAtComparison P π z e hP Y n :
      (complexTower P hP).cohomologyAt Y n → Ext.{w'} A Y n) = fun x => nativeYonedaSign n • old x := by
    funext x
    exact nativeCohomologyAtComparison_yoneda P hP π z e Y ha n x
  rw [h]
  exact (MulAction.bijective (nativeYonedaSign n)).comp old.bijective

end
end BPFixedPoints.ExtResolutionTools
