import BPFixedPoints.Incidence.ResolutionNativeExtComparison
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # The original first syzygy gives the native mapping-cone lift

This uses the original degree-zero and degree-one coefficients. The cone
and its projection are Mathlib's original cone, including its sign.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
attribute [local instance] Abelian.hasFiniteBiproducts
noncomputable section
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ) (S : ShortComplex C)
variable (u : K.X (-1) ⟶ S.X₁) (hu : K.d (-2) (-1) ≫ u=0)
variable (v : K.X 0 ⟶ S.X₂) (huv : K.d (-1) 0 ≫ v=u ≫ S.f)

/-- The original first syzygy projection as a native degree-one cocycle. -/
def firstConeCocycle : Cocycle K ((CochainComplex.singleFunctor C 0).obj S.X₁) 1 :=
  Cocycle.toSingleMk u (by omega : (-1 : ℤ)+1=0) (-2) (by omega) hu

/-- The original degree-zero coefficient as a native degree-zero cochain. -/
def firstConeCochain : Cochain K ((CochainComplex.singleFunctor C 0).obj S.X₂) 0 :=
  Cochain.toSingleMk v (zero_add 0)

include huv in
/-- The native cone-lift equation is precisely the original differential factorization. -/
theorem firstConeLift_equation :
    δ 0 1 (firstConeCochain K S v) + (firstConeCocycle K S u hu).val.comp
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.f)) (add_zero 1)=0 := by
  change δ 0 1 (Cochain.toSingleMk v (zero_add 0)) +
    (Cochain.toSingleMk u (by omega : (-1 : ℤ)+1=0)).comp
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.f)) (add_zero 1)=0
  rw [Cochain.δ_toSingleMk v (zero_add 0) 1 (-1) (by omega),← Cochain.toSingleMk_postcomp]
  simp only [Int.negOnePow_one,Units.neg_smul,one_smul]
  rw [huv]
  exact neg_add_cancel _

/-- The native cone lift retains the original first syzygy and degree-zero coefficients. -/
def firstConeLift : K ⟶ CochainComplex.mappingCone ((CochainComplex.singleFunctor C 0).map S.f) :=
  CochainComplex.mappingCone.lift _ (firstConeCocycle K S u hu) (firstConeCochain K S v)
    (firstConeLift_equation K S u hu v huv)

/-- The original augmentation coefficient defines its own native map to the original quotient single complex. -/
def firstConeAugmentation : K ⟶ (CochainComplex.singleFunctor C 0).obj S.X₃ :=
  mkHomToSingle (v ≫ S.g) (by
    intro p hp
    have hp' : p=(-1 : ℤ) := by change p+1=0 at hp; omega
    subst p
    rw [← Category.assoc,huv,Category.assoc,S.zero,comp_zero])

/-- The native cone lift retains precisely the original augmentation. -/
theorem firstConeLift_augmentation :
    firstConeLift K S u hu v huv ≫ CochainComplex.mappingCone.descShortComplex
      (S.map (CochainComplex.singleFunctor C 0)) = firstConeAugmentation K S u v huv := by
  apply to_single_hom_ext
  rw [comp_f,firstConeLift,CochainComplex.mappingCone.lift_f _ _ _ _ 0 1 (by omega)]
  simp only [Preadditive.add_comp,Category.assoc]
  have hl := CochainComplex.mappingCone.inl_v_descShortComplex_f
    (S.map (CochainComplex.singleFunctor C 0)) 1 0 (by omega)
  change (CochainComplex.mappingCone.inl ((CochainComplex.singleFunctor C 0).map S.f)).v
    1 0 (by omega) ≫ _ = 0 at hl
  have hr := CochainComplex.mappingCone.inr_f_descShortComplex_f
    (S.map (CochainComplex.singleFunctor C 0)) 0
  change (CochainComplex.mappingCone.inr ((CochainComplex.singleFunctor C 0).map S.f)).f 0 ≫
    _ = ((CochainComplex.singleFunctor C 0).map S.g).f 0 at hr
  rw [hl,hr]
  simp [firstConeCochain,firstConeAugmentation,Cochain.toSingleMk_v,
    CochainComplex.singleFunctor,single_map_f_self,Category.assoc]

/-- The original first cocycle as a map to the single complex in degree minus one. -/
def firstConeSingleMap : K ⟶ (CochainComplex.singleFunctor C (-1)).obj S.X₁ :=
  mkHomToSingle u (by
    intro p hp
    have hp' : p=(-2 : ℤ) := by change p+1=(-1 : ℤ) at hp; omega
    subst p
    exact hu)

/-- Mathlib's native triangle projects to the negative of the original first cocycle. -/
theorem firstConeLift_projection :
    firstConeLift K S u hu v huv ≫
      (CochainComplex.mappingCone.triangle ((CochainComplex.singleFunctor C 0).map S.f)).mor₃ =
    -(firstConeSingleMap K S u hu ≫
      ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by omega)).inv.app S.X₁) := by
  apply (cancel_mono
    (((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by omega)).hom.app S.X₁)).mp
  simp only [Preadditive.neg_comp,Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
  apply to_single_hom_ext
  simp only [comp_f]
  rw [firstConeLift,CochainComplex.mappingCone.lift_f _ _ _ _ (-1) 0 (by omega)]
  simp only [Preadditive.add_comp,Category.assoc]
  rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f_assoc,
    CochainComplex.mappingCone.inr_f_triangle_mor₃_f_assoc]
  simp [firstConeCocycle,firstConeSingleMap,Cocycle.toSingleMk,
    Cochain.toSingleMk_v,CochainComplex.shiftFunctorObjXIso]
  rfl

variable [HasDerivedCategory.{w} C]

/-- The actual SES connecting morphism is the negative native roof of the specified first cocycle. -/
theorem firstConeAugmentation_singleδ (hS : S.ShortExact) :
    DerivedCategory.Q.map (firstConeAugmentation K S u v huv) ≫ hS.singleδ =
      -(DerivedCategory.Q.map (firstConeSingleMap K S u hu) ≫
        ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by omega)).inv.app S.X₁) := by
  rw [← firstConeLift_augmentation K S u hu v huv,Functor.map_comp,Category.assoc]
  change _ ≫ (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex
    (S.map (CochainComplex.singleFunctor C 0))) ≫
      DerivedCategory.triangleOfSESδ (hS.map_of_exact (CochainComplex.singleFunctor C 0))) = _
  rw [DerivedCategory.descShortComplex_triangleOfSESδ,← Category.assoc,← Functor.map_comp]
  change DerivedCategory.Q.map (firstConeLift K S u hu v huv ≫
      (CochainComplex.mappingCone.triangle ((CochainComplex.singleFunctor C 0).map S.f)).mor₃) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((CochainComplex.singleFunctor C 0).obj S.X₁) = _
  rw [firstConeLift_projection,Functor.map_neg,Preadditive.neg_comp,Functor.map_comp,Category.assoc]
  simp [DerivedCategory.singleFunctors,SingleFunctors.postcomp]

end
end BPFixedPoints.ExtResolutionTools
