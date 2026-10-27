import BPFixedPoints.Incidence.ResolutionNativeDerivedSource

/-! # Native roofs of the original resolution cocycles

Use the original augmentation denominator and original single-degree
cochain map. Source compatibility is proved as native derived morphism
equality, without transporting a product through cohomology.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Native single-degree maps retain the original target postcomposition. -/
theorem negativeCocycleMap_postcomp (P : ChainComplex C ℕ) {Y Z : C} (n : ℕ)
    (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) (g : Y ⟶ Z)
    (hxg : P.d (n+1) n ≫ (x ≫ g)=0) :
    negativeCocycleMap P n (x ≫ g) hxg =
      negativeCocycleMap P n x hx ≫ (CochainComplex.singleFunctor C (-(n : ℤ))).map g := by
  have he : closedChainMap P n (x ≫ g) hxg =
      closedChainMap P n x hx ≫ (single C (ComplexShape.down ℕ) n).map g := by
    apply to_single_hom_ext
    simp [comp_f,closedChainMap_component,single_map_f_self,Category.assoc]
  simp only [negativeCocycleMap,negativeMap,he,extendMap_comp,Category.assoc,
    negativeSingleIso_naturality]

variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n+1))

/-- The original cocycle as a native derived roof with its original augmentation denominator. -/
def nativeCocycleRoof {Y : C} (n : ℕ) (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj A) ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-(n : ℤ))).obj Y) :=
  (nativeAugmentationIso P π z e hP).inv ≫ DerivedCategory.Q.map (negativeCocycleMap P n x hx)

/-- The original augmentation factorization normalizes the native degree-zero roof to the original target morphism. -/
theorem nativeCocycleRoof_zero_factor {Y : C} (g : A ⟶ Y)
    (hx : P.d 1 0 ≫ (π ≫ g)=0) :
    nativeCocycleRoof P π z e hP 0 (π ≫ g) hx =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map g) := by
  unfold nativeCocycleRoof
  rw [negativeCocycleMap_postcomp P 0 π z g hx,← negativeAugmentation_eq_cocycleMap,Functor.map_comp]
  change (nativeAugmentationIso P π z e hP).inv ≫
    (nativeAugmentationIso P π z e hP).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

variable {P} {Q : ChainComplex C ℕ} (f : P ⟶ Q)
variable {B : C} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0)
variable (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πQ] (hQ : ∀ n, Q.ExactAt (n+1))

/-- Every original augmentation square preserves the original cocycle roof as a native derived morphism. -/
theorem nativeCocycleRoof_source (a : A ⟶ B) (ha : f.f 0 ≫ πQ=π ≫ a)
    {Y : C} (n : ℕ) (x : Q.X n ⟶ Y) (hx : Q.d (n+1) n ≫ x=0)
    (hfx : P.d (n+1) n ≫ (f.f n ≫ x)=0) :
    nativeCocycleRoof P π z e hP n (f.f n ≫ x) hfx =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map a) ≫
        nativeCocycleRoof Q πQ zQ eQ hQ n x hx := by
  unfold nativeCocycleRoof
  rw [negativeCocycleMap_source P n f x hx hfx,Functor.map_comp,
    nativeDerivedMap_source π z e hP f πQ zQ eQ hQ a ha]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]

end
end BPFixedPoints.ExtResolutionTools
