import BPFixedPoints.Incidence.ResolutionNativeAugmentation
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Original augmentation-preserving maps have the canonical native derived source

Every denominator is the original exact epic augmentation, now proved a
native quasi-isomorphism. The resulting equality is an equality of actual
Mathlib derived-category morphisms, independent of relative acyclicity.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
noncomputable section
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n+1))

/-- The original exact augmentation gives its own native derived-category isomorphism. -/
def nativeAugmentationIso : DerivedCategory.Q.obj (negativeComplex P) ≅
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj A) := by
  haveI := negativeAugmentation_quasiIso P π z hP e
  exact asIso (DerivedCategory.Q.map (negativeAugmentation P π z))

variable {P} {Q : ChainComplex C ℕ} (f : P ⟶ Q)
variable {B : C} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0)
variable (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πQ] (hQ : ∀ n, Q.ExactAt (n+1))

/-- The original augmentation square determines the native derived morphism through the two original denominators. -/
theorem nativeDerivedMap_source (a : A ⟶ B) (h : f.f 0 ≫ πQ=π ≫ a) :
    DerivedCategory.Q.map (negativeMap P f) =
      (nativeAugmentationIso P π z e hP).hom ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map a) ≫
          (nativeAugmentationIso Q πQ zQ eQ hQ).inv := by
  apply (cancel_mono (nativeAugmentationIso Q πQ zQ eQ hQ).hom).mp
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change DerivedCategory.Q.map (negativeMap P f) ≫ DerivedCategory.Q.map (negativeAugmentation Q πQ zQ) =
    DerivedCategory.Q.map (negativeAugmentation P π z) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map a)
  rw [← Functor.map_comp,negativeAugmentation_source π z f πQ zQ a h,Functor.map_comp]

include e hP eQ hQ in
/-- Any two original lifts of the same original augmentation map induce the same native derived morphism. -/
theorem nativeDerivedMap_unique (g : P ⟶ Q) (a : A ⟶ B)
    (hf : f.f 0 ≫ πQ=π ≫ a) (hg : g.f 0 ≫ πQ=π ≫ a) :
    DerivedCategory.Q.map (negativeMap P f)=DerivedCategory.Q.map (negativeMap P g) := by
  rw [nativeDerivedMap_source π z e hP f πQ zQ eQ hQ a hf,
    nativeDerivedMap_source π z e hP g πQ zQ eQ hQ a hg]

include e hP eQ hQ in
/-- A lift of the original augmentation isomorphism is a native quasi-isomorphism of the original complexes. -/
theorem negativeMap_quasiIso_of_augmentation_iso (a : A ⟶ B) [IsIso a]
    (h : f.f 0 ≫ πQ=π ≫ a) : QuasiIso (negativeMap P f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso,
    nativeDerivedMap_source π z e hP f πQ zQ eQ hQ a h]
  infer_instance

end
end BPFixedPoints.ExtResolutionTools
