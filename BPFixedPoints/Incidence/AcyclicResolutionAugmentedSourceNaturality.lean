import BPFixedPoints.Incidence.AcyclicResolutionComplexSourceMap

/-! # Original augmented resolution comparisons preserve source chain maps

Every comparison uses the original differential cokernels, augmentation
identification and iterated Yoneda class. Source maps are supplied actual
chain maps; their existence is not inferred from free-open generators.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (P : ChainComplex C ℕ) (Y : C) (hP : ∀ n, P.ExactAt (n+1))
variable {A : C} (πP : P.X 0 ⟶ A) (zP : P.d 1 0 ≫ πP=0)
variable (eP : (ShortComplex.mk (P.d 1 0) πP zP).Exact) [Epi πP]

/-- The original augmentation and Yoneda class of every original closed cochain, including degree zero. -/
noncomputable def augmentedComplexCocycleComparison (n : ℕ) (x : (complexTower P hP).cycles Y n) :
    Ext.{w} A Y n :=
  (Ext.mk₀ (complexAugmentationIso P πP zP eP).inv).comp
    ((complexTower P hP).cocycleComparison Y n x) (zero_add n)

/-- The positive-degree augmented isomorphism has exactly the original all-degree representative comparison. -/
theorem augmentedComplexCocycleComparison_mk (ha : ComplexAcyclicAgainst P Y) (n : ℕ)
    (x : (complexTower P hP).cycles Y (n+1)) :
    augmentedComplexExtEquiv P Y hP πP zP eP ha n (QuotientAddGroup.mk x) =
      augmentedComplexCocycleComparison P Y hP πP zP eP (n+1) x := rfl

variable {P} {Q : ChainComplex C ℕ} (f : P ⟶ Q) (hQ : ∀ n, Q.ExactAt (n+1))
variable {B : C} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0)
variable (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πQ]

/-- The original all-degree augmented Yoneda representative preserves every original augmentation square. -/
theorem augmentedComplexCocycleComparison_source (a : A ⟶ B) (ha : f.f 0 ≫ πQ=πP ≫ a)
    (n : ℕ) (x : (complexTower Q hQ).cycles Y n) :
    augmentedComplexCocycleComparison P Y hP πP zP eP n ((complexSourceMap f hP hQ).cycles Y n x) =
      (Ext.mk₀ a).comp (augmentedComplexCocycleComparison Q Y hQ πQ zQ eQ n x) (zero_add n) := by
  unfold augmentedComplexCocycleComparison
  rw [ExactTower.SourceMap.cocycleComparison,Ext.mk₀_comp_mk₀_assoc]
  change (Ext.mk₀ ((complexAugmentationIso P πP zP eP).inv ≫ complexSyzygyMap f 0)).comp
    ((complexTower Q hQ).cocycleComparison Y n x) (zero_add n) = _
  rw [complexAugmentationIso_source_inv f πP πQ zP zQ eP eQ a ha,Ext.mk₀_comp_mk₀_assoc]

/-- The original augmented Ext isomorphisms are natural under every supplied original augmentation-preserving chain map. -/
theorem augmentedComplexExtEquiv_source (a : A ⟶ B) (ha : f.f 0 ≫ πQ=πP ≫ a)
    (haP : ComplexAcyclicAgainst P Y) (haQ : ComplexAcyclicAgainst Q Y)
    (n : ℕ) (x : (complexTower Q hQ).cohomology Y n) :
    augmentedComplexExtEquiv P Y hP πP zP eP haP n ((complexSourceMap f hP hQ).cohomologyAt Y (n+1) x) =
      (Ext.mk₀ a).comp (augmentedComplexExtEquiv Q Y hQ πQ zQ eQ haQ n x) (zero_add (n+1)) := by
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective x
  change augmentedComplexExtEquiv P Y hP πP zP eP haP n
    ((complexSourceMap f hP hQ).cohomologyAt Y (n+1) ((complexTower Q hQ).classAt Y (n+1) x)) = _
  rw [ExactTower.SourceMap.cohomologyAt_class]
  change augmentedComplexCocycleComparison P Y hP πP zP eP (n+1)
    ((complexSourceMap f hP hQ).cycles Y (n+1) x) =
      (Ext.mk₀ a).comp (augmentedComplexCocycleComparison Q Y hQ πQ zQ eQ (n+1) x) (zero_add (n+1))
  exact augmentedComplexCocycleComparison_source Y hP πP zP eP f hQ πQ zQ eQ a ha (n+1) x

end BPFixedPoints.ExtResolutionTools
