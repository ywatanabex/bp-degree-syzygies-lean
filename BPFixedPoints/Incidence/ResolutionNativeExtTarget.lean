import BPFixedPoints.Incidence.ResolutionNativeExtComparison

/-! # Native resolution Ext roofs preserve the original target maps -/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n+1))

/-- Every original target morphism is retained by the native Ext roof in every degree. -/
theorem nativeCocycleExt_postcomp {Y Z : C} (n : ℕ) (x : P.X n ⟶ Y)
    (hx : P.d (n+1) n ≫ x=0) (g : Y ⟶ Z) (hxg : P.d (n+1) n ≫ (x ≫ g)=0) :
    nativeCocycleExt P π z e hP n (x ≫ g) hxg =
      (nativeCocycleExt P π z e hP n x hx).comp (Ext.mk₀ g) (add_zero n) := by
  apply Ext.ext
  rw [nativeCocycleExt_hom,Ext.comp_hom,Ext.mk₀_hom,ShiftedHom.comp_mk₀,nativeCocycleExt_hom]
  unfold nativeCocycleRoof
  rw [negativeCocycleMap_postcomp P n x hx g hxg,Functor.map_comp]
  simp only [Category.assoc]
  apply congrArg (fun f => (nativeAugmentationIso P π z e hP).inv ≫
    DerivedCategory.Q.map (negativeCocycleMap P n x hx) ≫ f)
  exact ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.naturality g

/-- Native cohomology comparison preserves postcomposition by every original target morphism. -/
theorem nativeCycleComparison_postcomp {Y Z : C} (g : Y ⟶ Z) (n : ℕ)
    (x : (complexTower P hP).cycles Y n) :
    nativeCycleComparison P π z e hP Z n ((complexTower P hP).mapCycles g n x) =
      (nativeCycleComparison P π z e hP Y n x).comp (Ext.mk₀ g) (add_zero n) := by
  exact nativeCocycleExt_postcomp P π z e hP n x.val _ g _

end
end BPFixedPoints.ExtResolutionTools
