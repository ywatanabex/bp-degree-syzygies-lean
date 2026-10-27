import BPFixedPoints.Incidence.ResolutionNativeBoundaryHomotopy
import BPFixedPoints.Incidence.AcyclicResolutionAugmentedSourceNaturality

/-! # The original Hom quotient maps to native derived-roof Ext classes

Original boundaries are killed by their original native null-homotopy.
Degree zero agrees with the existing original augmented Yoneda comparison.
No positive-degree agreement or bijectivity is included without proof.
-/

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

private theorem closedChainMap_map_zero (Y : C) (n : ℕ) (h : P.d (n+1) n ≫ (0 : P.X n ⟶ Y)=0) :
    closedChainMap P n (0 : P.X n ⟶ Y) h=0 := by
  apply to_single_hom_ext
  simp [closedChainMap_component]

private theorem negativeCocycleMap_add {Y : C} (n : ℕ) (x y : P.X n ⟶ Y)
    (hx : P.d (n+1) n ≫ x=0) (hy : P.d (n+1) n ≫ y=0)
    (hxy : P.d (n+1) n ≫ (x+y)=0) :
    negativeCocycleMap P n (x+y) hxy=negativeCocycleMap P n x hx+negativeCocycleMap P n y hy := by
  have h : closedChainMap P n (x+y) hxy=closedChainMap P n x hx+closedChainMap P n y hy := by
    apply to_single_hom_ext
    simp only [closedChainMap_component,add_f_apply,Preadditive.add_comp]
  simp only [negativeCocycleMap,negativeMap,h,extendMap_add,Preadditive.add_comp]

/-- The native Ext representative of the zero original cochain is zero. -/
theorem nativeCocycleExt_zero (Y : C) (n : ℕ) (h : P.d (n+1) n ≫ (0 : P.X n ⟶ Y)=0) :
    nativeCocycleExt P π z e hP n (0 : P.X n ⟶ Y) h=0 := by
  apply Ext.ext
  rw [nativeCocycleExt_hom,Ext.zero_hom]
  unfold nativeCocycleRoof negativeCocycleMap negativeMap
  rw [closedChainMap_map_zero,extendMap_zero,zero_comp,Functor.map_zero,comp_zero,zero_comp]

/-- Original cochain addition is retained by the native Ext roof. -/
theorem nativeCocycleExt_add {Y : C} (n : ℕ) (x y : P.X n ⟶ Y)
    (hx : P.d (n+1) n ≫ x=0) (hy : P.d (n+1) n ≫ y=0)
    (hxy : P.d (n+1) n ≫ (x+y)=0) :
    nativeCocycleExt P π z e hP n (x+y) hxy =
      nativeCocycleExt P π z e hP n x hx+nativeCocycleExt P π z e hP n y hy := by
  apply Ext.ext
  simp only [nativeCocycleExt_hom,Ext.add_hom]
  unfold nativeCocycleRoof
  rw [negativeCocycleMap_add P n x y hx hy hxy,Functor.map_add]
  simp only [Preadditive.comp_add,Preadditive.add_comp]

/-- The original closed-cochain group maps additively to native derived-roof Ext. -/
def nativeCycleComparison (Y : C) (n : ℕ) : (complexTower P hP).cycles Y n →+ Ext.{w'} A Y n where
  toFun x := nativeCocycleExt P π z e hP n x.val (by
    have h : (complexTower P hP).differential n ≫ x.val=0 := x.property
    simpa only [complexTower_differential] using h)
  map_zero' := nativeCocycleExt_zero P π z e hP Y n _
  map_add' x y := nativeCocycleExt_add P π z e hP n x.val y.val _ _ _

/-- The native Ext comparison descends through the same original Hom boundaries in every degree. -/
def nativeCohomologyAtComparison (Y : C) (n : ℕ) :
    (complexTower P hP).cohomologyAt Y n →+ Ext.{w'} A Y n :=
  (complexTower P hP).liftAt n (nativeCycleComparison P π z e hP Y n) (by
    cases n with
    | zero => trivial
    | succ n =>
      intro g
      change nativeCocycleExt P π z e hP (n+1) ((complexTower P hP).differential n ≫ g) _=0
      simpa only [complexTower_differential] using nativeCocycleExt_boundary P n g π z e hP)

/-- Every original quotient representative retains its own original native Ext roof. -/
theorem nativeCohomologyAtComparison_class (Y : C) (n : ℕ) (x : (complexTower P hP).cycles Y n) :
    nativeCohomologyAtComparison P π z e hP Y n ((complexTower P hP).classAt Y n x) =
      nativeCycleComparison P π z e hP Y n x :=
  (complexTower P hP).liftAt_class _ _ _ x

/-- The native degree-zero roof equals the existing original augmented Yoneda representative. -/
theorem nativeCycleComparison_zero_yoneda (Y : C) (x : (complexTower P hP).cycles Y 0) :
    nativeCycleComparison P π z e hP Y 0 x = augmentedComplexCocycleComparison P Y hP π z e 0 x := by
  let g := (complexAugmentationIso P π z e).inv ≫ (complexTower P hP).cycleEquiv Y 0 x
  have hg : π ≫ g=x.val := calc
    π ≫ g = (cokernel.π (P.d 1 0) ≫ (complexAugmentationIso P π z e).hom) ≫ g :=
      congrArg (fun k => k ≫ g) (complexAugmentationIso_projection P π z e).symm
    _ = x.val := by
      dsimp only [g]
      rw [Category.assoc,Iso.hom_inv_id_assoc]
      exact (complexTower P hP).cycleEquiv_projection Y 0 x
  change nativeCocycleExt P π z e hP 0 x.val _ =
    (Ext.mk₀ (complexAugmentationIso P π z e).inv).comp
      (Ext.mk₀ ((complexTower P hP).cycleEquiv Y 0 x)) (zero_add 0)
  rw [Ext.mk₀_comp_mk₀]
  have hx : P.d 1 0 ≫ x.val=0 := by
    have h : (complexTower P hP).differential 0 ≫ x.val=0 := x.property
    simpa only [complexTower_differential] using h
  have hn := nativeCocycleExt_zero_factor P π z e hP g (by rw [hg]; exact hx)
  simpa only [hg] using hn

end
end BPFixedPoints.ExtResolutionTools
