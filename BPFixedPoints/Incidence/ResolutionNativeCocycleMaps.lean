import BPFixedPoints.Incidence.AugmentedComplexNativeQuasiIso
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Original resolution cocycles are native maps to single complexes

The negative cochain model is Mathlib's original extension along the
embedding n ↦ -n. No differential or representative is transported from
cohomology or from a state model.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ) {Y : C} (n : ℕ)

/-- A closed original homogeneous cochain is the native chain map to its original single degree. -/
def closedChainMap (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    P ⟶ (single C (ComplexShape.down ℕ) n).obj Y :=
  mkHomToSingle x (by
    intro i hi
    have hi' : i=n+1 := hi.symm
    subst i
    exact hx)

/-- The native map retains the specified original homogeneous cochain. -/
@[simp] theorem closedChainMap_component (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    (closedChainMap P n x hx).f n=x ≫ (singleObjXSelf (ComplexShape.down ℕ) n Y).inv :=
  mkHomToSingle_f _ _

/-- The original nonnegative chain complex in native negative integer cochain degrees. -/
abbrev negativeComplex := P.extend ComplexShape.embeddingDownNat

/-- The original chain map in the native negative integer cochain model. -/
abbrev negativeMap {Q : ChainComplex C ℕ} (f : P ⟶ Q) :=
  extendMap f ComplexShape.embeddingDownNat

/-- Extending the original single degree uses the native embedding isomorphism. -/
def negativeSingleIso (Y : C) :
    ((single C (ComplexShape.down ℕ) n).obj Y).extend ComplexShape.embeddingDownNat ≅
      (single C (ComplexShape.up ℤ) (-(n : ℤ))).obj Y :=
  extendSingleIso ComplexShape.embeddingDownNat Y n (-(n : ℤ)) rfl

/-- The original cocycle gives its specified native negative-degree cochain map. -/
def negativeCocycleMap (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    negativeComplex P ⟶ (single C (ComplexShape.up ℤ) (-(n : ℤ))).obj Y :=
  negativeMap P (closedChainMap P n x hx) ≫ (negativeSingleIso n Y).hom

/-- The native negative cochain map retains exactly the original cocycle coefficient and degree. -/
theorem negativeCocycleMap_component (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    (negativeCocycleMap P n x hx).f (-(n : ℤ)) =
      (P.extendXIso ComplexShape.embeddingDownNat (by rfl : ComplexShape.embeddingDownNat.f n=-(n : ℤ))).hom ≫
        x ≫ (singleObjXSelf (ComplexShape.up ℤ) (-(n : ℤ)) Y).inv := by
  simp only [negativeCocycleMap,negativeMap,comp_f]
  rw [extendMap_f (closedChainMap P n x hx) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) (by rfl)]
  simp [negativeSingleIso,extendSingleIso_hom_f,closedChainMap_component,Category.assoc]

/-- In degree zero this is the same original augmentation chain map. -/
theorem closedChainMap_zero {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0) :
    closedChainMap P 0 π z=augmentationChainMap P π z := rfl

/-- Precomposition by the original chain map retains the original homogeneous cocycle map. -/
theorem closedChainMap_source {Q : ChainComplex C ℕ} (f : P ⟶ Q)
    (x : Q.X n ⟶ Y) (hx : Q.d (n+1) n ≫ x=0)
    (hf : P.d (n+1) n ≫ (f.f n ≫ x)=0) :
    closedChainMap P n (f.f n ≫ x) hf=f ≫ closedChainMap Q n x hx := by
  apply to_single_hom_ext
  simp only [comp_f,closedChainMap_component,Category.assoc]

/-- Extending original cocycle maps preserves the original source precomposition. -/
theorem negativeCocycleMap_source {Q : ChainComplex C ℕ} (f : P ⟶ Q)
    (x : Q.X n ⟶ Y) (hx : Q.d (n+1) n ≫ x=0)
    (hf : P.d (n+1) n ≫ (f.f n ≫ x)=0) :
    negativeCocycleMap P n (f.f n ≫ x) hf=negativeMap P f ≫ negativeCocycleMap Q n x hx := by
  simp only [negativeCocycleMap,negativeMap,closedChainMap_source P n f x hx hf,
    extendMap_comp,Category.assoc]

end
end BPFixedPoints.ExtResolutionTools
