import BPFixedPoints.Incidence.ResolutionNativeExtRoofs
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Original Hom boundaries have their original native null-homotopy

The same preceding cochain is the only nonzero homotopy component.
Native extension and localization therefore kill original boundaries,
without choosing representatives or changing the original differential.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ) {Y : C} (n : ℕ) (g : P.X n ⟶ Y)

/-- The original preceding cochain placed in its original native homotopy degree. -/
def boundaryHomotopyFamily (p q : ℕ) (hpq : (ComplexShape.down ℕ).Rel q p) :
    P.X p ⟶ ((single C (ComplexShape.down ℕ) (n+1)).obj Y).X q := by
  by_cases hp : p=n
  · subst p
    have hq : q=n+1 := hpq.symm
    subst q
    exact g ≫ (singleObjXSelf (ComplexShape.down ℕ) (n+1) Y).inv
  · exact 0

/-- Every original boundary cocycle map is null-homotopic by that same original primitive. -/
def closedBoundaryHomotopy : Homotopy
    (closedChainMap P (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp])) 0 := by
  have he : closedChainMap P (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp]) =
      Homotopy.nullHomotopicMap' (boundaryHomotopyFamily P n g) := by
    apply to_single_hom_ext
    rw [closedChainMap_component,Homotopy.nullHomotopicMap'_f
      (k₂ := n+2) (k₀ := n) (by rfl) (by rfl)]
    simp [boundaryHomotopyFamily,Category.assoc]
  rw [he]
  exact Homotopy.nullHomotopy' (boundaryHomotopyFamily P n g)

/-- Native negative extension retains the same original boundary null-homotopy. -/
def negativeBoundaryHomotopy : Homotopy
    (negativeCocycleMap P (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp])) 0 := by
  simpa only [negativeCocycleMap,negativeMap,extendMap_zero,zero_comp] using
    ((closedBoundaryHomotopy P n g).extend ComplexShape.embeddingDownNat).compRight
      (negativeSingleIso (n+1) Y).hom

variable [HasDerivedCategory.{w} C]

/-- The original preceding boundary gives zero as an actual native derived-category morphism. -/
theorem negativeBoundary_localization_zero :
    DerivedCategory.Q.map (negativeCocycleMap P (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp])) = 0 := by
  simpa only [Functor.map_zero] using DerivedCategory.Q_map_eq_of_homotopy C (negativeBoundaryHomotopy P n g)

variable {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n+1))

/-- The native augmentation roof kills the originally specified boundary representatives. -/
theorem nativeCocycleRoof_boundary :
    nativeCocycleRoof P π z e hP (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp]) = 0 := by
  unfold nativeCocycleRoof
  rw [negativeBoundary_localization_zero,comp_zero]

variable [HasExt.{w'} C]

/-- The same original boundary is zero in Mathlib's original Ext group. -/
theorem nativeCocycleExt_boundary :
    nativeCocycleExt P π z e hP (n+1) (P.d (n+1) n ≫ g)
      (by rw [← Category.assoc,P.d_comp_d,zero_comp]) = 0 := by
  apply Ext.ext
  rw [nativeCocycleExt_hom,nativeCocycleRoof_boundary,zero_comp,Ext.zero_hom]

end
end BPFixedPoints.ExtResolutionTools
