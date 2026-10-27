import BPFixedPoints.Incidence.AcyclicResolutionExtCocycles

/-! # Target naturality of the original resolution-to-Ext comparison -/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ExactTower C) {Y Z : C}

/-- Postcomposition by the original target morphism on original Hom cocycles. -/
def mapCycles (f : Y ⟶ Z) (n : ℕ) : T.cycles Y n →+ T.cycles Z n where
  toFun x := ⟨x.val ≫ f,by
    change T.differential n ≫ (x.val ≫ f) = 0
    rw [← Category.assoc,show T.differential n ≫ x.val = 0 from x.property,zero_comp]⟩
  map_zero' := Subtype.ext zero_comp
  map_add' x y := Subtype.ext (by
    change (x.val+y.val) ≫ f = x.val ≫ f + y.val ≫ f
    simp only [Preadditive.add_comp])

/-- Original cocycle factorization commutes with every actual target morphism. -/
theorem cycleEquiv_postcomp (f : Y ⟶ Z) (n : ℕ) (x : T.cycles Y n) :
    T.cycleEquiv Z n (T.mapCycles f n x) = T.cycleEquiv Y n x ≫ f := by
  apply (cancel_epi (T.projection n)).mp
  rw [T.cycleEquiv_projection,← Category.assoc,T.cycleEquiv_projection]
  rfl

/-- Postcomposition preserves the original boundary representative itself. -/
theorem mapCycles_boundary (f : Y ⟶ Z) (n : ℕ) (g : T.P n ⟶ Y) :
    T.mapCycles f (n+1) (T.boundary Y n g) = T.boundary Z n (g ≫ f) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The original target morphism induces the original quotient map on Hom-complex cohomology. -/
def mapCohomology (f : Y ⟶ Z) (n : ℕ) : T.cohomology Y n →+ T.cohomology Z n :=
  QuotientAddGroup.map _ _ (T.mapCycles f (n+1)) (by
    rintro x ⟨g,rfl⟩
    exact ⟨g ≫ f,(T.mapCycles_boundary f n g).symm⟩)

/-- Every original quotient representative retains its original postcomposition. -/
theorem mapCohomology_mk (f : Y ⟶ Z) (n : ℕ) (x : T.cycles Y (n+1)) :
    T.mapCohomology f n (QuotientAddGroup.mk x) = QuotientAddGroup.mk (T.mapCycles f (n+1) x) := rfl

variable [HasExt.{w} C]

/-- The specified comparison on all original cocycles is natural in the actual target. -/
theorem cocycleComparison_postcomp (f : Y ⟶ Z) (n : ℕ) (x : T.cycles Y n) :
    T.cocycleComparison Z n (T.mapCycles f n x) =
      (T.cocycleComparison Y n x).comp (Ext.mk₀ f) (add_zero n) := by
  change T.connecting Z n (Ext.mk₀ (T.cycleEquiv Z n (T.mapCycles f n x))) = _
  rw [T.cycleEquiv_postcomp,← Ext.mk₀_comp_mk₀,T.connecting_postcomp]
  rfl

/-- The actual Ext isomorphism preserves every original target morphism on every cohomology class. -/
theorem cohomologyEquiv_postcomp (f : Y ⟶ Z) (n : ℕ)
    (hY : T.AcyclicAgainst Y) (hZ : T.AcyclicAgainst Z) (x : T.cohomology Y n) :
    T.cohomologyEquiv Z n hZ (T.mapCohomology f n x) =
      (T.cohomologyEquiv Y n hY x).comp (Ext.mk₀ f) (add_zero (n+1)) := by
  induction x using QuotientAddGroup.induction_on with
  | _ x => exact T.cocycleComparison_postcomp f (n+1) x

end BPFixedPoints.ExtResolutionTools.ExactTower
