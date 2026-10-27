import BPFixedPoints.Incidence.AcyclicResolutionSourceMaps
import BPFixedPoints.Incidence.AcyclicResolutionDegreeScalars

/-! # Original source pullback commutes with original geometric target actions -/

namespace BPFixedPoints.ExtResolutionTools.ExactTower.SourceMap
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe v u r
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {T S : ExactTower C} (f : SourceMap T S)

/-- Original source precomposition commutes with every original target postcomposition on cocycles. -/
theorem cycles_postcomp {Y Z : C} (g : Y ⟶ Z) (n : ℕ) (x : S.cycles Y n) :
    f.cycles Z n (S.mapCycles g n x) = T.mapCycles g n (f.cycles Y n x) := by
  apply Subtype.ext
  change f.term n ≫ (x.val ≫ g) = (f.term n ≫ x.val) ≫ g
  exact (Category.assoc _ _ _).symm

/-- The same original source and target operations commute through the original boundary quotients in all degrees. -/
theorem cohomologyAt_postcomp {Y Z : C} (g : Y ⟶ Z) (n : ℕ) (x : S.cohomologyAt Y n) :
    f.cohomologyAt Z n (S.mapAt g n x) = T.mapAt g n (f.cohomologyAt Y n x) := by
  obtain ⟨x,rfl⟩ := S.classAt_surjective Y n x
  rw [mapAt_class,f.cohomologyAt_class,f.cohomologyAt_class,mapAt_class]
  exact congrArg (T.classAt Z n) (f.cycles_postcomp g n x)

variable {R : Type r} [Ring R] {Y : C} (ρ : R →+* End Y)

/-- Original source pullback is linear for the independently specified original target-endomorphism actions. -/
noncomputable def cohomologyAtLinear (n : ℕ) :
    letI := S.cohomologyAtModule ρ n
    letI := T.cohomologyAtModule ρ n
    S.cohomologyAt Y n →ₗ[R] T.cohomologyAt Y n := by
  letI := S.cohomologyAtModule ρ n
  letI := T.cohomologyAtModule ρ n
  refine { f.cohomologyAt Y n with map_smul' := ?_ }
  intro a x
  exact f.cohomologyAt_postcomp (ρ a).asHom n x

/-- Linearization retains exactly the original pullback on every original class. -/
theorem cohomologyAtLinear_apply (n : ℕ) (x : S.cohomologyAt Y n) :
    letI := S.cohomologyAtModule ρ n
    letI := T.cohomologyAtModule ρ n
    f.cohomologyAtLinear ρ n x = f.cohomologyAt Y n x := rfl

end BPFixedPoints.ExtResolutionTools.ExactTower.SourceMap
