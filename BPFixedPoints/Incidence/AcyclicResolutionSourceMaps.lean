import BPFixedPoints.Incidence.AcyclicResolutionCohomologyDegree

/-! # Original source maps of exact resolution towers and their cocycles -/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A map of the original terms and original syzygies preserving both original presentation maps. -/
structure SourceMap (T S : ExactTower C) where
  syzygy (n : ℕ) : T.K n ⟶ S.K n
  term (n : ℕ) : T.P n ⟶ S.P n
  inclusion (n : ℕ) : T.inclusion n ≫ term n = syzygy (n+1) ≫ S.inclusion n
  projection (n : ℕ) : T.projection n ≫ syzygy n = term n ≫ S.projection n

namespace SourceMap
variable {T S : ExactTower C} (f : SourceMap T S)

/-- The original maps of syzygies and terms form a map of the original short exact presentations. -/
def sequence (n : ℕ) : T.sequence n ⟶ S.sequence n where
  τ₁ := f.syzygy (n+1)
  τ₂ := f.term n
  τ₃ := f.syzygy n
  comm₁₂ := (f.inclusion n).symm
  comm₂₃ := (f.projection n).symm

/-- Shift the same original source map along the same original resolution towers. -/
def tail : SourceMap T.tail S.tail where
  syzygy n := f.syzygy (n+1)
  term n := f.term (n+1)
  inclusion n := f.inclusion (n+1)
  projection n := f.projection (n+1)

/-- Source maps preserve the independently specified original Hom differentials. -/
theorem differential (n : ℕ) : T.differential n ≫ f.term n = f.term (n+1) ≫ S.differential n := by
  simp only [ExactTower.differential,Category.assoc]
  rw [f.inclusion,← Category.assoc,f.projection,Category.assoc]

variable (Y : C)

/-- Pull back original closed cochains by the original term map. -/
def cycles (n : ℕ) : S.cycles Y n →+ T.cycles Y n where
  toFun x := ⟨f.term n ≫ x.val,by
    change T.differential n ≫ (f.term n ≫ x.val) = 0
    rw [← Category.assoc,f.differential,Category.assoc]
    have hx : S.differential n ≫ x.val = 0 := x.property
    rw [hx,comp_zero]⟩
  map_zero' := Subtype.ext comp_zero
  map_add' x y := Subtype.ext (by
    change f.term n ≫ (x.val+y.val) = f.term n ≫ x.val + f.term n ≫ y.val
    simp only [Preadditive.comp_add])

/-- Pullback is literally precomposition by the original term map. -/
theorem cycles_val (n : ℕ) (x : S.cycles Y n) : (f.cycles Y n x).val = f.term n ≫ x.val := rfl

/-- Original boundary representatives pull back to the original preceding boundary with its same primitive. -/
theorem cycles_boundary (n : ℕ) (x : S.P n ⟶ Y) :
    f.cycles Y (n+1) (S.boundary Y n x) = T.boundary Y n (f.term n ≫ x) := by
  apply Subtype.ext
  change f.term (n+1) ≫ (S.differential n ≫ x) = T.differential n ≫ (f.term n ≫ x)
  rw [← Category.assoc,← Category.assoc,f.differential]

/-- Original syzygy factorization is natural under the specified original source maps. -/
theorem cycleEquiv (n : ℕ) (x : S.cycles Y n) :
    T.cycleEquiv Y n (f.cycles Y n x) = f.syzygy n ≫ S.cycleEquiv Y n x := by
  apply (cancel_epi (T.projection n)).mp
  rw [T.cycleEquiv_projection,← Category.assoc,f.projection,Category.assoc,S.cycleEquiv_projection]
  rfl

/-- Pullback descends through the original boundary quotient in every nonnegative degree. -/
noncomputable def cohomologyAt (n : ℕ) : S.cohomologyAt Y n →+ T.cohomologyAt Y n :=
  S.liftAt n ((T.classAt Y n).comp (f.cycles Y n)) (by
    cases n with
    | zero => trivial
    | succ n =>
      intro x
      change T.classAt Y (n+1) (f.cycles Y (n+1) (S.boundary Y n x)) = 0
      rw [f.cycles_boundary,T.classAt_boundary])

/-- Every original source pullback class retains the same original closed representative. -/
theorem cohomologyAt_class (n : ℕ) (x : S.cycles Y n) :
    f.cohomologyAt Y n (S.classAt Y n x) = T.classAt Y n (f.cycles Y n x) :=
  S.liftAt_class _ _ _ x

end SourceMap
end BPFixedPoints.ExtResolutionTools.ExactTower
