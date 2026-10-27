import BPFixedPoints.Incidence.AcyclicResolutionSourceMaps

/-! # The original Yoneda comparison is natural in the original resolution source

Use Mathlib's naturality of the original short exact extension class.
No acyclicity is needed for the representative formulas; acyclicity is
used only where the existing comparisons are asserted to be isomorphisms.
-/

namespace BPFixedPoints.ExtResolutionTools.ExactTower.SourceMap
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {T S : ExactTower C} (f : SourceMap T S) (Y : C)

/-- The original Yoneda connecting step retains each original short-exact-sequence source map. -/
theorem step (q : ℕ) (x : Ext.{w} (S.K 1) Y q) :
    T.step Y q ((Ext.mk₀ (f.syzygy 1)).comp x (zero_add q)) =
      (Ext.mk₀ (f.syzygy 0)).comp (S.step Y q x) (zero_add (q+1)) := by
  have he := ShortComplex.ShortExact.extClass_naturality (T.shortExact 0) (S.shortExact 0) (f.sequence 0)
  change (T.shortExact 0).extClass.comp (Ext.mk₀ (f.syzygy 1)) (add_zero 1) =
    (Ext.mk₀ (f.syzygy 0)).comp (S.shortExact 0).extClass (zero_add 1) at he
  change (T.shortExact 0).extClass.comp ((Ext.mk₀ (f.syzygy 1)).comp x (zero_add q)) (by omega) =
    (Ext.mk₀ (f.syzygy 0)).comp ((S.shortExact 0).extClass.comp x (by omega)) (zero_add (q+1))
  rw [← Ext.comp_assoc_of_second_deg_zero,he]
  exact Ext.comp_assoc _ _ _ (zero_add 1) (by omega) (by omega)

/-- All original iterated Yoneda connecting classes retain the original resolution source map. -/
theorem connecting (n : ℕ) : ∀ {T S : ExactTower C} (f : SourceMap T S) (x : Ext.{w} (S.K n) Y 0),
    T.connecting Y n ((Ext.mk₀ (f.syzygy n)).comp x (zero_add 0)) =
      (Ext.mk₀ (f.syzygy 0)).comp (S.connecting Y n x) (zero_add n) := by
  induction n with
  | zero => intro T S f x; rfl
  | succ n ih =>
    intro T S f x
    change T.step Y n (T.tail.connecting Y n ((Ext.mk₀ (f.syzygy (n+1))).comp x (zero_add 0))) = _
    exact (congrArg (T.step Y n) (ih f.tail x)).trans (f.step Y n (S.tail.connecting Y n x))

/-- Every original closed cochain retains its specified original Yoneda class under resolution pullback. -/
theorem cocycleComparison (n : ℕ) (x : S.cycles Y n) :
    T.cocycleComparison Y n (f.cycles Y n x) =
      (Ext.mk₀ (f.syzygy 0)).comp (S.cocycleComparison Y n x) (zero_add n) := by
  change T.connecting Y n (Ext.mk₀ (T.cycleEquiv Y n (f.cycles Y n x))) = _
  rw [f.cycleEquiv,← Ext.mk₀_comp_mk₀,connecting Y n f]
  rfl

/-- The original all-degree resolution-to-Ext isomorphism is natural under original source pullback. -/
theorem cohomologyAtExtEquiv (hT : T.AcyclicAgainst Y) (hS : S.AcyclicAgainst Y)
    (n : ℕ) (x : S.cohomologyAt Y n) :
    T.cohomologyAtExtEquiv Y hT n (f.cohomologyAt Y n x) =
      (Ext.mk₀ (f.syzygy 0)).comp (S.cohomologyAtExtEquiv Y hS n x) (zero_add n) := by
  obtain ⟨x,rfl⟩ := S.classAt_surjective Y n x
  rw [f.cohomologyAt_class,T.cohomologyAtExtEquiv_class,S.cohomologyAtExtEquiv_class]
  exact f.cocycleComparison Y n x

end BPFixedPoints.ExtResolutionTools.ExactTower.SourceMap
