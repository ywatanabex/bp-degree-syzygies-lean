import BPFixedPoints.Incidence.AcyclicResolutionExtCocycles

/-! # Right recursion of the original iterated Yoneda connecting classes

The original `connecting` is not redefined. Associativity of Mathlib's
actual Ext product gives its rightmost connecting step as well.
-/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The original iterated connecting class can be composed from its original last short exact presentation. -/
theorem connecting_right (n : ℕ) (T : ExactTower C) (Y : C) (x : Ext.{w} (T.K (n+1)) Y 0) :
    T.connecting Y (n+1) x =
      (T.connecting (T.K n) n (Ext.mk₀ (𝟙 (T.K n)))).comp
        ((T.shortExact n).extClass.comp x (add_zero 1)) rfl := by
  induction n generalizing T with
  | zero =>
    change (T.shortExact 0).extClass.comp x (add_zero 1) =
      (Ext.mk₀ (𝟙 (T.K 0))).comp ((T.shortExact 0).extClass.comp x (add_zero 1)) (zero_add 1)
    rw [Ext.mk₀_id_comp]
  | succ n ih =>
    change (T.shortExact 0).extClass.comp (T.tail.connecting Y (n+1) x) (by omega) =
      ((T.shortExact 0).extClass.comp
        (T.tail.connecting (T.K (n+1)) n (Ext.mk₀ (𝟙 (T.K (n+1))))) (by omega : 1+n=n+1)).comp
          ((T.shortExact (n+1)).extClass.comp x (add_zero 1)) (by omega)
    rw [ih T.tail]
    exact (Ext.comp_assoc _ _ _ _ _ (by omega)).symm

/-- The original universal Yoneda projection classes retain their original right connecting recursion. -/
theorem connecting_projection_succ (n : ℕ) (T : ExactTower C) :
    T.connecting (T.K (n+1)) (n+1) (Ext.mk₀ (𝟙 (T.K (n+1)))) =
      (T.connecting (T.K n) n (Ext.mk₀ (𝟙 (T.K n)))).comp (T.shortExact n).extClass (by omega) := by
  rw [connecting_right,Ext.comp_mk₀_id]

/-- Every original connecting representative is the original universal projection class followed by its original target morphism. -/
theorem connecting_projection_postcomp (n : ℕ) (T : ExactTower C) {Y : C} (f : T.K n ⟶ Y) :
    T.connecting Y n (Ext.mk₀ f) =
      (T.connecting (T.K n) n (Ext.mk₀ (𝟙 (T.K n)))).comp (Ext.mk₀ f) (add_zero n) := by
  simpa using T.connecting_postcomp f n (Ext.mk₀ (𝟙 (T.K n)))

end
end BPFixedPoints.ExtResolutionTools.ExactTower
