import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Specified Ext comparison from an exact tower with relatively acyclic terms

Only the actual positive Ext groups of the resolution terms against the target
are required to vanish. The terms need not be projective, and no linear splitting
of a surjection is chosen. All comparison maps use the original extension classes.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Original syzygies and original short exact presentations of an augmented resolution. -/
structure ExactTower (C : Type u) [Category.{v} C] [Abelian C] where
  K : ℕ → C
  P : ℕ → C
  inclusion (n : ℕ) : K (n+1) ⟶ P n
  projection (n : ℕ) : P n ⟶ K n
  zero (n : ℕ) : inclusion n ≫ projection n = 0
  shortExact (n : ℕ) : (ShortComplex.mk (inclusion n) (projection n) (zero n)).ShortExact

namespace ExactTower
variable (T : ExactTower C) (Y : C)

/-- The original short exact sequence at a specified resolution degree. -/
def sequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (T.inclusion n) (T.projection n) (T.zero n)

instance projection_epi (n : ℕ) : Epi (T.projection n) := (T.shortExact n).epi_g
instance inclusion_mono (n : ℕ) : Mono (T.inclusion n) := (T.shortExact n).mono_f

/-- Shift the original presentations by one, without changing any original map. -/
def tail : ExactTower C where
  K n := T.K (n+1)
  P n := T.P (n+1)
  inclusion n := T.inclusion (n+1)
  projection n := T.projection (n+1)
  zero n := T.zero (n+1)
  shortExact n := T.shortExact (n+1)

/-- Relative acyclicity refers to the original target and actual positive Ext groups. -/
def AcyclicAgainst : Prop :=
  ∀ n k (x : Ext.{w} (T.P n) Y (k+1)), x = 0

/-- The original Yoneda connecting map of the first specified presentation. -/
noncomputable def step (q : ℕ) : Ext.{w} (T.K 1) Y q →+ Ext.{w} (T.K 0) Y (q+1) :=
  (T.shortExact 0).extClass.precomp Y (by omega)

/-- Iterate the original extension-class connecting maps, retaining every original syzygy. -/
noncomputable def connecting (T : ExactTower C) (Y : C) :
    (q : ℕ) → Ext.{w} (T.K q) Y 0 →+ Ext.{w} (T.K 0) Y q
  | 0 => AddMonoidHom.id _
  | q+1 => (T.step Y q).comp (connecting T.tail Y q)

/-- The original restriction from the preceding resolution term on degree-zero Ext. -/
noncomputable def restriction (q : ℕ) : Ext.{w} (T.P q) Y 0 →+ Ext.{w} (T.K (q+1)) Y 0 :=
  (Ext.mk₀ (T.inclusion q)).precomp Y (zero_add 0)

/-- Relative acyclicity is inherited by the original tail resolution. -/
theorem acyclic_tail (h : T.AcyclicAgainst Y) : T.tail.AcyclicAgainst Y :=
  fun n k x => h (n+1) k x

/-- The original connecting map is onto when the next positive Ext of its original middle term vanishes. -/
theorem step_surjective (h : T.AcyclicAgainst Y) (q : ℕ) : Function.Surjective (T.step Y q) := by
  intro x
  exact Ext.contravariant_sequence_exact₃ (T.shortExact 0) Y x (h 0 q _) (by omega)

/-- In positive source degree the original connecting map is injective by actual middle-term acyclicity. -/
theorem step_injective (h : T.AcyclicAgainst Y) (q : ℕ) : Function.Injective (T.step Y (q+1)) := by
  intro x y he
  have hz : T.step Y (q+1) (x-y) = 0 := by rw [map_sub,he,sub_self]
  obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₁ (T.shortExact 0) Y (x-y) (by omega) hz
  rw [h 0 q z,Ext.comp_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- Every actual Ext class is represented through the original iterated connecting maps. -/
theorem connecting_surjective (q : ℕ) :
    ∀ (T : ExactTower C) (h : T.AcyclicAgainst Y), Function.Surjective (T.connecting Y q) := by
  induction q with
  | zero => intro T _ x; exact ⟨x,rfl⟩
  | succ q ih =>
    intro T h
    exact (T.step_surjective Y h q).comp (ih T.tail (T.acyclic_tail Y h))

/-- The kernel of the original all-degree comparison is exactly the preceding original restriction image. -/
theorem connecting_ker (q : ℕ) :
    ∀ (T : ExactTower C) (h : T.AcyclicAgainst Y),
      (T.restriction Y q).range = (T.connecting Y (q+1)).ker := by
  induction q with
  | zero =>
    intro T _
    exact (Ext.contravariant_sequence_exact₁' (T.shortExact 0) Y 0 1 rfl).ab_range_eq_ker
  | succ q ih =>
    intro T h
    have hk : (T.connecting Y (q+1+1)).ker = (T.tail.connecting Y (q+1)).ker := by
      ext x
      change T.step Y (q+1) (T.tail.connecting Y (q+1) x) = 0 ↔ T.tail.connecting Y (q+1) x = 0
      rw [← (T.step Y (q+1)).map_zero]
      exact (T.step_injective Y h q).eq_iff
    rw [hk]
    exact ih T.tail (T.acyclic_tail Y h)

/-- Actual Ext is the original syzygy Hom cokernel, through the original extension classes in every positive degree. -/
noncomputable def quotientEquiv (q : ℕ) (h : T.AcyclicAgainst Y) :
    (Ext.{w} (T.K (q+1)) Y 0 ⧸ (T.restriction Y q).range) ≃+ Ext.{w} (T.K 0) Y (q+1) :=
  (QuotientAddGroup.quotientAddEquivOfEq (T.connecting_ker Y q h)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (T.connecting Y (q+1))
      (T.connecting_surjective Y (q+1) h))

/-- Each original representative is sent by the original iterated connecting map, not by an arbitrary group isomorphism. -/
theorem quotientEquiv_mk (q : ℕ) (h : T.AcyclicAgainst Y) (x : Ext.{w} (T.K (q+1)) Y 0) :
    T.quotientEquiv Y q h (QuotientAddGroup.mk x) = T.connecting Y (q+1) x := rfl

/-- Iterated connecting maps preserve the original postcomposition by every target morphism. -/
theorem connecting_postcomp {Y Z : C} (f : Y ⟶ Z) (q : ℕ) :
    ∀ (T : ExactTower C) (x : Ext.{w} (T.K q) Y 0),
      T.connecting Z q (x.comp (Ext.mk₀ f) (add_zero 0)) =
        (T.connecting Y q x).comp (Ext.mk₀ f) (add_zero q) := by
  induction q with
  | zero => intro T x; rfl
  | succ q ih =>
    intro T x
    change T.step Z q (T.tail.connecting Z q (x.comp (Ext.mk₀ f) (add_zero 0))) = _
    rw [ih]
    exact (Ext.comp_assoc_of_third_deg_zero (T.shortExact 0).extClass
      (T.tail.connecting Y q x) (Ext.mk₀ f) (by omega)).symm

end ExactTower
end BPFixedPoints.ExtResolutionTools
