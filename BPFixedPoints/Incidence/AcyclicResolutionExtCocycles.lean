import BPFixedPoints.Incidence.AcyclicResolutionExtTower
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Original resolution cocycles compute actual Ext by the original extension classes -/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ExactTower C) (Y : C)

/-- The original differential between two consecutive resolution terms. -/
def differential (n : ℕ) : T.P (n+1) ⟶ T.P n := T.projection (n+1) ≫ T.inclusion n

/-- The original resolution differential squares to zero by the specified short exact presentations. -/
theorem differential_squared (n : ℕ) : T.differential (n+1) ≫ T.differential n = 0 := by
  simp only [differential,Category.assoc]
  rw [← Category.assoc (T.inclusion (n+1)),T.zero,zero_comp,comp_zero]

/-- The original contravariant Hom differential on resolution cochains. -/
def cochainDifferential (n : ℕ) : (T.P n ⟶ Y) →+ (T.P (n+1) ⟶ Y) where
  toFun f := T.differential n ≫ f
  map_zero' := comp_zero
  map_add' f g := by simp only [Preadditive.comp_add]

/-- Original cocycles, defined by the original Hom differential rather than by Ext or a state module. -/
def cycles (n : ℕ) : AddSubgroup (T.P n ⟶ Y) := (T.cochainDifferential Y n).ker

/-- The original syzygy Hom maps into original resolution cocycles by the original projection. -/
def syzygyToCycles (n : ℕ) : (T.K n ⟶ Y) →+ T.cycles Y n where
  toFun f := ⟨T.projection n ≫ f,by
    change (T.projection (n+1) ≫ T.inclusion n) ≫ (T.projection n ≫ f) = 0
    simp only [Category.assoc]
    rw [← Category.assoc (T.inclusion n),T.zero,zero_comp,comp_zero]⟩
  map_zero' := Subtype.ext comp_zero
  map_add' f g := Subtype.ext (by
    change T.projection n ≫ (f+g) = T.projection n ≫ f + T.projection n ≫ g
    simp only [Preadditive.comp_add])

/-- The syzygy factorization of a cocycle is unique because the original projection is epi. -/
theorem syzygyToCycles_injective (n : ℕ) : Function.Injective (T.syzygyToCycles Y n) := by
  intro f g h
  exact (cancel_epi (T.projection n)).mp (congrArg Subtype.val h)

/-- Original exactness supplies every cocycle factorization through the original syzygy. -/
theorem syzygyToCycles_surjective (n : ℕ) : Function.Surjective (T.syzygyToCycles Y n) := by
  intro x
  have hx : T.inclusion n ≫ x.val = 0 := by
    apply (cancel_epi (T.projection (n+1))).mp
    have hx' : T.differential n ≫ x.val = 0 := x.property
    simpa only [differential,Category.assoc,comp_zero] using hx'
  refine ⟨(T.shortExact n).exact.desc x.val hx,?_⟩
  apply Subtype.ext
  exact (T.shortExact n).exact.g_desc x.val hx

/-- Original Hom cocycles are the original syzygy Hom, by the specified epi factorization. -/
noncomputable def cycleEquiv (n : ℕ) : T.cycles Y n ≃+ (T.K n ⟶ Y) :=
  (AddEquiv.ofBijective (T.syzygyToCycles Y n)
    ⟨T.syzygyToCycles_injective Y n,T.syzygyToCycles_surjective Y n⟩).symm

/-- The cocycle comparison retains precisely the original factorization through the original projection. -/
theorem cycleEquiv_projection (n : ℕ) (x : T.cycles Y n) :
    T.projection n ≫ T.cycleEquiv Y n x = x.val :=
  congrArg Subtype.val ((T.cycleEquiv Y n).symm_apply_apply x)

/-- The original preceding Hom differential, with its original cocycle codomain. -/
def boundary (n : ℕ) : (T.P n ⟶ Y) →+ T.cycles Y (n+1) where
  toFun f := ⟨T.differential n ≫ f,by
    change T.differential (n+1) ≫ (T.differential n ≫ f) = 0
    rw [← Category.assoc,T.differential_squared,zero_comp]⟩
  map_zero' := Subtype.ext comp_zero
  map_add' f g := Subtype.ext (by
    change T.differential n ≫ (f+g) = T.differential n ≫ f + T.differential n ≫ g
    simp only [Preadditive.comp_add])

/-- Each original boundary factors through the original syzygy inclusion, with no sign or map replacement. -/
theorem cycleEquiv_boundary (n : ℕ) (f : T.P n ⟶ Y) :
    T.cycleEquiv Y (n+1) (T.boundary Y n f) = T.inclusion n ≫ f := by
  apply (cancel_epi (T.projection (n+1))).mp
  rw [T.cycleEquiv_projection]
  exact Category.assoc _ _ _

variable [HasExt.{w} C]

/-- The specified comparison uses the original cocycle factorization and original iterated extension classes. -/
noncomputable def cocycleComparison (n : ℕ) : T.cycles Y n →+ Ext.{w} (T.K 0) Y n :=
  (T.connecting Y n).comp (Ext.addEquiv₀.symm.toAddMonoidHom.comp (T.cycleEquiv Y n).toAddMonoidHom)

/-- Every actual Ext class is represented by an original resolution cocycle under relative term acyclicity. -/
theorem cocycleComparison_surjective (n : ℕ) (h : T.AcyclicAgainst Y) :
    Function.Surjective (T.cocycleComparison Y n) := by
  intro x
  obtain ⟨z,hz⟩ := T.connecting_surjective Y n h x
  obtain ⟨f,hf⟩ := (Ext.mk₀_bijective (T.K n) Y).surjective z
  refine ⟨(T.cycleEquiv Y n).symm f,?_⟩
  change T.connecting Y n (Ext.mk₀ (T.cycleEquiv Y n ((T.cycleEquiv Y n).symm f))) = _
  rw [AddEquiv.apply_symm_apply,hf,hz]

/-- Precisely the original Hom boundaries are killed by the specified actual Ext comparison. -/
theorem cocycleComparison_ker (n : ℕ) (h : T.AcyclicAgainst Y) :
    (T.boundary Y n).range = (T.cocycleComparison Y (n+1)).ker := by
  ext x
  constructor
  · rintro ⟨f,rfl⟩
    change T.connecting Y (n+1) (Ext.mk₀ (T.cycleEquiv Y (n+1) (T.boundary Y n f))) = 0
    rw [T.cycleEquiv_boundary]
    have hx : Ext.mk₀ (T.inclusion n ≫ f) ∈ (T.restriction Y n).range :=
      ⟨Ext.mk₀ f,Ext.mk₀_comp_mk₀ (T.inclusion n) f⟩
    rw [T.connecting_ker Y n h] at hx
    exact hx
  · intro hx
    change T.connecting Y (n+1) (Ext.mk₀ (T.cycleEquiv Y (n+1) x)) = 0 at hx
    have hz : Ext.mk₀ (T.cycleEquiv Y (n+1) x) ∈ (T.restriction Y n).range := by
      rw [T.connecting_ker Y n h]
      exact hx
    obtain ⟨z,hz⟩ := hz
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective (T.P n) Y).surjective z
    have hf : T.inclusion n ≫ f = T.cycleEquiv Y (n+1) x := by
      apply (Ext.mk₀_bijective _ _).injective
      exact (Ext.mk₀_comp_mk₀ (T.inclusion n) f).symm.trans hz
    refine ⟨f,(T.cycleEquiv Y (n+1)).injective ?_⟩
    rw [T.cycleEquiv_boundary,hf]

/-- Positive cohomology of the original Hom complex, using its original preceding boundaries. -/
abbrev cohomology (n : ℕ) := T.cycles Y (n+1) ⧸ (T.boundary Y n).range

/-- The original Hom-complex cohomology equals actual Ext through the original connecting classes in every positive degree. -/
noncomputable def cohomologyEquiv (n : ℕ) (h : T.AcyclicAgainst Y) :
    T.cohomology Y n ≃+ Ext.{w} (T.K 0) Y (n+1) :=
  (QuotientAddGroup.quotientAddEquivOfEq (T.cocycleComparison_ker Y n h)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (T.cocycleComparison Y (n+1))
      (T.cocycleComparison_surjective Y (n+1) h))

/-- Each original cocycle representative retains exactly its original factorization and iterated native connecting class. -/
theorem cohomologyEquiv_mk (n : ℕ) (h : T.AcyclicAgainst Y) (x : T.cycles Y (n+1)) :
    T.cohomologyEquiv Y n h (QuotientAddGroup.mk x) = T.cocycleComparison Y (n+1) x := rfl

end BPFixedPoints.ExtResolutionTools.ExactTower
