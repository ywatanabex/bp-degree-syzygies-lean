import BPFixedPoints.Incidence.AcyclicResolutionExtNaturality

/-! # Original target endomorphisms act on resolution cohomology before Ext comparison -/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u r
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ExactTower C) {R : Type r} [Ring R] {Y : C} (ρ : R →+* End Y)

/-- Original scalar endomorphisms act on the original cohomology representatives by postcomposition.
This action is defined on the source Hom complex and does not use any Ext comparison. -/
@[instance_reducible] noncomputable def cohomologyModule (n : ℕ) : Module R (T.cohomology Y n) where
  smul a x := T.mapCohomology (ρ a).asHom n x
  one_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change QuotientAddGroup.mk (T.mapCycles (ρ 1).asHom (n+1) x) = QuotientAddGroup.mk x
      apply congrArg QuotientAddGroup.mk
      apply Subtype.ext
      change x.val ≫ (ρ 1).asHom = x.val
      rw [map_one,End.one_asHom,Category.comp_id]
  mul_smul a b x := by
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change QuotientAddGroup.mk (T.mapCycles (ρ (a*b)).asHom (n+1) x) =
        QuotientAddGroup.mk (T.mapCycles (ρ a).asHom (n+1) (T.mapCycles (ρ b).asHom (n+1) x))
      apply congrArg QuotientAddGroup.mk
      apply Subtype.ext
      change x.val ≫ (ρ (a*b)).asHom = (x.val ≫ (ρ b).asHom) ≫ (ρ a).asHom
      rw [map_mul,End.mul_asHom]
      exact (Category.assoc _ _ _).symm
  smul_add a x y := (T.mapCohomology (ρ a).asHom n).map_add x y
  smul_zero a := (T.mapCohomology (ρ a).asHom n).map_zero
  add_smul a b x := by
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change (QuotientAddGroup.mk' ((T.boundary Y n).range)) (T.mapCycles (ρ (a+b)).asHom (n+1) x) =
        (QuotientAddGroup.mk' _) (T.mapCycles (ρ a).asHom (n+1) x) +
        (QuotientAddGroup.mk' _) (T.mapCycles (ρ b).asHom (n+1) x)
      rw [← map_add]
      apply congrArg (QuotientAddGroup.mk' _)
      apply Subtype.ext
      change x.val ≫ (ρ (a+b)).asHom = x.val ≫ (ρ a).asHom + x.val ≫ (ρ b).asHom
      rw [map_add,End.add_asHom]
      simp only [Preadditive.comp_add]
  zero_smul x := by
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      change QuotientAddGroup.mk (T.mapCycles (ρ 0).asHom (n+1) x) = QuotientAddGroup.mk (0 : T.cycles Y (n+1))
      apply congrArg QuotientAddGroup.mk
      apply Subtype.ext
      change x.val ≫ (ρ 0).asHom = 0
      rw [map_zero,End.zero_asHom,comp_zero]

/-- Every original scalar acts on every original quotient representative through the original target endomorphism. -/
theorem cohomologyModule_mk (n : ℕ) (a : R) (x : T.cycles Y (n+1)) :
    letI := T.cohomologyModule ρ n
    a • (QuotientAddGroup.mk x : T.cohomology Y n) =
      QuotientAddGroup.mk (T.mapCycles (ρ a).asHom (n+1) x) := rfl

variable [HasExt.{w} C]

/-- The specified actual Ext comparison is linear for any already defined target action by the same original endomorphisms. -/
noncomputable def cohomologyLinearEquiv (n : ℕ) (h : T.AcyclicAgainst Y)
    [Module R (Ext.{w} (T.K 0) Y (n+1))]
    (hscalar : ∀ (a : R) (x : Ext.{w} (T.K 0) Y (n+1)),
      a • x = x.comp (Ext.mk₀ (ρ a).asHom) (add_zero (n+1))) :
    letI := T.cohomologyModule ρ n
    T.cohomology Y n ≃ₗ[R] Ext.{w} (T.K 0) Y (n+1) := by
  letI := T.cohomologyModule ρ n
  refine { T.cohomologyEquiv Y n h with map_smul' := ?_ }
  intro a x
  change T.cohomologyEquiv Y n h (T.mapCohomology (ρ a).asHom n x) = a • T.cohomologyEquiv Y n h x
  rw [T.cohomologyEquiv_postcomp]
  exact (hscalar a _).symm

/-- The linear comparison retains the original iterated connecting representative, not only an abstract linear isomorphism. -/
theorem cohomologyLinearEquiv_mk (n : ℕ) (h : T.AcyclicAgainst Y)
    [Module R (Ext.{w} (T.K 0) Y (n+1))]
    (hscalar : ∀ (a : R) (x : Ext.{w} (T.K 0) Y (n+1)),
      a • x = x.comp (Ext.mk₀ (ρ a).asHom) (add_zero (n+1))) (x : T.cycles Y (n+1)) :
    T.cohomologyLinearEquiv ρ n h hscalar (QuotientAddGroup.mk x) =
      T.cocycleComparison Y (n+1) x := rfl

end BPFixedPoints.ExtResolutionTools.ExactTower
