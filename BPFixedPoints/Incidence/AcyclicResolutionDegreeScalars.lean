import BPFixedPoints.Incidence.AcyclicResolutionCohomologyDegree
import BPFixedPoints.Incidence.AcyclicResolutionScalars

/-! # Original target actions in every actual resolution cohomology degree

The action is original postcomposition on cycles and their original
positive-degree quotients. The Ext target action is supplied independently;
linearity is proved from the original Yoneda naturality.
-/

namespace BPFixedPoints.ExtResolutionTools.ExactTower
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
universe w v u r
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (T : ExactTower C) {R : Type r} [Ring R] {Y : C} (ρ : R →+* End Y)

/-- The original target endomorphisms act before comparison in every actual degree, including zero. -/
@[instance_reducible] noncomputable def cohomologyAtModule (n : ℕ) : Module R (T.cohomologyAt Y n) where
  smul a x := T.mapAt (ρ a).asHom n x
  one_smul x := by
    obtain ⟨x,rfl⟩ := T.classAt_surjective Y n x
    change T.mapAt (ρ 1).asHom n (T.classAt Y n x) = T.classAt Y n x
    rw [mapAt_class]
    apply congrArg (T.classAt Y n)
    apply Subtype.ext
    change x.val ≫ (ρ 1).asHom = x.val
    rw [map_one,End.one_asHom,Category.comp_id]
  mul_smul a b x := by
    obtain ⟨x,rfl⟩ := T.classAt_surjective Y n x
    change T.mapAt (ρ (a*b)).asHom n (T.classAt Y n x) =
      T.mapAt (ρ a).asHom n (T.mapAt (ρ b).asHom n (T.classAt Y n x))
    simp only [mapAt_class]
    apply congrArg (T.classAt Y n)
    apply Subtype.ext
    change x.val ≫ (ρ (a*b)).asHom = (x.val ≫ (ρ b).asHom) ≫ (ρ a).asHom
    rw [map_mul,End.mul_asHom]
    exact (Category.assoc _ _ _).symm
  smul_add a x y := (T.mapAt (ρ a).asHom n).map_add x y
  smul_zero a := (T.mapAt (ρ a).asHom n).map_zero
  add_smul a b x := by
    obtain ⟨x,rfl⟩ := T.classAt_surjective Y n x
    change T.mapAt (ρ (a+b)).asHom n (T.classAt Y n x) =
      T.mapAt (ρ a).asHom n (T.classAt Y n x) + T.mapAt (ρ b).asHom n (T.classAt Y n x)
    simp only [mapAt_class]
    rw [← map_add]
    apply congrArg (T.classAt Y n)
    apply Subtype.ext
    change x.val ≫ (ρ (a+b)).asHom = x.val ≫ (ρ a).asHom + x.val ≫ (ρ b).asHom
    rw [map_add,End.add_asHom,Preadditive.comp_add]
  zero_smul x := by
    obtain ⟨x,rfl⟩ := T.classAt_surjective Y n x
    change T.mapAt (ρ 0).asHom n (T.classAt Y n x) = 0
    rw [mapAt_class,← (T.classAt Y n).map_zero]
    apply congrArg (T.classAt Y n)
    apply Subtype.ext
    change x.val ≫ (ρ 0).asHom = 0
    rw [map_zero,End.zero_asHom,comp_zero]

/-- The action on every original class is exactly the original scalar postcomposition. -/
theorem cohomologyAtModule_class (n : ℕ) (a : R) (x : T.cycles Y n) :
    letI := T.cohomologyAtModule ρ n
    a • T.classAt Y n x = T.classAt Y n (T.mapCycles (ρ a).asHom n x) :=
  T.mapAt_class (ρ a).asHom n x

/-- Positive degrees keep the existing original cohomology action itself. -/
theorem cohomologyAtModule_succ (n : ℕ) :
    T.cohomologyAtModule ρ (n+1) = T.cohomologyModule ρ n := rfl

variable [HasExt.{w} C]

/-- The original Yoneda comparison is linear for independently specified target actions in every degree. -/
noncomputable def cohomologyAtExtLinearEquiv (n : ℕ) (h : T.AcyclicAgainst Y)
    [Module R (Ext.{w} (T.K 0) Y n)]
    (hscalar : ∀ (a : R) (x : Ext.{w} (T.K 0) Y n),
      a • x = x.comp (Ext.mk₀ (ρ a).asHom) (add_zero n)) :
    letI := T.cohomologyAtModule ρ n
    T.cohomologyAt Y n ≃ₗ[R] Ext.{w} (T.K 0) Y n := by
  letI := T.cohomologyAtModule ρ n
  refine { T.cohomologyAtExtEquiv Y h n with map_smul' := ?_ }
  intro a x
  change T.cohomologyAtExtEquiv Y h n (T.mapAt (ρ a).asHom n x) = a • T.cohomologyAtExtEquiv Y h n x
  rw [cohomologyAtExtEquiv_postcomp]
  exact (hscalar a _).symm

end BPFixedPoints.ExtResolutionTools.ExactTower
