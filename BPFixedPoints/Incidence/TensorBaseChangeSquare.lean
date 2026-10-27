import BPFixedPoints.Incidence.ProjectiveTargetBaseChange
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Comparing coefficient-ring base change with parameter-ring base change -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {T S B : Type*} [CommRing T] [CommRing S] [CommRing B]
  [Algebra T S] [Algebra T B]
  (M : Type*) [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower T S M]

/-- The canonical comparison for the square T -> S, T -> B. -/
noncomputable def tensorBaseChangeSquare :
    ((S ⊗[T] B) ⊗[S] M) ≃ₗ[T] B ⊗[T] M :=
  (TensorProduct.comm S (S ⊗[T] B) M).restrictScalars T ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T S S M B).restrictScalars T ≪≫ₗ
    TensorProduct.comm T M B

@[simp] theorem tensorBaseChangeSquare_tmul (s : S) (b : B) (m : M) :
    tensorBaseChangeSquare (T := T) M ((s ⊗ₜ[T] b) ⊗ₜ[S] m) = b ⊗ₜ[T] (s • m) := rfl

variable {M} {N : Type*} [AddCommGroup N] [Module S N] [Module T N] [IsScalarTower T S N]

theorem tensorBaseChangeSquare_naturality (f : M →ₗ[S] N)
    (x : (S ⊗[T] B) ⊗[S] M) :
    tensorBaseChangeSquare (T := T) N (f.baseChange (S ⊗[T] B) x) =
      (f.restrictScalars T).baseChange B (tensorBaseChangeSquare (T := T) M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul z m =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul s b => simp [LinearMap.baseChange_tmul]

variable {L : Type*} [AddCommGroup L] [Module S L] [Module T L] [IsScalarTower T S L]

/-- Exactness computed over the parameter ring is exactness over the changed coefficient ring. -/
theorem baseChange_exact_of_parameter_exact (f : L →ₗ[S] M) (g : M →ₗ[S] N)
    (h : Function.Exact ((f.restrictScalars T).baseChange B)
      ((g.restrictScalars T).baseChange B)) :
    Function.Exact (f.baseChange (S ⊗[T] B)) (g.baseChange (S ⊗[T] B)) := by
  intro x
  constructor
  · intro hx
    have hz : (g.restrictScalars T).baseChange B (tensorBaseChangeSquare (T := T) M x) = 0 := by
      rw [← tensorBaseChangeSquare_naturality, hx, map_zero]
    obtain ⟨y, hy⟩ := (h _).mp hz
    refine ⟨(tensorBaseChangeSquare (T := T) L).symm y, ?_⟩
    apply (tensorBaseChangeSquare (T := T) M).injective
    rw [tensorBaseChangeSquare_naturality, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    apply (tensorBaseChangeSquare (T := T) N).injective
    rw [map_zero, tensorBaseChangeSquare_naturality, tensorBaseChangeSquare_naturality]
    exact (h _).mpr ⟨_, rfl⟩

end BPFixedPoints.ResolutionTools
