import BPFixedPoints.Incidence.TensorBaseChangeSquare

/-! # Preserving the original coefficient resolution under parameter base change -/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u
variable {T S B : Type u} [CommRing T] [CommRing S] [CommRing B]
  [Algebra T S] [Algebra T B]
  (P : ℕ → Type u) [∀ n, AddCommGroup (P n)]
  [∀ n, Module S (P n)] [∀ n, Module T (P n)] [∀ n, IsScalarTower T S (P n)]
  [∀ n, Module.Free S (P n)] [∀ n, Module.Free T (P n)]
  (d : ∀ n, P (n + 1) →ₗ[S] P n)
  (hd : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n))
  {M : Type u} [AddCommGroup M] [Module S M] [Module T M] [IsScalarTower T S M]
  [Module.Projective T M]
  (ε : P 0 →ₗ[S] M) (hεs : Function.Surjective ε)
  (hεe : LinearMap.range (d 0) = LinearMap.ker ε)

include hd hεs hεe in
/-- The actual coefficient differentials remain exact after any parameter base change. -/
theorem coefficientBaseChange_exact (n : ℕ) :
    LinearMap.range ((d (n + 1)).baseChange (S ⊗[T] B)) =
      LinearMap.ker ((d n).baseChange (S ⊗[T] B)) := by
  have hdT : ∀ n, LinearMap.range ((d (n + 1)).restrictScalars T) =
      LinearMap.ker ((d n).restrictScalars T) := by
    intro n
    ext x
    exact SetLike.ext_iff.mp (hd n) x
  have hεT : LinearMap.range ((d 0).restrictScalars T) =
      LinearMap.ker (ε.restrictScalars T) := by
    ext x
    exact SetLike.ext_iff.mp hεe x
  have ht := baseChangeSplitResolution_exact (algebraMap T B) P
    (fun n => (d n).restrictScalars T) hdT (ε.restrictScalars T) hεs hεT n
  rw [toAlgebra_algebraMap] at ht
  have hp : Function.Exact ((d (n + 1)).restrictScalars T |>.baseChange B)
      ((d n).restrictScalars T |>.baseChange B) := by
    intro x
    exact (SetLike.ext_iff.mp ht x).symm
  have h := baseChange_exact_of_parameter_exact (d (n + 1)) (d n) hp
  ext x
  exact (h x).symm

include hεs hεe in
theorem coefficientBaseChange_augmentation_exact :
    LinearMap.range ((d 0).baseChange (S ⊗[T] B)) =
      LinearMap.ker (ε.baseChange (S ⊗[T] B)) := by
  have he : Function.Exact (d 0) ε := by
    intro x
    exact (SetLike.ext_iff.mp hεe x).symm
  have h := lTensor_exact (S ⊗[T] B) he hεs
  ext x
  exact (h x).symm

/-- This resolution has precisely the scalar-extended terms, differentials and augmentation. -/
noncomputable def coefficientBaseChangeResolution :
    ProjectiveResolution (ModuleCat.of (S ⊗[T] B) ((S ⊗[T] B) ⊗[S] M)) :=
  projectiveResolutionOfLinearExact (fun n => (S ⊗[T] B) ⊗[S] P n)
    (fun n => (d n).baseChange (S ⊗[T] B))
    (coefficientBaseChange_exact P d hd ε hεs hεe)
    (ε.baseChange (S ⊗[T] B)) (LinearMap.baseChange_surjective _ hεs)
    (coefficientBaseChange_augmentation_exact P d ε hεs hεe)

@[simp] theorem coefficientBaseChangeResolution_X (n : ℕ) :
    (coefficientBaseChangeResolution (B := B) P d hd ε hεs hεe).complex.X n =
      ModuleCat.of (S ⊗[T] B) ((S ⊗[T] B) ⊗[S] P n) := rfl

@[simp] theorem coefficientBaseChangeResolution_d (n : ℕ) :
    (coefficientBaseChangeResolution (B := B) P d hd ε hεs hεe).complex.d (n + 1) n =
      ModuleCat.ofHom ((d n).baseChange (S ⊗[T] B)) := by
  exact linearChainComplex_d _ _
    (fun i => LinearMap.range_le_ker_iff.mp
      (coefficientBaseChange_exact (B := B) P d hd ε hεs hεe i).le) n

end BPFixedPoints.ResolutionTools
