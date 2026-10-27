import BPFixedPoints.Incidence.ResolutionHomogeneous

/-!
# Coefficient control for maps between free modules

`MatrixOver A f` says that the actual matrix entries of `f` lie in the
subring `A`. It is stable under the operations used to build the concrete
Čech contraction. In particular, choosing the constant coefficient
subring does not assume that an arbitrary polynomial-linear map preserves
coefficient degree.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp
open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- Coefficientwise membership in a subring. -/
def AllCoeffsIn {I : Type*} (A : Subring R) (x : I →₀ R) : Prop :=
  ∀ i, x i ∈ A

namespace AllCoeffsIn

variable {A : Subring R} {I J : Type*}

@[simp] theorem zero : AllCoeffsIn A (0 : I →₀ R) := fun _ => A.zero_mem

theorem single (i : I) {r : R} (hr : r ∈ A) :
    AllCoeffsIn A (Finsupp.single i r) := by
  classical
  intro j
  by_cases h : j = i
  · subst j; simpa using hr
  · simpa [Finsupp.single_eq_of_ne h] using A.zero_mem

theorem add {x y : I →₀ R} (hx : AllCoeffsIn A x) (hy : AllCoeffsIn A y) :
    AllCoeffsIn A (x + y) := fun i => A.add_mem (hx i) (hy i)

theorem neg {x : I →₀ R} (hx : AllCoeffsIn A x) :
    AllCoeffsIn A (-x) := fun i => A.neg_mem (hx i)

theorem smul {x : I →₀ R} {r : R} (hr : r ∈ A) (hx : AllCoeffsIn A x) :
    AllCoeffsIn A (r • x) := fun i => A.mul_mem hr (hx i)

theorem sum {T : Type*} (s : Finset T) (f : T → I →₀ R)
    (hf : ∀ t ∈ s, AllCoeffsIn A (f t)) : AllCoeffsIn A (∑ t ∈ s, f t) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro hf
    simpa using (AllCoeffsIn.zero (A := A) (I := I))
  | @insert t s ht ih =>
    intro hf
    rw [Finset.sum_insert ht]
    exact (hf t (Finset.mem_insert_self t s)).add
      (ih (fun u hu => hf u (Finset.mem_insert_of_mem hu)))

end AllCoeffsIn

/-- All entries of the actual free-module matrix lie in `A`. -/
def MatrixOver {I J : Type*} (A : Subring R)
    (f : (I →₀ R) →ₗ[R] (J →₀ R)) : Prop :=
  ∀ i, AllCoeffsIn A (f (single i 1))

namespace MatrixOver

variable {A : Subring R} {I J K : Type*}
  {f f' : (I →₀ R) →ₗ[R] (J →₀ R)} {g : (J →₀ R) →ₗ[R] (K →₀ R)}

theorem apply (hf : MatrixOver A f) {x : I →₀ R} (hx : AllCoeffsIn A x) :
    AllCoeffsIn A (f x) := by
  rw [← x.sum_single, map_finsuppSum]
  apply AllCoeffsIn.sum
  intro i hi
  change AllCoeffsIn A (f (single i (x i)))
  have he : single i (x i) = x i • single i (1 : R) := by simp
  rw [he, map_smul]
  exact AllCoeffsIn.smul (hx i) (hf i)

theorem zero : MatrixOver A (0 : (I →₀ R) →ₗ[R] (J →₀ R)) :=
  fun _ => AllCoeffsIn.zero

theorem id : MatrixOver A (LinearMap.id : (I →₀ R) →ₗ[R] (I →₀ R)) :=
  fun i => AllCoeffsIn.single i A.one_mem

theorem add (hf : MatrixOver A f) (hf' : MatrixOver A f') : MatrixOver A (f + f') :=
  fun i => (hf i).add (hf' i)

theorem neg (hf : MatrixOver A f) : MatrixOver A (-f) := fun i => (hf i).neg

theorem comp (hg : MatrixOver A g) (hf : MatrixOver A f) : MatrixOver A (g.comp f) :=
  fun i => hg.apply (hf i)

theorem mapDomain (u : I → J) : MatrixOver A (Finsupp.lmapDomain R R u) := by
  intro i
  change AllCoeffsIn A (Finsupp.mapDomain u (single i 1))
  rw [mapDomain_single]
  exact AllCoeffsIn.single _ A.one_mem

theorem congr_mapDomain {I' J' : Type*} (u : I ≃ I') (v : J ≃ J')
    (hf : MatrixOver A f) :
    MatrixOver A ((Finsupp.mapDomain.linearEquiv R R v).toLinearMap.comp
      (f.comp (Finsupp.mapDomain.linearEquiv R R u).symm.toLinearMap)) := by
  have hi : MatrixOver A (Finsupp.lmapDomain R R u.symm) := mapDomain u.symm
  have ho : MatrixOver A (Finsupp.lmapDomain R R v) := mapDomain v
  simpa only [Finsupp.mapDomain.linearEquiv_symm,
    Finsupp.mapDomain.toLinearMap_linearEquiv] using ho.comp (hf.comp hi)

theorem freeTensorMap {I' J' : Type*}
    {g : (I' →₀ R) →ₗ[R] (J' →₀ R)}
    (hf : MatrixOver A f) (hg : MatrixOver A g) :
    MatrixOver A (ResolutionTools.freeTensorMap f g) := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩
  rw [ResolutionTools.freeTensorMap_single_apply]
  exact A.mul_mem (hf i j) (hg i' j')

theorem tensor_congr {I' J' K' L' : Type*}
    {g : (I' →₀ R) →ₗ[R] (J' →₀ R)}
    (hf : MatrixOver A f) (hg : MatrixOver A g)
    (u : I × I' ≃ K') (v : J × J' ≃ L') :
    MatrixOver A
      (((finsuppTensorFinsupp' R J J').trans
        (Finsupp.mapDomain.linearEquiv R R v)).toLinearMap.comp
        ((TensorProduct.map f g).comp
          ((finsuppTensorFinsupp' R I I').trans
            (Finsupp.mapDomain.linearEquiv R R u)).symm.toLinearMap)) := by
  have ht := (hf.freeTensorMap hg).congr_mapDomain u v
  convert ht using 1
  ext x
  rfl

end MatrixOver

end BPFixedPoints.ResolutionTools
