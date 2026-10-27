import BPFixedPoints.Incidence.CoefficientGrading
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Internal degrees from origin specialization

Map homogeneous pieces of weighted free modules by actual evaluation at the
coefficient origin. Prove their images are the subspaces of generators of
the specified weight, constructing constant-coefficient lifts rather than
defining the images by their desired dimensions.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp

variable {I σ k : Type*} [CommRing k]

/-- Evaluation at the coefficient origin. -/
noncomputable def freeAtOrigin : (I →₀ MvPolynomial σ k) →ₗ[k] (I →₀ k) :=
  Finsupp.mapRange.linearMap (MvPolynomial.aeval (fun _ : σ => (0 : k))).toLinearMap

@[simp] theorem freeAtOrigin_apply (x : I →₀ MvPolynomial σ k) (i : I) :
    freeAtOrigin x i = MvPolynomial.constantCoeff (x i) := by
  simp [freeAtOrigin, MvPolynomial.constantCoeff]

/-- Lift to the free module using constant coefficients. -/
noncomputable def freeConstantLift : (I →₀ k) →ₗ[k] (I →₀ MvPolynomial σ k) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap k (MvPolynomial σ k))

@[simp] theorem freeConstantLift_apply (x : I →₀ k) (i : I) :
    freeConstantLift (σ := σ) x i = MvPolynomial.C (x i) := rfl

@[simp] theorem freeAtOrigin_constantLift (x : I →₀ k) :
    freeAtOrigin (freeConstantLift (σ := σ) x) = x := by
  ext i
  simp

theorem constantCoeff_eq_zero_of_homogeneous {n : ℤ} {f : MvPolynomial σ k}
    (hf : f ∈ homogeneousCoeffPiece n) (hn : n ≠ 0) :
    MvPolynomial.constantCoeff f = 0 := by
  by_cases hpos : 0 ≤ n
  · have hh : f.IsHomogeneous n.toNat := by
      simpa [homogeneousCoeffPiece, hpos] using hf
    exact hh.coeff_eq_zero (by simp; omega)
  · have hf0 : f = 0 := by simpa [homogeneousCoeffPiece, hpos] using hf
    simp [hf0]

/-- Specialization kills components whose generator weight differs from the specified internal degree. -/
theorem freeAtOrigin_mem_supported (w : I → ℕ) (q : ℕ)
    {x : I →₀ MvPolynomial σ k} (hx : x ∈ weightedFreePiece w q) :
    freeAtOrigin x ∈ Finsupp.supported k k {i | w i = q} := by
  rw [Finsupp.mem_supported']
  intro i hi
  rw [freeAtOrigin_apply]
  exact constantCoeff_eq_zero_of_homogeneous (hx i) (by
    change w i ≠ q at hi
    omega)

/-- An element supported on generators of the specified weight lifts with constant coefficients in that internal degree. -/
theorem freeConstantLift_mem_weightedFreePiece (w : I → ℕ) (q : ℕ)
    {x : I →₀ k} (hx : x ∈ Finsupp.supported k k {i | w i = q}) :
    freeConstantLift (σ := σ) x ∈ weightedFreePiece w q := by
  intro i
  rw [freeConstantLift_apply]
  by_cases hi : w i = q
  · rw [hi, sub_self]
    exact homogeneousCoeffPiece_C _
  · rw [(Finsupp.mem_supported' k x).mp hx i hi, map_zero]
    exact (homogeneousCoeffPiece _).zero_mem

/-- Identify the image of each homogeneous piece under origin evaluation by both inclusions. -/
theorem weightedFreePiece_map_atOrigin (w : I → ℕ) (q : ℕ) :
    (weightedFreePiece (σ := σ) (k := k) w q).map freeAtOrigin =
      Finsupp.supported k k {i | w i = q} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact freeAtOrigin_mem_supported w q hy
  · intro hx
    exact ⟨freeConstantLift x, freeConstantLift_mem_weightedFreePiece w q hx,
      freeAtOrigin_constantLift x⟩

end BPFixedPoints.ResolutionTools
