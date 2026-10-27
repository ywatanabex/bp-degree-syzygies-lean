import BPFixedPoints.Incidence.ShiftedFreeGrading
import BPFixedPoints.Incidence.GradedSpecialization

/-! # Homogeneous parts of a free module after taking coefficient images -/

namespace BPFixedPoints.ResolutionTools

open Finsupp MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k σ R J : Type*} [Field k] [CommRing R] [Algebra k R]
  (f : MvPolynomial σ k →ₐ[k] R)

noncomputable def freeCoefficientMap : (J →₀ MvPolynomial σ k) →ₗ[k] (J →₀ R) :=
  Finsupp.mapRange.linearMap f.toLinearMap

@[simp] theorem freeCoefficientMap_apply (x : J →₀ MvPolynomial σ k) (j : J) :
    freeCoefficientMap f x j = f (x j) := rfl

@[simp] theorem freeCoefficientMap_single (j : J) (s : MvPolynomial σ k) :
    freeCoefficientMap f (single j s) = single j (f s) := by
  classical
  ext i
  by_cases h : i = j
  · subst i; simp
  · simp [single_eq_of_ne h, h]

theorem gradedIntPiece_image (q : ℤ) :
    gradedIntPiece (gradedImagePiece (homogeneousSubmodule σ k) f) q =
      (homogeneousCoeffPiece q).map f.toLinearMap := by
  by_cases hq : 0 ≤ q
  · simp [gradedIntPiece, homogeneousCoeffPiece, hq, gradedImagePiece]
  · simp [gradedIntPiece, homogeneousCoeffPiece, hq]

/-- The shifted pieces of the image coefficient grading are the actual images of the old pieces. -/
theorem shiftedFreePiece_image (w : J → ℕ) (q : ℤ) :
    shiftedFreePiece (gradedImagePiece (homogeneousSubmodule σ k) f) w q =
      (weightedFreePiece w q).map (freeCoefficientMap f) := by
  classical
  ext x
  constructor
  · intro hx
    have hi (j : J) : x j ∈ (homogeneousCoeffPiece (q - (w j : ℤ))).map f.toLinearMap := by
      rw [← gradedIntPiece_image]
      exact hx j
    choose z hz he using fun j => Submodule.mem_map.mp (hi j)
    have he' (j : J) : f (z j) = x j := he j
    refine ⟨x.sum (fun j _ => single j (z j)), ?_, ?_⟩
    · apply Submodule.sum_mem
      intro j _
      exact weightedFreePiece_single w q j (hz j)
    · rw [map_finsuppSum]
      simp only [freeCoefficientMap_single, he']
      simpa only [Finsupp.sum] using x.sum_single
  · rintro ⟨y, hy, rfl⟩ j
    rw [gradedIntPiece_image]
    exact ⟨y j, hy j, rfl⟩

end BPFixedPoints.ResolutionTools
