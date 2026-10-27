import BPFixedPoints.Incidence.GradedSurjectiveImage
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The actual quotient grading on the tensor presentation of a coefficient cut -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k T S : Type*} [Field k] [CommRing T] [CommRing S]
  [Algebra k S] [Algebra T S] (I : Ideal T)

/-- Explicit tower witness, avoiding ambiguous scalar-tower searches for concrete polynomial cuts. -/
theorem tensorQuotientScalarTower : IsScalarTower k S (S ⊗[T] (T ⧸ I)) := inferInstance

noncomputable def tensorQuotientCoefficientHom : S →ₐ[k] S ⊗[T] (T ⧸ I) :=
  IsScalarTower.toAlgHom k S (S ⊗[T] (T ⧸ I))

@[simp] theorem tensorQuotientCoefficientHom_apply (s : S) :
    tensorQuotientCoefficientHom (k := k) (S := S) I s = s ⊗ₜ[T] (1 : T ⧸ I) := rfl

theorem tensorQuotientCoefficientHom_surjective :
    Function.Surjective (tensorQuotientCoefficientHom (k := k) (S := S) I) := by
  intro x
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
  obtain ⟨y, rfl⟩ := e.surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨s, rfl⟩

theorem tensorQuotientCoefficientHom_ker :
    RingHom.ker (tensorQuotientCoefficientHom (k := k) (S := S) I).toRingHom =
      I.map (algebraMap T S) := by
  ext s
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I
  change e (Ideal.Quotient.mk (I.map (algebraMap T S)) s) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]

variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

/-- The coefficient cut carries the images of the original homogeneous components. -/
@[instance_reducible] noncomputable def tensorQuotientGradedAlgebra
    (hI : (I.map (algebraMap T S)).IsHomogeneous 𝒜) :
    GradedAlgebra (gradedImagePiece 𝒜 (tensorQuotientCoefficientHom (k := k) (S := S) I)) := by
  apply gradedImageAlgebra 𝒜 _ (tensorQuotientCoefficientHom_surjective I)
  rw [tensorQuotientCoefficientHom_ker]
  exact hI

/-- The image grading agrees with the actual homogeneous quotient grading through the canonical map. -/
theorem tensorQuotientPiece_eq (q : ℕ) :
    gradedImagePiece 𝒜 (tensorQuotientCoefficientHom (k := k) (S := S) I) q =
      (gradedQuotientPiece 𝒜 (I.map (algebraMap T S)) q).map
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toLinearEquiv.restrictScalars k).toLinearMap := by
  rw [gradedImagePiece, gradedQuotientPiece, ← Submodule.map_comp]
  rfl

end BPFixedPoints.ResolutionTools
