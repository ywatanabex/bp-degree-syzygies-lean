import BPFixedPoints.Incidence.GradedFreePairing
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Canonical product map from specialized graded pieces to the tensor complex -/

namespace BPFixedPoints.ResolutionTools

open Finsupp
open scoped TensorProduct

universe u
variable {R k A : Type u} [CommRing R] [CommRing k] [Algebra R k]
  (degree : A → ℕ)

noncomputable def freePair : LinearMap.BilinMap R (A →₀ R) (A × A →₀ R) :=
  (TensorProduct.mk R (A →₀ R) (A →₀ R)).compr₂ (finsuppTensorFinsupp' R A A).toLinearMap

theorem freePair_apply (x y : A →₀ R) :
    freePair x y = finsuppTensorFinsupp' R A A (x ⊗ₜ[R] y) := rfl

theorem freePair_degree (p q : ℕ) {x y : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (hy : y ∈ gradedPiece R degree q) :
    freePair x y ∈ gradedPiece R (fun a : A × A => degree a.1 + degree a.2) (p + q) := by
  apply (mem_supported' R _).mpr
  rintro ⟨a, b⟩ hab
  rw [freePair_apply, finsuppTensorFinsupp'_apply_apply]
  by_cases ha : degree a = p
  · have hb : degree b ≠ q := fun hb => hab (by simp [ha, hb])
    rw [(mem_supported' R y).mp hy b hb, mul_zero]
  · rw [(mem_supported' R x).mp hx a ha, zero_mul]

noncomputable def specializedGradedPair (p q : ℕ) :
    (k ⊗[R] gradedPiece R degree p) →ₗ[k]
      (k ⊗[R] gradedPiece R degree q) →ₗ[k]
        (k ⊗[R] gradedPiece R (fun a : A × A => degree a.1 + degree a.2) (p + q)) :=
  ((freePair (R := R) (A := A)).baseChange k |>.compl₁₂
    ((gradedPiece R degree p).subtype.baseChange k)
    ((gradedPiece R degree q).subtype.baseChange k)).compr₂
      ((Finsupp.restrictDom R R {a : A × A | degree a.1 + degree a.2 = p + q}).baseChange k)

theorem specializedGradedPair_tmul (p q : ℕ) (c d : k)
    (x : gradedPiece R degree p) (y : gradedPiece R degree q) :
    specializedGradedPair degree p q (c ⊗ₜ[R] x) (d ⊗ₜ[R] y) =
      (c * d) ⊗ₜ[R] (⟨freePair x.val y.val, freePair_degree degree p q x.property y.property⟩ :
        gradedPiece R (fun a : A × A => degree a.1 + degree a.2) (p + q)) := by
  change (c * d) ⊗ₜ[R]
    ((Finsupp.restrictDom R R {a : A × A | degree a.1 + degree a.2 = p + q})
      (freePair x.val y.val)) = _
  congr 1
  exact LinearMap.congr_fun (Finsupp.restrictDom_comp_subtype
    (M := R) (R := R) {a : A × A | degree a.1 + degree a.2 = p + q})
      ⟨freePair x.val y.val, freePair_degree degree p q x.property y.property⟩

end BPFixedPoints.ResolutionTools
