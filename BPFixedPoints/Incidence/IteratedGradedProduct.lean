import BPFixedPoints.Incidence.GradedTensorSpecialization

/-! # Multiplication on the actual twice-extended graded free terms -/

namespace BPFixedPoints.ResolutionTools

open Finsupp
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

universe u
variable {S R k A : Type u} [CommRing S] [CommRing R] [CommRing k]
  [Algebra S R] [Algebra R k]
  {degree : A → ℕ} {D : Module.End S (A →₀ S)}
  (μ : GradedFreePairing degree D)

/-- Extend the original bilinear multiplication twice, then restrict to its graded terms. -/
noncomputable def iteratedGradedProduct (p q : ℕ) :
    (k ⊗[R] (R ⊗[S] gradedPiece S degree p)) →ₗ[k]
      (k ⊗[R] (R ⊗[S] gradedPiece S degree q)) →ₗ[k]
        (k ⊗[R] (R ⊗[S] gradedPiece S degree (p + q))) :=
  ((LinearMap.BilinMap.baseChange k (LinearMap.BilinMap.baseChange R μ.mul)).compl₁₂
    (((gradedPiece S degree p).subtype.baseChange R).baseChange k)
    (((gradedPiece S degree q).subtype.baseChange R).baseChange k)).compr₂
      (((Finsupp.restrictDom S S {a : A | degree a = p + q}).baseChange R).baseChange k)

/-- The multiplication is the actual scalar extension of the original multiplication. -/
theorem iteratedGradedProduct_unit_tmul (p q : ℕ)
    (x : gradedPiece S degree p) (y : gradedPiece S degree q) :
    iteratedGradedProduct (R := R) (k := k) μ p q
      ((1 : k) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
      ((1 : k) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] y)) =
      (1 : k) ⊗ₜ[R] ((1 : R) ⊗ₜ[S]
        (⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩ :
          gradedPiece S degree (p + q))) := by
  change (1 * 1 : k) ⊗ₜ[R] ((1 * 1 : R) ⊗ₜ[S]
    Finsupp.restrictDom S S {a : A | degree a = p + q} (μ.mul x.val y.val)) = _
  simp only [one_mul]
  congr 1
  congr 1
  exact LinearMap.congr_fun (Finsupp.restrictDom_comp_subtype
    (M := S) (R := S) {a : A | degree a = p + q})
      ⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩

end BPFixedPoints.ResolutionTools
