import BPFixedPoints.Incidence.GradedFreeTensor

/-! # From bilinear chain maps on free resolutions to tensor-complex chain maps -/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.ResolutionTools

open Finsupp CategoryTheory
open scoped TensorProduct

universe u
variable {R A : Type u} [CommRing R] (degree : A → ℕ) (D : Module.End R (A →₀ R))

structure GradedFreePairing where
  mul : (A →₀ R) →ₗ[R] (A →₀ R) →ₗ[R] (A →₀ R)
  homogeneous : ∀ (p q : ℕ) {x y : A →₀ R}, x ∈ gradedPiece R degree p →
    y ∈ gradedPiece R degree q → mul x y ∈ gradedPiece R degree (p + q)
  leibniz : ∀ x y, D (mul x y) = mul (D x) y + mul (gradedParity degree x) (D y)

namespace GradedFreePairing

variable {degree D} (μ : GradedFreePairing degree D)

noncomputable def linearize : (A × A →₀ R) →ₗ[R] (A →₀ R) :=
  (TensorProduct.lift μ.mul).comp (finsuppTensorFinsupp' R A A).symm.toLinearMap

theorem linearize_tmul (x y : A →₀ R) :
    μ.linearize (finsuppTensorFinsupp' R A A (x ⊗ₜ[R] y)) = μ.mul x y := by
  simp [linearize]

theorem linearize_single (a b : A) (r : R) :
    μ.linearize (single (a, b) r) = μ.mul (single a 1) (single b r) := by
  simp [linearize, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

theorem linearize_degree (n : ℕ) {x : A × A →₀ R}
    (hx : x ∈ gradedPiece R (fun a : A × A => degree a.1 + degree a.2) n) :
    μ.linearize x ∈ gradedPiece R degree n := by
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  rintro ⟨a, b⟩ hab
  dsimp only
  rw [linearize_single]
  have h := μ.homogeneous (degree a) (degree b)
    (x := single a 1) (y := single b (x (a, b)))
    (single_mem_supported R _ rfl) (single_mem_supported R _ rfl)
  have hd : degree a + degree b = n := (mem_supported R x).mp hx hab
  simpa only [hd] using h

theorem linearize_chain (x : A × A →₀ R) :
    D (μ.linearize x) = μ.linearize (gradedTensorD degree D x) := by
  obtain ⟨t, rfl⟩ := (finsuppTensorFinsupp' R A A).surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul x y =>
    rw [linearize_tmul, gradedTensorD_tmul, map_add, map_add,
      linearize_tmul, linearize_tmul, μ.leibniz]

noncomputable def component (n : ℕ) :
    gradedPiece R (fun a : A × A => degree a.1 + degree a.2) n →ₗ[R] gradedPiece R degree n :=
  (μ.linearize.comp (gradedPiece R (fun a : A × A => degree a.1 + degree a.2) n).subtype).codRestrict _
    (fun x => μ.linearize_degree n x.property)

end GradedFreePairing

variable (hdegree : HasDegree (fun a => (degree a : ℤ)) (fun a => (degree a : ℤ)) (-1) D)
  (hD : D * D = 0)

noncomputable def gradedTensorComplex : ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => gradedPiece R (fun a : A × A => degree a.1 + degree a.2) n)
    (gradedDifferential (fun a : A × A => degree a.1 + degree a.2) (gradedTensorD degree D)
      (gradedTensorD_graded degree D hdegree))
    (gradedDifferential_square _ _ _ (gradedTensorD_sq degree D hdegree hD))

noncomputable instance gradedTensorComplex_projective (n : ℕ) :
    Projective ((gradedTensorComplex degree D hdegree hD).X n) := by
  change Projective (ModuleCat.of R (gradedPiece R (fun a : A × A => degree a.1 + degree a.2) n))
  exact ModuleCat.projective_of_categoryTheory_projective _

theorem gradedTensorComplex_d (n : ℕ) :
    (gradedTensorComplex degree D hdegree hD).d (n + 1) n =
      ModuleCat.ofHom (gradedDifferential (fun a : A × A => degree a.1 + degree a.2)
        (gradedTensorD degree D) (gradedTensorD_graded degree D hdegree) n) :=
  linearChainComplex_d _ _ _ n

theorem gradedTensorComplex_minimal (I : Ideal R)
    (hmin : ∀ x, D x ∈ I • (⊤ : Submodule R (A →₀ R))) (i j : ℕ) :
    LinearMap.range ((gradedTensorComplex degree D hdegree hD).d i j).hom ≤
      I • (⊤ : Submodule R ((gradedTensorComplex degree D hdegree hD).X j)) := by
  by_cases h : j + 1 = i
  · subst i
    rw [gradedTensorComplex_d]
    exact gradedDifferential_minimal I _ _ (gradedTensorD_graded degree D hdegree) (fun x => gradedTensorD_minimal degree D I hmin x) j
  · rw [(gradedTensorComplex degree D hdegree hD).shape i j h]
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact bot_le

end BPFixedPoints.ResolutionTools
