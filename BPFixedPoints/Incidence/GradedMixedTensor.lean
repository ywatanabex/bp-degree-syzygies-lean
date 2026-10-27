import BPFixedPoints.Incidence.GradedParityLaws

/-! # Signed tensor product of two different free complexes -/
namespace BPFixedPoints.ResolutionTools
open Finsupp CategoryTheory
open scoped TensorProduct
universe u
variable {R A B : Type u} [CommRing R]
  (da : A → ℕ) (db : B → ℕ)
  (D : Module.End R (A →₀ R)) (D' : Module.End R (B →₀ R))

noncomputable def mixedTensorD : Module.End R (A × B →₀ R) :=
  freeTensorMap D 1 + freeTensorMap (gradedParity da) D'

theorem mixedTensorD_tmul (x : A →₀ R) (y : B →₀ R) :
    mixedTensorD da D D' (finsuppTensorFinsupp' R A B (x ⊗ₜ[R] y)) =
      finsuppTensorFinsupp' R A B (D x ⊗ₜ[R] y + gradedParity da x ⊗ₜ[R] D' y) := by
  simp only [mixedTensorD, freeTensorMap, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    Module.End.one_apply, map_add]

theorem mixedTensorD_sq
    (hd : HasDegree (fun a => (da a : ℤ)) (fun a => (da a : ℤ)) (-1) D)
    (hD : D * D = 0) (hD' : D' * D' = 0) :
    mixedTensorD da D D' * mixedTensorD da D D' = 0 := by
  have hcancel (f : Module.End R (A →₀ R)) (g : Module.End R (B →₀ R)) :
      TensorProduct.map (-f) g + TensorProduct.map f g = 0 := by
    ext x y
    change (-f (single x 1)) ⊗ₜ[R] g (single y 1) +
      f (single x 1) ⊗ₜ[R] g (single y 1) = 0
    rw [← TensorProduct.add_tmul, neg_add_cancel, TensorProduct.zero_tmul]
  let e := finsuppTensorFinsupp' R A B
  have h : (TensorProduct.map D 1 + TensorProduct.map (gradedParity da) D') *
      (TensorProduct.map D 1 + TensorProduct.map (gradedParity da) D') = 0 := by
    simp only [add_mul, mul_add, ← TensorProduct.map_mul, hD, hD',
      one_mul, mul_one, gradedParity_d da D hd,
      TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero, zero_add]
    exact hcancel _ _
  apply LinearMap.ext
  intro x
  have hx := congrArg e (LinearMap.congr_fun h (e.symm x))
  simpa only [mixedTensorD, freeTensorMap, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add, LinearEquiv.symm_apply_apply,
    LinearMap.zero_apply, map_zero] using hx

theorem mixedTensorD_degree
    (hd : HasDegree (fun a => (da a : ℤ)) (fun a => (da a : ℤ)) (-1) D)
    (hd' : HasDegree (fun b => (db b : ℤ)) (fun b => (db b : ℤ)) (-1) D') :
    HasDegree (fun a : A × B => ((da a.1 + db a.2 : ℕ) : ℤ))
      (fun a : A × B => ((da a.1 + db a.2 : ℕ) : ℤ)) (-1) (mixedTensorD da D D') := by
  have h₁ := hd.freeTensorMap (HasDegree.id (R := R) (M := R) (fun b => (db b : ℤ)))
  have h₂ := (gradedParity_degree (R := R) da).freeTensorMap hd'
  simpa only [Nat.cast_add, add_zero, zero_add, mixedTensorD, Module.End.one_eq_id] using h₁.add h₂

theorem mixedTensorD_minimal (I : Ideal R)
    (hD : ∀ x, D x ∈ I • (⊤ : Submodule R (A →₀ R)))
    (hD' : ∀ y, D' y ∈ I • (⊤ : Submodule R (B →₀ R))) (x : A × B →₀ R) :
    mixedTensorD da D D' x ∈ I • (⊤ : Submodule R (A × B →₀ R)) := by
  induction x using Finsupp.induction_linear with
  | zero => simpa using (Submodule.zero_mem (I • (⊤ : Submodule R (A × B →₀ R))))
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single ab r =>
    have he : single ab r = finsuppTensorFinsupp' R A B
        (single ab.1 1 ⊗ₜ[R] single ab.2 r) := by simp
    rw [he, mixedTensorD_tmul]
    apply map_mem_ideal_smul_top I (finsuppTensorFinsupp' R A B).toLinearMap
    apply Submodule.add_mem
    · exact map_mem_ideal_smul_top I ((TensorProduct.mk R (A →₀ R) (B →₀ R)).flip
        (single ab.2 r)) (hD (single ab.1 1))
    · exact map_mem_ideal_smul_top I ((TensorProduct.mk R (A →₀ R) (B →₀ R))
        (gradedParity da (single ab.1 1))) (hD' (single ab.2 r))

variable {da db D D'}

theorem HasDegree.nat_differential
    (hd : HasDegree (fun a => (da a : ℤ)) (fun a => (da a : ℤ)) (-1) D)
    (n : ℕ) (x : A →₀ R) (hx : x ∈ gradedPiece R da (n + 1)) :
    D x ∈ gradedPiece R da n := by
  have hx' : x ∈ supported R R {a | (da a : ℤ) = ((n + 1 : ℕ) : ℤ)} := by
    simpa only [gradedPiece, Int.natCast_inj] using hx
  have h := hd ((n + 1 : ℕ) : ℤ) x hx'
  simpa only [gradedPiece, Nat.cast_add, Nat.cast_one, Int.add_neg_cancel_right,
    Int.natCast_inj] using h

variable (da D)
  (hd : HasDegree (fun a => (da a : ℤ)) (fun a => (da a : ℤ)) (-1) D)
  (hD : D * D = 0)

noncomputable def gradedFreeComplex : ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => gradedPiece R da n)
    (gradedDifferential da D hd.nat_differential)
    (gradedDifferential_square da D hd.nat_differential hD)

noncomputable instance gradedFreeComplex_projective (n : ℕ) :
    Projective ((gradedFreeComplex da D hd hD).X n) := by
  change Projective (ModuleCat.of R (gradedPiece R da n))
  exact ModuleCat.projective_of_categoryTheory_projective _

theorem gradedFreeComplex_d (n : ℕ) :
    (gradedFreeComplex da D hd hD).d (n + 1) n =
      ModuleCat.ofHom (gradedDifferential da D hd.nat_differential n) :=
  linearChainComplex_d _ _ _ n

theorem gradedFreeComplex_minimal (I : Ideal R)
    (hmin : ∀ x, D x ∈ I • (⊤ : Submodule R (A →₀ R))) (i j : ℕ) :
    LinearMap.range ((gradedFreeComplex da D hd hD).d i j).hom ≤
      I • (⊤ : Submodule R ((gradedFreeComplex da D hd hD).X j)) := by
  by_cases h : j + 1 = i
  · subst i
    rw [gradedFreeComplex_d]
    exact gradedDifferential_minimal I da D hd.nat_differential hmin j
  · rw [(gradedFreeComplex da D hd hD).shape i j h]
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact bot_le

end BPFixedPoints.ResolutionTools
