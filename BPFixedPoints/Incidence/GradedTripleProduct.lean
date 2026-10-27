import BPFixedPoints.Incidence.GradedMixedTensor
import BPFixedPoints.Incidence.GradedFreePairingLaws

/-! # Triple tensor complex and its two parenthesizations -/
namespace BPFixedPoints.ResolutionTools
open Finsupp
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] (degree : A → ℕ)

def tripleDegree (a : (A × A) × A) : ℕ := degree a.1.1 + degree a.1.2 + degree a.2

noncomputable def freeTriple (x y z : A →₀ R) : (A × A) × A →₀ R :=
  finsuppTensorFinsupp' R (A × A) A
    (finsuppTensorFinsupp' R A A (x ⊗ₜ[R] y) ⊗ₜ[R] z)

@[simp] theorem freeTriple_single (a b c : A) (r : R) :
    freeTriple (single a 1) (single b 1) (single c r) = single ((a,b),c) r := by
  simp [freeTriple]

theorem freeTriple_degree (p q r : ℕ) {x y z : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (hy : y ∈ gradedPiece R degree q)
    (hz : z ∈ gradedPiece R degree r) :
    freeTriple x y z ∈ gradedPiece R (tripleDegree degree) (p + q + r) := by
  apply (mem_supported' R _).mpr
  rintro ⟨⟨a,b⟩,c⟩ habc
  simp only [freeTriple, finsuppTensorFinsupp'_apply_apply]
  by_cases ha : degree a = p
  · by_cases hb : degree b = q
    · have hc : degree c ≠ r := fun hc => habc (by simp [tripleDegree, ha, hb, hc])
      rw [(mem_supported' R z).mp hz c hc, mul_zero]
    · rw [(mem_supported' R y).mp hy b hb, mul_zero, zero_mul]
  · rw [(mem_supported' R x).mp hx a ha, zero_mul, zero_mul]

theorem gradedParity_pair (x y : A →₀ R) :
    gradedParity (fun a : A × A => degree a.1 + degree a.2)
        (finsuppTensorFinsupp' R A A (x ⊗ₜ[R] y)) =
      finsuppTensorFinsupp' R A A (gradedParity degree x ⊗ₜ[R] gradedParity degree y) := by
  ext ⟨a,b⟩
  simp only [gradedParity_apply, finsuppTensorFinsupp'_apply_apply, pow_add]
  ring

variable (D : Module.End R (A →₀ R))
noncomputable def tripleD : Module.End R ((A × A) × A →₀ R) :=
  mixedTensorD (fun a : A × A => degree a.1 + degree a.2) (gradedTensorD degree D) D

theorem tripleD_triple (x y z : A →₀ R) :
    tripleD degree D (freeTriple x y z) = freeTriple (D x) y z +
      freeTriple (gradedParity degree x) (D y) z +
        freeTriple (gradedParity degree x) (gradedParity degree y) (D z) := by
  simp only [tripleD, freeTriple, mixedTensorD_tmul, gradedTensorD_tmul,
    gradedParity_pair, map_add, TensorProduct.add_tmul]

variable {degree D} (μ : GradedFreePairing degree D)
namespace GradedFreePairing

theorem parity_mul (x y : A →₀ R) :
    gradedParity degree (μ.mul x y) = μ.mul (gradedParity degree x) (gradedParity degree y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single b s =>
      rw [gradedParity_homogeneous degree (degree a + degree b)
        (μ.homogeneous _ _ (single_mem_supported _ _ rfl) (single_mem_supported _ _ rfl)),
        gradedParity_single, gradedParity_single, LinearMap.map_smul₂, map_smul, pow_add, smul_smul]

noncomputable def tripleLeft : ((A × A) × A →₀ R) →ₗ[R] (A →₀ R) :=
  μ.linearize.comp (freeTensorMap μ.linearize 1)

noncomputable def tripleRight : ((A × A) × A →₀ R) →ₗ[R] (A →₀ R) :=
  μ.linearize.comp ((freeTensorMap 1 μ.linearize).comp
    (Finsupp.lmapDomain R R (Equiv.prodAssoc A A A)))

theorem tripleLeft_triple (x y z : A →₀ R) :
    μ.tripleLeft (freeTriple x y z) = μ.mul (μ.mul x y) z := by
  simp only [tripleLeft, freeTriple, freeTensorMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    Module.End.one_apply, μ.linearize_tmul]

theorem tripleRight_triple (x y z : A →₀ R) :
    μ.tripleRight (freeTriple x y z) = μ.mul x (μ.mul y z) := by
  have h : (Finsupp.lmapDomain R R (Equiv.prodAssoc A A A)) (freeTriple x y z) =
      finsuppTensorFinsupp' R A (A × A)
        (x ⊗ₜ[R] finsuppTensorFinsupp' R A A (y ⊗ₜ[R] z)) := by
    ext ⟨a,b,c⟩
    simp only [lmapDomain_apply, mapDomain_equiv_apply, Equiv.prodAssoc_symm_apply,
      freeTriple, finsuppTensorFinsupp'_apply_apply]
    exact mul_assoc _ _ _
  simp only [tripleRight, LinearMap.comp_apply, h, freeTensorMap,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    Module.End.one_apply, μ.linearize_tmul]

theorem tripleLeft_chain (x : (A × A) × A →₀ R) :
    D (μ.tripleLeft x) = μ.tripleLeft (tripleD degree D x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single abc r =>
    rw [← freeTriple_single abc.1.1 abc.1.2 abc.2 r, tripleLeft_triple, tripleD_triple,
      map_add, map_add, tripleLeft_triple, tripleLeft_triple, tripleLeft_triple,
      μ.leibniz, μ.leibniz, μ.parity_mul, map_add, LinearMap.add_apply]

theorem tripleRight_chain (x : (A × A) × A →₀ R) :
    D (μ.tripleRight x) = μ.tripleRight (tripleD degree D x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single abc r =>
    rw [← freeTriple_single abc.1.1 abc.1.2 abc.2 r, tripleRight_triple, tripleD_triple,
      map_add, map_add, tripleRight_triple, tripleRight_triple, tripleRight_triple,
      μ.leibniz, μ.leibniz, map_add, add_assoc]

theorem tripleLeft_degree (n : ℕ) {x : (A × A) × A →₀ R}
    (hx : x ∈ gradedPiece R (tripleDegree degree) n) :
    μ.tripleLeft x ∈ gradedPiece R degree n := by
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  rintro ⟨⟨a,b⟩,c⟩ habc
  dsimp only
  rw [← freeTriple_single a b c _, tripleLeft_triple]
  have h : μ.mul (μ.mul (single a 1) (single b 1)) (single c (x ((a,b),c))) ∈
      gradedPiece R degree (degree a + degree b + degree c) :=
    μ.homogeneous (degree a + degree b) (degree c)
    (μ.homogeneous _ _ (single_mem_supported _ _ rfl) (single_mem_supported _ _ rfl))
    (single_mem_supported _ _ rfl)
  have hd : degree a + degree b + degree c = n := (mem_supported R x).mp hx habc
  simpa only [hd] using h

theorem tripleRight_degree (n : ℕ) {x : (A × A) × A →₀ R}
    (hx : x ∈ gradedPiece R (tripleDegree degree) n) :
    μ.tripleRight x ∈ gradedPiece R degree n := by
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  rintro ⟨⟨a,b⟩,c⟩ habc
  dsimp only
  rw [← freeTriple_single a b c _, tripleRight_triple]
  have h : μ.mul (single a 1) (μ.mul (single b 1) (single c (x ((a,b),c)))) ∈
      gradedPiece R degree (degree a + (degree b + degree c)) :=
    μ.homogeneous (degree a) (degree b + degree c)
    (single_mem_supported _ _ rfl)
    (μ.homogeneous _ _ (single_mem_supported _ _ rfl) (single_mem_supported _ _ rfl))
  have hd : degree a + (degree b + degree c) = n := by
    have hh := (mem_supported R x).mp hx habc
    change degree a + degree b + degree c = n at hh
    omega
  simpa only [hd] using h

end GradedFreePairing
end BPFixedPoints.ResolutionTools
