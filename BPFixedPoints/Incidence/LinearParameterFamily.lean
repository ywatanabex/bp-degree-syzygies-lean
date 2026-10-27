import BPFixedPoints.Incidence.LinearSequenceMultiplication
import BPFixedPoints.Incidence.LinearFamilyOpen
import BPFixedPoints.Incidence.FiniteCoefficientQuotient
import Mathlib.RingTheory.Artinian.Module

/-! # Linear parameter tuples and finite-dimensional quotient certificates -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k A σ ι : Type*} [Field k] [CommRing A] [Algebra k A] [Fintype σ] [Fintype ι]

/-- All tuples of linear combinations of the specified coefficient elements. -/
noncomputable def linearParameterForm (c : σ → A) (a : ι × σ → k) (i : ι) : A :=
  ∑ j, a (i, j) • c j

variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (c : σ → A) (hc : ∀ j, c j ∈ 𝒜 1)

include hc in
theorem linearParameterForm_mem (a : ι × σ → k) (i : ι) :
    linearParameterForm c a i ∈ 𝒜 1 :=
  Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hc j))

theorem linearParameterMultiply_eq (a : ι × σ → k) (q : ℕ) :
    linearSequenceMultiply 𝒜 (linearParameterForm c a) (linearParameterForm_mem 𝒜 c hc a) q =
      ∑ t : ι × σ, a t • (gradedLinearMultiply 𝒜 (hc t.2) q).comp (LinearMap.proj t.1) := by
  ext y
  simp [linearSequenceMultiply_apply, linearParameterForm, gradedLinearMultiply,
    Fintype.sum_prod_type, Finset.sum_mul, smul_mul_assoc]

variable [∀ q, Module.Finite k (𝒜 q)]

theorem exists_linearParameter_surjectivity_certificate (q : ℕ) (a : ι × σ → k)
    (ha : Function.Surjective (linearSequenceMultiply 𝒜 (linearParameterForm c a)
      (linearParameterForm_mem 𝒜 c hc a) q)) :
    ∃ P : MvPolynomial (ι × σ) k, eval a P ≠ 0 ∧ ∀ b, eval b P ≠ 0 →
      Function.Surjective (linearSequenceMultiply 𝒜 (linearParameterForm c b)
        (linearParameterForm_mem 𝒜 c hc b) q) := by
  let f : ι × σ → (ι → 𝒜 q) →ₗ[k] 𝒜 (q + 1) :=
    fun t => (gradedLinearMultiply 𝒜 (hc t.2) q).comp (LinearMap.proj t.1)
  have ha' : Function.Surjective (∑ t, a t • f t : (ι → 𝒜 q) →ₗ[k] 𝒜 (q + 1)) := by
    rwa [linearParameterMultiply_eq] at ha
  obtain ⟨P, hp, hb⟩ := exists_linear_family_surjectivity_certificate
    (M := ι → 𝒜 q) (N := 𝒜 (q + 1)) f a ha'
  exact ⟨P, hp, fun b h => by rw [linearParameterMultiply_eq]; exact hb b h⟩

variable [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]
  [Module.Finite (MvPolynomial σ k) A]

/-- Vanishing of one positive quotient component kills powers of every coefficient variable,
so finiteness over the coefficient ring yields a finite-dimensional Artin quotient. -/
theorem finite_quotient_of_linearSequenceMultiply_surjective
    (hx : ∀ j : σ, algebraMap (MvPolynomial σ k) A (X j) ∈ 𝒜 1)
    (x : ι → A) (hh : ∀ i, x i ∈ 𝒜 1) (q : ℕ)
    (hs : Function.Surjective (linearSequenceMultiply 𝒜 x hh q)) :
    Module.Finite k (A ⧸ Ideal.span (Set.range x)) ∧
      IsArtinianRing (A ⧸ Ideal.span (Set.range x)) := by
  let I : Ideal A := Ideal.span (Set.range x)
  have hf : Module.Finite k (A ⧸ I) := by
    apply finite_of_polynomial_variables_nilpotent (σ := σ) (q + 1) (Nat.succ_pos _)
    intro j
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ k) A (A ⧸ I), ← map_pow]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hm : (algebraMap (MvPolynomial σ k) A (X j)) ^ (q + 1) ∈ 𝒜 (q + 1) := by
      simpa using SetLike.pow_mem_graded (A := 𝒜) (q + 1) (hx j)
    apply (mem_ker_gradedQuotientMap 𝒜 I _ ⟨_, hm⟩).mp
    rw [← range_linearSequenceMultiply 𝒜 x hh q, LinearMap.range_eq_top.mpr hs]
    trivial
  exact ⟨hf, IsArtinianRing.of_finite k _⟩

end BPFixedPoints.ResolutionTools
