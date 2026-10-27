import BPFixedPoints.Incidence.KoszulBilinear
import BPFixedPoints.Incidence.KoszulGrading

/-!
# Degrees after coefficient change of local Koszul contractions

Coefficient-ring isomorphisms preserve exterior states. Transferring the
contraction to the actual four-coefficient edge equations retains homotopy
degree +1 and quotient-section degree zero.
-/

namespace BPFixedPoints.Koszul

open ResolutionTools IncidencePerturbation

set_option linter.unusedSectionVars false

variable {E R A B : Type*} [LinearOrder E] [Fintype E]
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem coeffEquiv_degree (φ : A ≃ₐ[R] B) :
    HasDegree exteriorDegree exteriorDegree 0 (coeffEquiv (E := E) φ).toLinearMap := by
  simpa only [coeffEquiv, Finsupp.mapRange.linearEquiv_toLinearMap] using
    HasDegree.mapRange φ.toLinearMap (exteriorDegree (E := E))

theorem coeffEquiv_symm_degree (φ : A ≃ₐ[R] B) :
    HasDegree exteriorDegree exteriorDegree 0 (coeffEquiv (E := E) φ).symm.toLinearMap := by
  simpa only [coeffEquiv, Finsupp.mapRange.linearEquiv_symm,
    Finsupp.mapRange.linearEquiv_toLinearMap] using
    HasDegree.mapRange φ.toLinearEquiv.symm.toLinearMap (exteriorDegree (E := E))

variable {σ : Type*} [DecidableEq σ]

theorem transportedContraction_h_degree (ι : E → σ) (hι : Function.Injective ι)
    (φ : MvPolynomial σ R ≃ₐ[R] A) :
    HasDegree exteriorDegree exteriorDegree 1 (transportedContraction ι hι φ).h := by
  intro n x hx
  rw [transportedContraction, Contraction.congr_h_apply]
  have h₁ := coeffEquiv_symm_degree φ n x hx
  have h₂ := variableContraction_h_degree ι hι (n + 0) _ h₁
  have h₃ := coeffEquiv_degree φ (n + 0 + 1) _ h₂
  simpa only [add_zero, LinearEquiv.coe_coe] using h₃

theorem transportedContraction_i_mem_degree_zero (ι : E → σ) (hι : Function.Injective ι)
    (φ : MvPolynomial σ R ≃ₐ[R] A) (x : A ⧸ transportedIdeal ι φ) :
    (transportedContraction ι hι φ).i x ∈
      Finsupp.supported A R {S | exteriorDegree S = 0} := by
  rw [transportedContraction, Contraction.congr_i_apply]
  have h := coeffEquiv_degree φ 0 _
    (variableContraction_i_mem_degree_zero ι hι
      ((transportedQuotientEquiv ι φ).symm x))
  simpa only [add_zero, LinearEquiv.coe_coe, AlgEquiv.coe_symm_toLinearEquiv] using h

theorem transportedContraction_p_eq_zero (ι : E → σ) (hι : Function.Injective ι)
    (φ : MvPolynomial σ R ≃ₐ[R] A) {n : ℤ} {x : Space E A}
    (hx : x ∈ Finsupp.supported A R {S | exteriorDegree S = n}) (hn : n ≠ 0) :
    (transportedContraction ι hι φ).p x = 0 := by
  rw [transportedContraction_p]
  have hx0 : x ∅ = 0 := (Finsupp.mem_supported' R x).mp hx ∅ (by
    change exteriorDegree ∅ ≠ n
    simpa only [exteriorDegree, Finset.card_empty, Nat.cast_zero] using hn.symm)
  rw [hx0, map_zero]

theorem bilinearContraction_h_degree (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R) :
    HasDegree exteriorDegree exteriorDegree 1 (bilinearContraction τ₁ τ₂ x y).h := by
  intro n z hz
  rw [bilinearContraction, Contraction.congr_h_apply]
  exact transportedContraction_h_degree pivotIndex pivotIndex_injective
    (flippedBilinearEquiv τ₁ τ₂ x y) n z hz

theorem bilinearContraction_i_mem_degree_zero (τ₁ τ₂ : E → Fin 2 ≃ Fin 2)
    (x y : E → R) (z : MvPolynomial (E × Fin 2 × Fin 2) R ⧸ bilinearIdeal τ₁ τ₂ x y) :
    (bilinearContraction τ₁ τ₂ x y).i z ∈
      Finsupp.supported (MvPolynomial (E × Fin 2 × Fin 2) R) R
        {S | exteriorDegree S = 0} := by
  rw [bilinearContraction, Contraction.congr_i_apply]
  exact transportedContraction_i_mem_degree_zero pivotIndex pivotIndex_injective
    (flippedBilinearEquiv τ₁ τ₂ x y) _

theorem bilinearContraction_p_eq_zero (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R)
    {n : ℤ} {z : Space E (MvPolynomial (E × Fin 2 × Fin 2) R)}
    (hz : z ∈ Finsupp.supported (MvPolynomial (E × Fin 2 × Fin 2) R) R
      {S | exteriorDegree S = n}) (hn : n ≠ 0) :
    (bilinearContraction τ₁ τ₂ x y).p z = 0 := by
  rw [bilinearContraction_p]
  have hz0 : z ∅ = 0 := (Finsupp.mem_supported' R z).mp hz ∅ (by
    change exteriorDegree ∅ ≠ n
    simpa only [exteriorDegree, Finset.card_empty, Nat.cast_zero] using hn.symm)
  rw [hz0, map_zero]

end BPFixedPoints.Koszul
