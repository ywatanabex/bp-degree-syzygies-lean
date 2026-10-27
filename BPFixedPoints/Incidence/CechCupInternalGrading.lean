import BPFixedPoints.Incidence.CechCupSigns
import BPFixedPoints.Incidence.CoefficientGrading
import BPFixedPoints.Incidence.CechCoefficientMatrices

/-!
# Coefficient degree of the Čech chain product

Prove additivity of homogeneous coefficient degrees from the basis formula
for the actual Alexander–Whitney product.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp

variable {k R I : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem coefficientwise_single (P : Submodule k R) (i : I) {r : R} (hr : r ∈ P) :
    single i r ∈ coefficientwise P := by
  classical
  intro j
  by_cases h : j = i
  · subst j; simpa using hr
  · rw [single_eq_of_ne h]; exact P.zero_mem

theorem coefficientwise_sign_smul (P : Submodule k R) (n : ℕ) {x : I →₀ R}
    (hx : x ∈ coefficientwise P) : (-1 : R) ^ n • x ∈ coefficientwise P := by
  apply coefficientwise_smul_constant P _ hx
  exact ⟨(-1 : k) ^ n, by simp⟩

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.CechProduct

open Finsupp ResolutionTools

variable {k σ : Type*} [CommRing k]

theorem finChainPairing_mul_coefficient_degree (n : ℕ) (d e : Fin n → ℕ)
    (a b : Fin n → Basis) {r s : MvPolynomial σ k} {p q : ℤ}
    (hr : r ∈ homogeneousCoeffPiece p) (hs : s ∈ homogeneousCoeffPiece q) :
    (finChainPairing (MvPolynomial σ k) n d e).mul (single a r) (single b s) ∈
      coefficientwise (homogeneousCoeffPiece (p + q)) := by
  rw [finChainPairing_mul_single]
  cases h : finCupBasis n e a b with
  | none => exact Submodule.zero_mem _
  | some z =>
    change single z ((-1 : MvPolynomial σ k) ^ finCupCross n a b * (r * s)) ∈ _
    rw [← smul_eq_mul, ← Finsupp.smul_single]
    exact coefficientwise_sign_smul _ _
      (coefficientwise_single _ z (homogeneousCoeffPiece_mul hr hs))

theorem chainCup_single_coefficient_degree {V : Type*} [Fintype V]
    (d e : V → ℕ) (a b : V → Basis) {r s : MvPolynomial σ k} {p q : ℤ}
    (hr : r ∈ homogeneousCoeffPiece p) (hs : s ∈ homogeneousCoeffPiece q) :
    chainCup (MvPolynomial σ k) d e (single a r) (single b s) ∈
      coefficientwise (homogeneousCoeffPiece (p + q)) := by
  let v := (Fintype.equivFin V).symm
  let re := v.arrowCongr (Equiv.refl Basis)
  have hsingle (z : V → Basis) (t : MvPolynomial σ k) :
      single z t = vertexReindex (MvPolynomial σ k) (single (re.symm z) t) := by
    change single z t = mapDomain re (single (re.symm z) t)
    rw [mapDomain_single, Equiv.apply_symm_apply]
  rw [hsingle a r, hsingle b s, chainCup_reindex]
  exact (MatrixOver.mapDomain (A := (algebraMap k (MvPolynomial σ k)).range) re).preserve_coefficients _
      (finChainPairing_mul_coefficient_degree (Fintype.card V) (d ∘ v) (e ∘ v)
        (re.symm a) (re.symm b) hr hs)

theorem chainCup_coefficient_degree {V : Type*} [Fintype V]
    (d e : V → ℕ) (p q : ℤ) {x y : C (MvPolynomial σ k) V}
    (hx : x ∈ coefficientwise (homogeneousCoeffPiece p))
    (hy : y ∈ coefficientwise (homogeneousCoeffPiece q)) :
    chainCup (MvPolynomial σ k) d e x y ∈
      coefficientwise (homogeneousCoeffPiece (p + q)) := by
  rw [← x.sum_single, map_finsuppSum, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro a _
  rw [← y.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro b _
  exact chainCup_single_coefficient_degree d e a b (hx a) (hy b)

theorem parity_pow_coefficient_degree {V : Type*} [Fintype V] (n : ℕ) (p : ℤ)
    {x : C (MvPolynomial σ k) V} (hx : x ∈ coefficientwise (homogeneousCoeffPiece p)) :
    (parity (MvPolynomial σ k) ^ n) x ∈ coefficientwise (homogeneousCoeffPiece p) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [parity_pow_succ_apply]
    exact (contraction_matrices (MvPolynomial σ k)
      (algebraMap k (MvPolynomial σ k)).range (0 : V → ℕ)).sign.preserve_coefficients _ ih

end BPFixedPoints.CechProduct
