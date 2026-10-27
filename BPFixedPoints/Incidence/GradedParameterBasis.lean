import BPFixedPoints.Incidence.GradedBasisLift
import BPFixedPoints.Incidence.GradedPresentationEquivalence
import BPFixedPoints.Incidence.HilbertSeriesTools

/-! # A homogeneous free basis over a polynomial parameter algebra -/

namespace BPFixedPoints.ResolutionTools

open DirectSum MvPolynomial Finsupp
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k A σ : Type*} [Field k] [CommRing A] [Algebra k A] [Fintype σ]
  [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] [∀ q, Module.Finite k (𝒜 q)]

/-- Homogeneous lifts form a free basis if the actual Hilbert series has the parameter factor.
The quotient ideal and every grading in this statement use the original algebra operations. -/
theorem exists_homogeneous_parameter_basis
    (hp : ∀ i : σ, algebraMap (MvPolynomial σ k) A (X i) ∈ 𝒜 1)
    (J : Ideal A) (hJ : J = Ideal.span
      (Set.range (fun i : σ => algebraMap (MvPolynomial σ k) A (X i))))
    [Module.Finite k (A ⧸ J)]
    (hseries : gradedHilbertSeries 𝒜 =
      gradedHilbertSeries (gradedQuotientPiece 𝒜 J) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val) :
    ∃ b : Module.Basis (HomogeneousBasisIndex (gradedQuotientPiece 𝒜 J)) (MvPolynomial σ k) A,
      ∀ i, b i ∈ 𝒜 i.1 := by
  classical
  have hJh : J.IsHomogeneous 𝒜 := by
    rw [hJ]
    apply Ideal.homogeneous_span
    rintro x ⟨i, rfl⟩
    exact ⟨1, hp i⟩
  let ℬ := gradedQuotientPiece 𝒜 J
  letI : GradedAlgebra ℬ := gradedQuotientAlgebra 𝒜 J hJh
  let T := HomogeneousBasisIndex ℬ
  let w : T → ℕ := Sigma.fst
  let bQ := homogeneousBasis ℬ
  have hlift (i : T) : ∃ x : A, x ∈ 𝒜 (w i) ∧ Ideal.Quotient.mk J x = bQ i :=
    Submodule.mem_map.mp (homogeneousBasis_mem ℬ i)
  choose v hv hqv using hlift
  let f := Finsupp.linearCombination (MvPolynomial σ k) v
  have hmod : ∀ q x, x ∈ 𝒜 q → ∃ z ∈ weightedFreePiece w (q : ℤ),
      x - f z ∈ Ideal.span (Set.range (fun i : σ => algebraMap (MvPolynomial σ k) A (X i))) := by
    intro q x hx
    rw [← hJ]
    exact exists_weighted_lift_mod_ideal 𝒜 w v J bQ
      (fun q x hx i hi => homogeneousBasis_repr_eq_zero ℬ
        (Submodule.mem_map.mpr ⟨x, hx, rfl⟩) i hi) hqv hx
  have hs := linearCombination_graded_surjective 𝒜 w v hp hv hmod
  let 𝒲 : ℕ → Submodule k (T →₀ MvPolynomial σ k) :=
    fun q => weightedFreePiece w (q : ℤ)
  have hW : DirectSum.IsInternal 𝒲 :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (iSupIndep_weightedFreePiece_nat w) (iSup_weightedFreePiece_nat w)
  have hdim (q : ℕ) : Module.finrank k (𝒲 q) = Module.finrank k (𝒜 q) := by
    have hser : PowerSeries.mk (fun q => (Module.finrank k (𝒲 q) : ℤ)) =
        gradedHilbertSeries 𝒜 := by
      rw [weightedFreePiece_hilbert, ← Finset.sum_mul]
      change (∑ i : HomogeneousBasisIndex ℬ, (PowerSeries.X : PowerSeries ℤ) ^ i.1) * _ = _
      rw [homogeneousBasis_hilbert ℬ]
      exact hseries.symm
    have h := congrArg (PowerSeries.coeff q) hser
    simpa only [PowerSeries.coeff_mk, gradedHilbertSeries, Nat.cast_inj] using h
  have hbij : Function.Bijective f :=
    bijective_of_graded_surjective_of_finrank_eq 𝒲 𝒜 hW (Decomposition.isInternal 𝒜)
      (f.restrictScalars k) (fun _ _ hx => linearCombination_weighted_degree 𝒜 w v hp hv hx)
      hs hdim
  let e : (T →₀ MvPolynomial σ k) ≃ₗ[MvPolynomial σ k] A := LinearEquiv.ofBijective f hbij
  let b := (Finsupp.basisSingleOne : Module.Basis T (MvPolynomial σ k) _).map e
  refine ⟨b, fun i => ?_⟩
  have hb : b i = v i := by simp [b, e, f]
  rw [hb]
  exact hv i

end BPFixedPoints.ResolutionTools
