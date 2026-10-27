import BPFixedPoints.Incidence.GradedPolynomialEvaluation
import BPFixedPoints.Incidence.LinearSequenceMultiplication
import BPFixedPoints.Incidence.HomogeneousBasis

/-! # Homogeneous lifts of a quotient basis generate over the parameter algebra -/

namespace BPFixedPoints.ResolutionTools

open DirectSum MvPolynomial Finsupp
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k A σ I : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype σ] [Fintype I] [Algebra (MvPolynomial σ k) A]
  [IsScalarTower k (MvPolynomial σ k) A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  (w : I → ℕ) (v : I → A)

/-- A homogeneous quotient basis can be lifted with constant coefficients in its own degree. -/
theorem exists_weighted_lift_mod_ideal (J : Ideal A) (b : Module.Basis I k (A ⧸ J))
    (hb : ∀ q x, x ∈ 𝒜 q → ∀ i, q ≠ w i →
      b.repr (Ideal.Quotient.mk J x) i = 0)
    (hv : ∀ i, Ideal.Quotient.mk J (v i) = b i)
    {q : ℕ} {x : A} (hx : x ∈ 𝒜 q) :
    ∃ z ∈ weightedFreePiece w (q : ℤ),
      x - Finsupp.linearCombination (MvPolynomial σ k) v z ∈ J := by
  classical
  let c := b.repr (Ideal.Quotient.mk J x)
  let z : I →₀ MvPolynomial σ k := ∑ i, single i (C (c i))
  have hz : z ∈ weightedFreePiece w (q : ℤ) := by
    apply Submodule.sum_mem
    intro i _
    apply weightedFreePiece_single
    by_cases hi : q = w i
    · rw [hi, sub_self]
      exact homogeneousCoeffPiece_C _
    · have hc : c i = 0 := hb q x hx i hi
      simp only [hc, map_zero]
      exact Submodule.zero_mem _
  have he : Finsupp.linearCombination (MvPolynomial σ k) v z = ∑ i, c i • v i := by
    simp only [z, map_sum, linearCombination_single]
    apply Finset.sum_congr rfl
    intro i _
    exact IsScalarTower.algebraMap_smul (MvPolynomial σ k) (c i) (v i)
  refine ⟨z, hz, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [he, map_sub]
  have hm : Ideal.Quotient.mk J (∑ i, c i • v i) = ∑ i, c i • b i := by
    change (Ideal.Quotient.mkₐ k J) (∑ i, c i • v i) = _
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (Ideal.Quotient.mkₐ k J) (v i) = b i from hv i]
  rw [hm, b.sum_repr (Ideal.Quotient.mk J x), sub_self]

/-- Graded Nakayama with specified homogeneous lifts, preserving the source degree. -/
theorem linearCombination_graded_surjective
    (hp : ∀ i : σ, algebraMap (MvPolynomial σ k) A (X i) ∈ 𝒜 1)
    (hv : ∀ i, v i ∈ 𝒜 (w i))
    (hmod : ∀ q (x : A), x ∈ 𝒜 q →
      ∃ z ∈ weightedFreePiece w (q : ℤ),
        x - Finsupp.linearCombination (MvPolynomial σ k) v z ∈
          Ideal.span (Set.range (fun i : σ => algebraMap (MvPolynomial σ k) A (X i)))) :
    ∀ q (x : A), x ∈ 𝒜 q → ∃ z ∈ weightedFreePiece w (q : ℤ),
      Finsupp.linearCombination (MvPolynomial σ k) v z = x := by
  classical
  let p : σ → A := fun i => algebraMap (MvPolynomial σ k) A (X i)
  let J := Ideal.span (Set.range p)
  let f := Finsupp.linearCombination (MvPolynomial σ k) v
  intro q
  induction q with
  | zero =>
    intro x hx
    obtain ⟨z, hz, hm⟩ := hmod 0 x hx
    have hd : x - f z ∈ 𝒜 0 :=
      (𝒜 0).sub_mem hx (linearCombination_weighted_degree 𝒜 w v hp hv hz)
    have hle : J ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      apply Ideal.span_le.mpr
      rintro a ⟨i, rfl⟩
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (hp i)
    have hh := hle hm
    change (decompose 𝒜 (x - f z) 0 : A) = 0 at hh
    rw [decompose_of_mem_same 𝒜 hd] at hh
    exact ⟨z, hz, (sub_eq_zero.mp hh).symm⟩
  | succ q ih =>
    intro x hx
    obtain ⟨z, hz, hm⟩ := hmod (q + 1) x hx
    have hd : x - f z ∈ 𝒜 (q + 1) :=
      (𝒜 (q + 1)).sub_mem hx (linearCombination_weighted_degree 𝒜 w v hp hv hz)
    have hk : (⟨x - f z, hd⟩ : 𝒜 (q + 1)) ∈
        LinearMap.ker (gradedQuotientMap 𝒜 J (q + 1)) :=
      (mem_ker_gradedQuotientMap 𝒜 J _ _).mpr hm
    rw [← range_linearSequenceMultiply 𝒜 p hp q] at hk
    obtain ⟨a, ha⟩ := hk
    choose u hu heu using (fun i => ih (a i).val (a i).property)
    have heu' (i) : f (u i) = (a i).val := heu i
    have he : (∑ i, p i * (a i).val) = x - f z := by
      simpa only [linearSequenceMultiply_apply] using congrArg Subtype.val ha
    refine ⟨z + ∑ i, (X i : MvPolynomial σ k) • u i,
      (weightedFreePiece w ((q + 1 : ℕ) : ℤ)).add_mem hz
        (Submodule.sum_mem _ (fun i _ => weightedFreePiece_X_smul w (hu i) i)), ?_⟩
    change f (z + ∑ i, (X i : MvPolynomial σ k) • u i) = x
    rw [map_add, map_sum]
    simp only [map_smul, heu', Algebra.smul_def]
    change f z + ∑ i, p i * (a i).val = x
    rw [he]
    abel

end BPFixedPoints.ResolutionTools
