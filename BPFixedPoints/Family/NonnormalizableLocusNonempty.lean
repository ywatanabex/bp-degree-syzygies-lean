import BPFixedPoints.Family.NonnormalizableLocusDominant
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Generic nonemptiness of the non-normalizable locus (ν ≥ 1)

`exists_poly_forall_exists_algHom`: if R is a finitely presented domain over an algebraically
closed field K and f : ι → R is algebraically independent (the map K[X_ι] → R is injective, i.e.
dominant), then there is a nonzero g ∈ K[X_ι] such that every c ∈ K^ι with g(c) ≠ 0 is the image
of a K-point of R: some K-algebra map ψ : R → K has ψ(f_i) = c_i. The proof uses Chevalley's
theorem (the image of Spec R → Spec K[X_ι] is constructible and contains the generic point, so it
contains a basic open D(g) with g ≠ 0), and then the Nullstellensatz (a residue field of R is
finite over K, hence equal to K) to produce a K-point over the closed point c.

Applied to the complex chart ring and the dominance theorem of
`NonnormalizableLocusDominant`, this gives: for connected G with ν(G) ≥ 1 there is a nonzero
g ∈ ℂ[a,b] such that the chart fiber over (a,b) is nonempty whenever g(a,b) ≠ 0
(`exists_poly_chartSolution_nonempty`), hence the non-normalizable locus is nonempty when in
addition a_e² ≠ 1 (`exists_poly_nonnormalizable_nonempty`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open MvPolynomial

/-- **Generic points of a dominant map.** If R is a finitely presented domain over an
algebraically closed field K and f : ι → R is algebraically independent over K, then some
nonzero g ∈ K[X_ι] has the property: for every c with g(c) ≠ 0 there is a K-algebra map
ψ : R → K with ψ ∘ f = c. -/
theorem exists_poly_forall_exists_algHom {K : Type*} [Field K] [IsAlgClosed K]
    {R : Type*} [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FinitePresentation K R]
    {ι : Type*} [Finite ι] (f : ι → R) (hf : AlgebraicIndependent K f) :
    ∃ g : MvPolynomial ι K, g ≠ 0 ∧
      ∀ c : ι → K, eval c g ≠ 0 → ∃ ψ : R →ₐ[K] K, ∀ i, ψ (f i) = c i := by
  classical
  set φ : MvPolynomial ι K →+* R := (aeval f).toRingHom with hφ
  have hinj : Function.Injective φ := (algebraicIndependent_iff_injective_aeval).mp hf
  have hfp : φ.FinitePresentation := by
    refine RingHom.FinitePresentation.of_comp_finiteType (algebraMap K (MvPolynomial ι K)) ?_ ?_
    · have : φ.comp (algebraMap K (MvPolynomial ι K)) = algebraMap K R := by
        rw [hφ]
        exact (aeval f).comp_algebraMap
      rw [this, RingHom.finitePresentation_algebraMap]
      infer_instance
    · rw [RingHom.finiteType_algebraMap]
      infer_instance
  have hcons := PrimeSpectrum.isConstructible_range_comap hfp
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hcons
  have hbot : (⊥ : PrimeSpectrum (MvPolynomial ι K)) ∈ Set.range (PrimeSpectrum.comap φ) := by
    refine ⟨⊥, PrimeSpectrum.ext ?_⟩
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  rw [← hS] at hbot
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion] at hbot
  obtain ⟨B0, hB0, hbotC⟩ := hbot
  simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
    PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] at hbotC
  obtain ⟨hg0, hf0⟩ := hbotC
  have hgk : ∀ k, B0.g k = 0 := fun k => hg0 ⟨k, rfl⟩
  refine ⟨B0.f, hf0, fun c hc => ?_⟩
  let p : PrimeSpectrum (MvPolynomial ι K) :=
    ⟨RingHom.ker (eval c), RingHom.ker_isPrime _⟩
  have hp : p ∈ Set.range (PrimeSpectrum.comap φ) := by
    rw [← hS]
    simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
    refine ⟨B0, hB0, ?_⟩
    simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k, rfl⟩
      rw [hgk k]
      exact Ideal.zero_mem _
    · intro h
      exact hc h
  obtain ⟨q, hq⟩ := hp
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  let _ : Field (R ⧸ M) := Ideal.Quotient.field M
  have : Algebra.FiniteType K (R ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K M) Ideal.Quotient.mk_surjective
  have : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  have : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsIntegral.isAlgebraic
  let ψ : R →ₐ[K] K := (IsAlgClosed.lift : (R ⧸ M) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K M)
  refine ⟨ψ, fun i => ?_⟩
  have hmem : X i - C (c i) ∈ p.asIdeal := by
    change X i - C (c i) ∈ RingHom.ker (eval c)
    simp [RingHom.mem_ker]
  rw [← hq] at hmem
  change φ (X i - C (c i)) ∈ q.asIdeal at hmem
  have hM' : φ (X i - C (c i)) ∈ M := hqM hmem
  have hψ : ψ (φ (X i - C (c i))) = 0 := by
    change (IsAlgClosed.lift : (R ⧸ M) →ₐ[K] K) (Ideal.Quotient.mk M _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hM', map_zero]
  simp only [hφ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, aeval_X, aeval_C,
    AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hψ
  exact sub_eq_zero.mp hψ

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

theorem chartDen_complex_ne_zero : (chartDen (E := E) ℂ) ≠ 0 := by
  intro h
  have hx : IsChartPoint (fun _ : E => (3 : ℂ)) (fun _ => 1) := fun e => by norm_num
  have := aeval_chartDen_ne_zero (k := ℂ) hx
  rw [h, map_zero] at this
  exact this rfl

instance : IsDomain (ChartRing (E := E) ℂ) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors chartDen_complex_ne_zero)

instance : Algebra.FinitePresentation ℂ (ChartRing (E := E) ℂ) := by
  have : Algebra.FinitePresentation (MvPolynomial (E ⊕ E) ℂ) (ChartRing (E := E) ℂ) :=
    IsLocalization.Away.finitePresentation (chartDen (E := E) ℂ)
  exact Algebra.FinitePresentation.trans ℂ (MvPolynomial (E ⊕ E) ℂ) (ChartRing (E := E) ℂ)

/-- **Generic nonemptiness of the chart fiber.** For connected G with ν(G) ≥ 1 (|V| ≤ |E|)
there is a nonzero g ∈ ℂ[a,b] such that the chart fiber over (a,b) is nonempty whenever
g(a,b) ≠ 0. -/
theorem exists_poly_chartSolution_nonempty (hc : G.Connected)
    (hcard : Fintype.card V ≤ Fintype.card E) :
    ∃ g : MvPolynomial (E ⊕ V) ℂ, g ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), eval (Sum.elim a b) g ≠ 0 → ∃ x, G.IsChartSolution a b x := by
  obtain ⟨g, hg, h⟩ := exists_poly_forall_exists_algHom (G.chartRingFamily ℂ)
    (G.chartRingFamily_algebraicIndependent hc hcard)
  refine ⟨g, hg, fun a b hab => ?_⟩
  obtain ⟨ψ, hψ⟩ := h _ hab
  set x : E → ℂ := fun e => ψ (chartRingX ℂ e)
  have ha : ∀ e, ψ (chartRingA ℂ e) = a e := fun e => hψ (Sum.inl e)
  have hx : IsChartPoint a x := by
    intro e
    obtain ⟨hX, hAX, h1⟩ := isUnit_chartRing_factors (E := E) ℂ e
    refine ⟨(hX.map ψ).ne_zero, fun h' => (hAX.map ψ).ne_zero ?_, fun h' => (h1.map ψ).ne_zero ?_⟩
    · rw [map_sub, ha]
      change a e - x e = 0
      rw [h', sub_self]
    · have : ψ (algebraMap (MvPolynomial (E ⊕ E) ℂ) (ChartRing (E := E) ℂ)
          (1 - X (Sum.inl e) * X (Sum.inr e))) = 1 - a e * x e := by
        rw [map_sub, map_one, map_mul, map_sub, map_one, map_mul]
        rw [← ha e]
        rfl
      rw [this, h', sub_self]
  have hψeq : chartRingEval a x hx = ψ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartDen (E := E) ℂ))
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, chartRingEval_algebraMap, aeval_C,
        ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      simp
    · intro z
      rw [RingHom.comp_apply, RingHom.comp_apply, chartRingEval_algebraMap, aeval_X]
      rcases z with e | e
      · exact (ha e).symm
      · rfl
  refine ⟨x, (G.isChartSolution_iff_eval (k := ℂ) hx).mpr ?_⟩
  rw [hψeq]
  funext z
  exact hψ z

/-- **`supp:nonnormalizable-dim`, nonemptiness.** For connected G with ν(G) ≥ 1 there is a
nonzero g ∈ ℂ[a,b] such that for all complex a, b with g(a,b) ≠ 0 we have a_e² ≠ 1 for every
edge and the non-normalizable locus at (a,b) is nonempty. -/
theorem exists_poly_nonnormalizable_nonempty (hc : G.Connected)
    (hcard : Fintype.card V ≤ Fintype.card E) :
    ∃ g : MvPolynomial (E ⊕ V) ℂ, g ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), eval (Sum.elim a b) g ≠ 0 →
        (∀ e, a e ^ 2 ≠ 1) ∧ ∃ y, G.IsNonnormalizableSolution a b y := by
  obtain ⟨g, hg, h⟩ := G.exists_poly_chartSolution_nonempty hc hcard
  have hsq : ∀ e : E, (X (Sum.inl e) ^ 2 - 1 : MvPolynomial (E ⊕ V) ℂ) ≠ 0 := by
    intro e h0
    have := congrArg (eval (fun _ => (0 : ℂ))) h0
    simp at this
  refine ⟨g * ∏ e, (X (Sum.inl e) ^ 2 - 1), mul_ne_zero hg
    (Finset.prod_ne_zero_iff.mpr fun e _ => hsq e), fun a b hab => ?_⟩
  rw [eval_mul, eval_prod] at hab
  have ha : ∀ e, a e ^ 2 ≠ 1 := by
    intro e h1
    apply hab
    rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp [h1]), mul_zero]
  refine ⟨ha, ?_⟩
  obtain ⟨x, hx⟩ := h a b (left_ne_zero_of_mul hab)
  exact (G.nonnormalizable_nonempty_iff b ha).mpr ⟨x, hx⟩

end Multigraph

end BPFixedPoints
