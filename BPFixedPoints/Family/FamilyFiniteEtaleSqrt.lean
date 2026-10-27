import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Square-root algebras A[x_i]/(x_i²−s_i)

For a commutative ring A and a finite family s:ι→A, let
`SqrtAlg s = A[X_i]/(X_i²−s_i)`.

* `sqrtAlgBasis`: the monomials ∏_{i∈S}x_i, S⊆ι, form an A-basis, so
  `SqrtAlg s` is free of rank 2^|ι| (`finrank_sqrtAlg`). No unit condition
  is needed here.
* `sqrtAlg_etale`: if 2 and every s_i are units, `SqrtAlg s` is étale over A
  (Mathlib's `Algebra.Etale`). Formal étaleness is checked on the lifting
  property: square roots of units lift uniquely through square-zero ideals.

The belief cover `eq:belief-cover` is of this form
(`FamilyFiniteEtaleBelief.lean`).
-/

namespace BPFixedPoints

open MvPolynomial
set_option linter.unusedSectionVars false

section SqrtAlg

variable {A : Type*} [CommRing A] {ι : Type*} (s : ι → A)

/-- The ideal (X_i²−s_i) of A[X_i]. -/
noncomputable def sqrtIdeal : Ideal (MvPolynomial ι A) :=
  Ideal.span (Set.range fun i => X i ^ 2 - C (s i))

/-- The square-root algebra A[X_i]/(X_i²−s_i). -/
abbrev SqrtAlg := MvPolynomial ι A ⧸ sqrtIdeal s

/-- The class x_i of X_i in `SqrtAlg s`. -/
noncomputable def sqrtRoot (i : ι) : SqrtAlg s := Ideal.Quotient.mk (sqrtIdeal s) (X i)

theorem sqrtRoot_sq (i : ι) : sqrtRoot s i ^ 2 = algebraMap A (SqrtAlg s) (s i) := by
  rw [sqrtRoot, ← map_pow, ← sub_eq_zero, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq,
    ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {T : Type*} [CommRing T] [Algebra A T]

theorem aeval_eq_zero_of_mem_sqrtIdeal (x : ι → T) (hx : ∀ i, x i ^ 2 = algebraMap A T (s i))
    {a : MvPolynomial ι A} (ha : a ∈ sqrtIdeal s) : aeval x a = 0 := by
  have hle : sqrtIdeal s ≤ RingHom.ker (aeval x : MvPolynomial ι A →ₐ[A] T) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp [hx i]
  exact RingHom.mem_ker.1 (hle ha)

/-- The A-algebra map `SqrtAlg s → T` sending x_i to a square root x_i of s_i in T. -/
noncomputable def sqrtLift (x : ι → T) (hx : ∀ i, x i ^ 2 = algebraMap A T (s i)) :
    SqrtAlg s →ₐ[A] T :=
  Ideal.Quotient.liftₐ (sqrtIdeal s) (aeval x) fun _ ha => aeval_eq_zero_of_mem_sqrtIdeal s x hx ha

@[simp] theorem sqrtLift_root (x : ι → T) (hx : ∀ i, x i ^ 2 = algebraMap A T (s i)) (i : ι) :
    sqrtLift s x hx (sqrtRoot s i) = x i := by
  have h := AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp (sqrtIdeal s) (aeval x)
    fun _ ha => aeval_eq_zero_of_mem_sqrtIdeal s x hx ha) (X i)
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, aeval_X] at h
  exact h

theorem sqrtAlg_hom_ext {f g : SqrtAlg s →ₐ[A] T}
    (h : ∀ i, f (sqrtRoot s i) = g (sqrtRoot s i)) : f = g :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

/-! ### The monomial basis -/

section Basis

variable [Fintype ι] [DecidableEq ι]

/-- The monomial x^S=∏_{i∈S}x_i. -/
noncomputable def sqrtMonomial (S : Finset ι) : SqrtAlg s := ∏ i ∈ S, sqrtRoot s i

/-- Odd part {i : n_i odd} of an exponent vector. -/
def sqrtOddPart (n : ι →₀ ℕ) : Finset ι := Finset.univ.filter fun i => n i % 2 = 1

/-- Square factor ∏_i s_i^{⌊n_i/2⌋} of an exponent vector. -/
noncomputable def sqrtSqFactor (n : ι →₀ ℕ) : A := ∏ i, s i ^ (n i / 2)

/-- Reduction X^n ↦ sqrtSqFactor(n)·e_{sqrtOddPart(n)}, an A-linear map A[X]→A^{Finset ι}. -/
noncomputable def sqrtReduce : MvPolynomial ι A →ₗ[A] (Finset ι → A) :=
  (basisMonomials ι A).constr A fun n => sqrtSqFactor s n • Pi.single (sqrtOddPart n) 1

theorem sqrtReduce_monomial_one (n : ι →₀ ℕ) :
    sqrtReduce s (monomial n 1) = sqrtSqFactor s n • Pi.single (sqrtOddPart n) 1 := by
  have h := (basisMonomials ι A).constr_basis A
    (fun n => sqrtSqFactor s n • (Pi.single (sqrtOddPart n) 1 : Finset ι → A)) n
  rw [coe_basisMonomials] at h
  exact h

theorem sqrtOddPart_add_two (n : ι →₀ ℕ) (i : ι) : sqrtOddPart (n + Finsupp.single i 2) = sqrtOddPart n := by
  ext j
  simp only [sqrtOddPart, Finset.mem_filter, Finset.mem_univ, true_and, Finsupp.add_apply,
    Finsupp.single_apply]
  split_ifs <;> omega

theorem sqrtSqFactor_add_two (n : ι →₀ ℕ) (i : ι) :
    sqrtSqFactor s (n + Finsupp.single i 2) = s i * sqrtSqFactor s n := by
  have h : ∀ j, s j ^ ((n + Finsupp.single i 2 : ι →₀ ℕ) j / 2) =
      (if i = j then s j else 1) * s j ^ (n j / 2) := by
    intro j
    rw [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with hij
    · rw [Nat.add_div_right _ two_pos, pow_succ, mul_comm]
    · rw [add_zero, one_mul]
  rw [sqrtSqFactor, Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq, ite_eq_left (Finset.mem_univ i), sqrtSqFactor]

theorem sqrtReduce_mul_generator (q : MvPolynomial ι A) (i : ι) :
    sqrtReduce s (q * (X i ^ 2 - C (s i))) = 0 := by
  have hL : (sqrtReduce s).comp (LinearMap.mulRight A (X i ^ 2 - C (s i))) = 0 := by
    apply (basisMonomials ι A).ext
    intro n
    have hm : monomial n (1 : A) * (X i ^ 2 - C (s i)) =
        monomial (n + Finsupp.single i 2) 1 - s i • monomial n 1 := by
      rw [mul_sub, X_pow_eq_monomial, monomial_mul_monomial, one_mul,
        mul_comm (monomial n 1) (C (s i)), C_mul']
    rw [coe_basisMonomials, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.zero_apply,
      hm, map_sub, map_smul, sqrtReduce_monomial_one, sqrtReduce_monomial_one, sqrtOddPart_add_two,
      sqrtSqFactor_add_two, smul_smul, sub_self]
  exact LinearMap.congr_fun hL q

theorem sqrtReduce_eq_zero {p : MvPolynomial ι A} (hp : p ∈ sqrtIdeal s) : sqrtReduce s p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => sqrtReduce_mul_generator s (c i) i

/-- Indicator exponent vector of S. -/
noncomputable def sqrtIndicatorExp (S : Finset ι) : ι →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

theorem sqrtIndicatorExp_apply (S : Finset ι) (j : ι) : sqrtIndicatorExp S j = if j ∈ S then 1 else 0 := by
  rw [sqrtIndicatorExp, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem sqrt_prod_X_eq_monomial (S : Finset ι) :
    (∏ i ∈ S, X i : MvPolynomial ι A) = monomial (sqrtIndicatorExp S) 1 := by
  rw [sqrtIndicatorExp, monomial_sum_one]
  rfl

theorem sqrtReduce_prod_X (S : Finset ι) :
    sqrtReduce s (∏ i ∈ S, X i) = Pi.single S 1 := by
  rw [sqrt_prod_X_eq_monomial, sqrtReduce_monomial_one]
  have hodd : sqrtOddPart (sqrtIndicatorExp S) = S := by
    ext j
    simp only [sqrtOddPart, Finset.mem_filter, Finset.mem_univ, true_and, sqrtIndicatorExp_apply]
    split_ifs with h <;> simp [h]
  have hsq : sqrtSqFactor s (sqrtIndicatorExp S) = 1 := by
    rw [sqrtSqFactor]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [sqrtIndicatorExp_apply]
    split_ifs <;> simp
  rw [hodd, hsq, one_smul]

theorem mk_monomial_one (n : ι →₀ ℕ) :
    Ideal.Quotient.mk (sqrtIdeal s) (monomial n 1) =
      sqrtSqFactor s n • sqrtMonomial s (sqrtOddPart n) := by
  have hmon : (monomial n (1 : A)) = ∏ i, X i ^ (n i) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype]
    intro i
    rw [pow_zero]
  have hpow : ∀ i, sqrtRoot s i ^ (n i) =
      algebraMap A (SqrtAlg s) (s i ^ (n i / 2)) * (if n i % 2 = 1 then sqrtRoot s i else 1) := by
    intro i
    conv_lhs => rw [← Nat.div_add_mod (n i) 2, pow_add, pow_mul, sqrtRoot_sq, ← map_pow]
    rcases Nat.mod_two_eq_zero_or_one (n i) with h | h <;> simp [h]
  rw [hmon, map_prod]
  simp only [map_pow]
  change ∏ i, sqrtRoot s i ^ (n i) = _
  rw [Finset.prod_congr rfl fun i _ => hpow i, Finset.prod_mul_distrib, ← map_prod,
    show sqrtSqFactor s n • sqrtMonomial s (sqrtOddPart n) =
      algebraMap A (SqrtAlg s) (sqrtSqFactor s n) * sqrtMonomial s (sqrtOddPart n) from Algebra.smul_def (sqrtSqFactor s n) (sqrtMonomial s (sqrtOddPart n)),
    sqrtMonomial, sqrtOddPart, Finset.prod_filter]
  rfl

/-- x^S as an A-linear combination: (c_S) ↦ Σ_S c_S x^S. -/
noncomputable def sqrtCombination : (Finset ι → A) →ₗ[A] SqrtAlg s :=
  Fintype.linearCombination A (sqrtMonomial s)

theorem mkₐ_eq_comp :
    (Ideal.Quotient.mkₐ A (sqrtIdeal s)).toLinearMap = (sqrtCombination s).comp (sqrtReduce s) := by
  apply (basisMonomials ι A).ext
  intro n
  rw [coe_basisMonomials, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, mk_monomial_one,
    LinearMap.comp_apply, sqrtReduce_monomial_one, map_smul, sqrtCombination,
    Fintype.linearCombination_apply_single, one_smul]

theorem sqrtCombination_bijective : Function.Bijective (sqrtCombination s) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    let P : MvPolynomial ι A := ∑ S, c S • ∏ i ∈ S, X i
    have hP : Ideal.Quotient.mk (sqrtIdeal s) P = sqrtCombination s c := by
      simp only [P, map_sum, sqrtCombination, Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [← Ideal.Quotient.mkₐ_eq_mk A, map_smul, map_prod]
      rfl
    have hmem : P ∈ sqrtIdeal s := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hP, hc]
    have h1 := sqrtReduce_eq_zero s hmem
    simp only [P, map_sum, map_smul, sqrtReduce_prod_X] at h1
    rw [← h1]
    funext S
    simp [Finset.sum_apply, Pi.single_apply]
  · intro t
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨sqrtReduce s p, ?_⟩
    rw [← LinearMap.comp_apply, ← mkₐ_eq_comp]
    rfl

/-- **Monomial basis.** The monomials x^S, S⊆ι, form an A-basis of `SqrtAlg s`. -/
noncomputable def sqrtAlgBasis : Module.Basis (Finset ι) A (SqrtAlg s) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective (sqrtCombination s) (sqrtCombination_bijective s)).symm

theorem sqrtAlg_free : Module.Free A (SqrtAlg s) := Module.Free.of_basis (sqrtAlgBasis s)

theorem sqrtAlg_finite : Module.Finite A (SqrtAlg s) := Module.Finite.of_basis (sqrtAlgBasis s)

/-- **Rank 2^|ι|.** -/
theorem finrank_sqrtAlg [Nontrivial A] : Module.finrank A (SqrtAlg s) = 2 ^ Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (sqrtAlgBasis s), Fintype.card_finset]

end Basis

/-! ### Étaleness -/

section Etale

variable {s}

theorem sqrtAlg_root_sq_map {B : Type*} [CommRing B] [Algebra A B] (f : SqrtAlg s →ₐ[A] B) (i : ι) :
    f (sqrtRoot s i) ^ 2 = algebraMap A B (s i) := by
  rw [← map_pow, sqrtRoot_sq, AlgHom.commutes]

/-- **Formal étaleness.** If 2 and all s_i are units, square roots lift uniquely through square-zero ideals. -/
theorem sqrtAlg_formallyEtale (h2 : IsUnit (2 : A)) (hs : ∀ i, IsUnit (s i)) :
    Algebra.FormallyEtale A (SqrtAlg s) := by
  rw [Algebra.FormallyEtale.iff_comp_bijective]
  intro B _ _ I hI
  have hsq : ∀ a b : B, a ∈ I → b ∈ I → a * b = 0 := by
    intro a b ha hb
    have h : a * b ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    rw [hI] at h
    exact (Submodule.mem_bot _).1 h
  constructor
  · intro f g hfg
    apply sqrtAlg_hom_ext
    intro i
    have hx := sqrtAlg_root_sq_map f i
    have hy := sqrtAlg_root_sq_map g i
    have hxy : f (sqrtRoot s i) - g (sqrtRoot s i) ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact AlgHom.congr_fun hfg (sqrtRoot s i)
    have h0 := hsq _ _ hxy hxy
    have hyu : IsUnit (2 * g (sqrtRoot s i)) := by
      have hu : IsUnit (g (sqrtRoot s i) ^ 2) := by
        rw [hy]
        exact (hs i).map _
      have h2' : IsUnit (2 : B) := by
        rw [← map_ofNat (algebraMap A B) 2]
        exact h2.map _
      exact h2'.mul ((isUnit_pow_iff two_ne_zero).1 hu)
    have h3 : (f (sqrtRoot s i) - g (sqrtRoot s i)) * (2 * g (sqrtRoot s i)) = 0 := by
      linear_combination hx - hy - h0
    exact sub_eq_zero.1 (hyu.mul_left_eq_zero.1 h3)
  · intro g
    choose y hy using fun i => Ideal.Quotient.mk_surjective (g (sqrtRoot s i))
    have hg := sqrtAlg_root_sq_map g
    have hgu : ∀ i, IsUnit (g (sqrtRoot s i)) := fun i =>
      (isUnit_pow_iff two_ne_zero).1 (by rw [hg]; exact (hs i).map _)
    have hyu : ∀ i, IsUnit (2 * y i) := by
      intro i
      rw [← IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩, map_mul, hy]
      have h2' : IsUnit (2 : B ⧸ I) := by
        rw [← map_ofNat (algebraMap A (B ⧸ I)) 2]
        exact h2.map _
      exact h2'.mul (hgu i)
    have hdI : ∀ i, y i ^ 2 - algebraMap A B (s i) ∈ I := by
      intro i
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hy, Ideal.Quotient.mk_algebraMap,
        hg, sub_self]
    have hεI : ∀ i, (y i ^ 2 - algebraMap A B (s i)) * ↑(hyu i).unit⁻¹ ∈ I := fun i =>
      I.mul_mem_right _ (hdI i)
    have hx : ∀ i, (y i - (y i ^ 2 - algebraMap A B (s i)) * ↑(hyu i).unit⁻¹) ^ 2 =
        algebraMap A B (s i) := by
      intro i
      have h1 : (2 * y i) * ↑(hyu i).unit⁻¹ = 1 := (hyu i).mul_val_inv
      have h0 := hsq _ _ (hεI i) (hεI i)
      linear_combination h0 - (y i ^ 2 - algebraMap A B (s i)) * h1
    refine ⟨sqrtLift s _ hx, ?_⟩
    apply sqrtAlg_hom_ext
    intro i
    rw [AlgHom.comp_apply, sqrtLift_root, Ideal.Quotient.mkₐ_eq_mk, map_sub, hy,
      Ideal.Quotient.eq_zero_iff_mem.2 (hεI i), sub_zero]

theorem sqrtAlg_finitePresentation [Finite ι] : Algebra.FinitePresentation A (SqrtAlg s) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

/-- **Étaleness.** `SqrtAlg s` is étale over A if 2 and all s_i are units. -/
theorem sqrtAlg_etale [Finite ι] (h2 : IsUnit (2 : A)) (hs : ∀ i, IsUnit (s i)) :
    Algebra.Etale A (SqrtAlg s) where
  formallyEtale := sqrtAlg_formallyEtale h2 hs
  finitePresentation := sqrtAlg_finitePresentation

end Etale

end SqrtAlg

end BPFixedPoints
