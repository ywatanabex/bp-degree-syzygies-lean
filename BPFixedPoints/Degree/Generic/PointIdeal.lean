import BPFixedPoints.Degree.Lift.Taylor

/-!
# Ideal of a finite set of simple zeros

For a square polynomial system h over an algebraically closed field Ω,
assume its zero locus is the finite set S and the Jacobian determinant
is nonzero on S. Every polynomial vanishing on S belongs to J=(h), so J
is the radical, zero-dimensional vanishing ideal of S.
Nullstellensatz and Noetherianity give (product_{y∈S} m_y)^N⊆J.
At a simple zero, first-order Taylor expansion gives m_y⊆J+m_y²,
and iteration gives m_y⊆J+m_y^N. Distinct maximal-ideal powers are
coprime, so their images in R/J have zero intersection and product.
-/

namespace BPFixedPoints.BP

set_option linter.unusedSectionVars false

open MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {Ω : Type*} [Field Ω]

/-- Kernel of evaluation at y, the maximal ideal m_y. -/
noncomputable abbrev ptIdeal (y : σ → Ω) : Ideal (MvPolynomial σ Ω) := RingHom.ker (eval y)

theorem mem_ptIdeal {y : σ → Ω} {p : MvPolynomial σ Ω} : p ∈ ptIdeal y ↔ eval y p = 0 :=
  RingHom.mem_ker

theorem ptIdeal_isMaximal (y : σ → Ω) : (ptIdeal y).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C a⟩

theorem X_sub_C_mem_ptIdeal (y : σ → Ω) (j : σ) : X j - C (y j) ∈ ptIdeal y := by
  simp

theorem ptIdeal_injective : Function.Injective (ptIdeal (σ := σ) (Ω := Ω)) := by
  intro y y' h
  funext j
  have := X_sub_C_mem_ptIdeal y' j
  rw [← h, mem_ptIdeal] at this
  simpa [sub_eq_zero] using this

/-- First-order Taylor expansion: p-p(y)-sum_j ∂_j p(y)(X_j-y_j) belongs to m_y². -/
theorem taylor_mem_ptIdeal_sq (y : σ → Ω) (p : MvPolynomial σ Ω) :
    p - C (eval y p) - ∑ j, C (eval y (pderiv j p)) * (X j - C (y j)) ∈ ptIdeal y ^ 2 := by
  let Cs : Ω →+* MvPolynomial σ Ω := C
  have ht := taylor_first_order (map Cs p) (fun j => C (y j)) (fun j => X j - C (y j))
  have h1 : ((fun j => C (y j)) + fun j => X j - C (y j)) = (X : σ → MvPolynomial σ Ω) := by
    funext j; simp
  have hev : ∀ q : MvPolynomial σ Ω, eval (fun j => C (y j)) (map Cs q) = C (eval y q) := by
    intro q
    rw [eval_map, eval, coe_eval₂Hom, eval₂_comp_left]
    rfl
  rw [h1, eval_map, eval₂_eta, hev] at ht
  simp only [pderiv_map, hev] at ht
  refine (Ideal.span_le.2 ?_) ht
  rintro _ ⟨⟨j, k⟩, rfl⟩
  rw [pow_two]
  exact Ideal.mul_mem_mul (X_sub_C_mem_ptIdeal y j) (X_sub_C_mem_ptIdeal y k)

/-- At a simple zero y, m_y⊆J+m_y². -/
theorem ptIdeal_le_sup_sq (h : σ → MvPolynomial σ Ω) (y : σ → Ω) (hy : ∀ i, eval y (h i) = 0)
    (hdet : (Matrix.of fun i j => eval y (pderiv j (h i))).det ≠ 0) :
    ptIdeal y ≤ Ideal.span (Set.range h) ⊔ ptIdeal y ^ 2 := by
  set I := Ideal.span (Set.range h) ⊔ ptIdeal y ^ 2 with hI
  have hlin : ∀ j, X j - C (y j) ∈ I := by
    let π := Ideal.Quotient.mk I
    let M : Matrix σ σ Ω := Matrix.of fun i j => eval y (pderiv j (h i))
    let v : σ → MvPolynomial σ Ω ⧸ I := fun j => π (X j - C (y j))
    have hMv : Matrix.mulVec (M.map (π.comp C)) v = 0 := by
      funext i
      have ht := taylor_mem_ptIdeal_sq y (h i)
      rw [hy i, map_zero, sub_zero] at ht
      have h1 : π (h i - ∑ j, C (eval y (pderiv j (h i))) * (X j - C (y j))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right ht)
      have h2 : π (h i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      rw [map_sub, h2, zero_sub, neg_eq_zero, map_sum] at h1
      simpa [Matrix.mulVec, dotProduct, M, v] using h1
    have hu : IsUnit (M.map (π.comp C)).det := by
      change IsUnit ((π.comp C).mapMatrix M).det
      rw [← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 hdet).map _
    have hv : v = 0 := by
      have h2 := congrArg (fun w => Matrix.mulVec (M.map (π.comp C))⁻¹ w) hMv
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h2
      exact h2
    intro j
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hv j)
  intro p hp
  have ht := taylor_mem_ptIdeal_sq y p
  rw [mem_ptIdeal.1 hp, map_zero, sub_zero] at ht
  have e : p = (p - ∑ j, C (eval y (pderiv j p)) * (X j - C (y j))) +
      ∑ j, C (eval y (pderiv j p)) * (X j - C (y j)) := by ring
  rw [e]
  exact I.add_mem (Ideal.mem_sup_right ht) (I.sum_mem fun j _ => I.mul_mem_left _ (hlin j))

/-- If m⊆J+m², then m⊆J+m^{n+1} for every n. -/
theorem le_sup_pow_of_le_sup_sq {R : Type*} [CommRing R] {J m : Ideal R} (h : m ≤ J ⊔ m ^ 2) :
    ∀ n : ℕ, m ≤ J ⊔ m ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := le_sup_pow_of_le_sup_sq h n
    have hstep : m ^ (n + 1) ≤ J ⊔ m ^ (n + 2) := by
      calc m ^ (n + 1) = m ^ n * m := pow_succ _ _
        _ ≤ m ^ n * (J ⊔ m ^ 2) := Ideal.mul_mono_right h
        _ = m ^ n * J ⊔ m ^ n * m ^ 2 := Ideal.mul_sup _ _ _
        _ ≤ J ⊔ m ^ (n + 2) := sup_le_sup Ideal.mul_le_right (by rw [← pow_add])
    calc m ≤ J ⊔ m ^ (n + 1) := ih
      _ ≤ J ⊔ (J ⊔ m ^ (n + 2)) := sup_le_sup_left hstep _
      _ = J ⊔ m ^ (n + 1 + 1) := by rw [← sup_assoc, sup_idem]

variable [IsAlgClosed Ω]

/--
Ideal of simple finite zeros: if all zeros of h lie in S and every point
of S is a zero with nonzero Jacobian determinant, every polynomial
vanishing on S belongs to the ideal generated by h.
-/
theorem mem_span_of_forall_eval_eq_zero (h : σ → MvPolynomial σ Ω) (S : Finset (σ → Ω))
    (hS : ∀ y, (∀ i, eval y (h i) = 0) → y ∈ S) (hSz : ∀ y ∈ S, ∀ i, eval y (h i) = 0)
    (hsimp : ∀ y ∈ S, (Matrix.of fun i j => eval y (pderiv j (h i))).det ≠ 0)
    {p : MvPolynomial σ Ω} (hp : ∀ y ∈ S, eval y p = 0) :
    p ∈ Ideal.span (Set.range h) := by
  classical
  set J := Ideal.span (Set.range h) with hJdef
  -- Nullstellensatz：∏ m_y ⊆ √J
  have hrad : ∏ y ∈ S, ptIdeal y ≤ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
    intro q hq
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have hxS : x ∈ S := hS x fun i => by
      have := (mem_zeroLocus_iff.1 hx) (h i) (Ideal.subset_span ⟨i, rfl⟩)
      simpa [coe_aeval_eq_eval] using this
    have := (Ideal.prod_le_inf.trans (Finset.inf_le hxS)) hq
    simpa [coe_aeval_eq_eval] using this
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hJ : ∏ y ∈ S, ptIdeal y ^ (N + 1) ≤ J := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN
  have hloc : ∀ y ∈ S, ptIdeal y ≤ J ⊔ ptIdeal y ^ (N + 1) := fun y hy =>
    le_sup_pow_of_le_sup_sq (ptIdeal_le_sup_sq h y (hSz y hy) (hsimp y hy)) N
  let π := Ideal.Quotient.mk J
  have hcop : (S : Set (σ → Ω)).Pairwise (Function.onFun IsCoprime fun y => (ptIdeal y ^ (N + 1)).map π) := by
    intro y _ y' _ hne
    have hc : IsCoprime (ptIdeal y) (ptIdeal y') := by
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne (ptIdeal_isMaximal y) (ptIdeal_isMaximal y')
        fun e => hne (ptIdeal_injective e)
    have hc' := hc.pow (m := N + 1) (n := N + 1)
    show IsCoprime _ _
    rw [Ideal.isCoprime_iff_sup_eq] at hc' ⊢
    rw [← Ideal.map_sup, hc', Ideal.map_top]
  have hprod : ∏ y ∈ S, (ptIdeal y ^ (N + 1)).map π = ⊥ := by
    have hmp : ∏ y ∈ S, (ptIdeal y ^ (N + 1)).map π = (∏ y ∈ S, ptIdeal y ^ (N + 1)).map π :=
      (map_prod (Ideal.mapHom π) (fun y => ptIdeal y ^ (N + 1)) S).symm
    rw [hmp, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact hJ hq
  have hpm : ∀ y ∈ S, π p ∈ (ptIdeal y ^ (N + 1)).map π := by
    intro y hy
    have hmem : p ∈ J ⊔ ptIdeal y ^ (N + 1) := hloc y hy (mem_ptIdeal.2 (hp y hy))
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add]
    exact Ideal.mem_map_of_mem π hb
  have hmem : π p ∈ ∏ y ∈ S, (ptIdeal y ^ (N + 1)).map π := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
    simp only [Submodule.mem_iInf]
    exact hpm
  rw [hprod, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hmem

end BPFixedPoints.BP
