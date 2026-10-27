import BPFixedPoints.StateSum.Parity

/-!
# Numerical state-sum table: θ(t,2i) and divisibility by (1−t)^{ν−1}

The paper's `thm:structure` realizes E₁ as the minimal-resolution Betti table
of the universal incidence ring, indexed by k=|S| and i=|S|−v(S), weighted by
∏_v φ(d_S(v)). Total Betti number is N=Q, alternating numerator is θ_G(t,2i),
and the Hilbert series is θ_G(t,2i)/(1−t)^{4m}=ω_G(t)/(1−t)^{3m+n}.
This module treats only the numerical state-sum table; it does not itself
identify internal Betti degrees or prove the Hilbert-series statement.

Define f₀=1, f₁=0, f_{d+2}=γf_{d+1}+f_d (`fGen`). At γ=2i,
f_d(2i)=(1−d)i^d (`fGen_two_I`). The handshake identity gives
θ_G(t,2i)=Σ_S(−t)^{|S|}∏_v(1−d_S(v)) (`thetaGen_two_I`); define its integer
form as `thetaTwoI`. This equals Σ_S(−1)^{|S|−v(S)}t^{|S|}∏_v φ(d_S(v))
and Σ_{i,k}(−1)^i β_{i,k}t^k (`thetaTwoI_eq_alternating`, `thetaTwoI_eq_betti`).
The total table sum is Q (`sum_betti_eq_Q`).

Since ∏_v(1−d_S(v)) is a polynomial of total degree ≤n in edge indicators,
`pow_one_sub_dvd_sum` gives divisibility by (1−t)^{m−n}, using
Σ_{S⊇U}(−t)^{|S|}=(−t)^{|U|}(1−t)^{m−|U|} on each monomial
(`one_sub_pow_dvd_thetaTwoI`). Exponents use truncated natural subtraction.
For connected ν≥1, m−n=ν−1 and `exists_omega` gives the paper's ω_G.
For a tree the natural-exponent quotient is one, unlike the paper's ω_G=1−t.
For connected ν≥2 the alternating sum is zero (`thetaTwoI_eval_one_eq_zero`).
Loops are allowed and count twice.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Polynomial

/-! ### Local coefficients for general γ -/

section FGen

variable {R : Type*} [CommRing R]

/-- Local θ(·,γ) coefficients: f₀=1, f₁=0, f_{d+2}=γ f_{d+1}+f_d. -/
def fGen (γ : R) : ℕ → R
  | 0 => 1
  | 1 => 0
  | d + 2 => γ * fGen γ (d + 1) + fGen γ d

@[simp] theorem fGen_zero (γ : R) : fGen γ 0 = 1 := rfl
@[simp] theorem fGen_one (γ : R) : fGen γ 1 = 0 := rfl
theorem fGen_add_two (γ : R) (d : ℕ) : fGen γ (d + 2) = γ * fGen γ (d + 1) + fGen γ d := rfl

/-- At γ=2 these agree with the integer sequence f₂. -/
theorem fGen_two (d : ℕ) : fGen (2 : ℤ) d = (f2 d : ℤ) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp
    · simp
    · rw [fGen_add_two, ih (d + 1) (by omega), ih d (by omega), f2_add_two]
      push_cast; ring

/-- **f_d(2i) = (1 − d)·i^d。** -/
theorem fGen_two_I (d : ℕ) : fGen (2 * Complex.I) d = (1 - d) * Complex.I ^ d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp
    · simp
    · rw [fGen_add_two, ih (d + 1) (by omega), ih d (by omega)]
      push_cast
      linear_combination ((1 - (d : ℂ)) * Complex.I ^ d) * Complex.I_sq

end FGen

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- θ_G(t,γ) = Σ_S t^{|S|} ∏_v f_{d_S(v)}(γ) ∈ R[t]。 -/
noncomputable def thetaGen {R : Type*} [CommRing R] (γ : R) : R[X] :=
  ∑ S : Finset E, X ^ S.card * C (∏ v, fGen γ (G.deg S v))

/-- Handshake identity: Σ_v d_S(v)=2|S|, counting a loop twice. -/
theorem sum_deg (S : Finset E) : ∑ v, G.deg S v = 2 * S.card := by
  simp only [deg]
  rw [Finset.sum_comm]
  simp [G.sum_endCount, Finset.sum_const, mul_comm]

/-- Integer polynomial Σ_S(−t)^{|S|}∏_v(1−d_S(v)), equal to θ_G(t,2i). -/
noncomputable def thetaTwoI : ℤ[X] :=
  ∑ S : Finset E, (-X) ^ S.card * C (∏ v, (1 - (G.deg S v : ℤ)))

theorem prod_fGen_two_I (S : Finset E) :
    ∏ v, fGen (2 * Complex.I) (G.deg S v) = (-1) ^ S.card * ∏ v, (1 - (G.deg S v : ℂ)) := by
  simp only [fGen_two_I, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, G.sum_deg, pow_mul,
    Complex.I_sq]
  ring

/-- **θ_G(t,2i) = Σ_S (−t)^{|S|} ∏_v (1 − d_S(v))。** -/
theorem thetaGen_two_I :
    G.thetaGen (2 * Complex.I) = (G.thetaTwoI).map (Int.castRingHom ℂ) := by
  rw [thetaGen, thetaTwoI, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_fGen_two_I, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_X,
    Polynomial.map_C, neg_pow (X : ℂ[X]), C_mul, C_pow, C_neg, C_1]
  simp only [eq_intCast, Int.cast_prod, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  ring

/-! ### Betti table -/

/-- ∏_v (1 − d_S(v)) = (−1)^{v(S)} ∏_v φ(d_S(v))。 -/
theorem prod_one_sub_deg (S : Finset E) :
    ∏ v, (1 - (G.deg S v : ℤ)) = (-1) ^ (G.support S).card * (G.wt phi S : ℤ) := by
  rw [wt, Nat.cast_prod, support, Finset.card_filter, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rcases h : G.deg S v with _ | d
  · simp
  · simp

/-- A generalized loop satisfies v(S)≤|S|. -/
theorem card_support_le (S : Finset E) (hS : G.wt phi S ≠ 0) : (G.support S).card ≤ S.card := by
  have h2 : ∀ v ∈ G.support S, 2 ≤ G.deg S v := by
    intro v hv
    have hpos := (Finset.mem_filter.1 hv).2
    have hne : G.deg S v ≠ 1 := by
      intro h1
      apply hS
      rw [wt]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [h1]; rfl)
    omega
  have := Finset.sum_le_sum h2
  rw [Finset.sum_const, smul_eq_mul] at this
  have hle : ∑ v ∈ G.support S, G.deg S v ≤ ∑ v, G.deg S v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [G.sum_deg] at hle
  omega

/-- **Alternating numerator.** θ_G(t,2i)=Σ_S(−1)^{|S|−v(S)}t^{|S|}∏_v φ(d_S(v)). -/
theorem thetaTwoI_eq_alternating :
    G.thetaTwoI = ∑ S : Finset E,
      C ((-1) ^ (S.card - (G.support S).card) * (G.wt phi S : ℤ)) * X ^ S.card := by
  rw [thetaTwoI]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [G.prod_one_sub_deg, neg_pow (X : ℤ[X])]
  by_cases hS : G.wt phi S = 0
  · simp [hS]
  · have hle := G.card_support_le S hS
    have hp : ((-1 : ℤ) ^ S.card * (-1) ^ (G.support S).card) =
        (-1) ^ (S.card - (G.support S).card) := by
      rw [← pow_add]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, Nat.add_sub_cancel_left, show (G.support S).card + k + (G.support S).card =
        k + 2 * (G.support S).card by ring, pow_add, pow_mul]
      simp
    rw [← hp]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring

/-- Numerical state-sum table β_{i,k}=Σ_{|S|=k,|S|−v(S)=i}∏_v φ(d_S(v)). This definition does not include its identification with actual internally graded Betti numbers. -/
def betti (i k : ℕ) : ℕ :=
  ∑ S ∈ Finset.univ.filter fun S : Finset E => S.card = k ∧ S.card - (G.support S).card = i,
    G.wt phi S

/-- Rewrite the sum over Betti indices (i,k) as a sum over edge sets. -/
theorem sum_betti_index {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → Finset E → M) :
    ∑ i ∈ Finset.range (Fintype.card E + 1), ∑ k ∈ Finset.range (Fintype.card E + 1),
      ∑ S ∈ Finset.univ.filter (fun S : Finset E => S.card = k ∧ S.card - (G.support S).card = i),
        F i k S =
      ∑ S : Finset E, F (S.card - (G.support S).card) S.card S := by
  simp_rw [Finset.sum_filter]
  calc ∑ i ∈ Finset.range (Fintype.card E + 1), ∑ k ∈ Finset.range (Fintype.card E + 1),
        ∑ S : Finset E, (if S.card = k ∧ S.card - (G.support S).card = i then F i k S else 0)
      = ∑ i ∈ Finset.range (Fintype.card E + 1), ∑ S : Finset E,
          ∑ k ∈ Finset.range (Fintype.card E + 1),
            (if S.card = k ∧ S.card - (G.support S).card = i then F i k S else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ S : Finset E, ∑ i ∈ Finset.range (Fintype.card E + 1),
          ∑ k ∈ Finset.range (Fintype.card E + 1),
            (if S.card = k ∧ S.card - (G.support S).card = i then F i k S else 0) :=
        Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun S _ => ?_
      have hk : S.card ∈ Finset.range (Fintype.card E + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.card_le_univ S))
      have hi : S.card - (G.support S).card ∈ Finset.range (Fintype.card E + 1) := by
        rw [Finset.mem_range] at hk ⊢; omega
      rw [Finset.sum_eq_single_of_mem _ hi, Finset.sum_eq_single_of_mem _ hk]
      · simp
      · intro k _ hk'; simp [Ne.symm hk']
      · intro i _ hi'
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ite_eq_right]
        rintro ⟨-, h⟩
        exact hi' h.symm

/-- **The total Betti number is Q (=N).** -/
theorem sum_betti_eq_Q :
    ∑ i ∈ Finset.range (Fintype.card E + 1), ∑ k ∈ Finset.range (Fintype.card E + 1),
      G.betti i k = G.Q := by
  simp only [betti]
  rw [G.sum_betti_index fun _ _ S => G.wt phi S, Q, QOn, Finset.powerset_univ]

/-- **Betti expression for the alternating numerator.** θ_G(t,2i)=Σ_{i,k}(−1)^i β_{i,k}t^k. -/
theorem thetaTwoI_eq_betti :
    G.thetaTwoI = ∑ i ∈ Finset.range (Fintype.card E + 1), ∑ k ∈ Finset.range (Fintype.card E + 1),
      C ((-1) ^ i * (G.betti i k : ℤ)) * X ^ k := by
  rw [thetaTwoI_eq_alternating]
  simp only [betti, Nat.cast_sum, Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [G.sum_betti_index fun i k S => C ((-1) ^ i * (G.wt phi S : ℤ)) * X ^ k]

/-! ### Divisibility by (1−t)^{m−n} -/

section Divisibility

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Indicator function of an edge set. -/
def ind (S : Finset σ) : σ → ℤ := fun e => if e ∈ S then 1 else 0

/-- Σ_{S ⊇ U} a^{|S|} = a^{|U|}(1 + a)^{|σ| − |U|}。 -/
theorem sum_superset_pow (U : Finset σ) (a : ℤ[X]) :
    ∑ S : Finset σ, (if U ⊆ S then a ^ S.card else 0) =
      a ^ U.card * (a + 1) ^ (Fintype.card σ - U.card) := by
  classical
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter (fun S : Finset σ => U ⊆ S) =
      (Finset.univ \ U).powerset.image fun T => U ∪ T := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_powerset]
    constructor
    · intro h
      refine ⟨S \ U, Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl, ?_⟩
      exact Finset.union_sdiff_of_subset h
    · rintro ⟨T, -, rfl⟩
      exact Finset.subset_union_left
  rw [himg, Finset.sum_image]
  · have hcard : ∀ T ∈ (Finset.univ \ U).powerset, (U ∪ T).card = U.card + T.card := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      exact Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hT Finset.disjoint_sdiff)
    rw [Finset.sum_congr rfl fun T hT => by rw [hcard T hT, pow_add], ← Finset.mul_sum]
    congr 1
    have := Finset.sum_pow_mul_eq_add_pow a 1 (Finset.univ \ U)
    simp only [one_pow, mul_one] at this
    rw [this, Finset.card_univ_sdiff]
  · intro T hT T' hT' h
    have h' : U ∪ T = U ∪ T' := h
    rw [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hT hT'
    have h1 : T = (U ∪ T) \ U := by
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint]
      exact Finset.disjoint_of_subset_left hT (Finset.sdiff_disjoint)
    have h2 : T' = (U ∪ T') \ U := by
      rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint]
      exact Finset.disjoint_of_subset_left hT' (Finset.sdiff_disjoint)
    rw [h1, h2, h']

theorem eval_ind_monomial (S : Finset σ) (α : σ →₀ ℕ) (a : ℤ) :
    MvPolynomial.eval (ind S) (MvPolynomial.monomial α a) = if α.support ⊆ S then a else 0 := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod]
  split_ifs with h
  · rw [Finset.prod_eq_one, mul_one]
    intro e he
    simp [ind, h he]
  · obtain ⟨e, he, heS⟩ := Finset.not_subset.1 h
    rw [Finset.prod_eq_zero he, mul_zero]
    simp [ind, heS, zero_pow (Finsupp.mem_support_iff.1 he)]

theorem card_support_le_sum (α : σ →₀ ℕ) : α.support.card ≤ α.sum fun _ e => e := by
  rw [Finsupp.sum, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun e he => Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 he)

/-- **Divisibility lemma.** If P has total degree ≤k, then (1−t)^{|σ|−k} divides Σ_S(−t)^{|S|}P(1_S). -/
theorem one_sub_pow_dvd_sum (P : MvPolynomial σ ℤ) {k : ℕ} (hk : P.totalDegree ≤ k) :
    (1 - X : ℤ[X]) ^ (Fintype.card σ - k) ∣
      ∑ S : Finset σ, (-X) ^ S.card * C (MvPolynomial.eval (ind S) P) := by
  classical
  have hP : ∀ S : Finset σ, MvPolynomial.eval (ind S) P =
      ∑ α ∈ P.support, if α.support ⊆ S then P.coeff α else 0 := by
    intro S
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    simp only [eval_ind_monomial]
  simp_rw [hP, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun α hα => ?_
  have h1 : ∑ S : Finset σ, (-X) ^ S.card * C (if α.support ⊆ S then P.coeff α else 0) =
      C (P.coeff α) * ∑ S : Finset σ, (if α.support ⊆ S then (-X : ℤ[X]) ^ S.card else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [h1, sum_superset_pow]
  have hsupp : α.support.card ≤ k :=
    (card_support_le_sum α).trans ((MvPolynomial.le_totalDegree hα).trans hk)
  apply Dvd.dvd.mul_left
  apply Dvd.dvd.mul_left
  rw [neg_add_eq_sub]
  exact pow_dvd_pow _ (by omega)

end Divisibility

/-- Write ∏_v(1−d_S(v)) as a polynomial in edge indicators: ∏_v(1−Σ_e c_{e,v}x_e). -/
noncomputable def degPoly : MvPolynomial E ℤ :=
  ∏ v, (1 - ∑ e, MvPolynomial.C (G.endCount e v : ℤ) * MvPolynomial.X e)

theorem eval_degPoly (S : Finset E) :
    MvPolynomial.eval (ind S) G.degPoly = ∏ v, (1 - (G.deg S v : ℤ)) := by
  simp only [degPoly, map_prod, map_sub, map_one, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, ind, mul_ite, mul_one, mul_zero, deg, Nat.cast_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem totalDegree_degPoly : G.degPoly.totalDegree ≤ Fintype.card V := by
  calc G.degPoly.totalDegree
      ≤ ∑ v, (1 - ∑ e, MvPolynomial.C (G.endCount e v : ℤ) * MvPolynomial.X e).totalDegree :=
        by unfold degPoly; exact MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _v : V, 1 := by
        refine Finset.sum_le_sum fun v _ => ?_
        refine (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ?_)
        refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun e _ => ?_)
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    _ = Fintype.card V := by simp

/-- **(1−t)^{m−n} ∣ θ_G(t,2i)**（m = |E|、n = |V|）。 -/
theorem one_sub_pow_dvd_thetaTwoI :
    (1 - X : ℤ[X]) ^ (Fintype.card E - Fintype.card V) ∣ G.thetaTwoI := by
  have := one_sub_pow_dvd_sum G.degPoly G.totalDegree_degPoly
  simpa only [thetaTwoI, eval_degPoly] using this

/-- For connected G a quotient of θ_G(t,2i) by the natural exponent ν−1 exists. It is the paper's ω_G for ν≥1; for a tree it is one, whereas the paper's ω_G=1−t. -/
theorem exists_omega (hc : G.Connected) :
    ∃ ω : ℤ[X], G.thetaTwoI = (1 - X) ^ (G.cycleRank - 1) * ω := by
  have h := G.one_sub_pow_dvd_thetaTwoI
  have hle := G.card_vertex_le_of_connected hc
  have : G.cycleRank - 1 = Fintype.card E - Fintype.card V := by unfold cycleRank; omega
  rw [this]
  exact h


/-- Coefficient formula: [t^k]θ_G(t,2i)=(−1)^k Σ_{|S|=k}∏_v(1−d_S(v)). -/
theorem coeff_thetaTwoI (k : ℕ) :
    G.thetaTwoI.coeff k =
      (-1) ^ k * ∑ S ∈ Finset.univ.filter (fun S : Finset E => S.card = k),
        ∏ v, (1 - (G.deg S v : ℤ)) := by
  rw [thetaTwoI, finsetSum_coeff, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [neg_pow (X : ℤ[X]), mul_assoc, mul_comm (X ^ S.card) _, ← mul_assoc,
    show ((-1 : ℤ[X]) ^ S.card) = C ((-1) ^ S.card) by simp, ← C_mul, coeff_C_mul_X_pow]
  split_ifs with h1 h2 h2
  · subst h1; ring
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- Uniqueness of ω_G: cancellation of (1−t)^k gives a unique quotient. -/
theorem omega_unique {k : ℕ} {ω₁ ω₂ : ℤ[X]} (h₁ : G.thetaTwoI = (1 - X) ^ k * ω₁)
    (h₂ : G.thetaTwoI = (1 - X) ^ k * ω₂) : ω₁ = ω₂ := by
  have hne : (1 - X : ℤ[X]) ^ k ≠ 0 := pow_ne_zero _ (by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this)
  exact mul_left_cancel₀ hne (h₁.symm.trans h₂)

/-- For a connected graph with ν≥2 (m>n), the alternating Betti sum θ_G(1,2i) is zero. -/
theorem thetaTwoI_eval_one_eq_zero (h : Fintype.card V < Fintype.card E) :
    G.thetaTwoI.eval 1 = 0 := by
  obtain ⟨q, hq⟩ := G.one_sub_pow_dvd_thetaTwoI
  rw [hq, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self,
    zero_pow (by omega), zero_mul]


end Multigraph

end BPFixedPoints
