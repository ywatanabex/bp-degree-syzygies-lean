import BPFixedPoints.Incidence.Betti
import BPFixedPoints.StateSum.Rate

/-!
# The special value θ_G(1,γ) for general γ (`alg:theta-special-value`)

For a connected multigraph G with cycle rank ν and every γ,
θ_G(1,γ)=Σ_{k=0}^{ν}C(ν,k)f_{2k}(γ)=(ξ+ξ⁻¹)^{ν−1}(ξ^{ν−1}+ξ^{1−ν}), γ=ξ−ξ⁻¹.
Here θ_G(t,γ) is `Multigraph.thetaGen` and f_d(γ) is `fGen` (f₀=1, f₁=0,
f_{d+2}=γf_{d+1}+f_d), both from `Incidence/Betti.lean`; the value at t=1 is
`Polynomial.eval 1`.

Proved here:

* `fGen_local`: f_{a+1}f_{b+1}+f_af_b=f_{a+b} over any commutative ring. It gives the
  t=1 contraction invariance θ_A(1,γ)=θ_{A−e}^{G/e}(1,γ) for a nonloop edge e
  (`Multigraph.thetaGenOn_eq_contractMap`), the general-γ form of
  `thetaOn_eq_contractMap`.
* The first equality (`Multigraph.thetaGen_eval_one_of_connected`), over any
  commutative ring, by contracting nonloop edges down to a bouquet as in
  `connectedOn_bounds`.
* The closed form of f_d: (1+ξ²)f_d(ξ−ξ')=ξ^d+(−1)^dξ²ξ'^d whenever ξξ'=1, over
  any commutative ring (`one_add_sq_mul_fGen`), and
  f_d(ξ−ξ⁻¹)=(ξ^d+(−1)^dξ^{2−d})/(1+ξ²) in a field when ξ≠0 and 1+ξ²≠0
  (`fGen_sub_inv`).
* The second equality: Σ_kC(n+1,k)f_{2k}(ξ−ξ')=(ξ+ξ')^n(ξ^n+ξ'^n) whenever ξξ'=1,
  over any commutative ring and with no condition on 1+ξ² (`bouquetThetaGen_succ`),
  and the paper's zpow form for every ν≥0 in a field when ξ≠0 and 1+ξ²≠0
  (`bouquetThetaGen_sub_inv`). The graph statements are
  `Multigraph.thetaGen_eval_one_of_connected_of_mul_eq_one` (ν≥1, any commutative
  ring) and `Multigraph.thetaGen_eval_one_of_connected_sub_inv` (every ν, field).
  The proof does not use the closed form of f_d and the binomial theorem, as the
  paper does: it checks the second-order recurrence b_{n+2}=(γ²+4)(b_{n+1}−b_n)
  of the binomial transform b_n=Σ_kC(n,k)f_{2k}(γ) (`binomTransform_add_two`).
* γ=2: θ_G(1,2) of `thetaGen` is the natural number `theta`
  (`Multigraph.thetaGen_two_eval_one`); ξ=1+√2 gives
  θ_G(1,2)=(4+2√2)^{ν−1}+(4−2√2)^{ν−1} for connected G
  (`Multigraph.theta_eq_lam_mu_zpow_of_connected`), and with `U_eq` this recovers
  `theta_eq_U_of_connected` (`Multigraph.theta_eq_U_of_connected_of_special_value`)
  without `bouquetTheta_eq_U`.

Hypotheses as in the Lean definitions: `Multigraph.Connected` (a nonempty vertex type,
every two vertices joined by edges); loops and parallel edges are allowed, a loop counting
twice in the degree; pendant edges need no hypothesis. ν is `cycleRank`, |E|+1−|V| with
truncated subtraction; a connected graph has |V|≤|E|+1 (`card_vertex_le_of_connected`).

Not proved here: the polynomial deletion–contraction formula
θ_G(t,γ)=(1−t)θ_{G−e}(t,γ)+tθ_{G/e}(t,γ) for general γ (only its value at t=1 is used;
the γ=2 case is `thetaPolyOn_deletion_contraction`). The paper's citation of
Watanabe's Lemma 4.2 is a literature reference and is not formalized; the statement is
proved here directly.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Finset Polynomial

/-! ### The local identity and the bouquet sum -/

section Local

variable {R : Type*} [CommRing R]

/-- **Local identity.** f_{a+1}(γ)f_{b+1}(γ)+f_a(γ)f_b(γ)=f_{a+b}(γ) for every γ in a
commutative ring: the general-γ form of `f2_local`, giving pure contraction invariance of
θ(1,γ). -/
theorem fGen_local (γ : R) (a b : ℕ) :
    fGen γ (a + 1) * fGen γ (b + 1) + fGen γ a * fGen γ b = fGen γ (a + b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases a with _ | _ | a
    · simp
    · rw [Nat.add_comm 1 b]
      simp [fGen_add_two]
    · have h1 : fGen γ (a + 2) * fGen γ (b + 1) + fGen γ (a + 1) * fGen γ b =
          fGen γ (a + b + 1) := by
        have := ih (a + 1) (by omega) b
        rwa [show a + 1 + b = a + b + 1 by omega] at this
      have h0 := ih a (by omega) b
      have e2 := fGen_add_two γ a
      show fGen γ (a + 1 + 2) * fGen γ (b + 1) + fGen γ (a + 2) * fGen γ b = fGen γ (a + 2 + b)
      rw [show a + 2 + b = (a + b) + 2 by omega, fGen_add_two γ (a + 1), fGen_add_two γ (a + b)]
      linear_combination γ * h1 + h0 + fGen γ b * e2

/-- At γ=2 the coefficients f_d(2) in any commutative ring are the casts of the natural
numbers `f2 d`; `fGen_two` is the case of ℤ. -/
theorem fGen_two_eq_f2 (d : ℕ) : fGen (2 : R) d = (f2 d : R) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp
    · simp
    · rw [fGen_add_two, ih (d + 1) (by omega), ih d (by omega), f2_add_two]
      push_cast; ring

/-- Bouquet value Σ_{k≤r}C(r,k)f_{2k}(γ): θ(1,γ) of a bouquet of r loops at one vertex,
the general-γ form of `bouquetTheta`. -/
def bouquetThetaGen (γ : R) (r : ℕ) : R :=
  ∑ k ∈ range (r + 1), (r.choose k : R) * fGen γ (2 * k)

end Local

/-! ### Closed forms -/

section ClosedForm

variable {R : Type*} [CommRing R]

/-- **Closed form of f_d, cleared of denominators.** If ξξ'=1 then
(1+ξ²)f_d(ξ−ξ')=ξ^d+(−1)^dξ²ξ'^d, in any commutative ring. -/
theorem one_add_sq_mul_fGen {ξ ξ' : R} (h : ξ * ξ' = 1) (d : ℕ) :
    (1 + ξ ^ 2) * fGen (ξ - ξ') d = ξ ^ d + (-1) ^ d * ξ ^ 2 * ξ' ^ d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp
    · show (1 + ξ ^ 2) * fGen (ξ - ξ') 1 = ξ ^ 1 + (-1) ^ 1 * ξ ^ 2 * ξ' ^ 1
      rw [fGen_one]
      linear_combination ξ * h
    · rw [fGen_add_two]
      have h1 := ih (d + 1) (by omega)
      have h0 := ih d (by omega)
      linear_combination (ξ - ξ') * h1 + h0 + (-ξ ^ d - (-1) ^ d * ξ ^ 2 * ξ' ^ d) * h

/-- **Closed form of f_d.** In a field, if ξ≠0 and 1+ξ²≠0, then
f_d(ξ−ξ⁻¹)=(ξ^d+(−1)^dξ^{2−d})/(1+ξ²). -/
theorem fGen_sub_inv {K : Type*} [Field K] {ξ : K} (hξ : ξ ≠ 0) (h1 : 1 + ξ ^ 2 ≠ 0) (d : ℕ) :
    fGen (ξ - ξ⁻¹) d = (ξ ^ d + (-1) ^ d * ξ ^ (2 - (d : ℤ))) / (1 + ξ ^ 2) := by
  rw [eq_div_iff h1, mul_comm, one_add_sq_mul_fGen (mul_inv_cancel₀ hξ), zpow_sub₀ hξ,
    zpow_natCast, zpow_ofNat, div_eq_mul_inv, inv_pow]
  ring

/-- Even-index recurrence f_{2k+4}=(γ²+2)f_{2k+2}−f_{2k}, eliminating odd indices; at γ=2
this is `f2Even_add_two`. -/
theorem fGen_two_mul_add_two (γ : R) (k : ℕ) :
    fGen γ (2 * (k + 2)) = (γ ^ 2 + 2) * fGen γ (2 * (k + 1)) - fGen γ (2 * k) := by
  have h1 : fGen γ (2 * k + 4) = γ * fGen γ (2 * k + 3) + fGen γ (2 * k + 2) :=
    fGen_add_two γ (2 * k + 2)
  have h2 : fGen γ (2 * k + 3) = γ * fGen γ (2 * k + 2) + fGen γ (2 * k + 1) :=
    fGen_add_two γ (2 * k + 1)
  have h3 : fGen γ (2 * k + 2) = γ * fGen γ (2 * k + 1) + fGen γ (2 * k) := fGen_add_two γ (2 * k)
  rw [show 2 * (k + 2) = 2 * k + 4 by ring, show 2 * (k + 1) = 2 * k + 2 by ring]
  linear_combination h1 + γ * h2 - h3

/-- Binomial transform Σ_{k≤n}C(n,k)a_k of a sequence in a commutative ring; `binom` is the
integer case. -/
def binomTransform (a : ℕ → R) (n : ℕ) : R := ∑ k ∈ range (n + 1), (n.choose k : R) * a k

/-- Pascal step of the binomial transform: b_{n+1}=b_n+Σ_kC(n,k)a_{k+1}. -/
theorem binomTransform_succ (a : ℕ → R) (n : ℕ) :
    binomTransform a (n + 1) = binomTransform a n + binomTransform (fun k => a (k + 1)) n := by
  unfold binomTransform
  exact Finset.sum_choose_succ_mul (fun i _ => a i) n

/-- If a_{k+2}=p a_{k+1}−a_k, the binomial transform satisfies
b_{n+2}=(p+2)(b_{n+1}−b_n); at p=6 this is `binom_f2Even_add_two`. -/
theorem binomTransform_add_two {a : ℕ → R} {p : R} (ha : ∀ k, a (k + 2) = p * a (k + 1) - a k)
    (n : ℕ) :
    binomTransform a (n + 2) = (p + 2) * (binomTransform a (n + 1) - binomTransform a n) := by
  have h1 := binomTransform_succ a n
  have h2 := binomTransform_succ a (n + 1)
  have h3 := binomTransform_succ (fun k => a (k + 1)) n
  have h4 : binomTransform (fun k => a (k + 1 + 1)) n =
      p * binomTransform (fun k => a (k + 1)) n - binomTransform a n := by
    simp only [binomTransform, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha k]
    ring
  linear_combination h2 + h3 + h4 - (p + 1) * h1

theorem bouquetThetaGen_eq_binomTransform (γ : R) (n : ℕ) :
    bouquetThetaGen γ n = binomTransform (fun k => fGen γ (2 * k)) n := rfl

/-- **Second equality, ν=n+1≥1.** If ξξ'=1 then
Σ_{k≤n+1}C(n+1,k)f_{2k}(ξ−ξ')=(ξ+ξ')^n(ξ^n+ξ'^n), in any commutative ring and without
any condition on 1+ξ². -/
theorem bouquetThetaGen_succ {ξ ξ' : R} (h : ξ * ξ' = 1) (n : ℕ) :
    bouquetThetaGen (ξ - ξ') (n + 1) = (ξ + ξ') ^ n * (ξ ^ n + ξ' ^ n) := by
  have hrec : ∀ m, bouquetThetaGen (ξ - ξ') (m + 2) =
      (ξ + ξ') ^ 2 * (bouquetThetaGen (ξ - ξ') (m + 1) - bouquetThetaGen (ξ - ξ') m) := by
    intro m
    simp only [bouquetThetaGen_eq_binomTransform]
    rw [binomTransform_add_two (p := (ξ - ξ') ^ 2 + 2) (fun k => fGen_two_mul_add_two _ k)]
    linear_combination (-4 : R) * h *
      (binomTransform (fun k => fGen (ξ - ξ') (2 * k)) (m + 1) -
        binomTransform (fun k => fGen (ξ - ξ') (2 * k)) m)
  induction n using Nat.twoStepInduction with
  | zero => simp [bouquetThetaGen, Finset.sum_range_succ, fGen_add_two]
  | one =>
    simp [bouquetThetaGen, Finset.sum_range_succ, fGen_add_two]
    linear_combination (-4 : R) * h
  | more n ih0 ih1 =>
    rw [show n + 2 + 1 = (n + 1) + 2 by ring, hrec, ih1, ih0]
    linear_combination ((ξ + ξ') ^ (n + 2) * (ξ ^ n + ξ' ^ n)) * h

/-- **Second equality for ν≥1.** If ξξ'=1 and 1≤ν then
Σ_{k≤ν}C(ν,k)f_{2k}(ξ−ξ')=(ξ+ξ')^{ν−1}(ξ^{ν−1}+ξ'^{ν−1}), in any commutative ring. -/
theorem bouquetThetaGen_of_one_le {ξ ξ' : R} (h : ξ * ξ' = 1) {ν : ℕ} (hν : 1 ≤ ν) :
    bouquetThetaGen (ξ - ξ') ν = (ξ + ξ') ^ (ν - 1) * (ξ ^ (ν - 1) + ξ' ^ (ν - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
  rw [bouquetThetaGen_succ h, Nat.add_sub_cancel]

/-- **Second equality, field form.** In a field, if ξ≠0 and 1+ξ²≠0, then for every ν≥0
Σ_{k≤ν}C(ν,k)f_{2k}(ξ−ξ⁻¹)=(ξ+ξ⁻¹)^{ν−1}(ξ^{ν−1}+ξ^{1−ν}) with integer exponents; the case
ν=0 is where 1+ξ²≠0 is needed. -/
theorem bouquetThetaGen_sub_inv {K : Type*} [Field K] {ξ : K} (hξ : ξ ≠ 0) (h1 : 1 + ξ ^ 2 ≠ 0)
    (ν : ℕ) :
    bouquetThetaGen (ξ - ξ⁻¹) ν =
      (ξ + ξ⁻¹) ^ ((ν : ℤ) - 1) * (ξ ^ ((ν : ℤ) - 1) + ξ ^ (1 - (ν : ℤ))) := by
  rcases ν with _ | n
  · have hs : ξ + ξ⁻¹ ≠ 0 := by
      intro hs
      apply h1
      have : ξ * (ξ + ξ⁻¹) = 1 + ξ ^ 2 := by field_simp; ring
      rw [← this, hs, mul_zero]
    rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, show (1 : ℤ) - ((0 : ℕ) : ℤ) = 1 by norm_num,
      zpow_neg_one, zpow_neg_one, zpow_one, add_comm ξ⁻¹ ξ, inv_mul_cancel₀ hs]
    simp [bouquetThetaGen]
  · rw [bouquetThetaGen_succ (mul_inv_cancel₀ hξ),
      show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring,
      show (1 : ℤ) - ((n + 1 : ℕ) : ℤ) = -(n : ℤ) by push_cast; ring,
      zpow_natCast, zpow_natCast, zpow_neg, zpow_natCast, inv_pow]

end ClosedForm

/-! ### Graphs -/

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] {R : Type*} [CommRing R]

/-- θ_A(1,γ)=Σ_{S⊆A}∏_v f_{d_S(v)}(γ) for the subgraph with edge set A, with values in a
commutative ring; at γ=2 its natural-number analogue is `thetaOn`. -/
def thetaGenOn (G : Multigraph V E) (γ : R) (A : Finset E) : R :=
  ∑ S ∈ A.powerset, ∏ v, fGen γ (G.deg S v)

section Contract

variable [DecidableEq E] {G : Multigraph V E} {e : E}

/-- For a nonloop edge e∉T, the states T and T∪{e} together carry the contracted weight:
∏_v f_{d_T(v)}+∏_v f_{d_{T∪e}(v)}=∏_v f_{d^{G/e}_T(v)}. General-γ form of `wt_f2_pair`. -/
theorem prod_fGen_pair (he : G.fst e ≠ G.snd e) (γ : R) {T : Finset E} (hT : e ∉ T) :
    ∏ v, fGen γ (G.deg T v) + ∏ v, fGen γ (G.deg (insert e T) v) =
      ∏ v, fGen γ ((G.contractMap e).deg T v) := by
  have split : ∀ g : V → R,
      ∏ v, g v = g (G.fst e) * g (G.snd e) * ∏ v ∈ (univ.erase (G.fst e)).erase (G.snd e), g v := by
    intro g
    rw [← Finset.mul_prod_erase univ g (mem_univ (G.fst e)),
      ← Finset.mul_prod_erase (univ.erase (G.fst e)) g
        (mem_erase.2 ⟨he.symm, mem_univ (G.snd e)⟩), mul_assoc]
  have hrest1 : ∏ v ∈ (univ.erase (G.fst e)).erase (G.snd e), fGen γ (G.deg (insert e T) v) =
      ∏ v ∈ (univ.erase (G.fst e)).erase (G.snd e), fGen γ (G.deg T v) :=
    prod_congr rfl fun v hv => by
      rw [mem_erase, mem_erase] at hv
      rw [G.deg_insert hT, G.endCount_of_ne_ne (Ne.symm hv.2.1) (Ne.symm hv.1), add_zero]
  have hrest2 :
      ∏ v ∈ (univ.erase (G.fst e)).erase (G.snd e), fGen γ ((G.contractMap e).deg T v) =
        ∏ v ∈ (univ.erase (G.fst e)).erase (G.snd e), fGen γ (G.deg T v) :=
    prod_congr rfl fun v hv => by
      rw [mem_erase, mem_erase] at hv
      rw [contractMap_deg_of_ne T hv.2.1 hv.1]
  rw [split, split, split (fun v => fGen γ ((G.contractMap e).deg T v)), hrest1, hrest2,
    G.deg_insert hT, G.deg_insert hT, G.endCount_fst_of_ne he, G.endCount_snd_of_ne he,
    contractMap_deg_fst he, contractMap_deg_snd he, fGen_zero,
    ← fGen_local γ (G.deg T (G.fst e)) (G.deg T (G.snd e))]
  ring

/-- **Contraction invariance at t=1.** For a nonloop edge e∈A,
θ_A(1,γ)=θ^{G/e}_{A−e}(1,γ): the t=1 case of deletion–contraction, for every γ. -/
theorem thetaGenOn_eq_contractMap {A : Finset E} (he : G.fst e ≠ G.snd e) (hA : e ∈ A) (γ : R) :
    G.thetaGenOn γ A = (G.contractMap e).thetaGenOn γ (A.erase e) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase e A)
    (fun S => ∏ v, fGen γ (G.deg S v))
  rw [Finset.insert_erase hA] at h
  unfold thetaGenOn
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_powerset] at hT
  exact prod_fGen_pair he γ fun h => Finset.notMem_erase e A (hT h)

end Contract

/-- If every edge of A is a loop at v₀, θ_A(1,γ)=Σ_kC(|A|,k)f_{2k}(γ). -/
theorem thetaGenOn_of_isBouquetAt {G : Multigraph V E} {A : Finset E} {v₀ : V}
    (hB : G.IsBouquetAt A v₀) (γ : R) : G.thetaGenOn γ A = bouquetThetaGen γ A.card := by
  unfold thetaGenOn bouquetThetaGen
  have hS : ∀ S ∈ A.powerset, ∏ v, fGen γ (G.deg S v) = fGen γ (2 * S.card) := by
    intro S hS
    rw [Fintype.prod_eq_single v₀]
    · simp [deg_of_isBouquetAt hB (mem_powerset.1 hS)]
    · intro w hw
      simp [deg_of_isBouquetAt hB (mem_powerset.1 hS), hw]
  rw [Finset.sum_congr rfl hS, Finset.sum_powerset_apply_card (fun k => fGen γ (2 * k))]
  simp [nsmul_eq_mul]

/-- Induction for connected subgraphs on W and A: θ_A(1,γ)=Σ_kC(ν,k)f_{2k}(γ) with
ν=|A|+1−|W|. General-γ form of the θ part of `connectedOn_bounds`. -/
theorem thetaGenOn_of_connectedOn [DecidableEq E] (γ : R) :
    ∀ (n : ℕ) (G : Multigraph V E) (A : Finset E) (W : Finset V), W.card = n →
      G.ConnectedOn A W → G.thetaGenOn γ A = bouquetThetaGen γ (A.card + 1 - W.card) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G A W hn hc
  rcases Nat.lt_or_ge 1 W.card with hW | hW
  · obtain ⟨e, he, hne⟩ := G.exists_nonloop_of_connectedOn hc hW
    have hc' := connectedOn_contractMap hc he hne
    have hv : G.snd e ∈ W := (hc.2.1 e he).2
    have hcard : (W.erase (G.snd e)).card = W.card - 1 := Finset.card_erase_of_mem hv
    have hAcard : (A.erase e).card = A.card - 1 := Finset.card_erase_of_mem he
    have hA1 : 0 < A.card := Finset.card_pos.2 ⟨e, he⟩
    have h3 := ih (W.card - 1) (by omega) (G.contractMap e) (A.erase e) (W.erase (G.snd e))
      hcard hc'
    rw [hcard, hAcard, show A.card - 1 + 1 - (W.card - 1) = A.card + 1 - W.card by omega] at h3
    rw [thetaGenOn_eq_contractMap hne he, h3]
  · have hW1 : W.card = 1 := by have := hc.1.card_pos; omega
    obtain ⟨w₀, rfl⟩ := Finset.card_eq_one.1 hW1
    have hB : G.IsBouquetAt A w₀ := fun e he => by
      have := hc.2.1 e he
      simp only [Finset.mem_singleton] at this
      exact this
    rw [thetaGenOn_of_isBouquetAt hB]
    simp

variable [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- θ_G(1,γ), the value of `thetaGen` at t=1, is `thetaGenOn` on the whole edge set. -/
theorem thetaGen_eval_one (γ : R) : (G.thetaGen γ).eval 1 = G.thetaGenOn γ univ := by
  simp [thetaGen, thetaGenOn, eval_finsetSum, eval_prod]

/-- **`alg:theta-special-value`, first equality.** For a connected multigraph (loops and
parallel edges allowed, a loop counting twice) and every γ in a commutative ring,
θ_G(1,γ)=Σ_{k=0}^{ν}C(ν,k)f_{2k}(γ), ν=`cycleRank`. -/
theorem thetaGen_eval_one_of_connected (hc : G.Connected) (γ : R) :
    (G.thetaGen γ).eval 1 =
      ∑ k ∈ range (G.cycleRank + 1), (G.cycleRank.choose k : R) * fGen γ (2 * k) := by
  rw [thetaGen_eval_one]
  have := thetaGenOn_of_connectedOn γ _ G univ univ rfl hc
  simpa [cycleRank, bouquetThetaGen] using this

/-- **`alg:theta-special-value`, both equalities, ν≥1.** For a connected multigraph with
cycle rank ν≥1 and ξξ'=1 in a commutative ring,
θ_G(1,ξ−ξ')=(ξ+ξ')^{ν−1}(ξ^{ν−1}+ξ'^{ν−1}). -/
theorem thetaGen_eval_one_of_connected_of_mul_eq_one (hc : G.Connected) {ξ ξ' : R}
    (h : ξ * ξ' = 1) (hν : 1 ≤ G.cycleRank) :
    (G.thetaGen (ξ - ξ')).eval 1 =
      (ξ + ξ') ^ (G.cycleRank - 1) * (ξ ^ (G.cycleRank - 1) + ξ' ^ (G.cycleRank - 1)) :=
  (G.thetaGen_eval_one_of_connected hc (ξ - ξ')).trans (bouquetThetaGen_of_one_le h hν)

/-- **`alg:theta-special-value`, field form.** For a connected multigraph with cycle rank ν
and ξ≠0, 1+ξ²≠0 in a field,
θ_G(1,ξ−ξ⁻¹)=Σ_kC(ν,k)f_{2k}(ξ−ξ⁻¹)=(ξ+ξ⁻¹)^{ν−1}(ξ^{ν−1}+ξ^{1−ν}) with integer
exponents, for every ν≥0. -/
theorem thetaGen_eval_one_of_connected_sub_inv {K : Type*} [Field K] (hc : G.Connected) {ξ : K}
    (hξ : ξ ≠ 0) (h1 : 1 + ξ ^ 2 ≠ 0) :
    (G.thetaGen (ξ - ξ⁻¹)).eval 1 =
      (ξ + ξ⁻¹) ^ ((G.cycleRank : ℤ) - 1) *
        (ξ ^ ((G.cycleRank : ℤ) - 1) + ξ ^ (1 - (G.cycleRank : ℤ))) :=
  (G.thetaGen_eval_one_of_connected hc (ξ - ξ⁻¹)).trans (bouquetThetaGen_sub_inv hξ h1 _)

/-! ### The case γ=2 -/

/-- At γ=2, θ_G(1,2) computed from `thetaGen` in any commutative ring is the cast of the
natural number `theta`. -/
theorem thetaGen_two_eval_one : (G.thetaGen (2 : R)).eval 1 = (G.theta : R) := by
  rw [thetaGen_eval_one]
  simp [thetaGenOn, theta, thetaOn, wt, fGen_two_eq_f2]

open Real in
/-- **γ=2 via ξ=1+√2.** For a connected multigraph,
θ_G(1,2)=(4+2√2)^{ν−1}+(4−2√2)^{ν−1} (integer exponents), obtained from the general-γ
formula with (ξ+ξ⁻¹)ξ^{±1}=4±2√2, without the recurrence for U. -/
theorem theta_eq_lam_mu_zpow_of_connected (hc : G.Connected) :
    (G.theta : ℝ) =
      (4 + 2 * √2) ^ ((G.cycleRank : ℤ) - 1) + (4 - 2 * √2) ^ ((G.cycleRank : ℤ) - 1) := by
  have hs : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  have hξ : (1 + √2 : ℝ) ≠ 0 := by positivity
  have hinv : (1 + √2 : ℝ)⁻¹ = √2 - 1 :=
    inv_eq_of_mul_eq_one_right (by linear_combination hs)
  have h1 : 1 + (1 + √2 : ℝ) ^ 2 ≠ 0 := by positivity
  have hγ : (1 + √2 : ℝ) - (1 + √2)⁻¹ = 2 := by rw [hinv]; ring
  rw [← G.thetaGen_two_eval_one,
    show G.thetaGen (2 : ℝ) = G.thetaGen ((1 + √2) - (1 + √2)⁻¹) by rw [hγ],
    G.thetaGen_eval_one_of_connected_sub_inv hc hξ h1,
    show (1 : ℤ) - G.cycleRank = -((G.cycleRank : ℤ) - 1) by ring, zpow_neg, ← inv_zpow,
    mul_add, ← mul_zpow, ← mul_zpow, hinv]
  congr 2 <;> linear_combination 2 * hs

/-- **γ=2 recovers `theta_eq_U_of_connected`.** The ξ=1+√2 case of the general-γ formula
and the closed form `U_eq` give θ_G(1,2)=U_ν, independently of `bouquetTheta_eq_U`. -/
theorem theta_eq_U_of_connected_of_special_value (hc : G.Connected) :
    (G.theta : ℤ) = U G.cycleRank := by
  have h := G.theta_eq_lam_mu_zpow_of_connected hc
  have hU : (U G.cycleRank : ℝ) =
      (4 + 2 * √2) ^ ((G.cycleRank : ℤ) - 1) + (4 - 2 * √2) ^ ((G.cycleRank : ℤ) - 1) := by
    have hl : (lam : ℝ) ≠ 0 := lam_pos.ne'
    have hm : (mu : ℝ) ≠ 0 := mu_pos.ne'
    have hlm := lam_mul_mu
    rw [U_eq, show (4 + 2 * √2 : ℝ) = lam from rfl, show (4 - 2 * √2 : ℝ) = mu from rfl,
      zpow_sub_one₀ hl, zpow_sub_one₀ hm, zpow_natCast, zpow_natCast]
    have hli : lam⁻¹ = mu / 8 := by
      rw [eq_div_iff (by norm_num : (8 : ℝ) ≠ 0), inv_mul_eq_iff_eq_mul₀ hl]; linarith
    have hmi : mu⁻¹ = lam / 8 := by
      rw [eq_div_iff (by norm_num : (8 : ℝ) ≠ 0), inv_mul_eq_iff_eq_mul₀ hm]
      linarith [mul_comm lam mu]
    rw [hli, hmi]
    ring
  exact_mod_cast h.trans hU.symm

end Multigraph

end BPFixedPoints
