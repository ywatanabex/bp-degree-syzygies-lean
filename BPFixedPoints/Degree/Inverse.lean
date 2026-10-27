import BPFixedPoints.Degree.Equations

/-!
# Recovering BP solutions from auxiliary coordinates

Fix (s,β), choose a_e²=s_e and put b_i=β_i∏_{e∋i}a_e.
Given (A,F) satisfying (4)–(5), A≠0,−1 and F≠0,−1, define
y_{j→i,e}=F_i/(a_e A_{e,i}). This uniquely recovers an admissible BP solution.
Its cavity ratio is X_{i,e}=a_e A_{e,i}; (4) yields the update, with nonzero
update denominator a_e(A_{e,i}+1), normalization 1+F_i and messages, so D≠0.
The recovered auxiliary coordinates and total fields return (A,F).
Here s_e=a_e² is supplied through a, so (4) uses `a α.1 ^ 2`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E) {K : Type*} [Field K]

theorem zpow_one_sub_eq_inv {F : K} {d : ℕ} (hd : 1 ≤ d) :
    F ^ ((1 : ℤ) - d) = (F ^ (d - 1))⁻¹ := by
  rw [← zpow_natCast, Nat.cast_sub hd, ← zpow_neg]
  congr 1
  push_cast
  ring

section Reconstruct

variable (a : E → K) (β : V → K) (A : Dart E → K) (F : V → K)

/-- Recovered vertex parameter b_i=β_i product_incident a_e. -/
def reconB (i : V) : K := β i * ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e

/-- Recovered message y_α=F_headα/(a_e A_tail-side) from (6); rev α is the dart on the head side. -/
def reconY (α : Dart E) : K := F (G.head α) / (a α.1 * A (rev α))

variable {G a β A F}
variable (hG : G.Loopless) (ha : ∀ e, a e ≠ 0) (hA0 : ∀ α, A α ≠ 0) (hA1 : ∀ α, A α ≠ -1)
  (hF0 : ∀ i, F i ≠ 0) (hF1 : ∀ i, F i ≠ -1)
  (h4 : ∀ α, F (G.tail α) = A α * (1 + a α.1 ^ 2 * A (rev α)) / (1 + A (rev α)))
  (h5 : ∀ i, β i = F i ^ ((1 : ℤ) - G.degree i) * ∏ α ∈ G.inDarts i, A (rev α))

include hG ha hA0 hF0 h5 in
/-- The recovered cavity ratio is X_α=a_e A_α. -/
theorem cavity_reconY (α : Dart E) :
    G.cavity (G.reconB a β) (G.reconY a A F) α = a α.1 * A α := by
  unfold cavity reconB
  rw [← G.prod_inDarts_edge hG (G.tail α) a, h5 (G.tail α)]
  have hy : ∀ γ ∈ (G.inDarts (G.tail α)).erase (rev α),
      G.reconY a A F γ = F (G.tail α) / (a γ.1 * A (rev γ)) := by
    intro γ hγ
    rw [Finset.mem_erase, inDarts, Finset.mem_filter] at hγ
    unfold reconY
    rw [hγ.2.2]
  rw [Finset.prod_congr rfl hy, Finset.prod_div_distrib, Finset.prod_const, Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase (G.inDarts (G.tail α)) (fun γ => A (rev γ)) (G.rev_mem_inDarts α),
    ← Finset.mul_prod_erase (G.inDarts (G.tail α)) (fun γ => a γ.1) (G.rev_mem_inDarts α),
    Finset.card_erase_of_mem (G.rev_mem_inDarts α)]
  simp only [rev_rev, rev_fst]
  have hd : 1 ≤ (G.inDarts (G.tail α)).card := Finset.card_pos.2 ⟨rev α, G.rev_mem_inDarts α⟩
  unfold degree
  rw [zpow_one_sub_eq_inv hd]
  have hpa : ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), a γ.1 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun γ _ => ha γ.1
  have hpA : ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), A (rev γ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun γ _ => hA0 (rev γ)
  have hF := hF0 (G.tail α)
  have hFp : F (G.tail α) ^ ((G.inDarts (G.tail α)).card - 1) ≠ 0 := pow_ne_zero _ hF
  field_simp

include hG ha hA0 hF0 h5 in
/-- The recovered full field is F_i. -/
theorem totalField_reconY (i : V) : G.totalField (G.reconB a β) (G.reconY a A F) i = F i := by
  unfold totalField reconB
  rw [← G.prod_inDarts_edge hG i a, h5 i]
  have hy : ∀ γ ∈ G.inDarts i, G.reconY a A F γ = F i / (a γ.1 * A (rev γ)) := by
    intro γ hγ
    rw [inDarts, Finset.mem_filter] at hγ
    unfold reconY
    rw [hγ.2]
  rw [Finset.prod_congr rfl hy, Finset.prod_div_distrib, Finset.prod_const, Finset.prod_mul_distrib]
  unfold degree
  rw [zpow_sub₀ (hF0 i), zpow_one, zpow_natCast]
  have hpa : ∏ γ ∈ G.inDarts i, a γ.1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun γ _ => ha γ.1
  have hpA : ∏ γ ∈ G.inDarts i, A (rev γ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun γ _ => hA0 (rev γ)
  have hF := hF0 i
  have hFp : F i ^ (G.inDarts i).card ≠ 0 := pow_ne_zero _ hF
  field_simp

include hG ha hA0 hF0 h5 in
/-- The recovered auxiliary coordinate is A. -/
theorem auxA_reconY (α : Dart E) : G.auxA a (G.reconB a β) (G.reconY a A F) α = A α := by
  unfold auxA
  rw [cavity_reconY hG ha hA0 hF0 h5, mul_div_cancel_left₀ _ (ha α.1)]

include hG ha hA0 hA1 hF0 h4 h5 in
/-- Recovered messages satisfy the polynomial BP fixed-point equations. -/
theorem isFixedPoint_reconY : G.IsFixedPoint a (G.reconB a β) (G.reconY a A F) := by
  intro α
  unfold bpPoly
  rw [cavity_reconY hG ha hA0 hF0 h5]
  unfold reconY
  have h := h4 (rev α)
  rw [tail_rev, rev_rev, rev_fst] at h
  have hA := hA0 (rev α)
  have hA' := hA1 α
  have h1 : 1 + A α ≠ 0 := fun h0 => hA' (by linear_combination h0)
  have ha' := ha α.1
  rw [h]
  field_simp
  ring

include hG ha hA0 hA1 hF0 hF1 h5 in
/-- Recovered messages satisfy admissibility D≠0. -/
theorem admissible_reconY : G.Admissible a (G.reconB a β) (G.reconY a A F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    unfold reconY
    exact div_ne_zero (hF0 _) (mul_ne_zero (ha _) (hA0 _))
  · intro α
    rw [cavity_reconY hG ha hA0 hF0 h5]
    intro h0
    apply hA1 α
    have := ha α.1
    have h2 : a α.1 * (A α + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 this
    · linear_combination h3
  · intro i
    rw [totalField_reconY hG ha hA0 hF0 h5]
    intro h0
    exact hF1 i (by linear_combination h0)

include hG ha hA0 hA1 hF0 hF1 h4 h5 in
/-- An (A,F) satisfying the edge/vertex equations and nonvanishing conditions reconstructs an admissible BP solution. -/
theorem isAdmissibleSolution_reconY :
    G.IsAdmissibleSolution a (G.reconB a β) (G.reconY a A F) :=
  ⟨isFixedPoint_reconY hG ha hA0 hA1 hF0 h4 h5, admissible_reconY hG ha hA0 hA1 hF0 hF1 h5⟩

end Reconstruct

section RoundTrip

variable (a : E → K) (b : V → K) (y : Dart E → K)

/-- Round trip: applying (6) to auxiliary coordinates of an admissible solution returns the original messages. -/
theorem reconY_auxA (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0) (hy : ∀ α, y α ≠ 0) (α : Dart E) :
    G.reconY a (G.auxA a b y) (G.totalField b y) α = y α := by
  unfold reconY auxA
  rw [rev_fst, G.cavity_rev_eq b y hy α]
  have := ha α.1
  have hF := G.totalField_ne_zero b y hb hy (G.head α)
  have := hy α
  field_simp

/-- Round trip: recovering b from the auxiliary β returns the original b. -/
theorem reconB_auxBeta (ha : ∀ e, a e ≠ 0) (i : V) :
    G.reconB a (G.auxBeta a b) i = b i := by
  unfold reconB auxBeta
  have : ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun e _ => ha e
  rw [div_mul_cancel₀ _ this]

end RoundTrip

end Multigraph

end BPFixedPoints
