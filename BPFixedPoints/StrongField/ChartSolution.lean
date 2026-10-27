import BPFixedPoints.StrongField.Chart
import BPFixedPoints.Real.VertexMap

/-!
# From chart solutions to admissible BP solutions

For state S, parameters (a,π) with π_i≠0 and chart solution (q,w), set
f_i=π_i w_i; F_i=f_i for k_i≥2 and f_i⁻¹ for k_i=0;
y_α=q_α outside S and −F_{h(α)}/q_α on S;
b_i=(−1)^{k_i}/π_i^{r_i}, equivalently p_i=(−1)^{k_i}π_i^{r_i}.
Then y is admissible at (a,b) with total fields F (`isAdmissibleSolution_chartBP`).
The vertex equation is (−1)^k p_i C=f_i^{r_i}, paper (4.5). Edge equations
use positive updates and the negative-branch involution
(q_α,q_ᾱ)↦(−F_h/q_α,−F_t/q_ᾱ). Four open conditions give admissibility:
1+afq≠0 at inactive vertices, f+aq≠0 at active vertices, q≠a on S and f≠−1.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section ChartBP

variable (S : Finset E) (a : E → ℂ) (π : V → ℂ) (z : Dart E ⊕ V → ℂ)

/-- Total field F_i. -/
noncomputable def chartF (i : V) : ℂ :=
  if G.deg S i = 0 then (π i * z (Sum.inr i))⁻¹ else π i * z (Sum.inr i)

/-- Message y_α. -/
noncomputable def chartY (α : Dart E) : ℂ :=
  if α.1 ∈ S then -G.chartF S π z (G.head α) / z (Sum.inl α) else z (Sum.inl α)

/-- External field b_i=(−1)^{k_i}/π_i^{r_i}. -/
noncomputable def chartB (i : V) : ℂ := (-1) ^ G.deg S i / π i ^ G.rS S i

variable {G S a π z}

theorem deg_ne_zero_of_mem {e : E} (he : e ∈ S) {v : V} (hv : G.Incident e v) :
    G.deg S v ≠ 0 := by
  rw [Ne, deg_eq_zero_iff]
  push Not
  exact ⟨e, he, hv⟩

theorem head_incident (α : Dart E) : G.Incident α.1 (G.head α) := by
  rcases α with ⟨e, _ | _⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tail_incident (α : Dart E) : G.Incident α.1 (G.tail α) := by
  rcases α with ⟨e, _ | _⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem chartF_ne_zero (hπ : ∀ i, π i ≠ 0) (hw : ∀ i, z (Sum.inr i) ≠ 0) (i : V) :
    G.chartF S π z i ≠ 0 := by
  unfold chartF; split_ifs <;> simp [hπ i, hw i]

/-- **Chart solutions give admissible BP solutions.** -/
theorem isAdmissibleSolution_chartBP (hG : G.Loopless) (hS : IsState G S) (_ha : ∀ e, a e ≠ 0)
    (hπ : ∀ i, π i ≠ 0) (hw : ∀ i, z (Sum.inr i) ≠ 0) (hq : ∀ α, z (Sum.inl α) ≠ 0)
    (hsol : G.chartMap S (Sum.elim a π, z) = 0)
    (h1 : ∀ α, α.1 ∉ S → G.deg S (G.tail α) = 0 →
      1 + a α.1 * (π (G.tail α) * z (Sum.inr (G.tail α))) * z (Sum.inl (rev α)) ≠ 0)
    (h2 : ∀ α, α.1 ∉ S → G.deg S (G.tail α) ≠ 0 →
      π (G.tail α) * z (Sum.inr (G.tail α)) + a α.1 * z (Sum.inl (rev α)) ≠ 0)
    (h3 : ∀ α, α.1 ∈ S → z (Sum.inl (rev α)) ≠ a α.1)
    (h4 : ∀ i, π i * z (Sum.inr i) ≠ -1) :
    G.IsAdmissibleSolution a (G.chartB S π) (G.chartY S π z) ∧
      ∀ i, G.totalField (G.chartB S π) (G.chartY S π z) i = G.chartF S π z i := by
  classical
  set F := G.chartF S π z
  set y := G.chartY S π z
  set b := G.chartB S π
  have hF0 : ∀ i, F i ≠ 0 := chartF_ne_zero hπ hw
  have hy0 : ∀ α, y α ≠ 0 := by
    intro α
    simp only [y, chartY]
    split_ifs
    · exact div_ne_zero (neg_ne_zero.2 (hF0 _)) (hq α)
    · exact hq α
  -- Equations of the system.
  have hedge : ∀ α, eval (Sum.elim (Sum.elim a π) z) (G.chartEdge S α) = 0 := fun α => by
    have := congrFun hsol (Sum.inl α); exact this
  have hvert : ∀ i, eval (Sum.elim (Sum.elim a π) z) (G.chartVertex S i) = 0 := fun i => by
    have := congrFun hsol (Sum.inr i); exact this
  have hedge' : ∀ α, (if G.deg S (G.tail α) = 0 then
      z (Sum.inl α) * (1 + a α.1 * π (G.tail α) * z (Sum.inr (G.tail α)) * z (Sum.inl (rev α))) -
        (a α.1 + π (G.tail α) * z (Sum.inr (G.tail α)) * z (Sum.inl (rev α)))
      else z (Sum.inl α) * (π (G.tail α) * z (Sum.inr (G.tail α)) + a α.1 * z (Sum.inl (rev α))) -
        (a α.1 * π (G.tail α) * z (Sum.inr (G.tail α)) + z (Sum.inl (rev α)))) = 0 := by
    intro α
    have := hedge α
    simp only [chartEdge, vA, vP, vQ, vW] at this
    split_ifs at this ⊢ <;> simpa using this
  have hvert' : ∀ i, z (Sum.inr i) ^ G.rS S i *
      ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), z (Sum.inl α) =
      ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), z (Sum.inl α) := by
    intro i
    have := hvert i
    simp only [chartVertex, vQ, vW, map_sub, map_mul, map_pow, map_prod, eval_X, Sum.elim_inr]
      at this
    linear_combination this
  -- Total fields.
  have htot : ∀ i, G.totalField b y i = F i := by
    intro i
    unfold totalField
    have hhead : ∀ α ∈ G.inDarts i, G.head α = i := fun α hα => by simpa [inDarts] using hα
    rw [← Finset.prod_filter_mul_prod_filter_not (G.inDarts i) (fun α => α.1 ∈ S)]
    have hS1 : ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), y α =
        (-F i) ^ G.deg S i / ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), z (Sum.inl α) := by
      rw [← card_inDarts_filter_mem hG i, ← Finset.prod_const, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun α hα => ?_
      have hα' := Finset.mem_filter.1 hα
      simp only [y, chartY, hα'.2, ↓reduceIte, hhead α hα'.1, F]
    have hS2 : ∏ α ∈ (G.inDarts i).filter (fun α => ¬ α.1 ∈ S), y α =
        ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), z (Sum.inl α) := by
      refine Finset.prod_congr rfl fun α hα => ?_
      have hα' := Finset.mem_filter.1 hα
      simp only [y, chartY, hα'.2, ↓reduceIte]
    rw [hS1, hS2, ← hvert' i]
    have hP : ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), z (Sum.inl α) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun α _ => hq α
    have hπi := hπ i
    have hwi := hw i
    have e1 : b i * ((-F i) ^ G.deg S i / (z (Sum.inr i) ^ G.rS S i *
        ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), z (Sum.inl α)) *
        ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), z (Sum.inl α)) =
        F i ^ G.deg S i / (π i * z (Sum.inr i)) ^ G.rS S i := by
      simp only [b, chartB]
      rw [neg_pow, mul_pow]
      have hsq : ((-1 : ℂ) ^ (G.deg S i * 2)) = 1 := Even.neg_one_pow ⟨G.deg S i, by ring⟩
      field_simp
      linear_combination (F i ^ G.deg S i) * hsq
    rw [e1]
    simp only [F, chartF, rS]
    split_ifs with hk
    · rw [hk]; simp
    · obtain ⟨m, hm⟩ : ∃ m, G.deg S i = m + 2 := ⟨G.deg S i - 2, by have := hS i; omega⟩
      rw [hm, show m + 2 - 1 = m + 1 by omega]
      have hf : π i * z (Sum.inr i) ≠ 0 := mul_ne_zero hπi hwi
      field_simp
      ring
  -- Cavity fields.
  have hcav : ∀ α, G.cavity b y α = F (G.tail α) / y (rev α) := by
    intro α
    have := G.totalField_tail_eq b y α
    rw [htot] at this
    rw [this, mul_div_cancel_right₀ _ (hy0 _)]
  -- Activity at the edge head and tail.
  have hact : ∀ α, α.1 ∈ S → G.deg S (G.tail α) ≠ 0 ∧ G.deg S (G.head α) ≠ 0 := fun α hα =>
    ⟨deg_ne_zero_of_mem hα (tail_incident α), deg_ne_zero_of_mem hα (head_incident α)⟩
  refine ⟨⟨fun α => ?_, hy0, fun α => ?_, fun i => ?_⟩, htot⟩
  · -- Fixed point.
    unfold bpPoly
    rw [hcav]
    have hr := hy0 (rev α)
    by_cases hS' : α.1 ∈ S
    · -- Negative branch.
      obtain ⟨ht, hh⟩ := hact α hS'
      have hrS : (rev α).1 ∈ S := hS'
      have hE := hedge' (rev α)
      rw [tail_rev, rev_rev, rev_fst, ite_eq_right hh] at hE
      simp only [y, chartY, hS', hrS, ↓reduceIte, head_rev, F, chartF, ht, hh]
      have hqa := hq α
      have hqr := hq (rev α)
      have hFt : π (G.tail α) * z (Sum.inr (G.tail α)) ≠ 0 := mul_ne_zero (hπ _) (hw _)
      have key : ∀ (Fh Ft q q' A : ℂ), Ft ≠ 0 → q ≠ 0 → q' ≠ 0 →
          q' * (Fh + A * q) - (A * Fh + q) = 0 →
          (-Fh / q) * (Ft / (-Ft / q') + A) - (A * (Ft / (-Ft / q')) + 1) = 0 := by
        intro Fh Ft q q' A hFt hq hq' h
        have hX : Ft / (-Ft / q') = -q' := by field_simp
        rw [hX]
        field_simp
        linear_combination h
      exact key _ _ _ _ _ hFt hqa hqr (by linear_combination hE)
    · have hrS : (rev α).1 ∉ S := hS'
      have hE := hedge' α
      simp only [y, chartY, ite_eq_right hS', ite_eq_right hrS, F, chartF]
      have hqr := hq (rev α)
      have hπt := hπ (G.tail α)
      have hwt := hw (G.tail α)
      split_ifs at hE ⊢ with ht
      · field_simp
        linear_combination hE
      · field_simp
        linear_combination hE
  · -- Denominators.
    rw [hcav]
    by_cases hS' : α.1 ∈ S
    · have hrS : (rev α).1 ∈ S := hS'
      obtain ⟨ht, -⟩ := hact α hS'
      simp only [y, chartY, ite_eq_left hrS, head_rev, F, chartF, ite_eq_right ht]
      have hqr := hq (rev α)
      have hπt := hπ (G.tail α)
      have hwt := hw (G.tail α)
      have : π (G.tail α) * z (Sum.inr (G.tail α)) /
          (-(π (G.tail α) * z (Sum.inr (G.tail α))) / z (Sum.inl (rev α))) = -z (Sum.inl (rev α)) := by
        field_simp
      rw [this]
      intro h0
      exact h3 α hS' (by linear_combination -h0)
    · have hrS : (rev α).1 ∉ S := hS'
      simp only [y, chartY, ite_eq_right hrS, F, chartF]
      have hqr := hq (rev α)
      have hπt := hπ (G.tail α)
      have hwt := hw (G.tail α)
      split_ifs with ht
      · have hh := h1 α hS' ht
        intro h0
        apply hh
        field_simp at h0
        linear_combination h0
      · have hh := h2 α hS' ht
        intro h0
        apply hh
        field_simp at h0
        linear_combination h0
  · -- 1 + F ≠ 0
    rw [htot]
    simp only [F, chartF]
    have hπi := hπ i
    have hwi := hw i
    have h4i := h4 i
    split_ifs
    · intro h0
      apply h4i
      field_simp at h0
      linear_combination h0
    · intro h0; exact h4i (by linear_combination h0)

end ChartBP

end Multigraph

end BPFixedPoints
