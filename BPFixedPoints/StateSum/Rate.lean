import BPFixedPoints.StateSum.SharpBounds

/-!
# Growth per cycle

Let λ=4+2√2 and μ=4−2√2, with λ+μ=λμ=8. The recurrence has closed form
U_n=(μλ^n+λμ^n)/8=λ^{n−1}+μ^{n−1} (`U_eq`), hence λ^{n−1}≤U_n≤λ^n.
The connected bounds imply 2^ν≤Q(G)≤(4+2√2)^ν
(`two_pow_le_Q_of_connected`, `Q_le_lam_pow_of_connected`). Using N=Q,
these strengthen the asymptotic bounds log 2≤liminf log N/ν≤limsup log N/ν≤log λ
to each graph. The endpoints are attained by flowers
(`tendsto_log_bouquetQ_div`) and graphs with subcubic 2-core, Q=U_ν
(`tendsto_log_U_div`).
-/

namespace BPFixedPoints

open Real Filter Topology

/-- λ = 4 + 2√2。 -/
noncomputable def lam : ℝ := 4 + 2 * √2

/-- μ = 4 − 2√2。 -/
noncomputable def mu : ℝ := 4 - 2 * √2

theorem sqrt_two_lt_two : √2 < 2 := by
  rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
  exact sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem lam_add_mu : lam + mu = 8 := by unfold lam mu; ring

theorem lam_mul_mu : lam * mu = 8 := by
  unfold lam mu
  have : √2 * √2 = 2 := mul_self_sqrt (by norm_num)
  linear_combination -4 * this

theorem mu_pos : 0 < mu := by unfold mu; linarith [sqrt_two_lt_two]

theorem mu_le_lam : mu ≤ lam := by unfold lam mu; linarith [sqrt_nonneg 2]

theorem lam_pos : 0 < lam := by unfold lam; positivity

theorem one_lt_lam : 1 < lam := by unfold lam; linarith [sqrt_nonneg 2]

theorem lam_sq : lam ^ 2 = 8 * lam - 8 := by
  have h1 := lam_add_mu; have h2 := lam_mul_mu
  have : mu = 8 - lam := by linarith
  rw [this] at h2
  linear_combination -h2

theorem mu_sq : mu ^ 2 = 8 * mu - 8 := by
  have h1 := lam_add_mu; have h2 := lam_mul_mu
  have : lam = 8 - mu := by linarith
  rw [this] at h2
  linear_combination -h2

/-- **Closed form.** U_n=(μλ^n+λμ^n)/8=λ^{n−1}+μ^{n−1}. -/
theorem U_eq : ∀ n : ℕ, (U n : ℝ) = (mu * lam ^ n + lam * mu ^ n) / 8
  | 0 => by simp [lam_add_mu, add_comm]
  | 1 => by
    simp only [U_one, Int.cast_ofNat, pow_one]
    rw [mul_comm mu lam, lam_mul_mu]; norm_num
  | n + 2 => by
    rw [U_add_two, Int.cast_sub, Int.cast_mul, Int.cast_mul, U_eq (n + 1), U_eq n]
    push_cast
    have hl : lam ^ (n + 2) = 8 * lam ^ (n + 1) - 8 * lam ^ n := by
      rw [pow_add, lam_sq]; ring
    have hm : mu ^ (n + 2) = 8 * mu ^ (n + 1) - 8 * mu ^ n := by
      rw [pow_add, mu_sq]; ring
    rw [hl, hm]
    ring

/-- U_n ≤ λ^n。 -/
theorem U_le_lam_pow (n : ℕ) : (U n : ℝ) ≤ lam ^ n := by
  rw [U_eq]
  have hmu : mu ^ n ≤ lam ^ n := pow_le_pow_left₀ mu_pos.le mu_le_lam n
  have : mu * lam ^ n + lam * mu ^ n ≤ mu * lam ^ n + lam * lam ^ n := by
    have := mul_le_mul_of_nonneg_left hmu lam_pos.le
    linarith
  calc (mu * lam ^ n + lam * mu ^ n) / 8 ≤ (mu * lam ^ n + lam * lam ^ n) / 8 := by
        gcongr
    _ = lam ^ n := by rw [← add_mul, add_comm, lam_add_mu]; ring

/-- λ^n≤8U_n/μ, equivalently λ^{n−1}≤U_n. -/
theorem lam_pow_le_U (n : ℕ) : mu * lam ^ n ≤ 8 * (U n : ℝ) := by
  rw [U_eq]
  have : 0 ≤ lam * mu ^ n := mul_nonneg lam_pos.le (pow_nonneg mu_pos.le n)
  linarith

/-- U_n is positive. -/
theorem U_pos (n : ℕ) : (0 : ℝ) < U n := by
  have h := lam_pow_le_U n
  have : 0 < mu * lam ^ n := mul_pos mu_pos (pow_pos lam_pos n)
  linarith

/-- **Growth of U.** log U_n/n→log(4+2√2). -/
theorem tendsto_log_U_div :
    Tendsto (fun n : ℕ => log (U n : ℝ) / n) atTop (𝓝 (log lam)) := by
  have hup : ∀ n : ℕ, 0 < n → log (U n : ℝ) / n ≤ log lam := by
    intro n hn
    rw [div_le_iff₀ (by exact_mod_cast hn), mul_comm, ← log_pow]
    exact log_le_log (U_pos n) (U_le_lam_pow n)
  have hlow : ∀ n : ℕ, 0 < n → log lam + (log mu - log 8) / n ≤ log (U n : ℝ) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : log (mu * lam ^ n) ≤ log (8 * (U n : ℝ)) :=
      log_le_log (mul_pos mu_pos (pow_pos lam_pos n)) (lam_pow_le_U n)
    rw [log_mul mu_pos.ne' (pow_pos lam_pos n).ne', log_pow,
      log_mul (by norm_num) (U_pos n).ne'] at h1
    rw [add_div' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith
  have hconst : Tendsto (fun n : ℕ => log lam + (log mu - log 8) / n) atTop (𝓝 (log lam)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (log mu - log 8)).const_add (log lam)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn using hlow n hn
  · filter_upwards [eventually_gt_atTop 0] with n hn using hup n hn

/-- For n≥1, 2^n≤(n−1)2^n+2. -/
theorem two_pow_le_bouquet (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ^ n ≤ ((n : ℤ) - 1) * 2 ^ n + 2 := by
  rcases n with _ | _ | m
  · omega
  · norm_num
  · have hp : (0 : ℤ) ≤ 2 ^ (m + 2) := by positivity
    have : ((m + 2 : ℕ) : ℤ) - 1 = (m : ℤ) + 1 := by push_cast; ring
    rw [this]
    nlinarith

/-- **Flower growth.** log((ν−1)2^ν+2)/ν→log 2. -/
theorem tendsto_log_bouquetQ_div :
    Tendsto (fun n : ℕ => log (bouquetQ n : ℝ) / n) atTop (𝓝 (log 2)) := by
  have hb : ∀ n : ℕ, (bouquetQ n : ℝ) = ((n : ℝ) - 1) * 2 ^ n + 2 := by
    intro n
    have := bouquetQ_eq n
    exact_mod_cast this
  have hpos : ∀ n : ℕ, (0 : ℝ) < bouquetQ n := by
    intro n
    rw [hb]
    rcases n with _ | n
    · norm_num
    · push_cast
      have : ((n : ℝ) + 1 - 1) = n := by ring
      rw [this]
      positivity
  have hlow : ∀ n : ℕ, 0 < n → log 2 ≤ log (bouquetQ n : ℝ) / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn', mul_comm, ← log_pow]
    apply log_le_log (by positivity)
    rw [hb]
    have := two_pow_le_bouquet n hn
    exact_mod_cast this
  have hup : ∀ n : ℕ, 0 < n → log (bouquetQ n : ℝ) / n ≤ log 2 + log n / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [add_div' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn', mul_comm, ← log_pow,
      ← log_mul (by positivity) hn'.ne']
    apply log_le_log (hpos n)
    rw [hb]
    have : (2 : ℝ) ≤ 2 ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    nlinarith
  have hlogn : Tendsto (fun n : ℕ => log 2 + log (n : ℝ) / n) atTop (𝓝 (log 2)) := by
    have h := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun n : ℕ => log (n : ℝ) / n) atTop (𝓝 0) := by
      refine h.congr fun n => ?_
      simp
    simpa using h'.const_add (log 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlogn ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn using hlow n hn
  · filter_upwards [eventually_gt_atTop 0] with n hn using hup n hn

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- For connected G, 2^ν≤Q(G). -/
theorem two_pow_le_Q_of_connected (hc : G.Connected) : 2 ^ G.cycleRank ≤ G.Q := by
  have h := G.lower_bound_of_connected hc
  have : (2 : ℤ) ^ G.cycleRank ≤ G.Q := by
    rcases Nat.lt_or_ge G.cycleRank 1 with h0 | h1
    · have : G.cycleRank = 0 := by omega
      rw [this] at h ⊢
      simpa using h
    · exact (two_pow_le_bouquet _ h1).trans h
  exact_mod_cast this

/-- For connected G, Q(G)≤(4+2√2)^ν. -/
theorem Q_le_lam_pow_of_connected (hc : G.Connected) : (G.Q : ℝ) ≤ lam ^ G.cycleRank := by
  have h := G.Q_le_U_of_connected hc
  have : (G.Q : ℝ) ≤ (U G.cycleRank : ℝ) := by exact_mod_cast h
  exact this.trans (U_le_lam_pow _)

/-- **Per-graph form.** For connected ν≥1, log 2≤log Q(G)/ν≤log(4+2√2). -/
theorem log_Q_div_cycleRank_mem (hc : G.Connected) (hν : 1 ≤ G.cycleRank) :
    log 2 ≤ log (G.Q : ℝ) / G.cycleRank ∧ log (G.Q : ℝ) / G.cycleRank ≤ log lam := by
  have hν' : (0 : ℝ) < G.cycleRank := by exact_mod_cast hν
  have hQ2 : ((2 : ℝ) ^ G.cycleRank) ≤ G.Q := by exact_mod_cast G.two_pow_le_Q_of_connected hc
  have hQpos : (0 : ℝ) < G.Q := lt_of_lt_of_le (by positivity) hQ2
  constructor
  · rw [le_div_iff₀ hν', mul_comm, ← log_pow]
    exact log_le_log (by positivity) hQ2
  · rw [div_le_iff₀ hν', mul_comm, ← log_pow]
    exact log_le_log hQpos (G.Q_le_lam_pow_of_connected hc)

end Multigraph

end BPFixedPoints
