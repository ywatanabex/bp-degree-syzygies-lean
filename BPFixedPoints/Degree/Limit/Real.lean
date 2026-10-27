import BPFixedPoints.Degree.Limit.Strata
import BPFixedPoints.StateSum.Parity

/-!
# Real limit points and the cycle space

For real β_i>0, the equation β=(−1)^k F^{1−k} has exactly one real root
when k is even: F=β if k=0, and the odd-power equation F^{m+1}=1/β if k=m+2.
There is no real root for odd k: k=1 forces β=−1, and k≥3 forces a negative
even power. Real limit points therefore correspond to even-degree active
sets, the cycle space ker ∂ over 𝔽₂. There are 2^{dim ker ∂}
(`card_real_limitSolutions`), or 2^ν if connected (`card_real_limitSolutions_of_connected`).
Only this count of limit points is formalized. The analytic assertion that
these lift to all real nearby solutions at a=1 is not formalized here.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace BP

/-- For real β>0 and odd k, the vertex equation has no real roots. -/
theorem isEmpty_vertexLimitEq_real {k : ℕ} (hk : ¬ Even k) {β : ℝ} (hβ : 0 < β) :
    IsEmpty {F : ℝ // VertexLimitEq k β F} := by
  rcases k with _ | _ | m
  · exact absurd (by decide : Even 0) hk
  · exact ⟨fun F => vertexLimitEq_one β F.1 (by linarith) F.2⟩
  · have hm : ¬ Even m := fun h => hk (h.add (by decide : Even 2))
    have hodd : Odd m := Nat.not_even_iff_odd.1 hm
    have hev : Even (m + 1) := hodd.add_one
    refine ⟨fun F => ?_⟩
    have h1 := (vertexLimitEq_succ_succ_iff m β F.1 hβ.ne').1 F.2
    have hneg : (-1 : ℝ) ^ (m + 2) / β < 0 := by
      apply div_neg_of_neg_of_pos _ hβ
      rw [pow_add, hodd.neg_one_pow]
      norm_num
    have hnn : 0 ≤ F.1 ^ (m + 1) := hev.pow_nonneg _
    linarith

/-- For real β>0 and even k, the vertex equation has exactly one real root. -/
theorem existsUnique_vertexLimitEq_real {k : ℕ} (hk : Even k) {β : ℝ} (hβ : 0 < β) :
    ∃! F : ℝ, VertexLimitEq k β F := by
  rcases k with _ | _ | m
  · refine ⟨β, (vertexLimitEq_zero_iff β β).2 ⟨rfl, hβ.ne'⟩, fun F hF => ?_⟩
    exact ((vertexLimitEq_zero_iff β F).1 hF).1
  · exact absurd hk (by decide)
  · have hk' : Even (m + 2) := hk
    have hm : Even m := (Nat.even_add.1 hk').2 (by decide)
    have hodd : Odd (m + 1) := hm.add_one
    have hc : (-1 : ℝ) ^ (m + 2) / β = 1 / β := by
      rw [pow_add, hm.neg_one_pow]
      norm_num
    have hpos : 0 ≤ 1 / β := le_of_lt (one_div_pos.2 hβ)
    set r : ℝ := (1 / β) ^ ((m + 1 : ℕ) : ℝ)⁻¹ with hr
    have hr_root : r ^ (m + 1) = 1 / β := by
      rw [hr, Real.rpow_inv_natCast_pow hpos (Nat.succ_ne_zero m)]
    refine ⟨r, (vertexLimitEq_succ_succ_iff m β r hβ.ne').2 (by rw [hc, hr_root]), fun F hF => ?_⟩
    have h1 := (vertexLimitEq_succ_succ_iff m β F hβ.ne').1 hF
    rw [hc, ← hr_root] at h1
    exact hodd.strictMono_pow.injective h1

theorem finite_vertexLimitEq_real (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    Finite {F : ℝ // VertexLimitEq k β F} := by
  by_cases hk : Even k
  · obtain ⟨F, -, huniq⟩ := existsUnique_vertexLimitEq_real hk hβ
    have : Subsingleton {F : ℝ // VertexLimitEq k β F} :=
      ⟨fun a b => Subtype.ext ((huniq a.1 a.2).trans (huniq b.1 b.2).symm)⟩
    infer_instance
  · have := isEmpty_vertexLimitEq_real hk hβ
    infer_instance

/-- For real β>0, the real vertex-root count is 1 for even k and 0 for odd k. -/
theorem card_vertexLimitEq_real (k : ℕ) {β : ℝ} (hβ : 0 < β) :
    Nat.card {F : ℝ // VertexLimitEq k β F} = if Even k then 1 else 0 := by
  by_cases hk : Even k
  · rw [ite_eq_left hk, Nat.card_eq_one_iff_exists]
    obtain ⟨F, hF, huniq⟩ := existsUnique_vertexLimitEq_real hk hβ
    exact ⟨⟨F, hF⟩, fun x => Subtype.ext (huniq x.1 x.2)⟩
  · have := isEmpty_vertexLimitEq_real hk hβ
    rw [ite_eq_right hk]
    simp

end BP

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- **Real limit points.** If β_i>0, the number of real limit solutions equals the number of even-degree edge sets, namely 2^{dim ker ∂}. -/
theorem card_real_limitSolutions (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    Nat.card (G.LimitSolutions β) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker G.incMap) := by
  classical
  have hβ1 : ∀ i, β i ≠ -1 := fun i => by linarith [hβ i]
  rw [← G.card_evenSets, Nat.card_congr (G.limitSolutionsEquiv β hβ1)]
  unfold LimitParams
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun S : Finset E => fun F : V → ℝ => ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)))]
  have : ∀ S : Finset E, ∀ i : V, Finite {x : ℝ // VertexLimitEq (G.deg S i) (β i) x} :=
    fun S i => finite_vertexLimitEq_real _ (hβ i)
  have : ∀ S : Finset E,
      Finite {F : V → ℝ // ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)} :=
    fun S => Finite.of_equiv _ (Equiv.subtypePiEquivPi
      (p := fun i (x : ℝ) => VertexLimitEq (G.deg S i) (β i) x)).symm
  rw [Nat.card_sigma, Finset.card_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun i (x : ℝ) => VertexLimitEq (G.deg S i) (β i) x)), Nat.card_pi]
  simp only [fun i => card_vertexLimitEq_real (G.deg S i) (hβ i)]
  rw [Finset.prod_boole]
  simp [IsEvenSet]

/-- For a connected graph there are exactly 2^ν real limit points, ν=|E|−|V|+1; this is the limit-point part of the statement. -/
theorem card_real_limitSolutions_of_connected (hc : G.Connected) (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    Nat.card (G.LimitSolutions β) = 2 ^ G.cycleRank := by
  rw [G.card_real_limitSolutions β hβ, G.finrank_ker_incMap_of_connected hc]

end Multigraph

end BPFixedPoints
