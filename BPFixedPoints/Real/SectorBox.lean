import BPFixedPoints.Real.VertexMap

/-!
# Box bounds for the vertex map

Uniform estimates at positive edge parameters and boundedness of Eulerian
fibers, usable without assuming the total strong-field root count.
-/

namespace BPFixedPoints.Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  {G : Multigraph V E}

section Box

variable {a : E → ℝ} {S : Finset E} {u : V → ℝ}

/-- The vertex map differs from its diagonal part by at most J̄_i. -/
theorem abs_diag_sub_sectorField_le (ha : ∀ e, 0 < a e) (i : V) :
    |(1 - (G.deg S i : ℝ)) * u i - G.sectorField a S u i| ≤
      ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
  rw [sectorField, sub_sub_cancel]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  rw [abs_mul]
  have h1 : |sgnS S α| = 1 := by unfold sgnS; split_ifs <;> simp
  rw [h1, one_mul]
  exact abs_zPlus_le (ha α.1) _ _

/-- **Box bound (`real:global-box`).** If 𝔥_S(u)=h, then |(1−k_i)u_i−h_i|≤J̄_i. -/
theorem abs_sub_le_of_sectorField_eq (ha : ∀ e, 0 < a e) {h : V → ℝ}
    (hu : ∀ i, G.sectorField a S u i = h i) (i : V) :
    |(1 - (G.deg S i : ℝ)) * u i - h i| ≤ ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
  rw [← hu i]
  exact abs_diag_sub_sectorField_le ha i

/-- **Bounded fibers (properness).** For Eulerian S and 𝔥_S(u)=h, |u_i|≤|h_i|+J̄_i. -/
theorem abs_le_of_sectorField_eq (ha : ∀ e, 0 < a e) (hS : G.IsEvenSet S) {h : V → ℝ}
    (hu : ∀ i, G.sectorField a S u i = h i) (i : V) :
    |u i| ≤ |h i| + ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
  have hk : 1 ≤ |1 - (G.deg S i : ℝ)| := by
    obtain ⟨k, hk⟩ := hS i
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [hk, h0]; simp
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hpos
      have : (2 : ℝ) ≤ G.deg S i := by rw [hk]; push_cast; linarith
      rw [abs_of_nonpos (by linarith)]; linarith
  have hbox := abs_sub_le_of_sectorField_eq ha hu i
  calc |u i| = 1 * |u i| := (one_mul _).symm
    _ ≤ |1 - (G.deg S i : ℝ)| * |u i| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _ = |(1 - (G.deg S i : ℝ)) * u i| := (abs_mul _ _).symm
    _ ≤ |h i| + |(1 - (G.deg S i : ℝ)) * u i - h i| := by
        have := abs_add_le (h i) ((1 - (G.deg S i : ℝ)) * u i - h i)
        rwa [add_sub_cancel] at this
    _ ≤ _ := by linarith

end Box

end BPFixedPoints.Multigraph
