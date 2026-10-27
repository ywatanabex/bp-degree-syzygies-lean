import BPFixedPoints.Incidence.HomogeneousDimensions
import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # Homogeneous dimension generating functions and degree sums over finite bases -/

namespace BPFixedPoints.ResolutionTools
open scoped PowerSeries

theorem coeff_invOneSubPow_multichoose (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℤ d).val = (Nat.multichoose d n : ℤ) := by
  cases d with
  | zero => cases n <;> simp [PowerSeries.invOneSubPow]
  | succ d =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
      Nat.multichoose_eq]
    have h : d + 1 + n - 1 = d + n := by omega
    rw [h, Nat.choose_symm_add]

/-- Generating function of homogeneous dimensions of an actual weighted free term. -/
theorem weightedFreePiece_hilbert {k σ I : Type*} [Field k] [Fintype σ] [Fintype I]
    (w : I → ℕ) :
    PowerSeries.mk (fun n : ℕ =>
      (Module.finrank k (weightedFreePiece (σ := σ) (k := k) w n) : ℤ)) =
      ∑ i, PowerSeries.X ^ w i * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  classical
  ext n
  simp only [PowerSeries.coeff_mk, map_sum, finrank_weightedFreePiece, Nat.cast_sum,
    PowerSeries.coeff_X_pow_mul', coeff_invOneSubPow_multichoose]
  apply Finset.sum_congr rfl
  intro i _
  have he : ((w i : ℤ) ≤ (n : ℤ)) ↔ w i ≤ n := by omega
  have hn : ((n : ℤ) - (w i : ℤ)).toNat = n - w i := by omega
  simp only [he, hn, Nat.cast_ite, Nat.cast_zero]

theorem sum_finite_weight_fibres {I A : Type*} [Fintype I] [AddCommMonoid A]
    (w : I → ℕ) (N : ℕ) (hN : ∀ i, w i ≤ N) (f : I → A) :
    ∑ n ∈ Finset.range (N + 1), (∑ i : {i : I // w i = n}, f i.val) = ∑ i, f i := by
  classical
  have hf (n : ℕ) : (∑ i : {i : I // w i = n}, f i.val) =
      ∑ i ∈ Finset.univ.filter (fun i => w i = n), f i :=
    (Finset.sum_subtype _ (by simp) f).symm
  simp_rw [hf, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Finset.mem_range, Nat.lt_succ_of_le (hN i)]

end BPFixedPoints.ResolutionTools
