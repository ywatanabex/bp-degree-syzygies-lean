import BPFixedPoints.Incidence.ResolutionNativeYonedaSign
import Mathlib.Algebra.BigOperators.Intervals

/-! # The actual accumulated native cone sign

The recursion proved from the original cone projections has triangular
exponent. This sign is distinct from the cubical left-minus-right sign.
-/

namespace BPFixedPoints.ExtResolutionTools
open scoped BigOperators

/-- The actual successive cone signs multiply to the sign of the sum of their original degrees. -/
theorem nativeYonedaSign_eq_sum (n : ℕ) :
    nativeYonedaSign n = ((∑ k ∈ Finset.range (n+1), k : ℕ) : ℤ).negOnePow := by
  induction n with
  | zero => simp [nativeYonedaSign]
  | succ n ih =>
    have hs := Finset.sum_range_succ (fun k : ℕ => k) (n+1)
    rw [nativeYonedaSign,ih,hs,Int.natCast_add,Int.negOnePow_add,Int.natCast_succ]
    simp only [Int.negOnePow_add]
    ac_rfl

/-- The native resolution roof has the original iterated Yoneda sign (-1) to the triangular degree. -/
theorem nativeYonedaSign_eq (n : ℕ) :
    nativeYonedaSign n = ((n*(n+1)/2 : ℕ) : ℤ).negOnePow := by
  rw [nativeYonedaSign_eq_sum,Finset.sum_range_id]
  simp [Nat.mul_comm]

end BPFixedPoints.ExtResolutionTools
