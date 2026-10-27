import BPFixedPoints.StateSum.ConnectedBound
import BPFixedPoints.StateSum.Theta

/-!
# Sharp bounds for connected graphs

For nonempty connected G and ν=|E|−|V|+1,
(ν−1)2^ν+2≤Q(G)≤U_ν=(4+2√2)^{ν−1}+(4−2√2)^{ν−1}.
`ConnectedBound` gives the lower bound; coefficient comparison Q≤θ(1,2)
and θ(1,2)=bouquetTheta ν=U_ν give the upper bound.
-/

namespace BPFixedPoints

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- For connected G, θ(1,2)=U_ν, expressed by the integer recurrence. -/
theorem theta_eq_U_of_connected (hc : G.Connected) : (G.theta : ℤ) = U G.cycleRank := by
  rw [G.theta_eq_bouquetTheta_of_connected hc, bouquetTheta_eq_U]

/-- For nonempty connected G, Q(G)≤U_ν. -/
theorem Q_le_U_of_connected (hc : G.Connected) : (G.Q : ℤ) ≤ U G.cycleRank := by
  rw [← G.theta_eq_U_of_connected hc]
  exact_mod_cast G.QOn_le_thetaOn Finset.univ

/-- Combined sharp bounds: (ν−1)2^ν+2≤Q(G)≤U_ν. -/
theorem sharp_bounds_of_connected (hc : G.Connected) :
    ((G.cycleRank : ℤ) - 1) * 2 ^ G.cycleRank + 2 ≤ (G.Q : ℤ) ∧ (G.Q : ℤ) ≤ U G.cycleRank :=
  ⟨G.lower_bound_of_connected hc, G.Q_le_U_of_connected hc⟩

/-- For connected G with subcubic 2-core, Q(G)=U_ν: equality in the upper bound. -/
theorem Q_eq_U_of_connected_of_core (hc : G.Connected)
    (h : ∀ v, G.deg (G.core Finset.univ) v ≤ 3) : (G.Q : ℤ) = U G.cycleRank := by
  rw [← G.theta_eq_U_of_connected hc]
  unfold Q theta
  rw [G.thetaOn_eq_QOn_of_core Finset.univ h]

end Multigraph

end BPFixedPoints
