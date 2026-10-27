import BPFixedPoints.Incidence.KoszulCechCupDifferential
import BPFixedPoints.Incidence.CechCupDegree
import BPFixedPoints.Incidence.ResolutionDegree

/-! # Total degree and parity of the exterior Čech product -/

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incCupCoefficient_degree (S T : Finset E) (p q : ℤ)
    {x y : IncCechModule (V := V) (E := E)}
    (hx : x ∈ supported (IncCoeffRing E) (IncCoeffRing E) {b | (cechDegree b : ℤ) = p})
    (hy : y ∈ supported (IncCoeffRing E) (IncCoeffRing E) {b | (cechDegree b : ℤ) = q}) :
    G.incCupCoefficient S T x y ∈
      supported (IncCoeffRing E) (IncCoeffRing E) {b | (cechDegree b : ℤ) = p + q} := by
  apply chainCup_degree _ _ _ p q hx
  have h : HasDegree (fun b => (cechDegree b : ℤ)) (fun b => (cechDegree b : ℤ)) 0
      (parity (IncCoeffRing E) (V := V)) := by
    apply HasDegree.of_single
    intro b r
    rw [parity, contraction_sign_single]
    exact Submodule.smul_mem _ _ (single_mem_supported _ _ (by simp))
  simpa only [add_zero] using h.pow_zero S.card q y hy

theorem incTotalCup_degree (p q : ℤ) {x y : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalPiece p) (hy : y ∈ incTotalPiece q) :
    G.incTotalCup x y ∈ incTotalPiece (p + q) := by
  rw [← x.sum_single, map_finsuppSum, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro S _
  rw [← y.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro T _
  dsimp only
  rw [G.incTotalCup_single, Koszul.wedgeSingle_apply]
  by_cases h : Disjoint S T
  · rw [if_pos h]
    apply incTotalPiece_single
    apply Submodule.smul_mem
    have hdeg := G.incCupCoefficient_degree S T ((S.card : ℤ) - p) ((T.card : ℤ) - q)
      (hx S) (hy T)
    have he : ((S ∪ T).card : ℤ) - (p + q) = ((S.card : ℤ) - p) + ((T.card : ℤ) - q) := by
      rw [Finset.card_union_of_disjoint h, Nat.cast_add]; ring
    simpa only [he] using hdeg
  · rw [if_neg h]
    exact Submodule.zero_mem _

theorem incTotalSign_degree (p : ℕ) {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalPiece (p : ℤ)) :
    incTotalSign x = (-1 : IncCoeffRing E) ^ p • x := by
  rw [← x.sum_single, map_finsuppSum]
  simp only [Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [incTotalSign_single, smul_single]
  congr 1
  have hS := hx S
  rw [← (x S).sum_single, map_finsuppSum]
  simp only [Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := (mem_supported (IncCoeffRing E) (x S)).mp hS hb
  have hc : S.card = cechDegree b + p := by dsimp at hb'; omega
  rw [parity, contraction_sign_single, smul_smul, hc, pow_add]
  have hs : (-1 : IncCoeffRing E) ^ cechDegree b * (-1) ^ p * (-1) ^ cechDegree b =
      (-1 : IncCoeffRing E) ^ p := by
    rw [mul_right_comm, Koszul.neg_one_pow_mul_self, one_mul]
  rw [hs]

end BPFixedPoints.Multigraph
