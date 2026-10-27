import BPFixedPoints.Incidence.CechCupInternalGrading
import BPFixedPoints.Incidence.ResolutionCup
import BPFixedPoints.Incidence.ResolutionInternalGrading

/-!
# Internal degree of full exterior Čech products and transferred products

A common edge forces a zero product. For disjoint edge sets, basis weights
add, so the product preserves the existing internal degree, the sum of
coefficient degree and edge weight.
-/

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incCupCoefficient_internal_degree (S T : Finset E) (p q : ℤ)
    {x y : IncCechModule (V := V) (E := E)}
    (hx : x ∈ incCechInternalPiece p) (hy : y ∈ incCechInternalPiece q) :
    G.incCupCoefficient S T x y ∈ incCechInternalPiece (p + q) :=
  chainCup_coefficient_degree (G.deg S) (G.deg T) p q hx
    (parity_pow_coefficient_degree S.card q hy)

theorem incTotalCup_single_internal_degree (S T : Finset E) (p q : ℤ)
    {x y : IncCechModule (V := V) (E := E)}
    (hx : x ∈ incCechInternalPiece (p - (S.card : ℤ)))
    (hy : y ∈ incCechInternalPiece (q - (T.card : ℤ))) :
    G.incTotalCup (single S x) (single T y) ∈ incTotalInternalPiece (p + q) := by
  rw [G.incTotalCup_single, Koszul.wedgeSingle_apply]
  split_ifs with h
  · apply incTotalInternalPiece_single
    have hd : p + q - ((S ∪ T).card : ℤ) =
        (p - (S.card : ℤ)) + (q - (T.card : ℤ)) := by
      rw [Finset.card_union_of_disjoint h, Nat.cast_add]
      ring
    rw [hd]
    exact coefficientwise_sign_smul _ _ (G.incCupCoefficient_internal_degree S T _ _ hx hy)
  · exact Submodule.zero_mem _

theorem incTotalCup_internal_degree (p q : ℤ)
    {x y : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece p) (hy : y ∈ incTotalInternalPiece q) :
    G.incTotalCup x y ∈ incTotalInternalPiece (p + q) := by
  rw [← x.sum_single, map_finsuppSum, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro S _
  rw [← y.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro T _
  exact G.incTotalCup_single_internal_degree S T p q (hx S) (hy T)

/-- Internal degree of the actual resolution product, including all finite-perturbation corrections. -/
theorem incResolutionCup_internal_degree (p q : ℤ)
    {x y : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ G.incResolutionInternalPiece p) (hy : y ∈ G.incResolutionInternalPiece q) :
    G.incResolutionCup x y ∈ G.incResolutionInternalPiece (p + q) := by
  rw [G.incResolutionCup_apply]
  exact G.incResolutionProjection_internal_degree _
    (G.incTotalCup_internal_degree p q
      (G.incResolutionInclusion_internal_degree p hx)
      (G.incResolutionInclusion_internal_degree q hy))

end BPFixedPoints.Multigraph
