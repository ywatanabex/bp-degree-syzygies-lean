import BPFixedPoints.Incidence.KoszulCechCupDegree
import BPFixedPoints.Incidence.ResolutionExactness

/-! # Transfer the product to the actual finite free resolution -/

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Product on the original free resolution using inclusion and projection with HPL corrections. -/
noncomputable def incResolutionCup :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
      (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
        (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  (G.incTotalCup.compl₁₂ G.incResolutionInclusion G.incResolutionInclusion).compr₂
    G.incResolutionProjection

theorem incResolutionCup_apply (x y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incResolutionCup x y = G.incResolutionProjection
      (G.incTotalCup (G.incResolutionInclusion x) (G.incResolutionInclusion y)) := rfl

theorem incResolutionCup_degree (p q : ℕ) {x y : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree p)
    (hy : y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree q) :
    G.incResolutionCup x y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree (p + q) := by
  rw [G.incResolutionCup_apply]
  apply G.incResolutionProjection_degree
  simpa only [Nat.cast_add] using G.incTotalCup_degree (p : ℤ) (q : ℤ)
    (G.incResolutionInclusion_degree p x hx) (G.incResolutionInclusion_degree q y hy)

theorem incResolutionCup_leibniz (p : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree p)
    (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incResolutionDifferential (G.incResolutionCup x y) =
      G.incResolutionCup (G.incResolutionDifferential x) y +
      (-1 : IncCoeffRing E) ^ p • G.incResolutionCup x (G.incResolutionDifferential y) := by
  have hI (z) : G.incTotalDifferential (G.incResolutionInclusion z) =
      G.incResolutionInclusion (G.incResolutionDifferential z) :=
    LinearMap.congr_fun G.incResolutionInclusion_chain z
  have hP (z) : G.incResolutionDifferential (G.incResolutionProjection z) =
      G.incResolutionProjection (G.incTotalDifferential z) :=
    (LinearMap.congr_fun G.incResolutionProjection_chain z).symm
  rw [G.incResolutionCup_apply, hP, G.incTotalCup_leibniz,
    incTotalSign_degree p (G.incResolutionInclusion_degree p x hx), hI, hI]
  simp only [map_add, map_smul, LinearMap.smul_apply]
  rfl

end BPFixedPoints.Multigraph
