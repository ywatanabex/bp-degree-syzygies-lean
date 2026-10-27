import BPFixedPoints.Incidence.ResolutionExactness
import BPFixedPoints.Incidence.ResolutionFiniteModel

/-!
# Projective dimension from the actual free model

Use proved properties of the constructed incidence model: square-zero
differential, positive-degree exactness, length, nonzero top term and origin
minimality. The remaining input is a degree-zero augmentation with exactness
and surjectivity, supplied by gluing to the actual incidence ring.
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Identifying degree zero of the actual incidence free model determines projective dimension as rho. -/
theorem incResolution_projectiveDimension
    {M : Type} [AddCommGroup M] [Module (IncCoeffRing E) M] [Nontrivial M]
    (ε₀ : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 →ₗ[IncCoeffRing E] M)
    (hεexact : ∀ x : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0,
      ε₀ x = 0 ↔ ∃ y, y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 1 ∧
        G.incResolutionDifferential y = x.val)
    (hεsurj : Function.Surjective ε₀) :
    CategoryTheory.projectiveDimension (ModuleCat.of (IncCoeffRing E) M) =
      (G.rho : WithBot ℕ∞) := by
  letI : Algebra (IncCoeffRing E) ℂ :=
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
  apply projectiveDimension_eq_of_gradedResolution₀ (k := ℂ)
    G.incResolutionDegree G.incResolutionDifferential G.incResolutionDifferential_degree
    G.incResolutionDifferential_sq G.incResolutionDifferential_exact
    ε₀ hεexact hεsurj G.rho G.incResolutionDegree_le G.exists_incResolutionDegree_top
  intro x
  change G.incResolutionDifferential x ∈ incCoeffAugmentationIdeal E •
    (⊤ : Submodule (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E))
  exact G.incResolutionDifferential_minimal x

end BPFixedPoints.Multigraph
