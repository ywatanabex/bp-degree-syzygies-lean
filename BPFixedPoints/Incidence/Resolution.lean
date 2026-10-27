import BPFixedPoints.Incidence.Normal
import BPFixedPoints.Incidence.ResolutionAugmentation
import BPFixedPoints.Incidence.ResolutionProjective

/-!
# Projective dimension of the universal incidence module

For the incidence module over the original coefficient ring, the constructed
finite minimal free resolution has length equal to the maximal state degree
rho. Choose an edge ordering internally for Koszul signs, without adding a
hypothesis to the public statement.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

theorem incidenceRing_projectiveDimension :
    letI := G.coeffHom.toRingHom.toAlgebra
    CategoryTheory.projectiveDimension (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) =
      (G.rho : WithBot ℕ∞) := by
  letI := G.coeffHom.toRingHom.toAlgebra
  letI : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
  exact G.incResolution_projectiveDimension G.incResolutionAugmentation
    G.incResolutionAugmentation_exact G.incResolutionAugmentation_surjective

end BPFixedPoints.Multigraph
