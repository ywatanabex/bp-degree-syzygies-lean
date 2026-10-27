import BPFixedPoints.Incidence.Normal
import BPFixedPoints.Incidence.Finite
import BPFixedPoints.Incidence.Dimension
import BPFixedPoints.Incidence.Resolution

/-!
# Ring-theoretic properties of the universal edge-incidence ring

Definitions are in `Incidence/Ring.lean`; charts, torus and normal-domain proofs
are in `Incidence/Chart.lean`, `Torus.lean`, `Normal.lean`. Finiteness is in
`Incidence/Finite.lean`, dimension in `Incidence/Dimension.lean`. Projective
dimension is proved in `Incidence/Resolution.lean` using the actual finite
minimal free resolution constructed from the Koszul–Čech complex. Keep
completed declarations in their original files to preserve public names
and import compatibility.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- `alg:incidence-vector-bundle`: 𝒰_G is a finite S_G-module. -/
theorem incidenceRing_finite : G.coeffHom.toRingHom.Finite := by
  exact G.coeffHom_finite

/-- **Dimension in `alg:normal-cm`.** dim 𝒰_G=d_G=3m+n−τ. -/
theorem ringKrullDim_incidenceRing : ringKrullDim G.IncidenceRing = (G.dG : WithBot ℕ∞) := by
  exact G.incidenceRing_krullDim

/-- **Resolution length in `alg:resolution`.** Projective dimension over S_G is ρ. -/
theorem projectiveDimension_incidenceRing :
    letI := G.coeffHom.toRingHom.toAlgebra
    CategoryTheory.projectiveDimension (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) =
      (G.rho : WithBot ℕ∞) := by
  exact G.incidenceRing_projectiveDimension

end BPFixedPoints.Multigraph

