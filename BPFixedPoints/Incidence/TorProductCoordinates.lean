import BPFixedPoints.Incidence.ResolutionTorProduct

/-! # Transport Tor degrees and choose resolution representatives -/

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance torProductCoordinatesOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

/-- Canonical isomorphism between homological indices expressing the same natural number. -/
noncomputable def incidenceTorCast {p q : ℕ} (h : p = q) :
    G.incidenceTor p ≃ₗ[ℂ] G.incidenceTor q := by
  subst q
  exact LinearEquiv.refl ℂ _

@[simp] theorem incidenceTorToFull_cast {p q : ℕ} (h : p = q) (x : G.incidenceTor p) :
    G.incidenceTorToFull q (G.incidenceTorCast h x) = G.incidenceTorToFull p x := by
  subst q
  rfl

/-- Every Tor class is obtained by actual specialization of a free-resolution element. -/
theorem incFreeTermToTor_surjective (p : ℕ) : Function.Surjective (G.incFreeTermToTor p) := by
  intro x
  refine ⟨(G.incFreeTermBasis p).repr.symm
    (freeConstantLift (σ := IncCoeffIdx E) (G.incidenceTorEquivState p x)), ?_⟩
  apply (G.incidenceTorEquivState p).injective
  simp [incFreeTermToTor]

end BPFixedPoints.Multigraph
