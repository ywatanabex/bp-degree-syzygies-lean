import BPFixedPoints.Incidence.IncidenceParameterTor
import BPFixedPoints.Incidence.IncidenceParameterOrigin
import BPFixedPoints.Incidence.IncidenceParameterBaseChange
import BPFixedPoints.Incidence.TensorParameterQuotient

/-! # Actual Tor invariance for parameter cuts through the coefficient origin -/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

noncomputable local instance coefficientCutTorAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

/-- The changed coefficient ring is the original coefficient ring modulo the parameter relations. -/
noncomputable def incidenceParameterCoefficientCutEquiv
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (IncCoeffRing E ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E))) ≃ₐ[IncCoeffRing E]
      IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot (IncCoeffRing E) I

/-- The module resolved by the changed complex is the actual quotient of the incidence ring. -/
noncomputable def incidenceParameterCutResolvedRingEquiv
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := G.incidenceParameterAlgebra a
    letI : Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra
    letI := G.incidenceCoefficientParameter_tower a
    letI := @Algebra.TensorProduct.instCommRing (IncCoeffRing E)
      (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) G.IncidenceRing
      inferInstance inferInstance inferInstance inferInstance inferInstance
    ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E]
      G.IncidenceRing) ≃+* (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := G.incidenceParameterAlgebra a
  haveI := G.incidenceCoefficientParameter_tower a
  letI : Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra
  letI := @Algebra.TensorProduct.instCommRing (IncCoeffRing E)
    (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) G.IncidenceRing
    inferInstance inferInstance inferInstance inferInstance inferInstance
  exact tensorParameterQuotient (S := IncCoeffRing E) (U := G.IncidenceRing) I

variable (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hI : I ≤ RingHom.ker constantCoeff)

/-- The compatible origin of the cut coefficient ring. -/
noncomputable def incidenceParameterCutOrigin :
    letI := G.incidenceCoefficientParameterAlgebra a
    IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I) →+* ℂ :=
  G.incidenceParameterCoefficientOrigin a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)

/-- This is the actual derived functor for the cut coefficient ring and the cut incidence module. -/
noncomputable def incidenceParameterCutTor (p : ℕ) : ModuleCat ℂ :=
  G.incidenceParameterTor a (MvPolynomial (Fin G.dG) ℂ ⧸ I) p (G.incidenceParameterCutOrigin a I hI)

/-- Cutting by any parameter relations through the origin preserves every actual Tor space. -/
noncomputable def incidenceParameterCutTorEquiv (ha : a ∈ G.incidenceFiniteParameterLocus) (p : ℕ) :
    G.incidenceParameterCutTor a I hI p ≃ₗ[ℂ] G.incidenceTor p :=
  G.incidenceParameterTorEquiv a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p
    (G.incidenceParameterCutOrigin a I hI)
    (G.incidenceParameterCoefficientOrigin_compatible a _ _ _)

theorem finrank_incidenceParameterCutTor (ha : a ∈ G.incidenceFiniteParameterLocus) (p : ℕ) :
    Module.finrank ℂ (G.incidenceParameterCutTor a I hI p) =
      ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti p q :=
  (G.incidenceParameterCutTorEquiv a I hI ha p).finrank_eq.trans (G.finrank_incidenceTor p)

theorem sum_finrank_incidenceParameterCutTor (ha : a ∈ G.incidenceFiniteParameterLocus) :
    ∑ p ∈ Finset.range (Fintype.card E + 1),
      Module.finrank ℂ (G.incidenceParameterCutTor a I hI p) = G.Q := by
  simp_rw [G.finrank_incidenceParameterCutTor a I hI ha]
  exact G.sum_betti_eq_Q

end BPFixedPoints.Multigraph
