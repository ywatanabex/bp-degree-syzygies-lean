import BPFixedPoints.Incidence.IncidenceSectionTor
import BPFixedPoints.Incidence.TensorQuotientGrading
import BPFixedPoints.Incidence.GradedBaseChangeFree

/-! # The natural coefficient and free-term gradings after linear incidence cuts -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] MvPolynomial.gradedAlgebra

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

theorem incidenceParameterCoordinateIdeal_coefficient_homogeneous (r : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ((G.incidenceParameterCoordinateIdeal r).map
      (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E))).IsHomogeneous
        (homogeneousSubmodule (IncCoeffIdx E) ℂ) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  unfold incidenceParameterCoordinateIdeal
  rw [Ideal.map_ofList]
  apply Ideal.homogeneous_span
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take ht)
  refine ⟨1, ?_⟩
  change (aeval (polynomialLinearForm ∘ G.incidenceCoefficientParameterVector a)) (X i) ∈ _
  rw [aeval_X, Function.comp_apply, G.incidenceCoefficientParameterVector_form]
  exact linearParameterForm_mem (homogeneousSubmodule (IncCoeffIdx E) ℂ) X
    (fun j => isHomogeneous_X ℂ j) a i

variable (I : Ideal (MvPolynomial (Fin G.dG) ℂ))

/-- The homogeneous pieces of the cut coefficient ring, as images of the original pieces. -/
noncomputable def incidenceCutCoefficientPiece (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    Submodule ℂ (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact gradedImagePiece (k := ℂ) (A := IncCoeffRing E)
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
    (homogeneousSubmodule (IncCoeffIdx E) ℂ)
    (tensorQuotientCoefficientHom (k := ℂ) (S := IncCoeffRing E) I) q

/-- The actual changed free term, with the natural coefficient image grading and original shifts. -/
noncomputable def incidenceCutFreePiece (p q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    Submodule ℂ ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ]
      (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncFreeTerm p) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  exact baseChangeFreePiece (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) (G.incFreeTermBasis p)
    (fun b => G.incResolutionInternalDegree b.val) q

theorem incidenceCutFreePiece_image (p q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    G.incidenceCutFreePiece a I p q = (G.incFreeTermInternalPiece p q).map
      (baseChangeUnit (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p) (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ]
        (MvPolynomial (Fin G.dG) ℂ ⧸ I))) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  have h := baseChangeFreePiece_image (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) (G.incFreeTermBasis p)
    (fun b => G.incResolutionInternalDegree b.val) (q : ℤ)
  exact h

variable (hI : letI := G.incidenceCoefficientParameterAlgebra a
  (I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E))).IsHomogeneous
    (homogeneousSubmodule (IncCoeffIdx E) ℂ))

include hI in
theorem iSup_incidenceCutFreePiece (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    (⨆ q, G.incidenceCutFreePiece a I p q) = ⊤ := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  letI : GradedAlgebra (gradedImagePiece (k := ℂ) (A := IncCoeffRing E)
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
      (homogeneousSubmodule (IncCoeffIdx E) ℂ)
      (IsScalarTower.toAlgHom ℂ (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)))) :=
    tensorQuotientGradedAlgebra (k := ℂ) (T := MvPolynomial (Fin G.dG) ℂ)
      (S := IncCoeffRing E) I (homogeneousSubmodule (IncCoeffIdx E) ℂ) hI
  have h := iSup_baseChangeFreePiece (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) (G.incFreeTermBasis p)
    (fun b => G.incResolutionInternalDegree b.val)
  exact h

include hI in
theorem iSupIndep_incidenceCutFreePiece (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    iSupIndep (G.incidenceCutFreePiece a I p) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  letI : GradedAlgebra (gradedImagePiece (k := ℂ) (A := IncCoeffRing E)
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
      (homogeneousSubmodule (IncCoeffIdx E) ℂ)
      (IsScalarTower.toAlgHom ℂ (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)))) :=
    tensorQuotientGradedAlgebra (k := ℂ) (T := MvPolynomial (Fin G.dG) ℂ)
      (S := IncCoeffRing E) I (homogeneousSubmodule (IncCoeffIdx E) ℂ) hI
  have h := iSupIndep_baseChangeFreePiece (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) (G.incFreeTermBasis p)
    (fun b => G.incResolutionInternalDegree b.val)
  exact h

/-- The changed differentials preserve the natural internal degree. -/
theorem incidenceCutDifferential_degree (p q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    ∀ x ∈ G.incidenceCutFreePiece a I (p + 1) q,
      (G.incFreeTermDifferential p).baseChange
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x ∈
          G.incidenceCutFreePiece a I p q := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  intro x hx
  rw [G.incidenceCutFreePiece_image] at hx ⊢
  exact baseChange_image_homogeneous (k := ℂ) (σ := IncCoeffIdx E)
    (M := G.IncFreeTerm (p + 1)) (N := G.IncFreeTerm p)
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) (G.incFreeTermDifferential p) (G.incFreeTermInternalPiece (p + 1) q) (G.incFreeTermInternalPiece p q)
    (fun y hy => G.incFreeTermDifferential_internal_degree p q hy) hx

end BPFixedPoints.Multigraph
