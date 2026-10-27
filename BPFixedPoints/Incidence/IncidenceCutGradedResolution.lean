import BPFixedPoints.Incidence.IncidenceSectionGrading
import BPFixedPoints.Incidence.GradedTensorParameterQuotient

/-! # Graded exactness and the natural augmentation after parameter cuts -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local instance] MvPolynomial.gradedAlgebra

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)
  (I : Ideal (MvPolynomial (Fin G.dG) ℂ))

noncomputable local instance cutGradedCoefficientAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

/-- The natural components of the scalar-extended incidence ring. -/
noncomputable def incidenceCutRingPiece (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    Submodule ℂ ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncidenceRing) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  exact (G.incidenceCoefficientPiece q).map
    (baseChangeUnit (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncidenceRing) (R := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))))

theorem incidenceCutAugmentation_degree (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ x ∈ G.incidenceCutFreePiece a I 0 q,
      G.incResolutionAugmentation.baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x ∈ G.incidenceCutRingPiece a I q := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  intro x hx
  rw [G.incidenceCutFreePiece_image] at hx
  have h := baseChange_image_homogeneous (k := ℂ) (σ := IncCoeffIdx E)
    (M := G.IncFreeTerm 0) (N := G.IncidenceRing) (R := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)))
    G.incResolutionAugmentation (G.incFreeTermInternalPiece 0 q) (G.incidenceCoefficientPiece q)
    (fun y hy => G.incResolutionAugmentation_coefficient_degree q y
      ((G.mem_incFreeTermInternalPiece_iff 0 q y).mp hy)) hx
  exact h

theorem incidenceCutAugmentation_graded_surjective (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ u ∈ G.incidenceCutRingPiece a I q,
      ∃ x ∈ G.incidenceCutFreePiece a I 0 q,
        G.incResolutionAugmentation.baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x = u := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  rintro u ⟨v, hv, rfl⟩
  obtain ⟨x, hx, rfl⟩ := G.incResolutionAugmentation_graded_surjective q v hv
  refine ⟨baseChangeUnit (k := ℂ) (σ := IncCoeffIdx E) (R := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))) x, ?_, rfl⟩
  rw [G.incidenceCutFreePiece_image]
  exact ⟨x, hx, rfl⟩

/-- The image components agree with the natural grading of the actual quotient ring. -/
theorem incidenceCutRingPiece_quotient (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := G.incidenceParameterAlgebra a
    letI := G.incidenceCoefficientParameter_tower a
    letI := @Algebra.TensorProduct.instCommRing (IncCoeffRing E) (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) G.IncidenceRing
      inferInstance inferInstance inferInstance inferInstance inferInstance
    letI := tensorParameterQuotientGroundAlgebra (k := ℂ) (S := IncCoeffRing E) (U := G.IncidenceRing) I
    letI := parameterQuotientGroundModule (k := ℂ) (U := G.IncidenceRing) I
    (G.incidenceCutRingPiece a I q).map
      (tensorParameterQuotientAlgEquiv (k := ℂ) (S := IncCoeffRing E) (U := G.IncidenceRing) I).toLinearMap =
      gradedQuotientPiece G.incidenceCoefficientPiece
        (I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) q := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := G.incidenceParameterAlgebra a
  letI := G.incidenceCoefficientParameter_tower a
  letI := @Algebra.TensorProduct.instCommRing (IncCoeffRing E) (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) G.IncidenceRing
    inferInstance inferInstance inferInstance inferInstance inferInstance
  letI := tensorParameterQuotientGroundAlgebra (k := ℂ) (S := IncCoeffRing E) (U := G.IncidenceRing) I
  letI := parameterQuotientGroundModule (k := ℂ) (U := G.IncidenceRing) I
  have h := tensorParameterQuotient_piece (k := ℂ) (S := IncCoeffRing E) (U := G.IncidenceRing)
    I G.incidenceCoefficientPiece q
  exact h

/-- The linear section ideal is homogeneous for the original incidence grading. -/
theorem incidenceParameterCoordinateIdeal_incidence_homogeneous (r : ℕ) :
    letI := G.incidenceCoefficientGradedAlgebra
    letI := G.incidenceParameterAlgebra a
    ((G.incidenceParameterCoordinateIdeal r).map
      (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)).IsHomogeneous G.incidenceCoefficientPiece := by
  letI := G.incidenceParameterAlgebra a
  letI := G.incidenceCoefficientGradedAlgebra
  unfold incidenceParameterCoordinateIdeal
  rw [Ideal.map_ofList]
  apply Ideal.homogeneous_span
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take ht)
  refine ⟨1, ?_⟩
  change G.incidenceParameterHom a (X j) ∈ _
  rw [G.incidenceParameterHom_X]
  exact G.incidenceParameterForm_mem a j

variable (ha : a ∈ G.incidenceFiniteParameterLocus)
  (hI : letI := G.incidenceCoefficientParameterAlgebra a
    (I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E))).IsHomogeneous
      (homogeneousSubmodule (IncCoeffIdx E) ℂ))

include ha hI in
theorem incidenceCutDifferential_graded_exact (p q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ x ∈ G.incidenceCutFreePiece a I (p + 1) q,
      (G.incFreeTermDifferential p).baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x = 0 →
      ∃ y ∈ G.incidenceCutFreePiece a I (p + 2) q,
        (G.incFreeTermDifferential (p + 1)).baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) y = x := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  intro x hx hd
  have hr : x ∈ LinearMap.range ((G.incFreeTermDifferential (p + 1)).baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))) := by
    rw [G.incidenceParameterBaseChange_exact a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I) p,
      LinearMap.mem_ker]
    exact hd
  have h := exists_homogeneous_preimage (k := ℂ)
    (M := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncFreeTerm (p + 2))
    (N := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncFreeTerm (p + 1))
    (G.incidenceCutFreePiece a I (p + 2)) (G.incidenceCutFreePiece a I (p + 1))
    (G.iSup_incidenceCutFreePiece a I hI (p + 2))
    (G.iSupIndep_incidenceCutFreePiece a I hI (p + 1))
    (baseChangeGroundLinear (k := ℂ) (σ := IncCoeffIdx E) (R := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)))
      (M := G.IncFreeTerm (p + 2)) (N := G.IncFreeTerm (p + 1)) (G.incFreeTermDifferential (p + 1)))
    (fun n y hy => G.incidenceCutDifferential_degree a I (p + 1) n y hy) q hx hr
  exact h

include hI in
/-- Exactness at the augmentation also holds in each natural internal degree. -/
theorem incidenceCutAugmentation_graded_exact (q : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ x ∈ G.incidenceCutFreePiece a I 0 q,
      G.incResolutionAugmentation.baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x = 0 →
      ∃ y ∈ G.incidenceCutFreePiece a I 1 q,
        (G.incFreeTermDifferential 0).baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) y = x := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  intro x hx hd
  have he : Function.Exact (G.incFreeTermDifferential 0) G.incResolutionAugmentation := by
    intro y
    exact (SetLike.ext_iff.mp G.incFreeTermDifferential_augmentation_exact y).symm
  have ht := lTensor_exact (R := IncCoeffRing E)
    (M := G.IncFreeTerm 1) (N := G.IncFreeTerm 0) (P := G.IncidenceRing)
    (f := G.incFreeTermDifferential 0) (g := G.incResolutionAugmentation)
    (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) he G.incResolutionAugmentation_surjective
  have hr : x ∈ LinearMap.range ((G.incFreeTermDifferential 0).baseChange (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))) :=
    (ht x).mp hd
  have h := exists_homogeneous_preimage (k := ℂ)
    (M := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncFreeTerm 1)
    (N := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E] G.IncFreeTerm 0)
    (G.incidenceCutFreePiece a I 1) (G.incidenceCutFreePiece a I 0)
    (G.iSup_incidenceCutFreePiece a I hI 1) (G.iSupIndep_incidenceCutFreePiece a I hI 0)
    (baseChangeGroundLinear (k := ℂ) (σ := IncCoeffIdx E) (R := (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)))
      (M := G.IncFreeTerm 1) (N := G.IncFreeTerm 0) (G.incFreeTermDifferential 0))
    (fun n y hy => G.incidenceCutDifferential_degree a I 0 n y hy) q hx hr
  exact h

end BPFixedPoints.Multigraph
