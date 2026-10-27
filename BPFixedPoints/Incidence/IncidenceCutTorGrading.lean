import BPFixedPoints.Incidence.IncidenceSectionGrading
import BPFixedPoints.Incidence.GradedBaseChangeSpecialization

/-! # Natural internal components of actual Tor after incidence parameter cuts -/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)
  (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hI : I ≤ RingHom.ker constantCoeff)
  (ha : a ∈ G.incidenceFiniteParameterLocus)

/-- Specialize a changed free term into actual derived Tor, using its existing resolution isomorphism. -/
noncomputable def incidenceCutFreeToTor (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗[IncCoeffRing E]
      G.IncFreeTerm p) →ₗ[ℂ] G.incidenceParameterCutTor a I hI p := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  exact (G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e he).symm.toLinearMap.comp
    (baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) e he (G.incFreeTermBasis p))

/-- This map is the actual tensor specialization x -> 1 tensor x. -/
theorem incidenceCutFreeToTor_eq_tmul (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    let e := G.incidenceParameterCutOrigin a I hI
    letI : Algebra (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ℂ := e.toAlgebra
    ∀ x, (G.incidenceParameterTorIsoFreeTerm a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e
      (G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI))).hom
        (G.incidenceCutFreeToTor a I hI ha p x) = (1 : ℂ) ⊗ₜ[IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I), e] x := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  let e := G.incidenceParameterCutOrigin a I hI
  letI : Algebra (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ℂ := e.toAlgebra
  dsimp only
  intro x
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  let f := G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e he
  apply (((G.incidenceParameterBaseChangeBasis a (MvPolynomial (Fin G.dG) ℂ ⧸ I) p).baseChange ℂ).repr).injective
  have h := f.apply_symm_apply
    (baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
      (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
      e he (G.incFreeTermBasis p) x)
  have ht := baseChangeFreeToResidue_eq_tmul (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
    e he (G.incFreeTermBasis p) x
  exact h.trans ht.symm

/-- Internal components are images of natural homogeneous free parts under actual specialization. -/
noncomputable def incidenceCutTorInternalPiece (p q : ℕ) :
    Submodule ℂ (G.incidenceParameterCutTor a I hI p) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  exact (G.incidenceCutFreePiece a I p q).map (G.incidenceCutFreeToTor a I hI ha p)

theorem mem_incidenceCutTorInternalPiece_iff (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) :
    x ∈ G.incidenceCutTorInternalPiece a I hI ha p q ↔
      G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p
        (G.incidenceParameterCutOrigin a I hI) (G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)) x ∈
          Finsupp.supported ℂ ℂ {b | G.incResolutionInternalDegree b.val = q} := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  let f := G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e he
  have hp := baseChangeFreePiece_map_residue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) e he (G.incFreeTermBasis p)
    (fun b => G.incResolutionInternalDegree b.val) q
  constructor
  · rintro ⟨y, hy, rfl⟩
    change f (f.symm (baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) e he (G.incFreeTermBasis p) y)) ∈ _
    rw [LinearEquiv.apply_symm_apply, ← hp]
    exact ⟨y, hy, rfl⟩
  · intro hx
    rw [← hp] at hx
    obtain ⟨y, hy, heq⟩ := hx
    refine ⟨y, hy, ?_⟩
    apply f.injective
    change f (f.symm (baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (J := {b : G.IncResolutionBasis // G.incResolutionDegree b = p})
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) e he (G.incFreeTermBasis p) y)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact heq

/-- The previously constructed comparison preserves the natural internal components. -/
theorem incidenceParameterCutTorEquiv_internal (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) :
    x ∈ G.incidenceCutTorInternalPiece a I hI ha p q ↔
      G.incidenceParameterCutTorEquiv a I hI ha p x ∈ G.incidenceTorInternalPiece p q := by
  rw [G.mem_incidenceCutTorInternalPiece_iff, G.mem_incidenceTorInternalPiece_iff]
  simp only [incidenceParameterCutTorEquiv, incidenceParameterTorEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

noncomputable def incidenceCutTorInternalEquiv (p q : ℕ) :
    G.incidenceCutTorInternalPiece a I hI ha p q ≃ₗ[ℂ] G.incidenceTorInternalPiece p q := by
  let e := G.incidenceParameterCutTorEquiv a I hI ha p
  have he : (G.incidenceCutTorInternalPiece a I hI ha p q).map e.toLinearMap =
      G.incidenceTorInternalPiece p q := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (G.incidenceParameterCutTorEquiv_internal a I hI ha p q y).mp hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      apply (G.incidenceParameterCutTorEquiv_internal a I hI ha p q _).mpr
      simpa [e] using hx
  exact (e.submoduleMap _).trans (LinearEquiv.ofEq _ _ he)

theorem finrank_incidenceCutTorInternalPiece (p q : ℕ) :
    Module.finrank ℂ (G.incidenceCutTorInternalPiece a I hI ha p q) = G.betti p q :=
  (G.incidenceCutTorInternalEquiv a I hI ha p q).finrank_eq.trans
    (G.finrank_incidenceTorInternalPiece p q)

/-- Actual internal Tor components of each successive linear section. -/
noncomputable def incidenceSectionTorInternalPiece (r p q : ℕ) :
    Submodule ℂ (G.incidenceSectionTor a r p) :=
  G.incidenceCutTorInternalPiece a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) ha p q

/-- Every successive linear cut preserves the entire bigraded Betti table. -/
theorem finrank_incidenceSectionTorInternalPiece (r p q : ℕ) :
    Module.finrank ℂ (G.incidenceSectionTorInternalPiece a ha r p q) = G.betti p q :=
  G.finrank_incidenceCutTorInternalPiece a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) ha p q

end BPFixedPoints.Multigraph
