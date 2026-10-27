import BPFixedPoints.Incidence.IncidenceCutTorProduct
import BPFixedPoints.Incidence.BaseChangeResidueNaturality

/-! # Multiplicative Tor comparisons induced by successive parameter quotients -/

namespace BPFixedPoints.Multigraph
open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)
  (I J : Ideal (MvPolynomial (Fin G.dG) ℂ))
  (hI : I ≤ RingHom.ker constantCoeff) (hJ : J ≤ RingHom.ker constantCoeff)
  (ha : a ∈ G.incidenceFiniteParameterLocus)

/-- The actual quotient-induced homomorphism of coefficient rings. -/
noncomputable def incidenceCutCoefficientMap (hIJ : I ≤ J) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) →ₐ[IncCoeffRing E]
      (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ J)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact Algebra.TensorProduct.map (AlgHom.id (IncCoeffRing E) (IncCoeffRing E))
    (Ideal.Quotient.factorₐ (MvPolynomial (Fin G.dG) ℂ) hIJ)

/-- Quotient-induced coefficient change preserves the specified residue origin. -/
theorem incidenceCutCoefficientMap_origin (hIJ : I ≤ J) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (G.incidenceParameterCutOrigin a J hJ).comp
      (G.incidenceCutCoefficientMap a I J hIJ).toRingHom = G.incidenceParameterCutOrigin a I hI := by
  letI := G.incidenceCoefficientParameterAlgebra a
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
      change constantCoeff s * constantCoeff t = constantCoeff s * constantCoeff t
      rfl
  | add x y hx hy =>
      change G.incidenceParameterCutOrigin a J hJ (G.incidenceCutCoefficientMap a I J hIJ (x+y)) =
        G.incidenceParameterCutOrigin a I hI (x+y)
      rw [map_add, map_add, map_add]
      exact congrArg₂ (· + ·) hx hy

/-- Comparison in actual minimal-resolution residue coordinates. Naturality below
identifies it with specialization of the quotient-induced coefficient map. -/
noncomputable def incidenceCutTorComparison (p : ℕ) :
    G.incidenceParameterCutTor a I hI p ≃ₗ[ℂ] G.incidenceParameterCutTor a J hJ p :=
  (G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p
    (G.incidenceParameterCutOrigin a I hI)
    (G.incidenceParameterCoefficientOrigin_compatible a _ _ _)).trans
  (G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ J) ha p
    (G.incidenceParameterCutOrigin a J hJ)
    (G.incidenceParameterCoefficientOrigin_compatible a _ _ _)).symm

/-- Agreement with the existing comparison to original Tor. -/
theorem incidenceCutTorComparison_compatible (p : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) :
    G.incidenceParameterCutTorEquiv a J hJ ha p (G.incidenceCutTorComparison a I J hI hJ ha p x) =
      G.incidenceParameterCutTorEquiv a I hI ha p x := by
  change (G.incidenceTorEquivState p).symm
    ((G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ J) ha p _ _)
      ((G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ J) ha p _ _).symm
        ((G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p _ _) x))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The comparison is induced, on every free representative, by the actual
coefficient quotient, rather than only being an abstract vector-space isomorphism. -/
theorem incidenceCutTorComparison_natural (hIJ : I ≤ J) (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) J
    ∀ x, G.incidenceCutTorComparison a I J hI hJ ha p (G.incidenceCutFreeToTor a I hI ha p x) =
      G.incidenceCutFreeToTor a J hJ ha p
        (coefficientTermMap (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
          (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
          (R' := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ J))
          (G.incidenceCutCoefficientMap a I J hIJ) x) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) J
  intro x
  let ei := G.incidenceParameterCutOrigin a I hI
  let ej := G.incidenceParameterCutOrigin a J hJ
  let hi := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  let hj := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ J)
    (G.incidenceParameterQuotientOrigin J hJ) (G.incidenceParameterQuotientOrigin_compatible J hJ)
  let fi := G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p ei hi
  let fj := G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ J) ha p ej hj
  have hfi : ∀ z, fi (G.incidenceCutFreeToTor a I hI ha p z) =
      baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
        (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
        ei hi (G.incFreeTermBasis p) z := fun z => fi.apply_symm_apply _
  have hfj : ∀ z, fj (G.incidenceCutFreeToTor a J hJ ha p z) =
      baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
        (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ J))
        ej hj (G.incFreeTermBasis p) z := fun z => fj.apply_symm_apply _
  apply fj.injective
  change fj (fj.symm (fi (G.incidenceCutFreeToTor a I hI ha p x))) = _
  rw [LinearEquiv.apply_symm_apply, hfi, hfj]
  have hn := (baseChangeFreeToResidue_natural (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
          (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
          (R' := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ J))
          (G.incidenceCutCoefficientMap a I J hIJ)
    ei hi ej hj (G.incidenceCutCoefficientMap_origin a I J hI hJ hIJ) (G.incFreeTermBasis p) x)
  exact hn.symm

/-- Every parameter-quotient comparison preserves the actual scalar-extension product. -/
theorem incidenceCutTorComparison_mul (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) (y : G.incidenceParameterCutTor a I hI q) :
    G.incidenceCutTorComparison a I J hI hJ ha (p+q) (G.incidenceCutTorProduct a I hI ha p q x y) =
      G.incidenceCutTorProduct a J hJ ha p q
        (G.incidenceCutTorComparison a I J hI hJ ha p x)
        (G.incidenceCutTorComparison a I J hI hJ ha q y) := by
  apply (G.incidenceParameterCutTorEquiv a J hJ ha (p+q)).injective
  rw [G.incidenceCutTorComparison_compatible, G.incidenceParameterCutTorEquiv_mul,
    G.incidenceParameterCutTorEquiv_mul, G.incidenceCutTorComparison_compatible,
    G.incidenceCutTorComparison_compatible]

/-- The comparison also preserves the natural internal components. -/
theorem incidenceCutTorComparison_internal (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) :
    G.incidenceCutTorComparison a I J hI hJ ha p x ∈ G.incidenceCutTorInternalPiece a J hJ ha p q ↔
      x ∈ G.incidenceCutTorInternalPiece a I hI ha p q := by
  rw [G.incidenceParameterCutTorEquiv_internal, G.incidenceParameterCutTorEquiv_internal]
  rw [G.incidenceCutTorComparison_compatible]

/-- The comparisons compose independently of intermediate cuts. -/
theorem incidenceCutTorComparison_trans
    (K : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hK : K ≤ RingHom.ker constantCoeff)
    (p : ℕ) (x : G.incidenceParameterCutTor a I hI p) :
    G.incidenceCutTorComparison a J K hJ hK ha p (G.incidenceCutTorComparison a I J hI hJ ha p x) =
      G.incidenceCutTorComparison a I K hI hK ha p x := by
  apply (G.incidenceParameterCutTorEquiv a K hK ha p).injective
  rw [G.incidenceCutTorComparison_compatible, G.incidenceCutTorComparison_compatible,
    G.incidenceCutTorComparison_compatible]

/-- Every original free representative defines compatible classes in all cuts. -/
theorem incidenceCutTorComparison_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceCutTorComparison a I J hI hJ ha p (G.incidenceCutResolutionClass a I hI ha p x) =
      G.incidenceCutResolutionClass a J hJ ha p x := by
  apply (G.incidenceParameterCutTorEquiv a J hJ ha p).injective
  rw [G.incidenceCutTorComparison_compatible, G.incidenceParameterCutTorEquiv_class,
    G.incidenceParameterCutTorEquiv_class]

end BPFixedPoints.Multigraph
