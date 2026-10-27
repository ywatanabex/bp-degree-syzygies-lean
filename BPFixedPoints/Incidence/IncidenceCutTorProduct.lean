import BPFixedPoints.Incidence.IncidenceCutTorGrading
import BPFixedPoints.Incidence.IteratedGradedProduct
import BPFixedPoints.Incidence.TorProductCoordinates
import BPFixedPoints.Incidence.ResolutionTorProductGrading

/-! # Multiplication on actual Tor after parameter cuts -/

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

/-- The actual residue class of an element of the original resolution, after cutting. -/
noncomputable def incidenceCutResolutionClass (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceParameterCutTor a I hI p := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  exact G.incidenceCutFreeToTor a I hI ha p
    (baseChangeUnit (k := ℂ) (σ := IncCoeffIdx E)
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x)

/-- The existing Tor comparison agrees with actual tensor specialization on representatives. -/
theorem incidenceParameterCutTorEquiv_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.incidenceParameterCutTorEquiv a I hI ha p (G.incidenceCutResolutionClass a I hI ha p x) =
      G.incFreeTermToTor p x := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  let f := G.incidenceParameterTorEquivState a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e he
  let z := baseChangeFreeToResidue (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
    e he (G.incFreeTermBasis p)
    (baseChangeUnit (k := ℂ) (σ := IncCoeffIdx E)
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) x)
  have h := (G.incidenceTorEquivState p).apply_symm_apply (f (f.symm z))
  have h' := f.apply_symm_apply z
  have hz := baseChangeFreeToResidue_unit (k := ℂ) (σ := IncCoeffIdx E) (M := G.IncFreeTerm p)
    (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
    e he (G.incFreeTermBasis p) x
  have ho := (G.incidenceTorEquivState p).apply_symm_apply (freeAtOrigin ((G.incFreeTermBasis p).repr x))
  apply (G.incidenceTorEquivState p).injective
  exact ((h.trans h').trans hz).trans ho.symm

/-- Every actual Tor class after a cut has a representative in the original free term. -/
theorem incidenceCutResolutionClass_surjective (p : ℕ) :
    Function.Surjective (G.incidenceCutResolutionClass a I hI ha p) := by
  intro y
  obtain ⟨x, hx⟩ := G.incFreeTermToTor_surjective p (G.incidenceParameterCutTorEquiv a I hI ha p y)
  refine ⟨x, ?_⟩
  apply (G.incidenceParameterCutTorEquiv a I hI ha p).injective
  exact (G.incidenceParameterCutTorEquiv_class a I hI ha p x).trans hx

/-- Specialize the scalar-extended original multiplication lift on the actual changed resolution. -/
noncomputable def incidenceCutLiftProduct (μ : G.IncResolutionMultiplication) (p q : ℕ) :
    G.incidenceParameterCutTor a I hI p →ₗ[ℂ]
      G.incidenceParameterCutTor a I hI q →ₗ[ℂ] G.incidenceParameterCutTor a I hI (p + q) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  letI : Algebra (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ℂ := e.toAlgebra
  exact ((iteratedGradedProduct
      (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))
      (k := ℂ) μ.toGradedFreePairing p q).compl₁₂
      (G.incidenceParameterTorIsoFreeTerm a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha p e he).hom.hom
      (G.incidenceParameterTorIsoFreeTerm a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha q e he).hom.hom).compr₂
    (G.incidenceParameterTorIsoFreeTerm a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha (p + q) e he).inv.hom

/-- On actual residue classes the extended multiplication is the original lift. -/
theorem incidenceCutLiftProduct_on_classes (μ : G.IncResolutionMultiplication) (p q : ℕ)
    (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    G.incidenceCutLiftProduct a I hI ha μ p q
      (G.incidenceCutResolutionClass a I hI ha p x)
      (G.incidenceCutResolutionClass a I hI ha q y) =
      G.incidenceCutResolutionClass a I hI ha (p + q)
        ⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩ := by
  letI := G.incidenceCoefficientParameterAlgebra a
  let R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  letI : Algebra R ℂ := e.toAlgebra
  let f n := (G.incidenceParameterTorIsoFreeTerm a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha n e he).toLinearEquiv
  have hx : f p (G.incidenceCutResolutionClass a I hI ha p x) =
      (1 : ℂ) ⊗ₜ[R,e] ((1 : R) ⊗ₜ[IncCoeffRing E] x) :=
    G.incidenceCutFreeToTor_eq_tmul a I hI ha p ((1 : R) ⊗ₜ[IncCoeffRing E] x)
  have hy : f q (G.incidenceCutResolutionClass a I hI ha q y) =
      (1 : ℂ) ⊗ₜ[R,e] ((1 : R) ⊗ₜ[IncCoeffRing E] y) :=
    G.incidenceCutFreeToTor_eq_tmul a I hI ha q ((1 : R) ⊗ₜ[IncCoeffRing E] y)
  let z : G.IncFreeTerm (p + q) := ⟨μ.mul x.val y.val, μ.homogeneous p q x.property y.property⟩
  have hz : f (p + q) (G.incidenceCutResolutionClass a I hI ha (p + q) z) =
      (1 : ℂ) ⊗ₜ[R,e] ((1 : R) ⊗ₜ[IncCoeffRing E] z) :=
    G.incidenceCutFreeToTor_eq_tmul a I hI ha (p + q) ((1 : R) ⊗ₜ[IncCoeffRing E] z)
  apply (f (p + q)).injective
  change f (p + q) ((f (p + q)).symm
    (iteratedGradedProduct (R := R) (k := ℂ) μ.toGradedFreePairing p q
      (f p (G.incidenceCutResolutionClass a I hI ha p x))
      (f q (G.incidenceCutResolutionClass a I hI ha q y)))) = _
  rw [LinearEquiv.apply_symm_apply, hx, hy, hz]
  exact iteratedGradedProduct_unit_tmul μ.toGradedFreePairing p q x y

/-- The actual coefficient-extension product is preserved by the existing Tor comparison. -/
theorem incidenceCutLiftProduct_compatible (μ : G.IncResolutionMultiplication) (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) (y : G.incidenceParameterCutTor a I hI q) :
    G.incidenceParameterCutTorEquiv a I hI ha (p + q)
      (G.incidenceCutLiftProduct a I hI ha μ p q x y) =
      G.incidenceTorProduct p q (G.incidenceParameterCutTorEquiv a I hI ha p x)
        (G.incidenceParameterCutTorEquiv a I hI ha q y) := by
  obtain ⟨u, rfl⟩ := G.incidenceCutResolutionClass_surjective a I hI ha p x
  obtain ⟨v, rfl⟩ := G.incidenceCutResolutionClass_surjective a I hI ha q y
  rw [G.incidenceCutLiftProduct_on_classes, G.incidenceParameterCutTorEquiv_class,
    G.incidenceParameterCutTorEquiv_class, G.incidenceParameterCutTorEquiv_class,
    G.incidenceTorProduct_eq_of_lift μ]
  exact (μ.torProduct_on_classes p q u v).symm

/-- Changing the original multiplication lift has no effect after a cut and specialization. -/
theorem incidenceCutLiftProduct_eq (μ ν : G.IncResolutionMultiplication) (p q : ℕ) :
    G.incidenceCutLiftProduct a I hI ha μ p q = G.incidenceCutLiftProduct a I hI ha ν p q := by
  ext x y
  apply (G.incidenceParameterCutTorEquiv a I hI ha (p + q)).injective
  rw [G.incidenceCutLiftProduct_compatible, G.incidenceCutLiftProduct_compatible]

/-- The multiplication computed by the scalar-extended resolution of the actual cut module. -/
noncomputable def incidenceCutTorProduct (p q : ℕ) :
    G.incidenceParameterCutTor a I hI p →ₗ[ℂ]
      G.incidenceParameterCutTor a I hI q →ₗ[ℂ] G.incidenceParameterCutTor a I hI (p + q) :=
  G.incidenceCutLiftProduct a I hI ha G.incidenceStandardMultiplication p q

/-- The existing comparison with original Tor is multiplicative. -/
theorem incidenceParameterCutTorEquiv_mul (p q : ℕ)
    (x : G.incidenceParameterCutTor a I hI p) (y : G.incidenceParameterCutTor a I hI q) :
    G.incidenceParameterCutTorEquiv a I hI ha (p + q) (G.incidenceCutTorProduct a I hI ha p q x y) =
      G.incidenceTorProduct p q (G.incidenceParameterCutTorEquiv a I hI ha p x)
        (G.incidenceParameterCutTorEquiv a I hI ha q y) :=
  G.incidenceCutLiftProduct_compatible a I hI ha G.incidenceStandardMultiplication p q x y

/-- The actual cut product adds natural internal degrees as well as homological degrees. -/
theorem incidenceCutTorProduct_internal_degree (p q b c : ℕ)
    {x : G.incidenceParameterCutTor a I hI p} {y : G.incidenceParameterCutTor a I hI q}
    (hx : x ∈ G.incidenceCutTorInternalPiece a I hI ha p b)
    (hy : y ∈ G.incidenceCutTorInternalPiece a I hI ha q c) :
    G.incidenceCutTorProduct a I hI ha p q x y ∈
      G.incidenceCutTorInternalPiece a I hI ha (p+q) (b+c) := by
  apply (G.incidenceParameterCutTorEquiv_internal a I hI ha (p+q) (b+c) _).mpr
  rw [G.incidenceParameterCutTorEquiv_mul]
  exact G.incidenceTorProduct_internal_degree p q b c
    ((G.incidenceParameterCutTorEquiv_internal a I hI ha p b x).mp hx)
    ((G.incidenceParameterCutTorEquiv_internal a I hI ha q c y).mp hy)

end BPFixedPoints.Multigraph
