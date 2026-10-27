import BPFixedPoints.Incidence.KoszulCech
import BPFixedPoints.Incidence.KoszulFaces
import BPFixedPoints.Incidence.CechFaceSigns
import BPFixedPoints.Incidence.PerturbationScalar
import BPFixedPoints.Incidence.PerturbationProjection

/-!
# Return local Koszul contractions to the full Čech module

Take the product of contractions to actual incidence quotients on every face
and transfer to the common total module. Its differential is exactly the
signed Koszul differential used in the first perturbation.
-/

namespace BPFixedPoints.Multigraph

set_option synthInstance.maxHeartbeats 100000

open CechProduct IncidencePerturbation Finsupp

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Product of the incidence coordinate rings of all faces. -/
abbrev IncQuotientCechModule := (q : V → Fin 3) → G.IncFaceRing q

noncomputable instance : Module ℂ G.IncQuotientCechModule :=
  Pi.module (V → Fin 3) G.IncFaceRing ℂ

/-- Local Koszul contraction with the sign convention of the total differential. -/
noncomputable def incSignedFaceContraction (q : V → Fin 3) :
    Contraction ℂ (Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)))
      (G.IncFaceRing q) :=
  (G.incFaceContraction q).smulInvolution ((-1 : ℂ) ^ faceDegree q) (by
    rw [← mul_pow]
    simp)

theorem incSignedFaceContraction_d (q : V → Fin 3)
    (x : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) :
    (G.incSignedFaceContraction q).d x =
      (-1 : ℂ) ^ faceDegree q • Koszul.differential (G.incFaceEquation q) x := by
  change (-1 : ℂ) ^ faceDegree q • (G.incFaceContraction q).d x = _
  rw [G.incFaceContraction_d]
  rfl

theorem incSignedFaceContraction_p (q : V → Fin 3)
    (x : Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))) :
    (G.incSignedFaceContraction q).p x = Ideal.Quotient.mk (G.incFaceIdeal q) (x ∅) :=
  G.incFaceContraction_p q x

/-- Transfer the product of local contractions to the Čech-monomial total module. -/
noncomputable def incKoszulContraction :
    Contraction ℂ (IncTotalModule (V := V) (E := E)) G.IncQuotientCechModule :=
  (Contraction.pi G.incSignedFaceContraction).congr
    (totalFaceEquiv ℂ (IncCoeffIdx E) E).symm (LinearEquiv.refl ℂ _)

theorem totalFaceEquiv_incKoszulPerturbation
    (x : IncTotalModule (V := V) (E := E)) (q : V → Fin 3) :
    totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulPerturbation x) q =
      (-1 : ℂ) ^ faceDegree q • Koszul.differential (G.incFaceEquation q)
        (totalFaceEquiv ℂ (IncCoeffIdx E) E x q) := by
  let F : IncTotalModule (V := V) (E := E) →ₗ[ℂ]
      Koszul.Space E (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :=
    (LinearMap.proj q).comp (totalFaceEquiv ℂ (IncCoeffIdx E) E).toLinearMap
  let P : IncCechModule (V := V) (E := E) →ₗ[ℂ]
      MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q) :=
    (LinearMap.proj q).comp (polynomialFaceEquiv ℂ (IncCoeffIdx E)).toLinearMap
  have hh : F.comp (G.incKoszulPerturbation.restrictScalars ℂ) =
      (-1 : ℂ) ^ faceDegree q •
        ((Koszul.differential (G.incFaceEquation q)).restrictScalars ℂ).comp F := by
    apply Finsupp.lhom_ext
    intro S w
    change totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulPerturbation (single S w)) q = _
    rw [G.incKoszulPerturbation_single, map_sum, Finset.sum_apply]
    change _ = (-1 : ℂ) ^ faceDegree q •
      Koszul.differential (G.incFaceEquation q)
        (totalFaceEquiv ℂ (IncCoeffIdx E) E (single S w) q)
    rw [totalFaceEquiv_single, Koszul.differential_single, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [totalFaceEquiv_single, polynomialFaceEquiv_sign]
    have hsign := Koszul.map_sign_smul (R := IncCoeffRing E)
      (A := MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))
      P.toAddMonoidHom S e (G.incEdgeAction e w)
    change polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (Koszul.sign (A := IncCoeffRing E) S e • G.incEdgeAction e w) q =
      Koszul.sign S e * polynomialFaceEquiv ℂ (IncCoeffIdx E) (G.incEdgeAction e w) q at hsign
    rw [hsign]
    have haction := G.polynomialFaceEquiv_incSection q e w
    change polynomialFaceEquiv ℂ (IncCoeffIdx E) (G.incEdgeAction e w) q =
      G.incFaceEquation q e * polynomialFaceEquiv ℂ (IncCoeffIdx E) w q at haction
    rw [haction, Finsupp.smul_single]
  exact LinearMap.congr_fun hh x

/-- The second contraction's differential agrees with the first perturbation's Koszul differential. -/
theorem incKoszulContraction_d :
    G.incKoszulContraction.d = G.incKoszulPerturbation.restrictScalars ℂ := by
  apply LinearMap.ext
  intro x
  apply (totalFaceEquiv ℂ (IncCoeffIdx E) E).injective
  funext q
  rw [incKoszulContraction, Contraction.congr_d_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  change (G.incSignedFaceContraction q).d
      (totalFaceEquiv ℂ (IncCoeffIdx E) E x q) = _
  rw [G.incSignedFaceContraction_d]
  exact (G.totalFaceEquiv_incKoszulPerturbation x q).symm

/-- Projection to local quotients applies the actual quotient map to the empty exterior coefficient. -/
theorem incKoszulContraction_p (x : IncTotalModule (V := V) (E := E)) (q : V → Fin 3) :
    G.incKoszulContraction.p x q =
      Ideal.Quotient.mk (G.incFaceIdeal q) (polynomialFaceEquiv ℂ (IncCoeffIdx E) (x ∅) q) := by
  rw [incKoszulContraction, Contraction.congr_p_apply]
  exact G.incSignedFaceContraction_p q _

end BPFixedPoints.Multigraph
