import BPFixedPoints.Incidence.CoefficientModule
import BPFixedPoints.Incidence.KoszulLocalModel
import BPFixedPoints.Incidence.KoszulFaceChartTorus

/-! # Torus evaluation of local Koszul projections is coefficient-linear -/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Exchange coefficients and face coordinates before evaluation; the result agrees with the original coefficient action. -/
theorem incFacePolynomialCoeff_eval (q : V → Fin 3) (r : IncCoeffRing E) :
    G.incFaceAmbientToTorus q (facePolynomialEquiv ℂ (IncCoeffIdx E) q
      (algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) q) r)) =
        G.incTorusCoeffHom r := by
  have h : (G.incFaceAmbientToTorus q).comp
      ((facePolynomialEquiv ℂ (IncCoeffIdx E) q).toAlgHom.comp
        (IsScalarTower.toAlgHom ℂ (IncCoeffRing E) (FaceRing (IncCoeffRing E) q))) =
          G.incTorusCoeffHom := by
    apply MvPolynomial.algHom_ext
    intro c
    change G.incFaceAmbientToTorus q (facePolynomialEquiv ℂ (IncCoeffIdx E) q
      (AddMonoidAlgebra.single 0 (X c))) = G.incTorusCoeffHom (X c)
    rw [facePolynomialEquiv_single_X, ← AddMonoidAlgebra.one_def, map_one, one_mul]
    simp only [incFaceAmbientToTorus, facePolynomialEvaluate_X, G.incTorusCoeffHom_X]
  exact AlgHom.congr_fun h r

/-- Arbitrary coefficient-polynomial actions become coefficient actions on the common torus. -/
theorem incFaceEval_smul (q : V → Fin 3) (r : IncCoeffRing E)
    (x : IncCechModule (V := V) (E := E)) :
    G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) (r • x) q) =
      G.incTorusCoeffHom r *
        G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) x q) := by
  rw [polynomialFaceEquiv_apply, map_smul, Pi.smul_apply, Algebra.smul_def,
    map_mul, map_mul, G.incFacePolynomialCoeff_eval, polynomialFaceEquiv_apply]

/-- Coefficient-linear map taking the empty exterior component and evaluating the specified face on the torus. -/
noncomputable def incFaceRawEval (q : V → Fin 3) :
    letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] G.IncTorusRing := by
  letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
  exact
    { toFun := fun x => G.incFaceAmbientToTorus q
        (polynomialFaceEquiv ℂ (IncCoeffIdx E) (x ∅) q)
      map_add' := by
        intro x y
        simp only [Finsupp.add_apply, map_add, Pi.add_apply]
      map_smul' := by
        intro r x
        change G.incFaceAmbientToTorus q
          (polynomialFaceEquiv ℂ (IncCoeffIdx E) (r • x ∅) q) =
            G.incTorusCoeffHom r *
              G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) (x ∅) q)
        exact G.incFaceEval_smul q r (x ∅) }

@[simp] theorem incFaceRawEval_apply (q : V → Fin 3)
    (x : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval q x =
      G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) (x ∅) q) := rfl

/-- Evaluation of the second contraction's projection is exactly this coefficient-linear map. -/
theorem incFaceRawEval_eq_projection (q : V → Fin 3)
    (x : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval q x = G.incFaceToTorus q (G.incKoszulContraction.p x q) := by
  rw [G.incKoszulContraction_p, G.incFaceToTorus_mk]
  rfl

/-- Every face-quotient evaluation kills Koszul boundaries. -/
theorem incFaceRawEval_koszul (q : V → Fin 3)
    (x : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval q (G.incKoszulPerturbation x) = 0 := by
  rw [G.incFaceRawEval_eq_projection]
  have h := LinearMap.congr_fun G.incKoszulContraction.p_d x
  change G.incKoszulContraction.p (G.incKoszulContraction.d x) = 0 at h
  rw [G.incKoszulContraction_d] at h
  change G.incKoszulContraction.p (G.incKoszulPerturbation x) = 0 at h
  rw [h]
  exact map_zero _

end BPFixedPoints.Multigraph
