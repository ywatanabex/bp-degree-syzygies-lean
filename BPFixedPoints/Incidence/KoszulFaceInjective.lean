import BPFixedPoints.Incidence.KoszulTorusLaurent
import BPFixedPoints.Incidence.KoszulFaceFree

/-! # Injectivity of incidence-face quotient maps into the common torus -/

namespace BPFixedPoints.IncidenceLaurent

variable {V A B : Type*} [Fintype V] [CommRing A] [CommRing B]

theorem unitMonomial_map (f : A →* B) (u : V → Aˣ) (m : Multiplicative (V → ℤ)) :
    Units.map f (unitMonomial u m) = unitMonomial (fun v => Units.map f (u v)) m := by
  change Units.map f (∏ v, u v ^ m.toAdd v) = ∏ v, Units.map f (u v) ^ m.toAdd v
  simp only [map_prod, map_zpow]

end BPFixedPoints.IncidenceLaurent

namespace BPFixedPoints.CechProduct

open IncidenceLaurent

variable {V R A B : Type*} [Fintype V] [DecidableEq V]
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem faceEvaluate_comp (q : V → Fin 3) (u : V → Aˣ) (f : A →ₐ[R] B) :
    f.comp (faceEvaluate q u) =
      faceEvaluate q (fun v => Units.map f.toMonoidHom (u v)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    have h := congrArg Units.val
      (unitMonomial_map f.toMonoidHom u (Multiplicative.ofAdd (faceToInt q m)))
    change f ((unitMonomial u (Multiplicative.ofAdd (faceToInt q m))) : A) =
      ((unitMonomial (fun v => Units.map f.toMonoidHom (u v))
        (Multiplicative.ofAdd (faceToInt q m))) : B) at h
    simpa only [AlgHom.comp_apply, faceEvaluate_single, one_smul] using h
  · ext

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct IncidenceLaurent

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incTorusToLaurent_faceEvaluate (q : V → Fin 3) :
    (G.incTorusToLaurent (faceOrientation q)).comp (faceEvaluate q (G.incFaceVertexUnit q)) =
      AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (leftExponent.comp (faceToInt q)) := by
  rw [faceEvaluate_comp]
  have hu : (fun v => Units.map (G.incTorusToLaurent (faceOrientation q)).toMonoidHom
      (G.incFaceVertexUnit q v)) =
        fun v => monomialUnit (leftExponent (J := E × Fin 3) (Pi.single v 1)) :=
    funext (G.incTorusToLaurent_vertexUnit q)
  rw [hu, faceEvaluate_monomialUnits]

theorem faceFreeMap_bilinearFreeCoeff (q : V → Fin 3) (e : E) (α β : Fin 2) :
    faceFreeMap q (Koszul.bilinearFreeCoeff
      (fun j => faceVariable ℂ q (G.fst j)) (fun j => faceVariable ℂ q (G.snd j)) e α β) =
        polynomialMap (G.incFreeCoeff e α β) := by
  fin_cases α <;> fin_cases β <;>
    simp [Koszul.bilinearFreeCoeff, Koszul.bilinearTail, incFreeCoeff,
      faceFreeMap_X, faceFreeMap_C_variable]

/-- Each face torus map agrees with the free-coordinate embedding in the common Laurent ring. -/
theorem incFaceToLaurent_comp (q : V → Fin 3) :
    (G.incTorusToLaurent (faceOrientation q)).comp (G.incFaceToTorus q) =
      (faceFreeMap q).comp ((G.incFaceFreeEquiv q).restrictScalars ℂ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro r
    change G.incTorusToLaurent (faceOrientation q) (G.incFaceAmbientToTorus q (C r)) =
      faceFreeMap q (G.incFaceFreeEquiv q (Ideal.Quotient.mk _ (C r)))
    rw [G.incFaceFreeEquiv_C, faceFreeMap_C]
    rw [incFaceAmbientToTorus, facePolynomialEvaluate_C]
    exact AlgHom.congr_fun (G.incTorusToLaurent_faceEvaluate q) r
  · rintro ⟨e, α, β⟩
    change G.incTorusToLaurent (faceOrientation q)
        (G.incFaceToTorus q (Ideal.Quotient.mk _ (X (e, α, β)))) =
      faceFreeMap q (G.incFaceFreeEquiv q (Ideal.Quotient.mk _ (X (e, α, β))))
    rw [G.incFaceToTorus_X, G.incTorusToLaurent_coeff, G.incFaceFreeEquiv_X]
    exact (G.faceFreeMap_bilinearFreeCoeff q e _ _).symm

/-- Actual coordinate rings of all charts and overlaps inject into the common torus. -/
theorem incFaceToTorus_injective (q : V → Fin 3) :
    Function.Injective (G.incFaceToTorus q) := by
  intro x y h
  apply (G.incFaceFreeEquiv q).injective
  apply faceFreeMap_injective q
  have h' := congrArg (G.incTorusToLaurent (faceOrientation q)) h
  change ((G.incTorusToLaurent (faceOrientation q)).comp (G.incFaceToTorus q)) x =
    ((G.incTorusToLaurent (faceOrientation q)).comp (G.incFaceToTorus q)) y at h'
  rw [G.incFaceToLaurent_comp] at h'
  simpa using h'

end BPFixedPoints.Multigraph
