import BPFixedPoints.Incidence.KoszulFaceRing
import BPFixedPoints.Incidence.KoszulLaurentEvaluation

/-! # Evaluate Čech face coordinates at units -/

namespace BPFixedPoints

namespace CechProduct

open IncidenceLaurent

set_option linter.unusedSectionVars false

variable {V J R A : Type*} [Fintype V] [DecidableEq V]
  [CommRing R] [CommRing A] [Algebra R A]

/-- Substitute units for face vertex coordinates. -/
noncomputable def faceEvaluate (q : V → Fin 3) (u : V → Aˣ) : FaceRing R q →ₐ[R] A :=
  (evaluate u).comp (AddMonoidAlgebra.mapDomainAlgHom R R (faceToInt q))

@[simp] theorem faceEvaluate_single (q : V → Fin 3) (u : V → Aˣ)
    (m : FaceMonoid q) (r : R) :
    faceEvaluate q u (AddMonoidAlgebra.single m r) =
      r • (unitMonomial u (Multiplicative.ofAdd (faceToInt q m)) : A) := by
  simp [faceEvaluate]

@[simp] theorem faceEvaluate_variable (q : V → Fin 3) (u : V → Aˣ) (v : V) :
    faceEvaluate (R := R) q u (faceVariable R q v) = (u v : A) := by
  rw [faceVariable, faceEvaluate_single, faceToInt_vertex, unitMonomial_single]
  simp

/-- Evaluate face coordinates and free coefficients simultaneously. -/
noncomputable def facePolynomialEvaluate (q : V → Fin 3) (u : V → Aˣ) (c : J → A) :
    MvPolynomial J (FaceRing R q) →ₐ[R] A :=
  MvPolynomial.aevalTower (faceEvaluate q u) c

@[simp] theorem facePolynomialEvaluate_X (q : V → Fin 3) (u : V → Aˣ) (c : J → A) (j : J) :
    facePolynomialEvaluate (R := R) q u c (MvPolynomial.X j) = c j := by
  simp [facePolynomialEvaluate]

@[simp] theorem facePolynomialEvaluate_C (q : V → Fin 3) (u : V → Aˣ) (c : J → A)
    (r : FaceRing R q) :
    facePolynomialEvaluate q u c (MvPolynomial.C r) = faceEvaluate q u r := by
  simp [facePolynomialEvaluate]

variable {σ : Type*}

/-- Substitution of monomial units with integer exponents is the corresponding exponent map. -/
theorem faceEvaluate_monomialUnits (q : V → Fin 3)
    (T : (V → ℤ) →+ (σ → ℤ)) :
    faceEvaluate (R := R) q
      (fun v => monomialUnit (T (Pi.single v 1))) =
        AddMonoidAlgebra.mapDomainAlgHom R R (T.comp (faceToInt q)) := by
  apply AddMonoidAlgebra.algHom_ext
  · intro m
    rw [faceEvaluate_single]
    have h := unitMonomial_of_hom
      ((monomialUnitHom (R := R)).comp T.toMultiplicative) (faceToInt q m)
    change unitMonomial (fun v => monomialUnit (T (Pi.single v 1)))
      (Multiplicative.ofAdd (faceToInt q m)) = monomialUnit (T (faceToInt q m)) at h
    rw [h]
    simp
  · ext

@[simp] theorem chartFaceRingEquiv_symm_X (σ : V → Bool) (v : V) :
    (chartFaceRingEquiv (R := R) σ).symm (MvPolynomial.X v) =
      faceVariable R (chartFace σ) v := by
  apply (chartFaceRingEquiv (R := R) σ).injective
  simp

/-- Evaluation on an overlap-free face agrees with ordinary polynomial evaluation. -/
theorem faceEvaluate_chartFace (σ : V → Bool) (u : V → Aˣ) (r : FaceRing R (chartFace σ)) :
    faceEvaluate (chartFace σ) u r =
      MvPolynomial.aeval (fun v => (u v : A)) (chartFaceRingEquiv σ r) := by
  have h : (faceEvaluate (R := R) (chartFace σ) u).comp
      (chartFaceRingEquiv (R := R) σ).symm.toAlgHom =
        MvPolynomial.aeval (R := R) (fun v => (u v : A)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp
  have hh := AlgHom.congr_fun h (chartFaceRingEquiv σ r)
  simpa using hh

end CechProduct

namespace CechProduct

variable {V J R : Type*} [CommRing R]

/-- Extend vertex integer exponents by zero on the free-coefficient coordinates. -/
def leftExponent : (V → ℤ) →+ ((V ⊕ J) → ℤ) where
  toFun m := Sum.elim m (fun _ => 0)
  map_zero' := by funext i; cases i <;> rfl
  map_add' m n := by funext i; cases i <;> rfl

theorem faceFreeMap_C (q : V → Fin 3) (r : FaceRing R q) :
    faceFreeMap (J := J) q (MvPolynomial.C r) =
      AddMonoidAlgebra.mapDomainAlgHom R R (leftExponent.comp (faceToInt q)) r := by
  induction r using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp only [map_add, hr, hs]
  | single m r =>
    change faceFreeMap q (MvPolynomial.monomial 0 (AddMonoidAlgebra.single m r)) = _
    rw [faceFreeMap_monomial_single]
    simp only [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidHom.comp_apply]
    congr 1

theorem faceFreeMap_X [DecidableEq V] [DecidableEq J] (q : V → Fin 3) (j : J) :
    faceFreeMap (R := R) q (MvPolynomial.X j) =
      IncidenceLaurent.polynomialMap (MvPolynomial.X (Sum.inr j)) := by
  change faceFreeMap q (MvPolynomial.monomial (Finsupp.single j 1)
    (AddMonoidAlgebra.single 0 1)) = _
  rw [faceFreeMap_monomial_single, IncidenceLaurent.polynomialMap_X]
  congr 1
  funext i
  rcases i with v | k
  · simp [faceFreeExponent, faceToInt, IncidenceLaurent.natExponent]
  · by_cases h : k = j <;>
      simp [faceFreeExponent, IncidenceLaurent.natExponent, Finsupp.single_apply, h, Ne.symm]

theorem faceFreeMap_C_variable [DecidableEq V] [DecidableEq J]
    (q : V → Fin 3) (v : V) :
    faceFreeMap (J := J) q (MvPolynomial.C (faceVariable R q v)) =
      IncidenceLaurent.polynomialMap (MvPolynomial.X (Sum.inl v)) := by
  rw [faceFreeMap_C]
  change AddMonoidAlgebra.mapDomainAlgHom R R (leftExponent.comp (faceToInt q))
    (AddMonoidAlgebra.single _ 1) = _
  simp only [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single,
    AddMonoidHom.comp_apply, faceToInt_vertex, IncidenceLaurent.polynomialMap_X]
  congr 1
  funext i
  rcases i with w | j
  · by_cases h : w = v <;>
      simp [leftExponent, IncidenceLaurent.natExponent, h]
  · simp [leftExponent, IncidenceLaurent.natExponent]

end CechProduct

end BPFixedPoints
