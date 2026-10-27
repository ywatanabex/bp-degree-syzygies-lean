import BPFixedPoints.Incidence.CechBoundary
import BPFixedPoints.Incidence.CechFaceMaps
import BPFixedPoints.Incidence.KoszulFaceRing

/-!
# Restrictions from degree-zero charts to adjacent overlaps

Keep left-coordinate exponents and negate right-coordinate exponents when
passing to Laurent coordinates. Lift to monoid rings and coefficient polynomials.
-/

namespace BPFixedPoints.CechProduct

open Finsupp

variable {V : Type*} [DecidableEq V]

/-- Face with exactly one vertex replaced by an overlap. -/
def overlapFace (σ : V → Bool) (v : V) : V → Fin 3 :=
  Function.update (chartFace σ) v 2

@[simp] theorem overlapFace_self (σ : V → Bool) (v : V) : overlapFace σ v v = 2 := by
  simp [overlapFace]

theorem overlapFace_ne (σ : V → Bool) (v w : V) (hw : w ≠ v) :
    overlapFace σ v w = chartFace σ w := Function.update_of_ne hw _ _

@[simp] theorem overlapFace_update (σ : V → Bool) (v : V) (b : Bool) :
    overlapFace (Function.update σ v b) v = overlapFace σ v := by
  funext w
  by_cases hw : w = v
  · subst w; simp
  · simp [overlapFace, chartFace, hw]

def chartNatEquiv : (b : Bool) → ℕ ≃+ FaceExponent (if b then 1 else 0)
  | false => AddEquiv.refl ℕ
  | true => AddEquiv.refl ℕ

/-- Express chart exponents as a family of natural numbers. -/
def chartMonoidEquiv (σ : V → Bool) : (V → ℕ) ≃+ FaceMonoid (chartFace σ) :=
  AddEquiv.piCongrRight fun v => chartNatEquiv (σ v)

@[simp] theorem vertexFaceEquiv_chartNat (b : Bool) (k : ℕ) :
    vertexFaceEquiv.symm ⟨(if b then 1 else 0), chartNatEquiv b k⟩ =
      vertexChartBasis b k := by
  cases b <;> rfl

@[simp] theorem vertexFaceEquiv_cast {q q' : Fin 3} (h : q = q') (k : FaceExponent q) :
    vertexFaceEquiv.symm ⟨q', AddEquiv.cast (M := FaceExponent) h k⟩ =
      vertexFaceEquiv.symm ⟨q, k⟩ := by
  cases h
  rfl

@[simp] theorem embedFace_chartMonoid (σ : V → Bool) (k : V → ℕ) :
    embedFace (chartFace σ) (chartMonoidEquiv σ k) = chartBasis σ k := by
  funext v
  exact vertexFaceEquiv_chartNat (σ v) (k v)

/-- Use an integer exponent at the restricted vertex and retain chart exponents elsewhere. -/
def overlapCoordinate (σ : V → Bool) (v : V) (b : Bool) (w : V) :
    ℕ →+ FaceExponent (overlapFace σ v w) := by
  by_cases hw : w = v
  · subst w
    exact (AddEquiv.cast (M := FaceExponent) (overlapFace_self σ v).symm).toAddMonoidHom.comp
      (if b then -(Nat.castAddMonoidHom ℤ) else Nat.castAddMonoidHom ℤ)
  · exact (AddEquiv.cast (M := FaceExponent) (overlapFace_ne σ v w hw).symm).toAddMonoidHom.comp
      (chartNatEquiv (σ w)).toAddMonoidHom

def overlapExponent (σ : V → Bool) (v : V) (b : Bool) :
    (V → ℕ) →+ FaceMonoid (overlapFace σ v) where
  toFun k w := overlapCoordinate σ v b w (k w)
  map_zero' := by funext w; exact map_zero _
  map_add' k l := by funext w; exact map_add _ _ _

theorem embedFace_overlapExponent (σ : V → Bool) (v : V) (b : Bool) (k : V → ℕ) :
    embedFace (overlapFace σ v) (overlapExponent σ v b k) =
      boundaryBasis (fun _ => 0) (Function.update σ v b) k v := by
  funext w
  change vertexFaceEquiv.symm
    ⟨overlapFace σ v w, overlapCoordinate σ v b w (k w)⟩ = _
  by_cases hw : w = v
  · subst w
    simp only [overlapCoordinate, dite_true, AddMonoidHom.comp_apply,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, vertexFaceEquiv_cast]
    cases b <;> simp [boundaryBasis, restrictionExponent, vertexFaceEquiv] <;> rfl
  · simp only [overlapCoordinate, dite_eq_right hw]
    change vertexFaceEquiv.symm ⟨overlapFace σ v w,
      AddEquiv.cast (M := FaceExponent) (overlapFace_ne σ v w hw).symm
        (chartMonoidEquiv σ k w)⟩ = _
    calc
      _ = vertexFaceEquiv.symm ⟨chartFace σ w, chartMonoidEquiv σ k w⟩ :=
        vertexFaceEquiv_cast (overlapFace_ne σ v w hw).symm _
      _ = vertexChartBasis (σ w) (k w) := vertexFaceEquiv_chartNat (σ w) (k w)
      _ = _ := by simp [boundaryBasis, chartBasis, hw]

/-- Adjacent-chart restriction, negating the exponent for the right chart. -/
def chartRestrictionExponent (σ : V → Bool) (v : V) (b : Bool) :
    FaceMonoid (chartFace (Function.update σ v b)) →+ FaceMonoid (overlapFace σ v) :=
  (overlapExponent σ v b).comp (chartMonoidEquiv (Function.update σ v b)).symm.toAddMonoidHom

@[simp] theorem chartRestrictionExponent_chartMonoid
    (σ : V → Bool) (v : V) (b : Bool) (k : V → ℕ) :
    chartRestrictionExponent σ v b (chartMonoidEquiv (Function.update σ v b) k) =
      overlapExponent σ v b k := by
  simp [chartRestrictionExponent]

variable (R : Type*) [CommRing R]

noncomputable def chartRestriction (σ : V → Bool) (v : V) (b : Bool) :
    FaceRing R (chartFace (Function.update σ v b)) →ₐ[R] FaceRing R (overlapFace σ v) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (chartRestrictionExponent σ v b)

@[simp] theorem chartRestriction_single
    (σ : V → Bool) (v : V) (b : Bool) (k : V → ℕ) (r : R) :
    chartRestriction R σ v b
      (AddMonoidAlgebra.single (chartMonoidEquiv (Function.update σ v b) k) r) =
        AddMonoidAlgebra.single (overlapExponent σ v b k) r := by
  change AddMonoidAlgebra.mapDomain (chartRestrictionExponent σ v b)
    (AddMonoidAlgebra.single _ r) = _
  rw [AddMonoidAlgebra.mapDomain_single, chartRestrictionExponent_chartMonoid]

/-- Restrict only vertex coordinates, fixing universal coefficients. -/
noncomputable def chartPolynomialRestriction (J : Type*) (σ : V → Bool) (v : V) (b : Bool) :
    MvPolynomial J (FaceRing R (chartFace (Function.update σ v b))) →ₐ[R]
      MvPolynomial J (FaceRing R (overlapFace σ v)) :=
  MvPolynomial.mapAlgHom (chartRestriction R σ v b)

@[simp] theorem chartPolynomialRestriction_monomial_single (J : Type*)
    (σ : V → Bool) (v : V) (b : Bool) (n : J →₀ ℕ) (k : V → ℕ) (r : R) :
    chartPolynomialRestriction R J σ v b
      (MvPolynomial.monomial n
        (AddMonoidAlgebra.single (chartMonoidEquiv (Function.update σ v b) k) r)) =
      MvPolynomial.monomial n (AddMonoidAlgebra.single (overlapExponent σ v b k) r) := by
  simp [chartPolynomialRestriction]

end BPFixedPoints.CechProduct
