import BPFixedPoints.Incidence.CechRestrictionBoundary

/-! # Čech degree-zero boundary with universal coefficients -/

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type*) [CommRing R] (J : Type*)
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem facePolynomialEquiv_chartRestriction (σ : V → Bool) (v : V) (b : Bool)
    (x : FaceRing (MvPolynomial J R) (chartFace (Function.update σ v b))) :
    facePolynomialEquiv R J (overlapFace σ v) (chartRestriction (MvPolynomial J R) σ v b x) =
      chartPolynomialRestriction R J σ v b
        (facePolynomialEquiv R J (chartFace (Function.update σ v b)) x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp only [AddMonoidAlgebra.single_add, map_add, hp, hq]
    | single n r =>
      simp only [chartRestriction, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single, facePolynomialEquiv,
        AddMonoidAlgebra.commAlgEquiv_single_single,
        chartPolynomialRestriction, MvPolynomial.mapAlgHom_apply, MvPolynomial.map,
        AddMonoidAlgebra.mapRingHom_single]
      congr 1
      exact (AddMonoidAlgebra.mapDomain_single
        (f := chartRestrictionExponent σ v b) (a := m) (r := r)).symm

/-- Insert degree-zero sections with polynomial coefficients into the full Čech module. -/
noncomputable def polynomialZeroCharts :
    ((σ : V → Bool) → MvPolynomial J (FaceRing R (chartFace σ))) →ₗ[R]
      C (MvPolynomial J R) V :=
  ((zeroCharts (MvPolynomial J R)).restrictScalars R).comp
    (LinearMap.piMap fun σ => (facePolynomialEquiv R J (chartFace σ)).symm.toLinearMap)

@[simp] theorem polynomialZeroCharts_apply
    (x : (σ : V → Bool) → MvPolynomial J (FaceRing R (chartFace σ))) :
    polynomialZeroCharts R J x = zeroCharts (MvPolynomial J R)
      (fun σ => (facePolynomialEquiv R J (chartFace σ)).symm (x σ)) := rfl

/-- With polynomial coefficients included, the degree-zero boundary is the difference of adjacent restrictions. -/
theorem polynomialFaceEquiv_d_zeroCharts (σ : V → Bool) (v : V)
    (x : (τ : V → Bool) → MvPolynomial J (FaceRing R (chartFace τ))) :
    polynomialFaceEquiv R J
      ((contraction (MvPolynomial J R) (fun _ : V => 0)).d (polynomialZeroCharts R J x))
        (overlapFace σ v) =
      chartPolynomialRestriction R J σ v true (x (Function.update σ v true)) -
        chartPolynomialRestriction R J σ v false (x (Function.update σ v false)) := by
  rw [polynomialFaceEquiv_apply, polynomialZeroCharts_apply, faceEquiv_d_zeroCharts, map_sub,
    facePolynomialEquiv_chartRestriction, facePolynomialEquiv_chartRestriction]
  simp

end BPFixedPoints.CechProduct
