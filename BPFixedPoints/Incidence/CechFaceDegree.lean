import BPFixedPoints.Incidence.CechFaceMaps
import BPFixedPoints.Incidence.CechProductDegree

/-!
# Čech degrees and face decomposition

A homogeneous Čech component is the product of faces whose number of overlaps
is its specified degree. Total degree, including exterior states, is read
as the exterior degree on each face.
-/

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type*) [CommRing R] {V : Type*} [Fintype V]

theorem faceEquiv_eq_zero_of_degree {n : ℤ} {x : C R V}
    (hx : x ∈ supported R R {b | (cechDegree b : ℤ) = n})
    (q : V → Fin 3) (hq : (faceDegree q : ℤ) ≠ n) : faceEquiv R x q = 0 := by
  ext m
  rw [faceEquiv_coeff, AddMonoidAlgebra.coeff_zero]
  apply (mem_supported' R x).mp hx
  change (cechDegree (embedFace q m) : ℤ) ≠ n
  simpa only [cechDegree_embedFace] using hq

theorem mem_supported_iff_faceEquiv (n : ℤ) (x : C R V) :
    x ∈ supported R R {b | (cechDegree b : ℤ) = n} ↔
      ∀ q : V → Fin 3, (faceDegree q : ℤ) ≠ n → faceEquiv R x q = 0 := by
  constructor
  · exact fun hx q hq => faceEquiv_eq_zero_of_degree R hx q hq
  · intro hx
    apply (mem_supported' R x).mpr
    intro b hb
    obtain ⟨⟨q, m⟩, rfl⟩ := faceBasisEquiv.symm.surjective b
    have hq : (faceDegree q : ℤ) ≠ n := by
      change (cechDegree (embedFace q m) : ℤ) ≠ n at hb
      simpa only [cechDegree_embedFace] using hb
    have h := congrArg (fun z : FaceRing R q => z.coeff m) (hx q hq)
    change x (embedFace q m) = 0
    simpa only [faceEquiv_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using h

theorem polynomialFaceEquiv_eq_zero_of_degree (σ : Type*) {n : ℤ}
    {x : C (MvPolynomial σ R) V}
    (hx : x ∈ supported (MvPolynomial σ R) (MvPolynomial σ R)
      {b | (cechDegree b : ℤ) = n})
    (q : V → Fin 3) (hq : (faceDegree q : ℤ) ≠ n) :
    polynomialFaceEquiv R σ x q = 0 := by
  rw [polynomialFaceEquiv_apply, faceEquiv_eq_zero_of_degree _ hx q hq, map_zero]

theorem mem_supported_iff_polynomialFaceEquiv (σ : Type*) (n : ℤ)
    (x : C (MvPolynomial σ R) V) :
    x ∈ supported (MvPolynomial σ R) (MvPolynomial σ R)
        {b | (cechDegree b : ℤ) = n} ↔
      ∀ q : V → Fin 3, (faceDegree q : ℤ) ≠ n → polynomialFaceEquiv R σ x q = 0 := by
  rw [mem_supported_iff_faceEquiv]
  constructor
  · intro hx q hq
    rw [polynomialFaceEquiv_apply, hx q hq, map_zero]
  · intro hx q hq
    apply (facePolynomialEquiv R σ q).injective
    simpa only [map_zero, ← polynomialFaceEquiv_apply] using hx q hq

/-- Total degree n means exterior degree n+faceDegree(q) on face q. -/
theorem totalFaceEquiv_degree_iff (σ E : Type*) [Fintype E] (n : ℤ)
    (x : Finset E →₀ C (MvPolynomial σ R) V) :
    (∀ S, x S ∈ supported (MvPolynomial σ R) (MvPolynomial σ R)
      {b | (cechDegree b : ℤ) = (S.card : ℤ) - n}) ↔
    (∀ q : V → Fin 3, totalFaceEquiv R σ E x q ∈
      supported (MvPolynomial σ (FaceRing R q)) R
        {S | (S.card : ℤ) = n + (faceDegree q : ℤ)}) := by
  constructor
  · intro hx q
    apply (mem_supported' R _).mpr
    intro S hS
    rw [totalFaceEquiv_apply]
    apply polynomialFaceEquiv_eq_zero_of_degree R σ (hx S) q
    change (S.card : ℤ) ≠ n + (faceDegree q : ℤ) at hS
    omega
  · intro hx S
    rw [mem_supported_iff_polynomialFaceEquiv]
    intro q hq
    have hS : (S.card : ℤ) ≠ n + (faceDegree q : ℤ) := by omega
    exact (mem_supported' R _).mp (hx q) S hS

/-- Čech degree n means all face components of degree other than n vanish. -/
theorem totalFaceEquiv_cechDegree_iff (σ E : Type*) [Fintype E] (n : ℤ)
    (x : Finset E →₀ C (MvPolynomial σ R) V) :
    (∀ S, x S ∈ supported (MvPolynomial σ R) (MvPolynomial σ R)
      {b | (cechDegree b : ℤ) = n}) ↔
    (∀ q : V → Fin 3, (faceDegree q : ℤ) ≠ n → totalFaceEquiv R σ E x q = 0) := by
  constructor
  · intro hx q hq
    apply Finsupp.ext
    intro S
    rw [totalFaceEquiv_apply, Finsupp.zero_apply]
    exact polynomialFaceEquiv_eq_zero_of_degree R σ (hx S) q hq
  · intro hx S
    rw [mem_supported_iff_polynomialFaceEquiv]
    intro q hq
    exact congrArg (fun z => z S) (hx q hq)

end BPFixedPoints.CechProduct
