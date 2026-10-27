import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# A one-edge quadratic extension is a domain

The radicand contains the edge coordinate q exactly once as a factor.
Use Eisenstein in q and reflection of monic divisibility through coefficient extension.
-/

namespace BPFixedPoints

open Polynomial

variable {R : Type*} [CommRing R]

/-- Product of the four belief components of one edge. -/
noncomputable def edgeRadicand (u v : R) : Polynomial R :=
  X * (C (1 - u - v) + X) * (C u - X) * (C v - X)

/-- Monic quadratic adjoining the square root for one edge. -/
noncomputable def edgePolynomial (u v : R) : Polynomial (Polynomial R) :=
  X ^ 2 - C (edgeRadicand u v)

theorem edgePolynomial_monic (u v : R) : (edgePolynomial u v).Monic :=
  monic_X_pow_sub_C _ (by decide)

@[simp] theorem edgePolynomial_natDegree [Nontrivial R] (u v : R) :
    (edgePolynomial u v).natDegree = 2 := natDegree_X_pow_sub_C

@[simp] theorem edgeRadicand_coeff_one (u v : R) :
    (edgeRadicand u v).coeff 1 = (1 - u - v) * u * v := by
  simp [edgeRadicand, mul_assoc, coeff_X_mul]

theorem edgePolynomial_irreducible [IsDomain R] (u v : R)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : 1 - u - v ≠ 0) :
    Irreducible (edgePolynomial u v) := by
  let P : Ideal (Polynomial R) := Ideal.span {X}
  have hP : P.IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  have heis : (edgePolynomial u v).IsEisensteinAt P := by
    apply (edgePolynomial_monic u v).isEisensteinAt_of_mem_of_notMem hP.ne_top
    · intro n hn
      rw [edgePolynomial_natDegree] at hn
      interval_cases n
      · rw [Ideal.mem_span_singleton, X_dvd_iff]
        simp [edgePolynomial, edgeRadicand]
      · simp [edgePolynomial]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hc := (X_pow_dvd_iff.mp h) 1 (by decide)
      simp [edgePolynomial, hu, hv, huv] at hc
  exact heis.irreducible hP (edgePolynomial_monic u v).isPrimitive (by simp)

/-- Primality of a monic polynomial reflects through injective coefficient extension. -/
private theorem monic_prime_of_prime_map
    {S : Type*} [CommRing S] [Nontrivial R] (φ : R →+* S)
    (hφ : Function.Injective φ) {p : Polynomial R} (hp : p.Monic)
    (hprime : Prime (p.map φ)) : Prime p := by
  refine ⟨hp.ne_zero, ?_, ?_⟩
  · intro h
    exact hprime.not_isUnit (h.map (Polynomial.mapRingHom φ))
  · intro a b hab
    have hh : p.map φ ∣ a.map φ * b.map φ := by
      simpa only [Polynomial.map_mul] using Polynomial.map_dvd φ hab
    exact (hprime.dvd_or_dvd hh).imp (map_dvd_map φ hφ hp).mp (map_dvd_map φ hφ hp).mp

/-- If the three basic endpoint factors are nonzero, the one-edge square-root extension is a domain. -/
theorem edgeAdjoin_isDomain [IsDomain R] (u v : R)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : 1 - u - v ≠ 0) :
    IsDomain (AdjoinRoot (edgePolynomial u v)) := by
  let K := FractionRing R
  let φ : Polynomial R →+* Polynomial K := Polynomial.mapRingHom (algebraMap R K)
  have hbase : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hφ : Function.Injective φ := Polynomial.map_injective _ hbase
  have hu' : algebraMap R K u ≠ 0 := (map_ne_zero_iff _ hbase).mpr hu
  have hv' : algebraMap R K v ≠ 0 := (map_ne_zero_iff _ hbase).mpr hv
  have huv' : 1 - algebraMap R K u - algebraMap R K v ≠ 0 := by
    simpa only [map_sub, map_one] using (map_ne_zero_iff _ hbase).mpr huv
  have heq : (edgePolynomial u v).map φ =
      edgePolynomial (algebraMap R K u) (algebraMap R K v) := by
    simp [edgePolynomial, edgeRadicand, φ]
  apply AdjoinRoot.isDomain_of_prime
  apply monic_prime_of_prime_map φ hφ (edgePolynomial_monic u v)
  rw [heq]
  exact (edgePolynomial_irreducible _ _ hu' hv' huv').prime

end BPFixedPoints
