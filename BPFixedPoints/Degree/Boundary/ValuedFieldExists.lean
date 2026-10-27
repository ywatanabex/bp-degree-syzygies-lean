import BPFixedPoints.Degree.Boundary.ValuedField

/-!
# Existence of a Puiseux-type field (proof of the former axiom `newtonPuiseux_exists`)

`PuiseuxField K` needs an algebraically closed valued field L of characteristic
zero, an embedding of K⟦t⟧ compatible with constant coefficients, and residue
field K. It does not require value group ℚ or Puiseux expansions.

Take L to be an algebraic closure of K((t)). Chevalley's extension theorem,
`IsLocalRing.exists_factor_valuationRing`, gives a valuation ring A dominating
the local ring K⟦t⟧. Its valuation satisfies v(f)≤1 and v(f)<1 iff f has zero
constant coefficient; in particular it is trivial on K.
For integral x∈L, clear denominators in its algebraic equation and divide by a
power of t to get q(x)=0 over K⟦t⟧ with a coefficient of nonzero constant term.
The resulting nonzero P∈K[Y] satisfies v(P(x))<1. Factor P=c∏(Y−a_j) over K;
then some v(x−a_j)<1, proving that the residue field is K.
-/

universe u

namespace BPFixedPoints.BP

open Polynomial

section Residue

variable {K : Type u} [Field K] [IsAlgClosed K] {L : Type*} [Field L] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) (ψ : PowerSeries K →+* L)

/-- Existence of residues: an integral root of a nonzero polynomial over K[[t]] is congruent to an element of K. -/
theorem exists_residue_of_root
    (hlt : ∀ f, PowerSeries.constantCoeff f = 0 → v (ψ f) < 1)
    (hC : ∀ c : K, c ≠ 0 → v (ψ (PowerSeries.C c)) = 1) (hX : ψ PowerSeries.X ≠ 0)
    {x : L} (hx : v x ≤ 1) {q : (PowerSeries K)[X]} (hq0 : q ≠ 0) (hq : q.eval₂ ψ x = 0) :
    ∃ c : K, v (x - ψ (PowerSeries.C c)) < 1 := by
  classical
  -- Choose the coefficient with smallest order k.
  obtain ⟨k, hk, hmin⟩ := q.support.exists_min_image (fun i => (q.coeff i).order)
    (nonempty_support_iff.2 hq0)
  have hk0 : q.coeff k ≠ 0 := mem_support_iff.1 hk
  set n := (q.coeff k).order.toNat with hn
  have hdvd : ∀ i, PowerSeries.X ^ n ∣ q.coeff i := by
    intro i
    by_cases hi : q.coeff i = 0
    · rw [hi]; exact dvd_zero _
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    apply PowerSeries.coeff_of_lt_order
    have h1 := hmin i (mem_support_iff.2 hi)
    calc (m : ℕ∞) < n := by exact_mod_cast hm
      _ = (q.coeff k).order := ENat.natCast_toNat (by rwa [ne_eq, PowerSeries.order_eq_top])
      _ ≤ _ := h1
  choose r hr using hdvd
  -- Relation after dividing coefficients by t^n.
  have hsum : ∑ i ∈ q.support, ψ (r i) * x ^ i = 0 := by
    have e : q.eval₂ ψ x = ψ PowerSeries.X ^ n * ∑ i ∈ q.support, ψ (r i) * x ^ i := by
      rw [eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i, map_mul, map_pow]; ring
    rw [e] at hq
    exact (mul_eq_zero.1 hq).resolve_left (pow_ne_zero _ hX)
  set c : ℕ → K := fun i => PowerSeries.constantCoeff (r i) with hc
  have hck : c k ≠ 0 := by
    have h1 := PowerSeries.coeff_order hk0
    rw [← hn, hr k, PowerSeries.coeff_X_pow_mul'] at h1
    simpa [hc] using h1
  -- Constant-coefficient polynomial P.
  set P : K[X] := ∑ i ∈ q.support, monomial i (c i) with hP
  have hPk : P.coeff k = c k := by
    rw [hP, finsetSum_coeff, Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [coeff_monomial, hik]
    · intro h; exact absurd hk h
  have hP0 : P ≠ 0 := fun h => hck (by rw [← hPk, h, coeff_zero])
  -- v(P(x)) < 1
  have hPx : v (P.eval₂ (ψ.comp PowerSeries.C) x) < 1 := by
    have e : P.eval₂ (ψ.comp PowerSeries.C) x =
        -∑ i ∈ q.support, ψ (r i - PowerSeries.C (c i)) * x ^ i := by
      rw [hP, eval₂_finsetSum]
      have : ∑ i ∈ q.support, ψ (r i - PowerSeries.C (c i)) * x ^ i =
          ∑ i ∈ q.support, ψ (r i) * x ^ i -
            ∑ i ∈ q.support, ψ (PowerSeries.C (c i)) * x ^ i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sub]; ring
      rw [this, hsum]
      simp [eval₂_monomial]
    rw [e, Valuation.map_neg]
    refine v.map_sum_lt one_ne_zero fun i _ => ?_
    rw [map_mul, map_pow]
    refine mul_lt_one_of_lt_of_le (hlt _ ?_) (pow_le_one' hx i)
    simp [hc]
  -- Factor P into its leading coefficient times the product of Y-a.
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := P))
  rw [← hfac, eval₂_mul, eval₂_C, eval₂_multiset_prod, Multiset.map_map, map_mul,
    RingHom.comp_apply, hC _ (leadingCoeff_ne_zero.2 hP0), one_mul] at hPx
  by_contra hne
  push Not at hne
  have : (1 : Γ₀) ≤ v (Multiset.map ((fun p => p.eval₂ (ψ.comp PowerSeries.C) x) ∘
      fun a => X - Polynomial.C a) P.roots).prod := by
    rw [map_multiset_prod v]
    refine Multiset.one_le_prod_of_one_le fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.1 hz
    simpa using hne a
  exact absurd hPx (not_lt.2 this)

end Residue

/-- **Existence of a Puiseux-type valued field.** For algebraically closed K of characteristic zero, a valuation ring of an algebraic closure of K((t)) dominating K⟦t⟧ supplies `PuiseuxField K`. This proves the former axiom `newtonPuiseux_exists`; rational value group and Puiseux expansions are not used. -/
theorem newtonPuiseux_exists (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] :
    Nonempty (PuiseuxField K) := by
  classical
  let L := AlgebraicClosure (LaurentSeries K)
  let ψ : PowerSeries K →+* L := algebraMap (PowerSeries K) L
  have hψ : Function.Injective ψ := by
    have e : ψ = (algebraMap (LaurentSeries K) L).comp
        (algebraMap (PowerSeries K) (LaurentSeries K)) := IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    exact (algebraMap (LaurentSeries K) L).injective.comp
      (IsFractionRing.injective (PowerSeries K) (LaurentSeries K))
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let ψA := ψ.codRestrict A.toSubring hA
  have hψA : ∀ f, (ψA f : L) = ψ f := fun _ => rfl
  -- Unit criterion.
  have hunit : ∀ f : PowerSeries K, A.valuation (ψ f) = 1 ↔ PowerSeries.constantCoeff f ≠ 0 := by
    intro f
    rw [← hψA, ← A.valuation_eq_one_iff, ← isUnit_iff_ne_zero, ← PowerSeries.isUnit_iff_constantCoeff]
    exact ⟨fun h => IsLocalHom.map_nonunit f h, fun h => h.map ψA⟩
  have hle : ∀ f, A.valuation (ψ f) ≤ 1 := fun f => (A.valuation_le_one_iff _).2 (hA f)
  have hlt : ∀ f, A.valuation (ψ f) < 1 ↔ PowerSeries.constantCoeff f = 0 := by
    intro f
    constructor
    · intro h
      by_contra hne
      rw [(hunit f).2 hne] at h
      exact lt_irrefl _ h
    · intro h
      exact lt_of_le_of_ne (hle f) fun e => (hunit f).1 e h
  have hC : ∀ c : K, c ≠ 0 → A.valuation (ψ (PowerSeries.C c)) = 1 := fun c hc =>
    (hunit _).2 (by simpa using hc)
  have hX : ψ PowerSeries.X ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hψ (h.trans (map_zero ψ).symm))
  have : CharZero L := charZero_of_injective_ringHom (algebraMap K L).injective
  refine ⟨{
    L := L
    Γ₀ := A.ValueGroup
    v := A.valuation
    ofK := ψ.comp PowerSeries.C
    val_ofK := hC
    ofPS := ψ
    ofPS_injective := hψ
    ofPS_C := fun _ => rfl
    t := ψ PowerSeries.X
    ofPS_X := rfl
    val_ofPS_le_one := hle
    val_ofPS_lt_one_iff := hlt
    residue := ?_ }⟩
  intro x hx
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := LaurentSeries K) x
  let M := nonZeroDivisors (PowerSeries K)
  have hq := IsLocalization.integerNormalization_aeval_eq_zero M p hp
  have hq0 : IsLocalization.integerNormalization M p ≠ 0 :=
    (IsLocalization.integerNormalization_eq_zero_iff le_rfl p).not.2 hp0
  rw [aeval_def] at hq
  exact exists_residue_of_root A.valuation ψ (fun f h => (hlt f).2 h) hC hX hx hq0 hq

end BPFixedPoints.BP
