import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Krull dimension under integral extensions and on polynomial open sets -/

namespace BPFixedPoints

/-- An injective integral extension preserves Krull dimension. -/
theorem ringKrullDim_eq_of_integral_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) : ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under hpq
  · unfold ringKrullDim Order.krullDim
    apply iSup_le
    intro l
    letI : l.head.asIdeal.IsPrime := l.head.isPrime
    obtain ⟨P, _, hP, hPover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      l.head.asIdeal (⊥ : Ideal S) (by
        change RingHom.ker (algebraMap R S) ≤ _
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
        exact bot_le)
    letI : P.IsPrime := hP
    letI : P.LiesOver l.head.asIdeal := ⟨hPover.symm⟩
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by simpa [hlen])

/-- Every maximal ideal in a polynomial ring in finitely many variables over a field has height equal to the number of variables. -/
theorem height_maximal_mvPolynomial {k : Type*} [Field k]
    (ι : Type*) [Finite ι] (M : Ideal (MvPolynomial ι k)) [M.IsMaximal] :
    M.height = Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e IH =>
    let φ := (MvPolynomial.renameEquiv k e.symm).toRingEquiv
    letI : (M.map φ).IsMaximal := Ideal.map_isMaximal_of_equiv φ
    have h := IH (M.map φ)
    simpa [φ, RingEquiv.height_map, Nat.card_congr e] using h
  | h_empty =>
    let φ := MvPolynomial.isEmptyRingEquiv k PEmpty
    letI : (M.map φ).IsMaximal := Ideal.map_isMaximal_of_equiv φ
    have h : M.map φ = ⊥ :=
      (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right (Ideal.IsMaximal.ne_top inferInstance)
    rw [← φ.height_map M, h, Ideal.height_bot]
    simp
  | @h_option ι _ IH =>
    let φ := (MvPolynomial.optionEquivLeft k ι).toRingEquiv
    let P := M.map φ
    letI : P.IsMaximal := Ideal.map_isMaximal_of_equiv φ
    let p := P.under (MvPolynomial ι k)
    letI : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hp := IH p
    have hP := Polynomial.height_eq_height_add_one p P
    rw [hp] at hP
    simpa [P, φ, Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add,
      Nat.cast_one] using hP

/-- Localizing a polynomial ring over a field at a nonzero polynomial preserves dimension. -/
theorem ringKrullDim_away_mvPolynomial {k : Type*} [Field k]
    {ι : Type*} [Finite ι] {p : MvPolynomial ι k} (hp : p ≠ 0) :
    ringKrullDim (Localization.Away p) = (Nat.card ι : WithBot ℕ∞) := by
  let R := MvPolynomial ι k
  let S := Localization.Away p
  have hM : Submonoid.powers p ≤ nonZeroDivisors R :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hp)
  letI : IsDomain S := IsLocalization.isDomain_localization hM
  obtain ⟨M, hmax⟩ := Ideal.exists_maximal S
  letI : M.IsMaximal := hmax
  have hmax' := (IsLocalization.isMaximal_iff_isMaximal_disjoint S p M).mp hmax
  letI : (M.under R).IsMaximal := hmax'.1
  have hheight : M.height = Nat.card ι := by
    rw [← IsLocalization.height_under (Submonoid.powers p) M]
    exact height_maximal_mvPolynomial ι (M.under R)
  apply le_antisymm
  · have hle : ringKrullDim S ≤ ringKrullDim R := by
      apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      intro q r hqr
      exact (IsLocalization.orderEmbedding (Submonoid.powers p) S).strictMono hqr
    simpa [R, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] using hle
  · simpa [hheight] using (Ideal.height_le_ringKrullDim_of_ne_top hmax.ne_top)

end BPFixedPoints
