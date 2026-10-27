import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Basic.Finite.Prod

/-! # A length-n regular sequence at the polynomial coefficient origin -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem isRegular_map_ringEquiv (e : R ≃+* S) (rs : List R)
    (h : IsRegular R rs) : IsRegular S (rs.map e) := by
  apply (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mp h
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact e.map_mul r x

noncomputable def polynomialQuotXEquiv :
    QuotSMulTop (Polynomial.X : (Polynomial R)) (Polynomial R) ≃ₐ[R] R :=
  (Ideal.quotientEquivAlgOfEq R (show Polynomial.X • (⊤ : Ideal (Polynomial R)) =
      Ideal.span {Polynomial.X - Polynomial.C (0 : R)} by
    simp [← Submodule.ideal_span_singleton_smul])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv 0)

theorem isRegular_polynomial_X_cons (rs : List R) (h : IsRegular R rs) :
    IsRegular (Polynomial R) (Polynomial.X :: rs.map Polynomial.C) := by
  apply IsRegular.cons
  · exact Polynomial.isRegular_X.left
  · let e := polynomialQuotXEquiv (R := R)
    apply (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mpr h
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    change e ((algebraMap R _ r) * x) = r * e x
    rw [map_mul, e.commutes]
    rfl

theorem optionEquivLeft_symm_C_eq_rename (k : Type u) [CommRing k]
    {σ : Type u} (p : MvPolynomial σ k) :
    (MvPolynomial.optionEquivLeft k σ).symm (Polynomial.C p) =
      MvPolynomial.rename Option.some p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

/-- A finite-variable polynomial ring has an origin-contained regular sequence of length equal to its number of variables. -/
theorem exists_regular_sequence_mvPolynomial (k : Type u) [CommRing k] [Nontrivial k]
    (σ : Type u) [Finite σ] :
    ∃ rs : List (MvPolynomial σ k), rs.length = Nat.card σ ∧
      (∀ r ∈ rs, MvPolynomial.constantCoeff r = 0) ∧
      IsRegular (MvPolynomial σ k) rs := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨rs, hlen, hmem, hreg⟩ := ih
    let φ := MvPolynomial.renameEquiv k e
    refine ⟨rs.map φ, ?_, ?_, isRegular_map_ringEquiv φ.toRingEquiv rs hreg⟩
    · simpa only [List.length_map, Nat.card_congr e] using hlen
    · intro r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      simpa [φ] using hmem x hx
  | h_empty =>
    refine ⟨[], by simp, by simp, ?_⟩
    exact IsRegular.nil _ _
  | @h_option σ _ ih =>
    obtain ⟨rs, hlen, hmem, hreg⟩ := ih
    let φ := (MvPolynomial.optionEquivLeft k σ).symm
    let xs := Polynomial.X :: rs.map Polynomial.C
    refine ⟨xs.map φ, ?_, ?_, isRegular_map_ringEquiv φ.toRingEquiv xs
      (isRegular_polynomial_X_cons rs hreg)⟩
    · simp [xs, hlen, Nat.card_eq_fintype_card, Fintype.card_option]
    · intro r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [φ]
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        simpa [φ, optionEquivLeft_symm_C_eq_rename] using hmem y hy

end BPFixedPoints.ResolutionTools
