import BPFixedPoints.Incidence.RegularDepthTools
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.Data.ENat.Monoid

/-! # Actual Artin quotients by maximal-length regular sequences -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Quotienting by a regular sequence lowers support dimension by its length. -/
theorem supportDim_quotient_regular_add_length_le
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hreg : IsRegular M rs) :
    Module.supportDim R (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) +
      (rs.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
  induction rs generalizing M with
  | nil =>
    have he : (Ideal.ofList ([] : List R) • ⊤ : Submodule R M) = ⊥ := by simp
    simpa only [List.length_nil, Nat.cast_zero, add_zero] using
      (Module.supportDim_eq_of_equiv
        (Submodule.quotEquivOfEqBot _ he)).le
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := (isRegular_cons_iff M x xs).mp hreg
    rw [Module.supportDim_eq_of_equiv
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs)]
    have hd := Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (M := M) (fun p hp => hx.notMem_of_mem_minimalPrimes hp)
    have h := (add_le_add (ih (QuotSMulTop x M) hxs) (le_refl (1 : WithBot ℕ∞))).trans hd
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc] using h

/-- A quotient by a regular sequence as long as the ring dimension is Artinian. -/
theorem isArtinian_quotient_of_regular_length_dim (rs : List R) (hreg : IsRegular R rs)
    (hd : ringKrullDim R = (rs.length : WithBot ℕ∞)) :
    IsArtinianRing (R ⧸ Ideal.ofList rs) := by
  apply isArtinianRing_iff_krullDimLE_zero.mpr
  apply Ring.krullDimLE_iff.mpr
  have h := supportDim_quotient_regular_add_length_le R rs hreg
  have he : (Ideal.ofList rs • (⊤ : Ideal R)) = Ideal.ofList rs := by simp
  rw [he, Module.supportDim_quotient_eq_ringKrullDim,
    Module.supportDim_self_eq_ringKrullDim, hd] at h
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp
    (show ringKrullDim (R ⧸ Ideal.ofList rs) + (rs.length : WithBot ℕ∞) ≤
      0 + (rs.length : WithBot ℕ∞) by simpa using h)

/-- For a finite-type field algebra, this quotient is also finite-dimensional over the field. -/
theorem finite_quotient_of_regular_length_dim
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (rs : List R) (hreg : IsRegular R rs)
    (hd : ringKrullDim R = (rs.length : WithBot ℕ∞)) :
    Module.Finite k (R ⧸ Ideal.ofList rs) := by
  have := isArtinian_quotient_of_regular_length_dim rs hreg hd
  exact Module.finite_of_isArtinianRing k (R ⧸ Ideal.ofList rs)

end BPFixedPoints.ResolutionTools
