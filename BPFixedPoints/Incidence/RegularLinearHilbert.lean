import BPFixedPoints.Incidence.HomogeneousQuotient
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic

/-! # Hilbert series of an actual quotient by a regular linear form -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- The series is defined from the dimensions of the given components. -/
noncomputable def gradedHilbertSeries : PowerSeries ℤ :=
  PowerSeries.mk fun q => (Module.finrank k (𝒜 q) : ℤ)

/-- Multiplication by a degree-one element, on the actual homogeneous pieces. -/
noncomputable def gradedLinearMultiply {x : A} (hx : x ∈ 𝒜 1) (q : ℕ) :
    𝒜 q →ₗ[k] 𝒜 (q + 1) where
  toFun a := ⟨x * a.val, by simpa [Nat.add_comm] using SetLike.GradedMul.mul_mem hx a.property⟩
  map_add' a b := Subtype.ext (mul_add _ _ _)
  map_smul' c a := Subtype.ext (mul_smul_comm _ _ _)

theorem gradedLinearMultiply_injective {x : A} (hx : x ∈ 𝒜 1)
    (hr : IsSMulRegular A x) (q : ℕ) : Function.Injective (gradedLinearMultiply 𝒜 hx q) := by
  intro a b h
  exact Subtype.ext (hr (congrArg Subtype.val h))

theorem range_gradedLinearMultiply {x : A} (hx : x ∈ 𝒜 1) (q : ℕ) :
    LinearMap.range (gradedLinearMultiply 𝒜 hx q) =
      LinearMap.ker (gradedQuotientMap 𝒜 (Ideal.span {x}) (q + 1)) := by
  ext y
  rw [mem_ker_gradedQuotientMap]
  constructor
  · rintro ⟨a, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨a.val, rfl⟩
  · intro hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨decompose 𝒜 a q, Subtype.ext ?_⟩
    have h := coe_decompose_mul_add_of_left_mem 𝒜 hx (b := a) (j := q)
    rw [← ha] at h
    rw [Nat.add_comm 1 q, decompose_of_mem_same 𝒜 y.property] at h
    exact h.symm

theorem ker_gradedQuotientMap_zero {x : A} (hx : x ∈ 𝒜 1) :
    LinearMap.ker (gradedQuotientMap 𝒜 (Ideal.span {x}) 0) = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  rw [mem_ker_gradedQuotientMap] at hy
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
  have h := coe_decompose_mul_of_left_mem_of_not_le 𝒜 hx (b := a) (n := 0) (by omega)
  rw [← ha, decompose_of_mem_same 𝒜 y.property] at h
  exact Subtype.ext h

variable [∀ q, Module.Finite k (𝒜 q)]

theorem finrank_gradedQuotientPiece_zero {x : A} (hx : x ∈ 𝒜 1) :
    Module.finrank k (gradedQuotientPiece 𝒜 (Ideal.span {x}) 0) =
      Module.finrank k (𝒜 0) := by
  have h := (gradedQuotientMap 𝒜 (Ideal.span {x}) 0).finrank_range_add_finrank_ker
  rw [ker_gradedQuotientMap_zero 𝒜 hx,
    LinearMap.range_eq_top.mpr (gradedQuotientMap_surjective _ _ _)] at h
  simpa using h

theorem finrank_gradedQuotientPiece_succ {x : A} (hx : x ∈ 𝒜 1)
    (hr : IsSMulRegular A x) (q : ℕ) :
    Module.finrank k (gradedQuotientPiece 𝒜 (Ideal.span {x}) (q + 1)) +
      Module.finrank k (𝒜 q) = Module.finrank k (𝒜 (q + 1)) := by
  have hm := (gradedLinearMultiply 𝒜 hx q).finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr (gradedLinearMultiply_injective 𝒜 hx hr q)] at hm
  have h := (gradedQuotientMap 𝒜 (Ideal.span {x}) (q + 1)).finrank_range_add_finrank_ker
  rw [← range_gradedLinearMultiply 𝒜 hx q,
    LinearMap.range_eq_top.mpr (gradedQuotientMap_surjective _ _ _)] at h
  simp only [finrank_top, finrank_bot, add_zero] at hm h
  rwa [hm] at h

/-- The regularity hypothesis makes the multiplication sequence exact in every degree. -/
theorem gradedHilbertSeries_quotient_linear {x : A} (hx : x ∈ 𝒜 1)
    (hr : IsSMulRegular A x) :
    gradedHilbertSeries (gradedQuotientPiece 𝒜 (Ideal.span {x})) =
      (1 - PowerSeries.X) * gradedHilbertSeries 𝒜 := by
  ext q
  rw [sub_mul, one_mul, map_sub]
  cases q with
  | zero =>
    simp only [gradedHilbertSeries, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul,
      sub_zero, finrank_gradedQuotientPiece_zero 𝒜 hx]
  | succ q =>
    have h := finrank_gradedQuotientPiece_succ 𝒜 hx hr q
    have hc : (Module.finrank k (gradedQuotientPiece 𝒜 (Ideal.span {x}) (q+1)) : ℤ) +
        Module.finrank k (𝒜 q) = Module.finrank k (𝒜 (q+1)) := by exact_mod_cast h
    rw [show PowerSeries.X * gradedHilbertSeries 𝒜 =
      PowerSeries.X ^ 1 * gradedHilbertSeries 𝒜 by rw [pow_one],
      PowerSeries.coeff_X_pow_mul]
    simp only [gradedHilbertSeries, PowerSeries.coeff_mk]
    omega

end BPFixedPoints.ResolutionTools
