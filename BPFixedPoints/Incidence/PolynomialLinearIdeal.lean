import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.Ring

namespace BPFixedPoints.ResolutionTools

open MvPolynomial RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false

variable {k σ : Type*} [CommRing k]

theorem mvPolynomial_sub_constant_mem_span_X (p : MvPolynomial σ k) :
    p - C (constantCoeff p) ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ k)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have he : (p + q) - C (constantCoeff (p + q)) =
        (p - C (constantCoeff p)) + (q - C (constantCoeff q)) := by
      rw [map_add, map_add]
      ring
    rw [he]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    simpa using Ideal.mul_mem_left (Ideal.span (Set.range (X : σ → MvPolynomial σ k))) p
      (Ideal.subset_span (Set.mem_range_self i))

theorem ideal_span_X_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPolynomial σ k)) =
      RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp
  · intro p hp
    have h := mvPolynomial_sub_constant_mem_span_X p
    simpa only [RingHom.mem_ker.mp hp, map_zero, sub_zero] using h

/-- Homogeneous linear forms span the ideal of the coefficient origin. -/
theorem ideal_span_homogeneous_one_eq_ker_constantCoeff :
    Ideal.span (MvPolynomial.homogeneousSubmodule σ k 1 : Set (MvPolynomial σ k)) =
      RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) := by
  rw [homogeneousSubmodule_one_eq_span_X, ← ideal_span_X_eq_ker_constantCoeff]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    change Submodule.span k (Set.range X) ≤
      (Ideal.span (Set.range X)).restrictScalars k
    exact Submodule.span_le.mpr (fun _ h => Ideal.subset_span h)
  · exact Ideal.span_mono Submodule.subset_span

theorem regular_ideal_ofList_ne_top {A : Type*} [CommRing A]
    (rs : List A) (hreg : IsRegular A rs) : Ideal.ofList rs ≠ ⊤ := by
  simpa using hreg.top_ne_smul.symm

end BPFixedPoints.ResolutionTools
