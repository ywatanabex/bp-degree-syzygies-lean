import BPFixedPoints.Incidence.PolynomialRegularSequence
import Mathlib.RingTheory.Depth.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Regular sequences, depths of free modules and support dimension -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence CategoryTheory
open scoped Pointwise TensorProduct
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A nonzero free module is regular for every ring-regular sequence. -/
theorem isRegular_on_free (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] (rs : List R) (h : IsRegular R rs) :
    IsRegular M rs := by
  have hw := h.toIsWeaklyRegular.isWeaklyRegular_lTensor (M₂ := M)
  have hw' := ((TensorProduct.rid R M).isWeaklyRegular_congr rs).mp hw
  have hI : Ideal.ofList rs ≠ ⊤ := by simpa using h.top_ne_smul.symm
  have hn := (Module.FaithfullyFlat.iff_flat_and_proper_ideal R M).mp inferInstance
  exact ⟨hw', (hn.2 _ hI).symm⟩

/-- If I contains a ring-regular sequence of length n, the I-depth of a finite free module is at least n. -/
theorem length_le_depth_free (I : Ideal R) (hI : I ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (rs : List R) (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular R rs) :
    (rs.length : ℕ∞) ≤ I.depth (ModuleCat.of R M) := by
  by_cases hs : Subsingleton M
  · haveI := hs
    rw [Ideal.depth_eq_top_of_subsingleton]
    exact le_top
  · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hs
    have hn := (Module.FaithfullyFlat.iff_flat_and_proper_ideal R M).mp inferInstance
    rw [Ideal.depth_eq_sSup_length_isRegular I (ModuleCat.of R M) (hn.2 I hI).lt_top]
    exact le_sSup ⟨rs, isRegular_on_free M rs hreg, hmem, rfl⟩

/-- Regular-sequence length is bounded by module support dimension, without a locality assumption. -/
theorem regular_length_le_supportDim
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (rs : List R) (hreg : IsRegular M rs) :
    (rs.length : WithBot ℕ∞) ≤ Module.supportDim R M := by
  induction rs generalizing M with
  | nil =>
    haveI := hreg.nontrivial
    simpa only [List.length_nil, Nat.cast_zero] using
      (le_of_not_gt (fun h => Module.supportDim_ne_bot_of_nontrivial R M
        ((WithBot.lt_zero_iff_eq_bot _).mp h)))
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := (isRegular_cons_iff M x xs).mp hreg
    have hle := Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (M := M) (fun p hp => hx.notMem_of_mem_minimalPrimes hp)
    have ht : (xs.length : WithBot ℕ∞) + 1 ≤
        Module.supportDim R (QuotSMulTop x M) + 1 :=
      add_le_add (ih (QuotSMulTop x M) hxs) le_rfl
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using ht.trans hle

/-- A finite upper bound on support dimension also bounds I-depth. -/
theorem depth_le_of_supportDim_le (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hproper : I • (⊤ : Submodule R M) < ⊤) (d : ℕ)
    (hd : Module.supportDim R M ≤ (d : WithBot ℕ∞)) :
    I.depth M ≤ (d : ℕ∞) := by
  rw [Ideal.depth_eq_sSup_length_isRegular I M hproper]
  apply sSup_le
  rintro n ⟨rs, hreg, _, rfl⟩
  have h := (regular_length_le_supportDim M rs hreg).trans hd
  exact_mod_cast h

end BPFixedPoints.ResolutionTools
