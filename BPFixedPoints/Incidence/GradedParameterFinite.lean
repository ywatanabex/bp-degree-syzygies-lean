import BPFixedPoints.Incidence.FiniteGradedBound
import BPFixedPoints.Incidence.LinearSequenceMultiplication
import Mathlib.RingTheory.Finiteness.Basic

/-! # Finite generation over linear parameters from a finite homogeneous quotient -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false

variable {k R A ι : Type*} [Field k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A] [Fintype ι]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] [∀ q, Module.Finite k (𝒜 q)]
  (r : ι → R) (hr : ∀ i, algebraMap R A (r i) ∈ 𝒜 1)

include hr in
/-- A bound on homogeneous quotient components gives finite generation over the parameter ring.
The algebra need not be generated in degree one over the field. -/
theorem finite_over_parameters_of_graded_bound (N : ℕ) (hN : 0 < N)
    (hz : ∀ q, N ≤ q → gradedQuotientPiece 𝒜
      (Ideal.span (Set.range (fun i => algebraMap R A (r i)))) q = ⊥) :
    Module.Finite R A := by
  classical
  let W : Submodule k A := ⨆ q : Fin N, 𝒜 q.val
  let P : Submodule R A := Submodule.span R (W : Set A)
  have hW : W.FG := Submodule.fg_iSup _ (fun q => Module.Finite.iff_fg.mp inferInstance)
  have hP : P.FG := hW.span
  have hm (q : ℕ) : ∀ y ∈ 𝒜 q, y ∈ P := by
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro y hy
      by_cases hq : q < N
      · exact Submodule.subset_span ((le_iSup (fun j : Fin N => 𝒜 j.val) ⟨q, hq⟩) hy)
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
        have hs := linearSequenceMultiply_surjective_of_piece_zero 𝒜
          (fun i => algebraMap R A (r i)) hr q (hz _ (by omega))
        obtain ⟨z, he⟩ := hs ⟨y, hy⟩
        have hev := congrArg Subtype.val he
        rw [linearSequenceMultiply_apply] at hev
        simp only [Subtype.coe_mk] at hev
        rw [← hev]
        apply Submodule.sum_mem
        intro i _
        simpa only [Algebra.smul_def] using
          P.smul_mem (r i) (ih q (Nat.lt_succ_self q) _ (z i).property)
  have htop : P = ⊤ := by
    have hle : (⨆ q, 𝒜 q) ≤ P.restrictScalars k := iSup_le hm
    rw [(Decomposition.isInternal 𝒜).submodule_iSup_eq_top] at hle
    exact Submodule.eq_top_iff'.mpr (fun y => hle (Submodule.mem_top))
  exact Module.Finite.of_fg_top (htop ▸ hP)

include hr in
/-- Graded Nakayama for linear parameters, stated using the actual quotient algebra. -/
theorem finite_over_parameters_of_finite_quotient
    [Module.Finite k (A ⧸ Ideal.span (Set.range (fun i => algebraMap R A (r i))))] :
    Module.Finite R A := by
  let I : Ideal A := Ideal.span (Set.range (fun i => algebraMap R A (r i)))
  have hI : I.IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro x ⟨i, rfl⟩
    exact ⟨1, hr i⟩
  letI := gradedQuotientAlgebra 𝒜 I hI
  obtain ⟨N, hN⟩ := exists_gradedPiece_bound (gradedQuotientPiece 𝒜 I)
  exact finite_over_parameters_of_graded_bound 𝒜 r hr (N + 1) (Nat.succ_pos _)
    (fun q hq => hN q (by omega))

end BPFixedPoints.ResolutionTools
