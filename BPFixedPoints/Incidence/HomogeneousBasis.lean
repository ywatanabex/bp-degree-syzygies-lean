import BPFixedPoints.Incidence.RegularLinearHilbert
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Homogeneous bases of finite-dimensional graded algebras -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- The disjoint union of bases of the actual homogeneous components. -/
abbrev HomogeneousBasisIndex := Σ q : ℕ, Module.Free.ChooseBasisIndex k (𝒜 q)

noncomputable def homogeneousBasis : Module.Basis (HomogeneousBasisIndex 𝒜) k A :=
  (Decomposition.isInternal 𝒜).collectedBasis (fun q => Module.Free.chooseBasis k (𝒜 q))

theorem homogeneousBasis_mem (i : HomogeneousBasisIndex 𝒜) :
    homogeneousBasis 𝒜 i ∈ 𝒜 i.1 :=
  (Decomposition.isInternal 𝒜).collectedBasis_mem _ i

theorem homogeneousBasis_repr_eq_zero {q : ℕ} {x : A} (hx : x ∈ 𝒜 q)
    (i : HomogeneousBasisIndex 𝒜) (hi : q ≠ i.1) :
    (homogeneousBasis 𝒜).repr x i = 0 :=
  (Decomposition.isInternal 𝒜).collectedBasis_repr_of_mem_ne _ hi hx

variable [Module.Finite k A]

noncomputable instance homogeneousBasisIndex_fintype : Fintype (HomogeneousBasisIndex 𝒜) :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis (homogeneousBasis 𝒜))

theorem card_homogeneousBasisIndex_fibre (q : ℕ) :
    Fintype.card {i : HomogeneousBasisIndex 𝒜 // i.1 = q} = Module.finrank k (𝒜 q) := by
  classical
  let e : {i : HomogeneousBasisIndex 𝒜 // i.1 = q} ≃
      Module.Free.ChooseBasisIndex k (𝒜 q) := {
    toFun := fun i => i.property ▸ i.val.2
    invFun := fun j => ⟨⟨q, j⟩, rfl⟩
    left_inv := by rintro ⟨⟨r, j⟩, h⟩; change r = q at h; subst r; rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Module.finrank_eq_card_basis (Module.Free.chooseBasis k (𝒜 q))]

/-- The numerator counting homogeneous basis degrees is the actual Hilbert series. -/
theorem homogeneousBasis_hilbert :
    (∑ i : HomogeneousBasisIndex 𝒜, (PowerSeries.X : PowerSeries ℤ) ^ i.1) =
      gradedHilbertSeries 𝒜 := by
  classical
  ext q
  simp only [map_sum, PowerSeries.coeff_X_pow, gradedHilbertSeries, PowerSeries.coeff_mk]
  have hsum : (∑ i : HomogeneousBasisIndex 𝒜, if q = i.1 then (1 : ℤ) else 0) =
      Fintype.card {i : HomogeneousBasisIndex 𝒜 // i.1 = q} := by
    simp [eq_comm, ← Fintype.card_subtype]
  rw [hsum, card_homogeneousBasisIndex_fibre]

end BPFixedPoints.ResolutionTools
