import BPFixedPoints.Incidence.CoefficientGrading
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of homogeneous polynomials and weighted free terms

Count monomial bases of the actual homogeneous pieces. Negative coefficient
degrees contribute zero, rather than being replaced by degree zero through
truncated natural subtraction.
-/

namespace BPFixedPoints.ResolutionTools
open Finsupp
set_option backward.isDefEq.respectTransparency false

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable instance homogeneousCoeffPiece_finite (n : ℤ) :
    Module.Finite k (homogeneousCoeffPiece (σ := σ) (k := k) n) := by
  by_cases hn : 0 ≤ n
  · rw [homogeneousCoeffPiece, if_pos hn]
    exact Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg σ k _)
  · rw [homogeneousCoeffPiece_negative (by omega)]
    infer_instance

theorem finrank_homogeneousSubmodule (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Nat.multichoose (Fintype.card σ) n := by
  classical
  let e : Sym σ n ≃ ↑{d : σ →₀ ℕ | d.degree = n} := Sym.equivNatSum σ n
  letI : Fintype ↑{d : σ →₀ ℕ | d.degree = n} := Fintype.ofEquiv (Sym σ n) e
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank k (MvPolynomial.restrictSupport k {d : σ →₀ ℕ | d.degree = n}) = _
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k {d : σ →₀ ℕ | d.degree = n})]
  rw [← Fintype.card_congr e, Sym.card_sym_eq_multichoose]

theorem finrank_homogeneousCoeffPiece (n : ℤ) :
    Module.finrank k (homogeneousCoeffPiece (σ := σ) (k := k) n) =
      if 0 ≤ n then Nat.multichoose (Fintype.card σ) n.toNat else 0 := by
  by_cases hn : 0 ≤ n
  · rw [homogeneousCoeffPiece, if_pos hn, if_pos hn]
    exact finrank_homogeneousSubmodule (k := k) (σ := σ) _
  · rw [homogeneousCoeffPiece, if_neg hn, if_neg hn]
    simp

variable {I : Type*} [Fintype I] (w : I → ℕ)

/-- Decompose a weighted free term with finitely many generators into a product of homogeneous coefficient spaces. -/
noncomputable def weightedFreePieceEquivPi (n : ℤ) :
    weightedFreePiece (σ := σ) (k := k) w n ≃ₗ[k]
      ∀ i, homogeneousCoeffPiece (σ := σ) (k := k) (n - (w i : ℤ)) where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val), fun i => by
    simpa using (f i).property⟩
  left_inv x := by ext i; rfl
  right_inv f := by ext i; rfl
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

noncomputable instance weightedFreePiece_finite (n : ℤ) :
    Module.Finite k (weightedFreePiece (σ := σ) (k := k) w n) :=
  Module.Finite.of_surjective (weightedFreePieceEquivPi w n).symm.toLinearMap
    (weightedFreePieceEquivPi w n).symm.surjective

theorem finrank_weightedFreePiece (n : ℤ) :
    Module.finrank k (weightedFreePiece (σ := σ) (k := k) w n) =
      ∑ i, if (w i : ℤ) ≤ n then Nat.multichoose (Fintype.card σ) (n - (w i : ℤ)).toNat else 0 := by
  rw [(weightedFreePieceEquivPi (σ := σ) (k := k) w n).finrank_eq,
    Module.finrank_pi_fintype]
  simp only [finrank_homogeneousCoeffPiece, sub_nonneg]

end BPFixedPoints.ResolutionTools
