import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedBase
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-! # Blocks of Hom-complex cochains between two extended chain complexes

For chain complexes `P` and `Y` indexed by `ℕ`, the negative complex of `P` (`n ↦ -n`) and the
extension of `Y` along `n ↦ -n` are cochain complexes concentrated in nonpositive degrees. A
cochain of degree `m` between them is the same as a family of blocks `P_i ⟶ Y_k` with
`i = k + m`; this file proves that and computes the Hom-complex differential on blocks.

* `cochainBlock`: the block `P_i ⟶ Y_k` of a cochain, additively.
* `cochain_ext_of_blocks`: a cochain is determined by its blocks.
* `cochainOfBlocks`, `cochainBlock_ofBlocks`: every family of blocks comes from a cochain.
* `cochainBlock_δ_zero`, `cochainBlock_δ_succ`: the blocks of `δ z` are
  `z_{i,k+1} ≫ d_Y + (-1)^{m+1} d_P ≫ z_{i-1,k}` (the second term absent for `i = 0`).

Nothing about sheaves is used here.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape
open BPFixedPoints.ExtResolutionTools CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

universe v u

/-- The embedding `n ↦ 0 - n` sends `k` to `-k`. -/
theorem embeddingUpIntLE_zero_f (k : ℕ) : (embeddingUpIntLE 0).f k = -(k : ℤ) := by simp

section Blocks

variable {C : Type u} [Category.{v} C] [Abelian C] (P Y : ChainComplex C ℕ)

/-- **The block of a cochain.** For a cochain `z` of degree `m` from the negative complex of `P`
to the extension of `Y` along `n ↦ -n`, and `i = k + m`, the component of `z` from degree `-i`
to degree `-k`, read as a morphism `P_i ⟶ Y_k`. It is additive in `z`. -/
noncomputable def cochainBlock {m : ℤ} (i k : ℕ) (h : (i : ℤ) = k + m) :
    Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m →+ (P.X i ⟶ Y.X k) where
  toFun z := (P.extendXIso embeddingDownNat (rfl : embeddingDownNat.f i = -(i : ℤ))).inv ≫
      z.v (-(i : ℤ)) (-(k : ℤ)) (by omega) ≫
      (Y.extendXIso (embeddingUpIntLE 0) (embeddingUpIntLE_zero_f k)).hom
  map_zero' := by
    simp only [Cochain.zero_v, zero_comp, comp_zero]
  map_add' z z' := by
    simp only [Cochain.add_v, Preadditive.add_comp, Preadditive.comp_add]

/-- The block is the component of the cochain, conjugated by the extension isomorphisms. -/
theorem cochainBlock_apply {m : ℤ} (i k : ℕ) (h : (i : ℤ) = k + m)
    (z : Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m) :
    cochainBlock P Y i k h z =
      (P.extendXIso embeddingDownNat (rfl : embeddingDownNat.f i = -(i : ℤ))).inv ≫
        z.v (-(i : ℤ)) (-(k : ℤ)) (by omega) ≫
        (Y.extendXIso (embeddingUpIntLE 0) (embeddingUpIntLE_zero_f k)).hom := rfl

/-- **A cochain is determined by its blocks.** -/
theorem cochain_ext_of_blocks {m : ℤ}
    (z z' : Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m)
    (h : ∀ (i k : ℕ) (hik : (i : ℤ) = k + m), cochainBlock P Y i k hik z = cochainBlock P Y i k hik z') :
    z = z' := by
  ext p q hpq
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, p = -(i : ℤ) := ⟨(-p).toNat, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = -(k : ℤ) := ⟨(-q).toNat, by omega⟩
      have hb := h i k (by omega)
      rw [cochainBlock_apply, cochainBlock_apply] at hb
      exact (cancel_mono _).mp ((cancel_epi _).mp hb)
    · apply IsZero.eq_of_tgt
      apply isZero_extend_X
      intro k hk
      rw [embeddingUpIntLE_zero_f] at hk
      omega
  · apply IsZero.eq_of_src
    apply isZero_extend_X
    intro i hi
    change -(i : ℤ) = p at hi
    omega

/-- **The cochain with prescribed blocks.** Its component from degree `p ≤ 0` to degree
`q ≤ 0` is the block `P_{-p} ⟶ Y_{-q}`, conjugated by the extension isomorphisms; all other
components are zero (their source or target is zero). -/
noncomputable def cochainOfBlocks {m : ℤ} (B : ∀ (i k : ℕ), (i : ℤ) = k + m → (P.X i ⟶ Y.X k)) :
    Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m :=
  Cochain.mk fun p q hpq =>
    if hp : p ≤ 0 then
      if hq : q ≤ 0 then
        (P.extendXIso embeddingDownNat
            (show embeddingDownNat.f (-p).toNat = p by
              change -(((-p).toNat : ℕ) : ℤ) = p
              omega)).hom ≫
          B (-p).toNat (-q).toNat (by omega) ≫
          (Y.extendXIso (embeddingUpIntLE 0)
            (show (embeddingUpIntLE 0).f (-q).toNat = q by
              rw [embeddingUpIntLE_zero_f]
              omega)).inv
      else 0
    else 0

/-- Transport of a block along equalities of its indices. -/
theorem blocks_transport {m : ℤ} (B : ∀ (i k : ℕ), (i : ℤ) = k + m → (P.X i ⟶ Y.X k))
    (i k : ℕ) (h : (i : ℤ) = k + m) :
    ∀ (i' k' : ℕ) (_ : i' = i) (_ : k' = k) (h₁ : embeddingDownNat.f i' = -(i : ℤ))
      (h₂ : (embeddingUpIntLE 0).f k' = -(k : ℤ)) (h' : (i' : ℤ) = k' + m),
      (P.extendXIso embeddingDownNat h₁).hom ≫ B i' k' h' ≫
          (Y.extendXIso (embeddingUpIntLE 0) h₂).inv =
        (P.extendXIso embeddingDownNat (rfl : embeddingDownNat.f i = -(i : ℤ))).hom ≫ B i k h ≫
          (Y.extendXIso (embeddingUpIntLE 0) (embeddingUpIntLE_zero_f k)).inv := by
  rintro _ _ rfl rfl _ _ _
  rfl

/-- **The blocks of `cochainOfBlocks B` are `B`.** -/
theorem cochainBlock_ofBlocks {m : ℤ} (B : ∀ (i k : ℕ), (i : ℤ) = k + m → (P.X i ⟶ Y.X k))
    (i k : ℕ) (h : (i : ℤ) = k + m) :
    cochainBlock P Y i k h (cochainOfBlocks P Y B) = B i k h := by
  rw [cochainBlock_apply, cochainOfBlocks, Cochain.mk_v]
  have hp : -(i : ℤ) ≤ 0 := by omega
  have hq : -(k : ℤ) ≤ 0 := by omega
  simp only [hp, hq, dite_true]
  rw [blocks_transport P Y B i k h _ _ (by omega) (by omega)]
  simp

/-- **The Hom differential on blocks, source degree zero.** For `0 = k + m'`, the block of
`δ z` is `z_{0,k+1} ≫ d_Y`. -/
theorem cochainBlock_δ_zero {m m' : ℤ} (hm : m + 1 = m')
    (z : Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m) (k : ℕ)
    (h : ((0 : ℕ) : ℤ) = k + m') :
    cochainBlock P Y 0 k h (δ m m' z) =
      cochainBlock P Y 0 (k + 1) (by omega) z ≫ Y.d (k + 1) k := by
  rw [cochainBlock_apply, cochainBlock_apply,
    δ_v m m' hm z _ _ _ (-((k + 1 : ℕ) : ℤ)) 1 (by omega) (by omega)]
  have hz : (negativeComplex P).d (-((0 : ℕ) : ℤ)) 1 = 0 := by
    apply IsZero.eq_of_tgt
    apply isZero_extend_X
    intro i hi
    change -(i : ℤ) = 1 at hi
    omega
  rw [hz, zero_comp, smul_zero, add_zero,
    extend_d_eq Y (embeddingUpIntLE 0) (embeddingUpIntLE_zero_f (k + 1)) (embeddingUpIntLE_zero_f k)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The Hom differential on blocks.** For `i + 1 = k + m'` with `m + 1 = m'`, the block of
`δ z` is `z_{i+1,k+1} ≫ d_Y + (-1)^{m'} • (d_P ≫ z_{i,k})`. -/
theorem cochainBlock_δ_succ {m m' : ℤ} (hm : m + 1 = m')
    (z : Cochain (negativeComplex P) (Y.extend (embeddingUpIntLE 0)) m) (i k : ℕ)
    (h : ((i + 1 : ℕ) : ℤ) = k + m') :
    cochainBlock P Y (i + 1) k h (δ m m' z) =
      cochainBlock P Y (i + 1) (k + 1) (by omega) z ≫ Y.d (k + 1) k +
        m'.negOnePow • (P.d (i + 1) i ≫ cochainBlock P Y i k (by omega) z) := by
  rw [cochainBlock_apply, cochainBlock_apply, cochainBlock_apply,
    δ_v m m' hm z _ _ _ (-((k + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by omega) (by omega),
    extend_d_eq Y (embeddingUpIntLE 0) (embeddingUpIntLE_zero_f (k + 1)) (embeddingUpIntLE_zero_f k),
    extend_d_eq P embeddingDownNat (i' := -((i + 1 : ℕ) : ℤ)) (j' := -(i : ℤ)) (i := i + 1) (j := i)
      rfl rfl]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc, Units.smul_def, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]

end Blocks

end BPFixedPoints.Multigraph
