import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-! # Splitting off the bottom term of a chain complex, and induction on the length

For a chain complex `Y` indexed by `ℕ` in an abelian category, the inclusion of its degree-zero term
and the projection onto `Y` with that term removed (`chainBottomInclusion`,
`chainBottomProjection`, `chainBottomQuotient`) give, after extension to cochain complexes along
`n ↦ p - n`, a degreewise split short exact sequence (`bottomShortComplex`, `bottomSplitting`) and
hence a distinguished triangle in the homotopy category (`bottomTriangle_distinguished`). The third
term is the truncation `ChainComplex.truncate Y` extended along `n ↦ p - 1 - n`
(`bottomQuotientExtendIso`). This gives an induction principle on the length of a bounded chain
complex (`chainExtend_induction`): a property of objects of the homotopy category that is invariant
under isomorphism, holds for zero objects, satisfies two-out-of-three in distinguished triangles and
holds for single complexes on a class of objects holds for every bounded chain complex with terms
in that class.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open ComplexShape ZeroObject

set_option linter.unusedSectionVars false

section Truncation

variable {C : Type*} [Category C] [Abelian C]

/-- The chain complex `Y` with its degree-zero term replaced by zero. -/
noncomputable def chainBottomQuotient (Y : ChainComplex C ℕ) : ChainComplex C ℕ :=
  ChainComplex.augment (ChainComplex.truncate.obj Y)
    (0 : (ChainComplex.truncate.obj Y).X 0 ⟶ 0) comp_zero

/-- The inclusion of the degree-zero term of a chain complex. -/
noncomputable def chainBottomInclusion (Y : ChainComplex C ℕ) :
    (ChainComplex.single₀ C).obj (Y.X 0) ⟶ Y :=
  mkHomFromSingle (𝟙 (Y.X 0)) (fun k hk => by
    simp only [ComplexShape.down_Rel] at hk
    omega)

/-- The projection of a chain complex onto the complex with its degree-zero term removed. -/
noncomputable def chainBottomProjection (Y : ChainComplex C ℕ) : Y ⟶ chainBottomQuotient Y where
  f n := match n with
    | 0 => 0
    | n + 1 => 𝟙 (Y.X (n + 1))
  comm' i j hij := by
    have hij' : j + 1 = i := by simpa only [ComplexShape.down_Rel] using hij
    subst hij'
    cases j with
    | zero =>
      change 𝟙 _ ≫ (0 : Y.X 1 ⟶ 0) = Y.d 1 0 ≫ 0
      simp
    | succ j =>
      change 𝟙 _ ≫ Y.d (j + 2) (j + 1) = Y.d (j + 2) (j + 1) ≫ 𝟙 _
      simp

/-- The projection to the bottom quotient is the identity in positive degrees. -/
@[simp] theorem chainBottomProjection_f_succ (Y : ChainComplex C ℕ) (n : ℕ) :
    (chainBottomProjection Y).f (n + 1) = 𝟙 (Y.X (n + 1)) := rfl

/-- The inclusion of the bottom term followed by the projection to the bottom quotient is zero. -/
theorem chainBottomInclusion_projection (Y : ChainComplex C ℕ) :
    chainBottomInclusion Y ≫ chainBottomProjection Y = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  cases n with
  | zero =>
    exact IsZero.eq_of_tgt (isZero_zero C) _ _
  | succ n =>
    exact IsZero.eq_of_src (isZero_single_obj_X _ _ _ _ (by omega)) _ _

/-- The degreewise split short exact sequence `Y₀ → Y → Y/Y₀` of cochain complexes, extended
along `n ↦ p - n`. -/
noncomputable def bottomShortComplex (Y : ChainComplex C ℕ) (p : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (extendMap (chainBottomInclusion Y) (embeddingUpIntLE p))
    (extendMap (chainBottomProjection Y) (embeddingUpIntLE p)) (by
      rw [← extendMap_comp, chainBottomInclusion_projection, extendMap_zero])

/-- The degreewise splitting of `bottomShortComplex`. -/
noncomputable def bottomSplitting (Y : ChainComplex C ℕ) (p q : ℤ) :
    ((bottomShortComplex Y p).map (eval C (up ℤ) q)).Splitting := by
  by_cases hq : q = p
  · have h0 : (embeddingUpIntLE p).f 0 = q := by simp [hq]
    refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_
    · change IsIso ((extendMap (chainBottomInclusion Y) (embeddingUpIntLE p)).f q)
      rw [extendMap_f _ _ h0]
      dsimp only [chainBottomInclusion]
      rw [mkHomFromSingle_f]
      infer_instance
    · exact (isZero_zero C).of_iso ((chainBottomQuotient Y).extendXIso (embeddingUpIntLE p) h0)
  · by_cases hlt : q < p
    · have hk : (embeddingUpIntLE p).f ((p - 1 - q).toNat + 1) = q := by
        simp only [embeddingUpIntLE_f]
        omega
      refine ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_
      · exact (isZero_single_obj_X _ _ _ _ (by omega)).of_iso
          (((ChainComplex.single₀ C).obj (Y.X 0)).extendXIso (embeddingUpIntLE p) hk)
      · change IsIso ((extendMap (chainBottomProjection Y) (embeddingUpIntLE p)).f q)
        rw [extendMap_f _ _ hk, chainBottomProjection_f_succ]
        exact (Y.extendXIso (embeddingUpIntLE p) hk ≪≫ Iso.refl _ ≪≫
          ((chainBottomQuotient Y).extendXIso (embeddingUpIntLE p) hk).symm).isIso_hom
    · have hn : ∀ i : ℕ, (embeddingUpIntLE p).f i ≠ q := by
        intro i hi
        simp only [embeddingUpIntLE_f] at hi
        omega
      exact ShortComplex.Splitting.ofIsZero _ (isZero_extend_X _ _ _ hn)
        (isZero_extend_X _ _ _ hn) (isZero_extend_X _ _ _ hn)

/-- The distinguished triangle in the homotopy category attached to `bottomShortComplex`. -/
theorem bottomTriangle_distinguished (Y : ChainComplex C ℕ) (p : ℤ) :
    CochainComplex.trianglehOfDegreewiseSplit (bottomShortComplex Y p) (bottomSplitting Y p) ∈
      distTriang (HomotopyCategory C (up ℤ)) :=
  CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _

/-- The terms of the bottom quotient in positive degree are those of the truncation. -/
noncomputable def chainBottomQuotientXIso (Y : ChainComplex C ℕ) (k : ℕ) :
    (chainBottomQuotient Y).X (k + 1) ≅ (ChainComplex.truncate.obj Y).X k :=
  Iso.refl _

/-- The differentials of the bottom quotient are those of the truncation, through the bridging
isomorphisms. -/
theorem chainBottomQuotient_d (Y : ChainComplex C ℕ) (k k' : ℕ) :
    (chainBottomQuotient Y).d (k + 1) (k' + 1) =
      (chainBottomQuotientXIso Y k).hom ≫ (ChainComplex.truncate.obj Y).d k k' ≫
        (chainBottomQuotientXIso Y k').inv := by
  dsimp only [chainBottomQuotientXIso, Iso.refl_hom, Iso.refl_inv]
  erw [Category.id_comp, Category.comp_id]
  exact ChainComplex.augment_d_succ_succ _ _ _ _ _

/-- Away from the degrees `q ≤ p - 1`, the extended bottom quotient is zero. -/
theorem isZero_bottomQuotient_extend_X (Y : ChainComplex C ℕ) (p q : ℤ) (h : ¬ q ≤ p - 1) :
    IsZero (((chainBottomQuotient Y).extend (embeddingUpIntLE p)).X q) := by
  by_cases hqp : q = p
  · exact (isZero_zero C).of_iso ((chainBottomQuotient Y).extendXIso _
      (show (embeddingUpIntLE p).f 0 = q by simp [hqp]))
  · exact isZero_extend_X _ _ _ (fun i hi => by simp only [embeddingUpIntLE_f] at hi; omega)

/-- The components of the identification of the extended bottom quotient with the extended
truncation, shifted by one. -/
noncomputable def bottomQuotientExtendXIso (Y : ChainComplex C ℕ) (p q : ℤ) :
    ((chainBottomQuotient Y).extend (embeddingUpIntLE p)).X q ≅
      ((ChainComplex.truncate.obj Y).extend (embeddingUpIntLE (p - 1))).X q :=
  if h : q ≤ p - 1 then
    ((chainBottomQuotient Y).extendXIso (embeddingUpIntLE p)
        (show (embeddingUpIntLE p).f ((p - 1 - q).toNat + 1) = q by
          simp only [embeddingUpIntLE_f]; omega)) ≪≫
      chainBottomQuotientXIso Y (p - 1 - q).toNat ≪≫
      ((ChainComplex.truncate.obj Y).extendXIso (embeddingUpIntLE (p - 1))
        (show (embeddingUpIntLE (p - 1)).f (p - 1 - q).toNat = q by
          simp only [embeddingUpIntLE_f]; omega)).symm
  else
    IsZero.iso (isZero_bottomQuotient_extend_X Y p q h)
      (isZero_extend_X _ _ _ (fun i hi => by simp only [embeddingUpIntLE_f] at hi; omega))

/-- **The extended bottom quotient is the extended truncation.** Extending `Y` with its degree-zero
term removed along `n ↦ p - n` gives the truncation of `Y` extended along `n ↦ p - 1 - n`. -/
noncomputable def bottomQuotientExtendIso (Y : ChainComplex C ℕ) (p : ℤ) :
    (chainBottomQuotient Y).extend (embeddingUpIntLE p) ≅
      (ChainComplex.truncate.obj Y).extend (embeddingUpIntLE (p - 1)) :=
  Hom.isoOfComponents (bottomQuotientExtendXIso Y p) (by
    intro q q' hqq'
    have hq' : q + 1 = q' := by simpa only [ComplexShape.up_Rel] using hqq'
    by_cases h' : q' ≤ p - 1
    · have h : q ≤ p - 1 := by omega
      have hi : (embeddingUpIntLE p).f ((p - 1 - q).toNat + 1) = q := by
        simp only [embeddingUpIntLE_f]; omega
      have hj : (embeddingUpIntLE p).f ((p - 1 - q').toNat + 1) = q' := by
        simp only [embeddingUpIntLE_f]; omega
      have hi' : (embeddingUpIntLE (p - 1)).f (p - 1 - q).toNat = q := by
        simp only [embeddingUpIntLE_f]; omega
      have hj' : (embeddingUpIntLE (p - 1)).f (p - 1 - q').toNat = q' := by
        simp only [embeddingUpIntLE_f]; omega
      have e₁ : (bottomQuotientExtendXIso Y p q).hom =
          ((chainBottomQuotient Y).extendXIso (embeddingUpIntLE p) hi).hom ≫
            (chainBottomQuotientXIso Y (p - 1 - q).toNat).hom ≫
            ((ChainComplex.truncate.obj Y).extendXIso (embeddingUpIntLE (p - 1)) hi').inv := by
        rw [bottomQuotientExtendXIso, dite_eq_left h]
        rfl
      have e₂ : (bottomQuotientExtendXIso Y p q').hom =
          ((chainBottomQuotient Y).extendXIso (embeddingUpIntLE p) hj).hom ≫
            (chainBottomQuotientXIso Y (p - 1 - q').toNat).hom ≫
            ((ChainComplex.truncate.obj Y).extendXIso (embeddingUpIntLE (p - 1)) hj').inv := by
        rw [bottomQuotientExtendXIso, dite_eq_left h']
        rfl
      rw [e₁, e₂, extend_d_eq _ _ hi' hj', extend_d_eq _ _ hi hj, chainBottomQuotient_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · exact IsZero.eq_of_tgt (isZero_extend_X _ _ _
        (fun i hi => by simp only [embeddingUpIntLE_f] at hi; omega)) _ _)

/-- **Induction on the length of a chain complex.** Let `Pr` be a property of objects of the
homotopy category which is invariant under isomorphism, holds for zero objects and satisfies the
two-out-of-three property in distinguished triangles (for the middle object). If it holds for all
single complexes on objects of a class `Ac`, it holds for every bounded chain complex with terms in
`Ac`, extended to cochain complexes along `n ↦ p - n`. -/
theorem chainExtend_induction (Pr : HomotopyCategory C (up ℤ) → Prop)
    (hiso : ∀ {X Y : HomotopyCategory C (up ℤ)}, (X ≅ Y) → Pr X → Pr Y)
    (hzero : ∀ X : HomotopyCategory C (up ℤ), IsZero X → Pr X)
    (htri : ∀ T ∈ distTriang (HomotopyCategory C (up ℤ)), Pr T.obj₁ → Pr T.obj₃ → Pr T.obj₂)
    (Ac : C → Prop)
    (hsingle : ∀ (A : C) (p : ℤ), Ac A →
      Pr ((HomotopyCategory.quotient C (up ℤ)).obj ((HomologicalComplex.single C (up ℤ) p).obj A)))
    (m : ℕ) : ∀ (Y : ChainComplex C ℕ), (∀ n, m ≤ n → IsZero (Y.X n)) → (∀ n, Ac (Y.X n)) →
      ∀ p : ℤ, Pr ((HomotopyCategory.quotient C (up ℤ)).obj (Y.extend (embeddingUpIntLE p))) := by
  induction m with
  | zero =>
    intro Y hY _ p
    apply hzero
    apply Functor.map_isZero
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ (fun q => ?_)
    by_cases hq : ∃ i, (embeddingUpIntLE p).f i = q
    · obtain ⟨i, hi⟩ := hq
      exact ((hY i (Nat.zero_le i)).of_iso (Y.extendXIso _ hi)).eq_of_src _ _
    · exact (isZero_extend_X _ _ _ (fun i hi => hq ⟨i, hi⟩)).eq_of_src _ _
  | succ m ih =>
    intro Y hY hA p
    refine htri _ (bottomTriangle_distinguished Y p) ?_ ?_
    · exact hiso ((HomotopyCategory.quotient C (up ℤ)).mapIso
        (extendSingleIso (embeddingUpIntLE p) (Y.X 0) 0 p (by simp))).symm
        (hsingle (Y.X 0) p (hA 0))
    · exact hiso ((HomotopyCategory.quotient C (up ℤ)).mapIso (bottomQuotientExtendIso Y p)).symm
        (ih (ChainComplex.truncate.obj Y) (fun n hn => hY (n + 1) (by omega)) (fun n => hA (n + 1))
          (p - 1))

end Truncation

end BPFixedPoints.Multigraph
