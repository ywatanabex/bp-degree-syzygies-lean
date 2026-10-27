import BPFixedPoints.Incidence.ResolutionNativeAllYoneda
import BPFixedPoints.Incidence.ResolutionNativeBoundaryHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Morphisms from a resolution to a single complex in the derived category

Let `P` be a chain complex exact in positive degrees with an exact epic augmentation `P.X 0 ⟶ A`,
and let `Y` be an object against which `P` is acyclic (`ComplexAcyclicAgainst P Y`: all higher
`Ext` from the terms of `P` to `Y` vanish). This file shows that the functor
`DerivedCategory.Qh` is bijective on morphisms from the negative cochain complex of `P` to every
single complex on `Y` (`qh_map_bijective_negativeComplex_single`): homotopy classes of maps compute
morphisms in the derived category. The proof reduces to the existing comparison of the cohomology
of `Hom(P, Y)` with `Ext(A, Y)` (`nativeCohomologyAtComparison_bijective`), using that every chain
map to a single complex is a cocycle map (`negativeComplex_toSingle_eq`), that boundaries are
null-homotopic (`negativeBoundaryHomotopy`), and, in positive degrees, the vanishing of morphisms
between single complexes in the wrong order.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open BPFixedPoints.ExtResolutionTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

universe w w' v u

section Base

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every chain map from the negative cochain complex of `P` to a single complex in degree `-i`
is the cocycle map of a cocycle `x : P.X i ⟶ Y`. -/
theorem negativeComplex_toSingle_eq (P : ChainComplex C ℕ) (i : ℕ) (Y : C)
    (φ : negativeComplex P ⟶ (single C (ComplexShape.up ℤ) (-(i : ℤ))).obj Y) :
    ∃ (x : P.X i ⟶ Y) (hx : P.d (i + 1) i ≫ x = 0), φ = negativeCocycleMap P i x hx := by
  have hi : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  have hi1 : ComplexShape.embeddingDownNat.f (i + 1) = -(i : ℤ) - 1 := by
    change -(((i + 1 : ℕ) : ℤ)) = _
    push_cast
    ring
  let x : P.X i ⟶ Y := (P.extendXIso ComplexShape.embeddingDownNat hi).inv ≫
    φ.f (-(i : ℤ)) ≫ (singleObjXSelf (ComplexShape.up ℤ) (-(i : ℤ)) Y).hom
  have hx : P.d (i + 1) i ≫ x = 0 := by
    have hc := φ.comm (-(i : ℤ) - 1) (-(i : ℤ))
    rw [extend_d_eq _ _ hi1 hi] at hc
    have hs : ((single C (ComplexShape.up ℤ) (-(i : ℤ))).obj Y).d (-(i : ℤ) - 1) (-(i : ℤ)) = 0 :=
      by simp
    rw [hs, comp_zero] at hc
    have hc' : P.d (i + 1) i ≫ (P.extendXIso ComplexShape.embeddingDownNat hi).inv ≫
        φ.f (-(i : ℤ)) = 0 := by
      have := congrArg (fun f => (P.extendXIso ComplexShape.embeddingDownNat hi1).inv ≫ f) hc
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using this.symm
    simp only [x, ← Category.assoc] at hc' ⊢
    rw [hc', zero_comp]
  refine ⟨x, hx, ?_⟩
  apply to_single_hom_ext
  rw [negativeCocycleMap_component]
  simp only [x, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The cocycle map of the zero cocycle is zero. -/
theorem negativeCocycleMap_zero (P : ChainComplex C ℕ) (i : ℕ) (Y : C)
    (h : P.d (i + 1) i ≫ (0 : P.X i ⟶ Y) = 0) : negativeCocycleMap P i (0 : P.X i ⟶ Y) h = 0 := by
  apply to_single_hom_ext
  rw [negativeCocycleMap_component]
  simp

variable [HasDerivedCategory.{w} C] [HasExt.{w'} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π = 0)
  (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n + 1))

include π z e hP in
/-- The localization functor `Q` is bijective, up to homotopy, on morphisms from the negative
complex of a resolution to a single complex on an object against which the resolution is
acyclic. -/
theorem negativeComplex_single_Q (Y : C) (ha : ComplexAcyclicAgainst P Y) (p : ℤ) :
    (∀ φ : negativeComplex P ⟶ (single C (ComplexShape.up ℤ) p).obj Y,
        DerivedCategory.Q.map φ = 0 → (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ = 0) ∧
      (∀ g : DerivedCategory.Q.obj (negativeComplex P) ⟶
          DerivedCategory.Q.obj ((single C (ComplexShape.up ℤ) p).obj Y),
        ∃ φ, DerivedCategory.Q.map φ = g) := by
  by_cases hp : 0 < p
  · have hφ : ∀ φ : negativeComplex P ⟶ (single C (ComplexShape.up ℤ) p).obj Y, φ = 0 := by
      intro φ
      apply HomologicalComplex.hom_ext
      intro q
      by_cases hq : q = p
      · subst hq
        exact (isZero_extend_X _ _ _ (fun n hn => by
          change -(n : ℤ) = q at hn
          omega)).eq_of_src _ _
      · exact (isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
    refine ⟨fun φ _ => by rw [hφ φ, Functor.map_zero], fun g => ⟨0, ?_⟩⟩
    have hs := DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
      ((CochainComplex.singleFunctor C 0).obj A) ((single C (ComplexShape.up ℤ) p).obj Y) 0 p hp
    have hg : (nativeAugmentationIso P π z e hP).inv ≫ g = 0 := Subsingleton.elim _ _
    rw [Functor.map_zero]
    calc (0 : DerivedCategory.Q.obj (negativeComplex P) ⟶ _) =
        (nativeAugmentationIso P π z e hP).hom ≫ (nativeAugmentationIso P π z e hP).inv ≫ g := by
          rw [hg, comp_zero]
      _ = g := by rw [Iso.hom_inv_id_assoc]
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, p = -(i : ℤ) := ⟨(-p).toNat, by omega⟩
    let Θ : (DerivedCategory.Q.obj (negativeComplex P) ⟶
        DerivedCategory.Q.obj ((single C (ComplexShape.up ℤ) (-(i : ℤ))).obj Y)) → Ext.{w'} A Y i :=
      fun g => Ext.homEquiv.symm ((nativeAugmentationIso P π z e hP).inv ≫ g ≫
        ((DerivedCategory.singleFunctors C).shiftIso (i : ℤ) (-(i : ℤ)) 0 (by omega)).inv.app Y)
    have hΘinj : Function.Injective Θ := by
      intro g₁ g₂ hg
      have h₁ := Ext.homEquiv.symm.injective hg
      have h₂ := congrArg (fun f => (nativeAugmentationIso P π z e hP).hom ≫ f ≫
        ((DerivedCategory.singleFunctors C).shiftIso (i : ℤ) (-(i : ℤ)) 0 (by omega)).hom.app Y) h₁
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app, Functor.comp_obj] at h₂
      erw [Category.comp_id, Category.comp_id] at h₂
      exact h₂
    have hΘ : ∀ (x : P.X i ⟶ Y) (hx : P.d (i + 1) i ≫ x = 0),
        Θ (DerivedCategory.Q.map (negativeCocycleMap P i x hx)) =
          nativeCocycleExt P π z e hP i x hx := by
      intro x hx
      simp only [Θ, nativeCocycleExt, nativeCocycleRoof, Category.assoc]
    have hcyc : ∀ (x : P.X i ⟶ Y), P.d (i + 1) i ≫ x = 0 → x ∈ (complexTower P hP).cycles Y i := by
      intro x hx
      change (complexTower P hP).differential i ≫ x = 0
      rw [complexTower_differential]
      exact hx
    have hbij := nativeCohomologyAtComparison_bijective P hP π z e Y ha i
    constructor
    · intro φ hφ
      obtain ⟨x, hx, rfl⟩ := negativeComplex_toSingle_eq P i Y φ
      have h0 : nativeCocycleExt P π z e hP i x hx = 0 := by
        rw [← hΘ, hφ]
        apply Ext.ext
        simp only [Θ, zero_comp, comp_zero, Ext.zero_hom]
        exact Ext.homEquiv.apply_symm_apply _
      have hc : (complexTower P hP).classAt Y i ⟨x, hcyc x hx⟩ = 0 := by
        apply hbij.1
        rw [map_zero, nativeCohomologyAtComparison_class]
        exact h0
      cases i with
      | zero =>
        rw [ExactTower.classAt_zero] at hc
        have hx0 : x = 0 := congrArg Subtype.val hc
        subst hx0
        rw [negativeCocycleMap_zero, Functor.map_zero]
      | succ k =>
        rw [ExactTower.classAt_succ, QuotientAddGroup.eq_zero_iff] at hc
        obtain ⟨g, hg⟩ := hc
        have hxg : x = P.d (k + 1) k ≫ g := by
          have := congrArg Subtype.val hg
          change (complexTower P hP).differential k ≫ g = x at this
          rw [complexTower_differential] at this
          exact this.symm
        subst hxg
        rw [HomotopyCategory.eq_of_homotopy _ _ (negativeBoundaryHomotopy P k g), Functor.map_zero]
    · intro g
      obtain ⟨c, hc⟩ := hbij.2 (Θ g)
      obtain ⟨x, rfl⟩ := (complexTower P hP).classAt_surjective Y i c
      have hx : P.d (i + 1) i ≫ x.val = 0 := by
        have h : (complexTower P hP).differential i ≫ x.val = 0 := x.property
        rwa [complexTower_differential] at h
      refine ⟨negativeCocycleMap P i x.val hx, hΘinj ?_⟩
      rw [hΘ, ← hc, nativeCohomologyAtComparison_class]
      rfl

include π z e hP in
/-- **The base case: single complexes.** For an object `Y` against which the resolution `P` is
acyclic, the functor `Qh` from the homotopy category to the derived category is bijective on
morphisms from the negative complex of `P` to every single complex on `Y`. -/
theorem qh_map_bijective_negativeComplex_single (Y : C) (ha : ComplexAcyclicAgainst P Y) (p : ℤ) :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (negativeComplex P) ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((single C (ComplexShape.up ℤ) p).obj Y)) → _) := by
  obtain ⟨hinj, hsurj⟩ := negativeComplex_single_Q P π z e hP Y ha p
  let E := DerivedCategory.quotientCompQhIso C
  have hnat : ∀ φ : negativeComplex P ⟶ (single C (ComplexShape.up ℤ) p).obj Y,
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ) =
        E.hom.app _ ≫ DerivedCategory.Q.map φ ≫ E.inv.app _ := by
    intro φ
    have h := E.hom.naturality φ
    dsimp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  constructor
  · intro a b hab
    obtain ⟨φa, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective a
    obtain ⟨φb, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective b
    rw [hnat, hnat] at hab
    have hab' : DerivedCategory.Q.map (φa - φb) = 0 := by
      have := congrArg (fun f => E.inv.app _ ≫ f ≫ E.hom.app _) hab
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
        Category.comp_id] at this
      rw [Functor.map_sub, this, sub_self]
    have := hinj _ hab'
    rw [Functor.map_sub, sub_eq_zero] at this
    exact this
  · intro g
    obtain ⟨φ, hφ⟩ := hsurj (E.inv.app _ ≫ g ≫ E.hom.app _)
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ, ?_⟩
    rw [hnat, hφ]
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    erw [Category.comp_id]

end Base

end BPFixedPoints.Multigraph
