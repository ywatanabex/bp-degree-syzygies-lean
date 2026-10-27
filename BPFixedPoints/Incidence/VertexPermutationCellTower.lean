import BPFixedPoints.Incidence.AcyclicResolutionAugmentedSourceNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Yoneda representatives of augmented resolutions under exact functors

Let `F : C ⥤ D` be an additive exact functor between abelian categories. The image of an exact
tower (`ExtResolutionTools.ExactTower`) is an exact tower (`towerMap`), and Mathlib's map of Ext
groups along `F` (`Ext.mapExactFunctor`) carries the iterated Yoneda connecting maps and the Yoneda
representatives of closed cochains of a tower to those of the image tower
(`towerMap_connecting`, `towerMap_cocycleComparison`).

A chain map `χ : Q ⟶ F(P)` from a positively exact complex into the image of a positively exact
complex is a source map from the canonical tower of `Q` to the image of the canonical tower of `P`
(`complexMapSourceMap`). If `χ` is compatible with augmentations `P₀ → A` and `Q₀ → B` through a
map `a : B ⟶ F A`, then the augmented Yoneda representative of the pulled back image cochain is
`a` followed by the image of the augmented Yoneda representative
(`augmentedComplexCocycleComparison_map`).

These are general statements; no sheaves, schemes or states occur here.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian ExtResolutionTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

universe w w' v u u'

section Tower

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The image of an exact tower under an exact functor. -/
noncomputable def towerMap (T : ExactTower C) : ExactTower D where
  K n := F.obj (T.K n)
  P n := F.obj (T.P n)
  inclusion n := F.map (T.inclusion n)
  projection n := F.map (T.projection n)
  zero n := by rw [← F.map_comp, T.zero, F.map_zero]
  shortExact n := (T.shortExact n).map_of_exact F

/-- The image tower of the tail is the tail of the image tower. -/
theorem towerMap_tail (T : ExactTower C) : (towerMap F T).tail = towerMap F T.tail := rfl

section Ext
variable [HasExt.{w} C] [HasExt.{w'} D]

/-- Exact functors carry the iterated Yoneda connecting maps of a tower to those of its image. -/
theorem towerMap_connecting (Y : C) (q : ℕ) : ∀ (T : ExactTower C) (x : Ext.{w} (T.K q) Y 0),
    (T.connecting Y q x).mapExactFunctor F =
      (towerMap F T).connecting (F.obj Y) q (x.mapExactFunctor F) := by
  induction q with
  | zero => intro T x; rfl
  | succ q ih =>
    intro T x
    change ((T.shortExact 0).extClass.comp (T.tail.connecting Y q x) (by omega)).mapExactFunctor F =
      ((towerMap F T).shortExact 0).extClass.comp
        ((towerMap F T).tail.connecting (F.obj Y) q (x.mapExactFunctor F)) (by omega)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih T.tail x]
    rfl

end Ext

variable {T : ExactTower C} {Y : C}

/-- The image of a closed cochain of a tower is a closed cochain of the image tower. -/
def towerMapCycles (n : ℕ) (x : T.cycles Y n) : (towerMap F T).cycles (F.obj Y) n :=
  ⟨F.map x.val, by
    change (F.map (T.projection (n+1)) ≫ F.map (T.inclusion n)) ≫ F.map x.val = 0
    rw [← F.map_comp, ← F.map_comp]
    have hx : T.differential n ≫ x.val = 0 := x.property
    exact (congrArg F.map hx).trans (F.map_zero _ _)⟩

/-- The image cochain is the image of the cochain. -/
theorem towerMapCycles_val (n : ℕ) (x : T.cycles Y n) :
    (towerMapCycles F n x).val = F.map x.val := rfl

/-- The syzygy factorization of the image cochain is the image of the factorization. -/
theorem towerMap_cycleEquiv (n : ℕ) (x : T.cycles Y n) :
    (towerMap F T).cycleEquiv (F.obj Y) n (towerMapCycles F n x) = F.map (T.cycleEquiv Y n x) := by
  apply (cancel_epi ((towerMap F T).projection n)).mp
  rw [ExactTower.cycleEquiv_projection]
  change F.map x.val = F.map (T.projection n) ≫ F.map (T.cycleEquiv Y n x)
  rw [← F.map_comp, T.cycleEquiv_projection]

variable [HasExt.{w} C] [HasExt.{w'} D]

/-- **Exact functors and Yoneda representatives.** The image under an exact functor of the Ext
class represented by a closed cochain is the class of the image cochain in the image tower. -/
theorem towerMap_cocycleComparison (n : ℕ) (x : T.cycles Y n) :
    (T.cocycleComparison Y n x).mapExactFunctor F =
      (towerMap F T).cocycleComparison (F.obj Y) n (towerMapCycles F n x) := by
  change (T.connecting Y n (Ext.mk₀ (T.cycleEquiv Y n x))).mapExactFunctor F =
    (towerMap F T).connecting (F.obj Y) n (Ext.mk₀ ((towerMap F T).cycleEquiv (F.obj Y) n
      (towerMapCycles F n x)))
  rw [towerMap_connecting, Ext.mapExactFunctor_mk₀, towerMap_cycleEquiv]

end Tower

section Complex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {P : ChainComplex C ℕ} {Q : ChainComplex D ℕ} (hP : ∀ n, P.ExactAt (n+1))
  (hQ : ∀ n, Q.ExactAt (n+1)) (χ : Q ⟶ (F.mapHomologicalComplex _).obj P)

/-- The syzygy map of a chain map into the image of a complex. -/
noncomputable def complexMapSyzygy (n : ℕ) :
    complexSyzygy Q n ⟶ F.obj (complexSyzygy P n) :=
  cokernel.desc (Q.d (n+1) n) (χ.f n ≫ F.map (cokernel.π (P.d (n+1) n))) (by
    rw [← Category.assoc, (χ.comm (n+1) n).symm, Category.assoc]
    change χ.f (n+1) ≫ (F.map (P.d (n+1) n) ≫ F.map (cokernel.π (P.d (n+1) n))) = 0
    rw [← F.map_comp, cokernel.condition, F.map_zero, comp_zero])

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The syzygy map restricts the chain map on the cokernel projections. -/
theorem complexMapSyzygy_projection (n : ℕ) :
    cokernel.π (Q.d (n+1) n) ≫ complexMapSyzygy F χ n =
      χ.f n ≫ F.map (cokernel.π (P.d (n+1) n)) :=
  cokernel.π_desc _ _ _

/-- A chain map into the image of a complex is a source map from the tower of the source complex
to the image of the tower of the target complex. -/
noncomputable def complexMapSourceMap :
    ExactTower.SourceMap (complexTower Q hQ) (towerMap F (complexTower P hP)) where
  syzygy n := complexMapSyzygy F χ n
  term n := χ.f n
  inclusion n := by
    apply (cancel_epi (cokernel.π (Q.d (n+2) (n+1)))).mp
    change cokernel.π (Q.d (n+2) (n+1)) ≫ complexSyzygyInclusion Q n ≫ χ.f n =
      cokernel.π (Q.d (n+2) (n+1)) ≫ complexMapSyzygy F χ (n+1) ≫
        F.map (complexSyzygyInclusion P n)
    rw [← Category.assoc, complexSyzygy_factor, ← Category.assoc, complexMapSyzygy_projection,
      Category.assoc, ← F.map_comp, complexSyzygy_factor]
    exact (χ.comm (n+1) n).symm
  projection n := complexMapSyzygy_projection F χ n

variable {A : C} (πP : P.X 0 ⟶ A) (zP : P.d 1 0 ≫ πP = 0)
  (eP : (ShortComplex.mk (P.d 1 0) πP zP).Exact) [Epi πP]
variable {B : D} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ = 0)
  (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πQ]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The syzygy map in degree zero is the augmentation comparison. -/
theorem complexMapSyzygy_augmentation (a : B ⟶ F.obj A) (ha : χ.f 0 ≫ F.map πP = πQ ≫ a) :
    (complexAugmentationIso Q πQ zQ eQ).inv ≫ complexMapSyzygy F χ 0 =
      a ≫ F.map (complexAugmentationIso P πP zP eP).inv := by
  have hπ : cokernel.π (P.d 1 0) = πP ≫ (complexAugmentationIso P πP zP eP).inv := by
    rw [Iso.eq_comp_inv]
    exact complexAugmentationIso_projection P πP zP eP
  have hs : complexMapSyzygy F χ 0 = (complexAugmentationIso Q πQ zQ eQ).hom ≫ a ≫
      F.map (complexAugmentationIso P πP zP eP).inv := by
    apply (cancel_epi (cokernel.π (Q.d 1 0))).mp
    have h1 := complexMapSyzygy_projection F χ 0
    have h2 := complexAugmentationIso_projection Q πQ zQ eQ
    calc cokernel.π (Q.d 1 0) ≫ complexMapSyzygy F χ 0
        = χ.f 0 ≫ F.map (cokernel.π (P.d 1 0)) := h1
      _ = χ.f 0 ≫ F.map πP ≫ F.map (complexAugmentationIso P πP zP eP).inv := by
          rw [hπ, F.map_comp]
      _ = πQ ≫ a ≫ F.map (complexAugmentationIso P πP zP eP).inv := by
          rw [← Category.assoc, ha, Category.assoc]
      _ = _ := by conv_rhs => rw [← Category.assoc, h2]
  rw [hs, Iso.inv_hom_id_assoc]

variable [HasExt.{w} C] [HasExt.{w'} D]

/-- **Augmented Yoneda representatives under an exact functor.** For a chain map `χ` from an
augmented complex into the image of an augmented complex, compatible with the augmentations
through `a`, the augmented class of the pulled back image cochain is `a` followed by the image
of the augmented class. -/
theorem augmentedComplexCocycleComparison_map (a : B ⟶ F.obj A)
    (ha : χ.f 0 ≫ F.map πP = πQ ≫ a) {Y : C} (n : ℕ) (z : (complexTower P hP).cycles Y n) :
    augmentedComplexCocycleComparison Q (F.obj Y) hQ πQ zQ eQ n
        ((complexMapSourceMap F hP hQ χ).cycles (F.obj Y) n (towerMapCycles F n z)) =
      (Ext.mk₀ a).comp ((augmentedComplexCocycleComparison P Y hP πP zP eP n z).mapExactFunctor F)
        (zero_add n) := by
  unfold augmentedComplexCocycleComparison
  rw [ExactTower.SourceMap.cocycleComparison, ← towerMap_cocycleComparison, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc]
  congr 2
  exact complexMapSyzygy_augmentation F χ πP zP eP πQ zQ eQ a ha

end Complex

end BPFixedPoints.Multigraph
