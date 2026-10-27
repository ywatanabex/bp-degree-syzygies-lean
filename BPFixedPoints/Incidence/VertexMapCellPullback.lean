import BPFixedPoints.Incidence.VertexPermutationCellTransport
import BPFixedPoints.Incidence.VertexMapPullbackCohomology

/-!
# Cubical cell complexes along a continuous map

Let `g : T ⟶ T'` be a continuous map and `U`, `U'` binary covers of `T` and `T'` indexed by the
same finite type, with `g⁻¹ (U' i b) = U i b`. Then `g` pulls back the face open of every face of
`U'` to the face open of the same face of `U` (`faceOpen_pull`).

The inverse image of a section is the component of the unit of the adjunction `g⁻¹ ⊣ g_*`
(`topPullSection`); it commutes with restriction and is natural in the sheaf. No description of the
inverse image of the free sheaves `ℤ_O` is needed: the comparison of the cell complexes,
`cellPullMap g U U' hU : sheafComplex U ⟶ g⁻¹ (sheafComplex U')`, is defined through the universal
property of the cell terms (`sectionsEquiv`), sending the universal section of a face to the
pulled back universal section of the same face.

Proved here:
* `cellPullMap` is a chain map (`cellPullComponent_comm`);
* the face sections of `cellPullMap` followed by the inverse image of a cochain are the pulled
  back face sections of the cochain (`sectionsEquiv_cellPullComponent_comp`);
* it is compatible with the augmentations through the comparison `pullFreeTop` of the free sheaves
  on the whole spaces (`cellPullComponent_augmentation`);
* the identification of the inverse image of the constant sheaf with the constant sheaf
  (`topSheafPullbackConstant`, defined by uniqueness of adjoints) keeps the section `1`
  (`topSheafPullbackConstant_unit`, `freeSheafTopIso_pullFreeTop`);
* **class transport**: the pullback of Ext-defined cohomology `sheafHPullback` sends the class of
  a cubical cocycle of `U'` to the class of the cocycle of `U` obtained by pulling back its inverse
  image along `cellPullMap` (`cellPull_class`), in every degree.

Nothing here involves schemes, twists or states.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open SheafTools SheafTools.BinaryCells ExtResolutionTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

noncomputable local instance cellPullbackHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

section Sections

variable {T T' : TopCat.{0}} (g : T ⟶ T')

/-- The section of the inverse image determined by a section: the component of the unit of the
adjunction `g⁻¹ ⊣ g_*`. -/
noncomputable def topPullSection (F : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0})
    (O : Opens T') :
    F.obj.obj (op O) →+ ((topSheafPullback g).obj F).obj.obj (op ((Opens.map g).obj O)) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.app F).hom.app
    (op O)).hom

/-- Pulled back sections commute with restriction. -/
theorem topPullSection_restrict (F : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0})
    {O O' : Opens T'} (h : O' ≤ O) (x : F.obj.obj (op O)) :
    topPullSection g F O' (F.obj.map (homOfLE h).op x) =
      ((topSheafPullback g).obj F).obj.map (homOfLE ((Opens.map g).monotone h)).op
        (topPullSection g F O x) :=
  ConcreteCategory.congr_hom
    (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.app F).hom.naturality
      (homOfLE h).op) x

/-- Pulled back sections are natural in the sheaf. -/
theorem topPullSection_naturality {F G : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0}}
    (u : F ⟶ G) (O : Opens T') (x : F.obj.obj (op O)) :
    ((topSheafPullback g).map u).hom.app _ (topPullSection g F O x) =
      topPullSection g G O (u.hom.app _ x) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g).unit.naturality u
  exact (ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app (op O)) h) x).symm

end Sections

section Opens

variable {T T' : TopCat.{0}} (g : T ⟶ T') {I : Type} [Fintype I] (U : I → Fin 2 → Opens T)
  (U' : I → Fin 2 → Opens T') (hU : ∀ i b, (Opens.map g).obj (U' i b) = U i b)

include hU in
/-- The continuous map pulls back the face opens of `U'` to the face opens of `U`. -/
theorem faceOpen_pull (q : I → Fin 3) :
    (Opens.map g).obj (binaryCoverFaceOpen U' q) = binaryCoverFaceOpen U q := by
  have hf : ∀ i, (Opens.map g).obj (binaryCoverFaceFactor (U' i) (q i)) =
      binaryCoverFaceFactor (U i) (q i) := by
    intro i
    unfold binaryCoverFaceFactor
    split_ifs
    · exact hU i 0
    · exact hU i 1
    · rw [← hU i 0, ← hU i 1]
      rfl
  ext x
  simp only [binaryCoverFaceOpen, Opens.map_coe, Opens.coe_iInf, Set.mem_preimage, Set.mem_iInter,
    SetLike.mem_coe]
  constructor
  · intro hx i
    have := congrArg (fun O : Opens T => x ∈ O) (hf i)
    simp only [eq_iff_iff] at this
    exact this.mp (hx i)
  · intro hx i
    have := congrArg (fun O : Opens T => x ∈ O) (hf i)
    simp only [eq_iff_iff] at this
    exact this.mpr (hx i)

end Opens

section Chain

variable {T T' : TopCat.{0}} (g : T ⟶ T') {I : Type} [Fintype I] [DecidableEq I]
  (U : I → Fin 2 → Opens T) (U' : I → Fin 2 → Opens T')
  (hU : ∀ i b, (Opens.map g).obj (U' i b) = U i b)

/-- The section defining the comparison of cell complexes on the face open of a face: the pulled
back universal section of the same face of `U'`. -/
noncomputable def cellPullSection (n : ℕ) (q : FaceIndex (V := I) n) :
    ((topSheafPullback g).obj (sheafTerm U' n)).obj.obj (op (binaryCoverFaceOpen U q.val)) :=
  ((topSheafPullback g).obj (sheafTerm U' n)).obj.map
    (homOfLE (faceOpen_pull g U U' hU q.val).ge).op
    (topPullSection g (sheafTerm U' n) _ (cellGeneratorSection U' n q))

/-- **The comparison of cubical cell complexes along a continuous map** in each degree: the cell
sheaf term of `U` maps to the inverse image of the cell sheaf term of `U'` by sending the universal
section of a face to the pulled back universal section of the same face. -/
noncomputable def cellPullComponent (n : ℕ) :
    sheafTerm U n ⟶ (topSheafPullback g).obj (sheafTerm U' n) :=
  (sectionsEquiv U ((topSheafPullback g).obj (sheafTerm U' n)) n).symm (cellPullSection g U U' hU n)

/-- The face sections of the comparison are the pulled back universal sections. -/
theorem sectionsEquiv_cellPullComponent (n : ℕ) :
    sectionsEquiv U ((topSheafPullback g).obj (sheafTerm U' n)) n (cellPullComponent g U U' hU n) =
      cellPullSection g U U' hU n :=
  AddEquiv.apply_symm_apply _ _

/-- **Face sections of a pulled back cochain.** The face sections of the comparison followed by
the inverse image of a cochain are the pulled back face sections of the cochain. -/
theorem sectionsEquiv_cellPullComponent_comp (n : ℕ)
    {G : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0}} (f : sheafTerm U' n ⟶ G)
    (q : FaceIndex (V := I) n) :
    sectionsEquiv U ((topSheafPullback g).obj G) n
        (cellPullComponent g U U' hU n ≫ (topSheafPullback g).map f) q =
      ((topSheafPullback g).obj G).obj.map (homOfLE (faceOpen_pull g U U' hU q.val).ge).op
        (topPullSection g G _ (sectionsEquiv U' G n f q)) := by
  rw [sectionsEquiv_comp, sectionsEquiv_cellPullComponent]
  change ((topSheafPullback g).map f).hom.app _ (((topSheafPullback g).obj (sheafTerm U' n)).obj.map _
    (topPullSection g (sheafTerm U' n) _ (cellGeneratorSection U' n q))) = _
  rw [← ConcreteCategory.comp_apply, ((topSheafPullback g).map f).hom.naturality,
    ConcreteCategory.comp_apply, topPullSection_naturality, sectionsEquiv_eq_app]

/-- **The comparison of cell complexes along a continuous map is a chain map.** -/
theorem cellPullComponent_comm (n : ℕ) :
    cellPullComponent g U U' hU (n+1) ≫ (topSheafPullback g).map ((sheafComplex U').d (n+1) n) =
      (sheafComplex U).d (n+1) n ≫ cellPullComponent g U U' hU n := by
  apply (sectionsEquiv U ((topSheafPullback g).obj (sheafTerm U' n)) (n+1)).injective
  funext p
  rw [sectionsEquiv_cellPullComponent_comp, sectionsEquiv_boundary, sectionsEquiv_cellPullComponent]
  have hb := sectionsEquiv_boundary U' (sheafTerm U' n) n (𝟙 _) p
  rw [Category.comp_id] at hb
  rw [hb, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : p.val v = 2
  · rw [dite_eq_left hv, dite_eq_left hv, map_zsmul, map_zsmul, map_sub, map_sub,
      topPullSection_restrict, topPullSection_restrict]
    congr 2
    · rw [sheaf_map_map _ _ _ (homOfLE ((faceOpen_pull g U U' hU p.val).ge.trans
        ((Opens.map g).monotone (endpointOpenLE U' p v hv 0)))).op]
      change _ = ((topSheafPullback g).obj (sheafTerm U' n)).obj.map _
        (((topSheafPullback g).obj (sheafTerm U' n)).obj.map _ _)
      rw [sheaf_map_map]
      rfl
    · rw [sheaf_map_map _ _ _ (homOfLE ((faceOpen_pull g U U' hU p.val).ge.trans
        ((Opens.map g).monotone (endpointOpenLE U' p v hv 1)))).op]
      change _ = ((topSheafPullback g).obj (sheafTerm U' n)).obj.map _
        (((topSheafPullback g).obj (sheafTerm U' n)).obj.map _ _)
      rw [sheaf_map_map]
      rfl
  · rw [dite_eq_right hv, dite_eq_right hv, map_zero, map_zero]

/-- **The comparison chain map** from the cubical cell complex of `U` to the inverse image of the
cubical cell complex of `U'`. -/
noncomputable def cellPullMap :
    sheafComplex U ⟶ ((topSheafPullback g).mapHomologicalComplex _).obj (sheafComplex U') where
  f n := cellPullComponent g U U' hU n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    exact cellPullComponent_comm g U U' hU j

/-- The components of the comparison chain map. -/
theorem cellPullMap_f (n : ℕ) : (cellPullMap g U U' hU).f n = cellPullComponent g U U' hU n :=
  rfl

end Chain

section Constant

variable {T T' : TopCat.{0}} (g : T ⟶ T')

/-- **The sign of the constant-sheaf identification along a continuous map.** The identification
of the inverse image of the constant sheaf with the constant sheaf sends the pulled back global
section given by the adjunction unit at `a` to the global section given by the adjunction unit at
`a`. -/
theorem topSheafPullbackConstant_unit (A : AddCommGrpCat.{0}) (a : A) :
    ((topSheafPullbackConstant g).hom.app A).hom.app (op ⊤)
        (topPullSection g _ ⊤ (((constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
          (isTerminalTop (α := Opens T'))).unit.app A).hom a)) =
      ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
          (isTerminalTop (α := Opens T))).unit.app A).hom a := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T'))).comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} g)).ofNatIsoRight
          (topSheafPushforwardSections g))
    (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{0}
      (isTerminalTop (α := Opens T))) A
  have k2 := congrArg (fun f => f.hom a) key
  refine Eq.trans ?_ k2
  rfl

open SheafTools in
/-- The comparison of the free sheaves on the whole spaces: the universal section of the free sheaf
on `T` goes to the pulled back universal section of the free sheaf on `T'`. -/
noncomputable def pullFreeTop :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶
      (topSheafPullback g).obj ((presheafToSheaf (Opens.grothendieckTopology T')
        AddCommGrpCat).obj (yoneda.obj (⊤ : Opens T') ⋙ AddCommGrpCat.free)) :=
  (freeSheafSectionsEquiv _ ⊤).symm
    (topPullSection g _ ⊤ (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _)))

/-- The universal section of `pullFreeTop`. -/
theorem freeSheafSectionsEquiv_pullFreeTop :
    freeSheafSectionsEquiv _ ⊤ (pullFreeTop g) =
      topPullSection g _ ⊤ (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _)) :=
  AddEquiv.apply_symm_apply _ _

/-- **The constant-sheaf identification keeps the section `1`.** Under the identification of the
inverse image of the constant sheaf with the constant sheaf, the comparison of the free sheaves on
the whole spaces corresponds to the canonical comparisons with the constant sheaves. -/
theorem freeSheafTopIso_pullFreeTop :
    (freeSheafTopIso (T := T)).inv ≫ pullFreeTop g =
      ((topSheafPullbackConstant g).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (topSheafPullback g).map (freeSheafTopIso (T := T')).inv := by
  have hhom : (freeSheafTopIso (T := T)).hom = pullFreeTop g ≫
      (topSheafPullback g).map (freeSheafTopIso (T := T')).hom ≫
        ((topSheafPullbackConstant g).app (AddCommGrpCat.of (ULift ℤ))).hom := by
    apply (freeSheafSectionsEquiv _ (⊤ : Opens T)).injective
    have h1 := freeSheafTopIso_inv_sections (T := T)
      ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ))) (freeSheafTopIso (T := T)).hom
    rw [Iso.inv_hom_id] at h1
    rw [← h1, constantIntegerCorepresentsSections_id]
    have h0 := freeSheafTopIso_inv_sections (T := T')
      ((constantSheaf (Opens.grothendieckTopology T') AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ))) (freeSheafTopIso (T := T')).hom
    rw [Iso.inv_hom_id, constantIntegerCorepresentsSections_id] at h0
    have h2 : (freeSheafTopIso (T := T')).hom.hom.app (op ⊤)
        (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _)) =
          ((constantSheafAdj (Opens.grothendieckTopology T') AddCommGrpCat.{0}
            (isTerminalTop (α := Opens T'))).unit.app (AddCommGrpCat.of (ULift ℤ))).hom
              (ULift.up 1) := by
      rw [h0, ← Category.id_comp (freeSheafTopIso (T := T')).hom, freeSheafSectionsEquiv_comp]
      rfl
    rw [freeSheafSectionsEquiv_comp, freeSheafSectionsEquiv_pullFreeTop]
    change _ = ((topSheafPullbackConstant g).app (AddCommGrpCat.of (ULift ℤ))).hom.hom.app (op ⊤)
      (((topSheafPullback g).map (freeSheafTopIso (T := T')).hom).hom.app
        (op ((Opens.map g).obj ⊤))
        (topPullSection g _ ⊤ (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _))))
    rw [topPullSection_naturality, h2]
    exact (topSheafPullbackConstant_unit g _ _).symm
  rw [Iso.inv_comp_eq, hhom, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end Constant

section Transport

noncomputable local instance cellPullbackTopHasExt (S : TopCat.{0}) :
    HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} S) := HasExt.standard _

variable {T T' : TopCat.{0}} (g : T ⟶ T') {I : Type} [Fintype I] [DecidableEq I]
  (U : I → Fin 2 → Opens T) (U' : I → Fin 2 → Opens T')
  (hU : ∀ i b, (Opens.map g).obj (U' i b) = U i b)

/-- The comparison chain map is compatible with the augmentations, through the comparison of the
free sheaves on the whole spaces. -/
theorem cellPullComponent_augmentation :
    cellPullComponent g U U' hU 0 ≫ (topSheafPullback g).map (augmentation U') =
      augmentation U ≫ pullFreeTop g := by
  apply (sectionsEquiv U ((topSheafPullback g).obj ((presheafToSheaf
    (Opens.grothendieckTopology T') AddCommGrpCat).obj (yoneda.obj (⊤ : Opens T') ⋙
      AddCommGrpCat.free))) 0).injective
  funext q
  rw [sectionsEquiv_cellPullComponent_comp, sectionsEquiv_comp, sectionsEquiv_augmentation,
    sectionsEquiv_augmentation, topPullSection_restrict]
  have hn := ConcreteCategory.congr_hom ((pullFreeTop g).hom.naturality
    (homOfLE (show binaryCoverFaceOpen U q.val ≤ ⊤ from le_top)).op)
    (freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _))
  have ha : (pullFreeTop g).hom.app (op ⊤) (freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _)) =
      topPullSection g _ ⊤ (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _)) := by
    rw [← freeSheafSectionsEquiv_comp, Category.id_comp]
    exact freeSheafSectionsEquiv_pullFreeTop g
  refine Eq.trans ?_ hn.symm
  change _ = ((topSheafPullback g).obj _).obj.map _ ((pullFreeTop g).hom.app (op ⊤)
    (freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _)))
  rw [ha, sheaf_map_map]
  rfl

/-- **Transport of the cubical-cell Yoneda classes along a continuous map.** The pullback of
Ext-defined cohomology `sheafHPullback` sends the class of a cubical cocycle of `U'` to the class
of the cocycle of `U` obtained by pulling back its inverse image along the comparison chain map. -/
theorem cellPull_class (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (hcover' : (⊤ : Opens T') ≤ ⨆ b, chartOpen U' b)
    (F : Sheaf (Opens.grothendieckTopology T') AddCommGrpCat.{0}) (n : ℕ)
    (z : (cubicalTower U').cycles F n) :
    letI := augmentation_epi U hcover
    letI := augmentation_epi U' hcover'
    sheafHPullback g F n (localSheafTopEquiv F n (augmentedComplexCocycleComparison
        (sheafComplex U') F (sheafComplex_exact U') (augmentation U') (augmentation_zero U')
        (augmentation_exact U') n z)) =
      localSheafTopEquiv ((topSheafPullback g).obj F) n
        (augmentedComplexCocycleComparison (sheafComplex U) ((topSheafPullback g).obj F)
          (sheafComplex_exact U) (augmentation U) (augmentation_zero U) (augmentation_exact U) n
          ((complexMapSourceMap (topSheafPullback g) (sheafComplex_exact U')
            (sheafComplex_exact U) (cellPullMap g U U' hU)).cycles _ n
              (towerMapCycles (topSheafPullback g) n z))) := by
  let _ := augmentation_epi U hcover
  let _ := augmentation_epi U' hcover'
  rw [sheafHPullback_apply, augmentedComplexCocycleComparison_map (topSheafPullback g)
    (sheafComplex_exact U') (sheafComplex_exact U) (cellPullMap g U U' hU) (augmentation U')
    (augmentation_zero U') (augmentation_exact U') (augmentation U) (augmentation_zero U)
    (augmentation_exact U) (pullFreeTop g) (cellPullComponent_augmentation g U U' hU) n z,
    localSheafTopEquiv_apply, localSheafTopEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    freeSheafTopIso_pullFreeTop]

end Transport

end BPFixedPoints.Multigraph
