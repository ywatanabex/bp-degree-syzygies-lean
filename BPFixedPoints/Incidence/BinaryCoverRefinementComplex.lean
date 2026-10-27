import BPFixedPoints.Incidence.BinaryCoverRefinementCells
import BPFixedPoints.Incidence.BinaryCoverCellCoverAugmentation

/-! # The forgetful chain map between cubical cell sheaf complexes

Let `C : K → Fin 2 → Opens T` and `U : I → Fin 2 → Opens T` be binary cover
families and `ι : I → K` an injective map with `C (ι i) b ≤ U i b` for all `i`
and `b`. The signed restriction of cells along `ι` (forgetting the directions of
`K` outside the image of `ι`, with the explicit inversion sign of
`BinaryCoverRefinementCells`) carries the cells available on an open for `C`
to cells available on the same open for `U`, because the cell open of `C` is
contained in the cell open of `U` of the restricted cell. It therefore gives
an actual chain map `relabelSheafComplex C U hι hC : sheafComplex C ⟶ sheafComplex U`
of the cell sheaf complexes, obtained from a map of the cell presheaf complexes by
forgetting the integer module structure and sheafifying.

The chain map preserves the original terminal augmentation:
`relabelSheafComplex_augmentation`. No exactness, cover or acyclicity hypothesis
is used. That the products agree along this map is proved in
`BinaryCoverRefinementCup`.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell Function
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable {T : Type} [TopologicalSpace T]
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Each left, right and overlap open is monotone in the two endpoint opens. -/
theorem binaryCoverFaceFactor_mono {A B : Fin 2 → Opens T} (h : ∀ b, A b ≤ B b) (k : Fin 3) :
    binaryCoverFaceFactor A k ≤ binaryCoverFaceFactor B k := by
  unfold binaryCoverFaceFactor
  split_ifs
  · exact h 0
  · exact h 1
  · exact inf_le_inf (h 0) (h 1)

variable (C : K → Fin 2 → Opens T) (U : I → Fin 2 → Opens T) {ι : I → K}
variable (hι : Injective ι) (hC : ∀ i b, C (ι i) b ≤ U i b)

include hC in
/-- The cell open of `C` is contained in the cell open of `U` of the restricted cell. -/
theorem binaryCoverFaceOpen_relabel_le (q : K → Fin 3) :
    binaryCoverFaceOpen C q ≤ binaryCoverFaceOpen U (q ∘ ι) :=
  le_iInf fun i => (iInf_le _ (ι i)).trans (binaryCoverFaceFactor_mono (hC i) (q (ι i)))

include hC in
/-- The signed restriction carries cells available for `C` to cells available for `U`. -/
theorem relabelCells_available (R : Type*) [CommRing R] (W : Opens T) {x : Cells R K}
    (hx : x ∈ available C W R) : relabelCells R ι x ∈ available U W R := by
  unfold available at hx ⊢
  refine map_supported_of_single R (fun q hq => ?_) hx
  rw [relabelCells_single]
  exact single_mem_supported R _ (le_trans hq (binaryCoverFaceOpen_relabel_le C U hC q))

variable (R : Type) [CommRing R]

@[reducible] noncomputable local instance relabelChainsAddCommGroup {V : Type} [Fintype V]
    [DecidableEq V] (D : V → Fin 2 → Opens T) (W : Opens T) (n : ℕ) :
    AddCommGroup (chains D R W n) := (chains D R W n).addCommGroup
@[reducible] noncomputable local instance relabelChainsModule {V : Type} [Fintype V]
    [DecidableEq V] (D : V → Fin 2 → Opens T) (W : Opens T) (n : ℕ) :
    Module R (chains D R W n) := (chains D R W n).module

/-- The signed restriction on the available chains of one degree on one open. -/
noncomputable def relabelChains (W : Opens T) (n : ℕ) : chains C R W n →ₗ[R] chains U R W n :=
  ((relabelCells R ι).comp (chains C R W n).subtype).codRestrict _ fun x =>
    ⟨relabelCells_available C U hC R W x.property.1, relabelCells_degree R ι hι _ x.property.2⟩

/-- The signed restriction retains its value on the underlying cells. -/
theorem relabelChains_val (W : Opens T) (n : ℕ) (x : chains C R W n) :
    (relabelChains C U hι hC R W n x).val = relabelCells R ι x.val := rfl

/-- The signed restriction commutes with the inclusions of available cells. -/
noncomputable def relabelPresheaf (n : ℕ) : presheaf C R n ⟶ presheaf U R n where
  app W := ModuleCat.ofHom (relabelChains C U hι hC R W.unop n)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The signed restriction commutes with the cell presheaf differentials. -/
theorem relabelPresheaf_comm (n : ℕ) :
    relabelPresheaf C U hι hC R (n+1) ≫ presheafDifferential U R n =
      presheafDifferential C R n ≫ relabelPresheaf C U hι hC R n := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (LinearMap.congr_fun (relabelCells_d R ι hι) x.val).symm

/-- The signed restriction as a map of cell presheaf chain complexes. -/
noncomputable def relabelPresheafComplex : presheafComplex C R ⟶ presheafComplex U R :=
  ChainComplex.ofHom (relabelPresheaf C U hι hC R) (fun n => by
    dsimp only [presheafComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    exact relabelPresheaf_comm C U hι hC R n)

/-- The signed restriction is compatible with the two component augmentations. -/
theorem relabelPresheaf_componentAugmentation :
    relabelPresheaf C U hι hC R 0 ≫ componentPresheafAugmentation U R =
      componentPresheafAugmentation C R ≫ (Functor.const (Opens T)ᵒᵖ).map
        (ModuleCat.ofHom (Finsupp.lmapDomain R R (fun f : K → Fin 1 => f ∘ ι))) := by
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (relabelCells_p R ι) x.val

/-- The component map is compatible with the two terminal generator identifications. -/
theorem topComponentPresheafIso_relabel :
    (topComponentPresheafIso (V := K) (T := T)).hom ≫
      (toAbelianPresheaf (T := T)).map ((Functor.const (Opens T)ᵒᵖ).map
        (ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (fun f : K → Fin 1 => f ∘ ι)))) =
      (topComponentPresheafIso (V := I) (T := T)).hom := by
  ext W : 2
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  change Finsupp.lmapDomain ℤ ℤ (fun f : K → Fin 1 => f ∘ ι)
      (topComponentEquiv (V := K) W.unop (FreeAbelianGroup.of i)) =
    topComponentEquiv (V := I) W.unop (FreeAbelianGroup.of i)
  rw [topComponentEquiv_of, topComponentEquiv_of, Finsupp.lmapDomain_apply, mapDomain_single]
  rfl

/-- The forgetful chain map of the actual cubical cell sheaf complexes. -/
noncomputable def relabelSheafComplex : sheafComplex C ⟶ sheafComplex U :=
  ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).mapHomologicalComplex _).map
    (((toAbelianPresheaf (T := T)).mapHomologicalComplex _).map (relabelPresheafComplex C U hι hC ℤ))

/-- Each component of the forgetful chain map is the sheafified signed restriction. -/
theorem relabelSheafComplex_f (n : ℕ) :
    (relabelSheafComplex C U hι hC).f n =
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
        ((toAbelianPresheaf (T := T)).map (relabelPresheaf C U hι hC ℤ n)) := rfl

/-- The forgetful chain map preserves the original terminal augmentation. -/
theorem relabelSheafComplex_augmentation :
    (relabelSheafComplex C U hι hC).f 0 ≫ augmentation U = augmentation C := by
  rw [relabelSheafComplex_f, augmentation, augmentation, ← Functor.map_comp]
  congr 1
  rw [presheafAugmentation, presheafAugmentation, componentAbelianAugmentation,
    componentAbelianAugmentation, ← Category.assoc, ← Functor.map_comp,
    relabelPresheaf_componentAugmentation, Functor.map_comp, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
  exact topComponentPresheafIso_relabel

end BPFixedPoints.SheafTools.BinaryCells
