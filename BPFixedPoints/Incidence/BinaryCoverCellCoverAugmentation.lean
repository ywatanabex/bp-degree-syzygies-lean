import BPFixedPoints.Incidence.BinaryCoverCellAugmentedSheaf
import BPFixedPoints.Incidence.FreeAbelianCechAugmentation

/-! # The original binary chart cover makes the original cell augmentation epic

The degree-zero tuple cover generators map to the same original cubical
vertices. Their original augmentations agree. The existing sheaf-gluing
proof for the tuple cover therefore supplies the actual cell augmentation
epimorphism, without asserting an objectwise presheaf epimorphism.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell CechProduct
open AlgebraicTopology
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The original binary vertex, in its original overlap degree zero. -/
def vertexCell (b : V → Fin 2) : FaceIndex (V := V) 0 :=
  ⟨fun v => (b v).castSucc,by simp [cellDegree,faceDegree,endpoint_ne_overlap]⟩

/-- The original binary chart is exactly the actual open of its original vertex cell. -/
abbrev chartOpen (b : V → Fin 2) : Opens T := binaryCoverFaceOpen U (vertexCell b).val

/-- The original component projection sends every original binary vertex to the original coefficient-one component. -/
theorem component_projection_vertex (b : V → Fin 2) (r : ℤ) :
    (CechCubicalCell.contraction ℤ (fun _ : V => 0)).p (single (vertexCell b).val r) =
      single (fun _ => 0) r := by
  rw [contraction_p_eq ℤ (fun _ : V => 0) b]
  change (CechCubicalCell.contraction ℤ b).p (single (fun v => (b v).castSucc) r) = _
  rw [← contraction_i_single ℤ b (fun _ => 0) r]
  exact LinearMap.congr_fun (CechCubicalCell.contraction ℤ b).p_i _

/-- An original singleton cover tuple selects the same original available cubical vertex. -/
def zeroTupleToCells : (FreeCech.tuplePresheaf (FreeCech.coverVertices (chartOpen U))).obj (op ⦋0⦌) ⟶
    cellIndices U 0 where
  app W := ↾fun t => ⟨(vertexCell (t 0).val).val,(t 0).property,(vertexCell (t 0).val).property⟩
  naturality := by intros; rfl

/-- The original singleton tuple generators map to the same original cubical vertex generators. -/
noncomputable def zeroTuplePresheafMap :
    ((FreeCech.tuplePresheaf (FreeCech.coverVertices (chartOpen U))).obj (op ⦋0⦌) ⋙
      AddCommGrpCat.free) ⟶ presheafTerm U 0 :=
  ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (zeroTupleToCells U) ≫
    (freeCellPresheafIso U 0).hom

/-- On original generators, both original degree-zero augmentations give the same original component. -/
theorem zeroTuplePresheafMap_component :
    zeroTuplePresheafMap U ≫ componentAbelianAugmentation U =
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
        (FreeCech.tupleToTop (chartOpen U) 0) ≫
          (topComponentPresheafIso (V := V) (T := T)).hom := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro t
  change (CechCubicalCell.contraction ℤ (fun _ : V => 0)).p
    (chainFreeEquiv U W.unop 0 (FreeAbelianGroup.map ((zeroTupleToCells U).app W)
      (FreeAbelianGroup.of t))).val =
    topComponentEquiv (V := V) W.unop
      (FreeAbelianGroup.map _ (FreeAbelianGroup.of t))
  rw [FreeAbelianGroup.map_of_apply,chainFreeEquiv_of_val,
    FreeAbelianGroup.map_of_apply,topComponentEquiv_of]
  exact component_projection_vertex (t 0).val 1

/-- The actual original tuple-to-cell map in degree zero. -/
noncomputable def zeroTupleMap : FreeCech.freeTerm (chartOpen U) 0 ⟶ sheafTerm U 0 :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map (zeroTuplePresheafMap U)

/-- The specified original tuple-to-cell map commutes with the specified original terminal augmentations. -/
theorem zeroTupleMap_augmentation : zeroTupleMap U ≫ augmentation U =
    FreeCech.augmentationAt (chartOpen U) 0 := by
  rw [zeroTupleMap,augmentation,← Functor.map_comp,presheafAugmentation,
    ← Category.assoc,zeroTuplePresheafMap_component,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rfl

/-- The genuine chart cover, and the existing genuine sheaf gluing proof, make the original cell augmentation epic. -/
theorem augmentation_epi (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) : Epi (augmentation U) := by
  letI := FreeCech.augmentation_epi (chartOpen U) hcover
  exact epi_of_epi_fac (zeroTupleMap_augmentation U)

end BPFixedPoints.SheafTools.BinaryCells
