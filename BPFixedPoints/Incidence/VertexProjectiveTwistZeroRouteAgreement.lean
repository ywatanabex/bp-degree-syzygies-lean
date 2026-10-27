import BPFixedPoints.Incidence.VertexProjectiveTwistStateProduct
import BPFixedPoints.Incidence.VertexProjectiveTwistStateCohomology

/-! # The restriction route and the cell route give the same state coordinates

Two independently built comparisons send actual cohomology of a nonpositive
vertex twist to its original state degree piece. In degree zero the public
comparison evaluates the actual global section on the original charts; the
cell route uses the original augmentation-only cell comparison and the
original signed cell coefficients. A degree-zero cell cocycle factors through
the original terminal augmentation, its global section restricts on each
original chart to its value on the original chart generator, and both routes
then apply the same original contraction projection. In positive degrees the
two comparisons coincide by definition. Nothing is transported from states.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite Finsupp
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- Every original face of overlap degree zero is an original binary vertex. -/
theorem faceIndex_zero_vertexCell (q : FaceIndex (V := V) 0) :
    ∃ b : V → Fin 2, q.val = (vertexCell b).val := by
  have hq : CechProduct.faceDegree q.val = 0 := by
    have h := q.property
    dsimp only [CechCubicalCell.cellDegree] at h
    omega
  obtain ⟨σ,hσ⟩ := (CechProduct.faceDegree_eq_zero_iff q.val).mp hq
  refine ⟨fun v => if σ v then 1 else 0,?_⟩
  rw [hσ]
  funext v
  change CechProduct.chartFace σ v = ((if σ v then 1 else 0 : Fin 2)).castSucc
  unfold CechProduct.chartFace
  cases σ v <;> rfl

/-- Before sheafification, the original terminal augmentation sends each original vertex generator
to the original inclusion of its chart in the whole space. -/
theorem presheafGenerator_presheafAugmentation (q : FaceIndex (V := V) 0) :
    presheafGenerator U q ≫ presheafAugmentation U =
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
        (yoneda.map (homOfLE (show binaryCoverFaceOpen U q.val ≤ ⊤ from le_top))) := by
  obtain ⟨b,hb⟩ := faceIndex_zero_vertexCell q
  rw [presheafAugmentation,← Category.assoc,Iso.comp_inv_eq]
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  change (CechCubicalCell.contraction ℤ (fun _ : V => 0)).p
      ((presheafGenerator U q).app W (FreeAbelianGroup.of i)).val =
    topComponentEquiv (V := V) W.unop (FreeAbelianGroup.map _ (FreeAbelianGroup.of i))
  rw [presheafGenerator_app_of_val,FreeAbelianGroup.map_of_apply,topComponentEquiv_of,hb]
  exact component_projection_vertex b 1

/-- The original terminal augmentation sends each original vertex generator to the original
inclusion of its chart in the whole space. -/
theorem generator_augmentation (q : FaceIndex (V := V) 0) :
    generator U q ≫ augmentation U =
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (yoneda.map (homOfLE (show binaryCoverFaceOpen U q.val ≤ ⊤ from le_top)))) := by
  rw [generator,augmentation,← Functor.map_comp,presheafGenerator_presheafAugmentation]

local instance zeroRouteHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The global section of the augmentation-only degree-zero class is the original section
of the factorization of the cocycle through the original terminal augmentation. -/
theorem finiteCubicalActualZeroEquiv_sections
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) (z : (cubicalTower U).cycles F 0) :
    letI := augmentation_epi U hcover
    localSheafH0Equiv F ⊤ ((localSheafTopEquiv F 0).symm
        (finiteCubicalActualZeroEquiv U F hcover ((cubicalTower U).classAt F 0 z))) =
      freeSheafSectionsEquiv F ⊤
        ((complexAugmentationIso _ (augmentation U) (augmentation_zero U) (augmentation_exact U)).inv ≫
          (cubicalTower U).cycleEquiv F 0 z) := by
  have := augmentation_epi U hcover
  let e := complexAugmentationIso _ (augmentation U) (augmentation_zero U) (augmentation_exact U)
  let c := (cubicalTower U).cycleEquiv F 0 z
  change localSheafH0Equiv F ⊤ ((localSheafTopEquiv F 0).symm (localSheafTopEquiv F 0
    ((Ext.mk₀ e.inv).comp (Ext.mk₀ c) (zero_add 0)))) = _
  rw [AddEquiv.symm_apply_apply,Ext.mk₀_comp_mk₀]
  change freeSheafSectionsEquiv F ⊤ (Ext.addEquiv₀ (Ext.mk₀ (e.inv ≫ c))) = _
  rw [show Ext.addEquiv₀ (Ext.mk₀ (e.inv ≫ c)) = e.inv ≫ c from Ext.addEquiv₀.apply_symm_apply _]

/-- On each original vertex chart, the global section of the augmentation-only degree-zero
class restricts to the value of the cocycle on the original vertex generator. -/
theorem finiteCubicalActualZeroEquiv_restrict
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) (z : (cubicalTower U).cycles F 0)
    (q : FaceIndex (V := V) 0) :
    F.obj.map (homOfLE (show binaryCoverFaceOpen U q.val ≤ ⊤ from le_top)).op
      (localSheafH0Equiv F ⊤ ((localSheafTopEquiv F 0).symm
        (finiteCubicalActualZeroEquiv U F hcover ((cubicalTower U).classAt F 0 z)))) =
          sectionsEquiv U F 0 z.val q := by
  have := augmentation_epi U hcover
  let e := complexAugmentationIso _ (augmentation U) (augmentation_zero U) (augmentation_exact U)
  let c := (cubicalTower U).cycleEquiv F 0 z
  have hz : augmentation U ≫ e.inv ≫ c = z.val := by
    rw [← complexAugmentationIso_projection (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U),Category.assoc,Iso.hom_inv_id_assoc]
    exact (cubicalTower U).cycleEquiv_projection F 0 z
  rw [finiteCubicalActualZeroEquiv_sections,← freeSheafSectionsEquiv_naturality,sectionsEquiv_apply]
  congr 1
  rw [← hz,← Category.assoc (generator U q),generator_augmentation]

end BPFixedPoints.SheafTools.BinaryCells

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct Finsupp
open SheafTools SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexZeroRouteHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- On each original chart, the actual global section of a degree-zero cell class has the
original frame coordinate of the cocycle on the original chart generator. -/
theorem vertexTwistH0Sections_cellActualZero_chart (d : V → ℕ) (z : vertexTwistCellCycles R V d 0)
    (σ : V → Bool) :
    letI := vertexTwistH0BaseModule R V d
    letI := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) 0
    vertexTwistGlobalChartCoordinates R V _ (vertexTwistH0SectionsLinearEquiv R V d
        (vertexTwistCellActualZeroLinearEquiv R V _
          ((cubicalTower (vertexCoordinateOpen R V)).classAt _ 0 z))) σ =
      vertexTwistSheafFaceSectionsEquiv R V _ (chartFace σ)
        (sectionsEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) 0
          z.val (faceIndexOfDegree V 0 (chartFace σ) (by simp))) := by
  rw [vertexTwistGlobalChartCoordinates_apply]
  exact congrArg (vertexTwistSheafFaceSectionsEquiv R V _ (chartFace σ))
    (finiteCubicalActualZeroEquiv_restrict (vertexCoordinateOpen R V)
      (vertexTwistAbelianSheaf R V _) (vertexCellChartOpen_cover R V) z
      (faceIndexOfDegree V 0 (chartFace σ) (by simp)))

/-- The original chart restriction chain of the actual global section of a degree-zero cell class
is exactly the original signed cell coefficient of the cocycle. -/
theorem vertexTwistGlobalZeroChain_cellActualZero (d : V → ℕ) (z : vertexTwistCellCycles R V d 0) :
    letI := vertexTwistH0BaseModule R V d
    letI := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) 0
    vertexTwistGlobalZeroChain R V _ (vertexTwistH0SectionsLinearEquiv R V d
        (vertexTwistCellActualZeroLinearEquiv R V _
          ((cubicalTower (vertexCoordinateOpen R V)).classAt _ 0 z))) =
      (vertexTwistCellCoefficientEquiv R V d 0 z.val).val := by
  have hs : (vertexTwistCellCoefficientEquiv R V d 0 z.val).val ∈
      supported R R {b : V → CechProduct.Basis | (cechDegree b : ℤ) = 0} := by
    simpa only [Nat.cast_zero] using (vertexTwistCellCoefficientEquiv R V d 0 z.val).property
  rw [← zeroCharts_reconstruct R _ hs]
  change zeroCharts R (vertexTwistGlobalChartCoordinates R V _ _) = _
  congr 1
  funext σ
  rw [vertexTwistH0Sections_cellActualZero_chart]
  change _ = faceEquiv R (vertexTwistCubicalChainEquiv R V d
    (vertexTwistCellNativeEquiv R V _ 0 z.val).val) (chartFace σ)
  have hp : (-1 : R) ^ faceDegree (chartFace σ) = 1 := by
    rw [faceDegree_chartFace,pow_zero]
  rw [vertexTwistCubicalChainEquiv_face,hp,one_smul]
  exact congrArg (vertexTwistSheafFaceSectionsEquiv R V _ (chartFace σ))
    (vertexTwistCellNativeEquiv_apply R V _ 0 z.val
      (faceIndexOfDegree V 0 (chartFace σ) (by simp))).symm

variable [IsNoetherianRing R]

/-- In degree zero, the public restriction-route state comparison agrees with the cell route. -/
theorem vertexTwistStateLinearEquiv_zero_cell (d : V → ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) 0) :
    letI := vertexTwistStateCohomologyModule R V d 0
    (vertexTwistStateLinearEquiv R V d 0 x).val = (vertexTwistActualStateAt R V d 0 x).val := by
  let := vertexTwistStateCohomologyModule R V d 0
  let := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) 0
  obtain ⟨z,rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) 0).surjective x
  obtain ⟨z,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ 0 z
  rw [vertexTwistActualStateAt_actual,vertexTwistCellStateAt_class,vertexTwistCellCycleProjection_val,
    ← vertexTwistGlobalZeroChain_cellActualZero]
  rfl

/-- In every positive degree, the public state comparison agrees with the cell route. -/
theorem vertexTwistStateLinearEquiv_succ_cell (d : V → ℕ) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) (n+1)) :
    letI := vertexTwistStateCohomologyModule R V d (n+1)
    (vertexTwistStateLinearEquiv R V d (n+1) x).val = (vertexTwistActualStateAt R V d (n+1) x).val := by
  rfl

/-- In every degree, the public state comparison is the cell-route state coordinate. -/
theorem vertexTwistStateLinearEquiv_eq_actualStateAt (d : V → ℕ) (j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) j) :
    letI := vertexTwistStateCohomologyModule R V d j
    vertexTwistStateLinearEquiv R V d j x = vertexTwistActualStateAt R V d j x := by
  cases j with
  | zero => exact Subtype.ext (vertexTwistStateLinearEquiv_zero_cell R V d x)
  | succ n => exact Subtype.ext (vertexTwistStateLinearEquiv_succ_cell R V d n x)

/-- As additive maps, the public state comparison is the cell-route state coordinate in every degree. -/
theorem vertexTwistStateLinearEquiv_toAddMonoidHom (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d j
    (vertexTwistStateLinearEquiv R V d j).toAddEquiv.toAddMonoidHom = vertexTwistActualStateAt R V d j := by
  let := vertexTwistStateCohomologyModule R V d j
  exact AddMonoidHom.ext fun x => vertexTwistStateLinearEquiv_eq_actualStateAt R V d j x

/-- In every degree, the public inverse state comparison sends a state to the actual class of
its original cell representative given by the original contraction inclusion. -/
theorem vertexTwistStateLinearEquiv_symm_cell (d : V → ℕ) (j : ℕ) (s : stateDegreePiece R d j) :
    letI := vertexTwistStateCohomologyModule R V d j
    letI := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) j
    (vertexTwistStateLinearEquiv R V d j).symm s =
      vertexTwistCellActualAtLinearEquiv R V _ j
        ((cubicalTower (vertexCoordinateOpen R V)).classAt _ j (vertexTwistCellStateInclusion R V d j s)) := by
  let := vertexTwistStateCohomologyModule R V d j
  let := vertexTwistCellAtModule R V (fun v => -(d v : ℤ)) j
  apply (vertexTwistStateLinearEquiv R V d j).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistStateLinearEquiv_eq_actualStateAt,
    vertexTwistActualStateAt_actual,vertexTwistCellStateAt_class,vertexTwistCellCycleProjection_inclusion]

end
end BPFixedPoints.ProjectiveLine
