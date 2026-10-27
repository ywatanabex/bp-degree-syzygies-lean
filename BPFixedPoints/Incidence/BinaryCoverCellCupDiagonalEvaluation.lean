import BPFixedPoints.Incidence.BinaryCoverCellCupFaceFormula

/-! # Evaluate the actual diagonal cup as a sum on original face pairs -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance diagonalEvaluationSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
/-- The original available pair labels form a finite set, including on empty opens. -/
instance pairCellIndexFintype (W : Opens T) (n : ℕ) : Fintype (PairCellIndex U W n) := by
  unfold PairCellIndex
  exact Fintype.ofFinite _

/-- Additive evaluation of original supported pairs is the sum of their unchanged integer coefficients. -/
theorem pairedChains_evaluate {M : Type*} [AddCommGroup M] (W : Opens T) (n : ℕ)
    (φ : pairedChains U ℤ W n →+ M) (x : pairedChains U ℤ W n) :
    φ x = ∑ z : PairCellIndex U W n, x.val z.val •
      φ (pairGenerator U ℤ W n z.val.1 z.val.2 z.property.1 z.property.2.1 z.property.2.2 1) := by
  classical
  let e := pairCellCoordinates U ℤ W n
  have hx : x = ∑ z : PairCellIndex U W n,
      pairGenerator U ℤ W n z.val.1 z.val.2 z.property.1 z.property.2.1 z.property.2.2 (e x z) := by
    calc
      x = e.symm (e x) := (e.symm_apply_apply x).symm
      _ = e.symm (∑ z, single z (e x z)) := congrArg e.symm (Finsupp.univ_sum_single (e x)).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro z _
        exact pairCellCoordinates_generator U ℤ W n z (e x z)
  conv_lhs => rw [hx,map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [pairGenerator_smul]
  exact map_zsmul φ (x.val z.val) _

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- The original actual cup returns to exactly the original pair diagonal before evaluation. -/
theorem actualCellCupAt_pair (b : SectionPairing F G H) (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b n i j f g = (sheafDiagonalMap U).f n ≫ actualPairCochain U b n i j f g := by
  have e := HomologicalComplex.congr_hom (actualTensorDiagonal_toPair U) n
  change (actualTensorDiagonalMap U).f n ≫ (actualTensorPairComplexIso U).hom.f n = _ at e
  rw [← e,actualPairCochain,Category.assoc,← Category.assoc ((actualTensorPairComplexIso U).hom.f n)]
  have hi : (actualTensorPairComplexIso U).hom.f n ≫ (actualTensorPairComplexIso U).inv.f n = 𝟙 _ :=
    HomologicalComplex.congr_hom (actualTensorPairComplexIso U).hom_inv_id n
  rw [hi,Category.id_comp]
  rfl

/-- The original sheaf diagonal sends the original unit representatives to the same supported pair chain. -/
theorem sheafDiagonal_cellSheafSection (W : Opens T) (n : ℕ) (p : V → Fin 3)
    (hp : W ≤ binaryCoverFaceOpen U p) (hd : faceDegree p=n) :
    ((sheafDiagonalMap U).f n).hom.app (op W) (cellSheafSection U W n p hp hd 1) =
      ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
        (toAbelianPresheaf.obj (pairedPresheaf U ℤ n))).app (op W)
          (openDiagonal U ℤ W n (cellGenerator U ℤ W n p hp hd 1)) := by
  have hn := (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.naturality
    ((toAbelianPresheaf (T := T)).map (presheafDiagonal U ℤ n))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hn (op W))
    (cellGenerator U ℤ W n p hp hd 1)).symm

/-- Every actual cup representative has exactly the original finite face-pair formula and Koszul coefficient. -/
theorem actualCellCupAt_sections (b : SectionPairing F G H) (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (g : (sheafComplex U).X j ⟶ G)
    (s : FaceIndex (V := V) n) :
    sectionsEquiv U H n (actualCellCupAt U b n i j f g) s =
      ∑ z : PairCellIndex U (binaryCoverFaceOpen U s.val) n,
        (if DiagonalShape s.val z.val.1 z.val.2 then (-1 : ℤ)^diagonalCross z.val.1 z.val.2 else 0) •
          b.pairing (binaryCoverFaceOpen U s.val)
            (cellCochainValue U i f (binaryCoverFaceOpen U s.val) z.val.1 z.property.1)
            (cellCochainValue U j g (binaryCoverFaceOpen U s.val) z.val.2 z.property.2.1) := by
  classical
  let W := binaryCoverFaceOpen U s.val
  have hs : faceDegree s.val=n := by
    have h := s.property
    change -(faceDegree s.val : ℤ) = -(n : ℤ) at h
    omega
  let x := openDiagonal U ℤ W n (cellGenerator U ℤ W n s.val le_rfl hs 1)
  let ψ := actualPairCochain U b n i j f g
  let φ : pairedChains U ℤ W n →+ H.obj.obj (op W) :=
    (ψ.hom.app (op W)).hom.comp
      (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
        (toAbelianPresheaf.obj (pairedPresheaf U ℤ n))).app (op W)).hom
  rw [sectionsEquiv_cellSheafSection,actualCellCupAt_pair]
  change ψ.hom.app (op W) (((sheafDiagonalMap U).f n).hom.app (op W)
    (cellSheafSection U W n s.val le_rfl hs 1)) = _
  rw [sheafDiagonal_cellSheafSection]
  change φ x = _
  rw [pairedChains_evaluate U W n φ x]
  apply Finset.sum_congr rfl
  intro z _
  have hc : x.val z.val =
      if DiagonalShape s.val z.val.1 z.val.2 then (-1 : ℤ)^diagonalCross z.val.1 z.val.2 else 0 := by
    change flatDiagonal ℤ V (single s.val 1) z.val = _
    simpa only [flatDiagonal,LinearMap.comp_apply,LinearEquiv.coe_coe,mul_one] using
      diagonal_coefficient ℤ s.val z.val.1 z.val.2 1
  rw [hc]
  congr 1
  exact actualPairCochain_generator U b n i j f g W z.val.1 z.val.2 z.property.1 z.property.2.1 z.property.2.2

end
end BPFixedPoints.SheafTools.BinaryCells
