import BPFixedPoints.Incidence.BinaryCoverNativeCohomologyCup

/-! # The original native tensor roof depends only on its actual input classes

The original quotient cup and the proved native comparison injectivity
supply representative independence. The roof itself still tensors the
original two representative maps and retains its independent augmentation.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance tensorRepIndependenceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance tensorRepIndependenceDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H) (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- Native actual cohomology equality recovers equality in the same original input quotient under original term acyclicity. -/
theorem nativeCubicalClass_eq_of_image_eq
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (i : ℕ)
    (x x' : (cubicalTower U).cycles F i)
    (h : nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x) =
      nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x')) :
    (cubicalTower U).classAt F i x=(cubicalTower U).classAt F i x' :=
  (nativeCubicalComparison_bijective U F hcover ha i).injective h

/-- The original native tensor-product roof is independent of representatives of its two actual input cohomology classes. -/
theorem actualNativeTensorProductRoof_eq_of_input_classes
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (x x' : (cubicalTower U).cycles F i) (y y' : (cubicalTower U).cycles G j)
    (hx : nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x) =
      nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x'))
    (hy : nativeCubicalComparison U G hcover j ((cubicalTower U).classAt G j y) =
      nativeCubicalComparison U G hcover j ((cubicalTower U).classAt G j y')) :
    actualNativeTensorProductRoof U b hcover i j x.val (cubicalCycle_closed U i x)
      y.val (cubicalCycle_closed U j y) =
    actualNativeTensorProductRoof U b hcover i j x'.val (cubicalCycle_closed U i x')
      y'.val (cubicalCycle_closed U j y') := by
  have hcx := nativeCubicalClass_eq_of_image_eq U hcover haF i x x' hx
  have hcy := nativeCubicalClass_eq_of_image_eq U hcover haG j y y' hy
  have hc : nativeCubicalComparison U H hcover (i+j)
      (cubicalCohomologyCupAt U b (i+j) i j
        ((cubicalTower U).classAt F i x) ((cubicalTower U).classAt G j y)) =
    nativeCubicalComparison U H hcover (i+j)
      (cubicalCohomologyCupAt U b (i+j) i j
        ((cubicalTower U).classAt F i x') ((cubicalTower U).classAt G j y')) := by
    rw [hcx,hcy]
  rw [nativeCubicalComparison_cup_representative U b hcover i j x y,
    nativeCubicalComparison_cup_representative U b hcover i j x' y'] at hc
  have he := (localSheafTopEquiv H (i+j)).injective hc
  have hm := congrArg Ext.homEquiv he
  simp only [Equiv.apply_symm_apply] at hm
  exact (cancel_epi (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
    (actualTensorTerminalIso (V := V) (T := T)).hom))).mp
      ((cancel_mono (((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ)
        (-((i+j : ℕ) : ℤ)) 0 (by omega)).inv.app H)).mp hm)


end
end BPFixedPoints.SheafTools.BinaryCells
