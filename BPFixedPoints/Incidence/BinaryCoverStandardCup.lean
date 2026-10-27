import BPFixedPoints.Incidence.BinaryCoverTerminalUnit
import BPFixedPoints.Incidence.NativeShiftedTensorCocyclePairing
import BPFixedPoints.Incidence.BinaryCoverNativeClassProduct
import BPFixedPoints.Incidence.ResolutionNativeCupSign

/-! # The standard external cup through the original cell resolution

The standard external roof of two original cocycles is built from the
standard data only: the identification of the original terminal sheaf with
the actual tensor unit, the inverse standard left unitor, the inverse
tensor of the two unit input augmentations, and Mathlib's standard ordered
tensor shifts applied to the two original input maps with the original
pairing. It is not defined from the native negative-degree pairing or from
states. It equals the original native cup roof times the Koszul sign
(-1)^(ij), as a theorem.

On actual Ext-defined cohomology this gives a biadditive product computed by
every choice of original representatives. With the original iterated
Yoneda normalization of both inputs and the output, the original geometric
cup is exactly this standard product: the accumulated triangular signs and
the Koszul sign cancel, and no sign is inserted by hand.

Independence from the chosen cover or resolution is not claimed here.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance standardCupSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
local instance standardCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
local instance standardCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)

/-- The standard external roof of two original cocycles: unit identification, inverse standard left unitor, inverse tensor of the unit input augmentations, and Mathlib's standard shifted tensor pairing of the original input maps. -/
def actualStandardTensorRoof (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
    (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj (actualTerminalSheaf (T := T))) ⟶
      DerivedCategory.Q.obj (((CochainComplex.singleFunctor _ 0).obj H)⟦((i+j : ℕ) : ℤ)⟧) :=
  DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
      ((actualTerminalUnitIso (T := T) (V := V)).hom ≫
        (λ_ (𝟙_ (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}))).inv)) ≫
    (actualUnitTensorAugmentationIso U hcover).inv ≫
      DerivedCategory.Q.map (nativeShiftedTensorCocyclePairing b i j
        (negativeCocycleMap (sheafComplex U) i x hx) (negativeCocycleMap (sheafComplex U) j y hy))

/-- The standard external roof is the original native cup roof times the Koszul sign. -/
theorem actualStandardTensorRoof_native (i j : ℕ) (x : (sheafComplex U).X i ⟶ F)
    (hx : (sheafComplex U).d (i+1) i ≫ x=0) (y : (sheafComplex U).X j ⟶ G)
    (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    actualStandardTensorRoof U hcover b i j x hx y hy =
      ((i : ℤ)*j).negOnePow • (actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
        (actualCellCupAt_closed U b (i+j) i j x y hx hy) ≫
          DerivedCategory.Q.map (((CochainComplex.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ)
            (-((i+j : ℕ) : ℤ)) 0 (by omega)).inv.app H)) := by
  rw [actualCellNativeRoof_unit_tensor,actualStandardTensorRoof,nativeShiftedTensorCocyclePairing_eq]
  simp only [Units.smul_def,Functor.map_zsmul,Preadditive.comp_zsmul,
    Functor.map_comp,Category.assoc,nativeIntegerTensorCocycleMap]
  rfl

/-- The standard external roof as an actual Ext class, through the native commutation of the localization with shifts. -/
def actualStandardCupExt (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
    (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    Ext (actualTerminalSheaf (T := T)) H (i+j) :=
  Ext.homEquiv.symm (actualStandardTensorRoof U hcover b i j x hx y hy ≫
    (DerivedCategory.Q.commShiftIso ((i+j : ℕ) : ℤ)).hom.app ((CochainComplex.singleFunctor _ 0).obj H))

/-- The standard Ext class is the Koszul sign times the Ext class of the original native cup roof. -/
theorem actualStandardCupExt_native (i j : ℕ) (x : (sheafComplex U).X i ⟶ F)
    (hx : (sheafComplex U).d (i+1) i ≫ x=0) (y : (sheafComplex U).X j ⟶ G)
    (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    actualStandardCupExt U hcover b i j x hx y hy =
      ((i : ℤ)*j).negOnePow • Ext.homEquiv.symm
        (actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
          (actualCellCupAt_closed U b (i+j) i j x y hx hy) ≫
            ((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ) (-((i+j : ℕ) : ℤ)) 0
              (by omega)).inv.app H) := by
  apply Ext.ext
  rw [nativeExt_units_hom]
  simp only [actualStandardCupExt,Ext.hom,Equiv.apply_symm_apply,actualStandardTensorRoof_native,
    Linear.units_smul_comp,Category.assoc]
  congr 2
  simp [DerivedCategory.singleFunctors]

/-- The standard product class of two original cocycles in actual Ext-defined cohomology. -/
def actualStandardCupClass (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
    (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0) : H.H (i+j) :=
  localSheafTopEquiv H (i+j) (actualStandardCupExt U hcover b i j x hx y hy)

/-- The standard product class is the Koszul sign times the native image of the original quotient cup. -/
theorem actualStandardCupClass_native (i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    actualStandardCupClass U hcover b i j x.val (cubicalCycle_closed U i x) y.val (cubicalCycle_closed U j y) =
      ((i : ℤ)*j).negOnePow • nativeCubicalComparison U H hcover (i+j)
        (cubicalCohomologyCupAt U b (i+j) i j ((cubicalTower U).classAt F i x) ((cubicalTower U).classAt G j y)) := by
  rw [nativeCubicalComparison_cup_representative,actualStandardCupClass,actualStandardCupExt_native,
    actualCellNativeRoof_cup,Units.smul_def,Units.smul_def,map_zsmul]
  rfl

/-- An original representative cycle of an actual class, chosen through the original native comparison. -/
def nativeCubicalCycleRep {K : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (haK : ComplexAcyclicAgainst (sheafComplex U) K) (n : ℕ) (a : K.H n) : (cubicalTower U).cycles K n :=
  Classical.choose ((cubicalTower U).classAt_surjective K n
    (Classical.choose ((nativeCubicalComparison_bijective U K hcover haK n).surjective a)))

/-- The chosen original representative has the given actual class. -/
theorem nativeCubicalCycleRep_spec {K : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (haK : ComplexAcyclicAgainst (sheafComplex U) K) (n : ℕ) (a : K.H n) :
    nativeCubicalComparison U K hcover n
      ((cubicalTower U).classAt K n (nativeCubicalCycleRep U hcover haK n a)) = a := by
  unfold nativeCubicalCycleRep
  rw [Classical.choose_spec ((cubicalTower U).classAt_surjective K n _)]
  exact Classical.choose_spec ((nativeCubicalComparison_bijective U K hcover haK n).surjective a)

variable (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)

/-- The standard product of two actual classes: the standard external roof of original representatives. -/
def actualStandardClassProduct (i j : ℕ) (a : F.H i) (c : G.H j) : H.H (i+j) :=
  actualStandardCupClass U hcover b i j (nativeCubicalCycleRep U hcover haF i a).val
    (cubicalCycle_closed U i _) (nativeCubicalCycleRep U hcover haG j c).val (cubicalCycle_closed U j _)

/-- The standard product is the Koszul sign times the existing native roof product, as a theorem. -/
theorem actualStandardClassProduct_native (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassProduct U hcover b haF haG i j a c =
      ((i : ℤ)*j).negOnePow • actualNativeClassCup U b hcover haF haG i j a c := by
  rw [actualStandardClassProduct,actualStandardCupClass_native,← actualNativeClassCup_quotient,
    nativeCubicalCycleRep_spec,nativeCubicalCycleRep_spec]

/-- Every choice of original representatives computes the standard product by its own standard roof. -/
theorem actualStandardClassProduct_representative (i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    actualStandardClassProduct U hcover b haF haG i j
        (nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x))
        (nativeCubicalComparison U G hcover j ((cubicalTower U).classAt G j y)) =
      actualStandardCupClass U hcover b i j x.val (cubicalCycle_closed U i x) y.val (cubicalCycle_closed U j y) := by
  rw [actualStandardClassProduct_native,actualNativeClassCup_quotient,actualStandardCupClass_native]

/-- The standard product as a biadditive map of actual Ext-defined cohomology. -/
def actualStandardClassCup (i j : ℕ) : F.H i →+ G.H j →+ H.H (i+j) where
  toFun a :=
    { toFun := actualStandardClassProduct U hcover b haF haG i j a
      map_zero' := by simp [actualStandardClassProduct_native]
      map_add' := by intro c c'; simp [actualStandardClassProduct_native,smul_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro c
    simp [actualStandardClassProduct_native]
  map_add' a a' := by
    apply AddMonoidHom.ext
    intro c
    simp [actualStandardClassProduct_native,smul_add]

/-- The biadditive standard product evaluates the standard product. -/
@[simp] theorem actualStandardClassCup_apply (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hcover b haF haG i j a c = actualStandardClassProduct U hcover b haF haG i j a c := rfl

/-- The original iterated Yoneda comparison is the native comparison times the same accumulated sign. -/
theorem finiteCubicalActualAtEquiv_native {K : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (haK : ComplexAcyclicAgainst (sheafComplex U) K) (n : ℕ) (z : cubicalCohomologyAt U K n) :
    finiteCubicalActualAtEquiv U K hcover haK n z = nativeYonedaSign n • nativeCubicalComparison U K hcover n z := by
  rw [nativeCubicalComparison_yoneda U K hcover haK,smul_smul,Int.units_mul_self,one_smul]

/-- With the original iterated Yoneda normalization of both inputs and the output, the original geometric quotient cup is exactly the standard product. -/
theorem finiteCubicalActualAtEquiv_cup (haH : ComplexAcyclicAgainst (sheafComplex U) H) (i j : ℕ)
    (x : cubicalCohomologyAt U F i) (y : cubicalCohomologyAt U G j) :
    finiteCubicalActualAtEquiv U H hcover haH (i+j) (cubicalCohomologyCupAt U b (i+j) i j x y) =
      actualStandardClassCup U hcover b haF haG i j (finiteCubicalActualAtEquiv U F hcover haF i x)
        (finiteCubicalActualAtEquiv U G hcover haG j y) := by
  rw [finiteCubicalActualAtEquiv_native U hcover haH,finiteCubicalActualAtEquiv_native U hcover haF,
    finiteCubicalActualAtEquiv_native U hcover haG,actualStandardClassCup_apply,actualStandardClassProduct_native]
  simp only [Units.smul_def,map_zsmul,AddMonoidHom.zsmul_apply,actualNativeClassCup_quotient,smul_smul]
  congr 1
  rw [nativeYonedaSign_add]
  push_cast
  ring

end
end BPFixedPoints.SheafTools.BinaryCells
