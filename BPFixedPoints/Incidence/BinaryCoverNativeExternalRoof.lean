import BPFixedPoints.Incidence.BinaryCoverNativeTensorRepresentativeIndependence

/-! # Actual input cohomology classes determine a unique original native tensor roof

Existence uses the proved original acyclic-resolution comparison.
Uniqueness is the proved representative independence of the native tensor
roof itself. The product is specified by these actual derived morphisms,
not by state coordinates or an arbitrarily transported multiplication.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance nativeExternalRoofHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance nativeExternalRoofDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H) (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- The actual derived morphism type of the original native tensor-product roof. -/
abbrev NativeExternalRoof (i j : ℕ) :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
    (actualComponentSheaf (V := V) (T := T) ⊗ actualComponentSheaf (V := V) (T := T))) ⟶
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ (-((i+j : ℕ) : ℤ))).obj H)

/-- An actual roof is represented by the native tensor of original representatives of the two specified actual input classes. -/
def IsNativeExternalRoof (i j : ℕ) (a : F.H i) (c : G.H j)
    (r : NativeExternalRoof (T := T) (V := V) (H := H) i j) : Prop :=
  ∃ (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j),
    nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x)=a ∧
    nativeCubicalComparison U G hcover j ((cubicalTower U).classAt G j y)=c ∧
    actualNativeTensorProductRoof U b hcover i j x.val (cubicalCycle_closed U i x)
      y.val (cubicalCycle_closed U j y)=r

/-- Every pair of actual input cohomology classes determines one and only one original native tensor roof. -/
theorem existsUnique_nativeExternalRoof
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) :
    ∃! r, IsNativeExternalRoof U b hcover i j a c r := by
  obtain ⟨cx,hcx⟩ := (nativeCubicalComparison_bijective U F hcover haF i).surjective a
  obtain ⟨x,rfl⟩ := (cubicalTower U).classAt_surjective F i cx
  obtain ⟨cy,hcy⟩ := (nativeCubicalComparison_bijective U G hcover haG j).surjective c
  obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j cy
  refine ⟨actualNativeTensorProductRoof U b hcover i j x.val (cubicalCycle_closed U i x)
    y.val (cubicalCycle_closed U j y),⟨x,y,hcx,hcy,rfl⟩,?_⟩
  rintro r ⟨x',y',hx',hy',hr⟩
  rw [← hr]
  exact actualNativeTensorProductRoof_eq_of_input_classes U b hcover haF haG i j x' x y' y
    (hx'.trans hcx.symm) (hy'.trans hcy.symm)

/-- The unique actual native tensor roof of the two specified actual input classes. -/
def actualNativeExternalRoof
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) : NativeExternalRoof (T := T) (V := V) (H := H) i j :=
  Classical.choose (existsUnique_nativeExternalRoof U b hcover haF haG i j a c)

/-- Every choice of original representatives computes this same specified actual native roof. -/
theorem actualNativeExternalRoof_representative
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    actualNativeExternalRoof U b hcover haF haG i j
      (nativeCubicalComparison U F hcover i ((cubicalTower U).classAt F i x))
      (nativeCubicalComparison U G hcover j ((cubicalTower U).classAt G j y)) =
    actualNativeTensorProductRoof U b hcover i j x.val (cubicalCycle_closed U i x)
      y.val (cubicalCycle_closed U j y) :=
  ((Classical.choose_spec (existsUnique_nativeExternalRoof U b hcover haF haG i j _ _)).2
    _ ⟨x,y,rfl,rfl,rfl⟩).symm

/-- The actual cohomology class of the uniquely specified native tensor roof, through the original unit and native single shift. -/
def actualNativeClassProduct
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) : H.H (i+j) :=
  localSheafTopEquiv H (i+j) (Ext.homEquiv.symm
    ((DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
      actualNativeExternalRoof U b hcover haF haG i j a c) ≫
        ((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ) (-((i+j : ℕ) : ℤ)) 0
          (by omega)).inv.app H))

/-- Every original pair of quotient classes has the original quotient cup as the native cohomology image of its specified tensor roof. -/
theorem actualNativeClassProduct_quotient
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (i j : ℕ) (x : cubicalCohomologyAt U F i) (y : cubicalCohomologyAt U G j) :
    actualNativeClassProduct U b hcover haF haG i j
      (nativeCubicalComparison U F hcover i x) (nativeCubicalComparison U G hcover j y) =
      nativeCubicalComparison U H hcover (i+j) (cubicalCohomologyCupAt U b (i+j) i j x y) := by
  obtain ⟨x,rfl⟩ := (cubicalTower U).classAt_surjective F i x
  obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
  unfold actualNativeClassProduct
  rw [actualNativeExternalRoof_representative]
  exact (nativeCubicalComparison_cup_representative U b hcover i j x y).symm

end
end BPFixedPoints.SheafTools.BinaryCells
