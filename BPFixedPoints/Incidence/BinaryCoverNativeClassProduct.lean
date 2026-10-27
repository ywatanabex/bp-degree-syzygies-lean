import BPFixedPoints.Incidence.BinaryCoverNativeExternalRoof

/-! # The biadditive actual cohomology product of the original native tensor roofs

The already specified unique derived roof supplies the product. Its
biadditivity follows from the proved representative formula and the
original quotient cup, without imposing acyclicity on the output sheaf.
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
local instance nativeClassProductHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance nativeClassProductDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H) (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
variable (haF : ComplexAcyclicAgainst (sheafComplex U) F)
    (haG : ComplexAcyclicAgainst (sheafComplex U) G)

/-- The specified native roof product is additive in its first actual input class. -/
theorem actualNativeClassProduct_add_left (i j : ℕ) (a a' : F.H i) (c : G.H j) :
    actualNativeClassProduct U b hcover haF haG i j (a+a') c =
      actualNativeClassProduct U b hcover haF haG i j a c +
        actualNativeClassProduct U b hcover haF haG i j a' c := by
  obtain ⟨x,rfl⟩ := (nativeCubicalComparison_bijective U F hcover haF i).surjective a
  obtain ⟨x',rfl⟩ := (nativeCubicalComparison_bijective U F hcover haF i).surjective a'
  obtain ⟨y,rfl⟩ := (nativeCubicalComparison_bijective U G hcover haG j).surjective c
  rw [← map_add,actualNativeClassProduct_quotient,actualNativeClassProduct_quotient,
    actualNativeClassProduct_quotient,map_add,AddMonoidHom.add_apply,map_add]

/-- The specified native roof product is additive in its second actual input class. -/
theorem actualNativeClassProduct_add_right (i j : ℕ) (a : F.H i) (c c' : G.H j) :
    actualNativeClassProduct U b hcover haF haG i j a (c+c') =
      actualNativeClassProduct U b hcover haF haG i j a c +
        actualNativeClassProduct U b hcover haF haG i j a c' := by
  obtain ⟨x,rfl⟩ := (nativeCubicalComparison_bijective U F hcover haF i).surjective a
  obtain ⟨y,rfl⟩ := (nativeCubicalComparison_bijective U G hcover haG j).surjective c
  obtain ⟨y',rfl⟩ := (nativeCubicalComparison_bijective U G hcover haG j).surjective c'
  rw [← map_add,actualNativeClassProduct_quotient,actualNativeClassProduct_quotient,
    actualNativeClassProduct_quotient,map_add,map_add]

/-- The original native roof product vanishes when its first input is zero. -/
@[simp] theorem actualNativeClassProduct_zero_left (i j : ℕ) (c : G.H j) :
    actualNativeClassProduct U b hcover haF haG i j 0 c = 0 := by
  have h := actualNativeClassProduct_add_left U b hcover haF haG i j 0 0 c
  simpa only [zero_add,add_eq_left] using h.symm

/-- The original native roof product vanishes when its second input is zero. -/
@[simp] theorem actualNativeClassProduct_zero_right (i j : ℕ) (a : F.H i) :
    actualNativeClassProduct U b hcover haF haG i j a 0 = 0 := by
  have h := actualNativeClassProduct_add_right U b hcover haF haG i j a 0 0
  simpa only [zero_add,add_eq_left] using h.symm

/-- The specified actual native tensor roof product as a biadditive map of actual Ext-defined cohomology. -/
def actualNativeClassCup (i j : ℕ) : F.H i →+ G.H j →+ H.H (i+j) where
  toFun a :=
    { toFun := actualNativeClassProduct U b hcover haF haG i j a
      map_zero' := actualNativeClassProduct_zero_right U b hcover haF haG i j a
      map_add' := actualNativeClassProduct_add_right U b hcover haF haG i j a }
  map_zero' := by
    apply AddMonoidHom.ext
    intro c
    exact actualNativeClassProduct_zero_left U b hcover haF haG i j c
  map_add' a a' := by
    apply AddMonoidHom.ext
    intro c
    exact actualNativeClassProduct_add_left U b hcover haF haG i j a a' c

/-- This actual biadditive product retains the original quotient cup under the original native comparison in every degree. -/
theorem actualNativeClassCup_quotient (i j : ℕ)
    (x : cubicalCohomologyAt U F i) (y : cubicalCohomologyAt U G j) :
    actualNativeClassCup U b hcover haF haG i j
      (nativeCubicalComparison U F hcover i x) (nativeCubicalComparison U G hcover j y) =
      nativeCubicalComparison U H hcover (i+j) (cubicalCohomologyCupAt U b (i+j) i j x y) :=
  actualNativeClassProduct_quotient U b hcover haF haG i j x y

end
end BPFixedPoints.SheafTools.BinaryCells
