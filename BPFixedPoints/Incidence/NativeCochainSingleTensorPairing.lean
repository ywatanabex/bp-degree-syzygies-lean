import BPFixedPoints.Incidence.NativeSingleTensorPairing
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Original sheaf pairings on native integer single cochain complexes

These maps use Mathlib's original integer cochain tensor totalization.
No cell complex, cohomology quotient or state multiplication is used.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T]
local instance cochainSingleTensorSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The actual original sheaf in its native single integer cochain degree. -/
abbrev actualSingleCochain (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (i : ℤ) :=
  (CochainComplex.singleFunctor _ i).obj F

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- Native integer totalization evaluates the original pairing on the specified single bidegree. -/
def singleCochainTensorPairingTerm (p q n : ℤ) :
    (HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q)).X n ⟶ H :=
  mapBifunctorDesc (fun i j _ => by
    by_cases hi : i=p
    · subst i
      by_cases hj : j=q
      · subst j
        exact ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ b.sheafMap
      · exact 0
    · exact 0)

/-- The original integer single bidegree retains the original coefficient pairing. -/
@[reassoc] theorem singleCochainTensorPairingTerm_same (p q n : ℤ) (h : p+q=n) :
    ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) p q n h ≫
      singleCochainTensorPairingTerm b p q n =
        ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ b.sheafMap := by
  rw [singleCochainTensorPairingTerm,ι_mapBifunctorDesc]
  simp only [dite_true]

/-- Every other native integer bidegree has zero coefficient pairing. -/
@[reassoc] theorem singleCochainTensorPairingTerm_other (p q n i j : ℤ)
    (h : i+j=n) (hne : i≠p ∨ j≠q) :
    ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) i j n h ≫
      singleCochainTensorPairingTerm b p q n=0 := by
  rw [singleCochainTensorPairingTerm,ι_mapBifunctorDesc]
  by_cases hi : i=p
  · subst i
    simp only [dite_true,dif_neg (hne.resolve_left (by simp))]
  · simp only [dif_neg hi]

/-- The actual tensor differential of two native integer single complexes is zero. -/
theorem singleCochainTensor_d_zero (p q k l : ℤ) :
    (HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q)).d k l=0 := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,comp_zero]
  rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
    mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.up ℤ).Rel j (j+1) from rfl)]
  simp [actualSingleCochain,CochainComplex.singleFunctor_obj_d]

/-- The original sheaf pairing as a native integer cochain map to its specified single target degree. -/
def singleCochainTensorPairingMap (p q n : ℤ) :
    HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q) ⟶
      actualSingleCochain H n :=
  mkHomToSingle (singleCochainTensorPairingTerm b p q n) (by
    intro k hk
    rw [singleCochainTensor_d_zero,zero_comp])

/-- The native integer cochain map retains the original pairing on its original bidegree. -/
@[reassoc] theorem singleCochainTensorPairingMap_same (p q n : ℤ) (h : p+q=n) :
    ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) p q n h ≫
      (singleCochainTensorPairingMap b p q n).f n =
        ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ b.sheafMap ≫
            (singleObjXSelf (ComplexShape.up ℤ) n H).inv := by
  rw [singleCochainTensorPairingMap,mkHomToSingle_f,← Category.assoc,singleCochainTensorPairingTerm_same]
  rw [Category.assoc]

end
end BPFixedPoints.SheafTools.BinaryCells
