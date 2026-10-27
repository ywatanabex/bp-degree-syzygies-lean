import BPFixedPoints.Incidence.ResolutionNativeCocycleMaps
import BPFixedPoints.Incidence.BinaryCoverCellSheafCup

/-! # Native tensor pairings of single-degree actual sheaf complexes

The target map descends the native bidegree coproduct and evaluates the
original sheaf pairing. It is independent of the cell diagonal and all
cohomology comparisons.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T]
local instance singleTensorSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- An actual sheaf in its native single homological degree. -/
abbrev actualSingleChain (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (i : ℕ) :=
  (single _ (ComplexShape.down ℕ) i).obj F

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- The original pairing on the native degree-sum term of the tensor of two single complexes. -/
def singleTensorPairingTerm (i j n : ℕ) :
    (HomologicalComplex.tensorObj (actualSingleChain F i) (actualSingleChain G j)).X n ⟶ H :=
  mapBifunctorDesc (fun p q _ => by
    by_cases hp : p=i
    · subst p
      by_cases hq : q=j
      · subst q
        exact ((singleObjXSelf (ComplexShape.down ℕ) i F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.down ℕ) j G).hom) ≫ b.sheafMap
      · exact 0
    · exact 0)

/-- The independently defined tensor pairing retains its original single bidegree. -/
@[reassoc] theorem singleTensorPairingTerm_same (i j : ℕ) :
    ιTensorObj (actualSingleChain F i) (actualSingleChain G j) i j (i+j) rfl ≫
      singleTensorPairingTerm b i j (i+j) =
        ((singleObjXSelf (ComplexShape.down ℕ) i F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.down ℕ) j G).hom) ≫ b.sheafMap := by
  rw [singleTensorPairingTerm,ι_mapBifunctorDesc]
  simp only [dite_true]

/-- Every other native bidegree has zero pairing. -/
@[reassoc] theorem singleTensorPairingTerm_other (i j n p q : ℕ) (h : p+q=n) (hne : p≠i ∨ q≠j) :
    ιTensorObj (actualSingleChain F i) (actualSingleChain G j) p q n h ≫
      singleTensorPairingTerm b i j n=0 := by
  rw [singleTensorPairingTerm,ι_mapBifunctorDesc]
  by_cases hp : p=i
  · subst p
    simp only [dite_true,dif_neg (hne.resolve_left (by simp))]
  · simp only [dif_neg hp]

/-- The native tensor of single complexes has its independently specified zero differential. -/
theorem singleTensor_d_zero (i j k l : ℕ) :
    (HomologicalComplex.tensorObj (actualSingleChain F i) (actualSingleChain G j)).d k l=0 := by
  apply mapBifunctor.hom_ext
  intro p q h
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,comp_zero]
  have h₁ : mapBifunctor.d₁ (actualSingleChain F i) (actualSingleChain G j)
      (curriedTensor _) (ComplexShape.down ℕ) p q l=0 := by
    by_cases hp : p=0
    · subst p
      exact mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp)
    · obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
      rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.down ℕ).Rel (p+1) p from rfl)]
      simp [actualSingleChain]
  have h₂ : mapBifunctor.d₂ (actualSingleChain F i) (actualSingleChain G j)
      (curriedTensor _) (ComplexShape.down ℕ) p q l=0 := by
    by_cases hq : q=0
    · subst q
      exact mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)
    · obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
      rw [mapBifunctor.d₂_eq' _ _ _ _ p (show (ComplexShape.down ℕ).Rel (q+1) q from rfl)]
      simp [actualSingleChain]
  rw [h₁,h₂,add_zero]

/-- The independently specified pairing of native single complexes in the original sum degree. -/
def singleTensorPairingMap (i j : ℕ) :
    HomologicalComplex.tensorObj (actualSingleChain F i) (actualSingleChain G j) ⟶ actualSingleChain H (i+j) :=
  closedChainMap _ (i+j) (singleTensorPairingTerm b i j (i+j))
    (by rw [singleTensor_d_zero,zero_comp])

end
end BPFixedPoints.SheafTools.BinaryCells
