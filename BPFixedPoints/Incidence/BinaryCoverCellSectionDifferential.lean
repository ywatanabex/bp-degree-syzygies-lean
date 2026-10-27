import BPFixedPoints.Incidence.BinaryCoverCellBoundary

/-! # The original cubical Hom differential is the actual restriction difference

Every original cell coordinate retains its actual section, its actual
endpoint restriction maps and its original tensor prefix sign.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The specified original cubical boundary gives precisely the actual signed endpoint restriction difference. -/
theorem sectionsEquiv_boundary (n : ℕ) (f : sheafTerm U n ⟶ F)
    (q : FaceIndex (V := V) (n+1)) :
    sectionsEquiv U F (n+1) ((sheafComplex U).d (n+1) n ≫ f) q =
      ∑ v, if hv : q.val v = 2 then
        (-1 : ℤ)^faceBoundaryPrefix q.val v •
          (F.obj.map (homOfLE (endpointOpenLE U q v hv 0)).op
              (sectionsEquiv U F n f (endpoint q v hv 0)) -
            F.obj.map (homOfLE (endpointOpenLE U q v hv 1)).op
              (sectionsEquiv U F n f (endpoint q v hv 1)))
        else 0 := by
  rw [sectionsEquiv_apply,← boundary_eq_d,← Category.assoc,generator_boundary,
    Preadditive.sum_comp,map_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : q.val v = 2
  · rw [dite_eq_left hv,dite_eq_left hv,Preadditive.zsmul_comp,map_zsmul,
      Preadditive.sub_comp,map_sub,Category.assoc,Category.assoc]
    congr 2
    all_goals
      dsimp only [freeOpenPresheafMap]
      rw [freeSheafSectionsEquiv_naturality,sectionsEquiv_apply]
  · simp only [dite_eq_right hv,zero_comp,map_zero]

end BPFixedPoints.SheafTools.BinaryCells
