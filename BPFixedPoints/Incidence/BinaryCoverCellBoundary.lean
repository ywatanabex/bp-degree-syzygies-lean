import BPFixedPoints.Incidence.BinaryCoverCellEndpoint

/-! # Original cubical cell generators retain the original boundary

The original cell-presheaf differential is evaluated on the original free-open
generators. The resulting boundary is the original signed sum of original
endpoint inclusions, with the original fixed enumeration and prefix signs.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- The original differential after forgetting only the original integer module structure. -/
noncomputable def abelianDifferential (n : ℕ) : presheafTerm U (n+1) ⟶ presheafTerm U n :=
  (toAbelianPresheaf (T := T)).map (presheafDifferential U ℤ n)

/-- Evaluation at an original represented free-open generator retains the original cell coefficients. -/
noncomputable def coefficientEvaluation (n : ℕ) (A W : Opens T) (i : W ⟶ A) :
    ((yoneda.obj A ⋙ AddCommGrpCat.free) ⟶ presheafTerm U n) →+ Cells ℤ V where
  toFun f := let x : chains U ℤ W n := f.app (op W) (FreeAbelianGroup.of i); x.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original free-open inclusion evaluates to the same original endpoint cell. -/
theorem coefficientEvaluation_generator {n : ℕ} (q : FaceIndex (V := V) n)
    (A W : Opens T) (i : W ⟶ A) (h : A ≤ binaryCoverFaceOpen U q.val) :
    coefficientEvaluation U n A W i (freeOpenPresheafMap h ≫ presheafGenerator U q) = single q.val 1 := by
  change ((presheafGenerator U q).app (op W)
    (FreeAbelianGroup.map (fun j => j ≫ homOfLE h) (FreeAbelianGroup.of i)) : chains U ℤ W n).val = _
  rw [FreeAbelianGroup.map_of_apply]
  exact presheafGenerator_app_of_val U q W (i ≫ homOfLE h)

/-- The original presheaf generator is acted on by exactly the original full cell boundary. -/
theorem coefficientEvaluation_boundary {n : ℕ} (q : FaceIndex (V := V) (n+1))
    (W : Opens T) (i : W ⟶ binaryCoverFaceOpen U q.val) :
    coefficientEvaluation U n _ W i (presheafGenerator U q ≫ abelianDifferential U n) =
      (CechCubicalCell.contraction ℤ (fun _ : V => 0)).d (single q.val 1) := by
  change (CechCubicalCell.contraction ℤ (fun _ : V => 0)).d
    ((presheafGenerator U q).app (op W) (FreeAbelianGroup.of i) : chains U ℤ W (n+1)).val = _
  rw [presheafGenerator_app_of_val]

/-- The original cell-presheaf boundary is exactly the original signed sum of original endpoint inclusions. -/
theorem presheafGenerator_boundary {n : ℕ} (q : FaceIndex (V := V) (n+1)) :
    presheafGenerator U q ≫ abelianDifferential U n =
      ∑ v, if hv : q.val v = 2 then
        (-1 : ℤ)^faceBoundaryPrefix q.val v •
          (freeOpenPresheafMap (endpointOpenLE U q v hv 0) ≫ presheafGenerator U (endpoint q v hv 0) -
            freeOpenPresheafMap (endpointOpenLE U q v hv 1) ≫ presheafGenerator U (endpoint q v hv 1))
        else 0 := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  apply Subtype.ext
  change coefficientEvaluation U n _ W.unop i (presheafGenerator U q ≫ abelianDifferential U n) =
    coefficientEvaluation U n _ W.unop i _
  rw [coefficientEvaluation_boundary,map_sum,CechCubicalCell.contraction_d_single]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : q.val v = 2
  · rw [dite_eq_left hv,map_zsmul,map_sub,coefficientEvaluation_generator,coefficientEvaluation_generator]
    simp only [endpoint,hv,ite_true,mul_one,smul_sub,Finsupp.smul_single,smul_eq_mul]
    rfl
  · rw [dite_eq_right hv,map_zero]
    simp only [hv,ite_false,zero_mul,mul_zero,Finsupp.single_zero,sub_self]

/-- The original boundary after the original sheafification. -/
noncomputable def boundary (n : ℕ) : sheafTerm U (n+1) ⟶ sheafTerm U n :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map (abelianDifferential U n)

/-- The displayed original boundary is exactly the differential of the originally constructed sheaf complex. -/
theorem boundary_eq_d (n : ℕ) : boundary U n = (sheafComplex U).d (n+1) n := by
  simp only [boundary,sheafComplex,abelianPresheafComplex,presheafComplex,
    Functor.mapHomologicalComplex_obj_d,ChainComplex.of_d,abelianDifferential]

/-- Sheafification retains the original generator boundary, original inclusion maps and original signs. -/
theorem generator_boundary {n : ℕ} (q : FaceIndex (V := V) (n+1)) :
    generator U q ≫ boundary U n =
      ∑ v, if hv : q.val v = 2 then
        (-1 : ℤ)^faceBoundaryPrefix q.val v •
          ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
              (freeOpenPresheafMap (endpointOpenLE U q v hv 0)) ≫ generator U (endpoint q v hv 0) -
            (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
              (freeOpenPresheafMap (endpointOpenLE U q v hv 1)) ≫ generator U (endpoint q v hv 1))
        else 0 := by
  rw [generator,boundary,← Functor.map_comp,presheafGenerator_boundary,Functor.map_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : q.val v = 2
  · simp only [dite_eq_left hv,Functor.map_zsmul,Functor.map_sub,Functor.map_comp,generator]
  · simp only [dite_eq_right hv,Functor.map_zero]

end BPFixedPoints.SheafTools.BinaryCells
