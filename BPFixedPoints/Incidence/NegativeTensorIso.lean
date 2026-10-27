import BPFixedPoints.Incidence.NegativeTensorDifferential
import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-! # A specified native cochain tensor isomorphism for negative extension

Mathlib's existing liftExtend supplies the integer cochain map from the
proved restriction comparison. Its native boundary condition is empty for
embeddingDownNat. The original integer tensor is zero in positive degrees.
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
local instance negativeTensorIsoSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (P Q : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ)

/-- The original native integer tensor has no positive-degree terms. -/
theorem negativeTensor_isZero_positive (k : ℤ) (hk : 0<k) :
    IsZero ((HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).X k) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=k at h
  by_cases hp : p≤0
  · have hq : 0<q := by omega
    have hz := (tensorLeft ((negativeComplex P).X p)).map_isZero
      (Q.isZero_extend_X ComplexShape.embeddingDownNat q (by intro n; change -(n : ℤ)≠q; omega))
    exact hz.eq_of_src _ _
  · have hz := (tensorRight ((negativeComplex Q).X q)).map_isZero
      (P.isZero_extend_X ComplexShape.embeddingDownNat p (by intro n; change -(n : ℤ)≠p; omega))
    exact hz.eq_of_src _ _

/-- The original integer tensor maps to the negative extension of the original natural tensor by Mathlib's native lift. -/
def negativeTensorLift :
    HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q) ⟶
      negativeComplex (HomologicalComplex.tensorObj P Q) :=
  ComplexShape.embeddingDownNat.liftExtend (negativeTensorRestrictionIso P Q).inv (by
    intro j hj
    exact hj.false_of_isTruncLE.elim)

/-- The native lift retains the previously specified inverse on every original negative degree. -/
theorem negativeTensorLift_component (n : ℕ) :
    (negativeTensorLift P Q).f (-(n : ℤ)) =
      negativeTensorDegreeInv P Q n ≫ (negativeTermIso (HomologicalComplex.tensorObj P Q) n).inv := by
  rw [negativeTensorLift,ComplexShape.Embedding.liftExtend_f _ _ _ (by rfl)]
  simp only [restrictionXIso,eqToIso_refl,Iso.refl_inv,Category.id_comp]
  rfl

/-- The native lift is an actual isomorphism in all integer degrees. -/
theorem negativeTensorLift_isIso : IsIso (negativeTensorLift P Q) := by
  haveI (k : ℤ) : IsIso ((negativeTensorLift P Q).f k) := by
    by_cases hk : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n=k
    · obtain ⟨n,hk⟩ := hk
      apply (ComplexShape.embeddingDownNat.isIso_liftExtend_f_iff (negativeTensorRestrictionIso P Q).inv _ hk).mpr
      change IsIso (negativeTensorDegreeIso P Q n).inv
      infer_instance
    · have hk' : 0<k := by
        by_contra! h
        apply hk
        exact ⟨(-k).toNat,by change -((-k).toNat : ℤ)=k; omega⟩
      exact (negativeTensor_isZero_positive P Q k hk').isIso
        ((HomologicalComplex.tensorObj P Q).isZero_extend_X ComplexShape.embeddingDownNat k
          (by simpa using hk)) _
  exact Hom.isIso_of_components _

/-- Negative extension commutes with the original native tensor totalization as an actual cochain isomorphism. -/
def negativeTensorIso :
    negativeComplex (HomologicalComplex.tensorObj P Q) ≅
      HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q) := by
  letI := negativeTensorLift_isIso P Q
  exact (asIso (negativeTensorLift P Q)).symm

/-- The inverse cochain comparison keeps its original degree formula. -/
theorem negativeTensorIso_inv_component (n : ℕ) :
    (negativeTensorIso P Q).inv.f (-(n : ℤ)) =
      negativeTensorDegreeInv P Q n ≫ (negativeTermIso (HomologicalComplex.tensorObj P Q) n).inv :=
  negativeTensorLift_component P Q n

/-- The forward cochain comparison keeps the original degree map without an additional sign. -/
theorem negativeTensorIso_hom_component (n : ℕ) :
    (negativeTermIso (HomologicalComplex.tensorObj P Q) n).inv ≫
      (negativeTensorIso P Q).hom.f (-(n : ℤ)) = negativeTensorDegreeHom P Q n := by
  apply (cancel_mono ((negativeTensorIso P Q).inv.f (-(n : ℤ)))).mp
  rw [Category.assoc,← comp_f,Iso.hom_inv_id,id_f,Category.comp_id,
    negativeTensorIso_inv_component,← Category.assoc,negativeTensorDegreeHom_inv]
  exact (Category.id_comp _).symm

/-- Every original tensor bidegree is retained by the full native cochain isomorphism. -/
@[reassoc] theorem negativeTensorIso_hom_inclusion (p q n : ℕ) (h : p+q=n) :
    ιTensorObj P Q p q n h ≫ (negativeTermIso (HomologicalComplex.tensorObj P Q) n).inv ≫
      (negativeTensorIso P Q).hom.f (-(n : ℤ)) =
        ((negativeTermIso P p).inv ⊗ₘ (negativeTermIso Q q).inv) ≫
          ιTensorObj (negativeComplex P) (negativeComplex Q) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) := by
  rw [negativeTensorIso_hom_component,negativeTensorDegreeHom_inclusion]

end
end BPFixedPoints.SheafTools.BinaryCells
