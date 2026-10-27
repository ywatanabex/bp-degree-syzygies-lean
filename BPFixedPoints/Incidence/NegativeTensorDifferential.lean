import BPFixedPoints.Incidence.NegativeTensorDegreeIso
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! # The original tensor differentials agree under negative extension

The native natural chain differential and the native integer cochain
differential are compared on each original tensor bidegree, including
the boundary in degree zero and the right-factor Koszul sign.
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
local instance negativeTensorDifferentialSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (P Q : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ)

/-- The original differential retains the native negative-extension term identifications. -/
@[reassoc] theorem negativeTermIso_inv_d (n : ℕ) :
    (negativeTermIso P (n+1)).inv ≫ (negativeComplex P).d (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) =
      P.d (n+1) n ≫ (negativeTermIso P n).inv := by
  rw [extend_d_eq P ComplexShape.embeddingDownNat (by rfl) (by rfl)]
  simp [negativeTermIso,Category.assoc]

/-- The original negative extension has no outgoing differential from its degree-zero term. -/
theorem negativeComplex_d_from_zero (k : ℤ) : (negativeComplex P).d 0 k=0 :=
  extend_d_from_eq_zero P ComplexShape.embeddingDownNat 0 k 0 rfl (by simp)

/-- The original left tensor differential is unchanged on every original bidegree. -/
theorem negativeTensorDegreeHom_d₁ (p q n : ℕ) (h : p+q=n+1) :
    mapBifunctor.d₁ P Q (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        negativeTensorDegreeHom P Q n =
      ((negativeTermIso P p).inv ⊗ₘ (negativeTermIso Q q).inv) ≫
        mapBifunctor.d₁ (negativeComplex P) (negativeComplex Q) (curriedTensor _) (ComplexShape.up ℤ)
          (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases p with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero P Q _ _ 0 q n (by simp),zero_comp]
    erw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
    rw [negativeComplex_d_from_zero]
    simp [curriedTensor_map_app]
  | succ p =>
    have hpq : p+q=n := by omega
    rw [mapBifunctor.d₁_eq P Q _ _ (show (ComplexShape.down ℕ).Rel (p+1) p from rfl) q n hpq,
      mapBifunctor.d₁_eq (negativeComplex P) (negativeComplex Q) _ _
        (show (ComplexShape.up ℤ).Rel (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) by change -((p+1 : ℕ) : ℤ)+1= -(p : ℤ); omega)
        (-(q : ℤ)) (-(n : ℤ)) (by change -(p : ℤ)+ -(q : ℤ)= -(n : ℤ); omega)]
    have heN : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p+1,q)=(1 : ℤˣ) := rfl
    have heZ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (-((p+1 : ℕ) : ℤ),-(q : ℤ))=(1 : ℤˣ) := rfl
    rw [heN,heZ,one_smul,one_smul,Category.assoc]
    erw [negativeTensorDegreeHom_inclusion P Q p q n hpq]
    simp only [curriedTensor_map_app,← tensorHom_id,tensorHom_comp_tensorHom_assoc,
      Category.comp_id,Category.id_comp,negativeTermIso_inv_d]

/-- The original right tensor differential retains the same Koszul coefficient under negative extension. -/
theorem negativeTensorDegreeHom_d₂ (p q n : ℕ) (h : p+q=n+1) :
    mapBifunctor.d₂ P Q (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        negativeTensorDegreeHom P Q n =
      ((negativeTermIso P p).inv ⊗ₘ (negativeTermIso Q q).inv) ≫
        mapBifunctor.d₂ (negativeComplex P) (negativeComplex Q) (curriedTensor _) (ComplexShape.up ℤ)
          (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases q with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero P Q _ _ p 0 n (by simp),zero_comp]
    erw [mapBifunctor.d₂_eq' _ _ _ _ (-(p : ℤ)) (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
    rw [negativeComplex_d_from_zero]
    simp [curriedTensor_obj_map]
  | succ q =>
    have hpq : p+q=n := by omega
    rw [mapBifunctor.d₂_eq P Q _ _ p (show (ComplexShape.down ℕ).Rel (q+1) q from rfl) n hpq,
      mapBifunctor.d₂_eq (negativeComplex P) (negativeComplex Q) _ _ (-(p : ℤ))
        (show (ComplexShape.up ℤ).Rel (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) by change -((q+1 : ℕ) : ℤ)+1= -(q : ℤ); omega)
        (-(n : ℤ)) (by change -(p : ℤ)+ -(q : ℤ)= -(n : ℤ); omega)]
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,Category.assoc,
      negativeTensorDegreeHom_inclusion]
    change ((-1 : ℤˣ)^p) • _ = (-(p : ℤ)).negOnePow • _
    rw [Int.negOnePow_neg]
    have hs : (p : ℤ).negOnePow=(-1 : ℤˣ)^p := by
      apply Units.ext
      exact Int.coe_negOnePow_natCast p
    rw [hs]
    congr 1
    simp only [curriedTensor_obj_map,← id_tensorHom,tensorHom_comp_tensorHom_assoc,
      Category.comp_id,Category.id_comp,negativeTermIso_inv_d]

/-- The two independently specified native total differentials commute with the original degree comparison. -/
theorem negativeTensorDegreeHom_d (n : ℕ) :
    (HomologicalComplex.tensorObj P Q).d (n+1) n ≫ negativeTensorDegreeHom P Q n =
      negativeTensorDegreeHom P Q (n+1) ≫
        (HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).d
          (-((n+1 : ℕ) : ℤ)) (-(n : ℤ)) := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=n+1 at h
  rw [← Category.assoc,negativeTensorDegreeHom_inclusion_assoc P Q p q (n+1) h]
  simp only [mapBifunctor.d_eq,Preadditive.comp_add,Preadditive.add_comp,Category.assoc,
    mapBifunctor.ι_D₁_assoc,mapBifunctor.ι_D₂_assoc,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂]
  rw [negativeTensorDegreeHom_d₁ P Q p q n h,negativeTensorDegreeHom_d₂ P Q p q n h]

/-- The native integer tensor restricted to its negative degrees is the original native chain tensor, as a specified chain isomorphism. -/
def negativeTensorRestrictionIso :
    HomologicalComplex.tensorObj P Q ≅
      (HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).restriction
        ComplexShape.embeddingDownNat :=
  Hom.isoOfComponents (negativeTensorDegreeIso P Q) (by
    intro i j h
    have hi : i=j+1 := h.symm
    subst i
    exact (negativeTensorDegreeHom_d P Q j).symm)

end
end BPFixedPoints.SheafTools.BinaryCells
