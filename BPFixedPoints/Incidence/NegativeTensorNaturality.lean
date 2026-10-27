import BPFixedPoints.Incidence.NegativeTensorIso

/-! # Negative tensor comparison preserves the original two input maps

Naturality is checked on the original bidegree inclusions and native
extension term isomorphisms, rather than on cohomology coordinates.
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
local instance negativeTensorNaturalitySmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {P Q P' Q' : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ}
variable (f : P ⟶ P') (g : Q ⟶ Q')

/-- Original maps retain the original native negative term identifications. -/
@[reassoc] theorem negativeMap_term (n : ℕ) :
    (negativeTermIso P n).inv ≫ (negativeMap P f).f (-(n : ℤ)) =
      f.f n ≫ (negativeTermIso P' n).inv := by
  rw [extendMap_f f ComplexShape.embeddingDownNat (by rfl)]
  simp [negativeTermIso,Category.assoc]

private theorem tensorHom_nat_inclusion (p q n : ℕ) (h : p+q=n) :
    ιTensorObj P Q p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj P' Q' p q n h := by
  simpa only [curriedTensor_map_app,curriedTensor_obj_map,MonoidalCategory.tensorHom_def,Category.assoc] using
    (ι_mapBifunctorMap f g (curriedTensor _) (ComplexShape.down ℕ) p q n h)

private theorem tensorHom_int_inclusion
    {K L M N : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ}
    (u : K ⟶ M) (v : L ⟶ N) (p q n : ℤ) (h : p+q=n) :
    ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom u v).f n =
      (u.f p ⊗ₘ v.f q) ≫ ιTensorObj M N p q n h := by
  simpa only [curriedTensor_map_app,curriedTensor_obj_map,MonoidalCategory.tensorHom_def,Category.assoc] using
    (ι_mapBifunctorMap u v (curriedTensor _) (ComplexShape.up ℤ) p q n h)

/-- The original degree comparison commutes with the tensor of the original two input maps. -/
theorem negativeTensorDegreeHom_naturality (n : ℕ) :
    (HomologicalComplex.tensorHom f g).f n ≫ negativeTensorDegreeHom P' Q' n =
      negativeTensorDegreeHom P Q n ≫
        (HomologicalComplex.tensorHom (negativeMap P f) (negativeMap Q g)).f (-(n : ℤ)) := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=n at h
  rw [← Category.assoc,tensorHom_nat_inclusion,Category.assoc,negativeTensorDegreeHom_inclusion,
    negativeTensorDegreeHom_inclusion_assoc P Q p q n h]
  rw [tensorHom_int_inclusion]
  simp only [tensorHom_comp_tensorHom_assoc,negativeMap_term]

/-- The full native negative tensor cochain isomorphism is natural in both original input chain maps. -/
theorem negativeTensorIso_naturality :
    negativeMap (HomologicalComplex.tensorObj P Q) (HomologicalComplex.tensorHom f g) ≫
        (negativeTensorIso P' Q').hom =
      (negativeTensorIso P Q).hom ≫ HomologicalComplex.tensorHom (negativeMap P f) (negativeMap Q g) := by
  ext k : 1
  by_cases hk : k≤0
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, -(n : ℤ)=k := ⟨(-k).toNat,by omega⟩
    apply (cancel_epi (negativeTermIso (HomologicalComplex.tensorObj P Q) n).inv).mp
    simp only [comp_f,Category.assoc]
    rw [negativeMap_term_assoc,negativeTensorIso_hom_component]
    rw [← Category.assoc,negativeTensorIso_hom_component]
    exact negativeTensorDegreeHom_naturality f g n
  · exact ((HomologicalComplex.tensorObj P Q).isZero_extend_X ComplexShape.embeddingDownNat k
      (by intro n; change -(n : ℤ)≠k; omega)).eq_of_src _ _

end
end BPFixedPoints.SheafTools.BinaryCells
