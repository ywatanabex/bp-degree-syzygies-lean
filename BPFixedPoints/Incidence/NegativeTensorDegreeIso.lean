import BPFixedPoints.Incidence.NativeCochainSingleTensorPairing

/-! # Native tensor degrees commute with Mathlib's negative extension

Both totalizations and the extension are Mathlib's original constructions.
The comparison retains each original bidegree inclusion. Integer bidegrees
outside the image of the negative embedding contribute zero objects.
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
local instance negativeTensorDegreeSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (P Q : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ)

/-- The original native extension identification at its specified negative degree. -/
abbrev negativeTermIso (n : ℕ) :=
  P.extendXIso ComplexShape.embeddingDownNat (by rfl : ComplexShape.embeddingDownNat.f n=-(n : ℤ))

/-- Original natural tensor bidegrees map to the same negative integer tensor bidegrees. -/
def negativeTensorDegreeHom (n : ℕ) :
    (HomologicalComplex.tensorObj P Q).X n ⟶
      (HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).X (-(n : ℤ)) :=
  mapBifunctorDesc (fun p q h =>
    ((negativeTermIso P p).inv ⊗ₘ (negativeTermIso Q q).inv) ≫
      ιTensorObj (negativeComplex P) (negativeComplex Q) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
        (by change p+q=n at h; omega))

/-- The specified comparison preserves every original natural bidegree inclusion. -/
@[reassoc] theorem negativeTensorDegreeHom_inclusion (p q n : ℕ) (h : p+q=n) :
    ιTensorObj P Q p q n h ≫ negativeTensorDegreeHom P Q n =
      ((negativeTermIso P p).inv ⊗ₘ (negativeTermIso Q q).inv) ≫
        ιTensorObj (negativeComplex P) (negativeComplex Q) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
          (by omega) := by
  rw [negativeTensorDegreeHom,ι_mapBifunctorDesc]

/-- The inverse uses the same original bidegrees and vanishes off the image of the negative embedding. -/
def negativeTensorDegreeInv (n : ℕ) :
    (HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj P Q).X n :=
  mapBifunctorDesc (fun p q h => by
    by_cases hp : p≤0
    · by_cases hq : q≤0
      · let a := (-p).toNat
        let b := (-q).toNat
        have ha : ComplexShape.embeddingDownNat.f a=p := by
          change -(a : ℤ)=p
          dsimp [a]
          omega
        have hb : ComplexShape.embeddingDownNat.f b=q := by
          change -(b : ℤ)=q
          dsimp [b]
          omega
        exact ((P.extendXIso _ ha).hom ⊗ₘ (Q.extendXIso _ hb).hom) ≫
          ιTensorObj P Q a b n (by change p+q= -(n : ℤ) at h; dsimp [a,b]; omega)
      · exact 0
    · exact 0)

private theorem negativeTensorSummand_eq (a b p q n : ℕ)
    (ha : ComplexShape.embeddingDownNat.f a= -(p : ℤ))
    (hb : ComplexShape.embeddingDownNat.f b= -(q : ℤ)) (hab : a+b=n) (h : p+q=n) :
    ((P.extendXIso _ ha).hom ⊗ₘ (Q.extendXIso _ hb).hom) ≫ ιTensorObj P Q a b n hab =
      ((negativeTermIso P p).hom ⊗ₘ (negativeTermIso Q q).hom) ≫ ιTensorObj P Q p q n h := by
  have ha' : a=p := by change -(a : ℤ)= -(p : ℤ) at ha; omega
  have hb' : b=q := by change -(b : ℤ)= -(q : ℤ) at hb; omega
  subst a
  subst b
  rfl

/-- Every integer bidegree in the negative embedding has its original inverse coefficient. -/
@[reassoc] theorem negativeTensorDegreeInv_inclusion (p q n : ℕ) (h : p+q=n) :
    ιTensorObj (negativeComplex P) (negativeComplex Q) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) ≫
      negativeTensorDegreeInv P Q n =
        ((negativeTermIso P p).hom ⊗ₘ (negativeTermIso Q q).hom) ≫ ιTensorObj P Q p q n h := by
  rw [negativeTensorDegreeInv,ι_mapBifunctorDesc]
  simp only [dite_true,neg_nonpos.mpr (show (0 : ℤ)≤(p : ℤ) by omega),
    neg_nonpos.mpr (show (0 : ℤ)≤(q : ℤ) by omega),
    neg_neg,Int.toNat_natCast]
  exact negativeTensorSummand_eq P Q _ _ p q n _ _ _ h

/-- The original natural tensor degree is recovered without any sign or permutation. -/
theorem negativeTensorDegreeHom_inv (n : ℕ) :
    negativeTensorDegreeHom P Q n ≫ negativeTensorDegreeInv P Q n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=n at h
  rw [← Category.assoc,negativeTensorDegreeHom_inclusion,Category.assoc,
    negativeTensorDegreeInv_inclusion P Q p q n h]
  simp only [← Category.assoc,tensorHom_comp_tensorHom,Iso.inv_hom_id,tensorHom_id,
    id_whiskerRight,Category.id_comp,Category.comp_id]
  exact Category.id_comp _

/-- The original integer tensor degree is recovered, including its zero bidegrees. -/
theorem negativeTensorDegreeInv_hom (n : ℕ) :
    negativeTensorDegreeInv P Q n ≫ negativeTensorDegreeHom P Q n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q h
  by_cases hp : p≤0
  · by_cases hq : q≤0
    · obtain ⟨a,rfl⟩ : ∃ a : ℕ, -(a : ℤ)=p := ⟨(-p).toNat,by omega⟩
      obtain ⟨b,rfl⟩ : ∃ b : ℕ, -(b : ℤ)=q := ⟨(-q).toNat,by omega⟩
      have hab : a+b=n := by change -(a : ℤ)+ -(b : ℤ)= -(n : ℤ) at h; omega
      rw [← Category.assoc,negativeTensorDegreeInv_inclusion P Q a b n hab,Category.assoc,
        negativeTensorDegreeHom_inclusion]
      simp only [← Category.assoc,tensorHom_comp_tensorHom,Iso.hom_inv_id,tensorHom_id,
        id_whiskerRight,Category.id_comp,Category.comp_id]
      exact Category.id_comp _
    · have hz := (tensorLeft ((negativeComplex P).X p)).map_isZero
        (Q.isZero_extend_X ComplexShape.embeddingDownNat q (by intro k; change -(k : ℤ)≠q; omega))
      exact hz.eq_of_src _ _
  · have hz := (tensorRight ((negativeComplex Q).X q)).map_isZero
      (P.isZero_extend_X ComplexShape.embeddingDownNat p (by intro k; change -(k : ℤ)≠p; omega))
    exact hz.eq_of_src _ _

/-- The specified original tensor degree and the native negative integer tensor degree are isomorphic. -/
def negativeTensorDegreeIso (n : ℕ) :
    (HomologicalComplex.tensorObj P Q).X n ≅
      (HomologicalComplex.tensorObj (negativeComplex P) (negativeComplex Q)).X (-(n : ℤ)) where
  hom := negativeTensorDegreeHom P Q n
  inv := negativeTensorDegreeInv P Q n
  hom_inv_id := negativeTensorDegreeHom_inv P Q n
  inv_hom_id := negativeTensorDegreeInv_hom P Q n

end
end BPFixedPoints.SheafTools.BinaryCells
