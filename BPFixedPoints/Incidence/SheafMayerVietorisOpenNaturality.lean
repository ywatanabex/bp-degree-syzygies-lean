import BPFixedPoints.Incidence.SheafInjectiveFlasque
import BPFixedPoints.Incidence.SheafMayerVietorisQuotient

/-! # Native Mayer--Vietoris connecting maps commute with open restrictions -/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T]
noncomputable local instance mvOpenNaturalityHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (S Q : (Opens.grothendieckTopology T).MayerVietorisSquare)

/-- Actual inclusions of the four opens give the native map of free-sheaf resolutions. -/
noncomputable def mayerVietorisOpenShortComplexMap
    (i₁ : S.X₁ ⟶ Q.X₁) (i₂ : S.X₂ ⟶ Q.X₂)
    (i₃ : S.X₃ ⟶ Q.X₃) (i₄ : S.X₄ ⟶ Q.X₄) : S.shortComplex ⟶ Q.shortComplex where
  τ₁ := freeOpenAbelianSheaf.map i₁
  τ₂ := biprod.map (freeOpenAbelianSheaf.map i₂) (freeOpenAbelianSheaf.map i₃)
  τ₃ := freeOpenAbelianSheaf.map i₄
  comm₁₂ := by
    change freeOpenAbelianSheaf.map i₁ ≫
        biprod.lift (freeOpenAbelianSheaf.map Q.f₁₂) (-freeOpenAbelianSheaf.map Q.f₁₃) =
      biprod.lift (freeOpenAbelianSheaf.map S.f₁₂) (-freeOpenAbelianSheaf.map S.f₁₃) ≫
        biprod.map (freeOpenAbelianSheaf.map i₂) (freeOpenAbelianSheaf.map i₃)
    apply biprod.hom_ext <;> simp only [Category.assoc,
      biprod.lift_fst, biprod.lift_snd, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, Preadditive.neg_comp, Preadditive.comp_neg,
      ← Functor.map_comp]
    all_goals congr 1
  comm₂₃ := by
    change biprod.map (freeOpenAbelianSheaf.map i₂) (freeOpenAbelianSheaf.map i₃) ≫
        biprod.desc (freeOpenAbelianSheaf.map Q.f₂₄) (freeOpenAbelianSheaf.map Q.f₃₄) =
      biprod.desc (freeOpenAbelianSheaf.map S.f₂₄) (freeOpenAbelianSheaf.map S.f₃₄) ≫
        freeOpenAbelianSheaf.map i₄
    apply biprod.hom_ext' <;> simp only [
      biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_map_assoc, biprod.inr_map_assoc, biprod.inl_desc, biprod.inr_desc,
      ← Functor.map_comp]
    all_goals congr 1

/-- The native connecting homomorphism commutes with every inclusion of Mayer--Vietoris opens. -/
theorem mayerVietoris_delta_open_naturality
    (i₁ : S.X₁ ⟶ Q.X₁) (i₂ : S.X₂ ⟶ Q.X₂)
    (i₃ : S.X₃ ⟶ Q.X₃) (i₄ : S.X₄ ⟶ Q.X₄)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (n : ℕ) (x : F.H' n Q.X₁) :
    S.δ F n (n+1) rfl ((F.cohomologyPresheaf n).map i₁.op x) =
      (F.cohomologyPresheaf (n+1)).map i₄.op (Q.δ F n (n+1) rfl x) := by
  let φ := mayerVietorisOpenShortComplexMap S Q i₁ i₂ i₃ i₄
  have h := ShortComplex.ShortExact.extClass_naturality
    S.shortComplex_shortExact Q.shortComplex_shortExact φ
  change S.shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ φ.τ₁).comp x (zero_add n)) (by omega) =
    (Ext.mk₀ φ.τ₃).comp
      (Q.shortComplex_shortExact.extClass.comp x (by omega)) (zero_add (n+1))
  rw [← Ext.comp_assoc_of_second_deg_zero _ _ _ (show 1+n = n+1 by omega), h,
    Ext.comp_assoc _ _ _ (zero_add 1) (show 1+n = n+1 by omega) (by omega)]

end BPFixedPoints.SheafTools
