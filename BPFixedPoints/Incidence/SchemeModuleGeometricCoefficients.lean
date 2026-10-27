import BPFixedPoints.Incidence.SchemeModuleFrameScalars
import BPFixedPoints.Incidence.AffineOpenSectionCoordinates

/-! # Original over-site scalar coefficients as geometric restrictions -/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (X : Scheme.{0}) (U : X.Opens)

/-- The original multiplication coefficient commutes with every native over-site restriction. -/
theorem moduleOverMultiplicationCoefficient_naturality (r : Γ(U.toScheme, ⊤))
    {S T : Over U} (i : S ⟶ T) :
    X.presheaf.map i.left.op (moduleOverMultiplicationCoefficient X U r T) =
      moduleOverMultiplicationCoefficient X U r S := by
  have h := (moduleOverMultiplication X U r).val.naturality i.op
  have hh := congrArg (fun f => f.hom (1 : Γ(X, T.left))) h
  change ((moduleOverMultiplication X U r).val.app (op S)).hom
    (X.presheaf.map i.left.op (1 : Γ(X, T.left))) =
      X.presheaf.map i.left.op (((moduleOverMultiplication X U r).val.app (op T)).hom
        (1 : Γ(X, T.left))) at hh
  rw [map_one] at hh
  exact hh.symm

/-- Evaluation on the native image of the whole open gives the original geometric scalar. -/
theorem moduleOverMultiplicationCoefficient_imageTop (r : Γ(U.toScheme, ⊤)) :
    moduleOverMultiplicationCoefficient X U r ((Opens.overEquivalence U).inverse.obj ⊤) = r := by
  have h := moduleOverMultiplication_map X U r
  have hh := congrArg (fun f => f.app ⊤ (1 : Γ(U.toScheme, ⊤))) h
  change (show Γ(U.toScheme, ⊤) from
    ((moduleOverMultiplication X U r).val.app
      (op ((Opens.overEquivalence U).inverse.obj ⊤))).hom (1 : Γ(U.toScheme, ⊤))) = _ at hh
  change moduleOverMultiplicationCoefficient X U r ((Opens.overEquivalence U).inverse.obj ⊤) =
    (unitGlobalMultiplication U.toScheme r).val.app (op ⊤) (1 : Γ(U.toScheme, ⊤)) at hh
  exact hh.trans (unitGlobalMultiplication_top_one U.toScheme r)

/-- The native over-site scalar coefficient is the ordinary original geometric restriction. -/
theorem moduleOverMultiplicationCoefficient_geometric (r : Γ(U.toScheme, ⊤)) (S : Over U) :
    moduleOverMultiplicationCoefficient X U r S =
      X.presheaf.map S.hom.op (U.topIso.hom r) := by
  let T := (Opens.overEquivalence U).inverse.obj ⊤
  have hST : S.left ≤ T.left := by
    change S.left ≤ U.ι ''ᵁ ⊤
    rw [U.ι_image_top]
    exact S.hom.le
  let i : S ⟶ T := Over.homMk (homOfLE hST)
  have hh := (moduleOverMultiplicationCoefficient_naturality X U r i).symm
  rw [moduleOverMultiplicationCoefficient_imageTop] at hh
  refine hh.trans ?_
  change X.presheaf.map (homOfLE hST).op r = X.presheaf.map S.hom.op (U.topIso.hom r)
  change _ = X.presheaf.map S.hom.op (X.presheaf.map (eqToHom U.ι_image_top.symm).op r)
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Affine coordinates on a specified open are the actual affine pullback followed by Gamma--Spec. -/
theorem affineOpenSectionsIsoAt_hom {A : CommRingCat.{0}} (f : Spec A ⟶ X)
    [IsOpenImmersion f] (W : X.Opens) (hW : f.opensRange = W) :
    (affineOpenSectionsIsoAt A f W hW).hom =
      f.appLE W ⊤ (by rw [← hW, f.preimage_opensRange]) ≫ (Scheme.ΓSpecIso A).hom := by
  subst W
  simp [affineOpenSectionsIsoAt, affineOpenSectionsIso, openImageSectionsIso_hom]

/-- Native multiplication coefficients retain the actual factorization through the original open. -/
theorem affineOpenSectionsIsoAt_multiplication {A : CommRingCat.{0}} (f : Spec A ⟶ X)
    [IsOpenImmersion f] (W : X.Opens) (hW : f.opensRange = W) (hWU : W ≤ U)
    (g : Spec A ⟶ U.toScheme) (hg : g ≫ U.ι = f) (r : Γ(U.toScheme, ⊤)) :
    (affineOpenSectionsIsoAt A f W hW).hom
      (moduleOverMultiplicationCoefficient X U r (Over.mk (homOfLE hWU))) =
        (Scheme.ΓSpecIso A).hom (g.appTop r) := by
  have he : U.topIso.hom ≫ f.appLE U ⊤ (by
      rw [← hg, Scheme.Hom.comp_preimage]
      simp) = g.appTop := by
    simp only [← hg]
    rw [← Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ U.ι_preimage_self.ge (by simp)]
    rw [Scheme.Opens.ι_appLE]
    rw [← Category.assoc, Scheme.Opens.topIso_hom, ← X.presheaf.map_comp]
    simp [Scheme.Hom.appLE]
    exact (congrArg (fun k => k ≫ g.appTop)
      (X.presheaf.map_id (op (U.ι ''ᵁ ⊤)))).trans (Category.id_comp _)
  rw [affineOpenSectionsIsoAt_hom, moduleOverMultiplicationCoefficient_geometric]
  change (U.topIso.hom ≫ X.presheaf.map (homOfLE hWU).op ≫ f.appLE W ⊤ _ ≫
    (Scheme.ΓSpecIso A).hom) r = _
  rw [Scheme.Hom.map_appLE_assoc, ← Category.assoc, he]
  rfl

end BPFixedPoints.SheafTools
