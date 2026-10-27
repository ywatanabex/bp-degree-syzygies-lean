import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Global section coordinates induced by genuine affine scheme isomorphisms

The naturality lemma retains the original affine ring map. It is a direct
application of Mathlib's global-sections functor and Gamma-Spec naturality.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} {A B : CommRingCat}

/-- Actual global sections in the coordinates of a specified affine scheme isomorphism. -/
noncomputable def affineIsoSectionsIso (e : X ≅ Spec A) : Γ(X, ⊤) ≅ A :=
  (Scheme.Γ.mapIso e.op).symm ≪≫ Scheme.ΓSpecIso A

theorem affineIsoSectionsIso_hom (e : X ≅ Spec A) :
    (affineIsoSectionsIso e).hom = e.inv.appTop ≫ (Scheme.ΓSpecIso A).hom := rfl

/-- The actual affine global-section coordinates preserve a given genuine geometric ring map. -/
theorem affineIsoSectionsIso_naturality (eX : X ≅ Spec A) (eY : Y ≅ Spec B)
    (f : X ⟶ Y) (i : B ⟶ A) (he : f ≫ eY.hom = eX.hom ≫ Spec.map i) :
    f.appTop ≫ (affineIsoSectionsIso eX).hom = (affineIsoSectionsIso eY).hom ≫ i := by
  have h := congrArg (fun k => k.appTop) he
  simp only [Scheme.Hom.comp_appTop] at h
  have heX : eX.hom.appTop ≫ eX.inv.appTop = 𝟙 _ := (Scheme.Γ.mapIso eX.op).hom_inv_id
  have heY : eY.hom.appTop ≫ eY.inv.appTop = 𝟙 _ := (Scheme.Γ.mapIso eY.op).hom_inv_id
  rw [affineIsoSectionsIso_hom, affineIsoSectionsIso_hom]
  apply (cancel_epi eY.hom.appTop).mp
  calc
    _ = ((eY.hom.appTop ≫ f.appTop) ≫ eX.inv.appTop) ≫ (Scheme.ΓSpecIso A).hom := by
      simp only [Category.assoc]
    _ = ((Spec.map i).appTop ≫ eX.hom.appTop ≫ eX.inv.appTop) ≫ (Scheme.ΓSpecIso A).hom := by
      rw [h]
      simp only [Category.assoc]
    _ = (Scheme.ΓSpecIso B).hom ≫ i := by
      rw [heX, Category.comp_id, Scheme.ΓSpecIso_naturality]
    _ = _ := by
      simp only [← Category.assoc, heY, Category.id_comp]

end BPFixedPoints.SchemeTools
