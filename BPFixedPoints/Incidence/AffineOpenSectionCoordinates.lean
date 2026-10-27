import BPFixedPoints.Incidence.AffineOpenSections
import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars

/-! # Coordinates on independently specified affine image opens

The open and base action are given geometrically. Coordinate maps retain the
original affine inclusion, ring restrictions and structural morphism.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {X : Scheme.{0}} {A B : CommRingCat.{0}}

/-- Actual affine-image coordinates on a separately specified equal open. -/
noncomputable def affineOpenSectionsIsoAt (A : CommRingCat.{0}) (f : Spec A ⟶ X)
    [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U) : Γ(X, U) ≅ A :=
  X.presheaf.mapIso (eqToIso hU).op ≪≫ affineOpenSectionsIso A f

/-- The original ring restriction is preserved on independently specified image opens. -/
theorem affineOpenSectionsIsoAt_naturality (i : A ⟶ B) (f : Spec A ⟶ X) (g : Spec B ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] (hfg : Spec.map i ≫ f = g)
    (U W : X.Opens) (hU : f.opensRange = U) (hW : g.opensRange = W) (hWU : W ≤ U) :
    X.presheaf.map (homOfLE hWU).op ≫ (affineOpenSectionsIsoAt B g W hW).hom =
      (affineOpenSectionsIsoAt A f U hU).hom ≫ i := by
  subst U
  subst W
  simpa [affineOpenSectionsIsoAt] using affineOpenSectionsIso_naturality i f g hfg hWU

/-- The original affine-image section coordinates preserve a given geometric base map. -/
theorem affineOpenSectionsIsoAt_coefficient {R : Type} [CommRing R] (f : Spec A ⟶ X)
    [IsOpenImmersion f] (U : X.Opens) (hU : f.opensRange = U)
    (p : X ⟶ Spec (CommRingCat.of R)) (i : R →+* A)
    (hi : f ≫ p = Spec.map (CommRingCat.ofHom i)) (r : R) :
    (affineOpenSectionsIsoAt A f U hU).hom (SchemeTools.schemeBaseCoefficientAt p U r) = i r := by
  subst U
  simp only [affineOpenSectionsIsoAt, eqToIso_refl, Iso.op_refl, Functor.mapIso_refl, Iso.refl_trans]
  change (Scheme.ΓSpecIso A).hom
    ((openImageSectionsIso f).hom (SchemeTools.schemeBaseCoefficientAt p f.opensRange r)) = i r
  rw [openImageSectionsIso_hom]
  have hc : f.appLE f.opensRange ⊤ (by rw [f.preimage_opensRange])
      (SchemeTools.schemeBaseCoefficientAt p f.opensRange r) =
        SchemeTools.schemeBaseCoefficientHom (f ≫ p) r := by
    rw [SchemeTools.schemeBaseCoefficientHom_comp]
    dsimp only [SchemeTools.schemeBaseCoefficientAt, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE]
  rw [hc, hi]
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Spec.map (CommRingCat.ofHom i)).appTop) ≫ (Scheme.ΓSpecIso A).hom) r = i r
  rw [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rfl

end BPFixedPoints.SheafTools
