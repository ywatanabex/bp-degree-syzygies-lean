import BPFixedPoints.Incidence.IncidenceSheafComparison
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Global sections of genuine affine open embeddings

The coordinate-ring identification uses the structure sheaf's actual maps. Its
naturality compares restriction to a smaller affine open with the original
ring map, without transporting a desired map by definition.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The actual pullback of sections from an open image to its source. -/
noncomputable def openImageSectionsIso : Γ(Y, f.opensRange) ≅ Γ(X, ⊤) :=
  (IsOpenImmersion.ΓIsoTop f).symm

theorem openImageSectionsIso_hom :
    (openImageSectionsIso f).hom = f.appLE f.opensRange ⊤ (by rw [f.preimage_opensRange]) := by
  simp only [openImageSectionsIso, IsOpenImmersion.ΓIsoTop, Iso.symm_hom,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Scheme.Hom.appIso_hom']
  rw [Scheme.Hom.map_appLE]

variable {A B : CommRingCat.{0}} (i : A ⟶ B)
  (fA : Spec A ⟶ Y) (fB : Spec B ⟶ Y) [IsOpenImmersion fA] [IsOpenImmersion fB]
  (hfac : Spec.map i ≫ fA = fB) (hBA : fB.opensRange ≤ fA.opensRange)

/-- Coordinate-ring comparison for the structure sheaf on an actual affine open image. -/
noncomputable def affineOpenSectionsIso (A : CommRingCat.{0})
    (fA : Spec A ⟶ Y) [IsOpenImmersion fA] : Γ(Y, fA.opensRange) ≅ A :=
  openImageSectionsIso fA ≪≫ Scheme.ΓSpecIso A

include hfac in
/-- Restriction between realized affine opens is the prescribed original ring map. -/
theorem affineOpenSectionsIso_naturality :
    Y.presheaf.map (homOfLE hBA).op ≫ (affineOpenSectionsIso B fB).hom =
      (affineOpenSectionsIso A fA).hom ≫ i := by
  subst fB
  simp only [affineOpenSectionsIso, Iso.trans_hom, openImageSectionsIso_hom]
  rw [Scheme.Hom.map_appLE_assoc, Category.assoc, ← Scheme.ΓSpecIso_naturality i,
    ← Category.assoc]
  congr 1

end BPFixedPoints.SheafTools
