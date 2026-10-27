import BPFixedPoints.Incidence.AffineTildeCohomology
import BPFixedPoints.Incidence.OpenSheafCohomology

/-! # Actual affine open restrictions of quasi-coherent scheme modules

The original scheme-module restriction has exactly the underlying abelian
sheaf of the native naive open pullback. Native quasicoherence under
restriction and affine vanishing therefore imply vanishing of the original
ambient local Ext groups on the actual image open.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The actual scheme-module restriction retains precisely the original abelian restriction. -/
theorem schemeModule_restrict_underlying (M : Y.Modules) :
    (openAbelianSheafRestriction f.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M) =
      (SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f) := rfl

variable (R : CommRingCat.{0}) [IsNoetherianRing R] (j : Spec R ⟶ Y) [IsOpenImmersion j]
noncomputable local instance affineOpenCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) := HasExt.standard _
noncomputable local instance affineOpenSourceCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{0}) := HasExt.standard _

/-- All positive original local Ext groups vanish on a Noetherian affine chart of a quasi-coherent module. -/
theorem affineOpen_quasicoherent_local_cohomology_eq_zero (M : Y.Modules) [M.IsQuasicoherent]
    (n : ℕ) (x : ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).H' (n+1) j.opensRange) : x = 0 := by
  let F := (SheafOfModules.toSheaf Y.ringCatSheaf).obj M
  have hF (k : ℕ)
      (y : Sheaf.H.{1} ((openAbelianSheafRestriction j.isOpenEmbedding).obj F) (k+1)) : y = 0 := by
    change Sheaf.H.{1} ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (M.restrict j)) (k+1) at y
    have := Scheme.Modules.isQuasicoherent_restrictFunctor j M
    exact affineQuasicoherent_global_cohomology_eq_zero R (M.restrict j) k y
  have h := openRestriction_local_cohomology_eq_zero j.isOpenEmbedding n F hF
  have hi : j.isOpenEmbedding.functor.obj ⊤ = j.opensRange := j.image_top_eq_opensRange
  rw [hi] at h
  exact h x

/-- Subsingleton form on the actual affine image, with no local vanishing input assumption. -/
theorem affineOpen_quasicoherent_local_cohomology_subsingleton (M : Y.Modules) [M.IsQuasicoherent]
    (n : ℕ) : Subsingleton (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).H' (n+1) j.opensRange) :=
  subsingleton_of_forall_eq 0 (affineOpen_quasicoherent_local_cohomology_eq_zero R j M n)

end BPFixedPoints.SheafTools
