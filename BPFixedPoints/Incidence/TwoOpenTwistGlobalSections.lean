import BPFixedPoints.Incidence.TwoOpenTwistGlobalMatching
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Genuine global sections as the original chart-function matching kernel

Mathlib's kernel comparison and the actual chart-pair isomorphism identify
all global sections with all matching chart-function pairs. The comparison
retains the original inclusion and the genuine global structure-ring action.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

/-- The actual pair-coordinate change maps exactly the evaluated sheaf kernel to the original matching kernel. -/
theorem twoOpenChartPairSectionsEquiv_map_ker (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (LinearMap.ker ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op ⊤)).map
      (twoOpenTwistDifference X U V u)).hom).map
        (twoOpenChartPairSectionsEquiv X U V).toLinearMap =
      LinearMap.ker (twoOpenGlobalDifference X U V u) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change twoOpenGlobalDifference X U V u (twoOpenChartPairSectionsEquiv X U V x) = 0
    rw [twoOpenChartPairSectionsEquiv_difference]
    exact hx
  · intro hy
    refine ⟨(twoOpenChartPairSectionsEquiv X U V).symm y, ?_,
      (twoOpenChartPairSectionsEquiv X U V).apply_symm_apply y⟩
    change (twoOpenTwistDifference X U V u).app ⊤
      ((twoOpenChartPairSectionsEquiv X U V).symm y) = 0
    rw [← twoOpenChartPairSectionsEquiv_difference, LinearEquiv.apply_symm_apply]
    exact hy

/-- Genuine global sections equal all original matching chart-function pairs, linearly over actual global scalars. -/
noncomputable def twoOpenTwistGlobalSectionsEquiv (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    Γ(twoOpenTwistModule X U V u, ⊤) ≃ₗ[Γ(X, ⊤)]
      LinearMap.ker (twoOpenGlobalDifference X U V u) :=
  (twoOpenTwistSectionsEquivKer X U V u ⊤).trans
    ((twoOpenChartPairSectionsEquiv X U V).ofSubmodules _ _
      (twoOpenChartPairSectionsEquiv_map_ker X U V u))

/-- The global matching comparison preserves the original inclusion into the actual chart pair. -/
theorem twoOpenTwistGlobalSectionsEquiv_val (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (s : Γ(twoOpenTwistModule X U V u, ⊤)) :
    (twoOpenTwistGlobalSectionsEquiv X U V u s).val =
      twoOpenChartPairSectionsEquiv X U V ((twoOpenTwistInclusion X U V u).app ⊤ s) := by
  have h := ConcreteCategory.congr_hom (twoOpenTwistSectionsIsoKer_hom_subtype X U V u ⊤) s
  change (twoOpenTwistSectionsEquivKer X U V u ⊤ s).val =
    (twoOpenTwistInclusion X U V u).app ⊤ s at h
  change twoOpenChartPairSectionsEquiv X U V (twoOpenTwistSectionsEquivKer X U V u ⊤ s).val = _
  rw [h]

/-- Its left coordinate is the original geometric left projection on actual sections. -/
theorem twoOpenTwistGlobalSectionsEquiv_left (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (s : Γ(twoOpenTwistModule X U V u, ⊤)) :
    (twoOpenTwistGlobalSectionsEquiv X U V u s).val.1 =
      (twoOpenTwistInclusion X U V u ≫ biprod.fst).app ⊤ s := by
  rw [twoOpenTwistGlobalSectionsEquiv_val, twoOpenChartPairSectionsEquiv_fst]
  rfl

/-- Its right coordinate is the original geometric right projection on actual sections. -/
theorem twoOpenTwistGlobalSectionsEquiv_right (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (s : Γ(twoOpenTwistModule X U V u, ⊤)) :
    (twoOpenTwistGlobalSectionsEquiv X U V u s).val.2 =
      (twoOpenTwistInclusion X U V u ≫ biprod.snd).app ⊤ s := by
  rw [twoOpenTwistGlobalSectionsEquiv_val, twoOpenChartPairSectionsEquiv_snd]
  rfl

/-- Existence form of the genuine global matching-kernel comparison over actual global scalars. -/
theorem twoOpenTwistGlobalSections_comparison (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    Nonempty (Γ(twoOpenTwistModule X U V u, ⊤) ≃ₗ[Γ(X, ⊤)]
      LinearMap.ker (twoOpenGlobalDifference X U V u)) :=
  ⟨twoOpenTwistGlobalSectionsEquiv X U V u⟩

end BPFixedPoints.SheafTools
