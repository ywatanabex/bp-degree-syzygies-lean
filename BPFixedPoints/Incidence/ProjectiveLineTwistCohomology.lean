import BPFixedPoints.Incidence.AffineOpenCohomology
import BPFixedPoints.Incidence.ProjectiveLineTwistLocallyFree
import BPFixedPoints.Incidence.ProjectiveLineCanonicalH1
import BPFixedPoints.Incidence.ProjectiveLineTransitionMorphisms
import BPFixedPoints.Incidence.SheafMayerVietorisQuotient
import Mathlib.RingTheory.Localization.Submodule

/-! # Genuine twist cohomology without local vanishing input hypotheses

The actual polynomial and Laurent chart immersions are Noetherian affine.
Native quasicoherence of the original twist therefore gives vanishing of its
original ambient local Ext groups. The canonical Cech comparison then gives
genuine H1, while the native Mayer-Vietoris sequence kills all higher groups.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance actualTwistCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveLine R)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Every positive actual local Ext class of the original twist vanishes on either standard chart. -/
theorem twistSheaf_standard_local_cohomology_eq_zero (d : ℤ) (i : Fin 2) (n : ℕ)
    (x : (twistAbelianSheaf R d).H' (n+1) (standardOpen R i)) : x = 0 := by
  have h := SheafTools.affineOpen_quasicoherent_local_cohomology_eq_zero
    (CommRingCat.of (Polynomial R)) (chartι R i) (twistSheaf R d) n
  rw [chartι_opensRange R i] at h
  exact h x

/-- Native local groups on the two actual standard opens are subsingletons in all positive degrees. -/
theorem twistSheaf_standard_local_cohomology_subsingleton (d : ℤ) (i : Fin 2) (n : ℕ) :
    Subsingleton ((twistAbelianSheaf R d).H' (n+1) (standardOpen R i)) :=
  subsingleton_of_forall_eq 0 (twistSheaf_standard_local_cohomology_eq_zero R d i n)

/-- The original Laurent overlap is Noetherian by Mathlib's localization theorem. -/
theorem laurent_noetherian : IsNoetherianRing (LaurentPolynomial R) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial R))
    (LaurentPolynomial R) inferInstance

/-- Every positive actual local Ext class of the original twist vanishes on the original overlap. -/
theorem twistSheaf_overlap_local_cohomology_eq_zero (d : ℤ) (n : ℕ)
    (x : (twistAbelianSheaf R d).H' (n+1) (standardOpen R 0 ⊓ standardOpen R 1)) : x = 0 := by
  have := laurent_noetherian R
  have h := SheafTools.affineOpen_quasicoherent_local_cohomology_eq_zero
    (CommRingCat.of (LaurentPolynomial R)) (overlapι R) (twistSheaf R d) n
  rw [overlapι_opensRange R, overlapOpen_eq R] at h
  exact h x

/-- Genuine H1 of the actual negative twist is the original state module, with no local vanishing inputs. -/
noncomputable def twistSheafH1Equiv_noetherian (d : ℕ) :
    (twistAbelianSheaf R (-(d : ℤ))).H 1 ≃+ CechLine.H1 R d := by
  have := twistSheaf_standard_local_cohomology_subsingleton R (-(d : ℤ)) 0 0
  have := twistSheaf_standard_local_cohomology_subsingleton R (-(d : ℤ)) 1 0
  exact twistSheafH1Equiv R d

/-- Existence form of the genuine state comparison over a Noetherian base. -/
theorem twistSheafH1_noetherian_comparison (d : ℕ) :
    Nonempty ((twistAbelianSheaf R (-(d : ℤ))).H 1 ≃+ CechLine.H1 R d) :=
  ⟨twistSheafH1Equiv_noetherian R d⟩

/-- The genuine connecting class is sent to the original Laurent coefficient state projection. -/
theorem twistSheafH1Equiv_noetherian_connecting (d : ℕ)
    (z : Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1)) :
    twistSheafH1Equiv_noetherian R d
        (SheafTools.mayerVietorisGlobalConnecting (twistAbelianSheaf R (-(d : ℤ)))
          (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0
          ((SheafTools.localSheafH0Equiv (twistAbelianSheaf R (-(d : ℤ)))
            (standardOpen R 0 ⊓ standardOpen R 1)).symm z)) =
      canonicalCechProjectionOne R d z := by
  have := twistSheaf_standard_local_cohomology_subsingleton R (-(d : ℤ)) 0 0
  have := twistSheaf_standard_local_cohomology_subsingleton R (-(d : ℤ)) 1 0
  have hc : SheafTools.twoOpenSectionGlobalH1Equiv (twistAbelianSheaf R (-(d : ℤ)))
      (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) (QuotientAddGroup.mk z) =
        SheafTools.mayerVietorisGlobalConnecting (twistAbelianSheaf R (-(d : ℤ)))
          (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0
          ((SheafTools.localSheafH0Equiv (twistAbelianSheaf R (-(d : ℤ)))
            (standardOpen R 0 ⊓ standardOpen R 1)).symm z) := rfl
  rw [← hc]
  change canonicalCechH1Equiv R d
    ((SheafTools.twoOpenSectionGlobalH1Equiv (twistAbelianSheaf R (-(d : ℤ)))
      (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R)).symm
        (SheafTools.twoOpenSectionGlobalH1Equiv (twistAbelianSheaf R (-(d : ℤ)))
          (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) (QuotientAddGroup.mk z))) = _
  rw [AddEquiv.symm_apply_apply]
  exact canonicalCechH1Equiv_mk R d z

/-- All genuine cohomology groups of the original integral twist above degree one vanish. -/
theorem twistSheaf_higher_cohomology_eq_zero (d : ℤ) (n : ℕ)
    (x : (twistAbelianSheaf R d).H (n+2)) : x = 0 := by
  let F := twistAbelianSheaf R d
  let U := standardOpen R 0
  let V := standardOpen R 1
  have := twistSheaf_standard_local_cohomology_subsingleton R d 0 (n+1)
  have := twistSheaf_standard_local_cohomology_subsingleton R d 1 (n+1)
  let y := (SheafTools.localSheafTopEquiv F (n+2)).symm x
  have hcover : U ⊔ V = ⊤ := standardOpen_cover R
  have hy : ∃ z : F.H' (n+1) (U ⊓ V),
      (Opens.mayerVietorisSquare U V).δ F (n+1) (n+1+1) rfl z =
        (F.cohomologyPresheaf (n+2)).map (eqToHom hcover).op y :=
    SheafTools.mayerVietoris_delta_surjective F U V (n+1) _
  obtain ⟨z, hz⟩ := hy
  have hz0 : z = 0 := twistSheaf_overlap_local_cohomology_eq_zero R d n z
  rw [hz0, map_zero] at hz
  have hy0 : y = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((F.cohomologyPresheaf (n+2)).map (eqToHom hcover).op)).injective
    rw [map_zero]
    exact hz.symm
  have hx := congrArg (SheafTools.localSheafTopEquiv F (n+2)) hy0
  simpa only [y, AddEquiv.apply_symm_apply, map_zero] using hx

end BPFixedPoints.ProjectiveLine
