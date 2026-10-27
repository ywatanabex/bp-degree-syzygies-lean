import BPFixedPoints.Incidence.ProjectiveLineCechBaseLinearity
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity
import BPFixedPoints.Incidence.ProjectiveLineTwistCohomology

/-! # Geometric base linearity and rank of genuine negative-twist H1

The action on actual cohomology comes from the original structural scalar
endomorphisms, independently of the state comparison. The genuine connecting
map is linear and surjective, and its original state projection is linear.
Thus the existing additive comparison preserves the original base action.
Degree zero is connected to the existing genuine global section comparison
using the native Ext evaluation with the same original coefficient action.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R]
noncomputable local instance twistH1BaseLinearityHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveLine R)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The actual integral-twist cohomology has the original structural coefficient action. -/
@[instance_reducible] noncomputable def twistSheafCohomologyBaseModule (n : ℤ) (k : ℕ) :
    Module R ((twistAbelianSheaf R n).H k) :=
  SchemeTools.schemeBaseCohomologyModule (toSpecBase R) (twistSheaf R n) k

/-- Genuine Ext-defined H0 is the original state module for the independently induced geometric base action. -/
noncomputable def twistSheafH0CohomologyLinearEquiv (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
    (twistAbelianSheaf R (-(d : ℤ))).H 0 ≃ₗ[R] CechLine.H0 R d := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
  letI := twistSheafBaseModule R (-(d : ℤ))
  exact (SchemeTools.schemeBaseH0LinearEquiv (toSpecBase R) (twistSheaf R _)).trans
    (twistSheafGlobalSectionsH0LinearEquiv R d)

/-- Genuine negative-twist H0 is free over the original geometric coefficient ring. -/
theorem twistSheafH0Cohomology_free (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
    Module.Free R ((twistAbelianSheaf R (-(d : ℤ))).H 0) := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
  exact Module.Free.of_equiv (twistSheafH0CohomologyLinearEquiv R d).symm

/-- Genuine negative-twist H0 is finite over the original geometric coefficient ring. -/
theorem twistSheafH0Cohomology_finite (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
    Module.Finite R ((twistAbelianSheaf R (-(d : ℤ))).H 0) := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
  exact Module.Finite.equiv (twistSheafH0CohomologyLinearEquiv R d).symm

/-- Genuine H0 has rank one at d=0 and rank zero otherwise over every nontrivial base. -/
theorem twistSheafH0Cohomology_finrank [Nontrivial R] (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
    Module.finrank R ((twistAbelianSheaf R (-(d : ℤ))).H 0) = if d = 0 then 1 else 0 := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 0
  rw [(twistSheafH0CohomologyLinearEquiv R d).finrank_eq]
  simp only [CechLine.H0, Module.finrank_finsupp_self, CechLine.H0Index, Fintype.card_fin]

/-- The genuine global connecting class of an original overlap section. -/
noncomputable def twistOverlapConnecting (n : ℤ) :
    Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1) →+ (twistAbelianSheaf R n).H 1 :=
  (SheafTools.mayerVietorisGlobalConnecting (twistAbelianSheaf R n)
    (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0).comp
      (SheafTools.localSheafH0Equiv (twistAbelianSheaf R n)
        (standardOpen R 0 ⊓ standardOpen R 1)).symm.toAddMonoidHom

/-- Actual overlap sections and genuine global connecting classes have compatible original base actions. -/
theorem twistOverlapConnecting_smul (n : ℤ) (r : R)
    (s : Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1)) :
    letI := twistOverlapBaseModule R n
    letI := twistSheafCohomologyBaseModule R n 1
    twistOverlapConnecting R n (r • s) = r • twistOverlapConnecting R n s := by
  letI := twistOverlapBaseModule R n
  letI := twistSheafCohomologyBaseModule R n 1
  letI := SchemeTools.schemeBaseLocalCohomologyModule (toSpecBase R) (twistSheaf R n)
    (standardOpen R 0 ⊓ standardOpen R 1) 0
  let e := SchemeTools.schemeBaseLocalH0LinearEquiv (toSpecBase R) (twistSheaf R n)
    (standardOpen R 0 ⊓ standardOpen R 1)
  change SheafTools.mayerVietorisGlobalConnecting (twistAbelianSheaf R n)
      (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0 (e.symm (r • s)) =
    r • SheafTools.mayerVietorisGlobalConnecting (twistAbelianSheaf R n)
      (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0 (e.symm s)
  rw [map_smul]
  exact SchemeTools.schemeBaseGlobalConnecting_smul (toSpecBase R) (twistSheaf R n)
    (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0 r (e.symm s)

variable [IsNoetherianRing R]

/-- Every genuine global H1 class is an actual overlap connecting class. -/
theorem twistOverlapConnecting_surjective (n : ℤ) : Function.Surjective (twistOverlapConnecting R n) := by
  have := twistSheaf_standard_local_cohomology_subsingleton R n 0 0
  have := twistSheaf_standard_local_cohomology_subsingleton R n 1 0
  exact (SheafTools.mayerVietorisGlobalConnecting_surjective (twistAbelianSheaf R n)
    (standardOpen R 0) (standardOpen R 1) (standardOpen_cover R) 0).comp
      (SheafTools.localSheafH0Equiv (twistAbelianSheaf R n)
        (standardOpen R 0 ⊓ standardOpen R 1)).symm.surjective

/-- The genuine overlap connecting class has exactly the original coefficient state projection. -/
theorem twistSheafH1Equiv_overlapConnecting (d : ℕ)
    (s : Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1)) :
    twistSheafH1Equiv_noetherian R d (twistOverlapConnecting R (-(d : ℤ)) s) =
      canonicalCechProjectionOne R d s :=
  twistSheafH1Equiv_noetherian_connecting R d s

/-- The existing genuine H1 comparison preserves the independently defined original geometric coefficient action. -/
theorem twistSheafH1Equiv_base_smul (d : ℕ) (r : R) (x : (twistAbelianSheaf R (-(d : ℤ))).H 1) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    twistSheafH1Equiv_noetherian R d (r • x) = r • twistSheafH1Equiv_noetherian R d x := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
  letI := twistOverlapBaseModule R (-(d : ℤ))
  obtain ⟨s, rfl⟩ := twistOverlapConnecting_surjective R (-(d : ℤ)) x
  rw [← twistOverlapConnecting_smul, twistSheafH1Equiv_overlapConnecting,
    twistSheafH1Equiv_overlapConnecting]
  exact (canonicalCechProjectionOneLinearMap R d).map_smul r s

/-- Genuine global negative-twist H1 is the original state module over the original geometric base. -/
noncomputable def twistSheafH1LinearEquiv (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    (twistAbelianSheaf R (-(d : ℤ))).H 1 ≃ₗ[R] CechLine.H1 R d := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
  exact { twistSheafH1Equiv_noetherian R d with map_smul' := twistSheafH1Equiv_base_smul R d }

/-- The linear equivalence retains the existing genuine additive comparison exactly. -/
theorem twistSheafH1LinearEquiv_apply (d : ℕ) (x : (twistAbelianSheaf R (-(d : ℤ))).H 1) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    twistSheafH1LinearEquiv R d x = twistSheafH1Equiv_noetherian R d x := rfl

/-- Existence form over the independently induced geometric coefficient action. -/
theorem twistSheafH1Linear_comparison (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    Nonempty ((twistAbelianSheaf R (-(d : ℤ))).H 1 ≃ₗ[R] CechLine.H1 R d) :=
  ⟨twistSheafH1LinearEquiv R d⟩

/-- Genuine negative-twist H1 is free for the original geometric coefficient action. -/
theorem twistSheafH1_free (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    Module.Free R ((twistAbelianSheaf R (-(d : ℤ))).H 1) := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
  exact Module.Free.of_equiv (twistSheafH1LinearEquiv R d).symm

/-- Genuine negative-twist H1 is finite for the original geometric coefficient action. -/
theorem twistSheafH1_finite (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    Module.Finite R ((twistAbelianSheaf R (-(d : ℤ))).H 1) := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
  exact Module.Finite.equiv (twistSheafH1LinearEquiv R d).symm

/-- Over a nontrivial original Noetherian base, genuine negative-twist H1 has rank d-1. -/
theorem twistSheafH1_finrank [Nontrivial R] (d : ℕ) :
    letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
    Module.finrank R ((twistAbelianSheaf R (-(d : ℤ))).H 1) = d-1 := by
  letI := twistSheafCohomologyBaseModule R (-(d : ℤ)) 1
  rw [(twistSheafH1LinearEquiv R d).finrank_eq]
  simp only [CechLine.H1, Module.finrank_finsupp_self, CechLine.H1Index, Fintype.card_fin]

end BPFixedPoints.ProjectiveLine
