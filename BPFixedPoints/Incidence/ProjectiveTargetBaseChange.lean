import BPFixedPoints.Incidence.DerivedSpecialization
import BPFixedPoints.Incidence.ResolutionTools
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.Additive
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Base change of a resolution that splits over the parameter ring -/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section Category

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] {M : C} [Projective M] (P : ProjectiveResolution M)

/-- A resolution of a projective object is homotopy equivalent to its augmentation;
every additive functor preserves this particular quasi-isomorphism. -/
theorem map_resolution_augmentation_quasiIso :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) := by
  let e := ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)
  have he : e.hom = P.π := by
    simpa [e, ProjectiveResolution.self] using
      ProjectiveResolution.homotopyEquiv_hom_π P (ProjectiveResolution.self M)
  rw [← he]
  exact (F.mapHomotopyEquiv e).quasiIso_hom

/-- The augmentation and differentials are the images of the original ones. -/
noncomputable def mapResolutionOfProjective
    (hp : ∀ n, Projective (F.obj (P.complex.X n))) :
    ProjectiveResolution (F.obj M) where
  complex := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  projective := hp
  π := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
    (singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app M
  quasiIso := by
    haveI := map_resolution_augmentation_quasiIso F P
    infer_instance

end Category

section Linear

universe u
variable {T B : Type u} [CommRing T] [CommRing B] (f : T →+* B)
  (P : ℕ → Type u) [∀ n, AddCommGroup (P n)] [∀ n, Module T (P n)]
  [∀ n, Module.Free T (P n)]
  (d : ∀ n, P (n + 1) →ₗ[T] P n)
  (hd : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n))
  {M : Type u} [AddCommGroup M] [Module T M] [Module.Projective T M]
  (ε : P 0 →ₗ[T] M) (hεs : Function.Surjective ε)
  (hεe : LinearMap.range (d 0) = LinearMap.ker ε)

/-- Arbitrary base change preserves the given augmented resolution when it splits over T. -/
noncomputable def baseChangeSplitResolution :
    ProjectiveResolution ((ModuleCat.extendScalars f).obj (ModuleCat.of T M)) := by
  let Q := projectiveResolutionOfLinearExact P d hd ε hεs hεe
  haveI : Projective (ModuleCat.of T M) := ModuleCat.projective_of_categoryTheory_projective _
  apply mapResolutionOfProjective (ModuleCat.extendScalars f) Q
  intro n
  letI := f.toAlgebra
  change Projective (ModuleCat.of B (B ⊗[T] P n))
  exact ModuleCat.projective_of_categoryTheory_projective _

include hd hεs hεe in
theorem baseChangeSplitResolution_exact (n : ℕ) :
    letI := f.toAlgebra
    LinearMap.range ((d (n + 1)).baseChange B) = LinearMap.ker ((d n).baseChange B) := by
  letI := f.toAlgebra
  let Q := baseChangeSplitResolution f P d hd ε hεs hεe
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp (Q.exact_succ n)
  simpa only [Q, baseChangeSplitResolution, mapResolutionOfProjective,
    Functor.mapHomologicalComplex_obj_d, projectiveResolutionOfLinearExact,
    projectiveResolutionOfExact,
    linearChainComplex_d, ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
    ModuleCat.ExtendScalars.obj', ModuleCat.hom_ofHom] using h

include hεs hεe in
/-- Exactness at the augmentation is the usual right exactness of tensor product. -/
theorem baseChangeSplitResolution_augmentation_exact :
    letI := f.toAlgebra
    LinearMap.range ((d 0).baseChange B) = LinearMap.ker (ε.baseChange B) := by
  letI := f.toAlgebra
  have he : Function.Exact (d 0) ε := by
    intro x
    change x ∈ LinearMap.ker ε ↔ x ∈ LinearMap.range (d 0)
    rw [hεe]
  have h := lTensor_exact B he hεs
  ext x
  exact (h x).symm

end Linear

end BPFixedPoints.ResolutionTools
