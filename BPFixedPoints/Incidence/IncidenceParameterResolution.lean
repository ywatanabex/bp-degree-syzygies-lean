import BPFixedPoints.Incidence.IncidenceCoefficientParameters
import BPFixedPoints.Incidence.BaseChangeMinimality

/-! # The incidence coefficient resolution after arbitrary parameter base change -/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

noncomputable local instance coefficientResolutionAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

variable (ha : a ∈ G.incidenceFiniteParameterLocus)
  (B : Type) [CommRing B] [Algebra (MvPolynomial (Fin G.dG) ℂ) B]

/-- The original coefficient resolution remains a resolution after every parameter base change. -/
noncomputable def incidenceParameterBaseChangeResolution :
    letI := G.incidenceCoefficientParameterAlgebra a
    ProjectiveResolution
      (ModuleCat.of (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)
        ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ⊗[IncCoeffRing E] G.IncidenceRing)) := by
  let T := MvPolynomial (Fin G.dG) ℂ
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := G.incidenceParameterAlgebra a
  haveI := G.incidenceCoefficientParameter_tower a
  let mS : ∀ n, Module (IncCoeffRing E) (G.IncFreeTerm n) := fun _ => inferInstance
  let mT : ∀ n, Module T (G.IncFreeTerm n) :=
    fun n => Module.compHom (G.IncFreeTerm n) (algebraMap T (IncCoeffRing E))
  letI : ∀ n, Module T (G.IncFreeTerm n) := mT
  letI : ∀ n, SMul T (G.IncFreeTerm n) := fun n => (mT n).toSMul
  letI : ∀ n, Module (IncCoeffRing E) (G.IncFreeTerm n) := mS
  letI : ∀ n, SMul (IncCoeffRing E) (G.IncFreeTerm n) := fun n => (mS n).toSMul
  haveI : ∀ n, IsScalarTower T (IncCoeffRing E) (G.IncFreeTerm n) := by
    intro n
    constructor
    intro t s m
    change (algebraMap T (IncCoeffRing E) t * s) • m =
      algebraMap T (IncCoeffRing E) t • (s • m)
    exact mul_smul _ _ _
  haveI : Module.Free T (IncCoeffRing E) := G.incidenceCoefficientParameter_free a ha
  haveI : Module.Free T G.IncidenceRing := G.incidenceParameter_free a ha
  haveI : ∀ n, Module.Free T (G.IncFreeTerm n) := fun n =>
    Module.Free.of_basis ((Module.Free.chooseBasis T (IncCoeffRing E)).smulTower (G.incFreeTermBasis n))
  exact coefficientBaseChangeResolution (B := B) G.IncFreeTerm G.incFreeTermDifferential
    G.incFreeTermDifferential_exact G.incResolutionAugmentation
    G.incResolutionAugmentation_surjective G.incFreeTermDifferential_augmentation_exact

@[simp] theorem incidenceParameterBaseChangeResolution_X (n : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (G.incidenceParameterBaseChangeResolution a ha B).complex.X n =
      ModuleCat.of (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)
        ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ⊗[IncCoeffRing E] G.IncFreeTerm n) := rfl

@[simp] theorem incidenceParameterBaseChangeResolution_d (n : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (G.incidenceParameterBaseChangeResolution a ha B).complex.d (n + 1) n =
      ModuleCat.ofHom ((G.incFreeTermDifferential n).baseChange
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) := by
  simp only [incidenceParameterBaseChangeResolution, coefficientBaseChangeResolution_d]

/-- Each changed term has the original state basis, over the changed coefficient ring. -/
noncomputable def incidenceParameterBaseChangeBasis (n : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    Module.Basis {b : G.IncResolutionBasis // G.incResolutionDegree b = n}
      (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)
      ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ⊗[IncCoeffRing E] G.IncFreeTerm n) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact (G.incFreeTermBasis n).baseChange _

include ha in
theorem incidenceParameterBaseChange_exact (n : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    LinearMap.range ((G.incFreeTermDifferential (n + 1)).baseChange
      (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) =
      LinearMap.ker ((G.incFreeTermDifferential n).baseChange
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    ((G.incidenceParameterBaseChangeResolution a ha B).exact_succ n)
  simpa only [G.incidenceParameterBaseChangeResolution_d, ModuleCat.hom_ofHom] using h

end BPFixedPoints.Multigraph
