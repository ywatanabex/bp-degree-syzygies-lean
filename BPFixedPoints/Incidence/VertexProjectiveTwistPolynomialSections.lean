import BPFixedPoints.Incidence.VertexProjectiveChartSections
import BPFixedPoints.Incidence.VertexProjectiveTwistChartRestriction

/-! # Original multi-twist chart sections in polynomial coordinates

Both coefficient actions come from the original structural morphism. The frame
equivalence is the evaluation of the specified original chart isomorphism.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

/-- Evaluate the original local frame on an original subopen, retaining its native module action. -/
noncomputable def moduleLocalFrameSectionEquiv (X : Scheme.{0}) (U : X.Opens) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) (hW : W ≤ U) : Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  Iso.toLinearEquiv ((PresheafOfModules.evaluation _ (op (Over.mk (homOfLE hW)))).mapIso
    ((SheafOfModules.forget _).mapIso (moduleOverUnitIso X M U e)))

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {X : Scheme.{0}} {R : Type} [CommRing R]

/-- Equality of original opens retains their independently defined geometric section actions. -/
noncomputable def schemeBaseModuleOpenSectionsCongr
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) {U W : X.Opens} (h : U = W) :
    letI := schemeBaseOpenModuleSections f M U
    letI := schemeBaseOpenModuleSections f M W
    Γ(M, U) ≃ₗ[R] Γ(M, W) := by
  cases h
  letI := schemeBaseOpenModuleSections f M U
  exact LinearEquiv.refl R _

/-- The original local-frame section equivalence preserves the independent geometric base actions. -/
noncomputable def schemeBaseLocalFrameSectionLinearEquiv
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (M : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (W : X.Opens) (hW : W ≤ U) :
    letI := schemeBaseOpenModuleSections f M W
    letI : Module R Γ(X, W) := Module.compHom _ (schemeBaseCoefficientAt f W)
    Γ(M, W) ≃ₗ[R] Γ(X, W) := by
  letI := schemeBaseOpenModuleSections f M W
  letI : Module R Γ(X, W) := Module.compHom _ (schemeBaseCoefficientAt f W)
  exact { (SheafTools.moduleLocalFrameSectionEquiv X U M e W hW).toAddEquiv with
    map_smul' := fun r x => (SheafTools.moduleLocalFrameSectionEquiv X U M e W hW).map_smul
      (schemeBaseCoefficientAt f W r) x }

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- Original ambient chart functions have polynomial coordinates linear over the original base ring. -/
noncomputable def vertexChartSectionsLinearEquiv (σ : V → Fin 2) :
    letI : Module R Γ(vertexScheme R V, vertexChartOpen R V σ) :=
      Module.compHom _ (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ))
    Γ(vertexScheme R V, vertexChartOpen R V σ) ≃ₗ[R] MvPolynomial V R := by
  letI : Module R Γ(vertexScheme R V, vertexChartOpen R V σ) :=
    Module.compHom _ (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ))
  refine { (vertexChartSectionsEquiv R V σ).toAddEquiv with map_smul' := ?_ }
  intro r x
  change vertexChartSectionsEquiv R V σ
    (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ) r * x) = _
  rw [map_mul, vertexChartSectionsEquiv_coefficient, Algebra.smul_def]
  rfl

/-- Actual sections of the original multi-twist on its original chart are polynomial sections over the original base. -/
noncomputable def vertexTwistSheafChartPolynomialEquiv (a : V → ℤ) (σ : V → Fin 2) :
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V)
      (vertexTwistSheaf R V a) (vertexChartOpen R V σ)
    Γ(vertexTwistSheaf R V a, vertexChartOpen R V σ) ≃ₗ[R] MvPolynomial V R := by
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V)
    (vertexTwistSheaf R V a) (vertexChartOpen R V σ)
  letI : Module R Γ(vertexScheme R V, vertexChartOpen R V σ) :=
    Module.compHom _ (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) (vertexChartOpen R V σ))
  exact (SchemeTools.schemeBaseLocalFrameSectionLinearEquiv (vertexToBase R V)
    (vertexChartOpen R V σ) (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a σ)
      (vertexChartOpen R V σ) le_rfl).trans (vertexChartSectionsLinearEquiv R V σ)

/-- The polynomial section map is exactly the original chart-frame coefficient followed by the original coordinates. -/
theorem vertexTwistSheafChartPolynomialEquiv_apply (a : V → ℤ) (σ : V → Fin 2)
    (x : Γ(vertexTwistSheaf R V a, vertexChartOpen R V σ)) :
    vertexTwistSheafChartPolynomialEquiv R V a σ x =
      vertexChartSectionsEquiv R V σ
        (vertexTwistSheafChartCoefficient R V a σ (vertexChartOpen R V σ) le_rfl x) := rfl

end BPFixedPoints.ProjectiveLine
