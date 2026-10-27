import BPFixedPoints.Incidence.VertexProjectiveTwistPolynomialSections
import BPFixedPoints.Incidence.VertexProjectiveTwistHigherCohomology
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity

/-! # Actual cohomology of the original empty vertex product

The degree-zero comparison uses the original frame and polynomial coordinates.
The positive-degree vanishing is the established actual Ext degree bound.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [IsEmpty V]
noncomputable local instance vertexEmptyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual H0 on the original empty vertex product is the original base module. -/
noncomputable def vertexTwistSheafEmptyH0LinearEquiv (a : V → ℤ) :
    letI : Module R ((vertexTwistAbelianSheaf R V a).H 0) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 0
    (vertexTwistAbelianSheaf R V a).H 0 ≃ₗ[R] R := by
  let σ : V → Fin 2 := fun v => isEmptyElim v
  have hU : vertexChartOpen R V σ = ⊤ := by
    rw [vertexChartOpen_eq_coordinateOpen]
    simp only [iInf_of_empty]
  letI := SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 0
  letI := SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) ⊤ 0
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a) ⊤
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a)
    (vertexChartOpen R V σ)
  let e : Γ(vertexTwistSheaf R V a, ⊤) ≃ₗ[R] MvPolynomial V R :=
    (SchemeTools.schemeBaseModuleOpenSectionsCongr (vertexToBase R V) (vertexTwistSheaf R V a) hU.symm).trans
      (vertexTwistSheafChartPolynomialEquiv R V a σ)
  exact (SchemeTools.schemeBaseLocalTopLinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a) 0).symm.trans
    ((SchemeTools.schemeBaseLocalH0LinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a) ⊤).trans
      (e.trans (MvPolynomial.isEmptyAlgEquiv R V).toLinearEquiv))

/-- Every positive actual cohomology group on the original empty product vanishes over a Noetherian base. -/
theorem vertexTwistSheafEmpty_higher_eq_zero [IsNoetherianRing R] (a : V → ℤ) (k : ℕ)
    (x : (vertexTwistAbelianSheaf R V a).H (k+1)) : x = 0 := by
  let P : ℕ → Prop := fun j => ∀ z : (vertexTwistAbelianSheaf R V a).H j, z = 0
  have h : P (Fintype.card V+k+1) := vertexTwistSheaf_higher_cohomology_eq_zero R V a k
  rw [Fintype.card_of_isEmpty, Nat.zero_add] at h
  exact h x

end BPFixedPoints.ProjectiveLine
