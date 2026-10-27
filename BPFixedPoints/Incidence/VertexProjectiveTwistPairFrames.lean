import BPFixedPoints.Incidence.SchemeModulePullbackTransitions
import BPFixedPoints.Incidence.SchemeModuleTensorFrameTransitions
import BPFixedPoints.Incidence.ProjectiveLineTwistPairFrames
import BPFixedPoints.Incidence.VertexProjectiveTwistLocalFrames

/-! # Original factor transitions on the actual product-chart intersections

The original scheme modules, structure-ring maps and native comparisons are used.
Comparison with the coefficient face atlas and derived cohomology is separate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]
variable (V : Type) [Fintype V]

/-- The actual intersection of the two original vertex-labelled polynomial chart images. -/
noncomputable def vertexChartPairOpen (σ τ : V → Fin 2) : (vertexScheme R V).Opens :=
  vertexChartOpen R V σ ⊓ vertexChartOpen R V τ

/-- The original vertex projection factors through the actual common standard factor open. -/
noncomputable def vertexChartPairProjectionLift (σ τ : V → Fin 2) (v : V) :
    (vertexChartPairOpen R V σ τ).toScheme ⟶ (standardPairOpen R (σ v) (τ v)).toScheme :=
  IsOpenImmersion.lift (standardPairOpen R (σ v) (τ v)).ι
    ((vertexChartPairOpen R V σ τ).ι ≫ (vertexProjectionOver R V v).left) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact mem_standardPairOpen R (σ v) (τ v) _
        ((mem_vertexChartOpen R V σ x.1).mp x.2.1 v)
        ((mem_vertexChartOpen R V τ x.1).mp x.2.2 v))

/-- The pair-overlap factorization recovers the original vertex projection. -/
@[reassoc] theorem vertexChartPairProjectionLift_fac (σ τ : V → Fin 2) (v : V) :
    vertexChartPairProjectionLift R V σ τ v ≫ (standardPairOpen R (σ v) (τ v)).ι =
      (vertexChartPairOpen R V σ τ).ι ≫ (vertexProjectionOver R V v).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original factor frame pulled back to the actual product-chart intersection. -/
noncomputable def vertexTwistPairFactorIso (a : V → ℤ) (σ τ : V → Fin 2) (v : V) (right : Bool) :
    ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj
      (twistSheaf R (a v))).restrict (vertexChartPairOpen R V σ τ).ι ≅
        SheafOfModules.unit (vertexChartPairOpen R V σ τ).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (vertexChartPairOpen R V σ τ).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (vertexChartPairOpen R V σ τ).ι
      (vertexProjectionOver R V v).left).app _ ≪≫
    SheafTools.modulePullbackLocalUnitIso _ _ _ (twistSheafPairIso R (a v) (σ v) (τ v) right)
      (vertexChartPairProjectionLift R V σ τ v) (vertexChartPairProjectionLift_fac R V σ τ v)

/-- The original Laurent pair transition pulled back by the actual vertex projection. -/
noncomputable def vertexTwistPairFactorUnit (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)ˣ :=
  Units.map ((vertexChartPairProjectionLift R V σ τ v).appTop).hom.toMonoidHom
    (twistSheafPairUnit R (a v) (σ v) (τ v))

/-- The actual original factor overlap frames retain the original pulled-back transition function. -/
theorem vertexTwistPairFactorIso_transition (a : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    (vertexTwistPairFactorIso R V a σ τ v false).hom =
      (vertexTwistPairFactorIso R V a σ τ v true).hom ≫
        SheafTools.unitGlobalMultiplication (vertexChartPairOpen R V σ τ).toScheme
          (vertexTwistPairFactorUnit R V a σ τ v : Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)) := by
  have h := SheafTools.modulePullbackLocalUnitIso_transition
    ((vertexChartPairOpen R V σ τ).ι ≫ (vertexProjectionOver R V v).left)
    (standardPairOpen R (σ v) (τ v)) (twistSheaf R (a v))
    (twistSheafPairIso R (a v) (σ v) (τ v) false) (twistSheafPairIso R (a v) (σ v) (τ v) true)
    (vertexChartPairProjectionLift R V σ τ v) (vertexChartPairProjectionLift_fac R V σ τ v)
    (twistSheafPairUnit R (a v) (σ v) (τ v) : Γ((standardPairOpen R (σ v) (τ v)).toScheme, ⊤))
    (twistSheafPairIso_transition R (a v) (σ v) (τ v))
  dsimp only [vertexTwistPairFactorIso, Iso.trans_hom]
  rw [h]
  simp only [Category.assoc]
  rfl

/-- The actual multi-twist frame on the original pair intersection, from all original factor frames. -/
noncomputable def vertexTwistSheafPairIso (a : V → ℤ) (σ τ : V → Fin 2) (right : Bool) :
    (vertexTwistSheaf R V a).restrict (vertexChartPairOpen R V σ τ).ι ≅
      SheafOfModules.unit (vertexChartPairOpen R V σ τ).toScheme.ringCatSheaf :=
  SheafTools.moduleTensorFamilyLocalUnitIso (vertexScheme R V) (vertexChartPairOpen R V σ τ)
    (Fintype.card V) (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)))
      (fun i => vertexTwistPairFactorIso R V a σ τ ((Fintype.equivFin V).symm i) right)

/-- The product of the original vertex-labelled geometric transition units on the actual pair intersection. -/
noncomputable def vertexTwistSheafPairUnit (a : V → ℤ) (σ τ : V → Fin 2) :
    Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)ˣ :=
  ∏ v, vertexTwistPairFactorUnit R V a σ τ v

/-- The actual multi-twist overlap frames differ by the product of the original pulled-back Laurent units. -/
theorem vertexTwistSheafPairIso_transition (a : V → ℤ) (σ τ : V → Fin 2) :
    (vertexTwistSheafPairIso R V a σ τ false).hom =
      (vertexTwistSheafPairIso R V a σ τ true).hom ≫
        SheafTools.unitGlobalMultiplication (vertexChartPairOpen R V σ τ).toScheme
          (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)) := by
  have h := SheafTools.moduleTensorFamilyLocalUnitIso_transition
    (vertexScheme R V) (vertexChartPairOpen R V σ τ) (Fintype.card V)
    (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)))
    (fun i => vertexTwistPairFactorIso R V a σ τ ((Fintype.equivFin V).symm i) false)
    (fun i => vertexTwistPairFactorIso R V a σ τ ((Fintype.equivFin V).symm i) true)
    (fun i => (vertexTwistPairFactorUnit R V a σ τ ((Fintype.equivFin V).symm i) :
      Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)))
    (fun i => vertexTwistPairFactorIso_transition R V a σ τ ((Fintype.equivFin V).symm i))
  have hp : (∏ i : Fin (Fintype.card V),
      (vertexTwistPairFactorUnit R V a σ τ ((Fintype.equivFin V).symm i) :
        Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤))) =
      (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤)) := by
    change (∏ i : Fin (Fintype.card V),
      (vertexTwistPairFactorUnit R V a σ τ ((Fintype.equivFin V).symm i) :
        Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤))) =
      ↑(∏ v, vertexTwistPairFactorUnit R V a σ τ v)
    rw [Units.coe_prod]
    exact Fintype.prod_equiv (Fintype.equivFin V).symm _ _ (fun _ => rfl)
  exact h.trans (congrArg (fun r => (vertexTwistSheafPairIso R V a σ τ true).hom ≫
    SheafTools.unitGlobalMultiplication (vertexChartPairOpen R V σ τ).toScheme r) hp)

end BPFixedPoints.ProjectiveLine
