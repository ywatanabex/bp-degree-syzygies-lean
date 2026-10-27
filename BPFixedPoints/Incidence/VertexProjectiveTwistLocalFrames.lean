import BPFixedPoints.Incidence.SchemeModulePullbackFrames
import BPFixedPoints.Incidence.SchemeModuleTensorLocalFrames
import BPFixedPoints.Incidence.VertexProjectiveTwistSheaf
import BPFixedPoints.Incidence.ProjectiveProductChartImages
import BPFixedPoints.Incidence.ProjectiveLineTwistLocallyFree

/-! # Rank-one frames of the actual vertex multi-twist

Each original factor frame is pulled back by the original vertex projection
on every original product chart. Native tensor sheafification preserves
these rank-one frames, including the empty product. The original multi-face
transition formula and the derived-cohomology comparison are further properties.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The original rank-one frame on either of the two native standard opens. -/
noncomputable def twistSheafStandardIso (n : ℤ) (i : Fin 2) :
    (twistSheaf R n).restrict (standardOpen R i).ι ≅
      SheafOfModules.unit (standardOpen R i).toScheme.ringCatSheaf := by
  refine Fin.cases (twistSheafLeftIso R n) (fun j => ?_) i
  exact Fin.cases (twistSheafRightIso R n) (fun k => Fin.elim0 k) j

/-- The original vertex projection on a product chart factors through its prescribed standard open. -/
noncomputable def vertexChartOpenProjectionLift (σ : V → Fin 2) (v : V) :
    (vertexChartOpen R V σ).toScheme ⟶ (standardOpen R (σ v)).toScheme :=
  IsOpenImmersion.lift (standardOpen R (σ v)).ι
    ((vertexChartOpen R V σ).ι ≫ (vertexProjectionOver R V v).left) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (mem_vertexChartOpen R V σ x.1).mp x.2 v)

/-- The actual chart factorization recovers the original vertex projection. -/
@[reassoc] theorem vertexChartOpenProjectionLift_fac (σ : V → Fin 2) (v : V) :
    vertexChartOpenProjectionLift R V σ v ≫ (standardOpen R (σ v)).ι =
      (vertexChartOpen R V σ).ι ≫ (vertexProjectionOver R V v).left :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original factor twist has a genuine rank-one frame on every original product chart. -/
noncomputable def vertexTwistFactorChartIso (a : V → ℤ) (σ : V → Fin 2) (v : V) :
    ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj
      (twistSheaf R (a v))).restrict (vertexChartOpen R V σ).ι ≅
        SheafOfModules.unit (vertexChartOpen R V σ).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (vertexChartOpen R V σ).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (vertexChartOpen R V σ).ι
      (vertexProjectionOver R V v).left).app _ ≪≫
    SheafTools.modulePullbackLocalUnitIso _ _ _ (twistSheafStandardIso R (a v) (σ v))
      (vertexChartOpenProjectionLift R V σ v) (vertexChartOpenProjectionLift_fac R V σ v)

/-- The original vertex-labelled polynomial chart images cover the native terminal open. -/
theorem vertexChartOpens_coversTop :
    (Opens.grothendieckTopology (vertexScheme R V)).CoversTop
      (vertexChartOpen R V) := by
  intro W x hx
  obtain ⟨σ, y, hy⟩ := vertexChart_covers R V x
  have hσ : x ∈ vertexChartOpen R V σ := ⟨y, hy⟩
  exact ⟨W ⊓ vertexChartOpen R V σ, homOfLE inf_le_left,
    ⟨σ, ⟨homOfLE inf_le_right⟩⟩, hx, hσ⟩

/-- Original product-chart frames give native one-generator data for each pulled-back factor. -/
noncomputable def vertexTwistFactorLocalGenerators (a : V → ℤ) (v : V) :
    ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj
      (twistSheaf R (a v))).LocalGeneratorsData where
  I := V → Fin 2
  X := vertexChartOpen R V
  coversTop := vertexChartOpens_coversTop R V
  generators σ := SheafTools.localUnitGeneratingSections _ _ _ (vertexTwistFactorChartIso R V a σ v)

/-- Each original factor presentation is an actual isomorphism. -/
instance vertexTwistFactorLocalGenerators_isLocallyFreeData (a : V → ℤ) (v : V) :
    (vertexTwistFactorLocalGenerators R V a v).IsLocallyFreeData where
  isIso σ := by
    change IsIso (SheafTools.localUnitGeneratingSections _ _ _
      (vertexTwistFactorChartIso R V a σ v)).π
    exact SheafTools.localUnitGeneratingSections_isIso _ _ _ _

/-- Each original projection pullback of an integral twist is natively locally free. -/
instance vertexTwistFactor_isLocallyFree (a : V → ℤ) (v : V) :
    ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj
      (twistSheaf R (a v))).IsLocallyFree :=
  (vertexTwistFactorLocalGenerators R V a v).isLocallyFree

/-- Native local freeness supplies quasicoherence of the original factor pullback. -/
instance vertexTwistFactor_isQuasicoherent (a : V → ℤ) (v : V) :
    ((Scheme.Modules.pullback (vertexProjectionOver R V v).left).obj
      (twistSheaf R (a v))).IsQuasicoherent := by infer_instance

/-- Every original product chart is a rank-one chart for the actual integral multi-twist. -/
noncomputable def vertexTwistSheafChartIso (a : V → ℤ) (σ : V → Fin 2) :
    (vertexTwistSheaf R V a).restrict (vertexChartOpen R V σ).ι ≅
      SheafOfModules.unit (vertexChartOpen R V σ).toScheme.ringCatSheaf :=
  SheafTools.moduleTensorFamilyLocalUnitIso (vertexScheme R V) (vertexChartOpen R V σ)
    (Fintype.card V) (vertexPullbackModuleFamily R V (fun v => twistSheaf R (a v)))
      (fun i => vertexTwistFactorChartIso R V a σ ((Fintype.equivFin V).symm i))

/-- Original product-chart frames give native one-generator data for the actual multi-twist. -/
noncomputable def vertexTwistSheafLocalGenerators (a : V → ℤ) :
    (vertexTwistSheaf R V a).LocalGeneratorsData where
  I := V → Fin 2
  X := vertexChartOpen R V
  coversTop := vertexChartOpens_coversTop R V
  generators σ := SheafTools.localUnitGeneratingSections _ _ _ (vertexTwistSheafChartIso R V a σ)

/-- Every specified original multi-twist chart presentation is an actual isomorphism. -/
instance vertexTwistSheafLocalGenerators_isLocallyFreeData (a : V → ℤ) :
    (vertexTwistSheafLocalGenerators R V a).IsLocallyFreeData where
  isIso σ := by
    change IsIso (SheafTools.localUnitGeneratingSections _ _ _
      (vertexTwistSheafChartIso R V a σ)).π
    exact SheafTools.localUnitGeneratingSections_isIso _ _ _ _

/-- The actual integral multi-twist is locally free on the original projective product. -/
instance vertexTwistSheaf_isLocallyFree (a : V → ℤ) :
    (vertexTwistSheaf R V a).IsLocallyFree :=
  (vertexTwistSheafLocalGenerators R V a).isLocallyFree

/-- The actual integral multi-twist is quasicoherent by Mathlib's native theorem. -/
instance vertexTwistSheaf_isQuasicoherent (a : V → ℤ) :
    (vertexTwistSheaf R V a).IsQuasicoherent := by infer_instance

end BPFixedPoints.ProjectiveLine
