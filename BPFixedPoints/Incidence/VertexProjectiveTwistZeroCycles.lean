import BPFixedPoints.Incidence.CechZeroStatePiece
import BPFixedPoints.Incidence.CechTwistChartMatching
import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDifferences
import BPFixedPoints.Incidence.SchemeModuleOpenRestrictions
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Actual global twist sections and the original degree-zero cocycles -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original Boolean chart-face opens cover the original vertex product. -/
theorem vertexBooleanFaceOpens_cover :
    (⊤ : (vertexScheme R V).Opens) ≤
      ⨆ σ : V → Bool, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ) := by
  intro x _
  obtain ⟨σ,y,hy⟩ := vertexChart_covers R V x
  let τ : V → Bool := fun v => decide (σ v = 1)
  have hτ : vertexBooleanPivot V τ = σ := by
    funext v
    generalize hv : σ v = i
    fin_cases i <;> simp [vertexBooleanPivot,τ,hv]
  apply Opens.mem_iSup.mpr
  refine ⟨τ,?_⟩
  rw [← vertexFaceι_opensRange R V,vertexFaceι_chart_opensRange,hτ]
  exact ⟨y,hy⟩

/-- The independently defined original geometric base action on actual global twist sections. -/
noncomputable def vertexTwistGlobalSectionModule (a : V → ℤ) : ModuleCat R :=
  SchemeTools.schemeBaseOpenSectionModule (vertexToBase R V) (vertexTwistSheaf R V a) ⊤

/-- Original canonical chart coefficients of actual global sections, using native restrictions. -/
noncomputable def vertexTwistGlobalChartCoordinates (a : V → ℤ) :
    vertexTwistGlobalSectionModule R V a →ₗ[R] ((σ : V → Bool) → FaceRing R (chartFace σ)) := by
  apply LinearMap.pi
  intro σ
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a)
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ))
  exact (vertexTwistSheafFaceSectionsEquiv R V a (chartFace σ)).toLinearMap.comp
    (SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R V) (vertexTwistSheaf R V a)
      (homOfLE le_top))

/-- Global chart coordinates evaluate the actual restriction and the original specified frame. -/
theorem vertexTwistGlobalChartCoordinates_apply (a : V → ℤ)
    (s : vertexTwistGlobalSectionModule R V a) (σ : V → Bool) :
    vertexTwistGlobalChartCoordinates R V a s σ = vertexTwistSheafFaceSectionsEquiv R V a (chartFace σ)
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE le_top).op s) := rfl

/-- Include actual chart restrictions as original degree-zero coefficient chains. -/
noncomputable def vertexTwistGlobalZeroChain (a : V → ℤ) :
    vertexTwistGlobalSectionModule R V a →ₗ[R] C R V :=
  (zeroCharts R).comp (vertexTwistGlobalChartCoordinates R V a)

/-- Global restrictions give cocycles for the original differential, with no acyclicity hypothesis. -/
theorem vertexTwistGlobalZeroChain_closed (d : V → ℕ)
    (s : vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ))) :
    (contraction R d).d (vertexTwistGlobalZeroChain R V (fun v => -(d v : ℤ)) s) = 0 := by
  apply zeroCharts_closed_of_full
  intro σ τ
  simp only [vertexTwistGlobalChartCoordinates_apply]
  rw [← vertexTwistSheafFaceSections_restrict,← vertexTwistSheafFaceSections_restrict]
  rw [← (vertexTwistSheaf R V _).presheaf.map_comp_apply,
    ← (vertexTwistSheaf R V _).presheaf.map_comp_apply]
  rfl

/-- The original global section is determined by its original degree-zero coefficient chain. -/
theorem vertexTwistGlobalZeroChain_injective (a : V → ℤ) :
    Function.Injective (vertexTwistGlobalZeroChain R V a) := by
  intro s t h
  have he := zeroCharts_injective R h
  apply TopCat.Sheaf.eq_of_locally_eq' (X := TopCat.of (vertexScheme R V))
    (vertexTwistAbelianSheaf R V a)
    (fun σ : V → Bool => SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ))
    ⊤ (fun _ => homOfLE le_top) (vertexBooleanFaceOpens_cover R V)
  intro σ
  apply (vertexTwistSheafFaceSectionsEquiv R V a (chartFace σ)).injective
  exact congrFun he σ

private theorem chart_sections_compatible (d : V → ℕ)
    (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (hx : (contraction R d).d (zeroCharts R x) = 0) :
    TopCat.Presheaf.IsCompatible (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj
      (fun σ => SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ))
      (fun σ => (vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) (chartFace σ)).symm (x σ)) := by
  intro σ τ
  let F := vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))
  let M := vertexTwistSheaf R V (fun v => -(d v : ℤ))
  let U := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ)
  let W := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace τ)
  let s := (vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) (chartFace σ)).symm (x σ)
  let t := (vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) (chartFace τ)).symm (x τ)
  have he := vertexTwistSheafFaceSections_difference R V (fun v => -(d v : ℤ))
    (chartFace σ) (chartFace τ) s t
  simp only [s,t,LinearEquiv.apply_symm_apply,zeroCharts_closed_pair R d x hx,sub_self] at he
  have hz : M.presheaf.map (eqToHom (vertexBinaryFaceOpen_join R V (chartFace σ) (chartFace τ))).op
      (SheafTools.twoOpenSectionDifference F U W (s,t)) = 0 :=
    (vertexTwistSheafFaceSectionsEquiv R V _ _).injective (he.trans (map_zero _).symm)
  have hz' : SheafTools.twoOpenSectionDifference F U W (s,t) = 0 :=
    (ConcreteCategory.bijective_of_isIso
      (M.presheaf.map (eqToHom (vertexBinaryFaceOpen_join R V (chartFace σ) (chartFace τ))).op)).injective
        (hz.trans (map_zero _).symm)
  exact sub_eq_zero.mp hz'

/-- Mathlib's original sheaf gluing supplies a global section for every original degree-zero cocycle. -/
theorem vertexTwistGlobalZeroChain_surjective (d : V → ℕ) (x : zeroCycleModule R d) :
    ∃ s : vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ)),
      vertexTwistGlobalZeroChain R V (fun v => -(d v : ℤ)) s = x := by
  let c := fun σ => faceEquiv R x.val (chartFace σ)
  have hc : (contraction R d).d (zeroCharts R c) = 0 := by
    rw [zeroCharts_reconstruct R x.val x.property.1]
    exact x.property.2
  obtain ⟨s,hs,_⟩ := TopCat.Sheaf.existsUnique_gluing' (X := TopCat.of (vertexScheme R V))
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)))
    (fun σ : V → Bool => SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) (chartFace σ))
    ⊤ (fun _ => homOfLE le_top) (vertexBooleanFaceOpens_cover R V)
    (fun σ => (vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) (chartFace σ)).symm (c σ))
    (chart_sections_compatible R V d c hc)
  refine ⟨s,?_⟩
  change zeroCharts R (vertexTwistGlobalChartCoordinates R V _ s) = x.val
  rw [← zeroCharts_reconstruct R x.val x.property.1]
  congr 1
  funext σ
  rw [vertexTwistGlobalChartCoordinates_apply]
  change vertexTwistSheafFaceSectionsEquiv R V _ (chartFace σ)
    ((vertexTwistAbelianSheaf R V _).obj.map (homOfLE le_top).op s) = c σ
  rw [hs σ,LinearEquiv.apply_symm_apply]

/-- All actual global nonpositive-twist sections are exactly the original degree-zero cocycles. -/
noncomputable def vertexTwistGlobalZeroCycleEquiv (d : V → ℕ) :
    vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ)) ≃ₗ[R] zeroCycleModule R d := by
  let f : vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ)) →ₗ[R] zeroCycleModule R d :=
    (vertexTwistGlobalZeroChain R V (fun v => -(d v : ℤ))).codRestrict _ fun s =>
      ⟨zeroCharts_mem_supported R _,vertexTwistGlobalZeroChain_closed R V d s⟩
  apply LinearEquiv.ofBijective f
  constructor
  · intro s t h
    exact vertexTwistGlobalZeroChain_injective R V _ (congrArg Subtype.val h)
  · intro x
    obtain ⟨s,hs⟩ := vertexTwistGlobalZeroChain_surjective R V d x
    exact ⟨s,Subtype.ext hs⟩

/-- The comparison preserves the specified chain of actual chart restrictions. -/
theorem vertexTwistGlobalZeroCycleEquiv_val (d : V → ℕ)
    (s : vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ))) :
    (vertexTwistGlobalZeroCycleEquiv R V d s).val = vertexTwistGlobalZeroChain R V _ s := rfl

end BPFixedPoints.ProjectiveLine
