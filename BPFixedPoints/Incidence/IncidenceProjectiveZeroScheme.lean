import BPFixedPoints.Incidence.IncidenceProjectiveZeroCharts

/-! # Independent projective zero scheme and its comparison with the original incidence scheme

The closed subscheme is defined from the independent homogeneous zero charts:
its ideal sheaf is the intersection of their actual scheme-theoretic kernels.
It does not refer to the glued incidence scheme or its global morphism. The
comparison then proves that all these local zeros glue with their full scheme
structure, by Mathlib's kernel theorem for an actual open cover.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory

private theorem closedImmersionIsoOfKernelEq_exists {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : Y.IdealSheafData) (h : f.ker = I) :
    ∃ e : X ≅ I.subscheme, e.hom ≫ I.subschemeι = f := by
  subst I
  exact ⟨asIso f.toImage, f.toImage_imageι⟩

/-- Mathlib's image comparison for a closed immersion, with its embedding law retained.
Choosing the proved witness keeps dependent ideal transports out of later reductions. -/
noncomputable def closedImmersionIsoOfKernelEq {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : Y.IdealSheafData) (h : f.ker = I) : X ≅ I.subscheme :=
  Classical.choose (closedImmersionIsoOfKernelEq_exists f I h)

@[reassoc] theorem closedImmersionIsoOfKernelEq_hom_ι {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : Y.IdealSheafData) (h : f.ker = I) :
    (closedImmersionIsoOfKernelEq f I h).hom ≫ I.subschemeι = f :=
  Classical.choose_spec (closedImmersionIsoOfKernelEq_exists f I h)

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The genuine open cover by the original overlap-free quotient faces. -/
noncomputable def incidenceBooleanFaceCover : G.incidenceGluedScheme.OpenCover where
  I₀ := V → Bool
  X σ := G.incidenceAffineFace (chartFace σ)
  f σ := G.incidenceFaceι (chartFace σ)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨σ, y, hy⟩ := G.incidenceChartι_jointly_surjective x
      exact ⟨σ, ⟨(G.incidenceChartFaceIso σ).hom y, hy⟩⟩
    · intro σ
      infer_instance

/-- Independent global zero ideal, defined solely from the original homogeneous zero charts. -/
noncomputable def incidenceProjectiveZeroIdeal :
    (ProjectiveLine.vertexScheme (IncCoeffRing E) V).IdealSheafData :=
  ⨅ σ : V → Bool, (G.incidenceProjectiveZeroChartι σ).ker

/-- The independent closed incidence zero scheme in the actual projective product. -/
noncomputable def incidenceProjectiveZeroScheme : Scheme :=
  G.incidenceProjectiveZeroIdeal.subscheme

/-- Its genuine closed-subscheme inclusion in the actual projective product. -/
noncomputable def incidenceProjectiveZeroι :
    G.incidenceProjectiveZeroScheme ⟶ ProjectiveLine.vertexScheme (IncCoeffRing E) V :=
  G.incidenceProjectiveZeroIdeal.subschemeι

instance incidenceProjectiveZeroι_isClosedImmersion :
    IsClosedImmersion G.incidenceProjectiveZeroι := by
  dsimp only [incidenceProjectiveZeroι]
  infer_instance

/-- The global geometric incidence kernel is exactly the independent original zero ideal. -/
theorem incidenceProjectiveMorphism_ker :
    G.incidenceProjectiveMorphism.ker = G.incidenceProjectiveZeroIdeal := by
  rw [← G.incidenceProjectiveMorphism.iInf_ker_openCover_map_comp G.incidenceBooleanFaceCover]
  change (⨅ σ : V → Bool,
    (G.incidenceFaceι (chartFace σ) ≫ G.incidenceProjectiveMorphism).ker) = _
  apply iInf_congr
  intro σ
  rw [← G.incidenceProjectiveZeroChartIso_hom_ι]
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- Full scheme comparison with the independent original homogeneous projective zero scheme. -/
noncomputable def incidenceProjectiveZeroIso :
    G.incidenceGluedScheme ≅ G.incidenceProjectiveZeroScheme :=
  SchemeTools.closedImmersionIsoOfKernelEq G.incidenceProjectiveMorphism
    G.incidenceProjectiveZeroIdeal G.incidenceProjectiveMorphism_ker

/-- The global comparison preserves the actual projective embedding. -/
@[reassoc] theorem incidenceProjectiveZeroIso_hom_ι :
    G.incidenceProjectiveZeroIso.hom ≫ G.incidenceProjectiveZeroι = G.incidenceProjectiveMorphism :=
  SchemeTools.closedImmersionIsoOfKernelEq_hom_ι _ _ _

/-- The global comparison also preserves the original geometric coefficient-space morphism. -/
@[reassoc] theorem incidenceProjectiveZeroIso_hom_toBase :
    G.incidenceProjectiveZeroIso.hom ≫ G.incidenceProjectiveZeroι ≫
        ProjectiveLine.vertexToBase (IncCoeffRing E) V = G.incidenceCoefficientMorphism := by
  rw [← Category.assoc, G.incidenceProjectiveZeroIso_hom_ι, G.incidenceProjectiveMorphism_toBase]

/-- Existence form of the independently constructed global projective zero-scheme comparison. -/
theorem incidenceProjectiveZeroScheme_comparison :
    Nonempty (G.incidenceGluedScheme ≅ G.incidenceProjectiveZeroScheme) :=
  ⟨G.incidenceProjectiveZeroIso⟩

end BPFixedPoints.Multigraph
