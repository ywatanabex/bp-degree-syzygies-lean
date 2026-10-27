import BPFixedPoints.Incidence.IncidenceProjectiveZeroScheme

/-! # The independent zero charts are the actual open charts of the global zero scheme

The chart morphisms are the canonical lifts through the independent closed
subscheme. Their squares in the actual projective product are pullbacks.
Thus the independent construction has exactly the prescribed local zero rings.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The independent zero chart's canonical morphism into the independent global zero scheme. -/
noncomputable def incidenceProjectiveZeroChartToScheme (σ : V → Bool) :
    G.incidenceProjectiveZeroChart σ ⟶ G.incidenceProjectiveZeroScheme :=
  IsClosedImmersion.lift G.incidenceProjectiveZeroι (G.incidenceProjectiveZeroChartι σ) (by
    change G.incidenceProjectiveZeroIdeal.subschemeι.ker ≤ _
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact iInf_le _ σ)

@[reassoc] theorem incidenceProjectiveZeroChartToScheme_ι (σ : V → Bool) :
    G.incidenceProjectiveZeroChartToScheme σ ≫ G.incidenceProjectiveZeroι =
      G.incidenceProjectiveZeroChartι σ :=
  IsClosedImmersion.lift_fac _ _ _

/-- The canonical chart lift agrees with the original geometric comparison on that chart. -/
@[reassoc] theorem incidenceProjectiveZeroChartIso_hom_toScheme (σ : V → Bool) :
    (G.incidenceProjectiveZeroChartIso σ).hom ≫ G.incidenceProjectiveZeroChartToScheme σ =
      G.incidenceFaceι (chartFace σ) ≫ G.incidenceProjectiveZeroIso.hom := by
  apply (cancel_mono G.incidenceProjectiveZeroι).mp
  simp only [Category.assoc, G.incidenceProjectiveZeroChartToScheme_ι,
    G.incidenceProjectiveZeroIso_hom_ι]
  exact G.incidenceProjectiveZeroChartIso_hom_ι σ

/-- The full independent zero chart is the actual projective-chart base change of the zero scheme. -/
theorem incidenceProjectiveZeroChart_isPullback (σ : V → Bool) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ))))
      (G.incidenceProjectiveZeroChartToScheme σ)
      (ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ))
      G.incidenceProjectiveZeroι := by
  apply (G.incidenceProjectiveChart_isPullback σ).of_iso
    (G.incidenceProjectiveZeroChartIso σ) (Iso.refl _)
    G.incidenceProjectiveZeroIso (Iso.refl _)
  · apply (cancel_mono
      (ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ))).mp
    simp only [Iso.refl_hom, Category.comp_id, Category.assoc]
    exact (G.incidenceProjectiveMorphism_chart σ).trans
      (G.incidenceProjectiveZeroChartIso_hom_ι σ).symm
  · exact (G.incidenceProjectiveZeroChartIso_hom_toScheme σ).symm
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using
      G.incidenceProjectiveZeroIso_hom_ι.symm

instance incidenceProjectiveZeroChartToScheme_isOpenImmersion (σ : V → Bool) :
    IsOpenImmersion (G.incidenceProjectiveZeroChartToScheme σ) :=
  MorphismProperty.of_isPullback (G.incidenceProjectiveZeroChart_isPullback σ) inferInstance

/-- The independent original zero charts cover all points of the independent global zero scheme. -/
theorem incidenceProjectiveZeroChartToScheme_covers (x : G.incidenceProjectiveZeroScheme) :
    ∃ σ : V → Bool, ∃ y, G.incidenceProjectiveZeroChartToScheme σ y = x := by
  obtain ⟨σ, y, hy⟩ := G.incidenceBooleanFaceCover.exists_eq (G.incidenceProjectiveZeroIso.inv x)
  refine ⟨σ, (G.incidenceProjectiveZeroChartIso σ).hom y, ?_⟩
  rw [← Scheme.Hom.comp_apply, G.incidenceProjectiveZeroChartIso_hom_toScheme,
    Scheme.Hom.comp_apply]
  change G.incidenceFaceι (chartFace σ) y = G.incidenceProjectiveZeroIso.inv x at hy
  rw [hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

/-- Genuine affine open cover by the independent original zero quotients. -/
noncomputable def incidenceProjectiveZeroAffineCover : G.incidenceProjectiveZeroScheme.AffineOpenCover where
  I₀ := V → Bool
  X σ := CommRingCat.of (G.IncidenceProjectiveZeroChartRing σ)
  f := G.incidenceProjectiveZeroChartToScheme
  idx x := (G.incidenceProjectiveZeroChartToScheme_covers x).choose
  covers x := (G.incidenceProjectiveZeroChartToScheme_covers x).choose_spec

end BPFixedPoints.Multigraph
