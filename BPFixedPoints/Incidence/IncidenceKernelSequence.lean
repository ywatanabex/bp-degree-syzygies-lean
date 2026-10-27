import BPFixedPoints.Incidence.IncidenceKernelSheafCharts

/-! # The short exact sequence `0 → K_G → O^{4m} → F_G → 0`

This file completes the sheaf-level presentation of Lemma `alg:incidence-vector-bundle`
(supplement section `supp:vector-bundle`) on `X_G = vertexScheme ℂ V = (ℙ¹)^V`. The evaluation
map `incEvaluationSheafMap : O^{4m} ⟶ F_G` and its kernel `K_G = incKernelSheaf` are those of
`IncidenceKernelSheafEvaluation.lean` and `IncidenceKernelSheafCharts.lean`.

* **Epimorphisms from local surjectivity.** On any site, a morphism of sheaves of modules that is
  surjective on the sections over every object mapping to some member of a covering family of
  the terminal object is an epimorphism (`sheafOfModules_epi_of_coversTop`). The proof passes to
  the underlying abelian sheaves, which reflect epimorphisms, and uses Mathlib's
  `Sheaf.epi_of_isLocallySurjective`.
* **The evaluation map is an epimorphism.** On every subopen of a chart, the evaluation map is
  surjective on sections, by the splitting `incChartEvaluationSection` of the chart evaluation map
  (`incEvaluationSheafMap_app_surjective`). Hence `incEvaluationSheafMap` is an epimorphism in
  `SheafOfModules` (`incEvaluationSheafMap_epi`).
* **The short exact sequence.** `incKernelShortComplex` is the short complex
  `K_G → O^{4m} → F_G` of sheaves of modules on `X_G`, and it is short exact
  (`incKernelShortComplex_shortExact`). In particular `F_G` is the cokernel of
  `K_G → O^{4m}` (`incEvaluationSheafMap_isCokernel`).
* **Local splittings.** On the chart open of `σ`, the chart section that puts the chart
  coefficient of the `L_e` component on the unit coefficient `c_{e, incChartUnitIdx σ e}` is a
  morphism of sheaves of modules `F_G|σ ⟶ O^{4m}|σ` (`incEvaluationChartSection`) and a right
  inverse of the restricted evaluation map (`incEvaluationChartSection_comp`). So the restricted
  evaluation map is a split epimorphism (`incEvaluationSheafMap_over_isSplitEpi`), the restricted
  sequence `incKernelChartShortComplex σ` is split (`incKernelChartSplitting`) and short exact,
  and `O^{4m}|σ ≅ K_G|σ ⊞ F_G|σ` (`incCoeffChartBiprodIso`).

Not covered here: the relative spectrum of the symmetric algebra of the dual of `K_G` and its
identification with `Z_G` as schemes; cohomology of the sequence; global splittings (the
splittings above are chart by chart and are not claimed to glue).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

/-! ### Epimorphisms of sheaves of modules from local surjectivity -/

section General

universe v₁ u₁ u

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Local surjectivity gives epimorphisms.** Let `Y` be a family of objects covering the
terminal object of the site. A morphism of sheaves of modules that is surjective on sections over
every object mapping to some `Y i` is an epimorphism in `SheafOfModules R`. -/
theorem sheafOfModules_epi_of_coversTop [J.HasSheafCompose (forget AddCommGrpCat.{u})]
    {I : Type*} {Y : I → C} (hY : J.CoversTop Y) {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ (i : I) {W : C} (_ : W ⟶ Y i), Function.Surjective (f.val.app (op W)).hom) :
    Epi f := by
  have := Functor.reflectsEpimorphisms_of_faithful (SheafOfModules.toSheaf R)
  apply (SheafOfModules.toSheaf R).epi_of_epi_map
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
    ⟨fun {U} s => J.superset_covering (fun W g hg => by
      obtain ⟨i, ⟨a⟩⟩ := hg
      obtain ⟨x, hx⟩ := hf i a (N.val.map g.op s)
      exact ⟨x, hx⟩) (hY U)⟩
  exact Sheaf.epi_of_isLocallySurjective _

end General

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-! ### The evaluation map is an epimorphism -/

section Epi

/-- **Surjectivity on chart subopens.** On every subopen `W` of the standard chart `σ`, the
evaluation map `O^{4m} → F_G` is surjective on sections over `W`: a preimage of `y` is the chart
section `incChartEvaluationSection σ` applied to the chart coefficients of `y`. -/
theorem incEvaluationSheafMap_app_surjective (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) :
    Function.Surjective (G.incEvaluationSheafMap.val.app (op W)).hom := by
  intro y
  refine ⟨(incCoeffSectionsEquiv W).symm
    (G.incChartEvaluationSection σ (G.incEdgeChartEquiv σ W hW y)), ?_⟩
  apply (G.incEdgeChartEquiv σ W hW).injective
  rw [incEvaluationSheafMap_chart, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (G.incChartEvaluation_comp_section σ _) _

/-- **The evaluation map `O^{4m} → F_G` is an epimorphism** of sheaves of modules on `X_G`. -/
instance incEvaluationSheafMap_epi : Epi G.incEvaluationSheafMap :=
  sheafOfModules_epi_of_coversTop (incChartOpen_coversTop V) _
    fun σ W i => G.incEvaluationSheafMap_app_surjective σ W i.le

end Epi

/-! ### The short exact sequence -/

section ShortExact

/-- The short complex `K_G → O^{4m} → F_G` of sheaves of modules on `X_G`: the inclusion of the
kernel bundle followed by the evaluation map. -/
noncomputable def incKernelShortComplex :
    ShortComplex (SheafOfModules (vertexScheme ℂ V).ringCatSheaf) :=
  ShortComplex.mk G.incKernelSheafι G.incEvaluationSheafMap G.incKernelSheafι_comp

/-- The short complex `K_G → O^{4m} → F_G` is exact. -/
theorem incKernelShortComplex_exact : G.incKernelShortComplex.Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel G.incEvaluationSheafMap)

/-- **The sequence `0 → K_G → O^{4m} → F_G → 0` is short exact** in the abelian category of
sheaves of modules on `X_G`. -/
theorem incKernelShortComplex_shortExact : G.incKernelShortComplex.ShortExact :=
  ShortComplex.ShortExact.mk' G.incKernelShortComplex_exact
    (inferInstanceAs (Mono (kernel.ι G.incEvaluationSheafMap))) G.incEvaluationSheafMap_epi

/-- `F_G` is the cokernel of the inclusion `K_G → O^{4m}`, with cokernel map the evaluation
map. -/
noncomputable def incEvaluationSheafMap_isCokernel :
    IsColimit (CokernelCofork.ofπ G.incEvaluationSheafMap G.incKernelSheafι_comp) :=
  G.incKernelShortComplex_shortExact.gIsCokernel

end ShortExact

/-! ### The chart sections and the local splittings -/

section Splitting

/-- The chart section of the evaluation map, coordinatewise. -/
theorem incChartEvaluationSection_apply {R : Type*} [CommRing R] (σ : V → Bool) (y : E → R)
    (c : IncCoeffIdx E) :
    G.incChartEvaluationSection σ y c = if c.2 = G.incChartUnitIdx σ c.1 then y c.1 else 0 :=
  rfl

/-- **The chart section as a morphism of sheaves of modules.** On the chart open of `σ`, the
morphism `F_G|σ ⟶ O^{4m}|σ` that sends the `L_e` component, read in the chart frame of `L_e`, to
the unit coefficient `c_{e, incChartUnitIdx σ e}`. -/
noncomputable def incEvaluationChartSection (σ : V → Bool) :
    (G.edgeBundle ℂ).over (incChartOpen V σ) ⟶ (incCoeffSheaf V E).over (incChartOpen V σ) :=
  ∑ e : E, (SheafOfModules.overFunctor _ (incChartOpen V σ)).map
      (biproduct.π (fun e => G.edgeLineSheaf ℂ e) e) ≫
    (vertexTwistOverChartIso ℂ V (fun v => (G.endCount e v : ℤ))
      (vertexBooleanPivot V σ)).hom ≫
    (SheafOfModules.overFunctor _ (incChartOpen V σ)).map
      (biproduct.ι (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
        (e, G.incChartUnitIdx σ e))

/-- On every subopen of chart `σ`, the chart section morphism is, in the coefficient frame of
`O^{4m}` and the chart frame of `F_G`, the chart section `incChartEvaluationSection σ`. -/
theorem incCoeffSectionsEquiv_incEvaluationChartSection (σ : V → Bool)
    (S : Over (incChartOpen V σ)) (y : Γ(G.edgeBundle ℂ, S.left)) :
    incCoeffSectionsEquiv S.left (((G.incEvaluationChartSection σ).val.app (op S)).hom y) =
      G.incChartEvaluationSection σ (G.incEdgeChartEquiv σ S.left S.hom.le y) := by
  funext c
  obtain ⟨e₀, ab⟩ := c
  change ((biproduct.π
      (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
      (e₀, ab)).val.app (op S.left)).hom
      (((G.incEvaluationChartSection σ).val.app (op S)).hom y) = _
  rw [incEvaluationChartSection, sheafOfModules_sum_app_apply, map_sum,
    Finset.sum_eq_single e₀]
  · by_cases h : ab = G.incChartUnitIdx σ e₀
    · subst h
      have := biproduct_ι_π_app_self
        (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
        (e₀, G.incChartUnitIdx σ e₀) (op S.left)
      rw [incChartEvaluationSection_apply, ite_eq_left rfl, incEdgeChartEquiv_apply]
      exact this _
    · rw [incChartEvaluationSection_apply, ite_eq_right h]
      exact biproduct_ι_π_app_ne _ (fun h' => h (congrArg Prod.snd h').symm) _ _
  · intro e _ he
    exact biproduct_ι_π_app_ne _ (fun h' => he (congrArg Prod.fst h')) _ _
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- **The chart section splits the restricted evaluation map.** On the chart open of `σ`, the
chart section followed by the restricted evaluation map is the identity of `F_G|σ`. -/
@[reassoc (attr := simp)] theorem incEvaluationChartSection_comp (σ : V → Bool) :
    G.incEvaluationChartSection σ ≫
      (SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incEvaluationSheafMap = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (G.incEvaluationSheafMap.val.app (op S.unop.left)).hom
    (((G.incEvaluationChartSection σ).val.app S).hom y) = y
  apply (G.incEdgeChartEquiv σ S.unop.left S.unop.hom.le).injective
  rw [incEvaluationSheafMap_chart, incCoeffSectionsEquiv_incEvaluationChartSection]
  exact LinearMap.congr_fun (G.incChartEvaluation_comp_section σ _) _

/-- On the chart open of `σ`, the restricted evaluation map is a split epimorphism. -/
instance incEvaluationSheafMap_over_isSplitEpi (σ : V → Bool) :
    IsSplitEpi ((SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incEvaluationSheafMap) :=
  IsSplitEpi.mk' ⟨G.incEvaluationChartSection σ, G.incEvaluationChartSection_comp σ⟩

/-- The restriction to the chart open of `σ` of the short complex `K_G → O^{4m} → F_G`. -/
noncomputable def incKernelChartShortComplex (σ : V → Bool) :
    ShortComplex (SheafOfModules ((vertexScheme ℂ V).ringCatSheaf.over (incChartOpen V σ))) :=
  G.incKernelShortComplex.map (SheafOfModules.overFunctor _ (incChartOpen V σ))

/-- The restricted short complex on chart `σ` is exact: restriction preserves kernels. -/
theorem incKernelChartShortComplex_exact (σ : V → Bool) :
    (G.incKernelChartShortComplex σ).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (isLimit_kernelFork_over (incChartOpen V σ) G.incEvaluationSheafMap)

/-- **The sequence splits on every chart.** On the chart open of `σ`, the restricted sequence
`0 → K_G|σ → O^{4m}|σ → F_G|σ → 0` is split, with section the chart section
`incEvaluationChartSection σ` (`incKernelChartSplitting_s`). -/
noncomputable def incKernelChartSplitting (σ : V → Bool) :
    (G.incKernelChartShortComplex σ).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (G.incKernelChartShortComplex_exact σ)
    (G.incEvaluationChartSection σ) (G.incEvaluationChartSection_comp σ)
    (G.incKernelSheafι_over_mono _)

/-- The section of the chart splitting is the chart section. -/
theorem incKernelChartSplitting_s (σ : V → Bool) :
    (G.incKernelChartSplitting σ).s = G.incEvaluationChartSection σ :=
  rfl

/-- The restricted sequence on chart `σ` is short exact. -/
theorem incKernelChartShortComplex_shortExact (σ : V → Bool) :
    (G.incKernelChartShortComplex σ).ShortExact :=
  (G.incKernelChartSplitting σ).shortExact

/-- **Local decomposition.** On the chart open of `σ`, the chart splitting identifies `O^{4m}|σ`
with the biproduct `K_G|σ ⊞ F_G|σ`. -/
noncomputable def incCoeffChartBiprodIso (σ : V → Bool) :
    (incCoeffSheaf V E).over (incChartOpen V σ) ≅
      G.incKernelSheaf.over (incChartOpen V σ) ⊞ (G.edgeBundle ℂ).over (incChartOpen V σ) :=
  (G.incKernelChartSplitting σ).isoBinaryBiproduct

end Splitting

end BPFixedPoints.Multigraph
