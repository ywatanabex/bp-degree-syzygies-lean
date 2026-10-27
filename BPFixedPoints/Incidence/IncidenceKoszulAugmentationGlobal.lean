import BPFixedPoints.Incidence.IncidenceKoszulAugmentation

/-! # Global sections of the augmentation of `K_G` and the incidence ring `𝒰_G`

For the augmentation `incKoszulAugmentation : ∧^0 F_G^∨ ⟶ i_* O_{Z_G}` of
`IncidenceKoszulAugmentation.lean`, this file compares global sections with the existing
identification `incidenceProjectiveZeroGlobalSectionsEquiv : Γ(Z_G, O) ≃ 𝒰_G`, which goes through
the existing scheme comparison `incidenceProjectiveZeroIso` with the glued incidence scheme and the
common torus.

* On `r` times the unit section the augmentation is `i^* r` (`incKoszulAugmentation_unit`).
* **Coefficient action.** The global section `p · 1`, with `p ∈ S_G` acting through
  `Y ⟶ Spec S_G`, goes to the coefficient `p` of `Γ(Z_G, O)`, acting through `Z_G ⟶ Spec S_G`
  (`incKoszulAugmentation_coefficient`), hence to `coeffHom p ∈ 𝒰_G`
  (`incKoszulAugmentation_globalSections_coeff`).
* **Chart values.** The common torus of the glued scheme followed by the comparison factors
  through every chart of `Z_G`, by the existing chart identifications
  `A_σ/(f_e) ≅ IncFaceRing (chartFace σ) ≅ IncChartRing σ` (`incidenceTorusι_projectiveZeroIso`).
  Hence the element of `𝒰_G ⊆ IncTorusRing` of a global function of `Z_G` is the torus image of its
  value on any chart (`incidenceProjectiveZeroGlobalSectionsEquiv_chart`). For `ε(x)`, `x` a global
  section of `∧^0 F_G^∨`, this value is the existing face augmentation
  `incUniversalKoszulFaceAugmentation (chartFace σ)` of `x`
  (`incKoszulAugmentation_globalSections_chart`).

Not proved here: a comparison with the Čech-level identification `univCechKoszulH0Equiv`, or that
the global sections of `K_G` compute derived global sections.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 100000

section Coefficients

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- On `r` times the unit section, the augmentation is the pullback `i^* r` of functions: under
`O ≅ ∧^0 F_G^∨`, the augmentation is the structure map `O_Y ⟶ i_* O_{Z_G}`. -/
theorem incKoszulAugmentation_unit (W : (vertexScheme (IncCoeffRing E) V).Opens)
    (r : Γ(vertexScheme (IncCoeffRing E) V, W)) :
    ((G.incKoszulAugmentation).val.app (op W)).hom (r • G.exteriorSectionUnit (IncCoeffRing E) W) =
      G.incidenceProjectiveZeroι.app W r := by
  let φ := G.exteriorZeroUnitMap (R := IncCoeffRing E)
  have hr : ((inv φ).val.app (op W)).hom ((φ.val.app (op W)).hom r) = r :=
    congrArg (fun k => (k.val.app (op W)).hom r) (IsIso.hom_inv_id φ)
  change ((schemeStructurePushforward G.incidenceProjectiveZeroι).val.app (op W)).hom
    (((inv φ).val.app (op W)).hom ((φ.val.app (op W)).hom r)) = _
  rw [hr, schemeStructurePushforward_app]

/-- **The augmentation preserves the coefficient action.** The global unit section times the
coefficient `p ∈ S_G` (acting through `Y ⟶ Spec S_G`) goes to the coefficient `p` of the global
functions of `Z_G` (acting through `Z_G ⟶ Spec S_G`). -/
theorem incKoszulAugmentation_coefficient (p : IncCoeffRing E) :
    (show Γ(G.incidenceProjectiveZeroScheme, ⊤) from
      ((G.incKoszulAugmentation).val.app (op ⊤)).hom
        (SchemeTools.schemeBaseCoefficientAt (vertexToBase (IncCoeffRing E) V) ⊤ p •
          G.exteriorSectionUnit (IncCoeffRing E) ⊤)) =
      G.incidenceProjectiveZeroCoefficientHom p := by
  rw [incKoszulAugmentation_unit]
  change G.incidenceProjectiveZeroι.appTop ((vertexScheme (IncCoeffRing E) V).presheaf.map
    (homOfLE le_rfl).op (SchemeTools.schemeBaseCoefficientHom
      (vertexToBase (IncCoeffRing E) V) p)) = _
  rw [univPresheaf_map_le_rfl]
  rfl

/-- **Global sections and `𝒰_G`.** Under the existing identification
`incidenceProjectiveZeroGlobalSectionsEquiv : Γ(Z_G, O) ≃ 𝒰_G`, the augmentation of the global
section `p · 1` of `∧^0 F_G^∨` is the coefficient `p` of `𝒰_G`. -/
theorem incKoszulAugmentation_globalSections_coeff (p : IncCoeffRing E) :
    G.incidenceProjectiveZeroGlobalSectionsEquiv
      (show Γ(G.incidenceProjectiveZeroScheme, ⊤) from
        ((G.incKoszulAugmentation).val.app (op ⊤)).hom
          (SchemeTools.schemeBaseCoefficientAt (vertexToBase (IncCoeffRing E) V) ⊤ p •
            G.exteriorSectionUnit (IncCoeffRing E) ⊤)) = G.coeffHom p := by
  rw [incKoszulAugmentation_coefficient, incidenceProjectiveZeroGlobalSectionsEquiv_coeff]

end Coefficients

section GlobalCharts

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The common torus of the glued incidence scheme, followed by the existing comparison with the
projective zero scheme, factors through the chart `σ` of `Z_G` by the existing chain of chart
identifications `A_σ/(f_e) ≅ IncFaceRing (chartFace σ) ≅ IncChartRing σ` and the chart-to-torus
map. -/
theorem incidenceTorusι_projectiveZeroIso (σ : V → Bool) :
    G.incidenceTorusι ≫ G.incidenceProjectiveZeroIso.hom =
      Spec.map (CommRingCat.ofHom (R := G.IncidenceProjectiveZeroChartRing σ) (S := G.IncTorusRing)
        ((G.incChartMap σ).toRingHom.comp ((G.incFaceChartEquiv σ).toRingEquiv.toRingHom.comp
          (G.incidenceProjectiveZeroChartEquiv σ).toRingEquiv.toRingHom))) ≫
        G.incidenceProjectiveZeroChartToScheme σ := by
  rw [← G.incidenceTorusι_factor σ, Category.assoc, incidenceChartι, Category.assoc,
    ← incidenceProjectiveZeroChartIso_hom_toScheme]
  simp only [← Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom (G.incChartMap σ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (G.incFaceChartEquiv σ).toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (R := G.IncidenceProjectiveZeroChartRing σ)
          (S := G.IncFaceRing (chartFace σ))
          (G.incidenceProjectiveZeroChartEquiv σ).toRingEquiv.toRingHom) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- **Chart values of the global functions of `Z_G`.** Under the existing identification
`incidenceProjectiveZeroGlobalSectionsEquiv : Γ(Z_G, O) ≃ 𝒰_G ⊆ IncTorusRing`, a global function
of `Z_G` is the image in the torus ring of its value on any chart `σ`, read in the chart ring
`A_σ/(f_e)` and transported to `IncChartRing σ` by the existing chart identifications. -/
theorem incidenceProjectiveZeroGlobalSectionsEquiv_chart (σ : V → Bool)
    (s : Γ(G.incidenceProjectiveZeroScheme, ⊤)) :
    (G.incidenceProjectiveZeroGlobalSectionsEquiv s).val =
      G.incChartMap σ (G.incFaceChartEquiv σ (G.incidenceProjectiveZeroChartEquiv σ
        ((G.incZeroChartSectionsIso σ).hom
          (G.incidenceProjectiveZeroScheme.presheaf.map (homOfLE le_top).op s)))) := by
  have h1 : (G.incidenceProjectiveZeroGlobalSectionsEquiv s).val =
      G.incidenceGlobalTorusHom (G.incidenceProjectiveZeroIso.hom.appTop s) := by
    change (G.incidenceGluedGlobalSectionsEquiv
      (G.incidenceProjectiveZeroSectionsToGlued s)).val = _
    rw [incidenceGluedGlobalSectionsEquiv_val]
    congr 1
    unfold incidenceProjectiveZeroSectionsToGlued
    exact SchemeTools.globalSectionsRingEquiv_apply _ s
  have h2 := congrArg (fun k => k.hom (G.incidenceProjectiveZeroIso.hom.appTop s))
    G.incidenceGlobalTorusHom_eq
  rw [h1]
  refine h2.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of G.IncTorusRing)).hom
    ((G.incidenceTorusι ≫ G.incidenceProjectiveZeroIso.hom).appTop s) = _
  rw [G.incidenceTorusι_projectiveZeroIso σ, Scheme.Hom.comp_appTop]
  change ((Spec.map _).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of G.IncTorusRing)).hom)
    ((G.incidenceProjectiveZeroChartToScheme σ).appTop s) = _
  rw [Scheme.ΓSpecIso_naturality]
  change (G.incChartMap σ) (G.incFaceChartEquiv σ (G.incidenceProjectiveZeroChartEquiv σ
    ((Scheme.ΓSpecIso (CommRingCat.of (G.IncidenceProjectiveZeroChartRing σ))).hom
      ((G.incidenceProjectiveZeroChartToScheme σ).appTop s)))) = _
  congr 3
  simp only [incZeroChartSectionsIso, affineOpenSectionsIsoAt, affineOpenSectionsIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, openImageSectionsIso_hom]
  change _ = (Scheme.ΓSpecIso _).hom ((G.incidenceProjectiveZeroScheme.presheaf.map _ ≫
    G.incidenceProjectiveZeroScheme.presheaf.map _ ≫ Scheme.Hom.appLE _ _ _ _) s)
  rw [Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]
  rfl

/-- **Global sections of the augmentation and `𝒰_G`, with chart values.** For a global section
`x` of `∧^0 F_G^∨`, the element of `𝒰_G ⊆ IncTorusRing` attached to `ε(x) ∈ Γ(Z_G, O)` by the
existing identification is, for every chart `σ`, the torus image of the existing face
augmentation `incUniversalKoszulFaceAugmentation (chartFace σ)` of the restriction of `x` to the
chart. -/
theorem incKoszulAugmentation_globalSections_chart (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, ⊤)) :
    (G.incidenceProjectiveZeroGlobalSectionsEquiv
      (show Γ(G.incidenceProjectiveZeroScheme, ⊤) from
        ((G.incKoszulAugmentation).val.app (op ⊤)).hom x)).val =
      G.incChartMap σ (G.incFaceChartEquiv σ (G.incUniversalKoszulFaceAugmentation (chartFace σ)
        ((G.exteriorBundle (IncCoeffRing E) 0).val.map
          (homOfLE (le_top : univFaceOpen (IncCoeffRing E) V (chartFace σ) ≤ ⊤)).op x))) := by
  rw [incidenceProjectiveZeroGlobalSectionsEquiv_chart G σ,
    ← incidenceProjectiveZeroChartEquiv_chartAugmentation, ← incZeroChartSectionsIso_augmentation]
  congr 4
  exact (PresheafOfModules.naturality_apply (G.incKoszulAugmentation).val
    (homOfLE (le_top : univFaceOpen (IncCoeffRing E) V (chartFace σ) ≤ ⊤)).op x).symm

end GlobalCharts

end BPFixedPoints.Multigraph
