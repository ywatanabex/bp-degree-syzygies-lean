import BPFixedPoints.Incidence.IncidenceUniversalKoszulExact
import BPFixedPoints.Incidence.IncidenceProjectiveZeroAtlas
import BPFixedPoints.Incidence.IncidenceProjectiveZeroSections
import BPFixedPoints.Incidence.EdgeExteriorDegreeZero

/-! # The augmentation of the universal Koszul complex: `K_G` resolves `i_* O_{Z_G}`

Let `S_G = IncCoeffRing E`, `Y = vertexScheme S_G V = (ℙ¹)^V × Spec S_G`, and let
`i = incidenceProjectiveZeroι : Z_G ⟶ Y` be the closed immersion of the independent projective zero
scheme. Its target is literally `ProjectiveLine.vertexScheme (IncCoeffRing E) V`, the scheme on
which `K_G = incUniversalKoszulComplex` lives, so the comparison of ambient schemes over `S_G` is
the identity. The existing comparison `incidenceProjectiveZeroIso` with the glued incidence scheme
is used only for global sections, in `IncidenceKoszulAugmentationGlobal.lean`.

* **Structure map.** For a morphism of schemes `f : X ⟶ Y`, `schemeStructurePushforward f` is the
  morphism of sheaves of `O_Y`-modules `O_Y ⟶ f_* O_X` given on sections by `f.app`
  (`schemeStructurePushforward_app`). For a closed immersion it is an epimorphism
  (`schemeStructurePushforward_epi`), since `f.app` is surjective on affine opens.
* **`∧^0 F^∨ ≅ O`.** The map `exteriorZeroUnitMap : O ⟶ ∧^0 F^∨`, `r ↦ r · 1` with the existing
  unit section, is an isomorphism (`exteriorZeroUnitIso`): it is injective on all sections and
  surjective on chart subopens, checked in the chart frames.
* **The augmentation.** `incKoszulAugmentation : ∧^0 F_G^∨ ⟶ i_* O_{Z_G}` is the inverse of that
  isomorphism followed by the structure map. On every subopen of a chart it is `i^*` of the chart
  coordinate (`incKoszulAugmentation_chart`).
* **Charts of `Z_G`.** The chart `incidenceProjectiveZeroChartToScheme σ` of `Z_G` has image
  `i⁻¹ U_σ` (`incidenceProjectiveZeroChartToScheme_opensRange`, from the existing pullback square),
  so `Γ(Z_G, i⁻¹ U_σ) ≅ A_σ/(f_e)` (`incZeroChartSectionsIso`). In these coordinates `i^*` is the
  quotient map (`incZeroChartSectionsIso_app`, from the naturality of affine coordinates
  `affineOpenSectionsIsoAt_comap` and the ring identity
  `incidenceChartAmbient_facePolynomialEquiv`), and the augmentation is the existing chart
  augmentation `incUniversalKoszulChartAugmentation σ` (`incZeroChartSectionsIso_augmentation`).
* **The edge equations vanish.** The chart functions of the universal edge sections pull back to
  zero on `Z_G` (`incidenceProjectiveZeroι_app_edgeFaceSection`,
  `incidenceProjectiveZeroι_app_chartFunction`), hence `d ≫ ε = 0`
  (`univKoszulDifferential_incKoszulAugmentation`).
* **Exactness and the cokernel.** The sequence `∧^1 F_G^∨ ⟶ ∧^0 F_G^∨ ⟶ i_* O_{Z_G}` is exact in
  the abelian category of sheaves of modules (`incKoszulAugmentation_exact`) and `ε` is an
  epimorphism (`incKoszulAugmentation_epi`), so `ε` is a cokernel of `d`
  (`incKoszulAugmentationIsCokernel`, `incKoszulCokernelIso : coker d ≅ i_* O_{Z_G}`). The proof
  never computes sections of a sheaf cokernel. It proves that `∧^1 ⟶ ker ε` is locally surjective,
  on the basic opens `D(g)` of the charts. There the kernel of `i^*` is the value of the ideal
  sheaf of `Z_G` (`Scheme.IdealSheafData.ker_subschemeι_app`), which is the localization of its
  value on the chart (`map_ideal_basicOpen`); on the chart, that kernel is the image of `d` by the
  existing chart exactness (`exists_univKoszulDifferential_of_app_eq_zero`).
* **Quasi-isomorphism.** The chain map `incKoszulAugmentationChainMap : K_G ⟶ (i_* O_{Z_G})[0]`
  is a quasi-isomorphism (`incKoszulAugmentationChainMap_quasiIso`), from the above in degree zero
  and `incUniversalKoszulComplex_exactAt` in positive degrees. In particular
  `H_0(K_G) ≅ i_* O_{Z_G}` (`incUniversalKoszulHomologyZeroIso`).

Not proved here: statements about derived global sections or higher direct images of `K_G`; the
internal grading `S_G(-k)` is not part of these sheaf-level statements.
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

section AffineCoordinates

/-- **Affine coordinates are natural for morphisms of schemes.** Let `g : Spec B ⟶ Y` and
`f : Spec C ⟶ Z` be open immersions with images `F` and `U`, let `i : Z ⟶ Y` with
`U ≤ i⁻¹ F`, and let `θ : B ⟶ C` with `f ≫ i = Spec θ ≫ g`. Then pulling a function on `F` back
along `i`, restricting it to `U` and reading it in the coordinates of `f` is `θ` applied to its
coordinates for `g`. -/
theorem affineOpenSectionsIsoAt_comap {Y Z : Scheme.{0}} {B C : CommRingCat.{0}} (θ : B ⟶ C)
    (i : Z ⟶ Y) (g : Spec B ⟶ Y) (f : Spec C ⟶ Z) [IsOpenImmersion g] [IsOpenImmersion f]
    (hfac : f ≫ i = Spec.map θ ≫ g) (F : Y.Opens) (hF : g.opensRange = F)
    (U : Z.Opens) (hU : f.opensRange = U) (hUF : U ≤ i ⁻¹ᵁ F) :
    i.app F ≫ Z.presheaf.map (homOfLE hUF).op ≫ (affineOpenSectionsIsoAt C f U hU).hom =
      (affineOpenSectionsIsoAt B g F hF).hom ≫ θ := by
  subst hF hU
  simp only [affineOpenSectionsIsoAt, affineOpenSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    eqToIso_refl, Iso.op_refl, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp,
    openImageSectionsIso_hom]
  rw [Scheme.Hom.map_appLE_assoc, ← Scheme.Hom.comp_appLE_assoc, Category.assoc,
    ← Scheme.ΓSpecIso_naturality θ, ← Category.assoc]
  congr 1
  have h : ∀ (h : Spec C ⟶ Y) (_ : h = Spec.map θ ≫ g) (e : ⊤ ≤ h ⁻¹ᵁ g.opensRange),
      h.appLE g.opensRange ⊤ e =
        g.appLE g.opensRange ⊤ (by rw [g.preimage_opensRange]) ≫ (Spec.map θ).appTop := by
    rintro h rfl e
    change _ = _ ≫ (Spec.map θ).app ⊤
    rw [Scheme.Hom.app_eq_appLE (Spec.map θ), Scheme.Hom.appLE_comp_appLE]
    rfl
  exact h _ hfac _

end AffineCoordinates

section Structure

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- The structure map `O_Y ⟶ f_* O_X` of a morphism of schemes, as a morphism of sheaves of
`O_Y`-modules: on sections over `W` it is the comorphism `f.app W`. -/
noncomputable def schemeStructurePushforward :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :
        SheafOfModules Y.ringCatSheaf) :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun W => (1 : Γ(X, f ⁻¹ᵁ W.unop)), fun {W W'} i => by
      change X.presheaf.map _ (1 : Γ(X, f ⁻¹ᵁ W.unop)) = 1
      exact map_one _⟩

/-- On sections over `W`, the structure map is the comorphism `f.app W`. -/
theorem schemeStructurePushforward_app (W : Y.Opens) (r : Γ(Y, W)) :
    ((schemeStructurePushforward f).val.app (op W)).hom r = f.app W r := by
  exact mul_one (f.app W r)

end Structure

/-- **The structure map of a closed immersion is an epimorphism.** On every affine open the
comorphism of a closed immersion is surjective, and affine opens form a basis. -/
instance schemeStructurePushforward_epi {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Epi (schemeStructurePushforward f) := by
  apply schemeModules_epi_of_locally_surjective
  intro U s x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  obtain ⟨t, ht⟩ := f.app_surjective W hW
    (X.presheaf.map (homOfLE ((Opens.map f.base).map (homOfLE hWU)).le).op s)
  exact ⟨W, hWU, hxW, t, by rw [schemeStructurePushforward_app, ht]; rfl⟩

section UnitFrame

variable {R : Type} [CommRing R] {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E]
  [Fintype E] (G : Multigraph V E)

/-- The morphism `O ⟶ ∧^0 F^∨` sending a function `r` to `r` times the unit section of the
summand of the empty edge subset. -/
noncomputable def exteriorZeroUnitMap :
    SheafOfModules.unit (vertexScheme R V).ringCatSheaf ⟶ G.exteriorBundle R 0 :=
  (SheafOfModules.unitHomEquiv _).symm
    ⟨fun W => G.exteriorSectionUnit R W.unop,
      fun {_ _} i => G.exteriorSectionUnit_restrict R i.unop⟩

/-- On sections, the unit-section map multiplies the unit section. -/
theorem exteriorZeroUnitMap_app (W : (vertexScheme R V).Opens) (r : Γ(vertexScheme R V, W)) :
    ((G.exteriorZeroUnitMap (R := R)).val.app (op W)).hom r = r • G.exteriorSectionUnit R W :=
  rfl

/-- In every chart frame, the coordinate of `r` times the unit section is `r`. -/
theorem exteriorChartEquiv_zeroUnitMap (σ : V → Bool) (W : (vertexScheme R V).Opens)
    (hW : W ≤ univChartOpen R V σ) (r : Γ(vertexScheme R V, W)) (T : Set.powersetCard E 0) :
    G.exteriorChartEquiv 0 σ W hW (((G.exteriorZeroUnitMap (R := R)).val.app (op W)).hom r) T =
      r := by
  rw [exteriorZeroUnitMap_app, map_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : G.exteriorChartEquiv 0 σ W hW (G.exteriorSectionUnit R W) T = 1 :=
    G.exteriorChartCoordinates_unit R (vertexBooleanPivot V σ) W hW T
  rw [h1, mul_one]

/-- In every chart frame with an arbitrary pivot, the coordinate of `r` times the unit section
is `r`. -/
theorem exteriorChartCoordinates_zeroUnitMap (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) (r : Γ(vertexScheme R V, W)) (T : Set.powersetCard E 0) :
    G.exteriorChartCoordinates R σ W hW 0
        (((G.exteriorZeroUnitMap (R := R)).val.app (op W)).hom r) T = r := by
  rw [exteriorZeroUnitMap_app, map_smul, Pi.smul_apply, smul_eq_mul,
    exteriorChartCoordinates_unit, mul_one]

/-- The map `O ⟶ ∧^0 F^∨` is injective on sections over every open. -/
theorem exteriorZeroUnitMap_injective (W : (vertexScheme R V).Opens) :
    Function.Injective ((G.exteriorZeroUnitMap (R := R)).val.app (op W)).hom := by
  intro r r' h
  apply vertexSections_ext_of_charts (SheafOfModules.unit (vertexScheme R V).ringCatSheaf) W
  intro σ
  let W' := W ⊓ vertexChartOpen R V σ
  have key : ∀ s : Γ(vertexScheme R V, W),
      (vertexScheme R V).presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op s =
        G.exteriorChartCoordinates R σ W' inf_le_right 0
          ((G.exteriorBundle R 0).val.map (homOfLE (inf_le_left : W' ≤ W)).op
            (((G.exteriorZeroUnitMap (R := R)).val.app (op W)).hom s)) emptyEdgeSubset := by
    intro s
    rw [← PresheafOfModules.naturality_apply]
    exact (G.exteriorChartCoordinates_zeroUnitMap σ W' inf_le_right _ _).symm
  change (vertexScheme R V).presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op r =
    (vertexScheme R V).presheaf.map (homOfLE (inf_le_left : W' ≤ W)).op r'
  rw [key, key, h]

/-- The unit-section map is a monomorphism. -/
instance exteriorZeroUnitMap_mono : Mono (G.exteriorZeroUnitMap (R := R)) := by
  constructor
  intro Z g h hgh
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply G.exteriorZeroUnitMap_injective S.unop
  exact congrArg (fun k => (k.val.app S).hom x) hgh

/-- The unit-section map is an epimorphism: it is surjective on chart subopens. -/
instance exteriorZeroUnitMap_epi : Epi (G.exteriorZeroUnitMap (R := R)) := by
  apply schemeModules_epi_of_locally_surjective
  intro U s x hx
  obtain ⟨σ, y, hy⟩ := vertexChart_covers R V x
  let U' := U ⊓ vertexChartOpen R V σ
  refine ⟨U', inf_le_left, ⟨hx, ⟨y, hy⟩⟩, G.exteriorChartCoordinates R σ U' inf_le_right 0
    ((G.exteriorBundle R 0).val.map (homOfLE inf_le_left).op s) emptyEdgeSubset, ?_⟩
  apply (G.exteriorChartCoordinates R σ U' inf_le_right 0).injective
  funext T
  obtain rfl : T = emptyEdgeSubset := Subsingleton.elim _ _
  rw [exteriorChartCoordinates_zeroUnitMap]

/-- The unit-section map is an isomorphism. -/
instance exteriorZeroUnitMap_isIso : IsIso (G.exteriorZeroUnitMap (R := R)) :=
  isIso_of_mono_of_epi _

/-- **`∧^0 F^∨ ≅ O`**: the inverse of the unit-section map. -/
noncomputable def exteriorZeroUnitIso :
    SheafOfModules.unit (vertexScheme R V).ringCatSheaf ≅ G.exteriorBundle R 0 :=
  asIso (G.exteriorZeroUnitMap (R := R))

end UnitFrame

section Augmentation

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The ring-level identity relating the two chart presentations: exchanging coefficient
variables and face coordinates and then passing to the polynomial chart ring is the chart
identification `chartFaceRingEquiv` over `S_G`. -/
theorem incidenceChartAmbient_facePolynomialEquiv (σ : V → Bool)
    (p : FaceRing (IncCoeffRing E) (chartFace σ)) :
    (G.incidenceChartAmbientPolynomialEquiv σ).symm
        (facePolynomialEquiv ℂ (IncCoeffIdx E) (chartFace σ) p) =
      chartFaceRingEquiv (R := IncCoeffRing E) σ p := by
  let ψ : MvPolynomial V (IncCoeffRing E) →ₐ[ℂ] MvPolynomial V (IncCoeffRing E) :=
    (G.incidenceChartAmbientPolynomialEquiv σ).symm.toAlgHom.comp
      ((facePolynomialEquiv ℂ (IncCoeffIdx E) (chartFace σ)).toAlgHom.comp
        ((chartFaceRingEquiv (R := IncCoeffRing E) σ).symm.toAlgHom.restrictScalars ℂ))
  have hψ : ψ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext'
    · apply MvPolynomial.algHom_ext
      intro c
      change (G.incidenceChartAmbientPolynomialEquiv σ).symm
          (facePolynomialEquiv ℂ (IncCoeffIdx E) (chartFace σ)
            ((chartFaceRingEquiv (R := IncCoeffRing E) σ).symm (C (X c)))) = C (X c)
      rw [show (chartFaceRingEquiv (R := IncCoeffRing E) σ).symm (C (X c)) =
          algebraMap (IncCoeffRing E) (FaceRing (IncCoeffRing E) (chartFace σ)) (X c) from
        (chartFaceRingEquiv (R := IncCoeffRing E) σ).symm.commutes (X c),
        facePolynomialEquiv_algebraMap_X, AlgEquiv.symm_apply_eq,
        incidenceChartAmbientPolynomialEquiv_C_X]
    · intro v
      change (G.incidenceChartAmbientPolynomialEquiv σ).symm
          (facePolynomialEquiv ℂ (IncCoeffIdx E) (chartFace σ)
            ((chartFaceRingEquiv (R := IncCoeffRing E) σ).symm (X v))) = X v
      rw [show (chartFaceRingEquiv (R := IncCoeffRing E) σ).symm (X v) =
          faceVariable (IncCoeffRing E) (chartFace σ) v by
        rw [AlgEquiv.symm_apply_eq, chartFaceRingEquiv_variable],
        facePolynomialEquiv_faceVariable, AlgEquiv.symm_apply_eq,
        incidenceChartAmbientPolynomialEquiv_X]
  have h := congrArg (fun φ => φ (chartFaceRingEquiv (R := IncCoeffRing E) σ p)) hψ
  simpa [ψ] using h

/-- **`i_* O_{Z_G}`**: the pushforward of the structure sheaf of the independent projective zero
scheme `Z_G` along its closed immersion `i` into `Y = (ℙ¹)^V × B_G`, as a sheaf of
`O_Y`-modules. -/
noncomputable abbrev incZeroPushforward :
    SheafOfModules (vertexScheme (IncCoeffRing E) V).ringCatSheaf :=
  (Scheme.Modules.pushforward G.incidenceProjectiveZeroι).obj
    (SheafOfModules.unit G.incidenceProjectiveZeroScheme.ringCatSheaf)

/-- **The augmentation `ε : ∧^0 F_G^∨ ⟶ i_* O_{Z_G}`** of the universal Koszul complex: the
inverse of `O ≅ ∧^0 F_G^∨` followed by the structure map `O_Y ⟶ i_* O_{Z_G}`. -/
noncomputable def incKoszulAugmentation :
    G.exteriorBundle (IncCoeffRing E) 0 ⟶ G.incZeroPushforward :=
  inv (G.exteriorZeroUnitMap (R := IncCoeffRing E)) ≫
    schemeStructurePushforward G.incidenceProjectiveZeroι

/-- **The augmentation in a chart frame.** On every subopen `W` of the chart `σ`, the augmentation
of a section is the pullback along `i` of its chart coordinate. -/
theorem incKoszulAugmentation_chart (σ : V → Bool) (W : (vertexScheme (IncCoeffRing E) V).Opens)
    (hW : W ≤ univChartOpen (IncCoeffRing E) V σ)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, W)) :
    ((G.incKoszulAugmentation).val.app (op W)).hom x =
      G.incidenceProjectiveZeroι.app W
        (G.exteriorChartEquiv 0 σ W hW x (powersetCardEmpty E)) := by
  let φ := G.exteriorZeroUnitMap (R := IncCoeffRing E)
  obtain ⟨r, rfl⟩ : ∃ r, (φ.val.app (op W)).hom r = x :=
    ⟨((inv φ).val.app (op W)).hom x,
      congrArg (fun k => (k.val.app (op W)).hom x) (IsIso.inv_hom_id φ)⟩
  rw [exteriorChartEquiv_zeroUnitMap]
  have hr : ((inv φ).val.app (op W)).hom ((φ.val.app (op W)).hom r) = r :=
    congrArg (fun k => (k.val.app (op W)).hom r) (IsIso.hom_inv_id φ)
  change ((schemeStructurePushforward G.incidenceProjectiveZeroι).val.app (op W)).hom
    (((inv φ).val.app (op W)).hom ((φ.val.app (op W)).hom r)) = _
  rw [hr, schemeStructurePushforward_app]

/-- The chart `σ` of `Z_G` is the inverse image under `i` of the chart open `σ` of `Y`. -/
theorem incidenceProjectiveZeroChartToScheme_opensRange (σ : V → Bool) :
    (G.incidenceProjectiveZeroChartToScheme σ).opensRange =
      G.incidenceProjectiveZeroι ⁻¹ᵁ univFaceOpen (IncCoeffRing E) V (chartFace σ) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (G.incidenceProjectiveZeroChart_isPullback σ) ⊤
  rw [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange] at h
  rw [h, univFaceOpen_chartFace]
  rfl

/-- **Coordinates of `i_* O_{Z_G}` on a chart.** The functions on the inverse image of the
chart `σ` in `Z_G` are the chart ring `IncidenceProjectiveZeroChartRing σ = A_σ/(f_e)` of the
zero scheme, through its chart `incidenceProjectiveZeroChartToScheme σ`. -/
noncomputable def incZeroChartSectionsIso (σ : V → Bool) :
    Γ(G.incidenceProjectiveZeroScheme,
        G.incidenceProjectiveZeroι ⁻¹ᵁ univFaceOpen (IncCoeffRing E) V (chartFace σ)) ≅
      CommRingCat.of (G.IncidenceProjectiveZeroChartRing σ) :=
  affineOpenSectionsIsoAt _ (G.incidenceProjectiveZeroChartToScheme σ) _
    (G.incidenceProjectiveZeroChartToScheme_opensRange σ)

/-- The chart map of `Z_G` into `Y` is the quotient map of chart rings followed by the face chart
of `Y`. -/
theorem incidenceProjectiveZeroChartToScheme_ι_face (σ : V → Bool) :
    G.incidenceProjectiveZeroChartToScheme σ ≫ G.incidenceProjectiveZeroι =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ)).comp
        (chartFaceRingEquiv (R := IncCoeffRing E) σ).toRingEquiv.toRingHom)) ≫
        vertexFaceι (IncCoeffRing E) V (chartFace σ) := by
  rw [G.incidenceProjectiveZeroChartToScheme_ι, incidenceProjectiveZeroChartι,
    ← vertexFaceι_chart, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change Ideal.Quotient.mk _ p = Ideal.Quotient.mk _
    ((chartFaceRingEquiv (R := IncCoeffRing E) σ)
      ((chartFaceRingEquiv (R := IncCoeffRing E) σ).symm p))
  rw [AlgEquiv.apply_symm_apply]

/-- **Pullback of functions along `i` on a chart.** Pulling a function on the chart `σ` of `Y`
back to `Z_G` and reading it in the chart ring of `Z_G` is the quotient class of its polynomial
chart coordinate. -/
theorem incZeroChartSectionsIso_app (σ : V → Bool)
    (s : Γ(vertexScheme (IncCoeffRing E) V, univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    (G.incZeroChartSectionsIso σ).hom
        (G.incidenceProjectiveZeroι.app (univFaceOpen (IncCoeffRing E) V (chartFace σ)) s) =
      Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ)
        (chartFaceRingEquiv (R := IncCoeffRing E) σ
          (vertexFaceSectionsEquiv (IncCoeffRing E) V (chartFace σ) s)) := by
  have h := affineOpenSectionsIsoAt_comap
    (B := CommRingCat.of (FaceRing (IncCoeffRing E) (chartFace σ)))
    (C := CommRingCat.of (G.IncidenceProjectiveZeroChartRing σ))
    (CommRingCat.ofHom ((Ideal.Quotient.mk (G.incidenceProjectiveChartIdeal σ)).comp
      (chartFaceRingEquiv (R := IncCoeffRing E) σ).toRingEquiv.toRingHom))
    G.incidenceProjectiveZeroι (vertexFaceι (IncCoeffRing E) V (chartFace σ))
    (G.incidenceProjectiveZeroChartToScheme σ) (G.incidenceProjectiveZeroChartToScheme_ι_face σ)
    _ (vertexFaceι_opensRange (IncCoeffRing E) V (chartFace σ)) _
    (G.incidenceProjectiveZeroChartToScheme_opensRange σ) le_rfl
  have h' := congrArg (fun k => k.hom s) h
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  exact h'

/-- **The edge equations vanish on `Z_G`.** The face section of the universal edge section on the
chart `σ` pulls back to zero on `Z_G`. -/
theorem incidenceProjectiveZeroι_app_edgeFaceSection (σ : V → Bool) (e : E) :
    G.incidenceProjectiveZeroι.app (univFaceOpen (IncCoeffRing E) V (chartFace σ))
      ((vertexFaceSectionsEquiv (IncCoeffRing E) V (chartFace σ)).symm
        (G.edgeFaceSection X e (chartFace σ))) = 0 := by
  apply (G.incZeroChartSectionsIso σ).commRingCatIsoToRingEquiv.injective
  change (G.incZeroChartSectionsIso σ).hom _ = (G.incZeroChartSectionsIso σ).hom 0
  rw [incZeroChartSectionsIso_app, RingEquiv.apply_symm_apply, map_zero,
    ← incidenceChartAmbient_facePolynomialEquiv, facePolynomialEquiv_edgeFaceSection,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨e, rfl⟩

/-- Pullback along a morphism of schemes kills restrictions of functions it kills. -/
theorem scheme_app_restrict_eq_zero {X Y : Scheme.{0}} (f : X ⟶ Y) {U W : Y.Opens} (h : W ≤ U)
    (s : Γ(Y, U)) (hs : f.app U s = 0) : f.app W (Y.presheaf.map (homOfLE h).op s) = 0 := by
  have hn := congrArg (fun k => k.hom s) (f.naturality (homOfLE h).op)
  change f.app W (Y.presheaf.map (homOfLE h).op s) =
    X.presheaf.map _ (f.app U s) at hn
  rw [hn, hs, map_zero]

/-- On every subopen of a chart, the chart functions of the universal edge sections pull back to
zero on `Z_G`. -/
theorem incidenceProjectiveZeroι_app_chartFunction (σ : V → Bool) (e : E)
    (W : (vertexScheme (IncCoeffRing E) V).Opens) (hW : W ≤ univChartOpen (IncCoeffRing E) V σ) :
    G.incidenceProjectiveZeroι.app W ((vertexScheme (IncCoeffRing E) V).presheaf.map
      (homOfLE hW).op (twistChartFunction (G.edgeFaceSection X e) σ)) = 0 := by
  rw [twistChartFunction, univPresheaf_restrict_restrict _ _
    (homOfLE (hW.trans (univChartOpen_le_chartFace (IncCoeffRing E) V σ)))]
  exact scheme_app_restrict_eq_zero _ _ _ (G.incidenceProjectiveZeroι_app_edgeFaceSection σ e)

/-- The augmentation is an epimorphism of sheaves of modules. -/
instance incKoszulAugmentation_epi : Epi G.incKoszulAugmentation := by
  unfold incKoszulAugmentation
  infer_instance

/-- **The augmentation kills the boundaries**: `d ≫ ε = 0`, because the chart functions of the
universal edge sections pull back to zero on `Z_G`. -/
theorem univKoszulDifferential_incKoszulAugmentation :
    G.univKoszulDifferential (R := IncCoeffRing E) X 0 ≫ G.incKoszulAugmentation = 0 := by
  apply moduleHom_ext_of_cover (vertexScheme (IncCoeffRing E) V) _ _
    (univChartOpen (IncCoeffRing E) V) (univChartOpen_iSup_top (IncCoeffRing E) V)
  intro σ
  rw [Functor.map_zero]
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((G.incKoszulAugmentation).val.app (op S.unop.left)).hom
    (((G.univKoszulDifferential (R := IncCoeffRing E) X 0).val.app (op S.unop.left)).hom x) = 0
  rw [G.incKoszulAugmentation_chart σ _ S.unop.hom.le, univKoszulDifferential_chart,
    gradedKoszul_zero_apply, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [map_mul, G.incidenceProjectiveZeroι_app_chartFunction σ e _ S.unop.hom.le, zero_mul]

/-- **Chart values of the augmentation.** On the chart `σ`, the augmentation read in the chart
ring `A_σ/(f_e)` of `Z_G` is the existing chart augmentation
`incUniversalKoszulChartAugmentation σ` of `IncidenceUniversalKoszulFaces.lean`. -/
theorem incZeroChartSectionsIso_augmentation (σ : V → Bool)
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, univFaceOpen (IncCoeffRing E) V (chartFace σ))) :
    (G.incZeroChartSectionsIso σ).hom (((G.incKoszulAugmentation).val.app
        (op (univFaceOpen (IncCoeffRing E) V (chartFace σ)))).hom x) =
      G.incUniversalKoszulChartAugmentation σ x := by
  rw [G.incKoszulAugmentation_chart σ _ (univFaceOpen_chartFace (IncCoeffRing E) V σ).le,
    incZeroChartSectionsIso_app, incUniversalKoszulChartAugmentation_apply,
    incUnivChartKoszulEquiv_apply, incUnivFaceKoszulEquiv_apply,
    incidenceChartAmbient_facePolynomialEquiv, exteriorFaceEquiv_apply, twistFaceCoordinate_apply,
    exteriorChartEquiv_apply]
  congr 3
  exact univTwistChartCoefficient_congr _
    (congrArg (vertexBooleanPivot V) (vertexFaceBaseChoice_chartFace σ)).symm _ _ _ _

/-- Chart coordinates of the exterior bundles commute with restriction. -/
theorem exteriorChartEquiv_restrict (k : ℕ) (σ : V → Bool)
    {W U : (vertexScheme (IncCoeffRing E) V).Opens} (hWU : W ≤ U)
    (hU : U ≤ univChartOpen (IncCoeffRing E) V σ) (x : Γ(G.exteriorBundle (IncCoeffRing E) k, U))
    (S : Set.powersetCard E k) :
    G.exteriorChartEquiv k σ W (hWU.trans hU)
        ((G.exteriorBundle (IncCoeffRing E) k).val.map (homOfLE hWU).op x) S =
      (vertexScheme (IncCoeffRing E) V).presheaf.map (homOfLE hWU).op
        (G.exteriorChartEquiv k σ U hU x S) := by
  rw [exteriorChartEquiv_apply, exteriorChartEquiv_apply,
    ← vertexTwistSheafChartCoefficient_restrict]
  congr 1
  exact PresheafOfModules.naturality_apply (biproduct.π (C := SheafOfModules _)
    (fun S : Set.powersetCard E k => G.exteriorSummand (IncCoeffRing E) S) S).val
      (homOfLE hWU).op x

/-- **On a chart, every function killed by `i` is a boundary.** If a function `c` on the chart
`σ` pulls back to zero on `Z_G`, it is the chart coordinate of `d y` for a section `y` of
`∧^1 F_G^∨` on the chart. This uses the existing chart exactness
`incUniversalKoszulChartAugmentation_exact`. -/
theorem exists_univKoszulDifferential_of_app_eq_zero (σ : V → Bool)
    (c : Γ(vertexScheme (IncCoeffRing E) V, univFaceOpen (IncCoeffRing E) V (chartFace σ)))
    (hc : G.incidenceProjectiveZeroι.app (univFaceOpen (IncCoeffRing E) V (chartFace σ)) c = 0) :
    ∃ y : Γ(G.exteriorBundle (IncCoeffRing E) 1, univFaceOpen (IncCoeffRing E) V (chartFace σ)),
      G.exteriorChartEquiv 0 σ _ (univFaceOpen_chartFace (IncCoeffRing E) V σ).le
        (((G.univKoszulDifferential (R := IncCoeffRing E) X 0).val.app
          (op (univFaceOpen (IncCoeffRing E) V (chartFace σ)))).hom y)
        (powersetCardEmpty E) = c := by
  let x0 := ((G.exteriorZeroUnitMap (R := IncCoeffRing E)).val.app
    (op (univFaceOpen (IncCoeffRing E) V (chartFace σ)))).hom c
  have hx0 : G.incUniversalKoszulChartAugmentation σ x0 = 0 := by
    rw [← incZeroChartSectionsIso_augmentation,
      G.incKoszulAugmentation_chart σ _ (univFaceOpen_chartFace (IncCoeffRing E) V σ).le,
      exteriorChartEquiv_zeroUnitMap, hc, map_zero]
  obtain ⟨y, hy⟩ := (G.incUniversalKoszulChartAugmentation_exact σ x0).mp hx0
  exact ⟨y, by rw [hy, exteriorChartEquiv_zeroUnitMap]⟩

set_option maxHeartbeats 1000000 in
/-- **Exactness of `∧^1 F_G^∨ ⟶ ∧^0 F_G^∨ ⟶ i_* O_{Z_G}`** in the abelian category of sheaves of
modules. A section killed by the augmentation is, near every point, a boundary: on a basic open
`D(g)` of a chart, the kernel of the pullback of functions along the closed immersion `i` is the
localization of its kernel on the chart (`IdealSheafData.map_ideal_basicOpen`), and on the chart
it is the image of `d` (`exists_univKoszulDifferential_of_app_eq_zero`). -/
theorem incKoszulAugmentation_exact :
    (ShortComplex.mk (G.univKoszulDifferential (R := IncCoeffRing E) X 0) G.incKoszulAugmentation
      G.univKoszulDifferential_incKoszulAugmentation).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  apply schemeModules_epi_of_locally_surjective
  intro U s x hx
  let Y := vertexScheme (IncCoeffRing E) V
  let I := G.incidenceProjectiveZeroIdeal
  let i := G.incidenceProjectiveZeroι
  have hi : i = I.subschemeι := rfl
  let ε := G.incKoszulAugmentation
  let d := G.univKoszulDifferential (R := IncCoeffRing E) X 0
  let z := ((kernel.ι ε).val.app (op U)).hom s
  have hz : (ε.val.app (op U)).hom z = 0 := kernel_ι_app_comp ε (op U) s
  obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (univChartOpen_iSup_top (IncCoeffRing E) V (show x ∈ (⊤ : Y.Opens) from trivial))
  let F := univFaceOpen (IncCoeffRing E) V (chartFace σ)
  have hFσ : F = univChartOpen (IncCoeffRing E) V σ := univFaceOpen_chartFace (IncCoeffRing E) V σ
  have hFaff : IsAffineOpen F := by
    rw [hFσ]
    exact univChartOpen_isAffineOpen (IncCoeffRing E) σ
  have hxF : x ∈ F := by
    rw [hFσ]
    exact hσ
  obtain ⟨g, hgU, hxg⟩ := hFaff.exists_basicOpen_le (V := U) ⟨x, hx⟩ hxF
  let W := Y.basicOpen g
  have hWF : W ≤ F := Y.basicOpen_le g
  have hWσ : W ≤ univChartOpen (IncCoeffRing E) V σ := hWF.trans hFσ.le
  let zW := (G.exteriorBundle (IncCoeffRing E) 0).val.map (homOfLE hgU).op z
  let c := G.exteriorChartEquiv 0 σ W hWσ zW (powersetCardEmpty E)
  have hc : i.app W c = 0 := by
    rw [← G.incKoszulAugmentation_chart σ W hWσ zW]
    change (ε.val.app (op W)).hom zW = 0
    erw [PresheafOfModules.naturality_apply]
    rw [hz, map_zero]
  have hker : c ∈ (RingHom.ker (i.app F).hom).map
      (Y.presheaf.map (homOfLE hWF).op).hom := by
    have h1 : c ∈ RingHom.ker (I.subschemeι.app
        (Y.affineBasicOpen (U := ⟨F, hFaff⟩) g : Y.Opens)).hom := hc
    rw [Scheme.IdealSheafData.ker_subschemeι_app,
      ← I.map_ideal_basicOpen ⟨F, hFaff⟩ g,
      ← Scheme.IdealSheafData.ker_subschemeι_app] at h1
    exact h1
  let δ : Γ(G.exteriorBundle (IncCoeffRing E) 1, W) →ₗ[Γ(Y, W)] Γ(Y, W) :=
    (LinearMap.proj (powersetCardEmpty E)).comp
      ((G.exteriorChartEquiv 0 σ W hWσ).toLinearMap.comp (d.val.app (op W)).hom)
  have hT : (RingHom.ker (i.app F).hom).map (Y.presheaf.map (homOfLE hWF).op).hom ≤
      LinearMap.range δ := by
    rw [Ideal.map_le_iff_le_comap]
    intro c0 hc0
    obtain ⟨y0, hy0⟩ := G.exists_univKoszulDifferential_of_app_eq_zero σ c0 hc0
    refine ⟨(G.exteriorBundle (IncCoeffRing E) 1).val.map (homOfLE hWF).op y0, ?_⟩
    change G.exteriorChartEquiv 0 σ W hWσ ((d.val.app (op W)).hom
      ((G.exteriorBundle (IncCoeffRing E) 1).val.map (homOfLE hWF).op y0)) _ = _
    rw [PresheafOfModules.naturality_apply]
    rw [G.exteriorChartEquiv_restrict 0 σ hWF (univFaceOpen_chartFace (IncCoeffRing E) V σ).le,
      hy0]
  obtain ⟨y, hy⟩ := hT hker
  have hdy : (d.val.app (op W)).hom y = zW := by
    apply (G.exteriorChartEquiv 0 σ W hWσ).injective
    funext T
    obtain rfl : T = powersetCardEmpty E := Subsingleton.elim _ _
    exact hy
  refine ⟨W, hgU, hxg, y, ?_⟩
  apply kernel_ι_app_injective ε
  have hl : ((kernel.ι ε).val.app (op W)).hom
      (((kernel.lift ε d G.univKoszulDifferential_incKoszulAugmentation).val.app (op W)).hom y) =
      (d.val.app (op W)).hom y :=
    congrArg (fun φ => (φ.val.app (op W)).hom y)
      (kernel.lift_ι ε d G.univKoszulDifferential_incKoszulAugmentation)
  rw [hl]
  erw [PresheafOfModules.naturality_apply]
  exact hdy

/-- **`coker(d) ≅ i_* O_{Z_G}`**: the augmentation is a cokernel of the last differential
`d : ∧^1 F_G^∨ ⟶ ∧^0 F_G^∨` of `K_G`. -/
noncomputable def incKoszulAugmentationIsCokernel :
    IsColimit (CokernelCofork.ofπ G.incKoszulAugmentation
      G.univKoszulDifferential_incKoszulAugmentation) :=
  G.incKoszulAugmentation_exact.gIsCokernel

/-- The cokernel sheaf of the last differential of `K_G` is `i_* O_{Z_G}`. -/
noncomputable def incKoszulCokernelIso :
    cokernel (G.univKoszulDifferential (R := IncCoeffRing E) X 0) ≅ G.incZeroPushforward :=
  (colimit.isColimit _).coconePointUniqueUpToIso G.incKoszulAugmentationIsCokernel

/-- The cokernel identification sends the cokernel projection to the augmentation. -/
@[reassoc] theorem cokernel_π_incKoszulCokernelIso :
    cokernel.π (G.univKoszulDifferential (R := IncCoeffRing E) X 0) ≫ G.incKoszulCokernelIso.hom =
      G.incKoszulAugmentation :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- The last differential of `K_G` followed by the augmentation is zero, in the form needed for a
chain map to a complex concentrated in degree zero. -/
theorem incUniversalKoszulComplex_d_augmentation :
    G.incUniversalKoszulComplex.d 1 0 ≫ G.incKoszulAugmentation = 0 := by
  have h : G.incUniversalKoszulComplex.d 1 0 = G.univKoszulDifferential (R := IncCoeffRing E) X 0 :=
    G.univKoszulComplex_d _ 0
  rw [h]
  exact G.univKoszulDifferential_incKoszulAugmentation

/-- **The augmentation as a chain map** `K_G ⟶ (i_* O_{Z_G})[0]`. -/
noncomputable def incKoszulAugmentationChainMap :
    G.incUniversalKoszulComplex ⟶
      (ChainComplex.single₀ (SheafOfModules (vertexScheme (IncCoeffRing E) V).ringCatSheaf)).obj
        G.incZeroPushforward :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨G.incKoszulAugmentation, G.incUniversalKoszulComplex_d_augmentation⟩

/-- In degree zero the chain map is the augmentation. -/
theorem incKoszulAugmentationChainMap_f_zero :
    G.incKoszulAugmentationChainMap.f 0 = G.incKoszulAugmentation :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- **`K_G` resolves `i_* O_{Z_G}`**: the augmentation `K_G ⟶ (i_* O_{Z_G})[0]` is a
quasi-isomorphism of complexes of sheaves of modules on `(ℙ¹)^V × B_G`. In degree zero this is the
exactness of `∧^1 ⟶ ∧^0 ⟶ i_* O_{Z_G} ⟶ 0` (`incKoszulAugmentation_exact` and the epimorphism
`incKoszulAugmentation_epi`), and in positive degrees it is `incUniversalKoszulComplex_exactAt`. -/
instance incKoszulAugmentationChainMap_quasiIso : QuasiIso G.incKoszulAugmentationChainMap where
  quasiIsoAt n := by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨(ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        (Iso.refl _) ?_ ?_)).2 G.incKoszulAugmentation_exact, ?_⟩
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      · change Epi (G.incKoszulAugmentationChainMap.f 0)
        rw [incKoszulAugmentationChainMap_f_zero]
        infer_instance
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact G.incUniversalKoszulComplex_exactAt n
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- **`H_0(K_G) ≅ i_* O_{Z_G}`**, from the quasi-isomorphism. -/
noncomputable def incUniversalKoszulHomologyZeroIso :
    G.incUniversalKoszulComplex.homology 0 ≅ G.incZeroPushforward :=
  haveI := G.incKoszulAugmentationChainMap_quasiIso.quasiIsoAt 0
  isoOfQuasiIsoAt G.incKoszulAugmentationChainMap 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ _ _

end Augmentation

end BPFixedPoints.Multigraph
