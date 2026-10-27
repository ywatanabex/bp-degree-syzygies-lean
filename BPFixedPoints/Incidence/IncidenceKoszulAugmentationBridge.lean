import BPFixedPoints.Incidence.IncidenceKoszulAugmentationGlobal
import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedLinear

/-! # The two identifications of `H^0(K_G)` with `𝒰_G` agree

There are two routes from the universal Koszul complex `K_G` on `Y = (ℙ¹)^V × B_G` to the
incidence ring `𝒰_G`:

* **Čech route** (`incUniversalKoszulHypercohomologyZeroEquiv`, its `S_G`-linear form
  `incUniversalKoszulHypercohomologyZeroLinearEquiv`): `H^0(K_G)`, a morphism `ℤ_Y[0] ⟶ K_G` in the
  derived category, is a Hom-complex class from the cubical cell resolution of `ℤ_Y`
  (`incUniversalKoszulHypercohomologyEquiv`), hence a degree-zero cycle of the Čech–Koszul total
  complex (`cocycleZeroToCycles`), sent to `𝒰_G` by `univCechKoszulAugmentation`: the torus value
  of the face augmentation of its `∅`-component on the all-left chart.
* **Sheaf route**: the augmentation `ε = incKoszulAugmentation : ∧^0 F_G^∨ ⟶ i_* O_{Z_G}`, the
  identification of degree-zero cohomology of a sheaf with its global sections, and
  `incidenceProjectiveZeroGlobalSectionsEquiv : Γ(Z_G, O) ≅ 𝒰_G`.

**Definition of the sheaf-route map** (`incUniversalKoszulHypercohomologyZeroSections`). The
augmentation, as a morphism of abelian sheaves, is a cochain map
`incKoszulAugmentationCochainMap : K_G ⟶ (i_* O_{Z_G})[0]` (its degree-zero component is `ε`). A
class `x ∈ H^0(K_G)` goes to `x ≫ Q(ε)`, a morphism `ℤ_Y[0] ⟶ (i_* O_{Z_G})[0]` in the derived
category, i.e. an element of Mathlib's sheaf cohomology `H^0(Y, i_* O_{Z_G})`
(`sheafHypercohomologySingleEquiv`), and then to its global section by Mathlib's
`Sheaf.H.equiv₀`. The global sections of `i_* O_{Z_G}` over `Y` are `Γ(Z_G, O)`.

**Main results.**
* *Hypercohomology level* (`incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections`
  and its linear form `..._linear`, `..._comp`): the composite
  `H^0(K_G) → Γ(Z_G, O) ≅ 𝒰_G` equals `incUniversalKoszulHypercohomologyZeroEquiv` (and
  `incUniversalKoszulHypercohomologyZeroLinearEquiv`). Consequently the sheaf-route map is
  bijective (`incUniversalKoszulHypercohomologyZeroSections_bijective`) and semilinear over the
  coefficient map `S_G → Γ(Z_G, O)` (`incUniversalKoszulHypercohomologyZeroSections_smul`).
* *Section level* (`incKoszulAugmentation_globalSections_univCech`): for a global section `x` of
  `∧^0 F_G^∨` and a degree-zero Čech–Koszul cycle `c` whose `∅`-component on the all-left chart is
  the restriction of `x`, `incidenceProjectiveZeroGlobalSectionsEquiv (ε_⊤ x) =
  univCechKoszulAugmentation c`. Its chart form
  (`incidenceProjectiveZeroGlobalSectionsEquiv_eq_univCechKoszulAugmentation`) only asks that the
  restriction of a global function of `Z_G` to the all-left chart be `ε` of a section `y` whose
  `∅`-component is the chart component of `c`; this is the form used for the hypercohomology level.

**Proof of the hypercohomology level.** For a degree-zero cocycle `z` from the cell resolution
`P ⟶ ℤ_Y` to `K_G`, the postcomposite with `K_G ⟶ (i_* O_{Z_G})[0]` is the class of
`P ⟶ ℤ_Y[0] ⟶ (i_* O_{Z_G})[0]`, where `h : ℤ_Y ⟶ i_* O_{Z_G}` is the factorization of
`ε ∘ z_{0,0}` through the cokernel `P_0 ⟶ ℤ_Y` (`incCocycleSectionMap`, `incCocycle_postcomp_eq`).
The derived comparison sends such a class to `Q(h)` (`derivedCohomologyClassHom_mk_equivHomShift`,
`derivedCohomologyClassHom_single_augmentation`), and `H^0` sends `Q(h)` to the global section
represented by `h` (`incUniversalKoszulHypercohomologyZeroSections_mk`). On the all-left chart this
section restricts to `ε` of the chart section of `z_{0,0}` (`sectionsEquiv_augmentation_comp`),
which is what the Čech route evaluates.

Not proved here: comparisons in nonzero degrees (all vanish on both sides) or with
`RΓ(Z_G, O_{Z_G})`.
-/

namespace BPFixedPoints.SheafTools.BinaryCells

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- Before sheafification, the generator of a vertex cell followed by the augmentation is the map
of free presheaves induced by the inclusion of the vertex open into the whole space. -/
theorem presheafGenerator_vertexCell_augmentation (b : V → Fin 2) :
    presheafGenerator U (vertexCell b) ≫ presheafAugmentation U =
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
        (yoneda.map (homOfLE (le_top : binaryCoverFaceOpen U (vertexCell b).val ≤ ⊤))) := by
  rw [presheafAugmentation, ← Category.assoc, Iso.comp_inv_eq]
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  change (CechCubicalCell.contraction ℤ (fun _ : V => 0)).p
      ((presheafGenerator U (vertexCell b)).app W (FreeAbelianGroup.of i)).val =
    topComponentEquiv (V := V) W.unop (FreeAbelianGroup.map _ (FreeAbelianGroup.of i))
  rw [presheafGenerator_app_of_val, FreeAbelianGroup.map_of_apply, topComponentEquiv_of]
  exact component_projection_vertex b 1

/-- The generator of a vertex cell followed by the augmentation is the map of free sheaves
induced by the inclusion of the vertex open into the whole space. -/
theorem generator_vertexCell_augmentation (b : V → Fin 2) :
    generator U (vertexCell b) ≫ augmentation U =
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (yoneda.map (homOfLE (le_top : binaryCoverFaceOpen U (vertexCell b).val ≤ ⊤)))) := by
  rw [generator, augmentation, ← Functor.map_comp, presheafGenerator_vertexCell_augmentation]

/-- The vertex-cell section of a degree-zero cochain that factors through the augmentation by
`h` is the restriction of the global section represented by `h`. -/
theorem sectionsEquiv_augmentation_comp
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (h : (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶ F) (b : V → Fin 2) :
    sectionsEquiv U F 0 (augmentation U ≫ h) (vertexCell b) =
      F.obj.map (homOfLE (le_top : binaryCoverFaceOpen U (vertexCell b).val ≤ ⊤)).op
        (freeSheafSectionsEquiv F ⊤ h) := by
  rw [sectionsEquiv_apply, ← Category.assoc, generator_vertexCell_augmentation,
    freeSheafSectionsEquiv_naturality]

end BPFixedPoints.SheafTools.BinaryCells

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape
open BPFixedPoints.ExtResolutionTools CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

universe w v u

/-! ### The derived comparison on classes of chain maps -/

section DerivedClass

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (hπ : P.d 1 0 ≫ π = 0)
  (e : (ShortComplex.mk (P.d 1 0) π hπ).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n + 1))

/-- **The derived comparison on the class of a chain map** `f : P ⟶ L⟦n⟧` from the negative
complex of the resolution: it is `Q(f)`, read through the augmentation isomorphism and the
commutation of `Q` with shifts. -/
theorem derivedCohomologyClassHom_mk_equivHomShift (L : CochainComplex C ℤ) (n : ℤ)
    (f : negativeComplex P ⟶ L⟦n⟧) :
    derivedCohomologyClassHom P π hπ e hP L n (CohomologyClass.mk (Cocycle.equivHomShift f)) =
      (nativeAugmentationIso P π hπ e hP).inv ≫ DerivedCategory.Q.map f ≫
        (DerivedCategory.Q.commShiftIso n).hom.app L := by
  change (Iso.homCongr _ _) (DerivedCategory.Qh.map ((Iso.homCongr _ _)
    (CohomologyClass.toHom (CohomologyClass.mk (Cocycle.equivHomShift f))))) = _
  rw [CohomologyClass.toHom_mk, AddEquiv.symm_apply_apply]
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Iso.trans_inv, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  congr 1
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  congr 1
  have h := NatTrans.shift_app_comm (DerivedCategory.quotientCompQhIso C).hom n L
  rw [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  rw [h, Iso.inv_hom_id_app_assoc]

/-- **The derived comparison of an augmentation class in degree zero.** The class of
`P ⟶ A[0] ⟶ B[0]`, the augmentation followed by `h : A ⟶ B`, goes to `Q(h)`. -/
theorem derivedCohomologyClassHom_single_augmentation {B : C} (h : A ⟶ B) :
    derivedCohomologyClassHom P π hπ e hP ((CochainComplex.singleFunctor C 0).obj B) 0
      (CohomologyClass.mk (Cocycle.equivHomShift (negativeAugmentation P π hπ ≫
        (CochainComplex.singleFunctor C 0).map h ≫
          (shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app
            ((CochainComplex.singleFunctor C 0).obj B)))) =
      ShiftedHom.mk₀ (0 : ℤ) rfl
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map h)) := by
  rw [derivedCohomologyClassHom_mk_equivHomShift, Functor.map_comp, Functor.map_comp,
    show DerivedCategory.Q.map (negativeAugmentation P π hπ) =
      (nativeAugmentationIso P π hπ e hP).hom from rfl, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
  have hz : DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app
        ((CochainComplex.singleFunctor C 0).obj B)) ≫
      DerivedCategory.Q.map ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app
        ((CochainComplex.singleFunctor C 0).obj B)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [reassoc_of% hz]
  simp [ShiftedHom.mk₀, shiftFunctorZero']

end DerivedClass

/-! ### The section-level comparison -/

section Sections

open AlgebraicGeometry TopologicalSpace Opposite CechProduct ProjectiveLine SheafTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The all-left chart, the chart of the augmentation `univCechKoszulTorusAugmentation`. -/
abbrev allLeftChart (V : Type) : V → Bool := fun _ => false

/-- The component in the summand of `∅` of a section of `∧^0 F_G^∨`. -/
noncomputable abbrev exteriorZeroEmptyComponent {W : (vertexScheme (IncCoeffRing E) V).Opens}
    (y : Γ(G.exteriorBundle (IncCoeffRing E) 0, W)) :
    Γ(G.exteriorSummand (IncCoeffRing E) ∅, W) :=
  ((biproduct.π (fun S : Set.powersetCard E 0 => G.exteriorSummand (IncCoeffRing E) S)
    (powersetCardEmpty E)).val.app (op W)).hom y

/-- **Chart-level comparison.** Let `s` be a global function of `Z_G` whose restriction to the
all-left chart is `ε(y)` for a section `y` of `∧^0 F_G^∨` on that chart, and let `c` be a
degree-zero Čech–Koszul cycle whose `∅`-component on the all-left chart is the `∅`-component of
`y`. Then `s` and `c` give the same element of `𝒰_G`. -/
theorem incidenceProjectiveZeroGlobalSectionsEquiv_eq_univCechKoszulAugmentation
    (s : Γ(G.incidenceProjectiveZeroScheme, ⊤))
    (y : Γ(G.exteriorBundle (IncCoeffRing E) 0,
      univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V))))
    (c : G.univCechKoszulCycles0)
    (hs : G.incidenceProjectiveZeroScheme.presheaf.map
        (homOfLE (le_top : G.incidenceProjectiveZeroι ⁻¹ᵁ
          univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V)) ≤ ⊤)).op s =
      ((G.incKoszulAugmentation).val.app
        (op (univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V))))).hom y)
    (hc : c.val ∅ (chartFace (allLeftChart V)) = G.exteriorZeroEmptyComponent y) :
    G.incidenceProjectiveZeroGlobalSectionsEquiv s = G.univCechKoszulAugmentation c := by
  have hface : G.incUniversalKoszulFaceAugmentation (chartFace (allLeftChart V)) y =
      G.univCechKoszulFaceAugmentation c.val (chartFace (allLeftChart V)) := by
    rw [incUniversalKoszulFaceAugmentation_apply, univCechKoszulFaceAugmentation,
      incUnivFaceKoszulEquiv_apply, exteriorFaceEquiv_apply, hc]
    rfl
  apply Subtype.ext
  rw [incidenceProjectiveZeroGlobalSectionsEquiv_chart G (allLeftChart V) s, hs,
    incZeroChartSectionsIso_augmentation, incidenceProjectiveZeroChartEquiv_chartAugmentation,
    hface, univCechKoszulAugmentation_val, univCechKoszulTorusAugmentation_apply,
    incFaceToTorus_chartFace_apply]

/-- **Section-level comparison.** For a global section `x` of `∧^0 F_G^∨ = O_Y` and a degree-zero
Čech–Koszul cycle `c` whose `∅`-component on the all-left chart is the restriction of `x`, the
sheaf route `ε_⊤ x ∈ Γ(Z_G, O) ≅ 𝒰_G` and the Čech route `univCechKoszulAugmentation c` agree. -/
theorem incKoszulAugmentation_globalSections_univCech
    (x : Γ(G.exteriorBundle (IncCoeffRing E) 0, ⊤)) (c : G.univCechKoszulCycles0)
    (hc : c.val ∅ (chartFace (allLeftChart V)) =
      G.exteriorZeroEmptyComponent ((G.exteriorBundle (IncCoeffRing E) 0).val.map
        (homOfLE (le_top : univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V)) ≤ ⊤)).op
          x)) :
    G.incidenceProjectiveZeroGlobalSectionsEquiv
      (show Γ(G.incidenceProjectiveZeroScheme, ⊤) from
        ((G.incKoszulAugmentation).val.app (op ⊤)).hom x) = G.univCechKoszulAugmentation c :=
  G.incidenceProjectiveZeroGlobalSectionsEquiv_eq_univCechKoszulAugmentation _ _ c
    (PresheafOfModules.naturality_apply (G.incKoszulAugmentation).val
      (homOfLE (le_top : univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V)) ≤ ⊤)).op
        x).symm hc

end Sections

/-! ### The hypercohomology-level comparison -/

section Hypercohomology

open AlgebraicGeometry TopologicalSpace Opposite CechProduct ProjectiveLine SheafTools
open SheafTools.BinaryCells CategoryTheory.Abelian

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- `i_* O_{Z_G}` as an abelian sheaf on `Y`. -/
noncomputable abbrev incZeroPushforwardAbelian :
    Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (vertexScheme (IncCoeffRing E) V).ringCatSheaf).obj G.incZeroPushforward

/-- The augmentation `ε` as a morphism of abelian sheaves. -/
noncomputable abbrev incKoszulAugmentationAbelian :
    G.exteriorBundleAbelian (IncCoeffRing E) 0 ⟶ G.incZeroPushforwardAbelian :=
  (SheafOfModules.toSheaf (vertexScheme (IncCoeffRing E) V).ringCatSheaf).map
    G.incKoszulAugmentation

/-- The last differential of `K_G` followed by the augmentation vanishes, for abelian sheaves. -/
theorem incUniversalKoszulAbelianComplex_d_augmentation :
    G.incUniversalKoszulAbelianComplex.d 1 0 ≫ G.incKoszulAugmentationAbelian = 0 := by
  rw [show G.incUniversalKoszulAbelianComplex.d 1 0 = _ from
    G.incUniversalKoszulAbelianComplex_d 0, ← Functor.map_comp,
    univKoszulDifferential_incKoszulAugmentation, Functor.map_zero]

/-- **The augmentation `K_G ⟶ (i_* O_{Z_G})[0]`** as a morphism of cochain complexes of abelian
sheaves; its degree-zero component is `ε`. -/
noncomputable def incKoszulAugmentationCochainMap :
    G.incUniversalKoszulCochainComplex ⟶
      (CochainComplex.singleFunctor _ 0).obj G.incZeroPushforwardAbelian :=
  HomologicalComplex.mkHomToSingle
    ((G.incUniversalKoszulAbelianComplex.extendXIso (embeddingUpIntLE 0)
      (by simp : (embeddingUpIntLE 0).f 0 = 0)).hom ≫ G.incKoszulAugmentationAbelian)
    (by
      intro i hi
      have hi' : i = -((1 : ℕ) : ℤ) := by
        change i + 1 = 0 at hi
        omega
      subst hi'
      rw [G.incUniversalKoszulAbelianComplex.extend_d_eq (embeddingUpIntLE 0)
        (embeddingUpIntLE_zero_f 1) (by simp : (embeddingUpIntLE 0).f 0 = 0)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        incUniversalKoszulAbelianComplex_d_augmentation, comp_zero])

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0})]

local instance incKoszulAugmentationBridgeHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance incKoszulAugmentationBridgeEpi :
    Epi (augmentation (vertexCoordinateOpen (IncCoeffRing E) V)) :=
  augmentation_epi _ (vertexCellChartOpen_cover (IncCoeffRing E) V)

/-- The `(0, 0)` block `P_0 ⟶ ∧^0 F_G^∨` of a degree-zero cocycle followed by the augmentation. -/
noncomputable def incCocycleAugmentedBlock
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    sheafTerm (vertexCoordinateOpen (IncCoeffRing E) V) 0 ⟶ G.incZeroPushforwardAbelian :=
  cochainBlock _ _ 0 0 (by simp) z.1 ≫ G.incKoszulAugmentationAbelian

/-- The augmented block of a cocycle kills the boundary of the cell resolution. -/
theorem incCocycleAugmentedBlock_d
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)).d 1 0 ≫
      G.incCocycleAugmentedBlock z = 0 := by
  have h := cochainBlock_δ_succ (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V))
    G.incUniversalKoszulAbelianComplex (zero_add 1) z.1 0 0 (by simp)
  rw [Cocycle.δ_eq_zero, map_zero, Int.negOnePow_one, Units.neg_smul, one_smul] at h
  have hb := (add_neg_eq_zero.mp h.symm).symm
  rw [incCocycleAugmentedBlock, ← Category.assoc, hb, Category.assoc,
    incUniversalKoszulAbelianComplex_d_augmentation, comp_zero]

/-- The `(0, 0)` block of a degree-zero cocycle, with the extension isomorphisms at index `0`. -/
theorem cochainBlock_zero_zero
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    cochainBlock _ _ 0 0 (by simp) z.1 =
      ((sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)).extendXIso embeddingDownNat
          (rfl : embeddingDownNat.f 0 = 0)).inv ≫ z.1.v 0 0 (add_zero 0) ≫
        (G.incUniversalKoszulAbelianComplex.extendXIso (embeddingUpIntLE 0)
          (by simp : (embeddingUpIntLE 0).f 0 = 0)).hom :=
  rfl

/-- The morphism `h : ℤ_Y ⟶ i_* O_{Z_G}` through which the augmented block of a cocycle factors:
`P_0 ⟶ ℤ_Y` is a cokernel of the boundary of the cell resolution. -/
noncomputable def incCocycleSectionMap
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    (presheafToSheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat).obj (yoneda.obj ⊤ ⋙ AddCommGrpCat.free) ⟶ G.incZeroPushforwardAbelian :=
  (augmentation_exact (vertexCoordinateOpen (IncCoeffRing E) V)).desc
    (G.incCocycleAugmentedBlock z) (G.incCocycleAugmentedBlock_d z)

@[reassoc] theorem augmentation_incCocycleSectionMap
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    augmentation (vertexCoordinateOpen (IncCoeffRing E) V) ≫ G.incCocycleSectionMap z =
      G.incCocycleAugmentedBlock z :=
  (augmentation_exact (vertexCoordinateOpen (IncCoeffRing E) V)).g_desc _ _

/-- **The augmented cocycle is an augmentation class.** Postcomposing a degree-zero cocycle with
`K_G ⟶ (i_* O_{Z_G})[0]` gives the cocycle of `P ⟶ ℤ_Y[0] ⟶ (i_* O_{Z_G})[0]`. -/
theorem incCocycle_postcomp_eq
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    z.postcomp G.incKoszulAugmentationCochainMap =
      Cocycle.equivHomShift (negativeAugmentation _ _
          (augmentation_zero (vertexCoordinateOpen (IncCoeffRing E) V)) ≫
        (CochainComplex.singleFunctor _ 0).map (G.incCocycleSectionMap z) ≫
        (shiftFunctorZero (CochainComplex _ ℤ) ℤ).inv.app
          ((CochainComplex.singleFunctor _ 0).obj G.incZeroPushforwardAbelian)) := by
  refine Cocycle.ext (Cochain.ext _ _ fun p q hpq => ?_)
  obtain rfl : p = q := by omega
  by_cases hp : p = 0
  · subst hp
    simp only [Cocycle.postcomp, Cocycle.equivHomShift_apply, Cocycle.rightUnshift_coe,
      Cocycle.mk_coe, Cocycle.ofHom_coe]
    rw [Cochain.rightUnshift_v _ _ _ _ _ _ 0 (add_zero 0), Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, Cochain.ofHom_v]
    simp only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, negativeAugmentation_component]
    erw [Category.comp_id, HomologicalComplex.single_map_f_self,
      Iso.inv_hom_id_assoc, augmentation_incCocycleSectionMap_assoc]
    rw [incKoszulAugmentationCochainMap, HomologicalComplex.mkHomToSingle_f,
      incCocycleAugmentedBlock, cochainBlock_zero_zero]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hp

/-- **The sheaf-route map `H^0(K_G) → Γ(Z_G, O)` induced by the augmentation.** A class
`x : ℤ_Y[0] ⟶ K_G` goes to `x ≫ Q(K_G ⟶ (i_* O_{Z_G})[0])`, read as an element of Mathlib's sheaf
cohomology `H^0(Y, i_* O_{Z_G})` and then as a global section by `Sheaf.H.equiv₀`. -/
noncomputable def incUniversalKoszulHypercohomologyZeroSections
    (x : G.incUniversalKoszulHypercohomology 0) : Γ(G.incidenceProjectiveZeroScheme, ⊤) :=
  show G.incZeroPushforwardAbelian.obj.obj (op ⊤) from
    Sheaf.H.equiv₀ G.incZeroPushforwardAbelian
      (isTerminalTop (α := (vertexScheme (IncCoeffRing E) V).Opens))
      (sheafHypercohomologySingleEquiv G.incZeroPushforwardAbelian 0
        (x ≫ (DerivedCategory.Q.map G.incKoszulAugmentationCochainMap)⟦(0 : ℤ)⟧'))

/-- The class of a cocycle followed by the augmentation is `Q(h)`, read from the constant
sheaf. -/
theorem incUniversalKoszulHypercohomologyEquiv_comp_augmentation
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    G.incUniversalKoszulHypercohomologyEquiv 0 (CohomologyClass.mk z) ≫
        (DerivedCategory.Q.map G.incKoszulAugmentationCochainMap)⟦(0 : ℤ)⟧' =
      ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫
          G.incCocycleSectionMap z))) := by
  change ((cellAugmentationTargetIso (V := V) (E := E)).hom ≫
    derivedCohomologyClassHom _ _ _ _ _ _ 0 (CohomologyClass.mk z)) ≫ _ = _
  rw [Category.assoc, ← derivedCohomologyClassHom_postcomp, incCocycle_postcomp_eq,
    derivedCohomologyClassHom_single_augmentation]
  simp only [ShiftedHom.mk₀, cellAugmentationTargetIso, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]

/-- **The sheaf-route map on the class of a cocycle** is the global section represented by the
factorization `h` of its augmented block. -/
theorem incUniversalKoszulHypercohomologyZeroSections_mk
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    G.incUniversalKoszulHypercohomologyZeroSections
        (G.incUniversalKoszulHypercohomologyEquiv 0 (CohomologyClass.mk z)) =
      freeSheafSectionsEquiv G.incZeroPushforwardAbelian ⊤ (G.incCocycleSectionMap z) := by
  have he : sheafHypercohomologySingleEquiv G.incZeroPushforwardAbelian 0
      (ShiftedHom.mk₀ (0 : ℤ) rfl (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫
          G.incCocycleSectionMap z)))) =
      Ext.mk₀ ((freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫
        G.incCocycleSectionMap z) := by
    rw [sheafHypercohomologySingleEquiv]
    erw [AddEquiv.symm_apply_eq]
    exact (Ext.mk₀_hom _).symm
  have h₁ : Ext.addEquiv₀ (Ext.mk₀ ((freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫
      G.incCocycleSectionMap z)) =
      (freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫ G.incCocycleSectionMap z :=
    Ext.addEquiv₀.apply_symm_apply _
  unfold incUniversalKoszulHypercohomologyZeroSections
  rw [incUniversalKoszulHypercohomologyEquiv_comp_augmentation, he]
  change constantIntegerCorepresentsSections.homEquiv (Ext.addEquiv₀ (Ext.mk₀
    ((freeSheafTopIso (T := vertexScheme (IncCoeffRing E) V)).inv ≫
      G.incCocycleSectionMap z))) = _
  rw [h₁]
  exact freeSheafTopIso_inv_sections _ _

/-- The section of `∧^0 F_G^∨` on the all-left chart given by the `(0, 0)` block of a
cocycle. -/
noncomputable def incCocycleChartSection
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    Γ(G.exteriorBundle (IncCoeffRing E) 0,
      univFaceOpen (IncCoeffRing E) V (chartFace (allLeftChart V))) :=
  sectionsEquiv (vertexCoordinateOpen (IncCoeffRing E) V)
    (G.exteriorBundleAbelian (IncCoeffRing E) 0) 0 (cochainBlock _ _ 0 0 (by simp) z.1)
    (vertexCell fun _ => 0)

/-- **The two routes agree** (hypercohomology level). The sheaf-route map
`H^0(K_G) → Γ(Z_G, O)`, induced by the augmentation `ε : ∧^0 F_G^∨ ⟶ i_* O_{Z_G}`, followed by
`incidenceProjectiveZeroGlobalSectionsEquiv : Γ(Z_G, O) ≅ 𝒰_G`, is the Čech identification
`incUniversalKoszulHypercohomologyZeroEquiv`. -/
theorem incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections
    (x : G.incUniversalKoszulHypercohomology 0) :
    G.incidenceProjectiveZeroGlobalSectionsEquiv
        (G.incUniversalKoszulHypercohomologyZeroSections x) =
      G.incUniversalKoszulHypercohomologyZeroEquiv x := by
  obtain ⟨c, rfl⟩ := (G.incUniversalKoszulHypercohomologyEquiv 0).surjective x
  obtain ⟨z, rfl⟩ := c.mk_surjective
  have hR : G.incUniversalKoszulHypercohomologyZeroEquiv
      (G.incUniversalKoszulHypercohomologyEquiv 0 (CohomologyClass.mk z)) =
      G.univCechKoszulAugmentation (G.cocycleZeroToCycles z) := by
    simp only [incUniversalKoszulHypercohomologyZeroEquiv, AddEquiv.trans_apply,
      AddEquiv.symm_apply_apply, AddEquiv.ofBijective_apply, cohomologyClassZeroAugmentation_mk]
  rw [hR, incUniversalKoszulHypercohomologyZeroSections_mk]
  refine G.incidenceProjectiveZeroGlobalSectionsEquiv_eq_univCechKoszulAugmentation _
    (G.incCocycleChartSection z) _ ?_ ?_
  · have h1 := sectionsEquiv_augmentation_comp (vertexCoordinateOpen (IncCoeffRing E) V)
      G.incZeroPushforwardAbelian (G.incCocycleSectionMap z) (fun _ => 0)
    rw [augmentation_incCocycleSectionMap, incCocycleAugmentedBlock, sectionsEquiv_comp] at h1
    exact h1.symm
  · rw [cocycleZeroToCycles_val]
    have h2 : G.cechOfCochain 0 z.1 ∅ = koszulTotSign 0 •
        (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg ∅ v : ℤ)) 0
          (cochainBlock _ _ 0 0 (by simp) z.1 ≫
            G.exteriorAbelianProj (IncCoeffRing E) 0 (powersetCardEmpty E))).val :=
      G.cechOfCochain_powersetCard z.1 0 (powersetCardEmpty E) 0 (by simp)
    have hk : koszulTotSign 0 = 1 := by simp [koszulTotSign]
    rw [h2, Pi.smul_apply, hk, one_smul]
    have h3 := vertexTwistCellNativeEquiv_apply (IncCoeffRing E) V (fun v => -(G.deg ∅ v : ℤ)) 0
      (cochainBlock _ _ 0 0 (by simp) z.1 ≫
        G.exteriorAbelianProj (IncCoeffRing E) 0 (powersetCardEmpty E)) (vertexCell fun _ => 0)
    rw [sectionsEquiv_comp] at h3
    exact h3

/-- The same statement for the `S_G`-linear Čech identification. -/
theorem incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections_linear
    (x : G.incUniversalKoszulHypercohomology 0) :
    letI := G.incUniversalKoszulHypercohomologyModule 0
    G.incidenceProjectiveZeroGlobalSectionsEquiv
        (G.incUniversalKoszulHypercohomologyZeroSections x) =
      G.incUniversalKoszulHypercohomologyZeroLinearEquiv x :=
  G.incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections x

/-- **The composite `H^0(K_G) → Γ(Z_G, O) ≅ 𝒰_G` is the Čech identification**
`incUniversalKoszulHypercohomologyZeroLinearEquiv`, as functions. -/
theorem incidenceProjectiveZeroGlobalSectionsEquiv_comp_hypercohomologyZeroSections :
    letI := G.incUniversalKoszulHypercohomologyModule 0
    (G.incidenceProjectiveZeroGlobalSectionsEquiv ∘
        G.incUniversalKoszulHypercohomologyZeroSections) =
      G.incUniversalKoszulHypercohomologyZeroLinearEquiv :=
  funext G.incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections

/-- The sheaf-route map `H^0(K_G) → Γ(Z_G, O)` is bijective. -/
theorem incUniversalKoszulHypercohomologyZeroSections_bijective :
    Function.Bijective G.incUniversalKoszulHypercohomologyZeroSections := by
  have h : G.incUniversalKoszulHypercohomologyZeroSections =
      G.incidenceProjectiveZeroGlobalSectionsEquiv.symm ∘
        G.incUniversalKoszulHypercohomologyZeroEquiv := by
    funext x
    rw [Function.comp_apply, RingEquiv.eq_symm_apply,
      incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections]
  rw [h]
  exact G.incidenceProjectiveZeroGlobalSectionsEquiv.symm.bijective.comp
    G.incUniversalKoszulHypercohomologyZeroEquiv.bijective

/-- The sheaf-route map is semilinear over the coefficient map `S_G → Γ(Z_G, O)`. -/
theorem incUniversalKoszulHypercohomologyZeroSections_smul (r : IncCoeffRing E)
    (x : G.incUniversalKoszulHypercohomology 0) :
    letI := G.incUniversalKoszulHypercohomologyModule 0
    G.incUniversalKoszulHypercohomologyZeroSections (r • x) =
      G.incidenceProjectiveZeroCoefficientHom r *
        G.incUniversalKoszulHypercohomologyZeroSections x := by
  apply G.incidenceProjectiveZeroGlobalSectionsEquiv.injective
  rw [map_mul, incidenceProjectiveZeroGlobalSectionsEquiv_coeff,
    incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections_linear,
    incidenceProjectiveZeroGlobalSectionsEquiv_hypercohomologyZeroSections_linear]
  exact (G.incUniversalKoszulHypercohomologyZeroLinearEquiv.map_smul r x).trans rfl

end Derived

end Hypercohomology

end BPFixedPoints.Multigraph
