import BPFixedPoints.Incidence.VertexPermutationTwistCohomology
import BPFixedPoints.Incidence.IncidenceVertexRelabelTor
import BPFixedPoints.Incidence.IncidenceTorExteriorIsomorphism

/-!
# Vertex relabelings act on the exterior bundle and its cohomology

Let `φ : VertexRelabel G H` with vertex bijection `ψ = φ.vertex : V ≃ W`, and let
`g = a_{ψ⁻¹} : (P¹)^V ≅ (P¹)^W` be the coordinate map of `ψ⁻¹`. Since `φ` preserves vertex
degrees, the twist `-d_S` of an edge subset `S` for `G` is the twist `-d_S` for `H` composed with
`ψ`, so the transport `vertexTwistPermIso` gives `g_* O(-d^G_S) ≅ O(-d^H_S)`
(`exteriorSummandPermIso`). Summandwise these give an isomorphism of sheaves of modules
`g_* (∧^q F_G^∨) ≅ ∧^q F_H^∨` of exterior bundles (`exteriorPermIso`), and on underlying abelian
sheaves `exteriorAbelianPermIso : (vertexSheafPerm R ψ).functor.obj (∧^q F_G^∨) ≅ ∧^q F_H^∨`.

The geometric map of exterior cohomology (`exteriorCohomologyVertexRelabel`) is the transport of
Ext-defined cohomology along the scheme isomorphism (`vertexSheafHPerm`) followed by this
isomorphism. It is linear for the geometric base actions, hence `ℂ`-linear for `R = ℂ`. Its
summand components are the geometric maps of multi-twist cohomology
(`exteriorCohomologyVertexRelabel_proj`). None of these is defined through states.

The state formula of the geometric map is reduced to one statement about multi-twists,
`VertexTwistStateFormula R ψ`: the state coordinates of `vertexTwistHPerm x` are the signed
relabeling `hVertexPerm` of those of `x`. Assuming it, the following are proved: the exterior
state formula with the same Koszul sign as the Tor side (`exteriorCohomologyState_vertexRelabel_of`),
the naturality square of `incidenceTorExteriorEquiv` (`incidenceTorExteriorEquiv_vertexRelabel_of`),
and preservation of the exterior products and unit. `VertexTwistStateFormula` is proved in
`VertexPermutationTwistStateFormula.lean` (`vertexTwistStateFormula`), through the naturality of
the cubical-cell comparison under the equivalence `vertexSheafPerm R ψ`; the unconditional forms of
the results here are stated there.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open TopologicalSpace SheafTools SchemeTools ProjectiveLine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable local instance vertexRelabelExteriorHasExt (R : Type) [CommRing R] (U : Type)
    [Fintype U] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R U)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- An isomorphism of sheaves of modules on a scheme, read in the category `SheafOfModules`
(the two categories have the same morphisms). -/
def sheafOfModulesIso {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) :
    @Iso (SheafOfModules X.ringCatSheaf) _ M N where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- Pushforward of sheaves of modules along the coordinate map of `ψ⁻¹`, in the category
`SheafOfModules` (it is `Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)`). -/
noncomputable abbrev vertexModulePerm (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W]
    (ψ : V ≃ W) :
    SheafOfModules (vertexScheme R V).ringCatSheaf ⥤ SheafOfModules (vertexScheme R W).ringCatSheaf :=
  SheafOfModules.pushforward (vertexSchemePerm R ψ.symm).toRingCatSheafHom

/-- An isomorphism of sheaves of modules in the category `SheafOfModules`, read in the category
of sheaves of modules on the scheme. -/
def modulesIso {X : Scheme.{0}} {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N) :
    @Iso X.Modules _ M N where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

instance vertexModulePerm_additive (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W]
    (ψ : V ≃ W) : (vertexModulePerm R ψ).Additive where
  map_add {_ _ f g} := by
    apply SheafOfModules.hom_ext
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [Fintype E]
  {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)
variable (R : Type) [CommRing R]

omit [Fintype V] [Fintype W] [Fintype E] in
/-- The twist of an edge subset is carried to the twist of the same edge subset. -/
theorem twist_vertex (S : Finset E) (v : V) : -(H.deg S (φ.vertex v) : ℤ) = -(G.deg S v : ℤ) := by
  rw [φ.deg_vertex]

/-- The transport of the exterior summand of an edge subset. -/
noncomputable def exteriorSummandPermIso (S : Finset E) :
    (vertexModulePerm R φ.vertex).obj (G.exteriorSummand R S) ≅ H.exteriorSummand R S :=
  sheafOfModulesIso (vertexTwistPermIso R φ.vertex _ _ (φ.twist_vertex S))

/-- The transport of the `q`-th exterior bundle: componentwise the transport of the summands. -/
noncomputable def exteriorPermHom (q : ℕ) :
    (vertexModulePerm R φ.vertex).obj (G.exteriorBundle R q) ⟶ H.exteriorBundle R q :=
  biproduct.lift fun S => (vertexModulePerm R φ.vertex).map
    (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S) ≫
      (φ.exteriorSummandPermIso R S).hom

/-- The inverse transport of the `q`-th exterior bundle. -/
noncomputable def exteriorPermInv (q : ℕ) :
    H.exteriorBundle R q ⟶ (vertexModulePerm R φ.vertex).obj (G.exteriorBundle R q) :=
  biproduct.desc fun S => (φ.exteriorSummandPermIso R S).inv ≫ (vertexModulePerm R φ.vertex).map
    (biproduct.ι (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)

@[reassoc (attr := simp)] theorem exteriorPermHom_π (q : ℕ) (S : Set.powersetCard E q) :
    φ.exteriorPermHom R q ≫ biproduct.π (fun S : Set.powersetCard E q => H.exteriorSummand R S) S =
      (vertexModulePerm R φ.vertex).map
        (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S) ≫
          (φ.exteriorSummandPermIso R S).hom :=
  biproduct.lift_π _ _

@[reassoc (attr := simp)] theorem ι_exteriorPermInv (q : ℕ) (S : Set.powersetCard E q) :
    biproduct.ι (fun S : Set.powersetCard E q => H.exteriorSummand R S) S ≫ φ.exteriorPermInv R q =
      (φ.exteriorSummandPermIso R S).inv ≫ (vertexModulePerm R φ.vertex).map
        (biproduct.ι (fun S : Set.powersetCard E q => G.exteriorSummand R S) S) :=
  biproduct.ι_desc _ _

theorem exteriorPermHom_inv (q : ℕ) : φ.exteriorPermHom R q ≫ φ.exteriorPermInv R q = 𝟙 _ := by
  rw [exteriorPermHom, exteriorPermInv, biproduct.lift_desc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
  rw [← Functor.map_sum, biproduct.total]
  exact CategoryTheory.Functor.map_id _ _

theorem exteriorPermInv_hom (q : ℕ) : φ.exteriorPermInv R q ≫ φ.exteriorPermHom R q = 𝟙 _ := by
  apply biproduct.hom_ext'
  intro S
  apply biproduct.hom_ext
  intro T
  have hr : (biproduct.ι (fun S : Set.powersetCard E q => H.exteriorSummand R S) S ≫
      𝟙 (H.exteriorBundle R q)) ≫ biproduct.π (fun S : Set.powersetCard E q => H.exteriorSummand R S) T =
        biproduct.ι (fun S : Set.powersetCard E q => H.exteriorSummand R S) S ≫
          biproduct.π (fun S : Set.powersetCard E q => H.exteriorSummand R S) T := by
    erw [Category.comp_id]
  rw [hr]
  simp only [Category.assoc, ι_exteriorPermInv_assoc, exteriorPermHom_π]
  simp only [← Category.assoc, ← Functor.map_comp]
  by_cases h : S = T
  · subst h
    simp only [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id]
  · simp only [biproduct.ι_π_ne _ h, Functor.map_zero, comp_zero, zero_comp]

/-- **Transport of the exterior bundle** along a vertex relabeling, as an isomorphism of sheaves
of modules. -/
noncomputable def exteriorPermIso (q : ℕ) :
    (vertexModulePerm R φ.vertex).obj (G.exteriorBundle R q) ≅ H.exteriorBundle R q where
  hom := φ.exteriorPermHom R q
  inv := φ.exteriorPermInv R q
  hom_inv_id := φ.exteriorPermHom_inv R q
  inv_hom_id := φ.exteriorPermInv_hom R q

/-- **Transport of the abelian exterior bundle**: the image of the `q`-th exterior bundle of `G`
under `vertexSheafPerm R φ.vertex` is the `q`-th exterior bundle of `H`. -/
noncomputable def exteriorAbelianPermIso (q : ℕ) :
    (vertexSheafPerm R φ.vertex).functor.obj (G.exteriorBundleAbelian R q) ≅
      H.exteriorBundleAbelian R q :=
  (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).mapIso (φ.exteriorPermIso R q)

/-- The abelian exterior transport followed by a summand projection is the transported projection
followed by the transport of the summand. -/
theorem exteriorAbelianPermIso_proj (q : ℕ) (S : Set.powersetCard E q) :
    (φ.exteriorAbelianPermIso R q).hom ≫ H.exteriorProj R q S =
      (vertexSheafPerm R φ.vertex).functor.map (G.exteriorProj R q S) ≫
        (vertexTwistAbelianPermIso R φ.vertex _ _ (φ.twist_vertex S)).hom := by
  change (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map (φ.exteriorPermHom R q) ≫
      (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
        (biproduct.π (fun S : Set.powersetCard E q => H.exteriorSummand R S) S) =
    (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map ((vertexModulePerm R φ.vertex).map
        (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)) ≫
      (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map (φ.exteriorSummandPermIso R S).hom
  rw [← Functor.map_comp, ← Functor.map_comp, exteriorPermHom_π]

/-- **The geometric map of exterior cohomology** of a vertex relabeling: transport of
Ext-defined cohomology along the scheme isomorphism, followed by the transport of the exterior
bundle. It is linear for the geometric base actions. -/
noncomputable def exteriorCohomologyVertexRelabel (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R] Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  (vertexSheafHPermLinear R φ.vertex (G.exteriorBundle R q) j).trans
    (schemeBaseHMapLinear R (vertexToBase R W) (modulesIso (φ.exteriorPermIso R q)) j)

/-- The geometric map is the transport of cohomology followed by the map of the exterior
transport. -/
theorem exteriorCohomologyVertexRelabel_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyVertexRelabel R q j x =
      Sheaf.H.map (φ.exteriorAbelianPermIso R q).hom j (vertexSheafHPerm R φ.vertex _ j x) := rfl

/-- **Summand components.** The summand of an edge subset of the image of an exterior class is
the geometric map of multi-twist cohomology applied to the summand of the class. -/
theorem exteriorCohomologyVertexRelabel_proj (q j : ℕ) (S : Set.powersetCard E q)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    Sheaf.H.map (H.exteriorProj R q S) j (φ.exteriorCohomologyVertexRelabel R q j x) =
      vertexTwistHPerm R φ.vertex _ _ (φ.twist_vertex S) j
        (Sheaf.H.map (G.exteriorProj R q S) j x) := by
  rw [exteriorCohomologyVertexRelabel_apply, ← Sheaf.H.map_comp_apply,
    exteriorAbelianPermIso_proj, Sheaf.H.map_comp_apply, vertexTwistHPerm_apply,
    vertexSheafHPerm_map]

end VertexRelabel

/-! ## Reduction of the state formula to multi-twists -/

section Reduction

variable (R : Type) [CommRing R] [IsNoetherianRing R] {V W : Type} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

/-- **The multi-twist state formula** for a vertex bijection `ψ` (the statement; it is proved as
`vertexTwistStateFormula`):
for every nonnegative degree vector `d` on `V` with transported vector `d'` on `W`, the state
coordinates of the image of a class under the geometric map `vertexTwistHPerm` are the signed
relabeling `hVertexPerm` (Koszul sign of `ψ` on the twist support) of the state coordinates of the
class. -/
def VertexTwistStateFormula (ψ : V ≃ W) : Prop :=
  ∀ (d : V → ℕ) (d' : W → ℕ) (h : (fun w => d (ψ.symm w)) = d') (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n),
    (vertexTwistActualStateAt R W d' n
      (vertexTwistHPerm R ψ (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ))
        (fun v => by rw [← h]; simp) n x) : CechProduct.H R d') =
      CechProduct.castH R h (hVertexPerm R ψ d (vertexTwistActualStateAt R V d n x))

end Reduction

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)
variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- **Exterior state formula, assuming the multi-twist state formula.** The state vector of the
geometric image of an exterior class is the signed relabeling of its state vector. -/
theorem exteriorCohomologyState_vertexRelabel_of (hs : VertexTwistStateFormula R φ.vertex)
    (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyVertexRelabel R q j x) =
      φ.statePerm R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologyState_apply, exteriorCohomologyState_apply, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [exteriorCohomologyVertexRelabel_proj, statePerm_incStateEmbed]
  congr 1
  exact hs (G.deg S) (H.deg S) (φ.deg_eq S).symm j _

/-- **Naturality square, assuming the multi-twist state formula.** The Tor-to-exterior
isomorphism carries the Tor map of a vertex relabeling to the geometric map of exterior
cohomology. -/
theorem incidenceTorExteriorEquiv_vertexRelabel_of (hs : VertexTwistStateFormula ℂ φ.vertex)
    {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalVertexRelabel p q x) =
      φ.exteriorCohomologyVertexRelabel ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv,
    exteriorCohomologyState_vertexRelabel_of φ ℂ hs, exteriorCohomologyState_incidenceTorExteriorEquiv,
    incidenceTorInternalVertexRelabel_val, incidenceTorFullState_vertexRelabel]

/-- **Products, assuming the multi-twist state formula.** The geometric map preserves the
exterior cohomology products. -/
theorem exteriorCohomologyVertexRelabel_product_of (hs : VertexTwistStateFormula R φ.vertex)
    (q q' i j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologyVertexRelabel R (q + q') (i + j) (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologyVertexRelabel R q i x)
        (φ.exteriorCohomologyVertexRelabel R q' j y) := by
  apply H.exteriorCohomologyState_injective R (q + q') (i + j)
  rw [exteriorCohomologyState_vertexRelabel_of φ R hs, exteriorCohomologyState_product,
    exteriorCohomologyState_product, exteriorCohomologyState_vertexRelabel_of φ R hs,
    exteriorCohomologyState_vertexRelabel_of φ R hs, statePerm_incStateCup]

/-- **Unit, assuming the multi-twist state formula.** The geometric map sends the exterior unit
to the unit. -/
theorem exteriorCohomologyVertexRelabel_unit_of (hs : VertexTwistStateFormula R φ.vertex) :
    φ.exteriorCohomologyVertexRelabel R 0 0 (G.exteriorCohomologyUnit R) = H.exteriorCohomologyUnit R := by
  apply H.exteriorCohomologyState_injective R 0 0
  rw [exteriorCohomologyState_vertexRelabel_of φ R hs, exteriorCohomologyState_unit,
    exteriorCohomologyState_unit, statePerm_incStateUnit]

end VertexRelabel

end BPFixedPoints.Multigraph
