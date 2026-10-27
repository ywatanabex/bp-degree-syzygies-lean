import BPFixedPoints.Incidence.EdgeExteriorBundleProduct
import BPFixedPoints.Incidence.IncidenceRelabelStates

/-!
# Edge relabelings act on the actual exterior bundle and its cohomology

For an edge relabeling `φ : EdgeRelabel G H` the vertex set and the vertex projective product
are unchanged, and the summand `O(-d_S)` of the `q`-th exterior bundle of `G` is literally the
summand `O(-d_{φ S})` of `H`, since `φ` preserves vertex degrees. The induced isomorphism of
exterior bundles is the signed biproduct reindexing along `S ↦ φ S`, with the relabeling sign
`φ.sign ℤ S` on the summand of `S`: the exterior basis vector of `S` in the order of `G` is that
sign times the exterior basis vector of `φ S` in the order of `H`. It is constructed as an
isomorphism of the underlying actual abelian sheaves (`exteriorRelabelAbelianIso`), from the actual
biproduct projections and inclusions of the exterior bundles; its effect on cohomology is linear for
the original geometric base action. A version as an isomorphism of sheaves of modules is not
constructed here.

The induced map on actual Ext-defined cohomology (`exteriorCohomologyRelabel`) sends the state
vector of a class to the signed relabeling of its state vector, is linear for the original
geometric base action, preserves the exterior cohomology products (whose shuffle signs use the
two different edge orders) and sends the unit to the unit.

Identities of morphisms are proved by rewriting with the named morphisms `exteriorProj`,
`exteriorIncl` and `exteriorTwistHom`, so that only syntactically identical morphisms of the actual
sheaf category are compared.
-/

namespace BPFixedPoints

open CategoryTheory CategoryTheory.Limits

namespace Multigraph
open AlgebraicGeometry CategoryTheory.Abelian
open TopologicalSpace ProjectiveLine SchemeTools CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] exteriorProductHasExt

/-- The summand projections and inclusions of an exterior bundle decompose the identity. -/
theorem exterior_total {V E₀ : Type} [DecidableEq V] [Fintype V] [Fintype E₀] (K : Multigraph V E₀) (R : Type)
    [CommRing R] (q : ℕ) :
    ∑ S : Set.powersetCard E₀ q, K.exteriorProj R q S ≫ K.exteriorIncl R q S = 𝟙 _ := by
  have h := congrArg (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.total (f := fun S : Set.powersetCard E₀ q => K.exteriorSummand R S))
  rw [CategoryTheory.Functor.map_sum, CategoryTheory.Functor.map_id] at h
  simp only [CategoryTheory.Functor.map_comp] at h
  exact h

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)
variable (R : Type) [CommRing R]

/-- Relabeling of `q`-element edge subsets. -/
def powersetCardEquiv (q : ℕ) : Set.powersetCard E q ≃ Set.powersetCard E' q where
  toFun S := ⟨φ.edgeSet S, Set.powersetCard.mem_iff.mpr
    ((φ.card_edgeSet S).trans (Set.powersetCard.card_eq S))⟩
  invFun S := ⟨(S : Finset E').map φ.edge.symm.toEmbedding, Set.powersetCard.mem_iff.mpr
    ((Finset.card_map _).trans (Set.powersetCard.card_eq S))⟩
  left_inv S := Subtype.ext (by simp [edgeSet_def, Finset.map_map])
  right_inv S := Subtype.ext (by simp [edgeSet_def, Finset.map_map])

/-- The underlying edge set of a relabeled edge subset is the image edge set. -/
@[simp] theorem coe_powersetCardEquiv (q : ℕ) (S : Set.powersetCard E q) :
    ((φ.powersetCardEquiv q S : Set.powersetCard E' q) : Finset E') = φ.edgeSet S := rfl

/-- The relabeling sign of a `q`-element edge subset, as an integer. -/
def powersetSign (q : ℕ) (S : Set.powersetCard E q) : ℤ := φ.sign ℤ S

theorem powersetSign_mul_self (q : ℕ) (S : Set.powersetCard E q) :
    φ.powersetSign q S * φ.powersetSign q S = 1 :=
  φ.sign_mul_self ℤ S

/-- The degree of a relabeled edge subset, written through the relabeled subset. -/
theorem deg_powersetCardEquiv {q : ℕ} (S : Set.powersetCard E q) :
    H.deg ((φ.powersetCardEquiv q S : Set.powersetCard E' q) : Finset E') = G.deg (S : Finset E) :=
  φ.deg_edgeSet S

/-- The twist of an edge subset equals the twist of its relabeled edge subset. -/
theorem twist_powersetCardEquiv {q : ℕ} (S : Set.powersetCard E q) :
    (fun v => -(G.deg (S : Finset E) v : ℤ)) =
      fun v => -(H.deg ((φ.powersetCardEquiv q S : Set.powersetCard E' q) : Finset E') v : ℤ) := by
  rw [φ.deg_powersetCardEquiv]

/-- The identification of the abelian summand of an edge subset with the abelian summand of the
relabeled edge subset. -/
def exteriorTwistHom (q : ℕ) (S : Set.powersetCard E q) :
    vertexTwistAbelianSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ)) ⟶
      vertexTwistAbelianSheaf R V
        (fun v => -(H.deg ((φ.powersetCardEquiv q S : Set.powersetCard E' q) : Finset E') v : ℤ)) :=
  eqToHom (congrArg (vertexTwistAbelianSheaf R V) (φ.twist_powersetCardEquiv S))

/-- The inverse identification of abelian summands. -/
def exteriorTwistInv (q : ℕ) (S : Set.powersetCard E q) :
    vertexTwistAbelianSheaf R V
        (fun v => -(H.deg ((φ.powersetCardEquiv q S : Set.powersetCard E' q) : Finset E') v : ℤ)) ⟶
      vertexTwistAbelianSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ)) :=
  eqToHom (congrArg (vertexTwistAbelianSheaf R V) (φ.twist_powersetCardEquiv S).symm)

theorem exteriorTwistHom_inv (q : ℕ) (S : Set.powersetCard E q) :
    φ.exteriorTwistHom R q S ≫ φ.exteriorTwistInv R q S = 𝟙 _ := by
  rw [exteriorTwistHom, exteriorTwistInv, eqToHom_trans, eqToHom_refl]

theorem exteriorTwistInv_hom (q : ℕ) (S : Set.powersetCard E q) :
    φ.exteriorTwistInv R q S ≫ φ.exteriorTwistHom R q S = 𝟙 _ := by
  rw [exteriorTwistHom, exteriorTwistInv, eqToHom_trans, eqToHom_refl]

/-- The underlying abelian sheaf morphism of the relabeling of exterior bundles: on the summand of
an edge subset, the relabeling sign times the identification with the summand of the relabeled
edge subset. -/
def exteriorRelabelHom (q : ℕ) : G.exteriorBundleAbelian R q ⟶ H.exteriorBundleAbelian R q :=
  ∑ S : Set.powersetCard E q, φ.powersetSign q S •
    (G.exteriorProj R q S ≫ φ.exteriorTwistHom R q S ≫ H.exteriorIncl R q (φ.powersetCardEquiv q S))

/-- The inverse abelian relabeling of exterior bundles. -/
def exteriorRelabelInv (q : ℕ) : H.exteriorBundleAbelian R q ⟶ G.exteriorBundleAbelian R q :=
  ∑ S : Set.powersetCard E q, φ.powersetSign q S •
    (H.exteriorProj R q (φ.powersetCardEquiv q S) ≫ φ.exteriorTwistInv R q S ≫ G.exteriorIncl R q S)

/-- The abelian relabeling followed by the projection to the summand of a relabeled edge subset. -/
theorem exteriorRelabelHom_proj {q : ℕ} (S : Set.powersetCard E q) :
    φ.exteriorRelabelHom R q ≫ H.exteriorProj R q (φ.powersetCardEquiv q S) =
      φ.powersetSign q S • (G.exteriorProj R q S ≫ φ.exteriorTwistHom R q S) := by
  rw [exteriorRelabelHom, Preadditive.sum_comp, Finset.sum_eq_single S]
  · rw [Preadditive.zsmul_comp, Category.assoc, Category.assoc, exteriorIncl_proj_self,
      Category.comp_id]
  · intro T _ hT
    rw [Preadditive.zsmul_comp, Category.assoc, Category.assoc,
      exteriorIncl_proj_ne H R q ((φ.powersetCardEquiv q).injective.ne hT), comp_zero, comp_zero,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- The inclusion of the summand of an edge subset followed by the abelian relabeling. -/
theorem exteriorIncl_relabelHom {q : ℕ} (S : Set.powersetCard E q) :
    G.exteriorIncl R q S ≫ φ.exteriorRelabelHom R q =
      φ.powersetSign q S • (φ.exteriorTwistHom R q S ≫ H.exteriorIncl R q (φ.powersetCardEquiv q S)) := by
  rw [exteriorRelabelHom, Preadditive.comp_sum, Finset.sum_eq_single S]
  · rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorIncl_proj_self, Category.id_comp]
  · intro T _ hT
    rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorIncl_proj_ne G R q (Ne.symm hT),
      zero_comp, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- The inclusion of the summand of a relabeled edge subset followed by the inverse relabeling. -/
theorem exteriorIncl_relabelInv {q : ℕ} (S : Set.powersetCard E q) :
    H.exteriorIncl R q (φ.powersetCardEquiv q S) ≫ φ.exteriorRelabelInv R q =
      φ.powersetSign q S • (φ.exteriorTwistInv R q S ≫ G.exteriorIncl R q S) := by
  rw [exteriorRelabelInv, Preadditive.comp_sum, Finset.sum_eq_single S]
  · rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorIncl_proj_self, Category.id_comp]
  · intro T _ hT
    rw [Preadditive.comp_zsmul, ← Category.assoc,
      exteriorIncl_proj_ne H R q ((φ.powersetCardEquiv q).injective.ne (Ne.symm hT)),
      zero_comp, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ S) h

theorem exteriorRelabelHom_inv (q : ℕ) :
    φ.exteriorRelabelHom R q ≫ φ.exteriorRelabelInv R q = 𝟙 _ := by
  conv_rhs => rw [← exterior_total G R q]
  rw [exteriorRelabelHom, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Preadditive.zsmul_comp, Category.assoc, Category.assoc, exteriorIncl_relabelInv,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, smul_smul, powersetSign_mul_self, one_smul,
    ← Category.assoc (φ.exteriorTwistHom R q S), exteriorTwistHom_inv, Category.id_comp]

theorem exteriorRelabelInv_hom (q : ℕ) :
    φ.exteriorRelabelInv R q ≫ φ.exteriorRelabelHom R q = 𝟙 _ := by
  conv_rhs => rw [← exterior_total H R q, ← (φ.powersetCardEquiv q).sum_comp]
  rw [exteriorRelabelInv, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Preadditive.zsmul_comp, Category.assoc, Category.assoc, exteriorIncl_relabelHom,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, smul_smul, powersetSign_mul_self, one_smul,
    ← Category.assoc (φ.exteriorTwistInv R q S), exteriorTwistInv_hom, Category.id_comp]

/-- The abelian relabeling of exterior bundles as an isomorphism of actual abelian sheaves. -/
def exteriorRelabelAbelianIso (q : ℕ) :
    G.exteriorBundleAbelian R q ≅ H.exteriorBundleAbelian R q where
  hom := φ.exteriorRelabelHom R q
  inv := φ.exteriorRelabelInv R q
  hom_inv_id := φ.exteriorRelabelHom_inv R q
  inv_hom_id := φ.exteriorRelabelInv_hom R q

/-- The map induced on actual cohomology of the exterior bundles by an edge relabeling. -/
def exteriorCohomologyRelabel (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) j where
  toFun := Sheaf.H.map (φ.exteriorRelabelHom R q) j
  invFun := Sheaf.H.map (φ.exteriorRelabelInv R q) j
  left_inv x := by
    rw [← Sheaf.H.map_comp_apply, exteriorRelabelHom_inv, Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← Sheaf.H.map_comp_apply, exteriorRelabelInv_hom, Sheaf.H.map_id_apply]
  map_add' := map_add _

/-- The cohomology relabeling is the map induced by the abelian relabeling morphism. -/
theorem exteriorCohomologyRelabel_apply (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyRelabel R q j x = Sheaf.H.map (φ.exteriorRelabelHom R q) j x := rfl

omit [DecidableEq V] in
/-- Cohomology of an identification of nonpositive twists coming from an equality of degree
vectors is the transport of actual cohomology. -/
theorem sheafH_map_eqToHom_negative {d d' : V → ℕ} (h : d = d')
    (p : vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ)) =
      vertexTwistAbelianSheaf R V (fun v => -(d' v : ℤ))) (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    Sheaf.H.map (eqToHom p) n z = vertexNegativeHCast R V h rfl z := by
  subst h
  rw [eqToHom_refl, Sheaf.H.map_id_apply]
  rfl

/-- Cohomology of the identification of summands is the transport of actual cohomology. -/
theorem sheafH_map_exteriorTwistHom {q : ℕ} (S : Set.powersetCard E q) (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ))) n) :
    Sheaf.H.map (φ.exteriorTwistHom R q S) n z =
      vertexNegativeHCast R V (φ.deg_powersetCardEquiv S).symm rfl z := by
  rw [exteriorTwistHom]
  exact sheafH_map_eqToHom_negative R (φ.deg_powersetCardEquiv S).symm _ n z

/-- The relabeled class projected to the summand of a relabeled edge subset is the relabeling sign
times the transport of the projection of the original class to the original summand. -/
theorem exteriorProj_relabel (q j : ℕ) (S : Set.powersetCard E q)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    Sheaf.H.map (H.exteriorProj R q (φ.powersetCardEquiv q S)) j (φ.exteriorCohomologyRelabel R q j x) =
      φ.powersetSign q S • vertexNegativeHCast R V (φ.deg_powersetCardEquiv S).symm rfl
        (Sheaf.H.map (G.exteriorProj R q S) j x) := by
  rw [exteriorCohomologyRelabel_apply, ← Sheaf.H.map_comp_apply, exteriorRelabelHom_proj,
    sheafH_map_zsmul_apply, Sheaf.H.map_comp_apply, sheafH_map_exteriorTwistHom]

variable [IsNoetherianRing R]

/-- The state vector of a relabeled exterior class is the signed relabeling of its state
vector. -/
theorem exteriorCohomologyState_relabel (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyRelabel R q j x) =
      φ.stateRelabel R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologyState_apply, exteriorCohomologyState_apply, map_sum,
    ← (φ.powersetCardEquiv q).sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [stateRelabel_incStateEmbed, exteriorProj_relabel, map_zsmul, Submodule.coe_smul_of_tower,
    map_zsmul, ← Int.cast_smul_eq_zsmul R, powersetSign, intCast_sign,
    vertexTwistActualStateAt_cast]
  congr 1

/-- The map induced on actual exterior cohomology by an edge relabeling, as a linear isomorphism
for the original geometric base actions. -/
def exteriorCohomologyRelabelLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := H.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R] Sheaf.H.{1} (H.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := H.exteriorBundleCohomologyModule R q j
  { φ.exteriorCohomologyRelabel R q j with
    map_smul' := fun r x => by
      apply H.exteriorCohomologyState_injective R q j
      change H.exteriorCohomologyState R q j (φ.exteriorCohomologyRelabel R q j (r • x)) =
        H.exteriorCohomologyState R q j (r • φ.exteriorCohomologyRelabel R q j x)
      rw [exteriorCohomologyState_relabel, map_smul, map_smul, map_smul,
        exteriorCohomologyState_relabel] }

/-- The linear relabeling has the same underlying map. -/
theorem exteriorCohomologyRelabelLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    φ.exteriorCohomologyRelabelLinear R q j x = φ.exteriorCohomologyRelabel R q j x := rfl

/-- Edge relabelings preserve the exterior cohomology products. -/
theorem exteriorCohomologyRelabel_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologyRelabel R (q + q') (i + j) (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologyRelabel R q i x)
        (φ.exteriorCohomologyRelabel R q' j y) := by
  apply H.exteriorCohomologyState_injective R (q + q') (i + j)
  rw [exteriorCohomologyState_relabel, exteriorCohomologyState_product,
    exteriorCohomologyState_product, exteriorCohomologyState_relabel,
    exteriorCohomologyState_relabel, stateRelabel_incStateCup]

/-- Edge relabelings send the exterior cohomology unit to the unit. -/
theorem exteriorCohomologyRelabel_unit :
    φ.exteriorCohomologyRelabel R 0 0 (G.exteriorCohomologyUnit R) = H.exteriorCohomologyUnit R := by
  apply H.exteriorCohomologyState_injective R 0 0
  rw [exteriorCohomologyState_relabel, exteriorCohomologyState_unit, exteriorCohomologyState_unit,
    stateRelabel_incStateUnit]

end EdgeRelabel

end

end Multigraph

end BPFixedPoints
