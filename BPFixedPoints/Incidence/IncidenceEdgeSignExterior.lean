import BPFixedPoints.Incidence.IncidenceEdgeSignStates
import BPFixedPoints.Incidence.IncidenceRelabelExterior

/-!
# Edge signs act on the actual exterior bundle and its cohomology

For an edge sign `ε`, replacing every basis vector `e^*` of the dual edge bundle by `ε_e e^*`
multiplies the exterior basis vector of a `q`-element edge subset `S` by `∏_{e ∈ S} ε_e`. The
induced automorphism of the `q`-th exterior bundle is the diagonal biproduct endomorphism with this
sign on the summand `O(-d_S)` (`exteriorSignHom`). As in `IncidenceRelabelExterior.lean` it is
constructed as a morphism of the underlying actual abelian sheaves, from the actual biproduct
projections and inclusions; it is an involution (`exteriorSignAbelianIso`). A version as an
isomorphism of sheaves of modules is not constructed here.

The induced map on actual Ext-defined cohomology (`exteriorCohomologySign`) scales the state vector
of a class by the edge-sign scaling (`exteriorCohomologyState_sign`), is linear for the original
geometric base action (`exteriorCohomologySignLinear`), preserves the exterior cohomology products,
sends the unit to the unit, is the identity for the trivial sign and composes multiplicatively in
the sign.
-/

namespace BPFixedPoints

open CategoryTheory CategoryTheory.Limits

namespace Multigraph
open AlgebraicGeometry CategoryTheory.Abelian
open TopologicalSpace ProjectiveLine SchemeTools CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

noncomputable section

attribute [local instance] exteriorProductHasExt

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (ε : EdgeSign E) (R : Type) [CommRing R]

/-- The integer sign of a `q`-element edge subset. -/
def exteriorSign (q : ℕ) (S : Set.powersetCard E q) : ℤ := ε.setSign ℤ (S : Finset E)

theorem exteriorSign_mul_self (q : ℕ) (S : Set.powersetCard E q) :
    exteriorSign ε q S * exteriorSign ε q S = 1 :=
  ε.setSign_mul_self ℤ _

/-- The underlying abelian sheaf endomorphism of the sign change of the exterior bundle: the sign
of the edge subset on each summand. -/
def exteriorSignHom (q : ℕ) : G.exteriorBundleAbelian R q ⟶ G.exteriorBundleAbelian R q :=
  ∑ S : Set.powersetCard E q, exteriorSign ε q S • (G.exteriorProj R q S ≫ G.exteriorIncl R q S)

/-- The sign change followed by the projection to a summand. -/
theorem exteriorSignHom_proj {q : ℕ} (S : Set.powersetCard E q) :
    G.exteriorSignHom ε R q ≫ G.exteriorProj R q S = exteriorSign ε q S • G.exteriorProj R q S := by
  rw [exteriorSignHom, Preadditive.sum_comp, Finset.sum_eq_single S]
  · rw [Preadditive.zsmul_comp, Category.assoc, exteriorIncl_proj_self, Category.comp_id]
  · intro T _ hT
    rw [Preadditive.zsmul_comp, Category.assoc, exteriorIncl_proj_ne G R q hT, comp_zero,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- The inclusion of a summand followed by the sign change. -/
theorem exteriorIncl_signHom {q : ℕ} (S : Set.powersetCard E q) :
    G.exteriorIncl R q S ≫ G.exteriorSignHom ε R q = exteriorSign ε q S • G.exteriorIncl R q S := by
  rw [exteriorSignHom, Preadditive.comp_sum, Finset.sum_eq_single S]
  · rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorIncl_proj_self, Category.id_comp]
  · intro T _ hT
    rw [Preadditive.comp_zsmul, ← Category.assoc, exteriorIncl_proj_ne G R q (Ne.symm hT),
      zero_comp, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- Composites of sign changes multiply the signs. -/
theorem exteriorSignHom_comp (ε' : EdgeSign E) (q : ℕ) :
    G.exteriorSignHom ε R q ≫ G.exteriorSignHom ε' R q = G.exteriorSignHom (ε * ε') R q := by
  conv_rhs => rw [exteriorSignHom]
  conv_lhs => rw [exteriorSignHom, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Preadditive.zsmul_comp, Category.assoc, exteriorIncl_signHom, Preadditive.comp_zsmul,
    smul_smul, exteriorSign, exteriorSign, exteriorSign, EdgeSign.setSign_mul, mul_comm]

/-- The trivial sign gives the identity. -/
theorem exteriorSignHom_one (q : ℕ) : G.exteriorSignHom (1 : EdgeSign E) R q = 𝟙 _ := by
  rw [← exterior_total G R q, exteriorSignHom]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [exteriorSign, EdgeSign.setSign_one, one_smul]

/-- The sign change of the exterior bundle is an involution. -/
theorem exteriorSignHom_self (q : ℕ) : G.exteriorSignHom ε R q ≫ G.exteriorSignHom ε R q = 𝟙 _ := by
  rw [exteriorSignHom_comp, EdgeSign.mul_self, exteriorSignHom_one]

/-- The sign change of exterior bundles as an automorphism of actual abelian sheaves. -/
def exteriorSignAbelianIso (q : ℕ) : G.exteriorBundleAbelian R q ≅ G.exteriorBundleAbelian R q where
  hom := G.exteriorSignHom ε R q
  inv := G.exteriorSignHom ε R q
  hom_inv_id := G.exteriorSignHom_self ε R q
  inv_hom_id := G.exteriorSignHom_self ε R q

/-- The map induced on actual cohomology of the exterior bundle by an edge sign. -/
def exteriorCohomologySign (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃+ Sheaf.H.{1} (G.exteriorBundleAbelian R q) j where
  toFun := Sheaf.H.map (G.exteriorSignHom ε R q) j
  invFun := Sheaf.H.map (G.exteriorSignHom ε R q) j
  left_inv x := by
    rw [← Sheaf.H.map_comp_apply, exteriorSignHom_self, Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← Sheaf.H.map_comp_apply, exteriorSignHom_self, Sheaf.H.map_id_apply]
  map_add' := map_add _

/-- The cohomology sign change is the map induced by the abelian sign change. -/
theorem exteriorCohomologySign_apply (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologySign ε R q j x = Sheaf.H.map (G.exteriorSignHom ε R q) j x := rfl

/-- The sign-changed class projected to a summand is the sign times the projection of the class. -/
theorem exteriorProj_sign (q j : ℕ) (S : Set.powersetCard E q)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    Sheaf.H.map (G.exteriorProj R q S) j (G.exteriorCohomologySign ε R q j x) =
      exteriorSign ε q S • Sheaf.H.map (G.exteriorProj R q S) j x := by
  rw [exteriorCohomologySign_apply, ← Sheaf.H.map_comp_apply, exteriorSignHom_proj,
    sheafH_map_zsmul_apply]

/-- The cohomology sign change is an involution. -/
@[simp] theorem exteriorCohomologySign_self (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologySign ε R q j (G.exteriorCohomologySign ε R q j x) = x :=
  (G.exteriorCohomologySign ε R q j).left_inv x

/-- The trivial sign acts trivially on exterior cohomology. -/
theorem exteriorCohomologySign_one (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologySign (1 : EdgeSign E) R q j x = x := by
  rw [exteriorCohomologySign_apply, exteriorSignHom_one, Sheaf.H.map_id_apply]

/-- The cohomology sign change of a product of signs is the composite. -/
theorem exteriorCohomologySign_mul (ε' : EdgeSign E) (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologySign (ε * ε') R q j x =
      G.exteriorCohomologySign ε' R q j (G.exteriorCohomologySign ε R q j x) := by
  rw [exteriorCohomologySign_apply, exteriorCohomologySign_apply, exteriorCohomologySign_apply,
    ← Sheaf.H.map_comp_apply, exteriorSignHom_comp]

variable [IsNoetherianRing R]

/-- The state vector of a sign-changed exterior class is the edge-sign scaling of its state
vector. -/
theorem exteriorCohomologyState_sign (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologyState R q j (G.exteriorCohomologySign ε R q j x) =
      G.edgeSignState ε R (G.exteriorCohomologyState R q j x) := by
  rw [exteriorCohomologyState_apply, exteriorCohomologyState_apply, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [edgeSignState_incStateEmbed, exteriorProj_sign, map_zsmul, Submodule.coe_smul_of_tower,
    map_zsmul, ← Int.cast_smul_eq_zsmul R, exteriorSign, EdgeSign.intCast_setSign]

/-- The map induced on actual exterior cohomology by an edge sign, as a linear isomorphism for the
original geometric base action. -/
def exteriorCohomologySignLinear (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R] Sheaf.H.{1} (G.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  { G.exteriorCohomologySign ε R q j with
    map_smul' := fun r x => by
      apply G.exteriorCohomologyState_injective R q j
      change G.exteriorCohomologyState R q j (G.exteriorCohomologySign ε R q j (r • x)) =
        G.exteriorCohomologyState R q j (r • G.exteriorCohomologySign ε R q j x)
      rw [exteriorCohomologyState_sign, map_smul, map_smul, map_smul,
        exteriorCohomologyState_sign] }

/-- The linear sign change has the same underlying map. -/
theorem exteriorCohomologySignLinear_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologySignLinear ε R q j x = G.exteriorCohomologySign ε R q j x := rfl

/-- Edge signs preserve the exterior cohomology products. -/
theorem exteriorCohomologySign_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    G.exteriorCohomologySign ε R (q + q') (i + j) (G.exteriorCohomologyProduct R q q' i j x y) =
      G.exteriorCohomologyProduct R q q' i j (G.exteriorCohomologySign ε R q i x)
        (G.exteriorCohomologySign ε R q' j y) := by
  apply G.exteriorCohomologyState_injective R (q + q') (i + j)
  rw [exteriorCohomologyState_sign, exteriorCohomologyState_product,
    exteriorCohomologyState_product, exteriorCohomologyState_sign,
    exteriorCohomologyState_sign, edgeSignState_incStateCup]

/-- Edge signs send the exterior cohomology unit to the unit. -/
theorem exteriorCohomologySign_unit :
    G.exteriorCohomologySign ε R 0 0 (G.exteriorCohomologyUnit R) = G.exteriorCohomologyUnit R := by
  apply G.exteriorCohomologyState_injective R 0 0
  rw [exteriorCohomologyState_sign, exteriorCohomologyState_unit, edgeSignState_incStateUnit]

end

end Multigraph

end BPFixedPoints
