import BPFixedPoints.Incidence.EdgeExteriorBundle
import BPFixedPoints.Incidence.VertexProjectiveTwistSectionProduct
import BPFixedPoints.Incidence.VertexProjectiveTwistChartRestriction
import BPFixedPoints.Incidence.ExteriorAlgebraBridge

/-! # Chart identification of the actual exterior bundle with Mathlib exterior powers

Sections over an open `W` of the actual dual edge bundle and of the actual exterior bundle are
modules over the ring of functions `Γ(X, W)` of the original vertex projective product. The
section-level exterior wedge `exteriorSectionWedge` maps the Mathlib exterior power
`⋀[Γ(X, W)]^(q+1)` of the dual edge sections to the sections of the actual exterior bundle of
degree `q+1`. It is induced by the alternatization of ordered iterated products of the original
twist sections, the edges of each summand taken in increasing order, so a tuple of sections
supported on edges in increasing order goes to their ordered product in the summand of their edge
set. It commutes with restriction. On every subopen of an original product chart it sends Mathlib's
exterior power basis of the chart frame to the chart frame basis of the exterior bundle, so it is
bijective there: on charts the actual finite biproduct of the twists by minus the degrees of the
`(q+1)`-element edge subsets is the `(q+1)`-th exterior power of the dual edge bundle. The section
exterior pairing (twist product, twist identity, shuffle sign, zero on shared edges) of two
wedges is the wedge of the concatenated tuple. Degree zero needs a unit section of the
untwisted multi-twist and is not treated here.
-/

namespace BPFixedPoints.Koszul
open Set Set.powersetCard

variable {A M I : Type*} [CommRing A] [AddCommGroup M] [Module A M] [LinearOrder I] [Fintype I]

/-- A wedge of a concatenated family is the sum of the products of the basis coordinates of the
two wedges over disjoint pairs of index sets, each placed at the basis vector of their union with
the sign of the sorting permutation. -/
theorem exteriorPower_ιMulti_append_eq_sum (b : Module.Basis I A M) {m n : ℕ} (x : Fin m → M)
    (y : Fin n → M) :
    exteriorPower.ιMulti A (m + n) (Fin.append x y) =
      ∑ S : powersetCard I m, ∑ T : powersetCard I n,
        if h : Disjoint S.val T.val then
          ((permOfDisjoint h).sign • ((b.exteriorPower m).repr (exteriorPower.ιMulti A m x) S *
            (b.exteriorPower n).repr (exteriorPower.ιMulti A n y) T)) •
              b.exteriorPower (m + n) (disjUnion h)
        else 0 := by
  apply Subtype.ext
  rw [exteriorPower.ιMulti_apply_coe, ← ExteriorAlgebra.ιMulti_mul_ιMulti]
  have hx := (b.exteriorPower m).sum_repr (exteriorPower.ιMulti A m x)
  have hy := (b.exteriorPower n).sum_repr (exteriorPower.ιMulti A n y)
  rw [← exteriorPower.ιMulti_apply_coe, ← exteriorPower.ιMulti_apply_coe]
  conv_lhs => rw [← hx, ← hy]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_smul_comm, exteriorPower.coe_basis A m b, exteriorPower.coe_basis A n b,
    exteriorPower.ιMulti_family_apply_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun (S : powersetCard I m) _ =>
    Finset.sum_congr rfl fun (T : powersetCard I n) _ => ?_
  split_ifs with h
  · rw [ExteriorAlgebra.ιMulti_family_mul_of_disjoint _ _ _ _ h, Submodule.coe_smul,
      exteriorPower.coe_basis A (m + n) b, exteriorPower.ιMulti_family_apply_coe]
    exact (smul_comm _ _ _).trans (smul_assoc _ _ _).symm
  · rw [ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint _ _ _ _ h, smul_zero, ZeroMemClass.coe_zero]

/-- The basis coordinates of a wedge of a concatenated family. -/
theorem exteriorPower_basis_repr_ιMulti_append (b : Module.Basis I A M) {m n : ℕ} (x : Fin m → M)
    (y : Fin n → M) (U : powersetCard I (m + n)) :
    (b.exteriorPower (m + n)).repr (exteriorPower.ιMulti A (m + n) (Fin.append x y)) U =
      ∑ S : powersetCard I m, ∑ T : powersetCard I n,
        if h : Disjoint S.val T.val then
          (if disjUnion h = U then (permOfDisjoint h).sign •
            ((b.exteriorPower m).repr (exteriorPower.ιMulti A m x) S *
              (b.exteriorPower n).repr (exteriorPower.ιMulti A n y) T) else 0)
        else 0 := by
  classical
  rw [exteriorPower_ιMulti_append_eq_sum b x y, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs with h hU
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, hU, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      ite_eq_right_iff.mpr (fun h' => absurd h' hU), smul_zero]
  · rw [map_zero, Finsupp.zero_apply]

end BPFixedPoints.Koszul

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The sections over an open of an actual morphism of sheaves of modules on the vertex product. -/
noncomputable def vertexSectionMap {M N : SheafOfModules (vertexScheme R V).ringCatSheaf} (φ : M ⟶ N)
    (W : (vertexScheme R V).Opens) : Γ(M, W) →ₗ[Γ(vertexScheme R V, W)] Γ(N, W) :=
  (φ.val.app (op W)).hom

variable {R V}

/-- Sections of a composite are the composite of the sections. -/
theorem vertexSectionMap_comp {M N K : SheafOfModules (vertexScheme R V).ringCatSheaf}
    (φ : M ⟶ N) (ψ : N ⟶ K)
    (W : (vertexScheme R V).Opens) (x : Γ(M, W)) :
    vertexSectionMap R V (φ ≫ ψ) W x = vertexSectionMap R V ψ W (vertexSectionMap R V φ W x) := rfl

/-- Sections of the identity are the identity. -/
theorem vertexSectionMap_id (M : SheafOfModules (vertexScheme R V).ringCatSheaf)
    (W : (vertexScheme R V).Opens) (x : Γ(M, W)) :
    vertexSectionMap R V (𝟙 M) W x = x := rfl

/-- Sections of a sum of morphisms are the sum of the sections. -/
theorem vertexSectionMap_add {M N : SheafOfModules (vertexScheme R V).ringCatSheaf} (φ ψ : M ⟶ N)
    (W : (vertexScheme R V).Opens) (x : Γ(M, W)) :
    vertexSectionMap R V (φ + ψ) W x = vertexSectionMap R V φ W x + vertexSectionMap R V ψ W x := rfl

/-- Sections of the zero morphism vanish. -/
theorem vertexSectionMap_zero {M N : SheafOfModules (vertexScheme R V).ringCatSheaf}
    (W : (vertexScheme R V).Opens) (x : Γ(M, W)) :
    vertexSectionMap R V (0 : M ⟶ N) W x = 0 := rfl

/-- Sections of a finite sum of morphisms are the sum of the sections. -/
theorem vertexSectionMap_sum {ι : Type} (s : Finset ι) {M N : SheafOfModules (vertexScheme R V).ringCatSheaf}
    (φ : ι → (M ⟶ N)) (W : (vertexScheme R V).Opens) (x : Γ(M, W)) :
    vertexSectionMap R V (∑ i ∈ s, φ i) W x = ∑ i ∈ s, vertexSectionMap R V (φ i) W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, vertexSectionMap_add, ih]

/-- Sections of a morphism commute with the restriction maps of the two sheaves. -/
theorem vertexSectionMap_restrict {M N : SheafOfModules (vertexScheme R V).ringCatSheaf} (φ : M ⟶ N)
    {W U : (vertexScheme R V).Opens} (i : W ⟶ U) (x : Γ(M, U)) :
    (Scheme.Modules.presheaf N).map i.op (vertexSectionMap R V φ U x) =
      vertexSectionMap R V φ W ((Scheme.Modules.presheaf M).map i.op x) :=
  (congrArg (fun k => k.hom x) (φ.val.naturality i.op)).symm

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (F : ι → SheafOfModules (vertexScheme R V).ringCatSheaf)

/-- Sections of an actual finite biproduct are the product of the sections of the summands. -/
noncomputable def vertexBiproductSectionsEquiv (W : (vertexScheme R V).Opens) :
    Γ((⨁ F : SheafOfModules (vertexScheme R V).ringCatSheaf), W) ≃ₗ[Γ(vertexScheme R V, W)]
      ((i : ι) → Γ(F i, W)) where
  toFun x i := vertexSectionMap R V (biproduct.π F i) W x
  map_add' x y := by ext i; exact map_add _ x y
  map_smul' r x := by ext i; exact map_smul _ r x
  invFun y := ∑ i, vertexSectionMap R V (biproduct.ι F i) W (y i)
  left_inv x := by
    have h := congrArg (fun φ => vertexSectionMap R V φ W x) (biproduct.total (f := F))
    simp only [vertexSectionMap_sum, vertexSectionMap_id] at h
    exact h
  right_inv y := by
    funext j
    dsimp only
    rw [map_sum]
    simp only [← vertexSectionMap_comp, biproduct.ι_π]
    rw [Finset.sum_eq_single j]
    · simp only [dite_true, eqToHom_refl]; rfl
    · intro i _ hij
      simp only [hij, dite_false]; rfl
    · simp

/-- Each component of a biproduct section is its image under the biproduct projection. -/
theorem vertexBiproductSectionsEquiv_apply (W : (vertexScheme R V).Opens)
    (x : Γ((⨁ F : SheafOfModules (vertexScheme R V).ringCatSheaf), W)) (i : ι) :
    vertexBiproductSectionsEquiv F W x i = vertexSectionMap R V (biproduct.π F i) W x := rfl

/-- A family of summand sections is the sum of their images under the biproduct inclusions. -/
theorem vertexBiproductSectionsEquiv_symm_apply (W : (vertexScheme R V).Opens) (y : (i : ι) → Γ(F i, W)) :
    (vertexBiproductSectionsEquiv F W).symm y = ∑ i, vertexSectionMap R V (biproduct.ι F i) W (y i) := rfl

/-- The component of an included summand section on its own summand is the section itself. -/
theorem vertexBiproductSectionsEquiv_ι_self (W : (vertexScheme R V).Opens) (i : ι) (z : Γ(F i, W)) :
    vertexBiproductSectionsEquiv F W (vertexSectionMap R V (biproduct.ι F i) W z) i = z := by
  change vertexSectionMap R V (biproduct.ι F i ≫ biproduct.π F i) W z = z
  rw [biproduct.ι_π_self]
  rfl

/-- The component of an included summand section on another summand vanishes. -/
theorem vertexBiproductSectionsEquiv_ι_ne (W : (vertexScheme R V).Opens) {i j : ι} (h : i ≠ j)
    (z : Γ(F i, W)) : vertexBiproductSectionsEquiv F W (vertexSectionMap R V (biproduct.ι F i) W z) j = 0 := by
  change vertexSectionMap R V (biproduct.ι F i ≫ biproduct.π F j) W z = 0
  rw [biproduct.ι_π_ne _ h]
  rfl

/-- Sections of an actual sheaf of modules on the vertex product agree when their restrictions to
the intersections with all product charts agree. -/
theorem vertexSections_ext_of_charts (M : SheafOfModules (vertexScheme R V).ringCatSheaf)
    (W : (vertexScheme R V).Opens) {s t : Γ(M, W)}
    (h : ∀ σ : V → Fin 2,
      (Scheme.Modules.presheaf M).map (homOfLE (inf_le_left : W ⊓ vertexChartOpen R V σ ≤ W)).op s =
        (Scheme.Modules.presheaf M).map (homOfLE (inf_le_left : W ⊓ vertexChartOpen R V σ ≤ W)).op t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨Scheme.Modules.presheaf M, Scheme.Modules.isSheaf M⟩
    (fun σ => W ⊓ vertexChartOpen R V σ) W (fun σ => homOfLE inf_le_left) ?_ s t h
  intro x hx
  obtain ⟨σ, y, hy⟩ := vertexChart_covers R V x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨σ, hx, ⟨y, hy⟩⟩

variable (R V) in
/-- The chart coefficient of a multi-twist on a subopen of a product chart, as a linear equivalence. -/
noncomputable def vertexTwistChartCoefficientEquiv (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    Γ(vertexTwistSheaf R V a, W) ≃ₗ[Γ(vertexScheme R V, W)] Γ(vertexScheme R V, W) :=
  LinearEquiv.ofLinearMap (vertexTwistSheafChartCoefficient R V a σ W hW)
    ((SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
      (vertexChartOpen R V σ) (vertexTwistSheafChartIso R V a σ)).inv.val.app
        (op (Over.mk (homOfLE hW)))).hom
    (LinearMap.ext fun y => by
      exact congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hW)))).hom y)
        (SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
          (vertexChartOpen R V σ) (vertexTwistSheafChartIso R V a σ)).inv_hom_id)
    (LinearMap.ext fun y => by
      exact congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hW)))).hom y)
        (SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
          (vertexChartOpen R V σ) (vertexTwistSheafChartIso R V a σ)).hom_inv_id)

/-- The chart coefficient equivalence applies the chart coefficient. -/
theorem vertexTwistChartCoefficientEquiv_apply (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistChartCoefficientEquiv R V a σ W hW x = vertexTwistSheafChartCoefficient R V a σ W hW x := rfl

variable (R) in
/-- Transport of sections of multi-twists along an equality of twists. -/
noncomputable def vertexTwistCast {a b : V → ℤ} (h : a = b) (W : (vertexScheme R V).Opens) :
    Γ(vertexTwistSheaf R V a, W) ≃ₗ[Γ(vertexScheme R V, W)] Γ(vertexTwistSheaf R V b, W) := by
  subst h; exact LinearEquiv.refl _ _

/-- Transport along a reflexive twist equality is the identity. -/
@[simp] theorem vertexTwistCast_rfl (a : V → ℤ) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistCast R (rfl : a = a) W x = x := rfl

/-- Transport of twist sections commutes with restriction. -/
theorem vertexTwistCast_restrict {a b : V → ℤ} (h : a = b) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Γ(vertexTwistSheaf R V a, U)) :
    (vertexTwistSheaf R V b).presheaf.map i.op (vertexTwistCast R h U x) =
      vertexTwistCast R h W ((vertexTwistSheaf R V a).presheaf.map i.op x) := by
  subst h; rfl

/-- Transport of twist sections preserves chart coefficients. -/
theorem vertexTwistCast_chart {a b : V → ℤ} (h : a = b) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V b σ W hW (vertexTwistCast R h W x) =
      vertexTwistSheafChartCoefficient R V a σ W hW x := by
  subst h; rfl

/-- Sections of the equality morphism of two equal multi-twists are the transport of twist sections. -/
theorem vertexSectionMap_eqToHom_twist {a b : V → ℤ} (h : a = b) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexSectionMap R V (eqToHom (congrArg (vertexTwistSheaf R V) h)) W x = vertexTwistCast R h W x := by
  subst h; rfl

omit [Fintype V] in
/-- The total twist of an ordered nonempty tuple of twists, folded from the left. -/
def vertexTupleTwist : (n : ℕ) → (Fin (n + 1) → V → ℤ) → V → ℤ
  | 0, a => a 0
  | n + 1, a => a 0 + vertexTupleTwist n (Fin.tail a)

omit [Fintype V] in
/-- The folded total twist is the sum of the twists. -/
theorem vertexTupleTwist_eq_sum : (n : ℕ) → (a : Fin (n + 1) → V → ℤ) → vertexTupleTwist n a = ∑ i, a i
  | 0, a => by simp [vertexTupleTwist]
  | n + 1, a => by
    rw [vertexTupleTwist, vertexTupleTwist_eq_sum n]
    conv_rhs => rw [Fin.sum_univ_succ]
    rfl

variable (R) in
/-- The ordered iterated section product of a nonempty tuple of multi-twist sections. -/
noncomputable def vertexTupleProduct (W : (vertexScheme R V).Opens) : (n : ℕ) → (a : Fin (n + 1) → V → ℤ) →
    MultilinearMap Γ(vertexScheme R V, W) (fun i => Γ(vertexTwistSheaf R V (a i), W))
      Γ(vertexTwistSheaf R V (vertexTupleTwist n a), W)
  | 0, a =>
    { toFun := fun x => x 0
      map_update_add' := fun m i x y => by
        obtain rfl : i = 0 := Fin.fin_one_eq_zero i
        simp only [Function.update_self]
      map_update_smul' := fun m i r x => by
        obtain rfl : i = 0 := Fin.fin_one_eq_zero i
        simp only [Function.update_self] }
  | n + 1, a => LinearMap.uncurryLeft
    { toFun := fun x0 =>
        (vertexTwistSectionProduct R V (a 0) (vertexTupleTwist n (Fin.tail a)) W x0).compMultilinearMap
          (vertexTupleProduct W n (Fin.tail a))
      map_add' := fun x y => by ext m; simp only [map_add, LinearMap.compMultilinearMap_apply,
        add_apply, LinearMap.add_apply]
      map_smul' := fun r x => by ext m; simp only [map_smul, LinearMap.compMultilinearMap_apply,
        smul_apply, LinearMap.smul_apply, RingHom.id_apply] }

/-- The ordered product of a single section is that section. -/
theorem vertexTupleProduct_zero (W : (vertexScheme R V).Opens) (a : Fin 1 → V → ℤ)
    (x : (i : Fin 1) → Γ(vertexTwistSheaf R V (a i), W)) :
    vertexTupleProduct R W 0 a x = x 0 := rfl

/-- The ordered product of a longer tuple is the first section times the ordered product of the tail. -/
theorem vertexTupleProduct_succ (W : (vertexScheme R V).Opens) (n : ℕ) (a : Fin (n + 2) → V → ℤ)
    (x : (i : Fin (n + 2)) → Γ(vertexTwistSheaf R V (a i), W)) :
    vertexTupleProduct R W (n + 1) a x =
      vertexTwistSectionProduct R V (a 0) (vertexTupleTwist n (Fin.tail a)) W (x 0)
        (vertexTupleProduct R W n (Fin.tail a) (Fin.tail x)) := rfl

/-- The ordered iterated product commutes with restriction. -/
theorem vertexTupleProduct_restrict {W U : (vertexScheme R V).Opens} (i : W ⟶ U) : (n : ℕ) →
    (a : Fin (n + 1) → V → ℤ) → (x : (k : Fin (n + 1)) → Γ(vertexTwistSheaf R V (a k), U)) →
    (vertexTwistSheaf R V (vertexTupleTwist n a)).presheaf.map i.op (vertexTupleProduct R U n a x) =
      vertexTupleProduct R W n a (fun k => (vertexTwistSheaf R V (a k)).presheaf.map i.op (x k))
  | 0, a, x => rfl
  | n + 1, a, x => by
    rw [vertexTupleProduct_succ, vertexTupleProduct_succ]
    exact (vertexTwistSectionProduct_restrict R V (a 0) (vertexTupleTwist n (Fin.tail a)) i (x 0)
      (vertexTupleProduct R U n (Fin.tail a) (Fin.tail x))).trans
        (congrArg _ (vertexTupleProduct_restrict i n (Fin.tail a) (Fin.tail x)))

/-- On a chart, the coefficient of the ordered iterated product is the product of coefficients. -/
theorem vertexTupleProduct_chart (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) : (n : ℕ) →
    (a : Fin (n + 1) → V → ℤ) → (x : (k : Fin (n + 1)) → Γ(vertexTwistSheaf R V (a k), W)) →
    vertexTwistSheafChartCoefficient R V (vertexTupleTwist n a) σ W hW (vertexTupleProduct R W n a x) =
      ∏ k, vertexTwistSheafChartCoefficient R V (a k) σ W hW (x k)
  | 0, a, x => by rw [Fin.prod_univ_one]; rfl
  | n + 1, a, x => by
    rw [vertexTupleProduct_succ, Fin.prod_univ_succ]
    exact (vertexTwistSectionProduct_chart R V (a 0) (vertexTupleTwist n (Fin.tail a)) σ W hW (x 0)
      (vertexTupleProduct R W n (Fin.tail a) (Fin.tail x))).trans
        (congrArg _ (vertexTupleProduct_chart σ W hW n (Fin.tail a) (Fin.tail x)))

end BPFixedPoints.ProjectiveLine

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ProjectiveLine
open Set.powersetCard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable {V E : Type} [DecidableEq V] [Fintype V] (G : Multigraph V E)
variable (R : Type) [CommRing R]

/-- The twist of the dual line sheaf of an edge: minus its endpoint count. -/
def edgeDualTwist (e : E) : V → ℤ := fun v => -(G.endCount e v : ℤ)

omit [Fintype V] in
/-- The negative twist of a disjoint union of edge subsets is the sum of the negative twists. -/
theorem exteriorTwist_disjUnion {p q : ℕ} {S : Set.powersetCard E p} {T : Set.powersetCard E q}
    (h : Disjoint S.val T.val) :
    (fun v => -(G.deg S v : ℤ)) + (fun v => -(G.deg T v : ℤ)) =
      fun v => -(G.deg (disjUnion h : Set.powersetCard E (p + q)) v : ℤ) := by
  funext v
  rw [Pi.add_apply, coe_disjUnion, deg, deg, deg, Finset.sum_disjUnion, Nat.cast_add, neg_add]

variable [Fintype E]

/-! ### Sections of the dual edge bundle and of the exterior bundle -/

/-- The component of a section of the dual edge bundle on the dual line sheaf of one edge. -/
noncomputable def edgeDualComponent (W : (vertexScheme R V).Opens) (e : E) :
    Γ(G.edgeDualBundle R, W) →ₗ[Γ(vertexScheme R V, W)] Γ(vertexTwistSheaf R V (G.edgeDualTwist e), W) :=
  vertexSectionMap R V (biproduct.π (fun e : E => G.edgeDualLineSheaf R e) e) W

/-- The inclusion of the sections of the dual line sheaf of one edge into the dual edge bundle. -/
noncomputable def edgeDualInclusion (W : (vertexScheme R V).Opens) (e : E) :
    Γ(vertexTwistSheaf R V (G.edgeDualTwist e), W) →ₗ[Γ(vertexScheme R V, W)] Γ(G.edgeDualBundle R, W) :=
  vertexSectionMap R V (biproduct.ι (fun e : E => G.edgeDualLineSheaf R e) e) W

/-- Edge components of dual edge sections commute with restriction. -/
theorem edgeDualComponent_restrict {W U : (vertexScheme R V).Opens} (i : W ⟶ U) (e : E)
    (x : Γ(G.edgeDualBundle R, U)) :
    (vertexTwistSheaf R V (G.edgeDualTwist e)).presheaf.map i.op (G.edgeDualComponent R U e x) =
      G.edgeDualComponent R W e ((Scheme.Modules.presheaf (G.edgeDualBundle R)).map i.op x) :=
  vertexSectionMap_restrict _ i x

/-- The component of a section of the exterior bundle on the summand of one edge subset. -/
noncomputable def exteriorSectionProjection (q : ℕ) (W : (vertexScheme R V).Opens) (S : Set.powersetCard E q) :
    Γ(G.exteriorBundle R q, W) →ₗ[Γ(vertexScheme R V, W)] Γ(G.exteriorSummand R S, W) :=
  vertexSectionMap R V (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S) W

/-- The inclusion of the sections of the summand of one edge subset into the exterior bundle. -/
noncomputable def exteriorSectionInclusion (q : ℕ) (W : (vertexScheme R V).Opens) (S : Set.powersetCard E q) :
    Γ(G.exteriorSummand R S, W) →ₗ[Γ(vertexScheme R V, W)] Γ(G.exteriorBundle R q, W) :=
  vertexSectionMap R V (biproduct.ι (fun S : Set.powersetCard E q => G.exteriorSummand R S) S) W

/-- Summand inclusions commute with restriction. -/
theorem exteriorSectionInclusion_restrict (q : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (S : Set.powersetCard E q) (x : Γ(G.exteriorSummand R S, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R q)).map i.op (G.exteriorSectionInclusion R q U S x) =
      G.exteriorSectionInclusion R q W S ((Scheme.Modules.presheaf (G.exteriorSummand R S)).map i.op x) :=
  vertexSectionMap_restrict _ i x

/-- Summand projections commute with restriction. -/
theorem exteriorSectionProjection_restrict (q : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (S : Set.powersetCard E q) (x : Γ(G.exteriorBundle R q, U)) :
    (Scheme.Modules.presheaf (G.exteriorSummand R S)).map i.op (G.exteriorSectionProjection R q U S x) =
      G.exteriorSectionProjection R q W S ((Scheme.Modules.presheaf (G.exteriorBundle R q)).map i.op x) :=
  vertexSectionMap_restrict _ i x

variable [LinearOrder E]

/-- The component of an included edge section on its own edge is the section itself. -/
theorem edgeDualComponent_inclusion_self (W : (vertexScheme R V).Opens) (e : E)
    (z : Γ(vertexTwistSheaf R V (G.edgeDualTwist e), W)) :
    G.edgeDualComponent R W e (G.edgeDualInclusion R W e z) = z :=
  vertexBiproductSectionsEquiv_ι_self (fun e : E => G.edgeDualLineSheaf R e) W e z

/-- The component of an included edge section on another edge vanishes. -/
theorem edgeDualComponent_inclusion_ne (W : (vertexScheme R V).Opens) {e e' : E} (h : e ≠ e')
    (z : Γ(vertexTwistSheaf R V (G.edgeDualTwist e), W)) :
    G.edgeDualComponent R W e' (G.edgeDualInclusion R W e z) = 0 :=
  vertexBiproductSectionsEquiv_ι_ne (fun e : E => G.edgeDualLineSheaf R e) W h z

/-- The component of an included summand section on its own summand is the section itself. -/
theorem exteriorSectionInclusion_component_self (q : ℕ) (W : (vertexScheme R V).Opens)
    (S : Set.powersetCard E q) (z : Γ(G.exteriorSummand R S, W)) :
    vertexBiproductSectionsEquiv (fun S : Set.powersetCard E q => G.exteriorSummand R S) W
      (G.exteriorSectionInclusion R q W S z) S = z :=
  vertexBiproductSectionsEquiv_ι_self (fun S : Set.powersetCard E q => G.exteriorSummand R S) W S z

/-- The component of an included summand section on another summand vanishes. -/
theorem exteriorSectionInclusion_component_ne (q : ℕ) (W : (vertexScheme R V).Opens)
    {S T : Set.powersetCard E q} (h : S ≠ T) (z : Γ(G.exteriorSummand R S, W)) :
    vertexBiproductSectionsEquiv (fun S : Set.powersetCard E q => G.exteriorSummand R S) W
      (G.exteriorSectionInclusion R q W S z) T = 0 :=
  vertexBiproductSectionsEquiv_ι_ne (fun S : Set.powersetCard E q => G.exteriorSummand R S) W h z

/-! ### The section-level exterior wedge -/

/-- The twists of the dual line sheaves of the edges of a nonempty edge subset, in increasing
edge order. -/
noncomputable def exteriorOrderedTwist {q : ℕ} (S : Set.powersetCard E (q + 1)) : Fin (q + 1) → V → ℤ :=
  fun i => G.edgeDualTwist (ofFinEmbEquiv.symm S i)

omit [Fintype V] [Fintype E] in
/-- The ordered dual edge twists of an edge subset add up to minus its multigraph degree. -/
theorem vertexTupleTwist_exteriorOrderedTwist {q : ℕ} (S : Set.powersetCard E (q + 1)) :
    vertexTupleTwist q (G.exteriorOrderedTwist S) = fun v => -(G.deg S v : ℤ) := by
  rw [vertexTupleTwist_eq_sum]
  funext v
  rw [Finset.sum_apply, deg, Nat.cast_sum, ← Finset.sum_neg_distrib,
    ← Finset.map_orderEmbOfFin_univ (S : Finset E) S.prop, Finset.sum_map]
  rfl

/-- The ordered product of the components of a tuple of dual edge sections on the edges of each
nonempty edge subset, placed in the corresponding summand of the exterior bundle. -/
noncomputable def exteriorOrderedProduct (q : ℕ) (W : (vertexScheme R V).Opens) :
    MultilinearMap Γ(vertexScheme R V, W) (fun _ : Fin (q + 1) => Γ(G.edgeDualBundle R, W))
      Γ(G.exteriorBundle R (q + 1), W) :=
  (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S)
      W).symm.toLinearMap.compMultilinearMap
    (MultilinearMap.pi fun S =>
      (vertexTwistCast R (G.vertexTupleTwist_exteriorOrderedTwist S) W).toLinearMap.compMultilinearMap
        ((vertexTupleProduct R W q (G.exteriorOrderedTwist S)).compLinearMap
          fun i => G.edgeDualComponent R W (ofFinEmbEquiv.symm S i)))

/-- Each summand component of the ordered product is the transported ordered product of the
edge components. -/
theorem exteriorOrderedProduct_component (q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) (S : Set.powersetCard E (q + 1)) :
    vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W
        (G.exteriorOrderedProduct R q W x) S =
      vertexTwistCast R (G.vertexTupleTwist_exteriorOrderedTwist S) W
        (vertexTupleProduct R W q (G.exteriorOrderedTwist S)
          fun i => G.edgeDualComponent R W (ofFinEmbEquiv.symm S i) (x i)) := by
  exact congrFun ((vertexBiproductSectionsEquiv
    (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W).apply_symm_apply _) S

/-- The section-level exterior wedge: the map from the `(q+1)`-th exterior power, over the ring of
functions of an open, of the sections of the dual edge bundle to the sections of the actual exterior
bundle, induced by the alternatization of the ordered products. -/
noncomputable def exteriorSectionWedge (q : ℕ) (W : (vertexScheme R V).Opens) :
    ⋀[Γ(vertexScheme R V, W)]^(q + 1) Γ(G.edgeDualBundle R, W) →ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorBundle R (q + 1), W) :=
  exteriorPower.alternatingMapLinearEquiv (MultilinearMap.alternatization (G.exteriorOrderedProduct R q W))

/-- On a wedge of sections, the section-level exterior wedge is the signed sum of ordered products. -/
theorem exteriorSectionWedge_ιMulti (q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) x) =
      ∑ τ : Equiv.Perm (Fin (q + 1)), Equiv.Perm.sign τ • G.exteriorOrderedProduct R q W (x ∘ τ) := by
  rw [exteriorSectionWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply]
  rfl

/-- Each summand component of the section-level exterior wedge of a wedge of sections is the
signed sum of the transported ordered products of the edge components. -/
theorem exteriorSectionWedge_component (q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) (T : Set.powersetCard E (q + 1)) :
    vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W
        (G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) x)) T =
      ∑ τ : Equiv.Perm (Fin (q + 1)), Equiv.Perm.sign τ •
        vertexTwistCast R (G.vertexTupleTwist_exteriorOrderedTwist T) W
          (vertexTupleProduct R W q (G.exteriorOrderedTwist T)
            fun i => G.edgeDualComponent R W (ofFinEmbEquiv.symm T i) (x (τ i))) := by
  rw [exteriorSectionWedge_ιMulti, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, Pi.smul_apply, exteriorOrderedProduct_component]
  rfl

/-- The ordered products commute with restriction. -/
theorem exteriorOrderedProduct_restrict (q : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Fin (q + 1) → Γ(G.edgeDualBundle R, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R (q + 1))).map i.op (G.exteriorOrderedProduct R q U x) =
      G.exteriorOrderedProduct R q W
        (fun k => (Scheme.Modules.presheaf (G.edgeDualBundle R)).map i.op (x k)) := by
  apply (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W).injective
  funext S
  refine (vertexSectionMap_restrict
    (biproduct.π (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) S) i
      (G.exteriorOrderedProduct R q U x)).symm.trans ?_
  change (vertexTwistSheaf R V (fun v => -(G.deg S v : ℤ))).presheaf.map i.op
      (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) U
        (G.exteriorOrderedProduct R q U x) S) = _
  rw [exteriorOrderedProduct_component, exteriorOrderedProduct_component]
  refine (vertexTwistCast_restrict (G.vertexTupleTwist_exteriorOrderedTwist S) i _).trans ?_
  refine congrArg _ ((vertexTupleProduct_restrict i q _ _).trans ?_)
  exact congrArg _ (funext fun k => G.edgeDualComponent_restrict R i _ (x k))

/-- The section-level exterior wedge commutes with restriction to smaller opens. -/
theorem exteriorSectionWedge_restrict (q : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Fin (q + 1) → Γ(G.edgeDualBundle R, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R (q + 1))).map i.op
        (G.exteriorSectionWedge R q U (exteriorPower.ιMulti _ (q + 1) x)) =
      G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1)
        fun k => (Scheme.Modules.presheaf (G.edgeDualBundle R)).map i.op (x k)) := by
  rw [exteriorSectionWedge_ιMulti, exteriorSectionWedge_ιMulti, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, exteriorOrderedProduct_restrict]
  rfl

/-- The section-level exterior wedge of sections supported on single edges vanishes when an edge
repeats. -/
theorem exteriorSectionWedge_single_of_not_injective (q : ℕ) (W : (vertexScheme R V).Opens)
    (e : Fin (q + 1) → E) (he : ¬Function.Injective e)
    (y : (k : Fin (q + 1)) → Γ(vertexTwistSheaf R V (G.edgeDualTwist (e k)), W)) :
    G.exteriorSectionWedge R q W
      (exteriorPower.ιMulti _ (q + 1) fun k => G.edgeDualInclusion R W (e k) (y k)) = 0 := by
  apply (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W).injective
  rw [map_zero]
  funext T
  rw [exteriorSectionWedge_component, Pi.zero_apply]
  refine Finset.sum_eq_zero fun τ _ => ?_
  obtain ⟨a, ha⟩ : ∃ a, e (τ a) ≠ ofFinEmbEquiv.symm T a := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    apply he
    have he' : e = ofFinEmbEquiv.symm T ∘ τ.symm := funext fun k => by
      simpa using hall (τ.symm k)
    rw [he']
    exact (ofFinEmbEquiv.symm T).injective.comp τ.symm.injective
  rw [MultilinearMap.map_coord_zero _ a (G.edgeDualComponent_inclusion_ne R W ha _), map_zero, smul_zero]

/-- The section-level exterior wedge of sections supported on the edges of an edge subset, taken in
increasing edge order, is their ordered product placed in the summand of that subset. -/
theorem exteriorSectionWedge_ordered (q : ℕ) (W : (vertexScheme R V).Opens) (S : Set.powersetCard E (q + 1))
    (y : (k : Fin (q + 1)) → Γ(vertexTwistSheaf R V (G.exteriorOrderedTwist S k), W)) :
    G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1)
        fun k => G.edgeDualInclusion R W (ofFinEmbEquiv.symm S k) (y k)) =
      G.exteriorSectionInclusion R (q + 1) W S (vertexTwistCast R (G.vertexTupleTwist_exteriorOrderedTwist S) W
        (vertexTupleProduct R W q (G.exteriorOrderedTwist S) y)) := by
  apply (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E (q + 1) => G.exteriorSummand R S) W).injective
  funext T
  rw [exteriorSectionWedge_component]
  by_cases hT : S = T
  · subst hT
    rw [exteriorSectionInclusion_component_self, Finset.sum_eq_single 1]
    · rw [Equiv.Perm.sign_one, one_smul]
      exact congrArg _ (congrArg _ (funext fun i => G.edgeDualComponent_inclusion_self R W _ (y i)))
    · intro τ _ hτ
      obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
        by_contra h
        simp only [not_exists, ne_eq, not_not] at h
        exact hτ (Equiv.ext h)
      rw [MultilinearMap.map_coord_zero _ a (G.edgeDualComponent_inclusion_ne R W
        ((ofFinEmbEquiv.symm S).injective.ne ha) _), map_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [G.exteriorSectionInclusion_component_ne R _ _ hT]
    refine Finset.sum_eq_zero fun τ _ => ?_
    obtain ⟨a, ha⟩ : ∃ a, ofFinEmbEquiv.symm S (τ a) ≠ ofFinEmbEquiv.symm T a := by
      by_contra hall
      simp only [not_exists, ne_eq, not_not] at hall
      apply hT
      have hst : (ofFinEmbEquiv.symm S : Fin (q + 1) → E) ∘ τ = ofFinEmbEquiv.symm T := funext hall
      have hr : Set.range (ofFinEmbEquiv.symm S) = Set.range (ofFinEmbEquiv.symm T) := by
        rw [← hst, EquivLike.range_comp]
      apply Subtype.ext
      ext i
      have h1 := mem_range_ofFinEmbEquiv_symm_iff_mem S i
      have h2 := mem_range_ofFinEmbEquiv_symm_iff_mem T i
      rw [hr] at h1
      exact h1.symm.trans h2
    rw [MultilinearMap.map_coord_zero _ a (G.edgeDualComponent_inclusion_ne R W ha _), map_zero, smul_zero]

/-- The inverse of the degree-one identification followed by the projection to the summand of a
singleton is the projection to the edge followed by the singleton identity. -/
theorem exteriorBundleOneIso_inv_π (e : E) :
    (G.exteriorBundleOneIso R).inv ≫
        biproduct.π (fun S : Set.powersetCard E 1 => G.exteriorSummand R S) (ofSingleton e) =
      biproduct.π (fun e : E => G.edgeDualLineSheaf R e) e ≫ eqToHom (G.exteriorSummand_singleton R e).symm := by
  refine biproduct.hom_ext' _ _ fun e' => ?_
  rw [ι_exteriorBundleOneIso_inv_assoc]
  by_cases h : e' = e
  · subst h
    rw [biproduct.ι_π_self, biproduct.ι_π_self_assoc]
    exact Category.comp_id _
  · rw [biproduct.ι_π_ne _ (ofSingleton.injective.ne h), biproduct.ι_π_ne_assoc _ h]
    exact (comp_zero).trans zero_comp.symm

/-- In degree one, the section-level exterior wedge of a single dual edge section is its image
under the inverse of the degree-one identification of the exterior bundle with the dual edge
bundle. -/
theorem exteriorSectionWedge_one (W : (vertexScheme R V).Opens) (x : Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionWedge R 0 W (exteriorPower.ιMulti _ 1 fun _ => x) =
      vertexSectionMap R V (G.exteriorBundleOneIso R).inv W x := by
  apply (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E 1 => G.exteriorSummand R S) W).injective
  funext S
  obtain ⟨e, rfl⟩ := ofSingleton.surjective S
  have hs : ofFinEmbEquiv.symm (ofSingleton e) 0 = e := Finset.orderEmbOfFin_singleton e 0
  have hm : biproduct.π (fun e : E => G.edgeDualLineSheaf R e) (ofFinEmbEquiv.symm (ofSingleton e) 0) ≫
      eqToHom (congrArg (vertexTwistSheaf R V) (G.vertexTupleTwist_exteriorOrderedTwist (ofSingleton e))) =
      biproduct.π (fun e : E => G.edgeDualLineSheaf R e) e ≫ eqToHom (G.exteriorSummand_singleton R e).symm := by
    rw [← biproduct.π_comp_eqToHom (fun e : E => G.edgeDualLineSheaf R e) hs.symm, Category.assoc,
      eqToHom_trans]
  have : Subsingleton (Equiv.Perm (Fin (0 + 1))) :=
    ⟨fun a b => Equiv.ext fun i => Subsingleton.elim (α := Fin 1) _ _⟩
  rw [exteriorSectionWedge_component, Fintype.sum_subsingleton _ 1, Equiv.Perm.sign_one, one_smul,
    vertexTupleProduct_zero]
  change vertexTwistCast R _ W (G.edgeDualComponent R W _ x) = vertexSectionMap R V
    ((G.exteriorBundleOneIso R).inv ≫
      biproduct.π (fun S : Set.powersetCard E 1 => G.exteriorSummand R S) (ofSingleton e)) W x
  rw [exteriorBundleOneIso_inv_π, ← hm, ← vertexSectionMap_eqToHom_twist]
  rfl

/-! ### Bijectivity on product charts -/

section Chart

variable (σ : V → Fin 2) (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)

/-- On a subopen of a product chart, the chart coordinates of the sections of the dual edge bundle. -/
noncomputable def edgeDualChartCoordinates :
    Γ(G.edgeDualBundle R, W) ≃ₗ[Γ(vertexScheme R V, W)] (E → Γ(vertexScheme R V, W)) :=
  (vertexBiproductSectionsEquiv (fun e : E => G.edgeDualLineSheaf R e) W).trans
    (LinearEquiv.piCongrRight fun e => vertexTwistChartCoefficientEquiv R V (G.edgeDualTwist e) σ W hW)

/-- Each chart coordinate of a dual edge section is the chart coefficient of its edge component. -/
theorem edgeDualChartCoordinates_apply (x : Γ(G.edgeDualBundle R, W)) (e : E) :
    G.edgeDualChartCoordinates R σ W hW x e =
      vertexTwistSheafChartCoefficient R V (G.edgeDualTwist e) σ W hW (G.edgeDualComponent R W e x) := rfl

/-- On a subopen of a product chart, the chart frame basis of the sections of the dual edge bundle. -/
noncomputable def edgeDualChartBasis :
    Module.Basis E Γ(vertexScheme R V, W) Γ(G.edgeDualBundle R, W) :=
  Module.Basis.ofEquivFun (G.edgeDualChartCoordinates R σ W hW)

/-- The coordinates in the chart frame basis are the chart coefficients of the edge components. -/
theorem edgeDualChartBasis_repr (x : Γ(G.edgeDualBundle R, W)) (e : E) :
    (G.edgeDualChartBasis R σ W hW).repr x e =
      vertexTwistSheafChartCoefficient R V (G.edgeDualTwist e) σ W hW (G.edgeDualComponent R W e x) :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

/-- On a subopen of a product chart, the chart coordinates of the sections of the exterior bundle. -/
noncomputable def exteriorChartCoordinates (q : ℕ) :
    Γ(G.exteriorBundle R q, W) ≃ₗ[Γ(vertexScheme R V, W)] (Set.powersetCard E q → Γ(vertexScheme R V, W)) :=
  (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E q => G.exteriorSummand R S) W).trans
    (LinearEquiv.piCongrRight fun S => vertexTwistChartCoefficientEquiv R V (fun v => -(G.deg S v : ℤ)) σ W hW)

/-- Each chart coordinate of an exterior section is the chart coefficient of its summand component. -/
theorem exteriorChartCoordinates_apply (q : ℕ) (x : Γ(G.exteriorBundle R q, W)) (S : Set.powersetCard E q) :
    G.exteriorChartCoordinates R σ W hW q x S =
      vertexTwistSheafChartCoefficient R V (fun v => -(G.deg S v : ℤ)) σ W hW
        (vertexBiproductSectionsEquiv (fun S : Set.powersetCard E q => G.exteriorSummand R S) W x S) := rfl

/-- On a subopen of a product chart, the chart frame basis of the sections of the exterior bundle. -/
noncomputable def exteriorChartBasis (q : ℕ) :
    Module.Basis (Set.powersetCard E q) Γ(vertexScheme R V, W) Γ(G.exteriorBundle R q, W) :=
  Module.Basis.ofEquivFun (G.exteriorChartCoordinates R σ W hW q)

/-- On a chart, the coordinates of an ordered product are the products of the edge coordinates. -/
theorem exteriorChartCoordinates_orderedProduct (q : ℕ) (x : Fin (q + 1) → Γ(G.edgeDualBundle R, W))
    (T : Set.powersetCard E (q + 1)) :
    G.exteriorChartCoordinates R σ W hW (q + 1) (G.exteriorOrderedProduct R q W x) T =
      ∏ i, (G.edgeDualChartBasis R σ W hW).repr (x i) (ofFinEmbEquiv.symm T i) := by
  rw [exteriorChartCoordinates_apply, exteriorOrderedProduct_component, vertexTwistCast_chart,
    vertexTupleProduct_chart]
  rfl

/-- On a chart, the coordinates of the section-level exterior wedge of a wedge of sections are the
maximal minors of the coordinate matrix. -/
theorem exteriorChartCoordinates_wedge_ιMulti (q : ℕ) (x : Fin (q + 1) → Γ(G.edgeDualBundle R, W))
    (T : Set.powersetCard E (q + 1)) :
    G.exteriorChartCoordinates R σ W hW (q + 1)
        (G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) x)) T =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower (q + 1)).repr (exteriorPower.ιMulti _ (q + 1) x) T := by
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_apply,
    exteriorSectionWedge_ιMulti, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, Pi.smul_apply, exteriorChartCoordinates_orderedProduct]
  rfl

/-- On a chart, the chart coordinates of the section-level exterior wedge are the coordinates in
the exterior power basis of the chart frame. -/
theorem exteriorChartCoordinates_wedge (q : ℕ)
    (z : ⋀[Γ(vertexScheme R V, W)]^(q + 1) Γ(G.edgeDualBundle R, W)) (T : Set.powersetCard E (q + 1)) :
    G.exteriorChartCoordinates R σ W hW (q + 1) (G.exteriorSectionWedge R q W z) T =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower (q + 1)).repr z T := by
  have h : (LinearMap.proj T).comp ((G.exteriorChartCoordinates R σ W hW (q + 1)).toLinearMap.comp
      (G.exteriorSectionWedge R q W)) = ((G.edgeDualChartBasis R σ W hW).exteriorPower (q + 1)).coord T := by
    apply exteriorPower.linearMap_ext
    ext x
    exact G.exteriorChartCoordinates_wedge_ιMulti R σ W hW q x T
  exact LinearMap.congr_fun h z

/-- On a subopen of a product chart, the linear equivalence from the exterior power of the dual
edge sections to the exterior bundle sections matching the exterior power basis of the chart frame
with the chart frame basis of the exterior bundle. -/
noncomputable def exteriorChartWedgeEquiv (q : ℕ) :
    ⋀[Γ(vertexScheme R V, W)]^(q + 1) Γ(G.edgeDualBundle R, W) ≃ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorBundle R (q + 1), W) :=
  ((G.edgeDualChartBasis R σ W hW).exteriorPower (q + 1)).repr.trans
    (G.exteriorChartBasis R σ W hW (q + 1)).repr.symm

/-- On a chart, the basis-matching equivalence is the section-level exterior wedge. -/
theorem exteriorChartWedgeEquiv_apply (q : ℕ)
    (z : ⋀[Γ(vertexScheme R V, W)]^(q + 1) Γ(G.edgeDualBundle R, W)) :
    G.exteriorChartWedgeEquiv R σ W hW q z = G.exteriorSectionWedge R q W z := by
  apply (G.exteriorChartBasis R σ W hW (q + 1)).repr.injective
  rw [exteriorChartWedgeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext T
  rw [exteriorChartBasis, Module.Basis.ofEquivFun_repr_apply, exteriorChartCoordinates_wedge]

/-- On a chart, the section-level exterior wedge sends the exterior power basis of the chart frame
to the chart frame basis of the exterior bundle. -/
theorem exteriorSectionWedge_basis (q : ℕ) (S : Set.powersetCard E (q + 1)) :
    G.exteriorSectionWedge R q W ((G.edgeDualChartBasis R σ W hW).exteriorPower (q + 1) S) =
      G.exteriorChartBasis R σ W hW (q + 1) S := by
  rw [← exteriorChartWedgeEquiv_apply, exteriorChartWedgeEquiv, LinearEquiv.trans_apply,
    Module.Basis.repr_self, Module.Basis.repr_symm_single, one_smul]

end Chart

/-- On every subopen of a product chart, the section-level exterior wedge is bijective. -/
theorem exteriorSectionWedge_bijective (q : ℕ) (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) : Function.Bijective (G.exteriorSectionWedge R q W) := by
  have h : ⇑(G.exteriorSectionWedge R q W) = G.exteriorChartWedgeEquiv R σ W hW q :=
    funext fun z => (G.exteriorChartWedgeEquiv_apply R σ W hW q z).symm
  rw [h]
  exact (G.exteriorChartWedgeEquiv R σ W hW q).bijective

/-! ### Multiplicativity -/

section Pairing

/-- Exterior multiplication of two summands on sections: for disjoint edge subsets the original twist
section product, the twist identity onto the union, the inclusion of the union summand and the
shuffle sign; zero when the edge subsets share an edge. -/
noncomputable def exteriorSummandProduct {p q : ℕ} (S : Set.powersetCard E p) (T : Set.powersetCard E q)
    (W : (vertexScheme R V).Opens) :
    Γ(G.exteriorSummand R S, W) →ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorSummand R T, W) →ₗ[Γ(vertexScheme R V, W)] Γ(G.exteriorBundle R (p + q), W) :=
  if h : Disjoint S.val T.val then
    Koszul.shuffleSign (R := ℤ) S.val T.val •
      (vertexTwistSectionProduct R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)) W).compr₂
        (G.exteriorSectionInclusion R (p + q) W (disjUnion h) ∘ₗ
          (vertexTwistCast R (G.exteriorTwist_disjUnion h) W).toLinearMap)
  else 0

/-- The section-level exterior pairing of the actual exterior bundles: the sum over pairs of edge
subsets of the exterior multiplication of the summand components. -/
noncomputable def exteriorSectionPairing (p q : ℕ) (W : (vertexScheme R V).Opens) :
    Γ(G.exteriorBundle R p, W) →ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorBundle R q, W) →ₗ[Γ(vertexScheme R V, W)] Γ(G.exteriorBundle R (p + q), W) :=
  ∑ S : Set.powersetCard E p, ∑ T : Set.powersetCard E q,
    ((G.exteriorSummandProduct R S T W).compl₂ (G.exteriorSectionProjection R q W T)).comp
      (G.exteriorSectionProjection R p W S)

/-- The section exterior pairing is the sum of the summand products of the components. -/
theorem exteriorSectionPairing_apply (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Γ(G.exteriorBundle R p, W)) (y : Γ(G.exteriorBundle R q, W)) :
    G.exteriorSectionPairing R p q W x y = ∑ S : Set.powersetCard E p, ∑ T : Set.powersetCard E q,
      G.exteriorSummandProduct R S T W (G.exteriorSectionProjection R p W S x)
        (G.exteriorSectionProjection R q W T y) := by
  simp only [exteriorSectionPairing, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.compl₂_apply]

/-- For disjoint edge subsets, exterior multiplication of the summands is the shuffle sign times the
inclusion into the union summand of the transported twist section product. -/
theorem exteriorSummandProduct_of_disjoint {p q : ℕ} {S : Set.powersetCard E p} {T : Set.powersetCard E q}
    (h : Disjoint S.val T.val) (W : (vertexScheme R V).Opens) (x : Γ(G.exteriorSummand R S, W))
    (y : Γ(G.exteriorSummand R T, W)) :
    G.exteriorSummandProduct R S T W x y = Koszul.shuffleSign (R := ℤ) S.val T.val •
      G.exteriorSectionInclusion R (p + q) W (disjUnion h) (vertexTwistCast R (G.exteriorTwist_disjUnion h) W
        (vertexTwistSectionProduct R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)) W x y)) := by
  simp only [exteriorSummandProduct, h, ↓reduceDIte]
  rfl

/-- For edge subsets sharing an edge, exterior multiplication of the summands vanishes. -/
theorem exteriorSummandProduct_of_not_disjoint {p q : ℕ} {S : Set.powersetCard E p}
    {T : Set.powersetCard E q} (h : ¬Disjoint S.val T.val) (W : (vertexScheme R V).Opens)
    (x : Γ(G.exteriorSummand R S, W)) (y : Γ(G.exteriorSummand R T, W)) :
    G.exteriorSummandProduct R S T W x y = 0 := by
  simp only [exteriorSummandProduct, h, ↓reduceDIte]
  rfl

/-- Exterior multiplication of two summands commutes with restriction. -/
theorem exteriorSummandProduct_restrict {p q : ℕ} (S : Set.powersetCard E p) (T : Set.powersetCard E q)
    {W U : (vertexScheme R V).Opens} (i : W ⟶ U) (x : Γ(G.exteriorSummand R S, U))
    (y : Γ(G.exteriorSummand R T, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R (p + q))).map i.op (G.exteriorSummandProduct R S T U x y) =
      G.exteriorSummandProduct R S T W ((Scheme.Modules.presheaf (G.exteriorSummand R S)).map i.op x)
        ((Scheme.Modules.presheaf (G.exteriorSummand R T)).map i.op y) := by
  by_cases h : Disjoint S.val T.val
  · rw [G.exteriorSummandProduct_of_disjoint R h, G.exteriorSummandProduct_of_disjoint R h, map_zsmul,
      exteriorSectionInclusion_restrict]
    exact congrArg _ (congrArg _ ((vertexTwistCast_restrict _ i _).trans
      (congrArg _ (vertexTwistSectionProduct_restrict R V _ _ i x y))))
  · rw [G.exteriorSummandProduct_of_not_disjoint R h, G.exteriorSummandProduct_of_not_disjoint R h, map_zero]

/-- The section exterior pairing commutes with restriction. -/
theorem exteriorSectionPairing_restrict (p q : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Γ(G.exteriorBundle R p, U)) (y : Γ(G.exteriorBundle R q, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R (p + q))).map i.op (G.exteriorSectionPairing R p q U x y) =
      G.exteriorSectionPairing R p q W ((Scheme.Modules.presheaf (G.exteriorBundle R p)).map i.op x)
        ((Scheme.Modules.presheaf (G.exteriorBundle R q)).map i.op y) := by
  rw [exteriorSectionPairing_apply, exteriorSectionPairing_apply, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [exteriorSummandProduct_restrict, exteriorSectionProjection_restrict, exteriorSectionProjection_restrict]

section Chart

variable (σ : V → Fin 2) (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)

/-- On a chart, the coordinate of an included summand section on its own summand is its chart
coefficient. -/
theorem exteriorChartCoordinates_inclusion_self (q : ℕ) (S : Set.powersetCard E q)
    (z : Γ(G.exteriorSummand R S, W)) :
    G.exteriorChartCoordinates R σ W hW q (G.exteriorSectionInclusion R q W S z) S =
      vertexTwistSheafChartCoefficient R V (fun v => -(G.deg S v : ℤ)) σ W hW z := by
  rw [exteriorChartCoordinates_apply]
  exact congrArg _ (vertexBiproductSectionsEquiv_ι_self
    (fun S : Set.powersetCard E q => G.exteriorSummand R S) W S z)

/-- On a chart, the coordinates of an included summand section on the other summands vanish. -/
theorem exteriorChartCoordinates_inclusion_ne (q : ℕ) {S U : Set.powersetCard E q} (h : S ≠ U)
    (z : Γ(G.exteriorSummand R S, W)) :
    G.exteriorChartCoordinates R σ W hW q (G.exteriorSectionInclusion R q W S z) U = 0 := by
  rw [exteriorChartCoordinates_apply]
  refine (congrArg _ (vertexBiproductSectionsEquiv_ι_ne
    (fun S : Set.powersetCard E q => G.exteriorSummand R S) W h z)).trans ?_
  exact map_zero _

/-- On a chart, the coordinates of exterior multiplication of two summands: the sorting sign times
the product of the chart coefficients on the union of disjoint edge subsets, zero otherwise. -/
theorem exteriorChartCoordinates_summandProduct {p q : ℕ} (S : Set.powersetCard E p)
    (T : Set.powersetCard E q) (x : Γ(G.exteriorSummand R S, W)) (y : Γ(G.exteriorSummand R T, W))
    (U : Set.powersetCard E (p + q)) :
    G.exteriorChartCoordinates R σ W hW (p + q) (G.exteriorSummandProduct R S T W x y) U =
      if h : Disjoint S.val T.val then
        (if disjUnion h = U then (permOfDisjoint h).sign •
          (vertexTwistSheafChartCoefficient R V (fun v => -(G.deg S v : ℤ)) σ W hW x *
            vertexTwistSheafChartCoefficient R V (fun v => -(G.deg T v : ℤ)) σ W hW y) else 0)
      else 0 := by
  by_cases h : Disjoint S.val T.val
  · rw [G.exteriorSummandProduct_of_disjoint R h, map_zsmul, Pi.smul_apply]
    simp only [h, ↓reduceDIte]
    split_ifs with hU
    · subst hU
      rw [exteriorChartCoordinates_inclusion_self, vertexTwistCast_chart, vertexTwistSectionProduct_chart,
        Koszul.shuffleSign_eq_permOfDisjoint_sign h, Units.smul_def, Int.cast_id]
    · rw [exteriorChartCoordinates_inclusion_ne _ _ _ _ _ _ hU, smul_zero]
  · rw [G.exteriorSummandProduct_of_not_disjoint R h, map_zero, Pi.zero_apply]
    simp only [h, ↓reduceDIte]

/-- On a chart, the coordinates of the section exterior pairing. -/
theorem exteriorChartCoordinates_pairing (p q : ℕ) (x : Γ(G.exteriorBundle R p, W))
    (y : Γ(G.exteriorBundle R q, W)) (U : Set.powersetCard E (p + q)) :
    G.exteriorChartCoordinates R σ W hW (p + q) (G.exteriorSectionPairing R p q W x y) U =
      ∑ S : Set.powersetCard E p, ∑ T : Set.powersetCard E q,
        if h : Disjoint S.val T.val then
          (if disjUnion h = U then (permOfDisjoint h).sign •
            (G.exteriorChartCoordinates R σ W hW p x S * G.exteriorChartCoordinates R σ W hW q y T) else 0)
        else 0 := by
  rw [exteriorSectionPairing_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun T _ => G.exteriorChartCoordinates_summandProduct R σ W hW S T _ _ U

end Chart

/-- On a chart, the section exterior pairing of two wedges of dual edge sections is the wedge of
the concatenated tuple. -/
theorem exteriorSectionPairing_wedge_of_le (p q : ℕ) (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) (x : Fin (p + 1) → Γ(G.edgeDualBundle R, W))
    (y : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionPairing R (p + 1) (q + 1) W
        (G.exteriorSectionWedge R p W (exteriorPower.ιMulti _ (p + 1) x))
        (G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) y)) =
      G.exteriorSectionWedge R (p + 1 + q) W (exteriorPower.ιMulti _ (p + 1 + q + 1)
        (Fin.append x y : Fin ((p + 1) + (q + 1)) → Γ(G.edgeDualBundle R, W))) := by
  apply (G.exteriorChartCoordinates R σ W hW ((p + 1) + (q + 1))).injective
  funext U
  rw [exteriorChartCoordinates_pairing]
  refine Eq.trans ?_ (G.exteriorChartCoordinates_wedge_ιMulti R σ W hW (p + 1 + q)
    (Fin.append x y : Fin ((p + 1) + (q + 1)) → Γ(G.edgeDualBundle R, W)) U).symm
  refine Eq.trans ?_ (Koszul.exteriorPower_basis_repr_ιMulti_append (G.edgeDualChartBasis R σ W hW) x y U).symm
  simp only [exteriorChartCoordinates_wedge_ιMulti]

/-- On every open, the section exterior pairing of two wedges of dual edge sections is the wedge of
the concatenated tuple: the section-level exterior wedge is multiplicative. -/
theorem exteriorSectionPairing_wedge (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin (p + 1) → Γ(G.edgeDualBundle R, W)) (y : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionPairing R (p + 1) (q + 1) W
        (G.exteriorSectionWedge R p W (exteriorPower.ιMulti _ (p + 1) x))
        (G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) y)) =
      G.exteriorSectionWedge R (p + 1 + q) W (exteriorPower.ιMulti _ (p + 1 + q + 1)
        (Fin.append x y : Fin ((p + 1) + (q + 1)) → Γ(G.edgeDualBundle R, W))) := by
  apply vertexSections_ext_of_charts (G.exteriorBundle R ((p + 1) + (q + 1))) W
  intro σ
  rw [exteriorSectionPairing_restrict, exteriorSectionWedge_restrict, exteriorSectionWedge_restrict,
    G.exteriorSectionPairing_wedge_of_le R p q σ _ inf_le_right]
  refine Eq.trans ?_ (G.exteriorSectionWedge_restrict R (p + 1 + q) _ _).symm
  congr 2
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

end Pairing

end BPFixedPoints.Multigraph
