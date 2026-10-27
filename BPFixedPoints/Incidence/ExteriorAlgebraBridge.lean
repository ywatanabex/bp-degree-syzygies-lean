import BPFixedPoints.Incidence.ExteriorProduct
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.GroupTheory.Perm.Fin

/-!
# The project exterior signs and Mathlib's exterior algebra

The project models exterior products on finite edge sets by the free module
`Koszul.Space E R = Finset E →₀ R`, ordering each finite set increasingly and
multiplying basis states by `Koszul.shuffleSign`. Mathlib orders the same
products through `Set.powersetCard.permOfDisjoint`, the permutation sorting the
concatenation of two increasing lists. The inversions of that permutation are
the pairs of a left element and a smaller right element, so its sign is the
shuffle sign.

Consequently, for any family `v : E → M`, the increasingly ordered exterior
products `orderedWedge R v S` multiply with the project's sign, and the basis
of `ExteriorAlgebra R (E →₀ R)` built from `Finsupp.basisSingleOne` identifies
`Koszul.Space E R` with that exterior algebra, carrying `Koszul.wedge` to
multiplication and `Koszul.insert e` to left multiplication by the generator `e`.
-/

namespace BPFixedPoints.Koszul

open Set Set.powersetCard

variable {E R : Type*} [LinearOrder E] [CommRing R]

/-! ### The sign of `permOfDisjoint` -/

/-- `permOfDisjoint` sends the position of an element of the concatenated list to the
position of the same element of `E` in the sorted union. -/
theorem orderIsoOfFin_permOfDisjoint {m n : ℕ} {s : powersetCard E m}
    {t : powersetCard E n} (h : Disjoint s.val t.val) (x : Fin m ⊕ Fin n) :
    (orderIsoOfFin (disjUnion h) (permOfDisjoint h (finSumFinEquiv x)) : E) =
      Sum.elim (fun a => (orderIsoOfFin s a : E)) (fun b => (orderIsoOfFin t b : E)) x := by
  have h1 : permOfDisjoint h (finSumFinEquiv x) = (orderIsoOfFin (disjUnion h)).symm
      (Equiv.Finset.disjUnionEquiv _ _ h (Sum.map (orderIsoOfFin s) (orderIsoOfFin t) x)) := by
    simp only [permOfDisjoint, Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  rw [h1]
  exact (congrArg Subtype.val ((orderIsoOfFin (disjUnion h)).apply_symm_apply _)).trans
    (by rcases x with a | a <;> rfl)

/-- `permOfDisjoint` compares two positions exactly as the elements of `E` occupying them
in the concatenated list. -/
theorem permOfDisjoint_lt_iff {m n : ℕ} {s : powersetCard E m} {t : powersetCard E n}
    (h : Disjoint s.val t.val) (x y : Fin m ⊕ Fin n) :
    permOfDisjoint h (finSumFinEquiv x) < permOfDisjoint h (finSumFinEquiv y) ↔
      Sum.elim (fun a => (orderIsoOfFin s a : E)) (fun b => (orderIsoOfFin t b : E)) x <
        Sum.elim (fun a => (orderIsoOfFin s a : E)) (fun b => (orderIsoOfFin t b : E)) y := by
  rw [← orderIsoOfFin_permOfDisjoint, ← orderIsoOfFin_permOfDisjoint, Subtype.coe_lt_coe,
    OrderIso.lt_iff_lt]

/-- A product over the increasing enumeration of a finite set is the product over the set. -/
theorem prod_orderIsoOfFin {M : Type*} [CommMonoid M] {m : ℕ} (s : powersetCard E m)
    (F : E → M) : ∏ a : Fin m, F (orderIsoOfFin s a : E) = ∏ x ∈ s.val, F x := by
  rw [← Finset.prod_coe_sort s.val F]
  exact Equiv.prod_comp (orderIsoOfFin s).toEquiv (fun x => F x)

/-- `Fin.castAdd` preserves and reflects the order. -/
private theorem castAdd_lt_castAdd_iff {m n : ℕ} {a b : Fin m} :
    Fin.castAdd n a < Fin.castAdd n b ↔ a < b := Iff.rfl

/-- Every left position precedes every right position. -/
private theorem castAdd_lt_natAdd {m n : ℕ} (a : Fin m) (b : Fin n) :
    Fin.castAdd n a < Fin.natAdd m b := by
  rw [Fin.lt_def]; simp; omega

/-- No right position precedes a left position. -/
private theorem not_natAdd_lt_castAdd {m n : ℕ} (a : Fin m) (b : Fin n) :
    ¬ Fin.natAdd m b < Fin.castAdd n a := by
  rw [Fin.lt_def]; simp; omega

/-- A comparison sign guarded by its own condition is trivial. -/
private theorem ite_ite_self_one (p : Prop) [Decidable p] :
    (if p then (if p then (1 : ℤˣ) else -1) else 1) = 1 := by
  split_ifs <;> rfl

/-- The sign of `permOfDisjoint` as a product over pairs of a right and a left element:
only pairs whose left element is larger contribute `-1`. -/
theorem permOfDisjoint_sign_eq_prod {m n : ℕ} {s : powersetCard E m} {t : powersetCard E n}
    (h : Disjoint s.val t.val) :
    (permOfDisjoint h).sign = ∏ y ∈ t.val, ∏ x ∈ s.val, if x < y then 1 else -1 := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  simp_rw [← Finset.filter_gt_eq_Iio, Finset.prod_filter]
  rw [← Equiv.prod_comp finSumFinEquiv]
  simp_rw [← Equiv.prod_comp finSumFinEquiv (fun i => if i < _ then _ else _)]
  simp_rw [permOfDisjoint_lt_iff]
  simp only [Fintype.prod_sum_type, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Sum.elim_inl, Sum.elim_inr, castAdd_lt_castAdd_iff, Fin.natAdd_lt_natAdd_iff,
    castAdd_lt_natAdd, not_natAdd_lt_castAdd, Subtype.coe_lt_coe, OrderIso.lt_iff_lt,
    ite_true, ite_false, ite_ite_self_one, Finset.prod_const_one, one_mul, mul_one]
  rw [← prod_orderIsoOfFin t]
  exact Finset.prod_congr rfl fun b _ =>
    prod_orderIsoOfFin s fun x => if x < (orderIsoOfFin t b : E) then 1 else -1

/-- For an element outside `T`, the product of the comparison signs against `T` is the
removal sign `(-1) ^ index T x`. -/
theorem prod_ite_lt_eq_neg_one_pow_index {M : Type*} [CommMonoid M] [HasDistribNeg M]
    (T : Finset E) {x : E} (hx : x ∉ T) :
    ∏ y ∈ T, (if x < y then (1 : M) else -1) = (-1) ^ index T x := by
  rw [Finset.prod_congr rfl (g := fun y => if y < x then (-1 : M) else 1)]
  · rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, index]
  · intro y hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    rcases lt_or_gt_of_ne hyx with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h]

/-- The sign of Mathlib's sorting permutation of two disjoint increasing lists is
`(-1)` to the project's shuffle index. -/
theorem permOfDisjoint_sign {m n : ℕ} {s : powersetCard E m} {t : powersetCard E n}
    (h : Disjoint s.val t.val) :
    (permOfDisjoint h).sign = (-1) ^ shuffleIndex s.val t.val := by
  rw [permOfDisjoint_sign_eq_prod, Finset.prod_comm, shuffleIndex,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun x hx =>
    prod_ite_lt_eq_neg_one_pow_index _ (Finset.disjoint_left.mp h hx)

/-- The project's shuffle sign is the sign of Mathlib's `permOfDisjoint`, cast to the
coefficient ring. -/
theorem shuffleSign_eq_permOfDisjoint_sign {m n : ℕ} {s : powersetCard E m}
    {t : powersetCard E n} (h : Disjoint s.val t.val) :
    shuffleSign (R := R) s.val t.val = (((permOfDisjoint h).sign : ℤ) : R) := by
  rw [permOfDisjoint_sign, shuffleSign]
  push_cast
  rfl

/-- Finite-set form of `shuffleSign_eq_permOfDisjoint_sign`, with each set regarded as an
element of `Set.powersetCard` of its own cardinality. -/
theorem shuffleSign_eq_permOfDisjoint_sign' {S T : Finset E} (h : Disjoint S T) :
    shuffleSign (R := R) S T =
      (((permOfDisjoint (s := ofCard (rfl : S.card = S.card))
        (t := ofCard (rfl : T.card = T.card)) h).sign : ℤ) : R) :=
  shuffleSign_eq_permOfDisjoint_sign (s := ofCard rfl) (t := ofCard rfl) h

/-! ### Ordered exterior products of a family -/

section OrderedWedge

variable (R) {M : Type*} [AddCommGroup M] [Module R M]

/-- The exterior product of `v e` over `e ∈ S`, taken in increasing order of `E`. -/
noncomputable def orderedWedge (v : E → M) (S : Finset E) : ExteriorAlgebra R M :=
  ExteriorAlgebra.ιMulti_family R S.card v (ofCard rfl)

variable {R}

/-- Mathlib's `ιMulti_family` at a set of prescribed cardinality is the ordered wedge of
that set. -/
theorem ιMulti_family_eq_orderedWedge (v : E → M) {n : ℕ} (s : powersetCard E n) :
    ExteriorAlgebra.ιMulti_family R n v s = orderedWedge R v s.val := by
  obtain ⟨S, hS⟩ := s
  have hn : S.card = n := mem_iff.mp hS
  subst hn
  rfl

/-- The ordered wedge over the empty set is `1`. -/
@[simp] theorem orderedWedge_empty (v : E → M) : orderedWedge R v ∅ = 1 :=
  ExteriorAlgebra.ιMulti_zero_apply _

/-- The ordered wedge over a singleton is the generator `ι R (v e)`. -/
@[simp] theorem orderedWedge_singleton (v : E → M) (e : E) :
    orderedWedge R v {e} = ExteriorAlgebra.ι R (v e) := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Finset.card_singleton, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, Function.comp_apply]
  exact congrArg _ (congrArg v (Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)))

/-- The ordered wedge over `S` lies in the exterior power of degree `S.card`. -/
theorem orderedWedge_mem_exteriorPower (v : E → M) (S : Finset E) :
    orderedWedge R v S ∈ ⋀[R]^S.card M :=
  ExteriorAlgebra.ιMulti_range R S.card (Set.mem_range_self _)

/-- Ordered wedges over overlapping sets multiply to zero. -/
theorem orderedWedge_mul_of_not_disjoint (v : E → M) {S T : Finset E} (h : ¬Disjoint S T) :
    orderedWedge R v S * orderedWedge R v T = 0 :=
  ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint R v (ofCard rfl) (ofCard rfl) h

/-- Ordered wedges over disjoint sets multiply to the shuffle sign times the ordered wedge
over the union. -/
theorem orderedWedge_mul_of_disjoint (v : E → M) {S T : Finset E} (h : Disjoint S T) :
    orderedWedge R v S * orderedWedge R v T =
      shuffleSign (R := R) S T • orderedWedge R v (S ∪ T) := by
  have := ExteriorAlgebra.ιMulti_family_mul_of_disjoint R v
    (ofCard (rfl : S.card = S.card)) (ofCard (rfl : T.card = T.card)) h
  have hU : ((disjUnion (s := ofCard (rfl : S.card = S.card))
      (t := ofCard (rfl : T.card = T.card)) h : powersetCard E (S.card + T.card)) :
        Finset E) = S ∪ T :=
    Finset.disjUnion_eq_union S T h
  refine (this : orderedWedge R v S * orderedWedge R v T = _).trans ?_
  rw [ιMulti_family_eq_orderedWedge, hU, Units.smul_def, ← Int.cast_smul_eq_zsmul R,
    shuffleSign_eq_permOfDisjoint_sign' h]

/-- Product of ordered wedges in both cases, matching `Koszul.wedgeSingle`. -/
theorem orderedWedge_mul (v : E → M) (S T : Finset E) :
    orderedWedge R v S * orderedWedge R v T =
      if Disjoint S T then shuffleSign (R := R) S T • orderedWedge R v (S ∪ T) else 0 := by
  split_ifs with h
  · exact orderedWedge_mul_of_disjoint v h
  · exact orderedWedge_mul_of_not_disjoint v h

/-- Ordered wedges are natural for linear maps of the underlying module. -/
theorem map_orderedWedge {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (v : E → M) (S : Finset E) :
    ExteriorAlgebra.map f (orderedWedge R v S) = orderedWedge R (f ∘ v) S := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.map_apply_ιMulti]
  rfl

/-- The ordered wedge only depends on the values of the family on the set. -/
theorem orderedWedge_congr {v w : E → M} {S : Finset E} (h : ∀ e ∈ S, v e = w e) :
    orderedWedge R v S = orderedWedge R w S := by
  simp only [orderedWedge, ExteriorAlgebra.ιMulti_family]
  congr 1
  funext i
  exact h _ (Finset.orderEmbOfFin_mem S rfl i)

end OrderedWedge

/-! ### The exterior algebra of the free module on the edges -/

section Standard

variable (E R)

/-- The standard basis of `ExteriorAlgebra R (E →₀ R)`, indexed by finite edge sets. -/
noncomputable abbrev exteriorBasis : Module.Basis (Finset E) R (ExteriorAlgebra R (E →₀ R)) :=
  (Finsupp.basisSingleOne : Module.Basis E R (E →₀ R)).ExteriorAlgebra

/-- The project's exterior state module is the exterior algebra of the free module on the
edges: the finite set `S` corresponds to the increasing wedge of the generators in `S`. -/
noncomputable def exteriorAlgebraEquiv : Space E R ≃ₗ[R] ExteriorAlgebra R (E →₀ R) :=
  (exteriorBasis E R).repr.symm

variable {E R}

/-- The standard basis vector of `S` is the ordered wedge of the generators `single e 1`. -/
theorem exteriorBasis_apply (S : Finset E) :
    exteriorBasis E R S = orderedWedge R (fun e => Finsupp.single e (1 : R)) S := by
  rw [ExteriorAlgebra.basis_apply]
  simp only [prodEquiv_symm_apply, Finsupp.coe_basisSingleOne]
  rfl

/-- A basis state is sent to the corresponding multiple of the standard basis vector. -/
@[simp] theorem exteriorAlgebraEquiv_single (S : Finset E) (r : R) :
    exteriorAlgebraEquiv E R (Finsupp.single S r) = r • exteriorBasis E R S := by
  simp [exteriorAlgebraEquiv]

/-- The inverse isomorphism sends a standard basis vector to its basis state. -/
@[simp] theorem exteriorAlgebraEquiv_symm_exteriorBasis (S : Finset E) :
    (exteriorAlgebraEquiv E R).symm (exteriorBasis E R S) = Finsupp.single S 1 := by
  simp [exteriorAlgebraEquiv]

/-- A basis state is sent to the ordered wedge of the generators. -/
theorem exteriorAlgebraEquiv_single_one (S : Finset E) :
    exteriorAlgebraEquiv E R (Finsupp.single S 1) =
      orderedWedge R (fun e => Finsupp.single e (1 : R)) S := by
  rw [exteriorAlgebraEquiv_single, one_smul, exteriorBasis_apply]

/-- The empty state is the unit of the exterior algebra. -/
theorem exteriorAlgebraEquiv_single_empty (r : R) :
    exteriorAlgebraEquiv E R (Finsupp.single ∅ r) = algebraMap R _ r := by
  rw [exteriorAlgebraEquiv_single, exteriorBasis_apply, orderedWedge_empty,
    Algebra.algebraMap_eq_smul_one]

/-- A one-edge state is the generator of that edge. -/
theorem exteriorAlgebraEquiv_single_singleton (e : E) (r : R) :
    exteriorAlgebraEquiv E R (Finsupp.single {e} r) =
      ExteriorAlgebra.ι R (Finsupp.single e r) := by
  rw [exteriorAlgebraEquiv_single, exteriorBasis_apply, orderedWedge_singleton, ← map_smul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A state supported on `S` lies in the exterior power of degree `S.card`. -/
theorem exteriorAlgebraEquiv_single_mem (S : Finset E) (r : R) :
    exteriorAlgebraEquiv E R (Finsupp.single S r) ∈ ⋀[R]^S.card (E →₀ R) := by
  rw [exteriorAlgebraEquiv_single, exteriorBasis_apply]
  exact Submodule.smul_mem _ _ (orderedWedge_mem_exteriorPower _ _)

/-- The standard basis vectors multiply with the project's shuffle sign. -/
theorem exteriorBasis_mul (S T : Finset E) :
    exteriorBasis E R S * exteriorBasis E R T =
      if Disjoint S T then shuffleSign (R := R) S T • exteriorBasis E R (S ∪ T) else 0 := by
  simp only [exteriorBasis_apply]
  exact orderedWedge_mul _ S T

/-- `Koszul.wedgeSingle` corresponds to multiplication of basis states. -/
theorem exteriorAlgebraEquiv_wedgeSingle (S T : Finset E) (r : R) :
    exteriorAlgebraEquiv E R (wedgeSingle (R := R) S T r) =
      r • (exteriorBasis E R S * exteriorBasis E R T) := by
  rw [wedgeSingle_apply, exteriorBasis_mul]
  split_ifs
  · rw [exteriorAlgebraEquiv_single, smul_eq_mul, mul_comm, mul_smul]
  · simp

/-- The isomorphism carries the project's exterior product `Koszul.wedge` to
multiplication in Mathlib's exterior algebra. -/
theorem exteriorAlgebraEquiv_wedge (x y : Space E R) :
    exteriorAlgebraEquiv E R (wedge x y) =
      exteriorAlgebraEquiv E R x * exteriorAlgebraEquiv E R y := by
  let L : Space E R →ₗ[R] Space E R →ₗ[R] ExteriorAlgebra R (E →₀ R) :=
    wedge.compr₂ (exteriorAlgebraEquiv E R).toLinearMap
  let L' : Space E R →ₗ[R] Space E R →ₗ[R] ExteriorAlgebra R (E →₀ R) :=
    (LinearMap.mul R (ExteriorAlgebra R (E →₀ R))).compl₁₂
      (exteriorAlgebraEquiv E R).toLinearMap (exteriorAlgebraEquiv E R).toLinearMap
  have hL : L = L' := by
    refine Finsupp.lhom_ext fun S r => Finsupp.lhom_ext fun T s => ?_
    simp only [L, L', LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      LinearMap.mul_apply', wedge_single, exteriorAlgebraEquiv_wedgeSingle,
      exteriorAlgebraEquiv_single]
    rw [smul_mul_smul_comm]
  exact LinearMap.congr_fun₂ hL x y

/-- The inverse isomorphism carries multiplication to the project's exterior product. -/
theorem exteriorAlgebraEquiv_symm_mul (x y : ExteriorAlgebra R (E →₀ R)) :
    (exteriorAlgebraEquiv E R).symm (x * y) =
      wedge ((exteriorAlgebraEquiv E R).symm x) ((exteriorAlgebraEquiv E R).symm y) := by
  apply (exteriorAlgebraEquiv E R).injective
  rw [exteriorAlgebraEquiv_wedge, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- Left exterior multiplication by an edge in the project's model is left multiplication
by the generator of that edge. -/
theorem insert_eq_wedge (e : E) (x : Space E R) :
    insert e x = wedge (Finsupp.single {e} 1) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single S a =>
    rw [insert_single, wedge_single, wedgeSingle_apply, one_mul]
    by_cases he : e ∈ S
    · simp [he]
    · have hd : Disjoint {e} S := Finset.disjoint_singleton_left.mpr he
      have hsign : shuffleSign (R := R) {e} S = sign S e := by
        simp [shuffleSign, shuffleIndex, sign]
      simp only [he, hd, ↓reduceIte, Finset.singleton_union, smul_eq_mul, hsign]

/-- The isomorphism carries `Koszul.insert e` to left multiplication by `ι R (single e 1)`. -/
theorem exteriorAlgebraEquiv_insert (e : E) (x : Space E R) :
    exteriorAlgebraEquiv E R (insert e x) =
      ExteriorAlgebra.ι R (Finsupp.single e 1) * exteriorAlgebraEquiv E R x := by
  rw [insert_eq_wedge, exteriorAlgebraEquiv_wedge, exteriorAlgebraEquiv_single_singleton]

end Standard

/-! ### Fixed exterior degree -/

section FixedDegree

variable (E R)

/-- The exterior power of degree `n` of the free module on the edges, with the basis of
increasing wedges indexed by edge sets of cardinality `n`. -/
noncomputable def exteriorPowerEquiv (n : ℕ) :
    (powersetCard E n →₀ R) ≃ₗ[R] ⋀[R]^n (E →₀ R) :=
  ((Finsupp.basisSingleOne : Module.Basis E R (E →₀ R)).exteriorPower n).repr.symm

variable {E R}

/-- In the exterior algebra, the degree-`n` basis state of `s` is the standard basis state
of the underlying finite set. -/
theorem exteriorPowerEquiv_single (n : ℕ) (s : powersetCard E n) (r : R) :
    (exteriorPowerEquiv E R n (Finsupp.single s r) : ExteriorAlgebra R (E →₀ R)) =
      exteriorAlgebraEquiv E R (Finsupp.single s.val r) := by
  rw [exteriorPowerEquiv, Module.Basis.repr_symm_single, Submodule.coe_smul,
    exteriorAlgebraEquiv_single, ExteriorAlgebra.basis_eq_coe_basis]

end FixedDegree

end BPFixedPoints.Koszul
