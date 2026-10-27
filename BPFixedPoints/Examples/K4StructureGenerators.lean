import BPFixedPoints.Incidence.IncidenceCycleAlgebraQuotient
import BPFixedPoints.Incidence.IncidenceGeneratorCount
import BPFixedPoints.Examples.PaperTables

/-! # Module generators and their products for K₄ (`alg:k4-section`)

The paper states that the `8 = 2^3` module generators of `𝒰_{K₄}` are the unit, the four
triangle classes and the three four-cycle classes, and that every product of two nonunit classes
vanishes in `𝒰_{K₄}/S_+𝒰_{K₄}`, since any two cycles of K₄ meet at a vertex. Here
`𝒰_G/S_+𝒰_G` is `IncidenceAugmentationQuotient`, identified with the cycle-compatibility algebra
`ℂ[z_C]/(z_C z_D : V(C) ∩ V(D) ≠ ∅)` by `incidenceQuotientEquivCycleAlgebra`.

Proved here, for every graph:
* the degree-zero Tor class of the empty edge set is the unit (`cycleUnionClass_empty`);
* the minimal module generator of `𝒰_G` attached to a degree-zero resolution state (a cycle
  union `S`, `incidenceResolutionGenerators`) has class the cycle class of `S` in degree-zero Tor
  (`incidenceRingToTor_incidenceResolutionGenerators`); in `ℂ[z_C]/(z_C z_D)` it is the unit if
  `S = ∅` and `z_S` if `S` is a simple cycle
  (`incidenceQuotientEquivCycleAlgebra_generator_empty`,
  `incidenceQuotientEquivCycleAlgebra_generator_cycle`).

Proved for K₄ (`Examples.K4`):
* its simple cycles are exactly the nonempty cycle unions, four triangles and three squares
  (`K4_isSimpleCycle_iff`, `K4_simpleCycle_counts`), and any two of them share a vertex
  (`K4_simpleCycle_meet`);
* `ℂ[z_C]/(z_C z_D)` has the basis `1, z_C` indexed by `Option K4.SimpleCycle`, of size
  8 (`K4CycleAlgebraBasis`), every product `z_C z_D` vanishes (`K4_cycleAlgebra_X_mul_X`), and so
  does every product of two elements of the span of the `z_C` (`K4_cycleAlgebra_mul_eq_zero`);
* the same in `𝒰_{K₄}/S_+𝒰_{K₄}` (`K4QuotientBasis`, `K4_quotient_cycle_mul`);
* each of the 8 minimal module generators of `𝒰_{K₄}` is homogeneous and has class the unit
  (one generator, of degree 0) or the class `z_C` of a triangle (four generators, degree 3) or of
  a square (three generators, degree 4) (`K4_module_generator_class`,
  `K4_module_generator_counts`), and the product of the classes of two nonunit generators
  vanishes in `𝒰_{K₄}/S_+𝒰_{K₄}` (`K4_generator_mul_eq_zero`).

The minimality of the generating family is the general `incidenceResolutionGenerators_minimal`
and `incidenceModuleGeneratorNumber_eq`. Not covered: the classes of generators are identified
exactly (no sign or scalar ambiguity) only in `ℂ[z_C]/(z_C z_D)` and `𝒰_{K₄}/S_+𝒰_{K₄}`; nothing
is said about products in `𝒰_{K₄}` itself, where they need not vanish.
-/

set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp MvPolynomial CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The empty edge set is a cycle union. -/
theorem isCycleUnion_empty : G.IsCycleUnion ∅ := fun v => Or.inl (G.deg_empty v)

/-- The degree-zero Tor class of the empty edge set is the unit of degree-zero Tor. -/
theorem cycleUnionClass_empty : G.cycleUnionClass ∅ = 1 := by
  apply G.incidenceTorFullState_injective 0
  rw [G.incidenceTorFullState_cycleUnionClass G.isCycleUnion_empty, incidenceTorZero_one_def,
    incidenceTorFullState_one,
    G.incStateUnit_eq_single ℂ (zeroTwoStateIndex (G.deg ∅) G.isCycleUnion_empty)]
  rfl

/-- Origin specialization of a basis vector of the zeroth free term is the class of its cycle
union. -/
theorem incFreeTermToTor_basis_zero
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) :
    G.incFreeTermToTor 0 (G.incFreeTermBasis 0 b) = G.cycleUnionClass b.val.1 := by
  have h : freeAtOrigin ((G.incFreeTermBasis 0).repr (G.incFreeTermBasis 0 b)) =
      single b (1 : ℂ) := by
    rw [Module.Basis.repr_self]
    ext i
    rw [freeAtOrigin_apply, single_apply, single_apply]
    split_ifs <;> simp
  change (G.incidenceTorEquivState 0).symm
    (freeAtOrigin ((G.incFreeTermBasis 0).repr (G.incFreeTermBasis 0 b))) = _
  rw [h, incidenceTorEquivState_symm_single, one_smul]

/-- The minimal module generator of the incidence ring attached to a degree-zero resolution
state has, in degree-zero Tor, the class of its cycle union. -/
theorem incidenceRingToTor_incidenceResolutionGenerators
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) :
    G.incidenceRingToTor (G.incidenceResolutionGenerators b) = G.cycleUnionClass b.val.1 := by
  rw [incidenceResolutionGenerators, incidenceRingToTor_augmentation, incFreeTermToTor_basis_zero]

/-- In `ℂ[z_C]/(z_C z_D)`, the class of a minimal module generator is the preimage of the class
of its cycle union in degree-zero Tor. -/
theorem incidenceQuotientEquivCycleAlgebra_generator
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) :
    G.incidenceQuotientEquivCycleAlgebra
        (Ideal.Quotient.mk G.incidenceAugmentationIdeal (G.incidenceResolutionGenerators b)) =
      G.cycleAlgebraEquivTor.symm (G.cycleUnionClass b.val.1) := by
  change G.cycleAlgebraEquivTor.symm (G.incidenceQuotientEquivTor _) = _
  rw [incidenceQuotientEquivTor_mk, incidenceRingToTor_incidenceResolutionGenerators]

/-- The minimal module generator of the empty state is the unit of `ℂ[z_C]/(z_C z_D)`. -/
theorem incidenceQuotientEquivCycleAlgebra_generator_empty
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) (hb : b.val.1 = ∅) :
    G.incidenceQuotientEquivCycleAlgebra
        (Ideal.Quotient.mk G.incidenceAugmentationIdeal (G.incidenceResolutionGenerators b)) =
      1 := by
  rw [incidenceQuotientEquivCycleAlgebra_generator, hb, cycleUnionClass_empty, map_one]

/-- The minimal module generator of the state of a simple cycle `C` is `z_C` in
`ℂ[z_C]/(z_C z_D)`. -/
theorem incidenceQuotientEquivCycleAlgebra_generator_cycle
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = 0}) (C : G.SimpleCycle)
    (hb : b.val.1 = C.val) :
    G.incidenceQuotientEquivCycleAlgebra
        (Ideal.Quotient.mk G.incidenceAugmentationIdeal (G.incidenceResolutionGenerators b)) =
      Ideal.Quotient.mk G.cycleCompatibilityIdeal (X C) := by
  rw [incidenceQuotientEquivCycleAlgebra_generator, hb, AlgEquiv.symm_apply_eq,
    cycleAlgebraEquivTor_X, cycleClass]

end BPFixedPoints.Multigraph

namespace BPFixedPoints.Examples

open Multigraph MvPolynomial

/-! ## Simple cycles of K₄ -/

/-- The simple cycles of K₄ are exactly its nonempty cycle unions: the four triangles and the
three squares. -/
theorem K4_isSimpleCycle_iff (C : Finset (Fin 6)) :
    K4.IsSimpleCycle C ↔ K4.IsCycleUnion C ∧ C.Nonempty := by
  revert C; decide

/-- K₄ has seven simple cycles: four triangles (three edges) and three squares (four edges). -/
theorem K4_simpleCycle_counts :
    (Finset.univ.filter fun C : Finset (Fin 6) => K4.IsSimpleCycle C ∧ C.card = 3).card = 4 ∧
      (Finset.univ.filter fun C : Finset (Fin 6) => K4.IsSimpleCycle C ∧ C.card = 4).card = 3 ∧
      (∀ C : Finset (Fin 6), K4.IsSimpleCycle C → C.card = 3 ∨ C.card = 4) ∧
      Fintype.card K4.SimpleCycle = 7 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [Fintype.card_subtype]
  decide

/-- Any two simple cycles of K₄ share a vertex (including a cycle with itself). -/
theorem K4_simpleCycle_meet (C D : K4.SimpleCycle) :
    ¬ Disjoint (K4.support C.val) (K4.support D.val) :=
  K4_cycleUnions_meet.2 C.val D.val C.property.isCycleUnion D.property.isCycleUnion
    C.property.1 D.property.1

/-! ## The cycle-compatibility algebra of K₄ -/

/-- The generator `z_C` of the cycle-compatibility algebra of K₄. -/
noncomputable abbrev K4z (C : K4.SimpleCycle) : K4.CycleAlgebra :=
  Ideal.Quotient.mk K4.cycleCompatibilityIdeal (X C)

/-- **Products of generators of K₄ vanish.** `z_C z_D = 0` for all simple cycles `C, D` of K₄
(including `z_C² = 0`), since any two cycles of K₄ share a vertex. -/
theorem K4_cycleAlgebra_X_mul_X (C D : K4.SimpleCycle) : K4z C * K4z D = 0 :=
  K4.cycleAlgebra_X_mul_X_eq_zero (K4_simpleCycle_meet C D)

/-- The family `1, z_C` of the cycle-compatibility algebra of K₄, indexed by
`Option K4.SimpleCycle`. -/
noncomputable def K4CycleAlgebraFamily : Option K4.SimpleCycle → K4.CycleAlgebra
  | none => 1
  | some C => K4z C

/-- The span of `1, z_C` is closed under multiplication by every `z_D`. -/
theorem K4_span_mul_X {w : K4.CycleAlgebra}
    (hw : w ∈ Submodule.span ℂ (Set.range K4CycleAlgebraFamily)) (D : K4.SimpleCycle) :
    w * K4z D ∈ Submodule.span ℂ (Set.range K4CycleAlgebraFamily) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    cases i with
    | none => exact Submodule.subset_span ⟨some D, (one_mul _).symm⟩
    | some C =>
      change K4z C * K4z D ∈ _
      rw [K4_cycleAlgebra_X_mul_X]
      exact Submodule.zero_mem _
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

/-- The family `1, z_C` spans the cycle-compatibility algebra of K₄. -/
theorem K4_span_cycleAlgebraFamily :
    Submodule.span ℂ (Set.range K4CycleAlgebraFamily) = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on with
  | C c =>
    have h : Ideal.Quotient.mk K4.cycleCompatibilityIdeal (C c) = c • (1 : K4.CycleAlgebra) := by
      change Ideal.Quotient.mk K4.cycleCompatibilityIdeal
        (algebraMap ℂ (MvPolynomial K4.SimpleCycle ℂ) c) = _
      rw [Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_eq_smul_one]
    rw [h]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨none, rfl⟩)
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | mul_X p D hp => rw [map_mul]; exact K4_span_mul_X hp D

/-- **The basis `1, z_C` of the cycle-compatibility algebra of K₄.** It has `8 = 1 + 4 + 3`
elements: the unit, the four triangle generators and the three square generators. -/
noncomputable def K4CycleAlgebraBasis : Module.Basis (Option K4.SimpleCycle) ℂ K4.CycleAlgebra :=
  basisOfTopLeSpanOfCardEqFinrank K4CycleAlgebraFamily K4_span_cycleAlgebraFamily.ge (by
    rw [Fintype.card_option, K4_simpleCycle_counts.2.2.2, K4.finrank_cycleAlgebra,
      K4_cycleUnions])

@[simp] theorem K4CycleAlgebraBasis_none : K4CycleAlgebraBasis none = 1 := by
  simp [K4CycleAlgebraBasis, K4CycleAlgebraFamily]

@[simp] theorem K4CycleAlgebraBasis_some (C : K4.SimpleCycle) :
    K4CycleAlgebraBasis (some C) = K4z C := by
  simp [K4CycleAlgebraBasis, K4CycleAlgebraFamily]

/-- The cycle-compatibility algebra of K₄ has dimension 8. -/
theorem K4_finrank_cycleAlgebra : Module.finrank ℂ K4.CycleAlgebra = 8 := by
  rw [K4.finrank_cycleAlgebra, K4_cycleUnions]

/-- **Products of nonunit elements vanish.** In the cycle-compatibility algebra of K₄, the
product of any two elements of the span of the generators `z_C` is zero. -/
theorem K4_cycleAlgebra_mul_eq_zero {a b : K4.CycleAlgebra}
    (ha : a ∈ Submodule.span ℂ (Set.range K4z)) (hb : b ∈ Submodule.span ℂ (Set.range K4z)) :
    a * b = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨D, rfl⟩ := hy
      exact K4_cycleAlgebra_X_mul_X C D
    | zero => rw [mul_zero]
    | add y y' _ _ hy hy' => rw [mul_add, hy, hy', add_zero]
    | smul c y _ hy => rw [mul_smul_comm, hy, smul_zero]
  | zero => rw [zero_mul]
  | add x x' _ _ hx hx' => rw [add_mul, hx, hx', add_zero]
  | smul c x _ hx => rw [smul_mul_assoc, hx, smul_zero]

/-! ## `𝒰_{K₄}/S_+𝒰_{K₄}` -/

/-- The class in `𝒰_{K₄}/S_+𝒰_{K₄}` corresponding to the generator `z_C`. -/
noncomputable abbrev K4QuotientCycleClass (C : K4.SimpleCycle) : K4.IncidenceAugmentationQuotient :=
  K4.incidenceQuotientEquivCycleAlgebra.symm (K4z C)

/-- **The basis of `𝒰_{K₄}/S_+𝒰_{K₄}`**: the unit and the seven cycle classes, four triangles
and three squares, transported from `K4CycleAlgebraBasis` along `alg:cycle-algebra`. -/
noncomputable def K4QuotientBasis :
    Module.Basis (Option K4.SimpleCycle) ℂ K4.IncidenceAugmentationQuotient :=
  K4CycleAlgebraBasis.map K4.incidenceQuotientEquivCycleAlgebra.symm.toLinearEquiv

@[simp] theorem K4QuotientBasis_none : K4QuotientBasis none = 1 := by
  simp [K4QuotientBasis]

@[simp] theorem K4QuotientBasis_some (C : K4.SimpleCycle) :
    K4QuotientBasis (some C) = K4QuotientCycleClass C := by
  simp [K4QuotientBasis]

/-- **Products of two nonunit classes vanish in `𝒰_{K₄}/S_+𝒰_{K₄}`.** -/
theorem K4_quotient_cycle_mul (C D : K4.SimpleCycle) :
    K4QuotientCycleClass C * K4QuotientCycleClass D = 0 := by
  rw [← map_mul, K4_cycleAlgebra_X_mul_X, map_zero]

/-! ## The minimal module generators of `𝒰_{K₄}` -/

/-- **The module generators of `𝒰_{K₄}` (`alg:k4-section`).** Each of the minimal module
generators `incidenceResolutionGenerators b` of the incidence ring of K₄ (one for each
degree-zero resolution state `b`, a cycle union) is homogeneous of natural degree `|S|`, where
`S` is the edge set of `b`, and its class in `𝒰_{K₄}/S_+𝒰_{K₄} ≅ ℂ[z_C]/(z_C z_D)` is either
the unit (`S = ∅`) or the generator `z_C` of a simple cycle `C = S`, a triangle (`|C| = 3`) or a
square (`|C| = 4`). -/
theorem K4_module_generator_class
    (b : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0}) :
    K4.incidenceResolutionGenerators b ∈ K4.incidenceCoefficientPiece b.val.1.card ∧
      ((b.val.1 = ∅ ∧ K4.incidenceQuotientEquivCycleAlgebra
          (Ideal.Quotient.mk K4.incidenceAugmentationIdeal (K4.incidenceResolutionGenerators b)) =
            1) ∨
        ∃ C : K4.SimpleCycle, b.val.1 = C.val ∧ (C.val.card = 3 ∨ C.val.card = 4) ∧
          K4.incidenceQuotientEquivCycleAlgebra
            (Ideal.Quotient.mk K4.incidenceAugmentationIdeal (K4.incidenceResolutionGenerators b)) =
              K4z C) := by
  refine ⟨K4.incidenceResolutionGenerators_homogeneous b, ?_⟩
  have hS := K4.isCycleUnion_of_incResolutionDegree_eq_zero b.val b.property
  rcases b.val.1.eq_empty_or_nonempty with h | h
  · exact Or.inl ⟨h, K4.incidenceQuotientEquivCycleAlgebra_generator_empty b h⟩
  · have hC : K4.IsSimpleCycle b.val.1 := (K4_isSimpleCycle_iff _).2 ⟨hS, h⟩
    exact Or.inr ⟨⟨b.val.1, hC⟩, rfl, K4_simpleCycle_counts.2.2.1 _ hC,
      K4.incidenceQuotientEquivCycleAlgebra_generator_cycle b ⟨b.val.1, hC⟩ rfl⟩

/-- **The `8 = 2^3` module generators of `𝒰_{K₄}`.** The minimal number of generators of the
incidence ring of K₄ as a module over its coefficient ring is 8; the minimal generating family
`incidenceResolutionGenerators` has 8 members, of which one has natural degree 0 (the unit
class), four have degree 3 (the triangle classes) and three have degree 4 (the square classes),
and none has any other degree. -/
theorem K4_module_generator_counts :
    K4.incidenceModuleGeneratorNumber = 8 ∧
      Fintype.card {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0} = 8 ∧
      Fintype.card {b : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0} //
        K4.incResolutionInternalDegree b.val = 0} = 1 ∧
      Fintype.card {b : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0} //
        K4.incResolutionInternalDegree b.val = 3} = 4 ∧
      Fintype.card {b : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0} //
        K4.incResolutionInternalDegree b.val = 4} = 3 ∧
      ∀ q, q ≠ 0 → q ≠ 3 → q ≠ 4 →
        Fintype.card {b : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0} //
          K4.incResolutionInternalDegree b.val = q} = 0 := by
  have h8 : ∑ q ∈ Finset.range (Fintype.card (Fin 6) + 1), K4.betti 0 q = 8 :=
    congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) table_K4
  refine ⟨K4.incidenceModuleGeneratorNumber_eq.trans h8,
    (K4.card_incHomologicalBasis 0).trans h8, ?_, ?_, ?_, fun q h0 h3 h4 => ?_⟩
  · rw [K4.card_incidenceResolutionGenerators_degree]; decide
  · rw [K4.card_incidenceResolutionGenerators_degree]; decide
  · rw [K4.card_incidenceResolutionGenerators_degree]; decide
  · rw [K4.card_incidenceResolutionGenerators_degree]
    refine Finset.sum_eq_zero fun S hS => ?_
    rw [Finset.mem_filter] at hS
    obtain ⟨-, hcard, hsupp⟩ := hS
    by_contra hw
    have hcu : K4.IsCycleUnion S :=
      K4.deg_eq_two_of_card_le hw (by omega)
    rcases S.eq_empty_or_nonempty with he | hne
    · subst he; simp at hcard; omega
    · have := K4_simpleCycle_counts.2.2.1 S ((K4_isSimpleCycle_iff S).2 ⟨hcu, hne⟩)
      omega

/-- **Products of two nonunit generator classes vanish (`alg:k4-section`).** For two minimal
module generators of `𝒰_{K₄}` other than the unit class (nonempty edge sets), the product of
their classes in `𝒰_{K₄}/S_+𝒰_{K₄}` is zero, since any two cycles of K₄ meet at a vertex. -/
theorem K4_generator_mul_eq_zero
    (b b' : {b : K4.IncResolutionBasis // K4.incResolutionDegree b = 0})
    (hb : b.val.1.Nonempty) (hb' : b'.val.1.Nonempty) :
    Ideal.Quotient.mk K4.incidenceAugmentationIdeal (K4.incidenceResolutionGenerators b) *
      Ideal.Quotient.mk K4.incidenceAugmentationIdeal (K4.incidenceResolutionGenerators b') =
        0 := by
  apply K4.incidenceQuotientEquivCycleAlgebra.injective
  rw [map_mul, map_zero]
  rcases (K4_module_generator_class b).2 with ⟨h, -⟩ | ⟨C, -, -, hC⟩
  · exact absurd h hb.ne_empty
  rcases (K4_module_generator_class b').2 with ⟨h, -⟩ | ⟨D, -, -, hD⟩
  · exact absurd h hb'.ne_empty
  rw [hC, hD, K4_cycleAlgebra_X_mul_X]

end BPFixedPoints.Examples
