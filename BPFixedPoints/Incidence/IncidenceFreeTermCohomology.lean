import BPFixedPoints.Incidence.IncidenceZeroBaseChangeNormalization
import Mathlib.RingTheory.TensorProduct.Free

/-! # The free terms of the incidence resolution are exterior cohomology over `S_G`

The paper's equation `alg:free-terms` (Theorem 3.4) says that the minimal graded free resolution
of `𝒰_G` has terms `F_p = ⊕_q H^{q-p}(X_G, ∧^q F_G^∨) ⊗ S_G(-q)`. This file proves it for the
actual free resolution `IncFreeTerm p` of `ResolutionTor.lean`.

**Target.** The finite product over `p ≤ q ≤ |E|` (the index type `IncFreeTermDegree p`) of
`S_G ⊗_ℂ H^{q-p}(X_G, ∧^q F_G^∨)`, with the Ext-defined sheaf cohomology of the abelian exterior
bundle over `ℂ` and its geometric `ℂ`-action. Internal degrees `q < p` carry no generator (a
generator of a `q`-element edge set has homological degree at most `q`); they are left out because
`q - p` is truncated subtraction in `ℕ`. The product type is written out in the statement of
`incFreeTermCohomologyEquiv` rather than abbreviated: an abbreviation made the kernel check of every
statement about it several times slower.

**The isomorphism** (`incFreeTermCohomologyEquiv`). The `ℂ`-basis of `H^{q-p}(X_G, ∧^q F_G^∨)` used
here (`incExteriorStateBasis`) is the image, under the base-change isomorphism `zbcExteriorEquiv`
(built without state bases), of the Tor classes of the free generators of internal degree `q`; its
vectors are the exterior classes of the same states (`incExteriorStateBasis_apply`, from
`zbcExteriorEquiv_stateClass`). The isomorphism sends the free generator `e_b` to `1 ⊗` that vector
in the summand of the internal degree of `b`.

**Results.**
* *Generators* (`incFreeTermCohomologyEquiv_stateGenerator`): the generator of the state `(S, κ)`,
  with `|S| = q`, goes to `Pi.single q (1 ⊗ exteriorStateClass S κ)`.
* *Internal grading* (`incFreeTermCohomologyEquiv_mem_internal_iff`): an element of `F_p` has
  internal degree `n` (coefficients of `e_b` homogeneous of degree `n - |b|`) iff, for every `q`,
  the `q`-summand of its image lies in `(S_G)_{n-q} ⊗_ℂ H^{q-p}`. This is the grading of
  `S_G(-q) ⊗ H^{q-p}`, so the isomorphism is one of graded `S_G`-modules.
* *Acceptance test on generators* (`incFreeTermCohomologyEquiv_canonical`): if `y ∈ Tor_p`
  corresponds to `1 ⊗ e_b` under `incidenceTorIsoFreeTerm`, then `y` lies in internal degree `q`,
  `zbcExteriorEquiv` sends it to the exterior class of the same state and index, and the image of
  `e_b` is `1 ⊗ zbcExteriorEquiv y` in the summand `q`.
* *Modulo the coefficient ideal the isomorphism is canonical* (`incFreeTermCohomologyEquiv_residue`,
  `incFreeTermCohomologyEquiv_residue_of_tmul`): for every `x ∈ F_p` and every `q`, reducing the
  `q`-summand of the image of `x` along `S_G → ℂ` (`incCoeffResidue`, `f ⊗ h ↦ f(0) h`) gives
  `zbcExteriorEquiv` of the internal-degree-`q` component of the Tor class of `x`.

Not claimed: the `S_G`-linear isomorphism itself is not canonical. It depends on the free basis of
the resolution; only its reduction modulo `(S_G)_+` is the canonical identification.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory TopologicalSpace AlgebraicGeometry CechProduct ProjectiveLine Finsupp
open ResolutionTools
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option linter.unusedSectionVars false

noncomputable section

/-! ### Reduction modulo the coefficient ideal -/

/-- **Reduction modulo the coefficient ideal** `(S_G)_+` of `S_G ⊗_ℂ M`: `f ⊗ m ↦ f(0) m`. -/
def incCoeffResidue (E : Type) (M : Type*) [AddCommGroup M] [Module ℂ M] :
    IncCoeffRing E ⊗[ℂ] M →ₗ[ℂ] M :=
  TensorProduct.lift ((LinearMap.lsmul ℂ M).comp (MvPolynomial.lcoeff ℂ 0))

theorem incCoeffResidue_tmul (E : Type) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : IncCoeffRing E) (m : M) :
    incCoeffResidue E M (f ⊗ₜ m) = MvPolynomial.constantCoeff f • m :=
  rfl

/-- The residue is semilinear over the constant coefficient. -/
theorem incCoeffResidue_smul (E : Type) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (s : IncCoeffRing E) (t : IncCoeffRing E ⊗[ℂ] M) :
    incCoeffResidue E M (s • t) = MvPolynomial.constantCoeff s • incCoeffResidue E M t := by
  induction t using TensorProduct.inductionOn with
  | tmul f m =>
    rw [TensorProduct.smul_tmul', incCoeffResidue_tmul, incCoeffResidue_tmul, smul_eq_mul,
      map_mul, mul_smul]
  | add t u ht hu => rw [smul_add, map_add, map_add, ht, hu, smul_add]

/-- A tensor `t ∈ S_G ⊗_ℂ M` lies in `P ⊗_ℂ M` for a `ℂ`-subspace `P ⊆ S_G` iff all its
coordinates in the `S_G`-basis `1 ⊗ b_i` lie in `P`. -/
theorem incCoeff_mem_range_rTensor_iff_repr (E : Type) {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ι : Type} [Fintype ι] (bM : Module.Basis ι ℂ M) (P : Submodule ℂ (IncCoeffRing E))
    (t : IncCoeffRing E ⊗[ℂ] M) :
    t ∈ LinearMap.range (LinearMap.rTensor M P.subtype) ↔
      ∀ i, (Algebra.TensorProduct.basis (IncCoeffRing E) bM).repr t i ∈ P := by
  constructor
  · rintro ⟨s, rfl⟩
    induction s using TensorProduct.inductionOn with
    | tmul a m =>
      intro i
      rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def]
      exact P.smul_mem _ a.2
    | add s u hs hu =>
      intro i
      rw [map_add, map_add, Finsupp.add_apply]
      exact P.add_mem (hs i) (hu i)
  · intro h
    rw [← (Algebra.TensorProduct.basis (IncCoeffRing E) bM).sum_repr t]
    refine Submodule.sum_mem _ fun i _ => ⟨⟨_, h i⟩ ⊗ₜ bM i, ?_⟩
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.basis_repr_symm_apply']
    rfl

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

local instance incFreeTermCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

@[reducible] local instance incFreeTermCohomologyModule (q j : ℕ) :
    Module ℂ (Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) :=
  G.exteriorBundleCohomologyModule ℂ q j

/-! ### The basis of exterior cohomology transported by the base change -/

/-- The bigraded Tor basis vector of a state is the Tor class of that state. -/
theorem incidenceTorInternalEquivState_symm_single {p q : ℕ} (c : G.IncBigradedBasis p q) :
    (G.incidenceTorInternalEquivState p q).symm (single c 1) =
      ⟨G.incidenceTorStateClass c.1 c.2.1, G.incidenceTorStateClass_mem c.1 c.2.1 c.2.2⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  apply G.incBigradedEmbed_injective ℂ p q
  rw [incBigradedEmbed_internalEquivState, incidenceTorFullState_stateClass]
  exact mapDomain_single

/-- The `q`-element edge set of a generator of internal degree `q`. -/
def incBigradedEdgeSet {p q : ℕ} (c : G.IncBigradedBasis p q) : Set.powersetCard E q :=
  ⟨c.1.1, c.2.2⟩

/-- The exterior class of the state of a bigraded generator. -/
def incBigradedExteriorClass {p q : ℕ} (c : G.IncBigradedBasis p q) :
    Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p) :=
  G.exteriorStateClass ℂ (G.incBigradedEdgeSet c) c.1.2 (G.incBigraded_cohomologyDegree c)

/-- The `ℂ`-basis of `H^{q-p}(X_G, ∧^q F_G^∨)` obtained from the Tor basis of bidegree `(p, q)`
by the base-change isomorphism `zbcExteriorEquiv`. -/
def incExteriorStateBasis {p q : ℕ} (h : p ≤ q) :
    Module.Basis (G.IncBigradedBasis p q) ℂ (Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p)) :=
  Finsupp.basisSingleOne.map
    ((G.incidenceTorInternalEquivState p q).symm.trans (G.zbcExteriorEquiv h))

/-- The transported basis vectors are the exterior classes of the same states. -/
theorem incExteriorStateBasis_apply {p q : ℕ} (h : p ≤ q) (c : G.IncBigradedBasis p q) :
    G.incExteriorStateBasis h c = G.incBigradedExteriorClass c := by
  rw [incExteriorStateBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne,
    LinearEquiv.trans_apply, incidenceTorInternalEquivState_symm_single]
  exact G.zbcExteriorEquiv_stateClass h (G.incBigradedEdgeSet c) c.1.2 c.2.1

/-! ### The free terms -/

/-- The internal degrees of the summands in homological degree `p`: `p ≤ q ≤ |E|`. -/
abbrev IncFreeTermDegree (_G : Multigraph V E) (p : ℕ) := ↥(Finset.Icc p (Fintype.card E))

theorem incFreeTermDegree_le {p : ℕ} (q : G.IncFreeTermDegree p) : p ≤ (q : ℕ) :=
  (Finset.mem_Icc.mp q.2).1

/-- The internal degree of a generator of homological degree `p`, as a summand index. -/
def incFreeTermGeneratorDegree {p : ℕ}
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) : G.IncFreeTermDegree p :=
  ⟨G.incResolutionInternalDegree b.1, Finset.mem_Icc.mpr ⟨by
    have h := G.incResolutionDegree_add_support b.1
    rw [b.2] at h
    omega, G.incResolutionInternalDegree_le b.1⟩⟩

/-- The generators of homological degree `p`, sorted by internal degree. -/
def incFreeTermDegreeEquiv (p : ℕ) :
    {b : G.IncResolutionBasis // G.incResolutionDegree b = p} ≃
      Σ q : G.IncFreeTermDegree p, G.IncBigradedBasis p q where
  toFun b := ⟨G.incFreeTermGeneratorDegree b, ⟨b.1, b.2, rfl⟩⟩
  invFun c := ⟨c.2.1, c.2.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨q, hq⟩, ⟨b, hb, hbq⟩⟩
    change G.incResolutionInternalDegree b = q at hbq
    subst hbq
    rfl

/-- **The free terms of Theorem 3.4** (`alg:free-terms`): the term `F_p` of the actual minimal free
resolution is `S_G`-linearly isomorphic to the finite product over `p ≤ q ≤ |E|` of
`S_G ⊗_ℂ H^{q-p}(X_G, ∧^q F_G^∨)`, the `q`-summand being `H^{q-p} ⊗ S_G(-q)`. The generator `e_b`
goes to `1 ⊗` the exterior class of the state `b` in the summand of its internal degree. -/
def incFreeTermCohomologyEquiv (p : ℕ) :
    G.IncFreeTerm p ≃ₗ[IncCoeffRing E] ((q : G.IncFreeTermDegree p) →
      IncCoeffRing E ⊗[ℂ] Sheaf.H.{1} (G.exteriorBundleAbelian ℂ (q : ℕ)) ((q : ℕ) - p)) :=
  (G.incFreeTermBasis p).equiv
    (Pi.basis fun q => Algebra.TensorProduct.basis (IncCoeffRing E)
      (G.incExteriorStateBasis (G.incFreeTermDegree_le q)))
    (G.incFreeTermDegreeEquiv p)

/-- The state basis vector of a free term is the generator `e_b`. -/
theorem incFreeTermBasis_apply_eq (p : ℕ)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    G.incFreeTermBasis p b = ⟨single b.1 1, single_mem_supported _ _ b.2⟩ := by
  apply (G.incFreeTermBasis p).repr.injective
  rw [Module.Basis.repr_self]
  ext c
  rw [incFreeTermBasis_repr_apply]
  by_cases hc : c = b
  · subst hc
    simp
  · rw [single_eq_of_ne hc, single_eq_of_ne (fun h => hc (Subtype.ext h))]

/-- The generator indexed by a bigraded basis element goes to the basis vector `1 ⊗ h` of the
summand of its internal degree. -/
theorem incFreeTermCohomologyEquiv_bigraded (p : ℕ)
    (j : Σ q : G.IncFreeTermDegree p, G.IncBigradedBasis p q) :
    G.incFreeTermCohomologyEquiv p (G.incFreeTermBasis p ((G.incFreeTermDegreeEquiv p).symm j)) =
      Pi.single j.1 ((1 : IncCoeffRing E) ⊗ₜ G.incBigradedExteriorClass j.2) := by
  rw [incFreeTermCohomologyEquiv, Module.Basis.equiv_apply, Equiv.apply_symm_apply,
    Pi.basis_apply, Algebra.TensorProduct.basis_apply, incExteriorStateBasis_apply]

/-- The image of a basis generator, in the summand of its internal degree. -/
theorem incFreeTermCohomologyEquiv_basis (p : ℕ)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    G.incFreeTermCohomologyEquiv p (G.incFreeTermBasis p b) =
      Pi.single (G.incFreeTermDegreeEquiv p b).1
        ((1 : IncCoeffRing E) ⊗ₜ G.incBigradedExteriorClass (G.incFreeTermDegreeEquiv p b).2) := by
  have h := G.incFreeTermCohomologyEquiv_bigraded p (G.incFreeTermDegreeEquiv p b)
  rwa [Equiv.symm_apply_apply] at h

/-- The internal degree `q` of a state of a `q`-element edge set is a summand index. -/
theorem mem_incFreeTermDegree {p q : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    q ∈ Finset.Icc p (Fintype.card E) :=
  Set.powersetCard.card_eq S ▸ (G.incFreeTermGeneratorDegree ⟨⟨S, κ⟩, hb⟩).2

/-- **Generators.** The generator `e_b` of the state `b = (S, κ)`, `|S| = q`, goes to
`1 ⊗ (exterior class of (S, κ))` in the summand of internal degree `q`. -/
theorem incFreeTermCohomologyEquiv_stateGenerator {p q : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    G.incFreeTermCohomologyEquiv p ⟨single ⟨S, κ⟩ 1, single_mem_supported _ _ hb⟩ =
      Pi.single (⟨q, G.mem_incFreeTermDegree S κ hb⟩ : G.IncFreeTermDegree p)
        ((1 : IncCoeffRing E) ⊗ₜ
          G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb)) := by
  have h := G.incFreeTermCohomologyEquiv_bigraded p
    ⟨⟨q, G.mem_incFreeTermDegree S κ hb⟩, ⟨⟨S, κ⟩, hb, Set.powersetCard.card_eq S⟩⟩
  rw [incFreeTermBasis_apply_eq] at h
  exact h

/-! ### The acceptance test: comparison with the canonical identification -/

/-- The Tor class of a state is `1 ⊗ e_b` under `incidenceTorIsoFreeTerm`. -/
theorem incidenceTorIsoFreeTerm_stateClass (b : G.IncResolutionBasis) {p : ℕ}
    (hb : G.incResolutionDegree b = p) :
    letI : Algebra (IncCoeffRing E) ℂ :=
      (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
    (G.incidenceTorIsoFreeTerm p).hom (G.incidenceTorStateClass b hb) =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] (⟨single b 1, single_mem_supported _ _ hb⟩ : G.IncFreeTerm p) :=
  G.incFreeTermToTor_eq_tmul p _

/-- A Tor class corresponding to `1 ⊗ e_b` under `incidenceTorIsoFreeTerm` is the Tor class of the
state `b`. -/
theorem eq_incidenceTorStateClass_of_tmul (b : G.IncResolutionBasis) {p : ℕ}
    (hb : G.incResolutionDegree b = p) (y : G.incidenceTor p)
    (hy : letI : Algebra (IncCoeffRing E) ℂ :=
        (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
      (G.incidenceTorIsoFreeTerm p).hom y =
        (1 : ℂ) ⊗ₜ[IncCoeffRing E] (⟨single b 1, single_mem_supported _ _ hb⟩ : G.IncFreeTerm p)) :
    y = G.incidenceTorStateClass b hb := by
  apply (ModuleCat.mono_iff_injective (G.incidenceTorIsoFreeTerm p).hom).mp inferInstance
  rw [hy, incidenceTorIsoFreeTerm_stateClass]

/-- The image of the generator of a state is `1 ⊗` the base change of its Tor class. -/
theorem incFreeTermCohomologyEquiv_stateGenerator_eq_zbc {p q : ℕ} (h : p ≤ q)
    (S : Set.powersetCard E q) (κ : HBasis (G.deg (S : Finset E)))
    (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    G.incFreeTermCohomologyEquiv p ⟨single ⟨S, κ⟩ 1, single_mem_supported _ _ hb⟩ =
      Pi.single (⟨q, G.mem_incFreeTermDegree S κ hb⟩ : G.IncFreeTermDegree p)
        ((1 : IncCoeffRing E) ⊗ₜ G.zbcExteriorEquiv h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
          G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩) := by
  rw [incFreeTermCohomologyEquiv_stateGenerator G S κ hb, G.zbcExteriorEquiv_stateClass h S κ hb]

/-- **Acceptance test on generators.** Let `e_b` be the generator of the state `b = (S, κ)`, of
homological degree `p` and internal degree `q = |S|`, and let `y ∈ Tor_p` correspond to `1 ⊗ e_b`
under `incidenceTorIsoFreeTerm`. Then `y` has internal degree `q`; the base-change isomorphism
`zbcExteriorEquiv` sends it to the exterior class of the same state and index; and the image of
`e_b` is `1 ⊗ zbcExteriorEquiv y` in the summand `q`. -/
theorem incFreeTermCohomologyEquiv_canonical {p q : ℕ} (h : p ≤ q) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p)
    (y : G.incidenceTor p)
    (hy : letI : Algebra (IncCoeffRing E) ℂ :=
        (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
      (G.incidenceTorIsoFreeTerm p).hom y = (1 : ℂ) ⊗ₜ[IncCoeffRing E]
        (⟨single ⟨S, κ⟩ 1, single_mem_supported _ _ hb⟩ : G.IncFreeTerm p)) :
    ∃ hyq : y ∈ G.incidenceTorInternalPiece p q,
      G.zbcExteriorEquiv h ⟨y, hyq⟩ =
          G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb) ∧
        G.incFreeTermCohomologyEquiv p ⟨single ⟨S, κ⟩ 1, single_mem_supported _ _ hb⟩ =
          Pi.single (⟨q, G.mem_incFreeTermDegree S κ hb⟩ : G.IncFreeTermDegree p)
            ((1 : IncCoeffRing E) ⊗ₜ G.zbcExteriorEquiv h ⟨y, hyq⟩) := by
  obtain rfl := G.eq_incidenceTorStateClass_of_tmul _ hb y hy
  exact ⟨G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S),
    G.zbcExteriorEquiv_stateClass h S κ hb,
    G.incFreeTermCohomologyEquiv_stateGenerator_eq_zbc h S κ hb⟩

/-- Origin specialization of free terms is semilinear over the constant coefficient. -/
theorem incFreeTermToTor_constantCoeff_smul (p : ℕ) (s : IncCoeffRing E) (x : G.IncFreeTerm p) :
    G.incFreeTermToTor p (s • x) = MvPolynomial.constantCoeff s • G.incFreeTermToTor p x := by
  apply G.incidenceTorFullState_injective p
  rw [incidenceTorFullState_class, LinearMap.map_smul, incidenceTorFullState_class]
  ext b
  simp only [Submodule.coe_smul, mapRange_apply, Finsupp.smul_apply, smul_eq_mul, map_mul]

/-- The specialization of a basis generator is the Tor class of its state. -/
theorem incFreeTermToTor_basis (p : ℕ)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    G.incFreeTermToTor p (G.incFreeTermBasis p b) = G.incidenceTorStateClass b.1 b.2 := by
  rw [incFreeTermBasis_apply_eq]
  rfl

/-- The internal-degree-`q` component of the Tor class of an element of `F_p`. -/
def incFreeTermTorComponent (p : ℕ) (q : G.IncFreeTermDegree p) :
    G.IncFreeTerm p →ₗ[ℂ] G.incidenceTorInternalPiece p q :=
  LinearMap.codRestrict _ ((G.incidenceTorComponent p q).comp (G.incFreeTermToTor p))
    (fun _ => G.incidenceTorComponent_mem p q _)

theorem incFreeTermTorComponent_val (p : ℕ) (q : G.IncFreeTermDegree p) (x : G.IncFreeTerm p) :
    (G.incFreeTermTorComponent p q x).val =
      G.incidenceTorComponent p q (G.incFreeTermToTor p x) :=
  rfl

theorem incFreeTermTorComponent_smul (p : ℕ) (q : G.IncFreeTermDegree p) (s : IncCoeffRing E)
    (x : G.IncFreeTerm p) :
    G.incFreeTermTorComponent p q (s • x) =
      MvPolynomial.constantCoeff s • G.incFreeTermTorComponent p q x := by
  apply Subtype.ext
  rw [incFreeTermTorComponent_val, incFreeTermToTor_constantCoeff_smul, map_smul,
    Submodule.coe_smul, incFreeTermTorComponent_val]

/-- The residue statement on basis generators. -/
theorem incFreeTermCohomologyEquiv_residue_basis (p : ℕ) (q : G.IncFreeTermDegree p)
    (b : {b : G.IncResolutionBasis // G.incResolutionDegree b = p}) :
    incCoeffResidue E _ (G.incFreeTermCohomologyEquiv p (G.incFreeTermBasis p b) q) =
      G.zbcExteriorEquiv (G.incFreeTermDegree_le q)
        (G.incFreeTermTorComponent p q (G.incFreeTermBasis p b)) := by
  have hmem := G.incidenceTorStateClass_mem b.1 b.2 rfl
  have hc := G.incidenceTorComponent_of_mem p q _ hmem
  rw [incFreeTermCohomologyEquiv_basis]
  by_cases hq : q = (G.incFreeTermDegreeEquiv p b).1
  · subst hq
    have e : G.incFreeTermTorComponent p (G.incFreeTermDegreeEquiv p b).1
        (G.incFreeTermBasis p b) = ⟨G.incidenceTorStateClass b.1 b.2, hmem⟩ := by
      apply Subtype.ext
      rw [incFreeTermTorComponent_val, incFreeTermToTor_basis, hc]
      exact ite_eq_left rfl
    rw [Pi.single_eq_same, incCoeffResidue_tmul, map_one, one_smul, e]
    exact (G.zbcExteriorEquiv_stateClass _
      (G.incBigradedEdgeSet (G.incFreeTermDegreeEquiv p b).2) b.1.2 b.2).symm
  · have hq' : (q : ℕ) ≠ G.incResolutionInternalDegree b.1 := fun h => hq (Subtype.ext h)
    have e : G.incFreeTermTorComponent p q (G.incFreeTermBasis p b) = 0 := by
      apply Subtype.ext
      rw [incFreeTermTorComponent_val, incFreeTermToTor_basis, hc]
      exact ite_eq_right hq'
    rw [Pi.single_eq_of_ne hq, map_zero, e, map_zero]

/-- **Modulo the coefficient ideal, the isomorphism is the canonical identification.** For every
`x ∈ F_p` and every internal degree `q`, the residue of the `q`-summand of the image of `x` is the
base change `zbcExteriorEquiv` of the internal-degree-`q` component of the Tor class of `x`. -/
theorem incFreeTermCohomologyEquiv_residue (p : ℕ) (q : G.IncFreeTermDegree p)
    (x : G.IncFreeTerm p) :
    incCoeffResidue E _ (G.incFreeTermCohomologyEquiv p x q) =
      G.zbcExteriorEquiv (G.incFreeTermDegree_le q) (G.incFreeTermTorComponent p q x) := by
  let f₁ : G.IncFreeTerm p →ₛₗ[(MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)]
      Sheaf.H.{1} (G.exteriorBundleAbelian ℂ (q : ℕ)) ((q : ℕ) - p) :=
    { toFun := fun x => incCoeffResidue E _ (G.incFreeTermCohomologyEquiv p x q)
      map_add' := fun x y => by rw [map_add, Pi.add_apply, map_add]
      map_smul' := fun s x => by rw [map_smul, Pi.smul_apply, incCoeffResidue_smul] }
  let f₂ : G.IncFreeTerm p →ₛₗ[(MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)]
      Sheaf.H.{1} (G.exteriorBundleAbelian ℂ (q : ℕ)) ((q : ℕ) - p) :=
    { toFun := fun x => G.zbcExteriorEquiv (G.incFreeTermDegree_le q)
        (G.incFreeTermTorComponent p q x)
      map_add' := fun x y => by rw [map_add, map_add]
      map_smul' := fun s x => by rw [incFreeTermTorComponent_smul, map_smul] }
  have h : f₁ = f₂ := (G.incFreeTermBasis p).ext fun b =>
    G.incFreeTermCohomologyEquiv_residue_basis p q b
  exact LinearMap.congr_fun h x

/-- The residue statement through `incidenceTorIsoFreeTerm`: if `y ∈ Tor_p` corresponds to `1 ⊗ x`
under `Tor_p ≅ ℂ ⊗_{S_G} F_p`, the residue of the `q`-summand of the image of `x` is the base change
of the internal-degree-`q` component of `y`. -/
theorem incFreeTermCohomologyEquiv_residue_of_tmul (p : ℕ) (q : G.IncFreeTermDegree p)
    (x : G.IncFreeTerm p) (y : G.incidenceTor p)
    (hy : letI : Algebra (IncCoeffRing E) ℂ :=
        (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
      (G.incidenceTorIsoFreeTerm p).hom y = (1 : ℂ) ⊗ₜ[IncCoeffRing E] x) :
    incCoeffResidue E _ (G.incFreeTermCohomologyEquiv p x q) =
      G.zbcExteriorEquiv (G.incFreeTermDegree_le q)
        ⟨G.incidenceTorComponent p q y, G.incidenceTorComponent_mem p q y⟩ := by
  have hxy : y = G.incFreeTermToTor p x := by
    apply (ModuleCat.mono_iff_injective (G.incidenceTorIsoFreeTerm p).hom).mp inferInstance
    rw [hy, incFreeTermToTor_eq_tmul]
  subst hxy
  rw [G.incFreeTermCohomologyEquiv_residue p q x]
  congr 1

/-! ### The internal grading -/

/-- Coordinates of the image in the basis `1 ⊗ (exterior basis)` of a summand are the
coordinates in the state basis. -/
theorem incFreeTermCohomologyEquiv_repr (p : ℕ) (x : G.IncFreeTerm p) (q : G.IncFreeTermDegree p)
    (c : G.IncBigradedBasis p q) :
    (Algebra.TensorProduct.basis (IncCoeffRing E)
        (G.incExteriorStateBasis (G.incFreeTermDegree_le q))).repr
        (G.incFreeTermCohomologyEquiv p x q) c =
      (G.incFreeTermBasis p).repr x ((G.incFreeTermDegreeEquiv p).symm ⟨q, c⟩) := by
  let B := Pi.basis fun q : G.IncFreeTermDegree p => Algebra.TensorProduct.basis (IncCoeffRing E)
    (G.incExteriorStateBasis (G.incFreeTermDegree_le q))
  let f₁ : G.IncFreeTerm p →ₗ[IncCoeffRing E] IncCoeffRing E :=
    (Finsupp.lapply ⟨q, c⟩).comp (B.repr.toLinearMap.comp
      (G.incFreeTermCohomologyEquiv p).toLinearMap)
  let f₂ : G.IncFreeTerm p →ₗ[IncCoeffRing E] IncCoeffRing E :=
    (Finsupp.lapply ((G.incFreeTermDegreeEquiv p).symm ⟨q, c⟩)).comp
      (G.incFreeTermBasis p).repr.toLinearMap
  have h : f₁ = f₂ := (G.incFreeTermBasis p).ext fun b => by
    simp only [f₁, f₂, B, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      incFreeTermCohomologyEquiv, Module.Basis.equiv_apply, Module.Basis.repr_self,
      Finsupp.single_apply, Equiv.eq_symm_apply]
  have h1 := LinearMap.congr_fun h x
  simp only [f₁, f₂, B, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
    Pi.basis_repr] at h1
  exact h1

/-- **The isomorphism preserves the internal grading**, in both directions. An element `x ∈ F_p`
has internal degree `n` (`incFreeTermInternalPiece`: the coefficient of `e_b` is homogeneous of
degree `n - |b|`) iff, for every `q`, the `q`-summand of its image lies in
`(S_G)_{n-q} ⊗_ℂ H^{q-p}`, the internal degree `n` part of `S_G(-q) ⊗_ℂ H^{q-p}` (zero for
`n < q`). -/
theorem incFreeTermCohomologyEquiv_mem_internal_iff (p n : ℕ) (x : G.IncFreeTerm p) :
    (∀ q : G.IncFreeTermDegree p, G.incFreeTermCohomologyEquiv p x q ∈
      LinearMap.range (LinearMap.rTensor _
        (homogeneousCoeffPiece (σ := IncCoeffIdx E) (k := ℂ) ((n : ℤ) - ((q : ℕ) : ℤ))).subtype)) ↔
      x ∈ G.incFreeTermInternalPiece p n := by
  have key : x ∈ G.incFreeTermInternalPiece p n ↔ ∀ b, (G.incFreeTermBasis p).repr x b ∈
      homogeneousCoeffPiece (σ := IncCoeffIdx E) (k := ℂ)
        ((n : ℤ) - (G.incResolutionInternalDegree b.val : ℤ)) := Iff.rfl
  rw [key]
  constructor
  · intro h b
    have hb := (incCoeff_mem_range_rTensor_iff_repr E
      (G.incExteriorStateBasis (G.incFreeTermDegree_le (G.incFreeTermDegreeEquiv p b).1)) _ _).mp
      (h (G.incFreeTermDegreeEquiv p b).1) (G.incFreeTermDegreeEquiv p b).2
    rw [incFreeTermCohomologyEquiv_repr, Sigma.eta, Equiv.symm_apply_apply] at hb
    exact hb
  · intro h q
    apply (incCoeff_mem_range_rTensor_iff_repr E
      (G.incExteriorStateBasis (G.incFreeTermDegree_le q)) _ _).mpr
    intro c
    rw [incFreeTermCohomologyEquiv_repr]
    have hc := h ((G.incFreeTermDegreeEquiv p).symm ⟨q, c⟩)
    rwa [show G.incResolutionInternalDegree ((G.incFreeTermDegreeEquiv p).symm ⟨q, c⟩).val =
      (q : ℕ) from c.2.2] at hc

end

end BPFixedPoints.Multigraph
