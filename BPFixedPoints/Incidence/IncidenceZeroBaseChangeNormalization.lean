import BPFixedPoints.Incidence.IncidenceZeroBaseChangeSheaf

/-! # The derived base change to the coefficient origin and its normalization audit

This file assembles the comparison of the paper (end of the proof of Theorem 3.4,
`alg:zero-base-change`):

  `Tor_p^{S_G}(𝒰_G, ℂ)_q ≅ H^{q-p}(X_G, ∧^q F_G^∨)`, for `p ≤ q`.

**Definition** (`zbcExteriorEquiv`). The composite of
1. `zbcTorEquiv`: actual Tor (Mathlib's left derived extension of scalars along
   `constantCoeff`) is identified with the cohomology of the base-changed Čech model
   `ℂ ⊗_{S_G} K` by the base change of the comparison chain map `ι : F → K` of the existing finite
   homological perturbation (`IncidenceZeroBaseChangeTor`);
2. `zbcSheafEquiv`: the base-changed model has zero Koszul part, so in internal degree `q` it is
   the Čech complex of `∧^q F_G^∨ = ⊕_{|S| = q} O(-d_S)` on the product of the standard two-chart
   covers, whose cohomology is the actual sheaf cohomology (`IncidenceZeroBaseChangeSheaf`).

Neither step is defined through state coordinates.

**Normalization audit** (`zbcExteriorEquiv_apply`, `zbcExteriorEquiv_eq`). The base-change
isomorphism *equals* the existing isomorphism `incidenceTorExteriorEquiv`, which was built from
the state bases of both sides. State coordinates enter only here, to compare with that
isomorphism. The proof evaluates the composite on an arbitrary Tor class: by `zbcTorCycle_eq`
(from `zbcSpecialize_inclusion`: the perturbative corrections of `ι` vanish at the origin) the
base change of `ι` is the Čech inclusion over `ℂ` of the state coordinates of the class, and its
component at a `q`-element edge subset `S` is the Čech inclusion of the
edge-set state coordinate (`zbcComponent_torCycle`); by `zbcTwistSheafEquiv_inclusion` the
Čech-to-sheaf comparison sends this to the class that the existing state comparison assigns to
the same coordinate. There is no sign and no rescaling. Consequences:
* `zbcExteriorEquiv_stateClass`: the Tor class of every state goes to the exterior class of the
  same state with coefficient `+1`, in every bidegree; `zbcTorCycle_stateClass` is the Tor-side
  computation (the perturbative corrections vanish at the origin), and
  `smul_zbcExteriorEquiv_stateClass_eq_iff` shows that the test detects every rescaling;
* `zbcExteriorEquiv_product`, `zbcExteriorEquiv_one`: the base-change isomorphism is
  multiplicative and unital for the standard Tor product and the exterior cohomology product.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CechProduct ProjectiveLine IncidencePerturbation Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

@[reducible] local instance zbcNormCyclesAddCommGroup (p q : ℕ) : AddCommGroup (G.zbcCycles p q) :=
  (G.zbcCycles p q).addCommGroup

@[reducible] local instance zbcNormCyclesModule (p q : ℕ) : Module ℂ (G.zbcCycles p q) :=
  (G.zbcCycles p q).module

@[reducible] local instance zbcNormTwistCyclesAddCommGroup (d : V → ℕ) (j : ℕ) :
    AddCommGroup (zbcTwistCycles V d j) := (zbcTwistCycles V d j).addCommGroup

@[reducible] local instance zbcNormTwistCyclesModule (d : V → ℕ) (j : ℕ) :
    Module ℂ (zbcTwistCycles V d j) := (zbcTwistCycles V d j).module

local instance zbcNormalizationHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **The base-changed comparison is the Čech inclusion over `ℂ`.** On Tor, the base change of the
perturbed inclusion `ι` is the unperturbed Čech inclusion over `ℂ` applied to the state
coordinates of the specialized free resolution: the perturbative corrections vanish at the
coefficient origin. -/
theorem zbcTorCycle_eq (p : ℕ) (x : G.incidenceTor p) :
    G.zbcTorCycle p x = G.zbcContraction.i (G.incidenceTorFullState p x) := by
  obtain ⟨y, rfl⟩ := G.incFreeTermToTor_surjective p x
  rw [zbcTorCycle_class, zbcSpecialize_inclusion, incidenceTorFullState_class,
    zbcFreeSpecialize_apply]

/-- **The base-change isomorphism of the paper.** For `p ≤ q`,
`Tor_p^{S_G}(𝒰_G, ℂ)_q ≅ H^{q-p}(X_G, ∧^q F_G^∨)`: the base change along the coefficient origin
of the comparison chain map from the free resolution to the Čech–Koszul model, followed by the
identification of the base-changed model with the Čech complex of the exterior bundles and the
Čech-to-sheaf comparison. -/
def zbcExteriorEquiv {p q : ℕ} (h : p ≤ q) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ] Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p) :=
  (G.zbcTorEquiv p q).trans (G.zbcSheafEquiv (Nat.sub_add_cancel h))

/-- The component at a `q`-element edge subset of the base-changed cycle of a Tor class is the
Čech inclusion of its edge-set state coordinate. -/
theorem zbcComponent_torCycle {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q)
    (S : Set.powersetCard E q) :
    G.zbcComponent (Nat.sub_add_cancel h) S ⟨G.zbcTorCycle p x.val, G.zbcTorCycle_mem x⟩ =
      zbcTwistInclusion V (G.deg (S : Finset E)) (q - p) (G.incidenceTorBigradedStateEquiv h x S) := by
  apply Subtype.ext
  rw [zbcComponent_val, zbcTwistInclusion_val]
  change G.zbcTorCycle p x.val (S : Finset E) = _
  rw [zbcTorCycle_eq, zbcContraction_i_apply]
  congr 1
  ext κ
  rw [incidenceTorBigradedStateEquiv_apply]
  rfl

/-- **Normalization audit: the base-change isomorphism is the existing Tor-to-exterior
isomorphism.** On every element of every bigraded piece. -/
theorem zbcExteriorEquiv_apply {p q : ℕ} (h : p ≤ q) (x : G.incidenceTorInternalPiece p q) :
    G.zbcExteriorEquiv h x = G.incidenceTorExteriorEquiv h x := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  let _ := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule ℂ V (G.deg S) (q - p)
  change G.zbcSheafEquiv (Nat.sub_add_cancel h) (G.zbcTorEquiv p q x) =
    (G.exteriorBundleStateLinearEquiv ℂ q (q - p)).symm (G.incidenceTorBigradedStateEquiv h x)
  rw [zbcTorEquiv_apply, zbcSheafEquiv_class]
  change (G.exteriorBundleCohomologyLinearEquiv ℂ q (q - p)).symm _ =
    (G.exteriorBundleCohomologyLinearEquiv ℂ q (q - p)).symm _
  congr 1
  funext S
  rw [G.zbcComponent_torCycle h x S, zbcTwistSheafEquiv_inclusion]
  rfl

theorem zbcExteriorEquiv_eq {p q : ℕ} (h : p ≤ q) :
    G.zbcExteriorEquiv h = G.incidenceTorExteriorEquiv h :=
  LinearEquiv.ext (G.zbcExteriorEquiv_apply h)

/-- On the Tor class of a state `b` (the specialization of the free generator `e_b`), the
base-changed comparison is the Čech inclusion of `e_b` over `ℂ`, with coefficient `+1`: the
perturbative corrections of the inclusion vanish at the coefficient origin. -/
theorem zbcTorCycle_stateClass (b : G.IncResolutionBasis) {p : ℕ}
    (hb : G.incResolutionDegree b = p) :
    G.zbcTorCycle p (G.incidenceTorStateClass b hb) = G.zbcContraction.i (single b 1) := by
  rw [zbcTorCycle_eq, incidenceTorFullState_stateClass]

/-- **Normalization audit on state classes, every bidegree.** The base-change isomorphism sends
the Tor class of every state to the exterior class of the same state, with coefficient `+1` and no
sign. -/
theorem zbcExteriorEquiv_stateClass {p q : ℕ} (h : p ≤ q) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    G.zbcExteriorEquiv h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
        G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩ =
      G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb) := by
  rw [zbcExteriorEquiv_apply]
  exact G.incidenceTorExteriorEquiv_stateClass h S κ hb

/-- The state class test detects rescaling of the base-change isomorphism as well. -/
theorem smul_zbcExteriorEquiv_stateClass_eq_iff {p q : ℕ} (h : p ≤ q)
    (S : Set.powersetCard E q) (κ : HBasis (G.deg (S : Finset E)))
    (hb : G.incResolutionDegree ⟨S, κ⟩ = p) (c : ℂ) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    c • G.zbcExteriorEquiv h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
        G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩ =
      G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb) ↔
      c = 1 := by
  rw [zbcExteriorEquiv_apply]
  exact G.smul_incidenceTorExteriorEquiv_stateClass_eq_iff h S κ hb c

/-- The base-change isomorphism sends the standard Tor product to the exterior cohomology
product. -/
theorem zbcExteriorEquiv_product {p q p' q' : ℕ} (h : p ≤ q) (h' : p' ≤ q')
    (x : G.incidenceTorInternalPiece p q) (y : G.incidenceTorInternalPiece p' q') :
    G.zbcExteriorEquiv (Nat.add_le_add h h')
        ⟨G.incidenceTorProduct p p' x.val y.val,
          G.incidenceTorProduct_internal_degree p p' q q' x.property y.property⟩ =
      G.exteriorHCast ℂ rfl (by omega : (q - p) + (q' - p') = (q + q') - (p + p'))
        (G.exteriorCohomologyProduct ℂ q q' (q - p) (q' - p')
          (G.zbcExteriorEquiv h x) (G.zbcExteriorEquiv h' y)) := by
  rw [zbcExteriorEquiv_apply, zbcExteriorEquiv_apply, zbcExteriorEquiv_apply]
  exact G.incidenceTorExteriorEquiv_product h h' x y

/-- The base-change isomorphism sends the Tor unit to the exterior cohomology unit. -/
theorem zbcExteriorEquiv_one :
    G.zbcExteriorEquiv (le_refl 0) ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩ =
      G.exteriorCohomologyUnit ℂ := by
  rw [zbcExteriorEquiv_apply]
  exact G.incidenceTorExteriorEquiv_one

end

end BPFixedPoints.Multigraph
