import BPFixedPoints.Incidence.IncidenceTorExteriorIsomorphism

/-! # Normalization of the Tor-to-exterior isomorphism: acceptance tests

If `Φ_{p,q}` (`incidenceTorExteriorEquiv`) is a natural, multiplicative and unital bigraded
isomorphism, then so is `λ^p Φ_{p,q}` for every `λ ∈ ℂ^×`. Naturality, products and the unit
therefore do not determine the normalization; it is fixed by the coefficient formula
`incidenceTorExteriorEquiv_coefficient`. This file states the normalization as explicit
acceptance tests on specified representatives.

**State classes.** For a resolution state `b = (S, κ)` (a `q`-element edge set `S` and a state
`κ` of the twist `d_S`) of homological degree `p`:
* the *Tor class of the state* (`incidenceTorStateClass`) is the specialization at the coefficient
  origin of the free generator `e_b` of the actual free resolution; its full state vector is the
  basis vector `e_b` with coefficient `1` (`incidenceTorFullState_stateClass`), and it lies in the
  internal piece of bidegree `(p, q)` (`incidenceTorStateClass_mem`);
* the *exterior class of the state* (`exteriorStateClass`) is the class of actual cohomology
  `H^{q-p}` of the `q`-th exterior bundle whose state components are `single κ 1` in the summand
  of `S` and zero elsewhere (`exteriorBundleStateLinearEquiv_stateClass`); its state vector is
  `e_b` (`exteriorCohomologyState_stateClass`). It is the image under the biproduct inclusion of
  the summand of `S` of the state class of that summand (`exteriorStateClass_eq_map_incl`), and in
  positive cohomological degree it is represented by the specified cell cocycle whose signed tensor
  coefficients are the contraction inclusion of `single κ 1` (`exteriorStateClass_succ`, with
  `ProjectiveLine.vertexTwistCellStateInclusion_coefficient`).

**Acceptance tests.**
* *State classes, every bidegree* (`incidenceTorExteriorEquiv_stateClass`): `Φ` sends the Tor class
  of a state to the exterior class of the same state, with coefficient `+1` and no sign.
* *Rescaling is detected in positive Tor degree*
  (`smul_incidenceTorExteriorEquiv_stateClass_eq_iff`): `c • Φ(class) = exterior class` holds iff
  `c = 1`. Applied with `c = λ^p`, the rescaled isomorphism `λ^p Φ` passes the test iff `λ^p = 1`;
  in Tor degree `p = 1` iff `λ = 1`. The concrete instance on `K₄` in bidegree `(1, 5)`, in
  cohomological degree `4`, is `Examples.K4_torNormalization_pins_scalar`
  (`BPFixedPoints.Examples.TorNormalizationK4`).
* *Unit* (`incidenceTorExteriorEquiv_normalization_unit`, a restatement of
  `incidenceTorExteriorEquiv_one`): the Tor unit goes to the exterior unit. The two units are the
  state classes of the unique state of the empty edge set (`incidenceTorOne_eq_stateClass`,
  `exteriorCohomologyUnit_eq_stateClass`), so this is the bidegree `(0, 0)` case of the state class
  test; since `λ^0 = 1` it cannot detect a rescaling.

Sign tests of the maps on both sides are already theorems and are not repeated here: flipping the
sign of one edge of the two-cycle multiplies its Tor class by `-1`
(`incidenceTorSign_twoCycleClass`); the reversal of both edges introduces no sign and the signed
reversal introduces `-1` (`incidenceTorFullState_twoCycleReverse`,
`incidenceTorFullState_twoCycleSignedReverse`); the swap of the two vertices of `O(-2,-2)` sends
the class of the Laurent generator of `H²` to its negative (`vertexTwistHPerm_swap`), and vertex
bijections preserve the unit class (`vertexTwistHPerm_unit`).

Not proved here: any uniqueness statement for natural isomorphisms. The tests pin `Φ` against the
independently defined state comparisons of the two sides (the Tor state coordinates and the cell
state comparison of exterior cohomology); they say nothing about other choices of these
comparisons.
-/

namespace BPFixedPoints.Multigraph
open CategoryTheory TopologicalSpace AlgebraicGeometry CechProduct ProjectiveLine SchemeTools Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
noncomputable section

local instance incidenceTorNormalizationHasExt (R : Type) [CommRing R] (V : Type) [Fintype V] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-! ## The Tor class of a state -/

section TorSide

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- The Tor class of one resolution state `b` of homological degree `p`: the specialization at the
coefficient origin of the free generator `e_b` of the actual free resolution. -/
def incidenceTorStateClass (b : G.IncResolutionBasis) {p : ℕ} (hb : G.incResolutionDegree b = p) :
    G.incidenceTor p :=
  G.incFreeTermToTor p ⟨single b 1, single_mem_supported _ _ hb⟩

/-- The full state vector of the Tor class of a state is the basis vector of the state. -/
theorem incidenceTorFullState_stateClass (b : G.IncResolutionBasis) {p : ℕ}
    (hb : G.incResolutionDegree b = p) :
    G.incidenceTorFullState p (G.incidenceTorStateClass b hb) = single b 1 := by
  rw [incidenceTorStateClass, incidenceTorFullState_class, mapRange_single, map_one]

/-- The Tor class of a state lies in the internal piece of its internal degree. -/
theorem incidenceTorStateClass_mem (b : G.IncResolutionBasis) {p q : ℕ}
    (hb : G.incResolutionDegree b = p) (hq : G.incResolutionInternalDegree b = q) :
    G.incidenceTorStateClass b hb ∈ G.incidenceTorInternalPiece p q := by
  refine ⟨⟨single b 1, single_mem_supported _ _ hb⟩, ?_, rfl⟩
  apply (G.mem_incFreeTermInternalPiece_iff p q _).mpr
  intro c
  by_cases hc : c = b
  · subst hc
    rw [single_eq_same, hq, sub_self, ← Nat.cast_zero, ResolutionTools.homogeneousCoeffPiece_nat]
    exact MvPolynomial.isHomogeneous_one _ _
  · rw [single_eq_of_ne hc]
    exact Submodule.zero_mem _

/-- The Tor class of a state is nonzero. -/
theorem incidenceTorStateClass_ne_zero (b : G.IncResolutionBasis) {p : ℕ}
    (hb : G.incResolutionDegree b = p) : G.incidenceTorStateClass b hb ≠ 0 := by
  intro h
  have h' := G.incidenceTorFullState_stateClass b hb
  rw [h, map_zero] at h'
  exact one_ne_zero (single_eq_zero.mp h'.symm)

end TorSide

/-! ## The exterior class of a state -/

section ExteriorSide

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- A state basis vector of a twist lies in the state piece of the cohomological degree of the
twist. -/
theorem single_mem_stateDegreePiece {d : V → ℕ} (κ : HBasis d) {j : ℕ}
    (hj : cohomologyDegree d = j) : single κ (1 : R) ∈ stateDegreePiece R d j :=
  single_mem_supported _ _ (by simp [hj])

/-- The exterior class of one state `(S, κ)`: the class of actual cohomology `H^j` of the `q`-th
exterior bundle whose state components are `single κ 1` in the summand of `S` and zero in every
other summand. -/
def exteriorStateClass {q j : ℕ} (S : Set.powersetCard E q) (κ : HBasis (G.deg (S : Finset E)))
    (hj : cohomologyDegree (G.deg (S : Finset E)) = j) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  (G.exteriorBundleStateLinearEquiv R q j).symm
    (Pi.single S ⟨single κ 1, single_mem_stateDegreePiece R κ hj⟩)

/-- The state components of the exterior class of a state. -/
theorem exteriorBundleStateLinearEquiv_stateClass {q j : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hj : cohomologyDegree (G.deg (S : Finset E)) = j) :
    letI := G.exteriorBundleCohomologyModule R q j
    G.exteriorBundleStateLinearEquiv R q j (G.exteriorStateClass R S κ hj) =
      Pi.single S ⟨single κ 1, single_mem_stateDegreePiece R κ hj⟩ := by
  let _ := G.exteriorBundleCohomologyModule R q j
  exact LinearEquiv.apply_symm_apply _ _

/-- The state vector of the exterior class of a state is the basis vector of the state. -/
theorem exteriorCohomologyState_stateClass {q j : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hj : cohomologyDegree (G.deg (S : Finset E)) = j) :
    G.exteriorCohomologyState R q j (G.exteriorStateClass R S κ hj) = single ⟨S, κ⟩ 1 := by
  rw [exteriorCohomologyState_eq_sum, exteriorBundleStateLinearEquiv_stateClass,
    Finset.sum_eq_single S]
  · rw [Pi.single_eq_same, incStateEmbed_single]
  · intro T _ hT
    rw [Pi.single_eq_of_ne hT, Submodule.coe_zero, map_zero]
  · intro hS
    exact absurd (Finset.mem_univ S) hS

/-- The exterior class of a state is the image, under the biproduct inclusion of the summand of
`S`, of the class of the multi-twist `O(-d_S)` with state `single κ 1`. -/
theorem exteriorStateClass_eq_map_incl {q j : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hj : cohomologyDegree (G.deg (S : Finset E)) = j) :
    letI := vertexTwistStateCohomologyModule R V (G.deg (S : Finset E)) j
    G.exteriorStateClass R S κ hj =
      Sheaf.H.map (G.exteriorIncl R q S) j
        ((vertexTwistStateLinearEquiv R V (G.deg (S : Finset E)) j).symm
          ⟨single κ 1, single_mem_stateDegreePiece R κ hj⟩) := by
  let _ := G.exteriorBundleCohomologyModule R q j
  let _ := vertexTwistStateCohomologyModule R V (G.deg (S : Finset E)) j
  apply (G.exteriorBundleStateLinearEquiv R q j).injective
  rw [exteriorBundleStateLinearEquiv_stateClass]
  funext T
  rw [exteriorBundleStateLinearEquiv_apply]
  change _ = vertexTwistStateLinearEquiv R V (G.deg (T : Finset E)) j
    (Sheaf.H.map (G.exteriorProj R q T) j (Sheaf.H.map (G.exteriorIncl R q S) j
      ((vertexTwistStateLinearEquiv R V (G.deg (S : Finset E)) j).symm
        ⟨single κ 1, single_mem_stateDegreePiece R κ hj⟩)))
  rw [← Sheaf.H.map_comp_apply]
  by_cases hT : T = S
  · subst hT
    rw [Pi.single_eq_same, exteriorIncl_proj_self, Sheaf.H.map_id_apply, LinearEquiv.apply_symm_apply]
  · rw [Pi.single_eq_of_ne hT, exteriorIncl_proj_ne G R q (Ne.symm hT), sheafH_map_zero_apply, map_zero]

/-- **The specified representative in positive degree.** In cohomological degree `n + 1` the
exterior class of a state is the image, under the biproduct inclusion of the summand of `S`, of
the class of the cell cocycle `vertexTwistCellStateInclusion (single κ 1)`, whose signed tensor
coefficients are the contraction inclusion of `single κ 1`
(`vertexTwistCellStateInclusion_coefficient`). -/
theorem exteriorStateClass_succ {q n : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hj : cohomologyDegree (G.deg (S : Finset E)) = n + 1) :
    letI := vertexTwistStateCohomologyModule R V (G.deg (S : Finset E)) (n + 1)
    letI := vertexTwistCellModule R V (fun v => -(G.deg (S : Finset E) v : ℤ)) n
    G.exteriorStateClass R S κ hj =
      Sheaf.H.map (G.exteriorIncl R q S) (n + 1)
        (vertexTwistCellActualLinearEquiv R V _ n
          (QuotientAddGroup.mk (vertexTwistCellStateInclusion R V (G.deg (S : Finset E)) (n + 1)
            ⟨single κ 1, single_mem_stateDegreePiece R κ hj⟩))) := by
  let _ := vertexTwistStateCohomologyModule R V (G.deg (S : Finset E)) (n + 1)
  let _ := vertexTwistCellModule R V (fun v => -(G.deg (S : Finset E) v : ℤ)) n
  rw [exteriorStateClass_eq_map_incl, ← vertexTwistPositiveStateLinearEquiv_inverse]
  rfl

end ExteriorSide

/-! ## The acceptance tests -/

section Normalization

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- A state of a `q`-element edge set of homological degree `p` lies in cohomological degree
`q - p`. -/
theorem cohomologyDegree_deg_of_incResolutionDegree {p q : ℕ} (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    cohomologyDegree (G.deg (S : Finset E)) = q - p :=
  G.incBigraded_cohomologyDegree ⟨⟨S, κ⟩, hb, Set.powersetCard.card_eq S⟩

/-- **Acceptance test on state classes**, in every bidegree `(p, q)`. The Tor-to-exterior
isomorphism sends the Tor class of a state (the specialization of the free generator `e_b`) to the
exterior class of the same state, with coefficient `+1` and no sign. -/
theorem incidenceTorExteriorEquiv_stateClass {p q : ℕ} (h : p ≤ q) (S : Set.powersetCard E q)
    (κ : HBasis (G.deg (S : Finset E))) (hb : G.incResolutionDegree ⟨S, κ⟩ = p) :
    G.incidenceTorExteriorEquiv h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
        G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩ =
      G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb) := by
  apply G.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, exteriorCohomologyState_stateClass]
  exact G.incidenceTorFullState_stateClass _ hb

/-- **The state class test detects rescaling.** A scalar multiple `c • Φ` passes the state class
test iff `c = 1`. Applied with `c = λ^p`, the rescaled isomorphism `λ^p Φ` passes it iff
`λ^p = 1`, hence in Tor degree `p = 1` iff `λ = 1`. -/
theorem smul_incidenceTorExteriorEquiv_stateClass_eq_iff {p q : ℕ} (h : p ≤ q)
    (S : Set.powersetCard E q) (κ : HBasis (G.deg (S : Finset E)))
    (hb : G.incResolutionDegree ⟨S, κ⟩ = p) (c : ℂ) :
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    c • G.incidenceTorExteriorEquiv h ⟨G.incidenceTorStateClass ⟨S, κ⟩ hb,
        G.incidenceTorStateClass_mem ⟨S, κ⟩ hb (Set.powersetCard.card_eq S)⟩ =
      G.exteriorStateClass ℂ S κ (G.cohomologyDegree_deg_of_incResolutionDegree S κ hb) ↔
      c = 1 := by
  let _ := G.exteriorBundleCohomologyModule ℂ q (q - p)
  rw [incidenceTorExteriorEquiv_stateClass]
  constructor
  · intro hc
    have hs := congrArg (G.exteriorCohomologyState ℂ q (q - p)) hc
    rw [map_smul, exteriorCohomologyState_stateClass, smul_single, smul_eq_mul, mul_one] at hs
    simpa using congrArg (fun z => z ⟨S, κ⟩) hs
  · rintro rfl
    exact one_smul _ _

/-- **Acceptance test on the unit** (a restatement of `incidenceTorExteriorEquiv_one`): the
Tor-to-exterior isomorphism sends the Tor unit to the exterior unit. -/
theorem incidenceTorExteriorEquiv_normalization_unit :
    G.incidenceTorExteriorEquiv (le_refl 0) ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩ =
      G.exteriorCohomologyUnit ℂ :=
  G.incidenceTorExteriorEquiv_one

/-- The unique state of the empty edge set. -/
def emptyEdgeState : HBasis (G.deg ((emptyEdgeSubset : Set.powersetCard E 0) : Finset E)) :=
  fun _ => ⟨0, by simp [deg]⟩

/-- The state of the empty edge set has homological degree zero. -/
theorem incResolutionDegree_emptyEdgeState :
    G.incResolutionDegree ⟨((emptyEdgeSubset : Set.powersetCard E 0) : Finset E), G.emptyEdgeState⟩ =
      0 := by
  simp [incResolutionDegree]

/-- The twist of the empty edge set has cohomological degree zero. -/
theorem cohomologyDegree_deg_emptyEdgeSubset :
    cohomologyDegree (G.deg ((emptyEdgeSubset : Set.powersetCard E 0) : Finset E)) = 0 := by
  rw [cohomologyDegree_deg]
  simp [support]

/-- The Tor unit is the Tor class of the state of the empty edge set. -/
theorem incidenceTorOne_eq_stateClass :
    G.incidenceTorOne = G.incidenceTorStateClass _ G.incResolutionDegree_emptyEdgeState := by
  apply G.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_one, incidenceTorFullState_stateClass]
  exact G.incStateUnit_eq_single ℂ _

/-- The exterior unit is the exterior class of the state of the empty edge set. -/
theorem exteriorCohomologyUnit_eq_stateClass (R : Type) [CommRing R] [IsNoetherianRing R] :
    G.exteriorCohomologyUnit R =
      G.exteriorStateClass R emptyEdgeSubset G.emptyEdgeState G.cohomologyDegree_deg_emptyEdgeSubset := by
  apply G.exteriorCohomologyState_injective R 0 0
  rw [exteriorCohomologyState_unit, exteriorCohomologyState_stateClass]
  exact G.incStateUnit_eq_single R _

end Normalization

end
end BPFixedPoints.Multigraph
