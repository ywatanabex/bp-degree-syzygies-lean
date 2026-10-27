import BPFixedPoints.Incidence.EdgeExteriorBundleCohomology
import BPFixedPoints.Incidence.StateCohomology

/-! # Dimensions of the first page E₁ (`alg:state-dimensions`)

The first page is `E₁^{-q,j}(G) = H^j(X_G, ∧^q F_G^∨)`, formalized as the actual Ext-defined
sheaf cohomology `Sheaf.H` of the exterior bundle `exteriorBundleAbelian R q` on the product of
projective lines, with the original geometric base action `exteriorBundleCohomologyModule`.

Proved here, over every nontrivial Noetherian commutative base ring `R` (in particular over `ℂ`):
* each state summand `O(-d_S)` of `∧^q F^∨` has `H^j` of rank `wt(S)` if `j = v(S)` and rank zero
  otherwise (`exteriorSummandCohomology_finrank`); this includes the vanishing when `S` has a
  vertex of degree one, where `wt(S) = 0`;
* `H^j(∧^q F^∨)` is free and finite over `R` (`exteriorBundleCohomology_free`,
  `exteriorBundleCohomology_finite`), of rank `Σ_{|S| = q, v(S) = j} wt(S)`, the state sum
  `stateDim q j` (`exteriorBundleCohomology_finrank`);
* the rank vanishes unless `0 ≤ q - j ≤ ρ` (`exteriorBundleCohomology_finrank_eq_zero_of`), and
  outside `q ≤ |E|`, `j ≤ |V|` (`exteriorBundleCohomology_finrank_eq_zero_of_card_lt`);
* the total rank `Σ_{q,j} rank H^j(∧^q F^∨)` is `Q(G)` (`sum_exteriorBundleCohomology_finrank`).

`exteriorBundleCohomology_stateDimensions` states both displayed formulas of
`alg:state-dimensions` over `ℂ`.

The ranks come from the linear splitting of the cohomology of the exterior bundle into its
summands (`exteriorBundleCohomologyLinearEquiv`) and the summand ranks
(`vertexTwistCohomology_finrank`). Nothing here concerns the product structure of `E₁` or the
hypercohomology spectral sequence of which it is the first page.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory TopologicalSpace ProjectiveLine SchemeTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V E : Type} [DecidableEq V] [Fintype V] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

noncomputable local instance exteriorStateDimensionsHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable [IsNoetherianRing R]

omit [Fintype E] in
/-- **State cohomology of one summand (`alg:state-cohomology`).** Over a nontrivial Noetherian
base, the summand `O(-d_S)` of `∧^q F^∨` indexed by a `q`-element edge set `S` has `H^j` of rank
`wt(S) = ∏_v φ(d_S(v))` when `j = v(S)`, and of rank zero otherwise. When `S` has a vertex of
degree one, `wt(S) = 0`, so all its cohomology has rank zero. -/
theorem exteriorSummandCohomology_finrank [Nontrivial R] {q : ℕ} (S : Set.powersetCard E q)
    (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V (G.deg S) j
    Module.finrank R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) j) =
      if (G.support S).card = j then G.wt phi S else 0 := by
  rw [vertexTwistCohomology_finrank R V (G.deg S) j, CechProduct.cohomologyDegree_eq_card]
  rfl

/-- The actual cohomology of the exterior bundle `∧^q F^∨` is free over the base ring. -/
theorem exteriorBundleCohomology_free (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Module.Free R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) := by
  let _ := G.exteriorBundleCohomologyModule R q j
  let _ := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
  have := fun S : Set.powersetCard E q => vertexTwistCohomology_free R V (G.deg S) j
  exact Module.Free.of_equiv (G.exteriorBundleCohomologyLinearEquiv R q j).symm

/-- The actual cohomology of the exterior bundle `∧^q F^∨` is finite over the base ring. -/
theorem exteriorBundleCohomology_finite (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Module.Finite R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) := by
  let _ := G.exteriorBundleCohomologyModule R q j
  let _ := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
  have := fun S : Set.powersetCard E q => vertexTwistCohomology_finite R V (G.deg S) j
  exact Module.Finite.equiv (G.exteriorBundleCohomologyLinearEquiv R q j).symm

/-- A sum over the `q`-element edge sets is the filtered sum over all edge sets. -/
theorem sum_powersetCard_eq_sum_filter {M : Type*} [AddCommMonoid M] (q : ℕ)
    (f : Finset E → M) :
    ∑ S : Set.powersetCard E q, f S = ∑ S ∈ Finset.univ.filter fun S : Finset E => S.card = q,
      f S :=
  (Finset.sum_subtype _ (fun S => by simp) f).symm

/-- **`alg:state-dimensions` (dimension formula).** Over a nontrivial Noetherian base, the rank
of `E₁^{-q,j}(G) = H^j(X_G, ∧^q F_G^∨)` is `Σ_{|S| = q, v(S) = j} wt(S)`. -/
theorem exteriorBundleCohomology_finrank [Nontrivial R] (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Module.finrank R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) = G.stateDim q j := by
  let _ := G.exteriorBundleCohomologyModule R q j
  let _ := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
  have := fun S : Set.powersetCard E q => vertexTwistCohomology_free R V (G.deg S) j
  have := fun S : Set.powersetCard E q => vertexTwistCohomology_finite R V (G.deg S) j
  rw [(G.exteriorBundleCohomologyLinearEquiv R q j).finrank_eq, Module.finrank_pi_fintype]
  rw [Finset.sum_congr rfl fun S _ => G.exteriorSummandCohomology_finrank R S j]
  rw [sum_powersetCard_eq_sum_filter q
    (fun S => if (G.support S).card = j then G.wt phi S else 0), ← Finset.sum_filter,
    Finset.filter_filter]
  rfl

/-- The rank of `E₁^{-q,j}(G)` vanishes when `q > |E|` or `j > |V|`. -/
theorem exteriorBundleCohomology_finrank_eq_zero_of_card_lt [Nontrivial R] {q j : ℕ}
    (h : Fintype.card E < q ∨ Fintype.card V < j) :
    letI := G.exteriorBundleCohomologyModule R q j
    Module.finrank R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) = 0 := by
  rw [G.exteriorBundleCohomology_finrank R q j]
  refine Finset.sum_eq_zero fun S hS => ?_
  rw [Finset.mem_filter] at hS
  have hE := Finset.card_le_univ S
  have hV := Finset.card_le_univ (G.support S)
  omega

variable [DecidableEq E]

/-- The rank of `E₁^{-q,j}(G)` vanishes unless `0 ≤ q - j ≤ ρ`. -/
theorem exteriorBundleCohomology_finrank_eq_zero_of [Nontrivial R] {q j : ℕ}
    (h : q < j ∨ G.rho < q - j) :
    letI := G.exteriorBundleCohomologyModule R q j
    Module.finrank R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) = 0 := by
  rw [G.exteriorBundleCohomology_finrank R q j]
  exact G.stateDim_eq_zero_of h

/-- **`alg:state-dimensions` (total).** Over a nontrivial Noetherian base, the ranks of all
`E₁^{-q,j}(G) = H^j(X_G, ∧^q F_G^∨)` add up to `Q(G)`. The ranges `q ≤ |E|` and `j ≤ |V|`
contain every nonzero term (`exteriorBundleCohomology_finrank_eq_zero_of_card_lt`). -/
theorem sum_exteriorBundleCohomology_finrank [Nontrivial R] :
    ∑ q ∈ Finset.range (Fintype.card E + 1), ∑ j ∈ Finset.range (Fintype.card V + 1),
      (letI := G.exteriorBundleCohomologyModule R q j
       Module.finrank R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j)) = G.Q := by
  rw [← G.sum_stateDim_eq_Q]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ =>
    G.exteriorBundleCohomology_finrank R q j

/-- **`alg:state-dimensions`** over `ℂ`, as displayed in the paper:
`dim E₁^{-q,j}(G) = Σ_{|S| = q, v(S) = j} wt(S)` for all `q, j`, where
`E₁^{-q,j}(G) = H^j(X_G, ∧^q F_G^∨)`, and `Σ_{q,j} dim E₁^{-q,j}(G) = Q(G)`. -/
theorem exteriorBundleCohomology_stateDimensions :
    (∀ q j : ℕ,
      (letI := G.exteriorBundleCohomologyModule ℂ q j
       Module.finrank ℂ (Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j)) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset E => S.card = q ∧ (G.support S).card = j),
          G.wt phi S) ∧
    ∑ q ∈ Finset.range (Fintype.card E + 1), ∑ j ∈ Finset.range (Fintype.card V + 1),
      (letI := G.exteriorBundleCohomologyModule ℂ q j
       Module.finrank ℂ (Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j)) = G.Q :=
  ⟨G.exteriorBundleCohomology_finrank ℂ, G.sum_exteriorBundleCohomology_finrank ℂ⟩

end BPFixedPoints.Multigraph
