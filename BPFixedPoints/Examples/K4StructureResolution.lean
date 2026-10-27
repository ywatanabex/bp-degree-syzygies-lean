import BPFixedPoints.Incidence.IncidenceTorVanishing
import BPFixedPoints.Examples.PaperTables

/-! # The graded shape of the minimal resolution of 𝒰_{K₄} (`alg:k4-resolution`)

The paper displays the minimal free resolution of the incidence ring of K₄ as
`0 → S(-6)^16 → S(-5)^24 → S ⊕ S(-3)^4 ⊕ S(-4)^3 → 𝒰_{K₄} → 0`. Read off with the shift
`S(-q)` in homological degree `p`, its graded Betti numbers are `β_{0,0} = 1`, `β_{0,3} = 4`,
`β_{0,4} = 3`, `β_{1,5} = 24`, `β_{2,6} = 16`, and all others vanish (`K4GradedBetti`).

Proved here, for the chart-intersection incidence ring of `Examples.K4`:
* the full state-sum table: `K4.betti p q = K4GradedBetti p q` for all `p, q` (`K4_betti_eq`);
* the actual internal-degree-`q` pieces of `Tor_p` over the coefficient origin have exactly these
  dimensions, and are zero at all other bidegrees (`K4_finrank_incidenceTorInternalPiece`,
  `K4_incidenceTorInternalPiece_eq_bot`, `K4_graded_betti`);
* the free terms of the actual resolution `IncFreeTerm p` have exactly `β_{p,q}` basis elements
  of internal degree `q` (`K4_card_incBigradedBasis`), ranks 8, 24, 16 over the coefficient ring
  `S`, and rank zero for `p ≥ 3`, where `Tor_p` vanishes (`K4_free_terms`,
  `K4_incidenceTor_subsingleton`).

The minimality of the resolution, its natural grading and exactness are the general results
(`incFreeResolution`, `NaturalGradedResolution`); nothing K₄-specific is needed beyond the
numerical table, which is computed by kernel-checked `decide`. Not covered: explicit matrices
of the K₄ differentials, and a comparison of the free terms with the twisted modules `S(-q)` as
graded modules beyond the basis count by internal degree.
-/

set_option maxRecDepth 20000

namespace BPFixedPoints.Examples

open Multigraph

/-- The graded Betti table of `alg:k4-resolution`: `β_{0,0} = 1`, `β_{0,3} = 4`, `β_{0,4} = 3`,
`β_{1,5} = 24`, `β_{2,6} = 16`, and zero at every other bidegree `(p, q)` (homological degree
`p`, shift `S(-q)`). -/
def K4GradedBetti (p q : ℕ) : ℕ :=
  if p = 0 ∧ q = 0 then 1 else if p = 0 ∧ q = 3 then 4 else if p = 0 ∧ q = 4 then 3
  else if p = 1 ∧ q = 5 then 24 else if p = 2 ∧ q = 6 then 16 else 0

/-- The bidegrees at which `K4GradedBetti` is nonzero. -/
def K4BettiSupport : Finset (ℕ × ℕ) := {(0, 0), (0, 3), (0, 4), (1, 5), (2, 6)}

/-- `K4GradedBetti` vanishes exactly off its support. -/
theorem K4GradedBetti_eq_zero_iff (p q : ℕ) :
    K4GradedBetti p q = 0 ↔ (p, q) ∉ K4BettiSupport := by
  unfold K4GradedBetti K4BettiSupport
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The state-sum table of K₄ for `p ≤ 2` and `q ≤ 6`, by `decide`. -/
theorem K4_betti_eq_of_lt : ∀ p : Fin 3, ∀ q : Fin 7, K4.betti p q = K4GradedBetti p q := by
  decide

/-- **The numerical graded Betti table of K₄.** For all `p, q`, the state sum
`β_{p,q} = Σ_{|S| = q, |S| - v(S) = p} wt(S)` is `K4GradedBetti p q`. -/
theorem K4_betti_eq (p q : ℕ) : K4.betti p q = K4GradedBetti p q := by
  by_cases hp : p < 3
  · by_cases hq : q < 7
    · exact K4_betti_eq_of_lt ⟨p, hp⟩ ⟨q, hq⟩
    · rw [(K4GradedBetti_eq_zero_iff p q).2 (by
        simp only [K4BettiSupport, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        omega)]
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [Finset.mem_filter] at hS
      have := S.card_le_univ
      simp only [Fintype.card_fin] at this
      omega
  · rw [(K4GradedBetti_eq_zero_iff p q).2 (by
      simp only [K4BettiSupport, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      omega)]
    exact K4.betti_eq_zero_of_rho_lt (by rw [K4_rho]; omega) q

/-- **`alg:k4-resolution` (actual Tor).** The internal-degree-`q` piece of the actual
`Tor_p^{S}(𝒰_{K₄}, ℂ)` at the coefficient origin has dimension `K4GradedBetti p q`. -/
theorem K4_finrank_incidenceTorInternalPiece (p q : ℕ) :
    Module.finrank ℂ (K4.incidenceTorInternalPiece p q) = K4GradedBetti p q := by
  rw [K4.finrank_incidenceTorInternalPiece, K4_betti_eq]

/-- The resolution basis of K₄ has exactly `K4GradedBetti p q` generators in homological degree
`p` with shift `q`: the free term `F_p` is `⊕_q S(-q)^{K4GradedBetti p q}`. -/
theorem K4_card_incBigradedBasis (p q : ℕ) :
    Fintype.card (K4.IncBigradedBasis p q) = K4GradedBetti p q := by
  rw [K4.card_incBigradedBasis, K4_betti_eq]

/-- Off the five bidegrees of `alg:k4-resolution`, the internal Tor piece of K₄ is zero. -/
theorem K4_incidenceTorInternalPiece_eq_bot {p q : ℕ} (h : (p, q) ∉ K4BettiSupport) :
    K4.incidenceTorInternalPiece p q = ⊥ := by
  have hcard : Fintype.card (K4.IncBigradedBasis p q) = 0 := by
    rw [K4_card_incBigradedBasis, (K4GradedBetti_eq_zero_iff p q).2 h]
  have : IsEmpty (K4.IncBigradedBasis p q) := Fintype.card_eq_zero_iff.mp hcard
  have : Subsingleton (K4.incidenceTorInternalPiece p q) :=
    (K4.incidenceTorInternalEquivState p q).toEquiv.subsingleton
  exact Submodule.eq_bot_of_subsingleton

/-- **`alg:k4-resolution` (graded shape).** The nonzero graded Betti numbers of the incidence
ring of K₄, as dimensions of the internal pieces of actual Tor at the coefficient origin, are
exactly `β_{0,0} = 1`, `β_{0,3} = 4`, `β_{0,4} = 3`, `β_{1,5} = 24`, `β_{2,6} = 16`; every other
internal piece is zero. -/
theorem K4_graded_betti :
    (Module.finrank ℂ (K4.incidenceTorInternalPiece 0 0),
        Module.finrank ℂ (K4.incidenceTorInternalPiece 0 3),
        Module.finrank ℂ (K4.incidenceTorInternalPiece 0 4),
        Module.finrank ℂ (K4.incidenceTorInternalPiece 1 5),
        Module.finrank ℂ (K4.incidenceTorInternalPiece 2 6)) = (1, 4, 3, 24, 16) ∧
      ∀ p q : ℕ, (p, q) ∉ ({(0, 0), (0, 3), (0, 4), (1, 5), (2, 6)} : Finset (ℕ × ℕ)) →
        K4.incidenceTorInternalPiece p q = ⊥ := by
  refine ⟨?_, fun p q h => K4_incidenceTorInternalPiece_eq_bot h⟩
  simp only [K4_finrank_incidenceTorInternalPiece]
  decide

/-- The free terms of the actual resolution of K₄: `F_p` has `β_{p,q}` generators of shift `q`,
and its rank over the coefficient ring is 8, 24, 16 for `p = 0, 1, 2` and zero for `p ≥ 3`. -/
theorem K4_free_terms :
    (∀ p q, Fintype.card (K4.IncBigradedBasis p q) = K4GradedBetti p q) ∧
      ∀ p, Module.finrank (IncCoeffRing (Fin 6)) (K4.IncFreeTerm p) =
        if p = 0 then 8 else if p = 1 then 24 else if p = 2 then 16 else 0 := by
  refine ⟨K4_card_incBigradedBasis, fun p => ?_⟩
  rw [Module.finrank_eq_card_basis (K4.incFreeTermBasis p), K4.card_incHomologicalBasis]
  simp only [K4_betti_eq, Fintype.card_fin]
  rcases Nat.lt_or_ge p 3 with hp | hp
  · interval_cases p <;> decide
  · have h0 : p ≠ 0 := by omega
    have h1 : p ≠ 1 := by omega
    have h2 : p ≠ 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    refine Finset.sum_eq_zero fun q _ => (K4GradedBetti_eq_zero_iff p q).2 ?_
    simp only [K4BettiSupport, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega

/-- The actual `Tor_p` of K₄ at the coefficient origin vanishes for `p ≥ 3`: the resolution has
length `ρ = 2`. -/
theorem K4_incidenceTor_subsingleton {p : ℕ} (hp : 3 ≤ p) : Subsingleton (K4.incidenceTor p) := by
  have : IsEmpty {b : K4.IncResolutionBasis // K4.incResolutionDegree b = p} := by
    rw [← Fintype.card_eq_zero_iff, K4.card_incHomologicalBasis]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [K4_betti_eq, K4GradedBetti_eq_zero_iff]
    simp only [K4BettiSupport, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  exact (K4.incidenceTorEquivState p).toEquiv.subsingleton

end BPFixedPoints.Examples
