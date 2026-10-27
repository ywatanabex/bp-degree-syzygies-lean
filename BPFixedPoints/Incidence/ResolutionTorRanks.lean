import BPFixedPoints.Incidence.ResolutionTor

/-! # Actual Tor dimensions and the state-sum Betti table -/

namespace BPFixedPoints.ResolutionTools

/-- Partition a finite basis by a bounded natural-number weight. -/
theorem sum_card_weight_fibres {I : Type*} [Fintype I] (w : I → ℕ)
    (N : ℕ) (hN : ∀ i, w i ≤ N) :
    ∑ q ∈ Finset.range (N + 1), Fintype.card {i : I // w i = q} = Fintype.card I := by
  classical
  simp_rw [Fintype.card_subtype]
  simpa only [Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := w)
      (t := Finset.range (N + 1))
      (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN i)))).symm

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The ranks in a homological row are the sums of the bigraded state counts. -/
theorem card_incHomologicalBasis (p : ℕ) :
    Fintype.card {b : G.IncResolutionBasis // G.incResolutionDegree b = p} =
      ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti p q := by
  classical
  let B := {b : G.IncResolutionBasis // G.incResolutionDegree b = p}
  calc Fintype.card B =
      ∑ q ∈ Finset.range (Fintype.card E + 1),
        Fintype.card {b : B // G.incResolutionInternalDegree b.val = q} :=
      (sum_card_weight_fibres (fun b : B => G.incResolutionInternalDegree b.val)
        (Fintype.card E) (fun b => G.incResolutionInternalDegree_le b.val)).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [← G.card_incBigradedBasis p q]
      apply Fintype.card_congr
      exact
        { toFun := fun b => ⟨b.val.val, b.val.property, b.property⟩
          invFun := fun b => ⟨⟨b.val, b.property.1⟩, b.property.2⟩
          left_inv := fun b => rfl
          right_inv := fun b => rfl }

/-- Dimensions of the actual derived tensor product, with no dimension
formula built into the definition of the Tor space. -/
theorem finrank_incidenceTor (p : ℕ) :
    Module.finrank ℂ (G.incidenceTor p) =
      ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti p q := by
  rw [← G.card_incHomologicalBasis p]
  exact (G.incidenceTorEquivState p).finrank_eq.trans
    (Module.finrank_eq_card_basis (Finsupp.basisSingleOne))

/-- The total Betti number of the actual incidence module is Q(G). -/
theorem sum_finrank_incidenceTor :
    ∑ p ∈ Finset.range (Fintype.card E + 1),
      Module.finrank ℂ (G.incidenceTor p) = G.Q := by
  simp_rw [G.finrank_incidenceTor]
  exact G.sum_betti_eq_Q

end BPFixedPoints.Multigraph
