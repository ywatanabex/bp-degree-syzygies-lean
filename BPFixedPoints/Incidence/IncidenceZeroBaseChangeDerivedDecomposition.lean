import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedTor

/-! # The cohomology of `Q(C₀)` is the sum of the bidegree pieces

`IncidenceZeroBaseChangeDerivedTor` embeds each bidegree piece `ZbcCohomology p q` (cohomology of
the base-changed model in homological degree `p` and internal degree `q`) into the cohomology in
degree `-p` of the model and of `Q(C₀)`. This file proves that these pieces exhaust it and are
independent, so the cohomology of `C₀` is computed by the bidegree pieces, i.e. by sheaf
cohomology.

* `zbdCardFilter_sum`: the exterior-degree projections `zbdCardFilter q`, `q ≤ |E|`, sum to the
  identity; they commute with the Čech differential (`zbdCardFilter_d`) and kill the other
  exterior degrees (`zbdCardFilter_of_mem_ne`).
* `zbdCohomologySum_surjective`: every class of the model in degree `-p` is the sum of the
  classes of the exterior-degree parts of a representing cycle (`zbdCyclePart`).
* `zbdCohomologySum_injective`: if a sum of bidegree classes vanishes, each term bounds in its
  own bidegree (project a primitive with `zbdCardFilter`).
* `zbdModelCohomologyEquiv` and `zbdDerivedCohomologyEquiv`:
  `∏_{q ≤ |E|} ZbcCohomology p q ≃ H^{-p}(model) ≃ H^{-p}(Q(C₀))`; on the factor `q` it is the
  inclusion `zbdCohomologyToDerived` of the acceptance test (`zbdDerivedCohomologyEquiv_single`).
  The factors with `q < p` vanish (`zbdPiece_eq_bot_of_lt`, `zbdCohomology_subsingleton_of_lt`), and
  for `p ≤ q` the factor is `H^{q-p}(X_G, ∧^q F_G^∨)` by `zbcSheafEquiv`.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CechProduct ProjectiveLine IncidencePerturbation Finsupp ResolutionTools

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- The exterior-degree projections sum to the identity. -/
theorem zbdCardFilter_sum (x : ZbcModule V E) :
    ∑ q : Fin (Fintype.card E + 1), zbdCardFilter (q : ℕ) x = x := by
  ext S : 1
  rw [Finsupp.finsetSum_apply]
  simp only [zbdCardFilter_apply]
  rw [Finset.sum_eq_single ⟨S.card, Nat.lt_succ_of_le (Finset.card_le_univ S)⟩]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
  · intro b _ hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hb (Fin.ext h.symm))]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The exterior-degree projection kills the other exterior degrees. -/
theorem zbdCardFilter_of_mem_ne {p q q' : ℕ} {z : ZbcModule V E} (hz : z ∈ zbcPiece V E p q)
    (hq : q ≠ q') : zbdCardFilter q' z = 0 := by
  ext S : 1
  rw [zbdCardFilter_apply, Finsupp.zero_apply]
  split_ifs with hS
  · exact ((mem_zbcSlot_iff p q S (z S)).mp (hz S)).2 (fun h => hq (h.symm.trans hS))
  · rfl

/-- The exterior-degree projection of a chain of total degree `n` has bidegree `(n, q)`. -/
theorem zbdCardFilter_mem_piece {n q : ℕ} {y : ZbcModule V E}
    (hy : y ∈ zbdModelPiece V E (n : ℤ)) : zbdCardFilter q y ∈ zbcPiece V E n q := by
  intro S
  rw [mem_zbcSlot_iff, zbdCardFilter_apply]
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hS)]
    have h := hy S
    rw [zbdSlot, hS] at h
    exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hS)]

@[reducible] local instance zbdCohomologyAddCommGroup (p q : ℕ) :
    AddCommGroup (G.ZbcCohomology p q) := inferInstance

@[reducible] local instance zbdCohomologyModule (p q : ℕ) : Module ℂ (G.ZbcCohomology p q) :=
  inferInstance

/-- The sum of the bidegree classes in the cohomology of the model in degree `-p`. -/
def zbdCohomologySum (p : ℕ) :
    ((q : Fin (Fintype.card E + 1)) → G.ZbcCohomology p q) →ₗ[ℂ]
      G.zbdModelComplex.homology (-(p : ℤ)) :=
  ∑ q : Fin (Fintype.card E + 1), G.zbdCohomologyToModel p q ∘ₗ LinearMap.proj q

theorem zbdCohomologySum_apply (p : ℕ)
    (c : (q : Fin (Fintype.card E + 1)) → G.ZbcCohomology p q) :
    G.zbdCohomologySum p c = ∑ q : Fin (Fintype.card E + 1), G.zbdCohomologyToModel p q (c q) := by
  rw [zbdCohomologySum, LinearMap.sum_apply]
  rfl

/-- The underlying chain of a cycle of the model in degree `-p` has total degree `p`. -/
theorem zbd_iCycles_mem (p : ℕ) (w : G.zbdModelComplex.cycles (-(p : ℤ))) :
    Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ))))) (G.zbdModelComplex.iCycles _ w) ∈
      zbdModelPiece V E (p : ℤ) := by
  have h := Subtype.property (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
    (G.zbdModelComplex.iCycles _ w)
  generalize Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
    (G.zbdModelComplex.iCycles _ w) = x at h ⊢
  rwa [neg_neg] at h

/-- The underlying chain of a cycle of the model is a Čech cycle. -/
theorem zbd_iCycles_d (p : ℕ) (w : G.zbdModelComplex.cycles (-(p : ℤ))) :
    G.zbcContraction.d (Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
      (G.zbdModelComplex.iCycles _ w)) = 0 := by
  have h := congrArg (Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ) + 1)))))
    (congrArg (fun φ => φ w) (G.zbdModelComplex.iCycles_d (-(p : ℤ)) (-(p : ℤ) + 1)))
  rw [ConcreteCategory.comp_apply, ZbdGradedComplex.complex_d_val _ rfl] at h
  exact h

/-- The bidegree `(p, q)` part of a cycle of the model in degree `-p`. -/
def zbdCyclePart (p : ℕ) (w : G.zbdModelComplex.cycles (-(p : ℤ))) (q : ℕ) : G.zbcCycles p q :=
  ⟨zbdCardFilter q (Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
      (G.zbdModelComplex.iCycles _ w)),
    zbdCardFilter_mem_piece (G.zbd_iCycles_mem p w), LinearMap.mem_ker.mpr (by
      rw [zbdCardFilter_d, G.zbd_iCycles_d p w, map_zero])⟩

theorem zbdCyclePart_val (p : ℕ) (w : G.zbdModelComplex.cycles (-(p : ℤ))) (q : ℕ) :
    (G.zbdCyclePart p w q).val = zbdCardFilter q (Subtype.val
      (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ))))) (G.zbdModelComplex.iCycles _ w)) := rfl

theorem zbdCyclesClass_apply (p q : ℕ) (z : G.zbcCycles p q) :
    G.zbdCyclesClass p q z = G.zbdModelComplex.homologyπ _
      (G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q) z) :=
  rfl

theorem zbd_iCycles_liftCycles (p q : ℕ) (z : G.zbcCycles p q) :
    G.zbdModelComplex.iCycles _
      (G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q) z) =
      G.zbdCyclesToModel p q z :=
  ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i G.zbdModelComplex
    (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q)) z

/-- **The bidegree classes span the cohomology of the model in degree `-p`.** -/
theorem zbdCohomologySum_surjective (p : ℕ) : Function.Surjective (G.zbdCohomologySum p) := by
  intro c
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective (G.zbdModelComplex.homologyπ (-(p : ℤ)))).mp
    inferInstance c
  refine ⟨fun q => G.zbcClass p q (G.zbdCyclePart p w q), ?_⟩
  rw [zbdCohomologySum_apply]
  simp only [zbdCohomologyToModel_class]
  rw [Finset.sum_congr rfl (fun (q : Fin (Fintype.card E + 1)) _ =>
      G.zbdCyclesClass_apply p q (G.zbdCyclePart p w q)),
    ← map_sum]
  congr 1
  apply (ModuleCat.mono_iff_injective (G.zbdModelComplex.iCycles (-(p : ℤ)))).mp inferInstance
  rw [map_sum, Finset.sum_congr rfl (fun (q : Fin (Fintype.card E + 1)) _ =>
      G.zbd_iCycles_liftCycles p q (G.zbdCyclePart p w q))]
  apply Subtype.ext
  refine (Submodule.coe_sum (zbdModelPiece V E (-(-(p : ℤ))))
    (fun q : Fin (Fintype.card E + 1) =>
      (G.zbdCyclesToModel p q (G.zbdCyclePart p w q) : zbdModelPiece V E (-(-(p : ℤ)))))
    Finset.univ).trans ?_
  refine (Finset.sum_congr rfl (fun (q : Fin (Fintype.card E + 1)) _ =>
    (G.zbdCyclesToModel_val p q (G.zbdCyclePart p w q)).trans
      (G.zbdCyclePart_val p w q))).trans ?_
  exact zbdCardFilter_sum _

/-- On a family of cycles of the various exterior degrees, the projection to exterior degree `q`
picks the cycle of degree `q`. -/
theorem zbdCardFilter_sum_cycles (p : ℕ)
    (z : (q : Fin (Fintype.card E + 1)) → G.zbcCycles p q) (q : Fin (Fintype.card E + 1)) :
    zbdCardFilter q (∑ q' : Fin (Fintype.card E + 1), (z q').val) = (z q).val := by
  rw [map_sum, Finset.sum_eq_single q]
  · exact zbdCardFilter_of_mem (z q).2.1
  · intro b _ hb
    exact zbdCardFilter_of_mem_ne (z b).2.1 (fun h => hb (Fin.ext h))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The bidegree classes are independent in the cohomology of the model in degree `-p`.** -/
theorem zbdCohomologySum_injective (p : ℕ) : Function.Injective (G.zbdCohomologySum p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  choose z hz using fun q : Fin (Fintype.card E + 1) => G.zbcClass_surjective p q (c q)
  have hc' : G.zbdModelComplex.homologyπ _ (∑ q : Fin (Fintype.card E + 1),
      G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q)
        (z q)) = 0 := by
    rw [map_sum, ← hc, zbdCohomologySum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← hz q, zbdCohomologyToModel_class, zbdCyclesClass_apply]
  obtain ⟨j, y, hy⟩ := zbd_exists_boundary_of_homologyπ_eq_zero _ _ hc'
  have hsum : Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))
      (G.zbdModelComplex.iCycles _ (∑ q : Fin (Fintype.card E + 1),
        G.zbdModelComplex.liftCycles (G.zbdCyclesToModel p q) _ rfl (G.zbdCyclesToModel_d p q)
          (z q))) = ∑ q : Fin (Fintype.card E + 1), (z q).val := by
    rw [map_sum, Finset.sum_congr rfl (fun (q : Fin (Fintype.card E + 1)) _ =>
      G.zbd_iCycles_liftCycles p q (z q))]
    exact (Submodule.coe_sum (zbdModelPiece V E (-(-(p : ℤ))))
      (fun q : Fin (Fintype.card E + 1) =>
        (G.zbdCyclesToModel p q (z q) : zbdModelPiece V E (-(-(p : ℤ))))) Finset.univ).trans
      (Finset.sum_congr rfl (fun (q : Fin (Fintype.card E + 1)) _ =>
        G.zbdCyclesToModel_val p q (z q)))
  have h1 := congrArg (Subtype.val (p := (· ∈ zbdModelPiece V E (-(-(p : ℤ)))))) hy
  rw [hsum] at h1
  funext q
  rw [← hz q, Pi.zero_apply, zbcClass_eq_zero_iff]
  by_cases hj : j + 1 = -(p : ℤ)
  · rw [ZbdGradedComplex.complex_d_val _ hj] at h1
    refine ⟨zbdCardFilter q (Subtype.val (p := (· ∈ zbdModelPiece V E (-j))) y),
      zbdCardFilter_mem ?_, ?_⟩
    · have h2 := (Subtype.property (p := (· ∈ zbdModelPiece V E (-j))) y)
      generalize Subtype.val (p := (· ∈ zbdModelPiece V E (-j))) y = w at h2 ⊢
      rwa [show -j = ((p + 1 : ℕ) : ℤ) by push_cast; omega] at h2
    · rw [zbdCardFilter_d, h1, zbdCardFilter_sum_cycles]
  · rw [G.zbdModelComplex.shape j _ hj] at h1
    have h2 : ∑ q' : Fin (Fintype.card E + 1), (z q').val = 0 := h1.symm
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [map_zero, ← G.zbdCardFilter_sum_cycles p z q, h2, map_zero]

/-- **The cohomology of the model in degree `-p` is the product of the bidegree pieces**
`ZbcCohomology p q`, `q ≤ |E|`. -/
def zbdModelCohomologyEquiv (p : ℕ) :
    ((q : Fin (Fintype.card E + 1)) → G.ZbcCohomology p q) ≃ₗ[ℂ]
      G.zbdModelComplex.homology (-(p : ℤ)) :=
  LinearEquiv.ofBijective (G.zbdCohomologySum p)
    ⟨G.zbdCohomologySum_injective p, G.zbdCohomologySum_surjective p⟩

/-- The pieces of bidegree `(p, q)` with `q < p` vanish: their Čech degree `q - p` is negative. -/
theorem zbdPiece_eq_bot_of_lt {p q : ℕ} (h : q < p) : zbcPiece V E p q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  ext S : 1
  have hS := (mem_zbcSlot_iff p q S (z S)).mp (hz S)
  rw [Finsupp.zero_apply]
  by_cases hc : S.card = q
  · ext b
    rw [Finsupp.zero_apply]
    apply (mem_supported' ℂ _).mp (hS.1 hc) b
    change ¬ ((cechDegree b : ℤ) = (q : ℤ) - p)
    omega
  · exact hS.2 hc

theorem zbdCohomology_subsingleton_of_lt {p q : ℕ} (h : q < p) :
    Subsingleton (G.ZbcCohomology p q) := by
  have hz : ∀ z : G.zbcCycles p q, z = 0 := fun z => by
    apply Subtype.ext
    have h1 : z.val ∈ zbcPiece V E p q := z.2.1
    rw [zbdPiece_eq_bot_of_lt h, Submodule.mem_bot] at h1
    exact h1
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, rfl⟩ := G.zbcClass_surjective p q a
  obtain ⟨z', rfl⟩ := G.zbcClass_surjective p q b
  rw [hz z, hz z']

section Derived

universe w

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℂ)]

/-- **The cohomology of `Q(C₀)` in degree `-p`** is the product over the internal degrees
`q ≤ |E|` of the bidegree pieces `ZbcCohomology p q`; these vanish for `q < p`
(`zbdCohomology_subsingleton_of_lt`) and are `H^{q-p}(X_G, ∧^q F_G^∨)` for `p ≤ q`
(`zbcSheafEquiv`). -/
def zbdDerivedCohomologyEquiv (p : ℕ) :
    ((q : Fin (Fintype.card E + 1)) → G.ZbcCohomology p q) ≃ₗ[ℂ]
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).obj
        (DerivedCategory.Q.obj G.zbdTotalComplexC) :=
  (G.zbdModelCohomologyEquiv p).trans
    ((((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).app
      G.zbdModelComplex).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).mapIso
        (DerivedCategory.Q.mapIso G.zbdModelIso.symm)).toLinearEquiv)

/-- On the piece of internal degree `q`, the decomposition is the inclusion
`zbdCohomologyToDerived` used by the acceptance test. -/
theorem zbdDerivedCohomologyEquiv_single (p : ℕ) (q : Fin (Fintype.card E + 1))
    (c : G.ZbcCohomology p q) :
    G.zbdDerivedCohomologyEquiv p (Pi.single q c) = G.zbdCohomologyToDerived p q c := by
  have hsum : G.zbdCohomologySum p (Pi.single q c) = G.zbdCohomologyToModel p q c := by
    rw [zbdCohomologySum_apply, Finset.sum_eq_single q]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  change ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-(p : ℤ))).map
    (DerivedCategory.Q.map G.zbdModelIso.inv))
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{0} ℂ) (-(p : ℤ))).inv.app
        G.zbdModelComplex) (G.zbdCohomologySum p (Pi.single q c))) = _
  rw [hsum]
  rfl

end Derived

end

end BPFixedPoints.Multigraph
