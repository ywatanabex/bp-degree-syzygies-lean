import BPFixedPoints.Degree.Generic.Count

/-!
# Fixed-parameter weak coupling: generic fibers on a line

For fixed c_e≠0, β_i≠0,−1, write the auxiliary system along s_e=1+εc_e as
`lineAux` over K[ε]. The map K[ε]→L, ε↦t, to a Puiseux-type field is injective.
Its fiber has exactly Q(G) simple solutions by `card_puiseuxSolutions`.
Apply `generic_fiber_constancy` over K[ε] to obtain nonzero g∈K[ε] such that
all ε∈K with g(ε)≠0 have exactly Q(G) simple solutions (`exists_line_generic`).
Its nonzero roots are finite; over ℂ this gives all sufficiently small ε≠0
(`card_weak_coupling_eq_Q`). This algebraic argument proves the upper bound
as well as existence, without analysis. Branch convergence as ε→0 is proved
by the implicit function theorem in `WeakCouplingBranches.lean`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Line

variable {K : Type*} [Field K] (c : E → K) (β : V → K)

/-- Line specialization ℤ[s,β]→K[ε], sending s_e to 1+ε c_e and fixing β_i. -/
noncomputable def lineParam : ParamRing E V →+* Polynomial K :=
  eval₂Hom (Int.castRingHom _)
    (Sum.elim (fun e => 1 + Polynomial.X * Polynomial.C (c e)) fun i => Polynomial.C (β i))

/-- Auxiliary system on the line, over K[ε]. -/
noncomputable def lineAux : Var V E → MvPolynomial (Var V E) (Polynomial K) :=
  fun v => map (lineParam c β) (G.genericAux v)

/-- Denominator on the line. -/
noncomputable def lineDen : MvPolynomial (Var V E) (Polynomial K) :=
  map (lineParam c β) (auxDen V E)

/-- Solutions of the line system over θ:K[ε]→κ correspond to generic-system solutions over θ composed with lineParam. -/
def lineSolEquiv {κ : Type*} [Field κ] (θ : Polynomial K →+* κ) :
    SystemSolutions (G.lineAux c β) (lineDen c β) θ ≃
      SystemSolutions G.genericAux (auxDen V E) (θ.comp (lineParam c β)) :=
  Equiv.subtypeEquivRight fun y => by simp only [lineAux, lineDen, map_map]

theorem isSimpleAt_line_iff {κ : Type*} [Field κ] (θ : Polynomial K →+* κ) (y : Var V E → κ) :
    IsSimpleAt (G.lineAux c β) θ y ↔ IsSimpleAt G.genericAux (θ.comp (lineParam c β)) y := by
  simp only [IsSimpleAt, lineAux, map_map]

theorem evalRingHom_comp_lineParam_sGen (ε : K) :
    (Polynomial.evalRingHom ε).comp (lineParam c β) ∘ sGen = fun e => 1 + ε * c e := by
  funext e
  simp only [lineParam, sGen, Function.comp, RingHom.comp_apply, eval₂Hom_X', Sum.elim_inl,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C]

theorem evalRingHom_comp_lineParam_βGen (ε : K) :
    (Polynomial.evalRingHom ε).comp (lineParam c β) ∘ βGen = β := by
  funext i
  simp [lineParam, βGen]

variable [DecidableEq K] (P : PuiseuxField K)

/-- K[ε] → K⟦t⟧ → L、ε ↦ t。 -/
noncomputable def lineToL : Polynomial K →+* P.L :=
  P.ofPS.comp Polynomial.coeToPowerSeries.ringHom

theorem lineToL_injective : Function.Injective (lineToL P) := fun _ _ h =>
  Polynomial.coe_injective _ (P.ofPS_injective h)

theorem lineToL_comp_sGen : (lineToL P).comp (lineParam c β) ∘ sGen = sP P c := by
  funext e
  simp only [lineToL, lineParam, sGen, Function.comp, RingHom.comp_apply, eval₂Hom_X',
    Sum.elim_inl, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
  exact (sP_eq P c e).symm

theorem lineToL_comp_βGen : (lineToL P).comp (lineParam c β) ∘ βGen = βP P β := by
  funext i
  simp only [lineToL, lineParam, βGen, Function.comp, RingHom.comp_apply, eval₂Hom_X',
    Sum.elim_inr, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  exact (βP_eq P β i).symm

variable [IsAlgClosed K] [CharZero K] {c β}

/--
Generic-line theorem: c_e≠0 and β_i≠0,-1 give nonzero g∈K[ε]
such that every ε with g(ε)≠0 has exactly Q(G) simple auxiliary roots.
-/
theorem exists_line_generic (hc : ∀ e, c e ≠ 0) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    ∃ g : Polynomial K, g ≠ 0 ∧ ∀ ε : K, g.eval ε ≠ 0 →
      Nat.card {p : (Dart E → K) × (V → K) //
        G.IsAuxSolution (fun e => 1 + ε * c e) β p.1 p.2} = G.Q ∧
      ∀ A F, G.IsAuxSolution (fun e => 1 + ε * c e) β A F →
        G.IsSimpleAuxSolution (fun e => 1 + ε * c e) β A F := by
  classical
  obtain ⟨P⟩ := newtonPuiseux_exists K
  have hs := lineToL_comp_sGen c β P
  have hb := lineToL_comp_βGen c β P
  have hcard : Nat.card (SystemSolutions (G.lineAux c β) (lineDen c β) (lineToL P)) = G.Q :=
    (Nat.card_congr (G.lineSolEquiv c β (lineToL P))).trans
      (G.card_systemSolutions_of_comp P hs hb hc hβ0 hβ1)
  have hfin : Finite (SystemSolutions (G.lineAux c β) (lineDen c β) (lineToL P)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact G.Q_pos.ne')
  have hsimple : ∀ y : SystemSolutions (G.lineAux c β) (lineDen c β) (lineToL P),
      IsSimpleAt (G.lineAux c β) (lineToL P) y.1 := fun y =>
    (G.isSimpleAt_line_iff c β _ _).2
      (G.isSimpleAt_of_comp P hs hb hc hβ0 hβ1 (G.lineSolEquiv c β (lineToL P) y))
  obtain ⟨g, hg0, hg⟩ := generic_fiber_constancy (G.lineAux c β) (lineDen c β) G.Q (lineToL P)
    (lineToL_injective P) hfin hcard hsimple
  refine ⟨g, hg0, fun ε hε => ?_⟩
  obtain ⟨hcardε, hsimpε⟩ := hg K (Polynomial.evalRingHom ε) hε
  have hS := evalRingHom_comp_lineParam_sGen c β ε
  have hB := evalRingHom_comp_lineParam_βGen c β ε
  have e := (G.lineSolEquiv c β (Polynomial.evalRingHom ε)).trans
    (G.genericSolEquiv ((Polynomial.evalRingHom ε).comp (lineParam c β)))
  rw [hS, hB] at e
  refine ⟨(Nat.card_congr e).symm.trans hcardε, ?_⟩
  intro A F hAF
  have hy : (∀ i, eval (Sum.elim A F) (map (Polynomial.evalRingHom ε) (G.lineAux c β i)) = 0) ∧
      eval (Sum.elim A F) (map (Polynomial.evalRingHom ε) (lineDen c β)) ≠ 0 := by
    simp only [lineAux, lineDen, map_map]
    simp only [map_genericAux, map_auxDen, hS, hB]
    exact (G.isAuxSolution_iff _ _ (Sum.elim A F)).2 hAF
  have := hsimpε ⟨Sum.elim A F, hy⟩
  unfold IsSimpleAt at this
  simp only [lineAux, map_map] at this
  simp only [map_genericAux, hS, hB] at this
  exact this

end Line

/-- **Complex fixed-parameter version.** For fixed c_e≠0 and β_i≠0,−1, some ε₀>0 ensures exactly Q(G) simple auxiliary solutions for s_e=1+εc_e at every complex ε with 0<|ε|<ε₀. -/
theorem card_weak_coupling_eq_Q (c : E → ℂ) (hc : ∀ e, c e ≠ 0) (β : V → ℂ)
    (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < ε₀ →
      Nat.card {p : (Dart E → ℂ) × (V → ℂ) //
        G.IsAuxSolution (fun e => 1 + ε * c e) β p.1 p.2} = G.Q ∧
      ∀ A F, G.IsAuxSolution (fun e => 1 + ε * c e) β A F →
        G.IsSimpleAuxSolution (fun e => 1 + ε * c e) β A F := by
  classical
  obtain ⟨g, hg0, hg⟩ := G.exists_line_generic hc hβ0 hβ1
  let S : Finset ℝ := insert 1 ((g.roots.toFinset.filter (· ≠ 0)).image fun r => ‖r‖)
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hSne, ?_, fun ε hε0 hε => hg ε fun hroot => ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact norm_pos_iff.2 (Finset.mem_filter.1 hr).2
  · have hmem : ‖ε‖ ∈ S := by
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨ε, ?_, rfl⟩)
      rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      exact ⟨hroot, hε0⟩
    exact absurd (S.min'_le _ hmem) (not_le.2 hε)

end Multigraph

end BPFixedPoints
