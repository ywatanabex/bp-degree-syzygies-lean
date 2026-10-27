import BPFixedPoints.Degree.Lift.Count

/-!
# BP/auxiliary correspondence and counting at a special parameter

Over any field K', for a_e≠0 and β'_i≠0, put b_i=β'_i∏_{e∋i}a_e.
Admissible BP solutions at (a,b) correspond bijectively to auxiliary solutions
at (s_e=a_e²,β'), via y↦(A,F) and reconstruction (6), with both round trips.
Thus over a Puiseux-type L, choosing a_e²=1+t c_e gives exactly Q(G)
admissible BP solutions by `card_puiseuxSolutions`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace BP.PuiseuxField

universe u

variable {K : Type u} [Field K] (P : PuiseuxField K)

theorem ofK_ne_zero_of_ne_zero {c : K} (hc : c ≠ 0) : P.ofK c ≠ 0 :=
  (map_ne_zero P.ofK).2 hc

end BP.PuiseuxField

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section General

variable {K' : Type*} [Field K']

theorem auxBeta_reconB (a : E → K') (ha : ∀ e, a e ≠ 0) (β' : V → K') (i : V) :
    G.auxBeta a (G.reconB a β') i = β' i := by
  unfold auxBeta reconB
  have : ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun e _ => ha e
  rw [mul_div_assoc, div_self this, mul_one]

theorem reconB_ne_zero (a : E → K') (ha : ∀ e, a e ≠ 0) (β' : V → K') (hβ' : ∀ i, β' i ≠ 0)
    (i : V) : G.reconB a β' i ≠ 0 :=
  mul_ne_zero (hβ' i) (Finset.prod_ne_zero_iff.2 fun e _ => ha e)

/-- Correspondence between admissible BP solutions for (a,β' product a) and auxiliary solutions for (a²,β'). -/
noncomputable def admissibleEquivAux (hG : G.Loopless) (a : E → K') (ha : ∀ e, a e ≠ 0)
    (β' : V → K') (hβ' : ∀ i, β' i ≠ 0) :
    {y : Dart E → K' // G.IsAdmissibleSolution a (G.reconB a β') y} ≃
      {p : (Dart E → K') × (V → K') // G.IsAuxSolution (fun e => a e ^ 2) β' p.1 p.2} where
  toFun y := ⟨(G.auxA a (G.reconB a β') y.1, G.totalField (G.reconB a β') y.1), by
    have h := G.isAuxSolution_of_admissible hG a (G.reconB a β') y.1 ha
      (G.reconB_ne_zero a ha β' hβ') y.2
    have hb : G.auxBeta a (G.reconB a β') = β' := funext (G.auxBeta_reconB a ha β')
    rw [hb] at h
    exact h⟩
  invFun p := ⟨G.reconY a p.1.1 p.1.2, by
    obtain ⟨⟨A, F⟩, h⟩ := p
    change G.IsAuxSolution (fun e => a e ^ 2) β' A F at h
    have h4 : ∀ α, F (G.tail α) = A α * (1 + a α.1 ^ 2 * A (rev α)) / (1 + A (rev α)) := by
      intro α
      have hB : 1 + A (rev α) ≠ 0 := fun h0 => h.A_ne_neg_one (rev α) (by linear_combination h0)
      rw [eq_div_iff hB]
      exact h.edge α
    exact G.isAdmissibleSolution_reconY hG ha h.A_ne_zero h.A_ne_neg_one h.F_ne_zero
      h.F_ne_neg_one h4 h.vertex⟩
  left_inv y := by
    apply Subtype.ext
    funext α
    exact G.reconY_auxA a (G.reconB a β') y.1 ha (G.reconB_ne_zero a ha β' hβ')
      (fun α => y.2.2.1 α) α
  right_inv p := by
    obtain ⟨⟨A, F⟩, h⟩ := p
    change G.IsAuxSolution (fun e => a e ^ 2) β' A F at h
    apply Subtype.ext
    simp only
    refine Prod.ext (funext fun α => ?_) (funext fun i => ?_)
    · exact G.auxA_reconY hG ha h.A_ne_zero h.F_ne_zero h.vertex α
    · exact G.totalField_reconY hG ha h.A_ne_zero h.F_ne_zero h.vertex i

theorem card_admissible_eq_card_aux (hG : G.Loopless) (a : E → K') (ha : ∀ e, a e ≠ 0)
    (β' : V → K') (hβ' : ∀ i, β' i ≠ 0) :
    Nat.card {y : Dart E → K' // G.IsAdmissibleSolution a (G.reconB a β') y} =
      Nat.card {p : (Dart E → K') × (V → K') // G.IsAuxSolution (fun e => a e ^ 2) β' p.1 p.2} :=
  Nat.card_congr (G.admissibleEquivAux hG a ha β' hβ')

end General

section Puiseux

universe u

variable {K : Type u} [Field K] [DecidableEq K] (P : PuiseuxField K)

/-- If a_e²=1+t c_e over a Puiseux-type valued field, the admissible BP solution count at (a,β product a) is Q(G). -/
theorem card_admissible_puiseux [IsAlgClosed K] [CharZero K] (hG : G.Loopless) (c : E → K)
    (hc : ∀ e, c e ≠ 0) (β : V → K) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1)
    (a : E → P.L) (ha : ∀ e, a e ^ 2 = sP P c e) :
    Nat.card {y : Dart E → P.L // G.IsAdmissibleSolution a (G.reconB a (βP P β)) y} = G.Q := by
  have ha0 : ∀ e, a e ≠ 0 := by
    intro e h0
    have := ha e
    rw [h0, zero_pow two_ne_zero] at this
    have hv := val_sP_sub_one_lt P c e
    rw [← this, zero_sub, Valuation.map_neg, map_one] at hv
    exact lt_irrefl _ hv
  rw [G.card_admissible_eq_card_aux hG a ha0 (βP P β) (fun i => P.ofK_ne_zero_of_ne_zero (hβ0 i))]
  have hs : (fun e => a e ^ 2) = sP P c := funext ha
  rw [hs]
  exact G.card_puiseuxSolutions P c hc β hβ0 hβ1

end Puiseux

end Multigraph

end BPFixedPoints
