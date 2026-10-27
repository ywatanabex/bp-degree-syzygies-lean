import BPFixedPoints.Family.NonnormalizableLocus
import BPFixedPoints.Family.NonnormalizableLocusDependence

/-!
# The coordinate ring of the edge chart and evaluation at chart points

Over a commutative base ring k, the *chart ring* is k[a_e, x_e][1/D] with
D = ∏_e x_e (a_e − x_e)(1 − a_e x_e) (`ChartRing`). Its points with values in a field are exactly
the chart points (x_e ≠ 0, x_e ≠ a_e, a_e x_e ≠ 1) (`chartRingEval`). The chart ring carries the
parameter family (a_e, b_i) with b_i = −1/Φ_i(a,x) (`chartRingFamily`); at a chart point it
evaluates to (a, −1/Φ(a,x)) (`chartRingEval_comp_family`), so a chart point lies in the chart
fiber over (a,b) exactly when this evaluation is (a,b).

This file also proves the ring identities behind these statements: the ring form Φ_i of the
vertex product with a supplied inverse of 1 − a_e x_e (`ringChartField`), its compatibility with
ring homomorphisms, and the compatibility of `Ring.inverse` with ring homomorphisms on units.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section RingForm

variable {R : Type*} [CommRing R]

/-- Ring form of Φ_i(a,x), where u_e stands for an inverse of 1 − a_e x_e. -/
def ringChartField (a x u : E → R) (i : V) : R :=
  ∏ e, (if G.fst e = i then x e else 1) * (if G.snd e = i then (a e - x e) * u e else 1)

theorem map_ringChartField {S : Type*} [CommRing S] (ψ : R →+* S) (a x u : E → R) (i : V) :
    ψ (G.ringChartField a x u i) = G.ringChartField (ψ ∘ a) (ψ ∘ x) (ψ ∘ u) i := by
  simp only [ringChartField, map_prod, map_mul, apply_ite ψ, map_one, map_sub,
    Function.comp_apply]

theorem ringChartField_eq_chartField {K : Type*} [Field K] (a x : E → K) (i : V) :
    G.ringChartField a x (fun e => (1 - a e * x e)⁻¹) i = G.chartField a x i := by
  simp only [ringChartField, chartField, edgeInvolution, div_eq_mul_inv]

theorem isUnit_ringChartField {a x u : E → R} (hx : ∀ e, IsUnit (x e))
    (hax : ∀ e, IsUnit (a e - x e)) (hu : ∀ e, IsUnit (u e)) (i : V) :
    IsUnit (G.ringChartField a x u i) := by
  rw [ringChartField, IsUnit.prod_univ_iff]
  intro e
  refine IsUnit.mul ?_ ?_
  · split_ifs
    · exact hx e
    · exact isUnit_one
  · split_ifs
    · exact (hax e).mul (hu e)
    · exact isUnit_one

end RingForm

/-- Ring homomorphisms commute with `Ring.inverse` on units. -/
theorem ringHom_map_ringInverse {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) {y : R}
    (hy : IsUnit y) : ψ (Ring.inverse y) = Ring.inverse (ψ y) := by
  obtain ⟨u, rfl⟩ := hy
  rw [Ring.inverse_unit]
  have h : ψ ↑u = ↑(Units.map ψ.toMonoidHom u) := rfl
  rw [h, Ring.inverse_unit]
  rfl

section ChartRing

variable (k : Type*) [CommRing k]

/-- The chart denominator D = ∏_e x_e (a_e − x_e)(1 − a_e x_e) in k[a,x], with a_e = X (inl e)
and x_e = X (inr e). -/
noncomputable def chartDen : MvPolynomial (E ⊕ E) k :=
  ∏ e, X (Sum.inr e) * (X (Sum.inl e) - X (Sum.inr e)) * (1 - X (Sum.inl e) * X (Sum.inr e))

/-- The chart ring k[a,x][1/D]. -/
abbrev ChartRing := Localization.Away (chartDen (E := E) k)

/-- The coordinate a_e in the chart ring. -/
noncomputable def chartRingA (e : E) : ChartRing (E := E) k :=
  algebraMap (MvPolynomial (E ⊕ E) k) _ (X (Sum.inl e))

/-- The coordinate x_e in the chart ring. -/
noncomputable def chartRingX (e : E) : ChartRing (E := E) k :=
  algebraMap (MvPolynomial (E ⊕ E) k) _ (X (Sum.inr e))

/-- The inverse of 1 − a_e x_e in the chart ring. -/
noncomputable def chartRingU (e : E) : ChartRing (E := E) k :=
  Ring.inverse (algebraMap (MvPolynomial (E ⊕ E) k) _ (1 - X (Sum.inl e) * X (Sum.inr e)))

theorem isUnit_chartRing_factors (e : E) :
    IsUnit (chartRingX k e) ∧ IsUnit (chartRingA k e - chartRingX k e) ∧
      IsUnit (algebraMap (MvPolynomial (E ⊕ E) k) (ChartRing (E := E) k)
        (1 - X (Sum.inl e) * X (Sum.inr e))) := by
  have h0 := IsLocalization.Away.algebraMap_isUnit (S := ChartRing (E := E) k)
    (chartDen (E := E) k)
  have h : IsUnit (algebraMap (MvPolynomial (E ⊕ E) k) (ChartRing (E := E) k)
      (∏ e, X (Sum.inr e) * (X (Sum.inl e) - X (Sum.inr e)) *
        (1 - X (Sum.inl e) * X (Sum.inr e)))) := h0
  rw [map_prod, IsUnit.prod_univ_iff] at h
  have he := h e
  rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at he
  refine ⟨he.1.1, ?_, he.2⟩
  have := he.1.2
  rwa [map_sub] at this

/-- The parameter family on the chart ring: a_e and b_i = −1/Φ_i(a,x). -/
noncomputable def chartRingFamily : E ⊕ V → ChartRing (E := E) k
  | Sum.inl e => chartRingA k e
  | Sum.inr i => -Ring.inverse (G.ringChartField (chartRingA k) (chartRingX k) (chartRingU k) i)

theorem isUnit_chartRingField (i : V) :
    IsUnit (G.ringChartField (chartRingA k) (chartRingX k) (chartRingU k) i) :=
  G.isUnit_ringChartField (fun e => (isUnit_chartRing_factors k e).1)
    (fun e => (isUnit_chartRing_factors k e).2.1)
    (fun e => (isUnit_chartRing_factors k e).2.2.ringInverse) i

variable {k} {K : Type*} [Field K] [Algebra k K]

theorem aeval_chartDen_ne_zero {a x : E → K} (hx : IsChartPoint a x) :
    aeval (Sum.elim a x) (chartDen (E := E) k : MvPolynomial (E ⊕ E) k) ≠ 0 := by
  rw [chartDen, map_prod, Finset.prod_ne_zero_iff]
  intro e _
  simp only [map_mul, map_sub, map_one, aeval_X, Sum.elim_inl, Sum.elim_inr]
  obtain ⟨h0, h1, h2⟩ := hx e
  exact mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))) (one_sub_mul_ne_zero h2)

/-- Evaluation of the chart ring at a chart point. -/
noncomputable def chartRingEval (a x : E → K) (hx : IsChartPoint a x) :
    ChartRing (E := E) k →+* K :=
  Localization.awayLift (aeval (Sum.elim a x)).toRingHom (chartDen k)
    (isUnit_iff_ne_zero.mpr (aeval_chartDen_ne_zero hx))

theorem chartRingEval_algebraMap {a x : E → K} (hx : IsChartPoint a x)
    (p : MvPolynomial (E ⊕ E) k) :
    chartRingEval a x hx (algebraMap (MvPolynomial (E ⊕ E) k) (ChartRing (E := E) k) p) =
      aeval (Sum.elim a x) p :=
  IsLocalization.Away.lift_eq _ (isUnit_iff_ne_zero.mpr (aeval_chartDen_ne_zero hx)) p

/-- At a chart point the parameter family evaluates to (a, −1/Φ(a,x)). -/
theorem chartRingEval_comp_family {a x : E → K} (hx : IsChartPoint a x) :
    chartRingEval a x hx ∘ G.chartRingFamily k =
      Sum.elim a (fun i => -(G.chartField a x i)⁻¹) := by
  have hA : ∀ e, chartRingEval a x hx (chartRingA k e) = a e := fun e => by
    simp [chartRingA, chartRingEval_algebraMap]
  have hX : ∀ e, chartRingEval a x hx (chartRingX k e) = x e := fun e => by
    simp [chartRingX, chartRingEval_algebraMap]
  have hU : ∀ e, chartRingEval a x hx (chartRingU k e) = (1 - a e * x e)⁻¹ := fun e => by
    rw [chartRingU, ringHom_map_ringInverse _ (isUnit_chartRing_factors k e).2.2,
      chartRingEval_algebraMap, Ring.inverse_eq_inv']
    simp
  funext z
  rcases z with e | i
  · exact hA e
  · simp only [Function.comp_apply, chartRingFamily, Sum.elim_inr, map_neg]
    rw [ringHom_map_ringInverse _ (G.isUnit_chartRingField k i), map_ringChartField,
      Ring.inverse_eq_inv']
    have h1 : (chartRingEval a x hx) ∘ chartRingA k = a := funext hA
    have h2 : (chartRingEval a x hx) ∘ chartRingX k = x := funext hX
    have h3 : (chartRingEval a x hx) ∘ chartRingU k = fun e => (1 - a e * x e)⁻¹ := funext hU
    rw [h1, h2, h3, ringChartField_eq_chartField]

/-- A chart point lies in the chart fiber over (a,b) iff the parameter family evaluates to
(a,b). -/
theorem isChartSolution_iff_eval {a x : E → K} {b : V → K} (hx : IsChartPoint a x) :
    G.IsChartSolution a b x ↔ chartRingEval a x hx ∘ G.chartRingFamily k = Sum.elim a b := by
  rw [chartRingEval_comp_family]
  constructor
  · rintro ⟨-, hb⟩
    congr 1
    funext i
    have hΦ := G.chartField_ne_zero hx i
    field_simp
    linear_combination -hb i
  · intro h
    refine ⟨hx, fun i => ?_⟩
    have := congrFun h (Sum.inr i)
    simp only [Sum.elim_inr] at this
    rw [← this]
    have hΦ := G.chartField_ne_zero hx i
    field_simp

end ChartRing

end Multigraph

end BPFixedPoints
