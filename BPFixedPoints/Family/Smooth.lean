import BPFixedPoints.Family.Beliefs

/-!
# Smoothness of the total admissible BP space

Lift the free normalized-belief coordinates u,q through a square-zero extension,
then correct each edge equation a²rs=qd by Newton's method. Its derivative
2ars is a unit, so one correction is exact.
-/

namespace BPFixedPoints.Multigraph

open BP MvPolynomial
open scoped Ring
set_option linter.unusedSectionVars false

section SquareZero

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)

include hI in
/-- Lift a simple unit quadratic root through a square-zero extension. -/
theorem exists_quadratic_lift (r s q d : R) (hr : IsUnit r) (hs : IsUnit s)
    (htwo : IsUnit (2 : R)) (a₀ : R ⧸ I) (ha₀ : IsUnit a₀)
    (he : a₀ ^ 2 * Ideal.Quotient.mk I r * Ideal.Quotient.mk I s =
      Ideal.Quotient.mk I q * Ideal.Quotient.mk I d) :
    ∃ a : R, Ideal.Quotient.mk I a = a₀ ∧ IsUnit a ∧ a ^ 2 * r * s = q * d := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hau := (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).mp ha₀
  let err := a ^ 2 * r * s - q * d
  have herr : err ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [err, map_sub, map_mul, map_pow, sub_eq_zero] using he
  have herr2 : err ^ 2 = 0 := hI.le (Ideal.pow_mem_pow herr 2)
  have hder : IsUnit (2 * a * r * s) := ((htwo.mul hau).mul hr).mul hs
  let k := (2 * a * r * s)⁻¹ʳ
  have hk : 2 * a * r * s * k = 1 := Ring.mul_inverse_cancel _ hder
  have hm : Ideal.Quotient.mk I (a - err * k) = Ideal.Quotient.mk I a := by
    simp [map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr herr]
  refine ⟨a - err * k, hm, (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).mp
    (hm ▸ ha₀), ?_⟩
  have heq : err = a ^ 2 * r * s - q * d := rfl
  grind only

end SquareZero

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {G : Multigraph V E}

namespace BeliefPoint

variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem exists_lift (I : Ideal R) (hI : I ^ 2 = ⊥) (p : BeliefPoint G (R ⧸ I)) :
    ∃ p' : BeliefPoint G R, p'.map (Ideal.Quotient.mk I) = p := by
  classical
  obtain ⟨u, hu⟩ := show ∃ u : V → R, ∀ i, Ideal.Quotient.mk I (u i) = p.u i from
    Classical.axiomOfChoice fun i => Ideal.Quotient.mk_surjective (p.u i)
  obtain ⟨q, hq⟩ := show ∃ q : E → R, ∀ e, Ideal.Quotient.mk I (q e) = p.q e from
    Classical.axiomOfChoice fun e => Ideal.Quotient.mk_surjective (p.q e)
  have lift_unit {x : R} (h : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x :=
    (IsNilpotent.isUnit_quotient_mk_iff ⟨2, hI⟩).mp h
  have hur i : IsUnit (u i) := lift_unit (by rw [hu]; exact p.u_unit i)
  have huc i : IsUnit (1 - u i) := lift_unit (by simpa [hu] using p.uc_unit i)
  have hqr e : IsUnit (q e) := lift_unit (by rw [hq]; exact p.q_unit e)
  have hrr e : IsUnit (u (G.fst e) - q e) := lift_unit (by simpa [hu, hq] using p.r_unit e)
  have hsr e : IsUnit (u (G.snd e) - q e) := lift_unit (by simpa [hu, hq] using p.s_unit e)
  have hdr e : IsUnit (1 - u (G.fst e) - u (G.snd e) + q e) :=
    lift_unit (by simpa [hu, hq] using p.d_unit e)
  have ht : IsUnit (2 : R) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (show (2 : ℂ) ≠ 0 by norm_num)).map (algebraMap ℂ R)
  have he e := exists_quadratic_lift I hI (u (G.fst e) - q e) (u (G.snd e) - q e)
    (q e) (1 - u (G.fst e) - u (G.snd e) + q e) (hrr e) (hsr e) ht
    (p.a e) (p.a_unit e) (by simpa [hu, hq] using p.equation e)
  choose a ha hau hae using he
  let p' : BeliefPoint G R := ⟨a, u, q, hau, hur, huc, hqr, hrr, hsr, hdr, hae⟩
  refine ⟨p', ?_⟩
  ext i
  · exact ha i
  · exact hu i
  · exact hq i

end BeliefPoint

variable (G)

instance familyRing_finitePresentation : Algebra.FinitePresentation ℂ G.FamilyRing :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

instance familyRing_formallySmooth : Algebra.FormallySmooth ℂ G.FamilyRing := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro R _ _ I hI f
  let p := G.familyPointOfHom f
  obtain ⟨q, hq⟩ := p.toBelief.exists_lift I hI
  have hp : q.toFamily.map (Ideal.Quotient.mk I) = p := by
    rw [← q.toFamily_map, hq, p.toFamily_toBelief]
  refine ⟨q.toFamily.toHom, ?_⟩
  rw [← FamilyPoint.map_toHom]
  change (q.toFamily.map (Ideal.Quotient.mk I)).toHom = f
  rw [hp]
  exact G.toHom_familyPointOfHom f

/-- Smoothness in `prop:bp-family`: the defined admissible coordinate ring is smooth over ℂ. -/
theorem familyRing_smooth (_hG : G.Loopless) : Algebra.Smooth ℂ G.FamilyRing where
  formallySmooth := inferInstance
  finitePresentation := inferInstance

end BPFixedPoints.Multigraph
