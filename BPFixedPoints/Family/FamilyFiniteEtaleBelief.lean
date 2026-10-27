import BPFixedPoints.Family.FiniteCover
import BPFixedPoints.Family.FamilyFiniteEtaleSqrt

/-!
# The belief cover is finite étale of degree 2^m (`eq:belief-cover`)

Let A=`BeliefBaseRing`=ℂ[u,q][1/(∏u(1−u)∏q r s d)] be the ring of free
beliefs (the paper's ξ,q,ρ,σ,δ are u,q,r,s,d here) and `BeliefRing` the
coordinate ring of a_e²r_es_e=q_ed_e, an A-algebra through
`beliefBaseAlgebra`. The paper adjoins a_e with a_e²=q_ed_e/(r_es_e)
(`beliefBaseSquare`).

* `beliefRingEquivSqrtCover`: as A-algebras, `BeliefRing` is the square-root
  algebra A[x_e]/(x_e²−q_ed_e/(r_es_e)) (`SqrtAlg`).
* `beliefRing_finite_etale`: `BeliefRing` is finite, free of rank 2^m and
  étale over A (`beliefRing_free`, `finrank_beliefRing`,
  `beliefRing_etale`; finiteness is the existing `beliefRing_finite`).

`familyRingEquivBeliefRing` identifies `BeliefRing` with the BP family ring
as ℂ-algebras; transporting the A-algebra structure to `FamilyRing` is not
done here.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial BP
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- The square-root algebra of the belief cover: adjoin x_e with x_e²=q_e d_e/(r_e s_e) to the free-belief ring. -/
abbrev BeliefSqrtCover := SqrtAlg (G.beliefBaseSquare)

/-- Image of a free-belief polynomial in the square-root algebra. -/
noncomputable def sqrtCoverBase (f : BeliefBasePoly V E) : G.BeliefSqrtCover :=
  algebraMap G.BeliefBaseRing G.BeliefSqrtCover (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing f)

/-- The tautological belief point of the square-root algebra. -/
noncomputable def sqrtCoverPoint : BeliefPoint G G.BeliefSqrtCover := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.beliefBase_unit_factors
  refine
    { a := sqrtRoot G.beliefBaseSquare
      u := fun i => G.sqrtCoverBase (beliefBaseU i)
      q := fun e => G.sqrtCoverBase (beliefBaseQ e)
      a_unit := fun e => ?_
      u_unit := fun i => (hu i).map _
      uc_unit := fun i => ?_
      q_unit := fun e => (hq e).map _
      r_unit := fun e => ?_
      s_unit := fun e => ?_
      d_unit := fun e => ?_
      equation := fun e => ?_ }
  · apply (isUnit_pow_iff two_ne_zero).1
    rw [sqrtRoot_sq]
    exact (G.beliefBaseSquare_unit e).map _
  · simpa [sqrtCoverBase] using (huc i).map (algebraMap G.BeliefBaseRing G.BeliefSqrtCover)
  · simpa [sqrtCoverBase, beliefBaseR] using (hr e).map (algebraMap G.BeliefBaseRing G.BeliefSqrtCover)
  · simpa [sqrtCoverBase, beliefBaseS] using (hs e).map (algebraMap G.BeliefBaseRing G.BeliefSqrtCover)
  · simpa [sqrtCoverBase, beliefBaseD] using (hd e).map (algebraMap G.BeliefBaseRing G.BeliefSqrtCover)
  · have h := congrArg (algebraMap G.BeliefBaseRing G.BeliefSqrtCover) (G.beliefBaseSquare_mul e)
    rw [sqrtRoot_sq]
    simpa [sqrtCoverBase, beliefBaseR, beliefBaseS, beliefBaseD, map_mul] using h


@[simp] theorem sqrtCoverPoint_a (e : E) : G.sqrtCoverPoint.a e = sqrtRoot G.beliefBaseSquare e := rfl
@[simp] theorem sqrtCoverPoint_u (i : V) : G.sqrtCoverPoint.u i = G.sqrtCoverBase (beliefBaseU i) := rfl
@[simp] theorem sqrtCoverPoint_q (e : E) : G.sqrtCoverPoint.q e = G.sqrtCoverBase (beliefBaseQ e) := rfl

/-- Belief ring → square-root algebra, from the tautological point. -/
noncomputable def beliefToSqrtCover : G.BeliefRing →ₐ[ℂ] G.BeliefSqrtCover := G.sqrtCoverPoint.toHom

theorem beliefToSqrtCover_comp_algebraMap :
    (G.beliefToSqrtCover.comp (IsScalarTower.toAlgHom ℂ G.BeliefBaseRing G.BeliefRing)) =
      IsScalarTower.toAlgHom ℂ G.BeliefBaseRing G.BeliefSqrtCover := by
  apply IsLocalization.algHom_ext (Submonoid.powers G.beliefBaseDen)
  apply MvPolynomial.algHom_ext
  intro j
  change G.beliefToSqrtCover (algebraMap G.BeliefBaseRing G.BeliefRing
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X j))) =
    algebraMap G.BeliefBaseRing G.BeliefSqrtCover (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X j))
  rw [beliefBaseHom_map, aeval_X]
  rcases j with i | e
  · change G.beliefToSqrtCover (G.beliefRingPoint.u i) = G.sqrtCoverBase (beliefBaseU i)
    rw [beliefRingPoint, beliefPointOfHom_u, AlgHom.id_apply, beliefToSqrtCover,
      BeliefPoint.toHom_map, BeliefPoint.eval_u, sqrtCoverPoint_u]
  · change G.beliefToSqrtCover (G.beliefRingPoint.q e) = G.sqrtCoverBase (beliefBaseQ e)
    rw [beliefRingPoint, beliefPointOfHom_q, AlgHom.id_apply, beliefToSqrtCover,
      BeliefPoint.toHom_map, BeliefPoint.eval_q, sqrtCoverPoint_q]


/-- `beliefToSqrtCover` is linear over the free-belief ring. -/
noncomputable def beliefToSqrtCoverₐ : G.BeliefRing →ₐ[G.BeliefBaseRing] G.BeliefSqrtCover :=
  { G.beliefToSqrtCover.toRingHom with
    commutes' := fun r => AlgHom.congr_fun G.beliefToSqrtCover_comp_algebraMap r }

@[simp] theorem beliefToSqrtCoverₐ_apply (x : G.BeliefRing) : G.beliefToSqrtCoverₐ x = G.beliefToSqrtCover x :=
  rfl

/-- Square-root algebra → belief ring, x_e ↦ a_e. -/
noncomputable def sqrtCoverToBelief : G.BeliefSqrtCover →ₐ[G.BeliefBaseRing] G.BeliefRing :=
  sqrtLift G.beliefBaseSquare G.beliefRingPoint.a G.beliefRingPoint_a_sq

theorem beliefToSqrtCover_a (e : E) : G.beliefToSqrtCover (G.beliefRingPoint.a e) = sqrtRoot _ e := by
  rw [beliefRingPoint, beliefPointOfHom_a, AlgHom.id_apply, beliefToSqrtCover, BeliefPoint.toHom_map,
    BeliefPoint.eval_a, sqrtCoverPoint_a]

theorem sqrtCoverToBelief_sqrtCoverBase (f : BeliefBasePoly V E) :
    G.sqrtCoverToBelief (G.sqrtCoverBase f) = aeval G.beliefRingPoint.baseVal f := by
  rw [sqrtCoverBase, AlgHom.commutes, beliefBaseHom_map]

/-- **The belief cover is a square-root algebra.** As algebras over the free-belief ring, the belief ring is A[x_e]/(x_e²−q_e d_e/(r_e s_e)). -/
noncomputable def beliefRingEquivSqrtCover :
    G.BeliefRing ≃ₐ[G.BeliefBaseRing] G.BeliefSqrtCover :=
  AlgEquiv.ofAlgHom G.beliefToSqrtCoverₐ G.sqrtCoverToBelief
    (sqrtAlg_hom_ext _ fun e => by
      rw [AlgHom.comp_apply, sqrtCoverToBelief, sqrtLift_root, beliefToSqrtCoverₐ_apply, beliefToSqrtCover_a,
        AlgHom.id_apply])
    (by
      have h : (G.sqrtCoverToBelief.comp G.beliefToSqrtCoverₐ).restrictScalars ℂ = AlgHom.id ℂ G.BeliefRing := by
        apply G.beliefRing_hom_ext
        intro j
        rw [AlgHom.restrictScalars_apply, AlgHom.comp_apply, beliefToSqrtCoverₐ_apply, beliefToSqrtCover,
          BeliefPoint.toHom_map, aeval_X, AlgHom.id_apply]
        rcases j with e | i | e
        · change G.sqrtCoverToBelief (sqrtRoot _ e) = _
          rw [sqrtCoverToBelief, sqrtLift_root]
          rfl
        · change G.sqrtCoverToBelief (G.sqrtCoverBase (beliefBaseU i)) = _
          rw [sqrtCoverToBelief_sqrtCoverBase, BeliefPoint.base_eval_u]
          rfl
        · change G.sqrtCoverToBelief (G.sqrtCoverBase (beliefBaseQ e)) = _
          rw [sqrtCoverToBelief_sqrtCoverBase, BeliefPoint.base_eval_q]
          rfl
      ext x
      exact AlgHom.congr_fun h x)


/-! ### Finite étale of rank 2^m -/

theorem beliefBaseRing_two_isUnit : IsUnit (2 : G.BeliefBaseRing) := by
  rw [← map_ofNat (algebraMap ℂ G.BeliefBaseRing) 2]
  exact (isUnit_iff_ne_zero.2 two_ne_zero).map _

/-- **Étaleness in `eq:belief-cover`.** The belief ring is étale over the free-belief ring. -/
theorem beliefRing_etale : Algebra.Etale G.BeliefBaseRing G.BeliefRing := by
  have := sqrtAlg_etale (s := G.beliefBaseSquare) G.beliefBaseRing_two_isUnit G.beliefBaseSquare_unit
  exact Algebra.Etale.of_equiv G.beliefRingEquivSqrtCover.symm

/-- The belief ring is a free module over the free-belief ring. -/
theorem beliefRing_free : Module.Free G.BeliefBaseRing G.BeliefRing := by
  have := sqrtAlg_free G.beliefBaseSquare
  exact Module.Free.of_equiv G.beliefRingEquivSqrtCover.symm.toLinearEquiv

/-- **Covering degree in `eq:belief-cover`.** The belief cover has rank 2^m. -/
theorem finrank_beliefRing :
    Module.finrank G.BeliefBaseRing G.BeliefRing = 2 ^ Fintype.card E := by
  rw [G.beliefRingEquivSqrtCover.toLinearEquiv.finrank_eq, finrank_sqrtAlg]

/-- **`eq:belief-cover`.** Over the free-belief ring, the belief ring is finite, free of rank 2^m and étale. -/
theorem beliefRing_finite_etale :
    Module.Finite G.BeliefBaseRing G.BeliefRing ∧ Module.Free G.BeliefBaseRing G.BeliefRing ∧
      Module.finrank G.BeliefBaseRing G.BeliefRing = 2 ^ Fintype.card E ∧
      Algebra.Etale G.BeliefBaseRing G.BeliefRing :=
  ⟨G.beliefRing_finite, G.beliefRing_free, G.finrank_beliefRing, G.beliefRing_etale⟩

end BPFixedPoints.Multigraph
