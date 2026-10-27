import BPFixedPoints.Family.BeliefRing
import BPFixedPoints.Family.EdgeCover

/-!
# The belief coordinate ring is a domain

Embed the belief ring in an open subset of a domain using edge square roots
w=ars. Construct a map back and check that its composite is the identity
on the original belief coordinates.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial
open scoped Ring
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

noncomputable def coverBeliefPoint : BeliefPoint G G.BeliefRing :=
  G.beliefPointOfHom (AlgHom.id ℂ G.BeliefRing)

/-- Symmetric normalized beliefs exist for every graph. -/
noncomputable def symmetricBeliefPoint : BeliefPoint G ℂ where
  a := fun _ => 1
  u := fun _ => 1 / 2
  q := fun _ => 1 / 4
  a_unit := fun _ => isUnit_one
  u_unit := by intro; norm_num [isUnit_iff_ne_zero]
  uc_unit := by intro; norm_num [isUnit_iff_ne_zero]
  q_unit := by intro; norm_num [isUnit_iff_ne_zero]
  r_unit := by intro; norm_num [isUnit_iff_ne_zero]
  s_unit := by intro; norm_num [isUnit_iff_ne_zero]
  d_unit := by intro; norm_num [isUnit_iff_ne_zero]
  equation := by intro; norm_num

abbrev BeliefCover := EdgeCover (MvPolynomial V ℂ) E
  (fun e => X (G.fst e)) (fun e => X (G.snd e))

instance beliefCover_isDomain : IsDomain G.BeliefCover := by
  apply EdgeCover.isDomain
  · exact fun e => X_ne_zero _
  · exact fun e => X_ne_zero _
  · intro e h
    have he := congrArg (aeval (fun _ : V => (0 : ℂ))) h
    simp at he

noncomputable def coverU (i : V) : G.BeliefCover := algebraMap (MvPolynomial V ℂ) _ (X i)
noncomputable def coverQ (e : E) : G.BeliefCover := EdgeCover.q _ _ _ _ e
noncomputable def coverW (e : E) : G.BeliefCover := EdgeCover.w _ _ _ _ e
noncomputable def coverR (e : E) : G.BeliefCover := G.coverU (G.fst e) - G.coverQ e
noncomputable def coverS (e : E) : G.BeliefCover := G.coverU (G.snd e) - G.coverQ e
noncomputable def coverD (e : E) : G.BeliefCover :=
  1 - G.coverU (G.fst e) - G.coverU (G.snd e) + G.coverQ e
noncomputable def coverDen : G.BeliefCover :=
  (∏ i, G.coverU i) * (∏ i, (1 - G.coverU i)) * (∏ e, G.coverQ e) *
    (∏ e, G.coverR e) * (∏ e, G.coverS e) * ∏ e, G.coverD e

theorem cover_equation (e : E) :
    G.coverW e ^ 2 = G.coverQ e * G.coverD e * G.coverR e * G.coverS e := by
  simpa [coverW, coverQ, coverU, coverD, coverR, coverS, edgeRadicand]
    using EdgeCover.equation (MvPolynomial V ℂ) E
      (fun e => X (G.fst e)) (fun e => X (G.snd e)) e

noncomputable def coverToBelief : G.BeliefCover →ₐ[ℂ] G.BeliefRing := by
  let p := G.coverBeliefPoint
  let φ : MvPolynomial (E ⊕ E) (MvPolynomial V ℂ) →ₐ[ℂ] G.BeliefRing :=
    aevalTower (aeval p.u) (Sum.elim p.q
    (fun e => p.a e * (p.u (G.fst e) - p.q e) * (p.u (G.snd e) - p.q e)))
  exact Ideal.Quotient.liftₐ _ φ (by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨e, rfl⟩
      dsimp only [φ]
      simp only [edgeResidual, edgeRadicand, map_mul, map_pow, map_add, map_sub, map_one,
        Polynomial.aeval_X, Polynomial.aeval_C, MvPolynomial.algebraMap_eq,
        aevalTower_X, aevalTower_C, aeval_X, Sum.elim_inl, Sum.elim_inr]
      linear_combination (p.u (G.fst e) - p.q e) * (p.u (G.snd e) - p.q e) * p.equation e
    · exact map_zero _
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [smul_eq_mul, hx])

@[simp] theorem coverToBelief_mk (f : MvPolynomial (E ⊕ E) (MvPolynomial V ℂ)) :
    G.coverToBelief (Ideal.Quotient.mk _ f) =
      aevalTower (aeval G.coverBeliefPoint.u) (Sum.elim G.coverBeliefPoint.q
        (fun e => G.coverBeliefPoint.a e *
          (G.coverBeliefPoint.u (G.fst e) - G.coverBeliefPoint.q e) *
          (G.coverBeliefPoint.u (G.snd e) - G.coverBeliefPoint.q e))) f := rfl

@[simp] theorem coverToBelief_u (i : V) :
    G.coverToBelief (G.coverU i) = G.coverBeliefPoint.u i := by
  change G.coverToBelief (Ideal.Quotient.mk _ (C (X i))) = _
  rw [coverToBelief_mk]
  simp

@[simp] theorem coverToBelief_q (e : E) :
    G.coverToBelief (G.coverQ e) = G.coverBeliefPoint.q e := by
  change G.coverToBelief (Ideal.Quotient.mk _ (X (Sum.inl e))) = _
  rw [coverToBelief_mk]
  simp

@[simp] theorem coverToBelief_w (e : E) :
    G.coverToBelief (G.coverW e) = G.coverBeliefPoint.a e *
      (G.coverBeliefPoint.u (G.fst e) - G.coverBeliefPoint.q e) *
      (G.coverBeliefPoint.u (G.snd e) - G.coverBeliefPoint.q e) := by
  change G.coverToBelief (Ideal.Quotient.mk _ (X (Sum.inr e))) = _
  rw [coverToBelief_mk]
  simp

theorem coverToBelief_den_unit : IsUnit (G.coverToBelief G.coverDen) := by
  simp only [coverDen, coverR, coverS, coverD, map_mul, map_prod, map_sub, map_add,
    map_one, coverToBelief_u, coverToBelief_q]
  exact (((((IsUnit.prod_iff.mpr fun i _ => G.coverBeliefPoint.u_unit i).mul
    (IsUnit.prod_iff.mpr fun i _ => G.coverBeliefPoint.uc_unit i)).mul
    (IsUnit.prod_iff.mpr fun e _ => G.coverBeliefPoint.q_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => G.coverBeliefPoint.r_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => G.coverBeliefPoint.s_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => G.coverBeliefPoint.d_unit e)

theorem coverDen_ne_zero : G.coverDen ≠ 0 := by
  have : Nontrivial G.BeliefRing := G.symmetricBeliefPoint.toHom.toRingHom.domain_nontrivial
  intro h
  exact G.coverToBelief_den_unit.ne_zero (by rw [h, map_zero])

abbrev BeliefCoverOpen := Localization.Away G.coverDen

instance beliefCoverOpen_isDomain : IsDomain G.BeliefCoverOpen :=
  Localization.Away.isDomain G.coverDen_ne_zero

noncomputable def coverOpenU (i : V) : G.BeliefCoverOpen := algebraMap _ _ (G.coverU i)
noncomputable def coverOpenQ (e : E) : G.BeliefCoverOpen := algebraMap _ _ (G.coverQ e)
noncomputable def coverOpenW (e : E) : G.BeliefCoverOpen := algebraMap _ _ (G.coverW e)
noncomputable def coverOpenR (e : E) : G.BeliefCoverOpen := G.coverOpenU (G.fst e) - G.coverOpenQ e
noncomputable def coverOpenS (e : E) : G.BeliefCoverOpen := G.coverOpenU (G.snd e) - G.coverOpenQ e
noncomputable def coverOpenD (e : E) : G.BeliefCoverOpen :=
  1 - G.coverOpenU (G.fst e) - G.coverOpenU (G.snd e) + G.coverOpenQ e

theorem coverOpen_unit_factors :
    (∀ i, IsUnit (G.coverOpenU i)) ∧ (∀ i, IsUnit (1 - G.coverOpenU i)) ∧
    (∀ e, IsUnit (G.coverOpenQ e)) ∧ (∀ e, IsUnit (G.coverOpenR e)) ∧
    (∀ e, IsUnit (G.coverOpenS e)) ∧ (∀ e, IsUnit (G.coverOpenD e)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := G.BeliefCoverOpen) G.coverDen
  simp only [coverDen, coverR, coverS, coverD, map_mul, map_prod, RingHom.map_sub,
    RingHom.map_one, RingHom.map_add, IsUnit.mul_iff, IsUnit.prod_univ_iff] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem coverOpen_equation (e : E) :
    G.coverOpenW e ^ 2 = G.coverOpenQ e * G.coverOpenD e * G.coverOpenR e * G.coverOpenS e := by
  simpa only [coverOpenW, coverOpenQ, coverOpenU, coverOpenR, coverOpenS, coverOpenD,
    coverR, coverS, coverD, map_mul, map_pow, RingHom.map_add, RingHom.map_sub,
    RingHom.map_one] using congrArg (algebraMap G.BeliefCover G.BeliefCoverOpen)
      (G.cover_equation e)

noncomputable def coverOpenPoint : BeliefPoint G G.BeliefCoverOpen := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.coverOpen_unit_factors
  refine
    { a := fun e => G.coverOpenW e * (G.coverOpenR e)⁻¹ʳ * (G.coverOpenS e)⁻¹ʳ
      u := G.coverOpenU
      q := G.coverOpenQ
      a_unit := ?_
      u_unit := hu
      uc_unit := huc
      q_unit := hq
      r_unit := hr
      s_unit := hs
      d_unit := hd
      equation := ?_ }
  · intro e
    have hw : IsUnit (G.coverOpenW e) := by
      apply (isUnit_pow_iff (n := 2) (by decide)).mp
      rw [G.coverOpen_equation]
      exact (((hq e).mul (hd e)).mul (hr e)).mul (hs e)
    exact (hw.mul (unit_ringInverse (hr e))).mul (unit_ringInverse (hs e))
  · intro e
    change (_ * _ * _) ^ 2 * G.coverOpenR e * G.coverOpenS e =
      G.coverOpenQ e * G.coverOpenD e
    have hri := Ring.mul_inverse_cancel _ (hr e)
    have hsi := Ring.mul_inverse_cancel _ (hs e)
    calc
      _ = (G.coverOpenW e ^ 2) * (G.coverOpenR e * (G.coverOpenR e)⁻¹ʳ) *
          (G.coverOpenS e * (G.coverOpenS e)⁻¹ʳ) * (G.coverOpenR e)⁻¹ʳ *
          (G.coverOpenS e)⁻¹ʳ := by ring
      _ = (G.coverOpenW e ^ 2) * (G.coverOpenR e)⁻¹ʳ * (G.coverOpenS e)⁻¹ʳ := by
          rw [hri, hsi]; ring
      _ = (G.coverOpenQ e * G.coverOpenD e) * (G.coverOpenR e * (G.coverOpenR e)⁻¹ʳ) *
          (G.coverOpenS e * (G.coverOpenS e)⁻¹ʳ) := by rw [G.coverOpen_equation]; ring
      _ = _ := by rw [hri, hsi]; ring

noncomputable def coverOpenToBelief : G.BeliefCoverOpen →ₐ[ℂ] G.BeliefRing :=
  IsLocalization.Away.liftAlgHom G.coverDen G.coverToBelief_den_unit

@[simp] theorem coverOpenToBelief_map (x : G.BeliefCover) :
    G.coverOpenToBelief (algebraMap G.BeliefCover G.BeliefCoverOpen x) = G.coverToBelief x :=
  IsLocalization.Away.lift_eq _ G.coverToBelief_den_unit _

@[simp] theorem coverOpenToBelief_u (i : V) :
    G.coverOpenToBelief (G.coverOpenU i) = G.coverBeliefPoint.u i := by
  simp [coverOpenU]

@[simp] theorem coverOpenToBelief_q (e : E) :
    G.coverOpenToBelief (G.coverOpenQ e) = G.coverBeliefPoint.q e := by
  simp [coverOpenQ]

@[simp] theorem coverOpenToBelief_r (e : E) :
    G.coverOpenToBelief (G.coverOpenR e) = G.coverBeliefPoint.u (G.fst e) - G.coverBeliefPoint.q e := by
  simp [coverOpenR]

@[simp] theorem coverOpenToBelief_s (e : E) :
    G.coverOpenToBelief (G.coverOpenS e) = G.coverBeliefPoint.u (G.snd e) - G.coverBeliefPoint.q e := by
  simp [coverOpenS]

theorem coverOpenPoint_map :
    G.coverOpenPoint.map G.coverOpenToBelief.toRingHom = G.coverBeliefPoint := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.coverOpen_unit_factors
  ext i
  · change G.coverOpenToBelief
      (G.coverOpenW i * (G.coverOpenR i)⁻¹ʳ * (G.coverOpenS i)⁻¹ʳ) = G.coverBeliefPoint.a i
    simp only [map_mul, (hr i).map_ringInverse G.coverOpenToBelief,
      (hs i).map_ringInverse G.coverOpenToBelief, coverOpenToBelief_r,
      coverOpenToBelief_s, coverOpenW, coverOpenToBelief_map, coverToBelief_w]
    have hri := Ring.mul_inverse_cancel _ (G.coverBeliefPoint.r_unit i)
    have hsi := Ring.mul_inverse_cancel _ (G.coverBeliefPoint.s_unit i)
    calc
      _ = G.coverBeliefPoint.a i *
          ((G.coverBeliefPoint.u (G.fst i) - G.coverBeliefPoint.q i) *
            (G.coverBeliefPoint.u (G.fst i) - G.coverBeliefPoint.q i)⁻¹ʳ) *
          ((G.coverBeliefPoint.u (G.snd i) - G.coverBeliefPoint.q i) *
            (G.coverBeliefPoint.u (G.snd i) - G.coverBeliefPoint.q i)⁻¹ʳ) := by ring
      _ = _ := by rw [hri, hsi]; ring
  · change G.coverOpenToBelief (G.coverOpenU i) = G.coverBeliefPoint.u i
    simp [coverOpenU]
  · change G.coverOpenToBelief (G.coverOpenQ i) = G.coverBeliefPoint.q i
    simp [coverOpenQ]

/-- The belief ring embeds in an open subset of independent edge double covers. -/
theorem coverOpenPoint_toHom_injective : Function.Injective G.coverOpenPoint.toHom := by
  have h : G.coverOpenToBelief.comp G.coverOpenPoint.toHom = AlgHom.id ℂ G.BeliefRing := by
    rw [← BeliefPoint.map_toHom, G.coverOpenPoint_map]
    exact G.toHom_beliefPointOfHom _
  apply Function.LeftInverse.injective (g := G.coverOpenToBelief)
  intro x
  exact congrArg (fun f : G.BeliefRing →ₐ[ℂ] G.BeliefRing => f x) h

/-- The normalized-belief coordinate ring is a domain. -/
theorem beliefRing_isDomain : IsDomain G.BeliefRing :=
  G.coverOpenPoint_toHom_injective.isDomain G.coverOpenPoint.toHom.toRingHom

/-- The original admissible BP coordinate ring is also a domain. -/
theorem familyRing_domain : IsDomain G.FamilyRing := by
  have := G.beliefRing_isDomain
  exact G.familyRingEquivBeliefRing.injective.isDomain G.familyRingEquivBeliefRing.toRingHom

end BPFixedPoints.Multigraph
