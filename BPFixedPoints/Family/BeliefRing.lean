import BPFixedPoints.Family.Beliefs

/-!
# Coordinate ring of normalized beliefs

Promote the natural bijection between admissible BP points and belief points
to an actual ℂ-algebra isomorphism between `FamilyRing` and the belief ring.
Keep the original BP ring definition and verify the inverse homomorphisms
on every coordinate.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial BP
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- Belief coordinates: coupling a, vertex beliefs u and edge beliefs q. -/
abbrev BelVar (V E : Type) := E ⊕ V ⊕ E

noncomputable def belA (e : E) : MvPolynomial (BelVar V E) ℂ := X (Sum.inl e)
noncomputable def belU (i : V) : MvPolynomial (BelVar V E) ℂ := X (Sum.inr (Sum.inl i))
noncomputable def belQ (e : E) : MvPolynomial (BelVar V E) ℂ := X (Sum.inr (Sum.inr e))
noncomputable def belR (e : E) : MvPolynomial (BelVar V E) ℂ := belU (G.fst e) - belQ e
noncomputable def belS (e : E) : MvPolynomial (BelVar V E) ℂ := belU (G.snd e) - belQ e
noncomputable def belD (e : E) : MvPolynomial (BelVar V E) ℂ :=
  1 - belU (G.fst e) - belU (G.snd e) + belQ e
noncomputable def belResidual (e : E) : MvPolynomial (BelVar V E) ℂ :=
  belA e ^ 2 * G.belR e * G.belS e - belQ e * G.belD e
noncomputable def belDen : MvPolynomial (BelVar V E) ℂ :=
  (∏ e, belA e) * (∏ i, belU i) * (∏ i, (1 - belU i)) *
    (∏ e, belQ e) * (∏ e, G.belR e) * (∏ e, G.belS e) * ∏ e, G.belD e

/-- Coordinate ring of a²rs=qd on the open set of nonzero beliefs. -/
abbrev BeliefRing :=
  Localization.Away G.belDen ⧸
    Ideal.span (Set.range fun e => algebraMap _ (Localization.Away G.belDen) (G.belResidual e))

namespace BeliefPoint

variable {G} {R : Type*} [CommRing R] [Algebra ℂ R] (p : BeliefPoint G R)

def val : BelVar V E → R := Sum.elim p.a (Sum.elim p.u p.q)

@[simp] theorem eval_a (e : E) : aeval p.val (belA (V := V) e) = p.a e := by
  simp [belA, val]
@[simp] theorem eval_u (i : V) : aeval p.val (belU (E := E) i) = p.u i := by
  simp [belU, val]
@[simp] theorem eval_q (e : E) : aeval p.val (belQ (V := V) e) = p.q e := by
  simp [belQ, val]
@[simp] theorem eval_r (e : E) : aeval p.val (G.belR e) = p.u (G.fst e) - p.q e := by
  simp [belR]
@[simp] theorem eval_s (e : E) : aeval p.val (G.belS e) = p.u (G.snd e) - p.q e := by
  simp [belS]
@[simp] theorem eval_d (e : E) : aeval p.val (G.belD e) = p.d e := by
  simp [belD, d]

theorem eval_den_unit : IsUnit (aeval p.val G.belDen) := by
  simp only [belDen, map_mul, map_prod, map_sub, map_one, eval_a, eval_u, eval_q,
    eval_r, eval_s, eval_d]
  exact ((((((IsUnit.prod_iff.mpr fun e _ => p.a_unit e).mul
    (IsUnit.prod_iff.mpr fun i _ => p.u_unit i)).mul
    (IsUnit.prod_iff.mpr fun i _ => p.uc_unit i)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.q_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.r_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.s_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.d_unit e)

noncomputable def toLocalization : Localization.Away G.belDen →ₐ[ℂ] R :=
  IsLocalization.Away.liftAlgHom _ p.eval_den_unit

@[simp] theorem toLocalization_map (f : MvPolynomial (BelVar V E) ℂ) :
    p.toLocalization (algebraMap _ (Localization.Away G.belDen) f) = aeval p.val f :=
  IsLocalization.Away.lift_eq _ p.eval_den_unit _

noncomputable def toHom : G.BeliefRing →ₐ[ℂ] R :=
  Ideal.Quotient.liftₐ _ p.toLocalization <| by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨e, rfl⟩
      simp [belResidual, d, p.equation]
    · exact map_zero _
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro a x _ hx; simp [smul_eq_mul, hx]

@[simp] theorem toHom_map (f : MvPolynomial (BelVar V E) ℂ) :
    p.toHom (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing f) = aeval p.val f := by
  exact p.toLocalization_map f

end BeliefPoint

section Universal

variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem beliefRing_hom_ext {f g : G.BeliefRing →ₐ[ℂ] R}
    (h : ∀ i, f (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (X i)) =
      g (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (Submonoid.powers G.belDen)
  exact MvPolynomial.algHom_ext h

theorem beliefRing_den_unit :
    IsUnit (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing G.belDen) := by
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away G.belDen)
    G.belDen).map (algebraMap (Localization.Away G.belDen) G.BeliefRing)

theorem beliefRing_residual (e : E) :
    algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (G.belResidual e) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨e, rfl⟩

noncomputable def beliefPointOfHom (f : G.BeliefRing →ₐ[ℂ] R) : BeliefPoint G R := by
  let φ := f.comp (IsScalarTower.toAlgHom ℂ (MvPolynomial (BelVar V E) ℂ) G.BeliefRing)
  have hu := (G.beliefRing_den_unit).map f
  change IsUnit (φ G.belDen) at hu
  simp only [belDen, map_mul, map_prod, map_sub, map_one, IsUnit.mul_iff,
    IsUnit.prod_univ_iff] at hu
  refine ⟨fun e => φ (belA e), fun i => φ (belU i), fun e => φ (belQ e),
    hu.1.1.1.1.1.1, hu.1.1.1.1.1.2, hu.1.1.1.1.2, hu.1.1.1.2, ?_, ?_, ?_, ?_⟩
  · intro e; simpa [belR] using hu.1.1.2 e
  · intro e; simpa [belS] using hu.1.2 e
  · intro e; simpa [belD] using hu.2 e
  · intro e
    have h := congrArg f (G.beliefRing_residual e)
    change φ (G.belResidual e) = f 0 at h
    simpa [belResidual, belR, belS, belD, sub_eq_zero] using h

@[simp] theorem beliefPointOfHom_a (f : G.BeliefRing →ₐ[ℂ] R) (e : E) :
    (G.beliefPointOfHom f).a e = f (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (belA e)) := rfl
@[simp] theorem beliefPointOfHom_u (f : G.BeliefRing →ₐ[ℂ] R) (i : V) :
    (G.beliefPointOfHom f).u i = f (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (belU i)) := rfl
@[simp] theorem beliefPointOfHom_q (f : G.BeliefRing →ₐ[ℂ] R) (e : E) :
    (G.beliefPointOfHom f).q e = f (algebraMap (MvPolynomial (BelVar V E) ℂ) G.BeliefRing (belQ e)) := rfl

@[simp] theorem toHom_beliefPointOfHom (f : G.BeliefRing →ₐ[ℂ] R) :
    (G.beliefPointOfHom f).toHom = f := by
  apply G.beliefRing_hom_ext
  intro i
  rw [BeliefPoint.toHom_map, MvPolynomial.aeval_X]
  rcases i with e | i | e <;> rfl

theorem BeliefPoint.map_toHom (p : BeliefPoint G R) {S : Type*} [CommRing S] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) : (p.map φ.toRingHom).toHom = φ.comp p.toHom := by
  apply G.beliefRing_hom_ext
  intro i
  simp only [AlgHom.comp_apply, BeliefPoint.toHom_map, MvPolynomial.aeval_X]
  rcases i with e | i | e <;> rfl

@[simp] theorem beliefPointOfHom_toHom (p : BeliefPoint G R) : G.beliefPointOfHom p.toHom = p := by
  ext i <;> simp

@[simp] theorem familyPointOfHom_toHom (p : G.FamilyPoint R) : G.familyPointOfHom p.toHom = p := by
  ext i <;> simp

theorem beliefPointOfHom_map (f : G.BeliefRing →ₐ[ℂ] R)
    {S : Type*} [CommRing S] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) :
    (G.beliefPointOfHom f).map φ.toRingHom = G.beliefPointOfHom (φ.comp f) := by
  ext i <;> rfl

theorem familyPointOfHom_map (f : G.FamilyRing →ₐ[ℂ] R)
    {S : Type*} [CommRing S] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) :
    (G.familyPointOfHom f).map φ.toRingHom = G.familyPointOfHom (φ.comp f) := by
  ext i <;> rfl

end Universal

theorem FamilyPoint.toBelief_map {R S : Type*} [CommRing R] [CommRing S]
    (p : G.FamilyPoint R) (φ : R →+* S) : (p.map φ).toBelief = p.toBelief.map φ := by
  have h := congrArg FamilyPoint.toBelief (p.toBelief.toFamily_map φ)
  rw [BeliefPoint.toBelief_toFamily, FamilyPoint.toFamily_toBelief] at h
  exact h.symm

/-- Homomorphism evaluating BP coordinates in belief coordinates. -/
noncomputable def familyToBeliefRing : G.FamilyRing →ₐ[ℂ] G.BeliefRing :=
  (G.beliefPointOfHom (AlgHom.id ℂ G.BeliefRing)).toFamily.toHom

/-- Homomorphism evaluating belief coordinates in BP coordinates. -/
noncomputable def beliefToFamilyRing : G.BeliefRing →ₐ[ℂ] G.FamilyRing :=
  (G.familyPointOfHom (AlgHom.id ℂ G.FamilyRing)).toBelief.toHom

theorem beliefToFamilyRing_comp_familyToBeliefRing :
    G.beliefToFamilyRing.comp G.familyToBeliefRing = AlgHom.id ℂ G.FamilyRing := by
  change G.beliefToFamilyRing.comp
    (G.beliefPointOfHom (AlgHom.id ℂ G.BeliefRing)).toFamily.toHom = _
  rw [← FamilyPoint.map_toHom, ← BeliefPoint.toFamily_map, G.beliefPointOfHom_map]
  simp only [AlgHom.comp_id, beliefToFamilyRing, G.beliefPointOfHom_toHom,
    FamilyPoint.toFamily_toBelief, G.toHom_familyPointOfHom]

theorem familyToBeliefRing_comp_beliefToFamilyRing :
    G.familyToBeliefRing.comp G.beliefToFamilyRing = AlgHom.id ℂ G.BeliefRing := by
  change G.familyToBeliefRing.comp
    (G.familyPointOfHom (AlgHom.id ℂ G.FamilyRing)).toBelief.toHom = _
  rw [← BeliefPoint.map_toHom, ← FamilyPoint.toBelief_map, G.familyPointOfHom_map]
  simp only [AlgHom.comp_id, familyToBeliefRing, G.familyPointOfHom_toHom,
    BeliefPoint.toBelief_toFamily, G.toHom_beliefPointOfHom]

/-- ℂ-algebra isomorphism between the original admissible BP coordinate ring and the normalized-belief ring. -/
noncomputable def familyRingEquivBeliefRing : G.FamilyRing ≃ₐ[ℂ] G.BeliefRing :=
  AlgEquiv.ofAlgHom G.familyToBeliefRing G.beliefToFamilyRing
    (G.familyToBeliefRing_comp_beliefToFamilyRing) (G.beliefToFamilyRing_comp_familyToBeliefRing)

end BPFixedPoints.Multigraph
