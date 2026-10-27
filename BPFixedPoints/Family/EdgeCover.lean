import BPFixedPoints.Family.EdgePolynomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Fintype.Option

/-!
# Double covers with independent edge variables

Add variables qₑ,wₑ for each edge and impose
wₑ²=qₑ(1−uₑ−vₑ+qₑ)(uₑ−qₑ)(vₑ−qₑ).
Prove the resulting ring is a domain by adjoining edges successively and using
Eisenstein's criterion.
-/

namespace BPFixedPoints

variable (R : Type*) [CommRing R] (E : Type*) (u v : E → R)

noncomputable def edgeResidual (e : E) : MvPolynomial (E ⊕ E) R :=
  MvPolynomial.X (Sum.inr e) ^ 2 -
    Polynomial.aeval (MvPolynomial.X (Sum.inl e)) (edgeRadicand (u e) (v e))

abbrev EdgeCover := MvPolynomial (E ⊕ E) R ⧸ Ideal.span (Set.range (edgeResidual R E u v))

namespace EdgeCover

noncomputable def q (e : E) : EdgeCover R E u v :=
  algebraMap (MvPolynomial (E ⊕ E) R) _ (MvPolynomial.X (Sum.inl e))
noncomputable def w (e : E) : EdgeCover R E u v :=
  algebraMap (MvPolynomial (E ⊕ E) R) _ (MvPolynomial.X (Sum.inr e))

theorem equation (e : E) : w R E u v e ^ 2 =
    Polynomial.aeval (q R E u v e) (edgeRadicand (u e) (v e)) := by
  have h : algebraMap (MvPolynomial (E ⊕ E) R) (EdgeCover R E u v)
      (edgeResidual R E u v e) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)
  let φ := IsScalarTower.toAlgHom R (MvPolynomial (E ⊕ E) R) (EdgeCover R E u v)
  change φ (edgeResidual R E u v e) = 0 at h
  change φ (MvPolynomial.X (Sum.inr e)) ^ 2 =
    Polynomial.aeval (φ (MvPolynomial.X (Sum.inl e))) (edgeRadicand (u e) (v e))
  simpa only [edgeResidual, map_sub, map_pow, sub_eq_zero,
    ← Polynomial.aeval_algHom_apply] using h

variable {S : Type*} [CommRing S] [Algebra R S]

noncomputable def lift (x y : E → S)
    (h : ∀ e, y e ^ 2 = Polynomial.aeval (x e) (edgeRadicand (u e) (v e))) :
    EdgeCover R E u v →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (Sum.elim x y)) <| by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨e, rfl⟩
      simpa only [edgeResidual, map_sub, map_pow, sub_eq_zero,
        ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, Sum.elim_inl,
        Sum.elim_inr] using h e
    · exact map_zero _
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro a b _ hb; simp [smul_eq_mul, hb]

@[simp] theorem lift_q (x y : E → S) (h) (e : E) :
    lift R E u v x y h (q R E u v e) = x e := by
  change MvPolynomial.aeval (Sum.elim x y) (MvPolynomial.X (Sum.inl e)) = x e
  simp
@[simp] theorem lift_w (x y : E → S) (h) (e : E) :
    lift R E u v x y h (w R E u v e) = y e := by
  change MvPolynomial.aeval (Sum.elim x y) (MvPolynomial.X (Sum.inr e)) = y e
  simp

theorem hom_ext {f g : EdgeCover R E u v →ₐ[R] S}
    (hq : ∀ e, f (q R E u v e) = g (q R E u v e))
    (hw : ∀ e, f (w R E u v e) = g (w R E u v e)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro (e | e)
  · exact hq e
  · exact hw e

noncomputable def zeroHom : EdgeCover R E u v →ₐ[R] R :=
  lift R E u v (fun _ => 0) (fun _ => 0) (by intro e; simp [edgeRadicand])

theorem algebraMap_injective : Function.Injective (algebraMap R (EdgeCover R E u v)) := by
  have h : Function.LeftInverse (zeroHom R E u v) (algebraMap R (EdgeCover R E u v)) :=
    fun x => (zeroHom R E u v).commutes x
  exact h.injective

noncomputable def renameEquiv {F : Type*} (e : E ≃ F) :
    EdgeCover R E u v ≃ₐ[R] EdgeCover R F (u ∘ e.symm) (v ∘ e.symm) := by
  let f := lift R E u v (fun i => q R F (u ∘ e.symm) (v ∘ e.symm) (e i))
    (fun i => w R F (u ∘ e.symm) (v ∘ e.symm) (e i)) (by
      intro i
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
        equation R F (u ∘ e.symm) (v ∘ e.symm) (e i))
  let g := lift R F (u ∘ e.symm) (v ∘ e.symm) (fun i => q R E u v (e.symm i))
    (fun i => w R E u v (e.symm i)) (by intro i; exact equation R E u v (e.symm i))
  exact AlgEquiv.ofAlgHom f g
    (by apply hom_ext <;> intro i <;> simp [f, g])
    (by apply hom_ext <;> intro i <;> simp [f, g])

theorem isDomain_empty [IsDomain R] [IsEmpty E] : IsDomain (EdgeCover R E u v) := by
  have h : (Algebra.ofId R (EdgeCover R E u v)).comp (zeroHom R E u v) =
      AlgHom.id R (EdgeCover R E u v) := by
    apply hom_ext <;> exact fun e => isEmptyElim e
  apply Function.Injective.isDomain (zeroHom R E u v)
  exact (show Function.LeftInverse (algebraMap R (EdgeCover R E u v))
    (zeroHom R E u v) from fun x => congrArg (fun f : EdgeCover R E u v →ₐ[R]
      EdgeCover R E u v => f x) h).injective

section Option

variable (u v : Option E → R)

abbrev Old := EdgeCover R E (u ∘ some) (v ∘ some)
abbrev Step := AdjoinRoot (edgePolynomial
  (algebraMap R (Old R E u v) (u none)) (algebraMap R (Old R E u v) (v none)))

noncomputable def optionToStep : EdgeCover R (Option E) u v →ₐ[R] Step R E u v :=
  lift R (Option E) u v
    (fun i => match i with
      | none => algebraMap (Polynomial (Old R E u v)) (Step R E u v) (Polynomial.X : Polynomial (Old R E u v))
      | some e => algebraMap (Old R E u v) (Step R E u v) (q R E (u ∘ some) (v ∘ some) e))
    (fun i => match i with
      | none => AdjoinRoot.root _
      | some e => algebraMap (Old R E u v) (Step R E u v) (w R E (u ∘ some) (v ∘ some) e)) (by
        intro i
        cases i with
        | none =>
          let f := edgePolynomial (algebraMap R (Old R E u v) (u none))
            (algebraMap R (Old R E u v) (v none))
          have h := AdjoinRoot.eval₂_root f
          change Polynomial.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f)
            (Polynomial.X ^ 2 - Polynomial.C (edgeRadicand
              (algebraMap R (Old R E u v) (u none))
              (algebraMap R (Old R E u v) (v none)))) = 0 at h
          rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
            Polynomial.eval₂_C, sub_eq_zero] at h
          change AdjoinRoot.root f ^ 2 =
            algebraMap (Polynomial (Old R E u v)) (Step R E u v)
              (edgeRadicand (algebraMap R (Old R E u v) (u none))
                (algebraMap R (Old R E u v) (v none))) at h
          have hc (x : Old R E u v) :
              algebraMap (Polynomial (Old R E u v)) (Step R E u v) (Polynomial.C x) =
                algebraMap (Old R E u v) (Step R E u v) x :=
            (IsScalarTower.algebraMap_apply (Old R E u v)
              (Polynomial (Old R E u v)) (Step R E u v) x).symm
          have hR (x : R) : algebraMap (Old R E u v) (Step R E u v)
              (algebraMap R (Old R E u v) x) = algebraMap R (Step R E u v) x :=
            (IsScalarTower.algebraMap_apply R (Old R E u v) (Step R E u v) x).symm
          simpa only [edgeRadicand, RingHom.map_mul, RingHom.map_add,
            RingHom.map_sub, RingHom.map_one, Polynomial.aeval_mul,
            Polynomial.aeval_add, Polynomial.aeval_sub, Polynomial.aeval_X,
            Polynomial.aeval_C, hc, hR, map_sub, map_one] using h
        | some e =>
          let φ := IsScalarTower.toAlgHom R (Old R E u v) (Step R E u v)
          calc
            _ = φ (w R E (u ∘ some) (v ∘ some) e ^ 2) := (map_pow φ _ 2).symm
            _ = φ (Polynomial.aeval (q R E (u ∘ some) (v ∘ some) e)
                (edgeRadicand (u (some e)) (v (some e)))) :=
              congrArg φ (equation R E (u ∘ some) (v ∘ some) e)
            _ = _ := (Polynomial.aeval_algHom_apply φ _ _).symm)

noncomputable def oldToOption : Old R E u v →ₐ[R] EdgeCover R (Option E) u v :=
  lift R E (u ∘ some) (v ∘ some) (fun e => q R (Option E) u v (some e))
    (fun e => w R (Option E) u v (some e)) (fun e => equation R (Option E) u v (some e))

noncomputable def stepToOption : Step R E u v →ₐ[R] EdgeCover R (Option E) u v :=
  AdjoinRoot.liftAlgHom _
    (Polynomial.aevalTower (oldToOption R E u v) (q R (Option E) u v none))
    (w R (Option E) u v none) (by
      have h := equation R (Option E) u v none
      simpa [edgePolynomial, edgeRadicand, sub_eq_zero] using h)

@[simp] theorem optionToStep_w_none :
    optionToStep R E u v (w R (Option E) u v none) = AdjoinRoot.root _ := by
  simp [optionToStep]
@[simp] theorem optionToStep_q_some (e : E) :
    optionToStep R E u v (q R (Option E) u v (some e)) =
      algebraMap (Old R E u v) (Step R E u v) (q R E (u ∘ some) (v ∘ some) e) := by
  simp [optionToStep]
@[simp] theorem optionToStep_w_some (e : E) :
    optionToStep R E u v (w R (Option E) u v (some e)) =
      algebraMap (Old R E u v) (Step R E u v) (w R E (u ∘ some) (v ∘ some) e) := by
  simp [optionToStep]

@[simp] theorem stepToOption_root :
    stepToOption R E u v (AdjoinRoot.root _) = w R (Option E) u v none := by
  simp [stepToOption]
@[simp] theorem stepToOption_algebraMap (x : Old R E u v) :
    stepToOption R E u v (algebraMap (Old R E u v) (Step R E u v) x) =
      oldToOption R E u v x := by
  rw [IsScalarTower.algebraMap_apply (Old R E u v)
    (Polynomial (Old R E u v)) (Step R E u v)]
  simp [stepToOption, AdjoinRoot.algebraMap_eq]

theorem stepToOption_comp_optionToStep :
    (stepToOption R E u v).comp (optionToStep R E u v) =
      AlgHom.id R (EdgeCover R (Option E) u v) := by
  apply hom_ext
  · intro i
    cases i with
    | none => simp [optionToStep, stepToOption, AdjoinRoot.algebraMap_eq]
    | some e => simp [oldToOption]
  · intro i
    cases i <;> simp [oldToOption]

theorem isDomain_option [IsDomain R] [IsDomain (Old R E u v)]
    (hu : u none ≠ 0) (hv : v none ≠ 0) (huv : 1 - u none - v none ≠ 0) :
    IsDomain (EdgeCover R (Option E) u v) := by
  have hinj := algebraMap_injective R E (u ∘ some) (v ∘ some)
  letI : IsDomain (Step R E u v) := edgeAdjoin_isDomain _ _
    (fun h => hu (hinj (by simpa using h)))
    (fun h => hv (hinj (by simpa using h)))
    (fun h => huv (hinj (by simpa using h)))
  apply Function.Injective.isDomain (optionToStep R E u v)
  exact (show Function.LeftInverse (stepToOption R E u v) (optionToStep R E u v) from
    fun x => congrArg (fun f : EdgeCover R (Option E) u v →ₐ[R]
      EdgeCover R (Option E) u v => f x) (stepToOption_comp_optionToStep R E u v)).injective

end Option

theorem isDomain [IsDomain R] [Finite E]
    (hu : ∀ e, u e ≠ 0) (hv : ∀ e, v e ≠ 0) (huv : ∀ e, 1 - u e - v e ≠ 0) :
    IsDomain (EdgeCover R E u v) := by
  induction E using Finite.induction_empty_option with
  | of_equiv e IH =>
    have h := IH (u ∘ e) (v ∘ e) (fun i => hu (e i)) (fun i => hv (e i))
      (fun i => huv (e i))
    let φ := renameEquiv R _ u v e.symm
    apply φ.toRingEquiv.isDomain_iff.mpr
    simpa only [Equiv.symm_symm] using h
  | h_empty => exact isDomain_empty R _ u v
  | @h_option E _ IH =>
    letI := IH (u ∘ some) (v ∘ some) (fun e => hu (some e))
      (fun e => hv (some e)) (fun e => huv (some e))
    exact isDomain_option R E u v (hu none) (hv none) (huv none)

end EdgeCover

end BPFixedPoints
