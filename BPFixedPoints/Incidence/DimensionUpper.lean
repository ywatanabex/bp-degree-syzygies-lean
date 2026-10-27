import BPFixedPoints.Incidence.Integral
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Coordinates of the coefficient image and an upper dimension bound

Restrict functions extending to every chart to the zero chart. On tree
components retain constant coefficients per edge; on cyclic components retain
vertex coordinates. This places the coefficient image in a subalgebra with
d_G generators. Integrality gives the same upper bound for the incidence ring.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial

set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable (G : Multigraph V E)

noncomputable def incidenceToChart : G.IncidenceRing →ₐ[ℂ]
    G.IncChartRing (fun _ => false) :=
  (AlgEquiv.ofInjective (G.incChartMap (fun _ => false))
    (G.incChartMap_injective (fun _ => false))).symm.toAlgHom.comp
      (Subalgebra.inclusion (iInf_le _ (fun _ => false)))

@[simp] theorem incChartMap_incidenceToChart (x : G.IncidenceRing) :
    G.incChartMap (fun _ => false) (G.incidenceToChart x) = x.val := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective (G.incChartMap (fun _ => false))
      (G.incChartMap_injective (fun _ => false))).apply_symm_apply
        (Subalgebra.inclusion (iInf_le _ (fun _ => false)) x))

theorem incidenceToChart_injective : Function.Injective G.incidenceToChart := by
  intro x y h
  apply Subtype.val_injective
  simpa using congrArg (G.incChartMap (fun _ => false)) h

/-- Injection from the intersection of all charts into the zero chart's free coordinates. -/
noncomputable def incidenceToFree : G.IncidenceRing →ₐ[ℂ] IncFreeRing V E :=
  G.incChartZeroEquiv.toAlgHom.comp G.incidenceToChart

theorem incidenceToFree_injective : Function.Injective G.incidenceToFree :=
  G.incChartZeroEquiv.injective.comp G.incidenceToChart_injective

@[simp] theorem incidenceToFree_coeffHom_X (e : E) (α β : Fin 2) :
    G.incidenceToFree (G.coeffHom (X (e, α, β))) = G.incFreeCoeff e α β := by
  have h : G.incidenceToChart (G.coeffHom (X (e, α, β))) =
      Ideal.Quotient.mk _ (X (Sum.inr (e, α, β))) := by
    apply G.incChartMap_injective (fun _ => false)
    simp [coeffHom, incChartMap_mk, incChartVal]
  change G.incChartZeroEquiv (G.incidenceToChart _) = _
  rw [h]
  change aeval G.incFreeVal (X (Sum.inr (e, α, β))) = _
  simp [incFreeVal]

/-- Coefficient map after eliminating constant coefficients on the zero chart. -/
noncomputable def coeffFreeHom : IncCoeffRing E →ₐ[ℂ] IncFreeRing V E :=
  aeval fun (e, α, β) => G.incFreeCoeff e α β

@[simp] theorem coeffFreeHom_X (e : E) (α β : Fin 2) :
    G.coeffFreeHom (X (e, α, β)) = G.incFreeCoeff e α β := aeval_X _ _

theorem incidenceToFree_comp_coeffHom :
    G.incidenceToFree.comp G.coeffHom = G.coeffFreeHom := by
  apply MvPolynomial.algHom_ext
  rintro ⟨e, α, β⟩
  simp

/-- The three free coefficients per edge, constant coefficients of tree edges, and vertex coordinates of non-tree components. -/
abbrev IncDimVar := (E × Fin 3) ⊕
  {e : E // G.IsTreeComp (G.compOf (G.fst e))} ⊕
  {v : V // ¬ G.IsTreeComp (G.compOf v)}

private theorem card_subtype_preimage {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (p : B → Prop) [DecidablePred p] :
    Fintype.card {a : A // p (f a)} =
      ∑ b, if p b then (Finset.univ.filter fun a => f a = b).card else 0 := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset A) (Finset.univ.filter p) f
  simpa [Finset.sum_filter, Fintype.card_subtype] using h.symm

theorem card_incDimVar : Fintype.card G.IncDimVar = G.dG := by
  have he := card_subtype_preimage (fun e => G.compOf (G.fst e)) G.IsTreeComp
  have hv := card_subtype_preimage G.compOf (fun K => ¬ G.IsTreeComp K)
  change Fintype.card {e : E // G.IsTreeComp (G.compOf (G.fst e))} =
    ∑ K, if G.IsTreeComp K then (G.compEdges K).card else 0 at he
  change Fintype.card {v : V // ¬ G.IsTreeComp (G.compOf v)} =
    ∑ K, if ¬ G.IsTreeComp K then (G.compVerts K).card else 0 at hv
  have hsum : (∑ K, if G.IsTreeComp K then (G.compEdges K).card else 0) +
      (∑ K, if ¬ G.IsTreeComp K then (G.compVerts K).card else 0) + G.tau =
      Fintype.card V := by
    rw [← G.sum_ite_isTreeComp, G.card_eq_sum_compVerts, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro K _
    by_cases hK : G.IsTreeComp K
    · simp only [ite_eq_left hK, ite_eq_right (not_not.mpr hK), add_zero]
      exact hK
    · simp [hK]
  simp only [IncDimVar, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [he, hv]
  unfold dG
  omega

noncomputable def incDimVal : G.IncDimVar → IncFreeRing V E
  | Sum.inl (e, k) => X (Sum.inr (e, k))
  | Sum.inr (Sum.inl e) => G.incFreeCoeff e.val 0 0
  | Sum.inr (Sum.inr v) => X (Sum.inl v.val)

noncomputable def incDimAlgebra : Subalgebra ℂ (IncFreeRing V E) :=
  Algebra.adjoin ℂ (Set.range G.incDimVal)

theorem incFreeCoeff_mem_incDimAlgebra (e : E) (α β : Fin 2) :
    G.incFreeCoeff e α β ∈ G.incDimAlgebra := by
  have hfree (k : Fin 3) : (X (Sum.inr (e, k)) : IncFreeRing V E) ∈ G.incDimAlgebra :=
    Algebra.subset_adjoin ⟨Sum.inl (e, k), rfl⟩
  by_cases hα : α = 0 <;> by_cases hβ : β = 0
  · subst α; subst β
    by_cases he : G.IsTreeComp (G.compOf (G.fst e))
    · exact Algebra.subset_adjoin ⟨Sum.inr (Sum.inl ⟨e, he⟩), rfl⟩
    · have hu : (X (Sum.inl (G.fst e)) : IncFreeRing V E) ∈ G.incDimAlgebra :=
        Algebra.subset_adjoin ⟨Sum.inr (Sum.inr ⟨G.fst e, he⟩), rfl⟩
      have hv : (X (Sum.inl (G.snd e)) : IncFreeRing V E) ∈ G.incDimAlgebra :=
        Algebra.subset_adjoin ⟨Sum.inr (Sum.inr ⟨G.snd e,
          by rwa [← G.compOf_fst_eq_snd e]⟩), rfl⟩
      simpa only [incFreeCoeff, ↓reduceIte] using
        G.incDimAlgebra.neg_mem (G.incDimAlgebra.add_mem
          (G.incDimAlgebra.add_mem (G.incDimAlgebra.mul_mem (hfree 0) hv)
            (G.incDimAlgebra.mul_mem (hfree 1) hu))
          (G.incDimAlgebra.mul_mem (G.incDimAlgebra.mul_mem (hfree 2) hu) hv))
  · simpa [incFreeCoeff, hα, hβ] using hfree 0
  · simpa [incFreeCoeff, hα, hβ] using hfree 1
  · simpa [incFreeCoeff, hα, hβ] using hfree 2

theorem coeffFreeHom_range_le_incDimAlgebra : G.coeffFreeHom.range ≤ G.incDimAlgebra := by
  rw [coeffFreeHom, aeval_range]
  apply Algebra.adjoin_le
  rintro _ ⟨⟨e, α, β⟩, rfl⟩
  exact G.incFreeCoeff_mem_incDimAlgebra e α β

theorem trdeg_incDimAlgebra_le : Algebra.trdeg ℂ G.incDimAlgebra ≤ (G.dG : Cardinal) := by
  let f : MvPolynomial G.IncDimVar ℂ →ₐ[ℂ] IncFreeRing V E := aeval G.incDimVal
  let e : f.range ≃ₐ[ℂ] G.incDimAlgebra :=
    Subalgebra.equivOfEq _ _ (aeval_range G.incDimVal)
  calc
    Algebra.trdeg ℂ G.incDimAlgebra = Algebra.trdeg ℂ f.range := e.trdeg_eq.symm
    _ ≤ Algebra.trdeg ℂ (MvPolynomial G.IncDimVar ℂ) :=
      trdeg_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective
    _ = (G.dG : Cardinal) := by simp [Cardinal.mk_fintype, G.card_incDimVar]

theorem trdeg_incidenceRing_le : Algebra.trdeg ℂ G.IncidenceRing ≤ (G.dG : Cardinal) := by
  have : IsDomain G.IncidenceRing := G.incidenceRing_isDomain
  have : Nontrivial G.coeffHom.range := G.coeffHom.range.val.toRingHom.domain_nontrivial
  have : FaithfulSMul ℂ G.coeffHom.range :=
    (faithfulSMul_iff_algebraMap_injective ℂ G.coeffHom.range).mpr
      (algebraMap ℂ G.coeffHom.range).injective
  have : FaithfulSMul G.coeffHom.range G.IncidenceRing :=
    (faithfulSMul_iff_algebraMap_injective G.coeffHom.range G.IncidenceRing).mpr
      Subtype.val_injective
  have : Algebra.IsIntegral G.coeffHom.range G.IncidenceRing :=
    ⟨RingHom.IsIntegral.tower_top G.coeffHom.rangeRestrict.toRingHom
      G.coeffHom.range.val.toRingHom G.coeffHom_isIntegral⟩
  have : Algebra.IsAlgebraic G.coeffHom.range G.IncidenceRing :=
    Algebra.IsIntegral.isAlgebraic
  have htr : Algebra.trdeg ℂ G.IncidenceRing = Algebra.trdeg ℂ G.coeffHom.range := by
    have h := trdeg_add_eq (A := G.IncidenceRing) ℂ G.coeffHom.range
    simpa [trdeg_eq_zero (R := G.coeffHom.range) (A := G.IncidenceRing)] using h.symm
  have hrange : G.coeffHom.range.map G.incidenceToFree = G.coeffFreeHom.range := by
    rw [← AlgHom.range_comp, G.incidenceToFree_comp_coeffHom]
  let e : G.coeffHom.range ≃ₐ[ℂ] G.coeffFreeHom.range :=
    (G.coeffHom.range.equivMapOfInjective G.incidenceToFree
      G.incidenceToFree_injective).trans (Subalgebra.equivOfEq _ _ hrange)
  rw [htr, e.trdeg_eq]
  exact (trdeg_le_of_injective
    (Subalgebra.inclusion G.coeffFreeHom_range_le_incDimAlgebra)
    (Subalgebra.inclusion_injective _)).trans G.trdeg_incDimAlgebra_le

end BPFixedPoints.Multigraph
