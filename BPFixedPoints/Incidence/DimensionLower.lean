import BPFixedPoints.Incidence.Chart
import BPFixedPoints.Incidence.Matching
import BPFixedPoints.Incidence.PolynomialIndependent
import BPFixedPoints.Degree.PolynomialDerivative

/-!
# An algebraically independent family of incidence coefficients

Take the three free coefficients and constant coefficients chosen by a
vertex-edge matching. Set the matched linear coefficients to one and other
linear coefficients to zero; the vertex derivative is the identity. The
inverse function theorem and polynomial identity theorem imply algebraic
independence of these d_G coefficients.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Indices of the three free coefficients and the matching's constant coefficients. -/
abbrev IncIndependentVar := (E × Fin 3) ⊕ G.matchingVerts

theorem card_incIndependentVar : Fintype.card G.IncIndependentVar = G.dG := by
  have h := G.card_matchingVerts_add_tau
  simp only [IncIndependentVar, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_coe]
  unfold dG
  omega

/-- Coefficient family whose algebraic independence is proved. -/
noncomputable def incIndependentFamily : G.IncIndependentVar → IncFreeRing V E
  | Sum.inl i => X (Sum.inr i)
  | Sum.inr v => G.incFreeCoeff (G.vertexEdgeMatching v) 0 0

/-- Indices of the independent family among the original four coefficients. -/
noncomputable def incIndependentCoeff : G.IncIndependentVar → IncCoeffIdx E
  | Sum.inl (e, k) => (e, if k = 0 then 0 else 1, if k = 1 then 0 else 1)
  | Sum.inr v => (G.vertexEdgeMatching v, 0, 0)

theorem incIndependentFamily_eq_coeff (i : G.IncIndependentVar) :
    G.incIndependentFamily i =
      G.incFreeCoeff (G.incIndependentCoeff i).1 (G.incIndependentCoeff i).2.1
        (G.incIndependentCoeff i).2.2 := by
  rcases i with ⟨e, k⟩ | v
  · fin_cases k <;> simp [incIndependentFamily, incIndependentCoeff, incFreeCoeff]
  · rfl

/-- Index of the linear coefficient multiplying the chosen vertex. -/
noncomputable def matchingOrientation (v : G.matchingVerts) : Fin 3 :=
  if G.fst (G.vertexEdgeMatching v) = v.val then 1 else 0

noncomputable def matchingCoeff (v : G.matchingVerts) : E × Fin 3 :=
  (G.vertexEdgeMatching v, G.matchingOrientation v)

/-- Derivative evaluation point: only matched linear coefficients are one. -/
noncomputable def incIndependentBase : G.IncIndependentVar → ℂ
  | Sum.inl i => if ∃ v, G.matchingCoeff v = i then 1 else 0
  | Sum.inr _ => 0

theorem incIndependentBase_selected (v : G.matchingVerts) (k : Fin 3) :
    G.incIndependentBase (Sum.inl (G.vertexEdgeMatching v, k)) =
      if k = G.matchingOrientation v then 1 else 0 := by
  classical
  have h : (∃ w, G.matchingCoeff w = (G.vertexEdgeMatching v, k)) ↔
      k = G.matchingOrientation v := by
    constructor
    · rintro ⟨w, hw⟩
      have hwv := G.vertexEdgeMatching.injective (congrArg Prod.fst hw)
      subst w
      exact (congrArg Prod.snd hw).symm
    · intro hk
      exact ⟨v, Prod.ext rfl hk.symm⟩
  simp only [incIndependentBase, h]

/-- Negate the input at selected vertices; fix unselected vertices at zero. -/
noncomputable def incVertexCLM (v : V) : (G.IncIndependentVar → ℂ) →L[ℂ] ℂ :=
  if hv : v ∈ G.matchingVerts then
    -ContinuousLinearMap.proj (Sum.inr (⟨v, hv⟩ : G.matchingVerts)) else 0

@[simp] theorem incVertexCLM_matching (v : G.matchingVerts) :
    G.incVertexCLM v = -ContinuousLinearMap.proj (Sum.inr v) := by
  simp [incVertexCLM, v.property]

@[simp] theorem incVertexCLM_base (v : V) : G.incVertexCLM v G.incIndependentBase = 0 := by
  classical
  unfold incVertexCLM
  split_ifs <;> simp [incIndependentBase]

/-- Square parameter family into the free chart. -/
noncomputable def incIndependentParam (z : G.IncIndependentVar → ℂ) : IncFreeVar V E → ℂ
  | Sum.inl v => G.incVertexCLM v z
  | Sum.inr i => z (Sum.inl i)

theorem incIndependentFamily_eval_inl (z : G.IncIndependentVar → ℂ) (i : E × Fin 3) :
    eval (G.incIndependentParam z) (G.incIndependentFamily (Sum.inl i)) = z (Sum.inl i) := by
  simp [incIndependentFamily, incIndependentParam]

theorem incIndependentFamily_eval_inr (z : G.IncIndependentVar → ℂ) (v : G.matchingVerts) :
    eval (G.incIndependentParam z) (G.incIndependentFamily (Sum.inr v)) =
      -(z (Sum.inl (G.vertexEdgeMatching v, 0)) *
          G.incVertexCLM (G.snd (G.vertexEdgeMatching v)) z +
        z (Sum.inl (G.vertexEdgeMatching v, 1)) *
          G.incVertexCLM (G.fst (G.vertexEdgeMatching v)) z +
        z (Sum.inl (G.vertexEdgeMatching v, 2)) *
          G.incVertexCLM (G.fst (G.vertexEdgeMatching v)) z *
          G.incVertexCLM (G.snd (G.vertexEdgeMatching v)) z) := by
  simp [incIndependentFamily, incFreeCoeff, incIndependentParam]

theorem incIndependent_derivative_selected (v : G.matchingVerts) :
    -(G.incIndependentBase (Sum.inl (G.vertexEdgeMatching v, 0)) •
        G.incVertexCLM (G.snd (G.vertexEdgeMatching v)) +
      G.incIndependentBase (Sum.inl (G.vertexEdgeMatching v, 1)) •
        G.incVertexCLM (G.fst (G.vertexEdgeMatching v))) =
      ContinuousLinearMap.proj (Sum.inr v) := by
  classical
  ext z
  by_cases h : G.fst (G.vertexEdgeMatching v) = v.val
  · simp [incIndependentBase_selected, matchingOrientation, h, smul_eq_mul]
  · have hs : G.snd (G.vertexEdgeMatching v) = v.val :=
      (G.incident_vertexEdgeMatching v).resolve_left h
    simp [incIndependentBase_selected, matchingOrientation, h, hs, smul_eq_mul]

/-- The strict derivative of the selected-coefficient map is the identity. -/
theorem incIndependentFamily_hasStrictFDerivAt :
    HasStrictFDerivAt
      (fun z i => eval (G.incIndependentParam z) (G.incIndependentFamily i))
      (ContinuousLinearMap.id ℂ (G.IncIndependentVar → ℂ)) G.incIndependentBase := by
  classical
  apply hasStrictFDerivAt_pi'.mpr
  intro i
  simp only [ContinuousLinearMap.comp_id]
  rcases i with i | v
  · simpa only [G.incIndependentFamily_eval_inl] using
      hasStrictFDerivAt_apply (𝕜 := ℂ) (Sum.inl i) G.incIndependentBase
  · have hA := hasStrictFDerivAt_apply (𝕜 := ℂ)
      (Sum.inl (G.vertexEdgeMatching v, 0)) G.incIndependentBase
    have hB := hasStrictFDerivAt_apply (𝕜 := ℂ)
      (Sum.inl (G.vertexEdgeMatching v, 1)) G.incIndependentBase
    have hC := hasStrictFDerivAt_apply (𝕜 := ℂ)
      (Sum.inl (G.vertexEdgeMatching v, 2)) G.incIndependentBase
    have hu := (G.incVertexCLM (G.fst (G.vertexEdgeMatching v))).hasStrictFDerivAt
      (x := G.incIndependentBase)
    have hv := (G.incVertexCLM (G.snd (G.vertexEdgeMatching v))).hasStrictFDerivAt
      (x := G.incIndependentBase)
    have h := (((hA.mul hv).add (hB.mul hu)).add ((hC.mul hu).mul hv)).neg
    convert h using 1
    · funext z
      exact G.incIndependentFamily_eval_inr z v
    · ext z
      have heq := congrArg (fun f : (G.IncIndependentVar → ℂ) →L[ℂ] ℂ => f z)
        (G.incIndependent_derivative_selected v)
      simpa only [neg_apply, add_apply,
        smul_apply, incVertexCLM_base, Pi.mul_apply,
        smul_eq_mul, zero_mul, mul_zero, add_zero] using heq.symm

/-- The three free coefficients and matched constant coefficients are algebraically independent. -/
theorem incIndependentFamily_algebraicIndependent :
    AlgebraicIndependent ℂ G.incIndependentFamily := by
  exact algebraicIndependent_of_hasStrictFDerivAt_eval G.incIndependentFamily
    G.incIndependentParam (ContinuousLinearEquiv.refl ℂ _) G.incIndependentFamily_hasStrictFDerivAt

end BPFixedPoints.Multigraph
