import BPFixedPoints.Incidence.StateCohomology

/-!
# Chart definition of the universal edge-incidence ring

Define the coefficient ring, affine charts, common torus and restriction maps.
`IncidenceRing` is the intersection of all chart images in the torus ring.
`Incidence/Chart.lean` proves polynomial chart presentations and injectivity
of restrictions.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open MvPolynomial

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] (G : Multigraph V E)

/-- Coefficient indices (e,α,β), for X_{fst e,α}X_{snd e,β}. -/
abbrev IncCoeffIdx (E : Type) := E × Fin 2 × Fin 2

/-- Coefficient ring S_G=ℂ[c_{e,α,β}] in 4m variables. -/
abbrev IncCoeffRing (E : Type) := MvPolynomial (IncCoeffIdx E) ℂ

/-- Homogeneous-coordinate components on a chart: near zero use (1:t), near infinity use (t:1). -/
def incCoord {R : Type*} [CommRing R] (atInf : Bool) (α : Fin 2) (t : R) : R :=
  if atInf then (if α = 0 then t else 1) else (if α = 0 then 1 else t)

/-- Chart-ring variables: vertex coordinates t_v and coefficients c. -/
abbrev IncChartVar (V E : Type) := V ⊕ IncCoeffIdx E

/-- Edge equation on chart σ: b_e^σ=Σ_{α,β}c_{e,α,β}X_{u,α}X_{v,β}. -/
noncomputable def incChartEq (σ : V → Bool) (e : E) : MvPolynomial (IncChartVar V E) ℂ :=
  ∑ α : Fin 2, ∑ β : Fin 2, X (Sum.inr (e, α, β)) *
    incCoord (σ (G.fst e)) α (X (Sum.inl (G.fst e))) *
      incCoord (σ (G.snd e)) β (X (Sum.inl (G.snd e)))

/-- Coordinate ring ℂ[t,c]/(b_e^σ) of Z_G on chart σ. -/
abbrev IncChartRing (σ : V → Bool) :=
  MvPolynomial (IncChartVar V E) ℂ ⧸ Ideal.span (Set.range (G.incChartEq σ))

/-- Torus-ring variables: t_v, s_v=t_v⁻¹ and coefficients c. -/
abbrev IncTorusVar (V E : Type) := V ⊕ V ⊕ IncCoeffIdx E

/-- Torus relations: t_v s_v−1 and b_e from the all-zero chart. -/
noncomputable def incTorusRel : (V ⊕ E) → MvPolynomial (IncTorusVar V E) ℂ
  | Sum.inl v => X (Sum.inl v) * X (Sum.inr (Sum.inl v)) - 1
  | Sum.inr e => rename (Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))) (G.incChartEq (fun _ => false) e)

/-- Coordinate ring of Z_G over the torus. -/
abbrev IncTorusRing := MvPolynomial (IncTorusVar V E) ℂ ⧸ Ideal.span (Set.range G.incTorusRel)

/-- Torus values of chart variables: a coordinate near infinity is s_v=t_v⁻¹. -/
noncomputable def incChartVal (σ : V → Bool) : IncChartVar V E → G.IncTorusRing
  | Sum.inl v => if σ v then Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))
      else Ideal.Quotient.mk _ (X (Sum.inl v))
  | Sum.inr c => Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c)))

theorem incTorus_ts (v : V) :
    Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel)) (X (Sum.inl v)) *
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))) = 1 := by
  rw [← map_mul, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨Sum.inl v, rfl⟩

theorem incTorus_b (e : E) :
    Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
      (rename (Sum.elim Sum.inl (fun c => Sum.inr (Sum.inr c))) (G.incChartEq (fun _ => false) e)) =
      0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨Sum.inr e, rfl⟩

/-- Homogeneous chart change: if ts=1, each component of (t:1) is s times the corresponding component of (1:t). -/
theorem incCoord_true {R : Type*} [CommRing R] {t s : R} (h : t * s = 1) (α : Fin 2) :
    incCoord true α s = s * incCoord false α t := by
  fin_cases α
  · simp [incCoord]
  · simp [incCoord]; linear_combination -h

theorem map_incCoord {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (φ : F) (b : Bool) (α : Fin 2) (p : R) :
    φ (incCoord b α p) = incCoord b α (φ p) := by
  unfold incCoord; split_ifs <;> simp

/-- Chart equations vanish on the torus: b_e^σ=(∏_{σ_w=∞}s_w)b_e. -/
theorem eval_incChartEq (σ : V → Bool) (e : E) :
    aeval (G.incChartVal σ) (G.incChartEq σ e) = 0 := by
  have hts := G.incTorus_ts
  have hb := G.incTorus_b e
  simp only [incChartEq, map_sum, map_mul, rename_X, map_incCoord, Sum.elim_inl,
    Sum.elim_inr] at hb
  simp only [incChartEq, map_sum, map_mul, aeval_X, map_incCoord, incChartVal]
  -- At each vertex replace the components of (t:1) by s times those of (1:t).
  have hcoord : ∀ (w : V) (α : Fin 2),
      incCoord (σ w) α (if σ w then Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
          (X (Sum.inr (Sum.inl w))) else Ideal.Quotient.mk _ (X (Sum.inl w))) =
        (if σ w then Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
          (X (Sum.inr (Sum.inl w))) else 1) *
          incCoord false α (Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
            (X (Sum.inl w))) := by
    intro w α
    cases σ w
    · simp
    · simpa using incCoord_true (hts w) α
  simp only [hcoord]
  calc _ = (if σ (G.fst e) then Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
          (X (Sum.inr (Sum.inl (G.fst e)))) else 1) *
        (if σ (G.snd e) then Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
          (X (Sum.inr (Sum.inl (G.snd e)))) else 1) *
        ∑ α : Fin 2, ∑ β : Fin 2,
          Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel)) (X (Sum.inr (Sum.inr (e, α, β)))) *
          incCoord false α (Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
            (X (Sum.inl (G.fst e)))) *
          incCoord false β (Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
            (X (Sum.inl (G.snd e)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        ring
    _ = 0 := by rw [hb, mul_zero]

/-- Restriction χ_σ:IncChartRing σ→IncTorusRing. -/
noncomputable def incChartMap (σ : V → Bool) : G.IncChartRing σ →ₐ[ℂ] G.IncTorusRing :=
  Ideal.Quotient.liftₐ _ (aeval (G.incChartVal σ)) fun p hp => by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨e, rfl⟩; exact G.eval_incChartEq σ e
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

theorem incChartMap_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartMap σ (Ideal.Quotient.mk _ p) = aeval (G.incChartVal σ) p := rfl

/-- **Chart model of the universal edge-incidence ring:** regular functions on the torus extending to every chart. This definition does not itself formalize identification with sheaf global sections Γ(Z_G,𝒪). -/
noncomputable def IncidenceRing : Subalgebra ℂ G.IncTorusRing := ⨅ σ, (G.incChartMap σ).range

/-- Each coefficient c comes from every chart. -/
theorem coeff_mem_incidenceRing (c : IncCoeffIdx E) :
    Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel)) (X (Sum.inr (Sum.inr c))) ∈
      G.IncidenceRing := by
  rw [IncidenceRing, Algebra.mem_iInf]
  intro σ
  rw [AlgHom.mem_range]
  refine ⟨Ideal.Quotient.mk _ (X (Sum.inr c)), ?_⟩
  rw [incChartMap_mk, aeval_X]
  rfl

/-- Coefficient map S_G→𝒰_G. -/
noncomputable def coeffHom : IncCoeffRing E →ₐ[ℂ] G.IncidenceRing :=
  aeval fun c => ⟨_, G.coeff_mem_incidenceRing c⟩

end Multigraph

end BPFixedPoints
