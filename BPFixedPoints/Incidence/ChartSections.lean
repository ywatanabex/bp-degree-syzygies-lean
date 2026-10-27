import BPFixedPoints.Incidence.Torus

/-!
# Chart intersections and compatible chart sections

Without changing the current definition of `IncidenceRing`, identify it with
compatible families on all charts. This algebraic identification connects
the Čech degree-zero kernel to the actual incidence ring.
-/

namespace BPFixedPoints.Multigraph

/-- A map unchanged by changing one of finitely many coordinates at a time is constant. -/
theorem finiteFunction_constant_of_update {V A X : Type*} [Fintype V] [DecidableEq V]
    (f : (V → A) → X)
    (hf : ∀ σ v a, f (Function.update σ v a) = f σ) (σ τ : V → A) : f σ = f τ := by
  classical
  have h : ∀ S : Finset V, f (fun v => if v ∈ S then τ v else σ v) = f σ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih =>
      have he : (fun w => if w ∈ insert v S then τ w else σ w) =
          Function.update (fun w => if w ∈ S then τ w else σ w) v (τ v) := by
        funext w
        by_cases hw : w = v
        · subst w
          simp
        · simp [hw]
      rw [he, hf, ih]
  simpa using (h Finset.univ).symm

/-- Agreement along edges of a Boolean cube implies agreement at all its vertices. -/
theorem booleanCube_constant_of_edges {V X : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → X)
    (hf : ∀ σ v, f (Function.update σ v false) = f (Function.update σ v true))
    (σ τ : V → Bool) : f σ = f τ := by
  apply finiteFunction_constant_of_update f ?_ σ τ
  intro s v a
  have hh : f (Function.update s v a) = f (Function.update s v (s v)) := by
    cases a <;> cases hs : s v
    · rfl
    · exact hf s v
    · exact (hf s v).symm
    · rfl
  simpa only [Function.update_eq_self] using hh

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Families of chart sections agreeing on the common torus. -/
noncomputable def CompatibleCharts : Subalgebra ℂ (∀ σ : V → Bool, G.IncChartRing σ) where
  carrier := {x | ∀ σ τ, G.incChartMap σ (x σ) = G.incChartMap τ (x τ)}
  zero_mem' := by intro σ τ; simp
  one_mem' := by intro σ τ; simp
  add_mem' := by
    intro x y hx hy σ τ
    change G.incChartMap σ (x σ + y σ) = G.incChartMap τ (x τ + y τ)
    rw [map_add, map_add, hx σ τ, hy σ τ]
  mul_mem' := by
    intro x y hx hy σ τ
    change G.incChartMap σ (x σ * y σ) = G.incChartMap τ (x τ * y τ)
    rw [map_mul, map_mul, hx σ τ, hy σ τ]
  algebraMap_mem' := by intro c σ τ; exact (AlgHom.commutes _ c).trans (AlgHom.commutes _ c).symm

theorem compatibleCharts_of_adjacent (x : ∀ σ : V → Bool, G.IncChartRing σ)
    (hx : ∀ σ v,
      G.incChartMap (Function.update σ v false) (x (Function.update σ v false)) =
      G.incChartMap (Function.update σ v true) (x (Function.update σ v true))) :
    x ∈ G.CompatibleCharts :=
  booleanCube_constant_of_edges (fun σ => G.incChartMap σ (x σ)) hx

/-- Regard compatible chart sections as elements of the intersection inside the torus. -/
noncomputable def compatibleChartsToIncidence : G.CompatibleCharts →ₐ[ℂ] G.IncidenceRing where
  toFun x := ⟨G.incChartMap (fun _ => false) (x.val (fun _ => false)), by
    rw [IncidenceRing, Algebra.mem_iInf]
    intro σ
    exact ⟨x.val σ, x.property σ (fun _ => false)⟩⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_one' := by apply Subtype.ext; exact map_one _
  map_add' := by intro x y; apply Subtype.ext; exact map_add _ _ _
  map_mul' := by intro x y; apply Subtype.ext; exact map_mul _ _ _
  commutes' := by intro c; apply Subtype.ext; exact AlgHom.commutes _ c

theorem compatibleChartsToIncidence_bijective : Function.Bijective G.compatibleChartsToIncidence := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext σ
    apply G.incChartMap_injective σ
    have h₀ := congrArg Subtype.val h
    change G.incChartMap (fun _ => false) (x.val (fun _ => false)) =
      G.incChartMap (fun _ => false) (y.val (fun _ => false)) at h₀
    exact (x.property σ (fun _ => false)).trans
      (h₀.trans (y.property σ (fun _ => false)).symm)
  · intro x
    have hx : ∀ σ : V → Bool, ∃ y : G.IncChartRing σ, G.incChartMap σ y = x.val := by
      intro σ
      exact (Algebra.mem_iInf.mp x.property) σ
    choose y hy using hx
    refine ⟨⟨y, fun σ τ => (hy σ).trans (hy τ).symm⟩, ?_⟩
    apply Subtype.ext
    exact hy (fun _ => false)

/-- `IncidenceRing` is isomorphic to the actual ring of compatible chart sections. -/
noncomputable def incidenceRingEquivCompatibleCharts : G.IncidenceRing ≃ₐ[ℂ] G.CompatibleCharts :=
  (AlgEquiv.ofBijective G.compatibleChartsToIncidence G.compatibleChartsToIncidence_bijective).symm

theorem incidenceRingEquivCompatibleCharts_map (x : G.IncidenceRing) (σ : V → Bool) :
    G.incChartMap σ ((G.incidenceRingEquivCompatibleCharts x).val σ) = x.val := by
  have h := G.incidenceRingEquivCompatibleCharts.symm_apply_apply x
  have he := congrArg Subtype.val h
  change G.incChartMap (fun _ => false)
    ((G.incidenceRingEquivCompatibleCharts x).val (fun _ => false)) = x.val at he
  exact ((G.incidenceRingEquivCompatibleCharts x).property σ (fun _ => false)).trans he

end BPFixedPoints.Multigraph
