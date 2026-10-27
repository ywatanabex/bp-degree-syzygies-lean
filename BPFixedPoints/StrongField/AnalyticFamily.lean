import BPFixedPoints.StrongField.AnalyticFamilySeries
import BPFixedPoints.StrongField.AnalyticBoundary

/-!
# The free monomial basis over the parameter ring (`supp:boundary-algebra`)

The state chart is cut out over the parameter space by (−1)^{k_i} w_i^{r_i} − p_i: the analytic
germ algebra ℂ{w} = `analyticGerms V` is an algebra over the convergent parameter ring ℂ{p}
through p_i ↦ (−1)^{k_i} w_i^{r_i}. This file proves that ℂ{w} is a free ℂ{p}-module with basis
the monomials w^α, 0 ≤ α_i < r_i, as used in the supplement's proof of `sf:boundary-algebra`.
The signs (−1)^{k_i} may be any nonzero constants c_i.

* **The parameter ring.** `ParamGerms V r c hr` is `analyticGerms V` in the variables p, as a type
  synonym that records r and c. Through the pullback along Ψ(w) = (c_i w_i^{r_i})_i
  (`powPullback`), ℂ{w} is a ℂ{p}-algebra (`instAlgebraParamGerms`): p_i ↦ c_i w_i^{r_i}
  (`algebraMap_paramGerms_coord`) and g • φ = (g ∘ Ψ) φ (`ofGerm_smul`).
* **Free basis** (`familyBasis`, `familyBasis_apply`). If every r_i > 0 and every c_i ≠ 0, the
  monomial germs w^α, α ∈ `truncBox r`, form a basis of ℂ{w} over ℂ{p}. Spanning
  (`top_le_span_monoGerm`) is the residue decomposition f(w) = ∑_α w^α g_α(Ψ(w)) of
  `StrongField/AnalyticFamilySeries.lean`, and linear independence
  (`linearIndependent_monoGerm`) is its uniqueness. Hence ℂ{w} is free and finite of rank
  ∏_i r_i over ℂ{p} (`free_paramGerms`, `finite_paramGerms`, `finrank_paramGerms`), and
  ℂ{p} → ℂ{w} is injective (`algebraMap_paramGerms_injective`).
* **Specialization at p = 0.** The germs vanishing at 0 form the ideal (w_i)
  (`ker_evalZero_eq_span_coord`). The maximal ideal (p_i) of ℂ{p} generates the truncation ideal
  (w_i^{r_i}) of ℂ{w} (`map_ker_paramEvalZero`), so the special fiber is ℂ{w}/(w_i^{r_i}). Modulo
  (w_i^{r_i}) a parameter germ acts through its value at 0 (`mk_algebraMap_paramGerms`), the basis
  vector w^α becomes the fiber basis vector `truncGermBasis r α` of
  `StrongField/AnalyticDivision.lean` (`mk_familyBasis`), and the fiber coordinates are the values
  at p = 0 of the coordinates over ℂ{p} (`truncGermBasis_repr_mk`).
* **The state chart.** For a state S, with r_i = `G.rS S i` and c_i = (−1)^{k_i} (`stateSign`),
  the parameter ring `stateParamGerms` acts through the parameter germs (−1)^{k_i} w_i^{r_i} of
  `StrongField/AnalyticBoundary.lean` (`algebraMap_stateParamGerms_coord`). `stateFamilyBasis`
  is the monomial basis over ℂ{p}, of rank wt(S) (`finrank_stateParamGerms`). The maximal ideal of
  ℂ{p} generates the special fiber ideal (`map_ker_stateParamGerms`), and under `stateFiberEquiv`
  the basis and the coordinates specialize to the monomial basis `truncBasis` of 𝓑_{S,0}
  (`stateFiberEquiv_mk_stateFamilyBasis`, `truncBasis_repr_stateFiberEquiv`).

Not covered: the chart as an analytic space over the parameter space, i.e. the ring
ℂ{w, p}/((−1)^{k_i} w_i^{r_i} − p_i) and the regularity of this sequence in ℂ{w, p}; the family
is treated through ℂ{w} as a ℂ{p}-algebra. The vertex coordinate f = Φ(w) of a power-map chart is
not treated: all statements are in the chart coordinate w.
-/

set_option linter.unusedSectionVars false

open Filter Topology MvPolynomial

namespace BPFixedPoints

namespace BoundaryAlgebra

section PowPullback

variable {V : Type*} [Fintype V] {r : V → ℕ} {c : V → ℂ}

/-- The power map Ψ(w) = (c_i w_i^{r_i})_i is analytic. -/
theorem analyticAt_scaledPowMap (r : V → ℕ) (c : V → ℂ) (w : V → ℂ) :
    AnalyticAt ℂ (scaledPowMap r c) w :=
  analyticAt_pi_iff.2 fun i => analyticAt_const.fun_mul ((analyticAt_coord i w).pow _)

/-- **The power-map pullback** ℂ{p} → ℂ{w}, φ ↦ φ ∘ Ψ with Ψ(w) = (c_i w_i^{r_i})_i; it sends
p_i to c_i w_i^{r_i} (`powPullback_coord`). -/
noncomputable def powPullback (r : V → ℕ) (c : V → ℂ) (hr : ∀ i, 0 < r i) :
    analyticGerms V →ₐ[ℂ] analyticGerms V :=
  pullback (scaledPowMap r c) (analyticAt_scaledPowMap r c 0) (scaledPowMap_zero hr c)

/-- The pullback of the germ of g is the germ of g ∘ Ψ. -/
theorem powPullback_germOf (hr : ∀ i, 0 < r i) (g : (V → ℂ) → ℂ) (hg : AnalyticAt ℂ g 0) :
    powPullback r c hr (germOf g hg) =
      germOf (fun w => g (scaledPowMap r c w))
        (analyticAt_comp_zero hg (analyticAt_scaledPowMap r c 0) (scaledPowMap_zero hr c)) :=
  rfl

/-- The pullback sends the coordinate germ p_i to c_i w_i^{r_i}. -/
theorem powPullback_coord (hr : ∀ i, 0 < r i) (i : V) :
    powPullback r c hr (coord i) = algebraMap ℂ (analyticGerms V) (c i) * coord i ^ r i :=
  rfl

/-- The monomial function of an exponent vector is a polynomial function. -/
theorem monoFun_eq_eval (α : V →₀ ℕ) :
    monoFun (α : V → ℕ) = fun y => eval y (monomial α (1 : ℂ)) := by
  funext y
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), one_mul]
  rfl

/-- Monomial functions are analytic. -/
theorem analyticAt_monoFun (α : V →₀ ℕ) (y : V → ℂ) : AnalyticAt ℂ (monoFun (α : V → ℕ)) y := by
  rw [monoFun_eq_eval]
  exact analyticAt_eval _ y

/-- The monomial germ w^α is the germ of the monomial function. -/
theorem monoGerm_eq_germOf (α : V →₀ ℕ) :
    monoGerm α = germOf (monoFun (α : V → ℕ)) (analyticAt_monoFun α 0) := by
  classical
  have h := aeval_monomial_coord α (1 : ℂ)
  rw [one_smul, aeval_coord] at h
  rw [← h]
  exact germOf_congr _ _ fun y => by rw [monoFun_eq_eval]

end PowPullback

section ParamRing

variable {V : Type*} [Fintype V] {r : V → ℕ} {c : V → ℂ} {hr : ∀ i, 0 < r i}

/-- **The convergent parameter ring** ℂ{p_i : i ∈ V} of the power-map family p_i = c_i w_i^{r_i}.
It is the analytic germ algebra `analyticGerms V` in the variables p, as a type synonym that
records r and c: through the power-map pullback `powPullback`, ℂ{w} = `analyticGerms V` is an
algebra over it (`instAlgebraParamGerms`), with no clash with the structure of ℂ{w} over
itself. -/
def ParamGerms (V : Type*) [Fintype V] (_r : V → ℕ) (_c : V → ℂ) (_hr : ∀ i, 0 < _r i) :
    Type _ :=
  analyticGerms V

/-- The parameter ring is a commutative ring. -/
noncomputable instance instCommRingParamGerms : CommRing (ParamGerms V r c hr) :=
  inferInstanceAs (CommRing (analyticGerms V))

/-- The parameter ring is a ℂ-algebra. -/
noncomputable instance instAlgebraComplexParamGerms : Algebra ℂ (ParamGerms V r c hr) :=
  inferInstanceAs (Algebra ℂ (analyticGerms V))

/-- The parameter ring is nontrivial. -/
instance instNontrivialParamGerms : Nontrivial (ParamGerms V r c hr) :=
  inferInstanceAs (Nontrivial (analyticGerms V))

/-- The identification of the parameter ring with the germ algebra in the variables p. -/
noncomputable def ParamGerms.ofGerm : analyticGerms V ≃ₐ[ℂ] ParamGerms V r c hr :=
  AlgEquiv.refl

/-- The value at p = 0 of a parameter germ. -/
noncomputable def ParamGerms.evalZero : ParamGerms V r c hr →ₐ[ℂ] ℂ :=
  BoundaryAlgebra.evalZero

/-- **ℂ{w} as an algebra over ℂ{p}**, through p_i ↦ c_i w_i^{r_i}. -/
noncomputable instance instAlgebraParamGerms : Algebra (ParamGerms V r c hr) (analyticGerms V) :=
  RingHom.toAlgebra ((powPullback r c hr).toRingHom : ParamGerms V r c hr →+* analyticGerms V)

/-- The structure map ℂ{p} → ℂ{w} is the power-map pullback. -/
theorem algebraMap_paramGerms (g : analyticGerms V) :
    algebraMap (ParamGerms V r c hr) (analyticGerms V) (ParamGerms.ofGerm g) =
      powPullback r c hr g :=
  rfl

/-- The action of ℂ{p} on ℂ{w}: g • φ = (g ∘ Ψ) φ. -/
theorem ofGerm_smul (g φ : analyticGerms V) :
    (ParamGerms.ofGerm g : ParamGerms V r c hr) • φ = powPullback r c hr g * φ :=
  Algebra.smul_def _ _

/-- The structure map sends p_i to c_i w_i^{r_i}. -/
theorem algebraMap_paramGerms_coord (i : V) :
    algebraMap (ParamGerms V r c hr) (analyticGerms V) (ParamGerms.ofGerm (coord i)) =
      algebraMap ℂ (analyticGerms V) (c i) * coord i ^ r i :=
  rfl

/-- The scalar actions of ℂ, ℂ{p} and ℂ{w} are compatible. -/
instance instIsScalarTowerParamGerms :
    IsScalarTower ℂ (ParamGerms V r c hr) (analyticGerms V) :=
  IsScalarTower.of_algebraMap_eq fun x => ((powPullback r c hr).commutes x).symm

/-- The germ of ∑_α w^α g_α(Ψ(w)) is ∑_α g_α • w^α. -/
theorem germOf_sum_monoFun_mul (g : truncBox r → (V → ℂ) → ℂ) (hg : ∀ α, AnalyticAt ℂ (g α) 0)
    (h : AnalyticAt ℂ (fun w => ∑ α : truncBox r,
      monoFun ((α : V →₀ ℕ) : V → ℕ) w * g α (scaledPowMap r c w)) 0) :
    germOf (fun w => ∑ α : truncBox r,
      monoFun ((α : V →₀ ℕ) : V → ℕ) w * g α (scaledPowMap r c w)) h =
      ∑ α : truncBox r, (ParamGerms.ofGerm (germOf (g α) (hg α)) : ParamGerms V r c hr) •
        monoGerm (α : V →₀ ℕ) := by
  have hterm : ∀ α : truncBox r, AnalyticAt ℂ
      (fun w => monoFun ((α : V →₀ ℕ) : V → ℕ) w * g α (scaledPowMap r c w)) 0 := fun α =>
    (analyticAt_monoFun _ 0).fun_mul
      (analyticAt_comp_zero (hg α) (analyticAt_scaledPowMap r c 0) (scaledPowMap_zero hr c))
  rw [germOf_sum Finset.univ hterm h]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ofGerm_smul, powPullback_germOf, monoGerm_eq_germOf, mul_comm,
    ← germOf_mul (analyticAt_monoFun _ 0) _ (hterm α)]

end ParamRing

section Basis

variable {V : Type*} [Fintype V] {r : V → ℕ} {c : V → ℂ}

/-- Analyticity of w ↦ ∑_α w^α g_α(Ψ(w)). -/
theorem analyticAt_sum_monoFun_mul (hr : ∀ i, 0 < r i) (g : truncBox r → (V → ℂ) → ℂ)
    (hg : ∀ α, AnalyticAt ℂ (g α) 0) :
    AnalyticAt ℂ (fun w => ∑ α : truncBox r,
      monoFun ((α : V →₀ ℕ) : V → ℕ) w * g α (scaledPowMap r c w)) 0 :=
  Finset.analyticAt_fun_sum _ fun α _ => (analyticAt_monoFun _ 0).fun_mul
    (analyticAt_comp_zero (hg α) (analyticAt_scaledPowMap r c 0) (scaledPowMap_zero hr c))

/-- **Uniqueness.** The monomials w^α, α in the box, are linearly independent over ℂ{p}. -/
theorem linearIndependent_monoGerm (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    LinearIndependent (ParamGerms V r c hr) fun α : truncBox r => monoGerm (α : V →₀ ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg α
  choose G hG hGg using fun α => exists_germOf (ParamGerms.ofGerm.symm (g α))
  have hg' : ∀ α, g α = ParamGerms.ofGerm (germOf (G α) (hG α)) := fun α => by
    rw [hGg]
    rfl
  have hsum := analyticAt_sum_monoFun_mul (c := c) hr G hG
  have h0 : germOf _ hsum = germOf (fun _ => (0 : ℂ)) analyticAt_const := by
    rw [germOf_sum_monoFun_mul G hG hsum]
    simp_rw [← hg']
    exact hg
  have hz := eventuallyEq_zero_of_sum_monoFun_mul hr hc hG ((germOf_eq_iff _ _).1 h0) α
  rw [hg' α, (germOf_eq_iff (hG α) analyticAt_const).2 hz]
  rfl

/-- **Existence.** The monomials w^α, α in the box, span ℂ{w} over ℂ{p}. -/
theorem top_le_span_monoGerm (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    ⊤ ≤ Submodule.span (ParamGerms V r c hr)
      (Set.range fun α : truncBox r => monoGerm (α : V →₀ ℕ)) := by
  rintro φ -
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  obtain ⟨g, hg, hfg⟩ := exists_eventuallyEq_sum_monoFun_mul hr hc hf
  have hsum := analyticAt_sum_monoFun_mul (c := c) hr g hg
  rw [(germOf_eq_iff hf hsum).2 hfg, germOf_sum_monoFun_mul (hr := hr) g hg hsum]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- **Free monomial basis over the parameter ring (`supp:boundary-algebra`).** If every r_i > 0
and every c_i ≠ 0, then ℂ{w}, as an algebra over ℂ{p} through p_i ↦ c_i w_i^{r_i}, is a free
ℂ{p}-module with basis the monomials w^α, 0 ≤ α_i < r_i (`familyBasis_apply`). -/
noncomputable def familyBasis (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Module.Basis (truncBox r) (ParamGerms V r c hr) (analyticGerms V) :=
  Module.Basis.mk (linearIndependent_monoGerm hr hc) (top_le_span_monoGerm hr hc)

/-- The basis vector indexed by α is the monomial germ w^α. -/
@[simp]
theorem familyBasis_apply (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) (α : truncBox r) :
    familyBasis hr hc α = monoGerm (α : V →₀ ℕ) :=
  Module.Basis.mk_apply _ _ _

/-- **Freeness.** ℂ{w} is a free ℂ{p}-module. -/
theorem free_paramGerms (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Module.Free (ParamGerms V r c hr) (analyticGerms V) :=
  Module.Free.of_basis (familyBasis hr hc)

/-- **Finiteness.** ℂ{w} is a finite ℂ{p}-module. -/
theorem finite_paramGerms (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Module.Finite (ParamGerms V r c hr) (analyticGerms V) :=
  Module.Finite.of_basis (familyBasis hr hc)

/-- **Rank.** ℂ{w} has rank ∏_i r_i over ℂ{p}. -/
theorem finrank_paramGerms (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Module.finrank (ParamGerms V r c hr) (analyticGerms V) = ∏ i, r i := by
  rw [Module.finrank_eq_nat_card_basis (familyBasis hr hc), card_truncBox]

/-- **ℂ{p} ⊂ ℂ{w}.** If every r_i > 0 and every c_i ≠ 0, the structure map ℂ{p} → ℂ{w} is
injective. -/
theorem algebraMap_paramGerms_injective (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Function.Injective (algebraMap (ParamGerms V r c hr) (analyticGerms V)) := by
  have h0 : (0 : V →₀ ℕ) ∈ truncBox r := fun i => hr i
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h1 : g • familyBasis hr hc ⟨0, h0⟩ = 0 := by
    rw [Algebra.smul_def, hg, zero_mul]
  have h2 := congrArg (fun x => (familyBasis hr hc).repr x ⟨0, h0⟩) h1
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply] using h2

end Basis

section Specialization

variable {V : Type*} [Fintype V] {r : V → ℕ} {c : V → ℂ}

/-- Every germ is congruent to its value at 0 modulo the coordinates: φ − φ(0) ∈ (w_i : i ∈ V).
The proof restricts to growing sets of coordinates and divides by one coordinate at a time. -/
theorem sub_algebraMap_evalZero_mem_span_coord (φ : analyticGerms V) :
    φ - algebraMap ℂ (analyticGerms V) (evalZero φ) ∈
      Ideal.span (Set.range (coord : V → analyticGerms V)) := by
  classical
  set I := Ideal.span (Set.range (coord : V → analyticGerms V))
  suffices h : ∀ T : Finset V, ∀ φ : analyticGerms V,
      restrictTo T φ - algebraMap ℂ (analyticGerms V) (evalZero φ) ∈ I by
    simpa [restrictTo_univ] using h Finset.univ φ
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro φ
    rw [restrictTo_empty, sub_self]
    exact I.zero_mem
  | insert i T hi ih =>
    intro φ
    obtain ⟨ψ, hψ⟩ := exists_eq_restrictCoord_add i φ
    have e : restrictTo (insert i T) φ = restrictTo T φ + coord i * restrictTo (insert i T) ψ := by
      conv_lhs => rw [hψ]
      rw [map_add, map_mul, restrictTo_restrictCoord hi,
        restrictTo_coord (Finset.mem_insert_self i T)]
    rw [e, add_sub_right_comm]
    exact I.add_mem (ih φ) (I.mul_mem_right _ (Ideal.subset_span ⟨i, rfl⟩))

/-- **The maximal ideal of ℂ{w}.** The germs vanishing at 0 form the ideal (w_i : i ∈ V). -/
theorem ker_evalZero_eq_span_coord :
    RingHom.ker (evalZero : analyticGerms V →ₐ[ℂ] ℂ) =
      Ideal.span (Set.range (coord : V → analyticGerms V)) := by
  apply le_antisymm
  · intro φ hφ
    rw [RingHom.mem_ker] at hφ
    have h := sub_algebraMap_evalZero_mem_span_coord φ
    rwa [hφ, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, evalZero_coord]

/-- **The special fiber p = 0.** If every r_i > 0 and every c_i ≠ 0, the maximal ideal
(p_i : i ∈ V) of ℂ{p} generates the truncation ideal (w_i^{r_i} : i ∈ V) of ℂ{w}. -/
theorem map_ker_paramEvalZero (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) :
    Ideal.map (algebraMap (ParamGerms V r c hr) (analyticGerms V))
      (RingHom.ker (ParamGerms.evalZero : ParamGerms V r c hr →ₐ[ℂ] ℂ)) = truncGermIdeal r := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    have hg' : ParamGerms.ofGerm.symm g ∈ RingHom.ker (evalZero : analyticGerms V →ₐ[ℂ] ℂ) := hg
    rw [ker_evalZero_eq_span_coord, Ideal.mem_span_range_iff_exists_fun] at hg'
    obtain ⟨a, ha⟩ := hg'
    rw [Ideal.mem_comap]
    change powPullback r c hr (ParamGerms.ofGerm.symm g) ∈ truncGermIdeal r
    rw [← ha, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul, powPullback_coord]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  · rw [truncGermIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : (ParamGerms.ofGerm (algebraMap ℂ (analyticGerms V) (c i)⁻¹ * coord i) :
        ParamGerms V r c hr) ∈ RingHom.ker (ParamGerms.evalZero : ParamGerms V r c hr →ₐ[ℂ] ℂ) := by
      change evalZero (algebraMap ℂ (analyticGerms V) (c i)⁻¹ * coord i) = 0
      rw [map_mul, evalZero_coord, mul_zero]
    have h := Ideal.mem_map_of_mem (algebraMap (ParamGerms V r c hr) (analyticGerms V)) hmem
    rw [algebraMap_paramGerms, map_mul, AlgHom.commutes, powPullback_coord, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ (hc i), map_one, one_mul] at h
    exact h

/-- Modulo (w_i^{r_i}), a parameter germ acts through its value at p = 0. -/
theorem mk_algebraMap_paramGerms (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0)
    (g : ParamGerms V r c hr) :
    Ideal.Quotient.mk (truncGermIdeal r) (algebraMap (ParamGerms V r c hr) (analyticGerms V) g) =
      algebraMap ℂ (analyticGerms V ⧸ truncGermIdeal r) (ParamGerms.evalZero g) := by
  have hker : g - algebraMap ℂ (ParamGerms V r c hr) (ParamGerms.evalZero g) ∈
      RingHom.ker (ParamGerms.evalZero : ParamGerms V r c hr →ₐ[ℂ] ℂ) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have h := Ideal.mem_map_of_mem (algebraMap (ParamGerms V r c hr) (analyticGerms V)) hker
  rw [map_ker_paramEvalZero hr hc, map_sub, ← IsScalarTower.algebraMap_apply] at h
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact h

/-- **Specialization of the basis.** Modulo (w_i^{r_i}), the basis vector w^α of ℂ{w} over ℂ{p}
is the monomial basis vector of the special fiber ℂ{w}/(w_i^{r_i}) (`truncGermBasis`). -/
theorem mk_familyBasis (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) (α : truncBox r) :
    Ideal.Quotient.mk (truncGermIdeal r) (familyBasis hr hc α) = truncGermBasis r α := by
  classical
  rw [familyBasis_apply, truncGermBasis_apply, aeval_monomial_coord, one_smul]

/-- **Specialization of coordinates.** The coordinates in the fiber basis of the class of φ are
the values at p = 0 of the coordinates of φ over ℂ{p}. -/
theorem truncGermBasis_repr_mk (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ 0) (φ : analyticGerms V)
    (α : truncBox r) :
    (truncGermBasis r).repr (Ideal.Quotient.mk (truncGermIdeal r) φ) α =
      ParamGerms.evalZero ((familyBasis hr hc).repr φ α) := by
  have h : Ideal.Quotient.mk (truncGermIdeal r) φ =
      ∑ α, ParamGerms.evalZero ((familyBasis hr hc).repr φ α) • truncGermBasis r α := by
    conv_lhs => rw [← (familyBasis hr hc).sum_repr φ]
    rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Ideal.Quotient.mkₐ_eq_mk, Algebra.smul_def, map_mul, mk_algebraMap_paramGerms hr hc,
      mk_familyBasis, ← Algebra.smul_def]
  rw [h, Module.Basis.repr_sum_self]

end Specialization

end BoundaryAlgebra

namespace Multigraph

open BP BoundaryAlgebra

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
  (S : Finset E)

/-- The signs c_i = (−1)^{k_i}, k_i = d_S(i), of the state chart. -/
noncomputable def stateSign (i : V) : ℂ := (-1) ^ G.deg S i

/-- The signs are nonzero. -/
theorem stateSign_ne_zero (i : V) : G.stateSign S i ≠ 0 :=
  pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)

/-- **The parameter ring of the state chart.** For a state S, ℂ{p} acting on ℂ{w} through
p_i ↦ (−1)^{k_i} w_i^{r_i} (`algebraMap_stateParamGerms_coord`), the chart equations of
`sf:boundary-algebra`. -/
abbrev stateParamGerms (hS : IsState G S) : Type _ :=
  ParamGerms V (G.rS S) (G.stateSign S) (G.rS_pos S hS)

/-- The structure map sends the coordinate p_i to the parameter germ (−1)^{k_i} w_i^{r_i} of the
state chart (`powerMapGerm`). -/
theorem algebraMap_stateParamGerms_coord (hS : IsState G S) (i : V) :
    algebraMap (G.stateParamGerms S hS) (analyticGerms V) (ParamGerms.ofGerm (coord i)) =
      G.powerMapGerm S i :=
  rfl

/-- **`sf:boundary-algebra`, free basis over ℂ{p}.** For a state S, ℂ{w} is a free module over
the parameter ring ℂ{p} of the state chart, with basis the monomials w^α, 0 ≤ α_i < r_i
(`stateFamilyBasis_apply`). -/
noncomputable def stateFamilyBasis (hS : IsState G S) :
    Module.Basis (truncBox (G.rS S)) (G.stateParamGerms S hS) (analyticGerms V) :=
  familyBasis (G.rS_pos S hS) (G.stateSign_ne_zero S)

/-- The basis vector indexed by α is the monomial germ w^α. -/
@[simp]
theorem stateFamilyBasis_apply (hS : IsState G S) (α : truncBox (G.rS S)) :
    G.stateFamilyBasis S hS α = monoGerm (α : V →₀ ℕ) :=
  familyBasis_apply _ _ α

/-- **Rank wt(S).** For a state S, ℂ{w} has rank wt(S) = ∏_i r_i over ℂ{p}. -/
theorem finrank_stateParamGerms (hS : IsState G S) :
    Module.finrank (G.stateParamGerms S hS) (analyticGerms V) = G.wt phi S := by
  rw [finrank_paramGerms (G.rS_pos S hS) (G.stateSign_ne_zero S), prod_rS_eq_wt]

/-- **The special fiber p = 0.** The maximal ideal (p_i) of ℂ{p} generates the special fiber
ideal of the state chart. -/
theorem map_ker_stateParamGerms (hS : IsState G S) :
    Ideal.map (algebraMap (G.stateParamGerms S hS) (analyticGerms V))
      (RingHom.ker (ParamGerms.evalZero : G.stateParamGerms S hS →ₐ[ℂ] ℂ)) =
      G.stateFiberIdeal S := by
  rw [map_ker_paramEvalZero (G.rS_pos S hS) (G.stateSign_ne_zero S), stateFiberIdeal_eq]

/-- **Specialization of the basis at p = 0.** Under `stateFiberEquiv`, the class of the basis
vector w^α is the monomial basis vector of 𝓑_{S,0} (`truncBasis`). -/
theorem stateFiberEquiv_mk_stateFamilyBasis (hS : IsState G S) (α : truncBox (G.rS S)) :
    G.stateFiberEquiv S (Ideal.Quotient.mk _ (G.stateFamilyBasis S hS α)) =
      truncBasis ℂ (G.rS S) α := by
  have h := aeval_monomial_coord (α : V →₀ ℕ) (1 : ℂ)
  rw [one_smul] at h
  rw [stateFamilyBasis_apply, stateFiberEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, ← h, truncQuotEquiv_mk_aeval, truncBasis_apply]

/-- **Specialization of coordinates at p = 0.** The coordinates in 𝓑_{S,0} of the class of φ are
the values at p = 0 of the coordinates of φ over ℂ{p}. -/
theorem truncBasis_repr_stateFiberEquiv (hS : IsState G S) (φ : analyticGerms V)
    (α : truncBox (G.rS S)) :
    (truncBasis ℂ (G.rS S)).repr (G.stateFiberEquiv S (Ideal.Quotient.mk _ φ)) α =
      ParamGerms.evalZero ((G.stateFamilyBasis S hS).repr φ α) := by
  have h := truncGermBasis_repr_mk (G.rS_pos S hS) (G.stateSign_ne_zero S) φ α
  refine Eq.trans ?_ h
  rw [stateFiberEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk, truncGermBasis,
    Module.Basis.map_repr]
  rfl

end Multigraph

end BPFixedPoints
