import BPFixedPoints.StrongField.BoundaryAlgebra
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Germ

/-!
# The analytic germ algebra ℂ{w} at the origin of ℂ^V

For a finite index set V, `analyticGerms V` is the ℂ-subalgebra of the germ ring
`Germ (𝓝 0) ℂ` of functions ℂ^V → ℂ whose germs have a representative analytic at 0. It is the
convergent power series ring ℂ{w_i : i ∈ V}, presented through germs of analytic functions; no
general theory of convergent power series or analytic spaces is built here.

* `germOf f hf` is the germ of an analytic function, `coord i` the coordinate germ w_i,
  `evalZero` the value at 0, and `MvPolynomial.aeval coord` the evaluation of polynomials
  (`aeval_coord`).
* `pullback Φ` composes germs with an analytic map Φ fixing the origin; it is functorial
  (`pullback_pullback`), and an analytic map with analytic inverse gives an algebra isomorphism
  `pullbackEquiv`.
* Each coordinate germ is a nonzerodivisor (`coord_mul_eq_zero`).
* `truncGermIdeal r` is the ideal (w_i^{r_i} : i ∈ V) of ℂ{w}.

The germ ring carries no `Algebra` instance in Mathlib; `instAlgebraGerm` supplies the evident
one, with the existing scalar multiplication.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology MvPolynomial

namespace BoundaryAlgebra

/-- Germs of `A`-valued functions along a filter form an `R`-algebra whenever `A` is one. The
scalar multiplication is the existing pointwise one. -/
noncomputable instance instAlgebraGerm {α : Type*} {l : Filter α} {R A : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] : Algebra R (Germ l A) where
  algebraMap := (Germ.coeRingHom l).comp (algebraMap R (α → A))
  commutes' r x := Germ.inductionOn x fun f => by
    change (((algebraMap R (α → A) r : α → A) : Germ l A) * f) =
      (f : Germ l A) * ((algebraMap R (α → A) r : α → A) : Germ l A)
    rw [← Germ.coe_mul, ← Germ.coe_mul, Algebra.commutes]
  smul_def' r x := Germ.inductionOn x fun f => by
    change r • (f : Germ l A) = (((algebraMap R (α → A) r : α → A) : Germ l A) * f)
    rw [← Germ.coe_mul, ← Germ.coe_smul, Algebra.smul_def]

section Germs

variable (V : Type*) [Fintype V]

/-- The analytic germ algebra ℂ{w_i : i ∈ V} at the origin of ℂ^V: the germs at 0 that have a
representative analytic at 0. -/
noncomputable def analyticGerms : Subalgebra ℂ (Germ (𝓝 (0 : V → ℂ)) ℂ) where
  carrier := {φ | ∃ f : (V → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧ (f : Germ (𝓝 (0 : V → ℂ)) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  algebraMap_mem' c := ⟨fun _ => c, analyticAt_const, rfl⟩

variable {V}

/-- The germ of a function is analytic iff the function is analytic at 0. -/
theorem coe_mem_analyticGerms {f : (V → ℂ) → ℂ} :
    (f : Germ (𝓝 (0 : V → ℂ)) ℂ) ∈ analyticGerms V ↔ AnalyticAt ℂ f 0 := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact hg.congr (Germ.coe_eq.1 hgf)
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- The germ at 0 of a function analytic at 0. -/
noncomputable def germOf (f : (V → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) : analyticGerms V :=
  ⟨f, f, hf, rfl⟩

/-- The underlying germ of `germOf f hf` is the germ of f. -/
@[simp]
theorem coe_germOf (f : (V → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ((germOf f hf : analyticGerms V) : Germ (𝓝 (0 : V → ℂ)) ℂ) = f := rfl

/-- Two analytic functions have the same germ iff they agree near 0. -/
theorem germOf_eq_iff {f g : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    germOf f hf = germOf g hg ↔ f =ᶠ[𝓝 0] g :=
  Subtype.ext_iff.trans Germ.coe_eq

/-- Every analytic germ is the germ of an analytic function. -/
theorem exists_germOf (φ : analyticGerms V) : ∃ f hf, germOf f hf = φ := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨f, hf, Subtype.ext hφ⟩

/-- Functions which agree everywhere have the same germ. -/
theorem germOf_congr {f g : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : ∀ y, f y = g y) : germOf f hf = germOf g hg :=
  (germOf_eq_iff hf hg).2 (Eventually.of_forall h)

/-- Germs of sums are sums of germs. -/
theorem germOf_add {f g : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : AnalyticAt ℂ (fun y => f y + g y) 0) :
    germOf (fun y => f y + g y) hfg = germOf f hf + germOf g hg := rfl

/-- Germs of differences are differences of germs. -/
theorem germOf_sub {f g : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : AnalyticAt ℂ (fun y => f y - g y) 0) :
    germOf (fun y => f y - g y) hfg = germOf f hf - germOf g hg := rfl

/-- Germs of products are products of germs. -/
theorem germOf_mul {f g : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfg : AnalyticAt ℂ (fun y => f y * g y) 0) :
    germOf (fun y => f y * g y) hfg = germOf f hf * germOf g hg := rfl

/-- Germs of powers are powers of germs. -/
theorem germOf_pow {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ)
    (hfn : AnalyticAt ℂ (fun y => f y ^ n) 0) :
    germOf (fun y => f y ^ n) hfn = germOf f hf ^ n := rfl

/-- The germ of a constant function is the scalar. -/
theorem germOf_const (c : ℂ) (hc : AnalyticAt ℂ (fun _ : V → ℂ => c) 0) :
    germOf (fun _ => c) hc = algebraMap ℂ (analyticGerms V) c := rfl

/-- Germs of finite sums are finite sums of germs. -/
theorem germOf_sum {ι : Type*} (s : Finset ι) {f : ι → (V → ℂ) → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (hs : AnalyticAt ℂ (fun y => ∑ i ∈ s, f i y) 0) :
    germOf (fun y => ∑ i ∈ s, f i y) hs = ∑ i ∈ s, germOf (f i) (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih =>
    have hs' : AnalyticAt ℂ (fun y => ∑ i ∈ s, f i y) 0 :=
      Finset.analyticAt_fun_sum _ fun i _ => hf i
    rw [Finset.sum_insert hj, ← ih hs', ← germOf_add (hf j) hs' ((hf j).add hs')]
    congr 1
    funext y
    rw [Finset.sum_insert hj]

/-- The coordinate function y ↦ y_i is analytic. -/
theorem analyticAt_coord (i : V) (y : V → ℂ) : AnalyticAt ℂ (fun y : V → ℂ => y i) y :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : V => ℂ) i).analyticAt y

/-- The coordinate germ w_i. -/
noncomputable def coord (i : V) : analyticGerms V := germOf (fun y => y i) (analyticAt_coord i 0)

/-- Polynomial functions are analytic. -/
theorem analyticAt_eval (P : MvPolynomial V ℂ) (y : V → ℂ) :
    AnalyticAt ℂ (fun y : V → ℂ => eval y P) y :=
  AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id ℂ (V → ℂ)) P y trivial

/-- **Polynomial evaluation.** Evaluating a polynomial at the coordinate germs gives the germ of
the polynomial function. -/
theorem aeval_coord (P : MvPolynomial V ℂ) :
    aeval coord P = germOf (fun y => eval y P) (analyticAt_eval P 0) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, ← germOf_const c analyticAt_const]
    exact germOf_congr _ _ fun y => by simp
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, ← germOf_add _ _ ((analyticAt_eval P 0).add (analyticAt_eval Q 0))]
    exact germOf_congr _ _ fun y => by simp
  | mul_X P i hP =>
    rw [map_mul, hP, aeval_X, coord,
      ← germOf_mul _ _ ((analyticAt_eval P 0).mul (analyticAt_coord i 0))]
    exact germOf_congr _ _ fun y => by simp

/-- The value at the origin, as an algebra map ℂ{w} → ℂ. -/
noncomputable def evalZero : analyticGerms V →ₐ[ℂ] ℂ where
  toRingHom := Germ.valueRingHom.comp (analyticGerms V).val.toRingHom
  commutes' _ := rfl

/-- The value at 0 of the germ of f is f(0). -/
@[simp]
theorem evalZero_germOf (f : (V → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    evalZero (germOf f hf) = f 0 := rfl

/-- The coordinate germs vanish at the origin. -/
@[simp]
theorem evalZero_coord (i : V) : evalZero (coord i) = 0 := rfl

/-- **Coordinates are nonzerodivisors.** If y_i f(y) vanishes near 0 and f is analytic at 0,
then f vanishes near 0. -/
theorem eventually_eq_zero_of_coord_mul {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (i : V)
    (h : ∀ᶠ y in 𝓝 (0 : V → ℂ), y i * f y = 0) : ∀ᶠ y in 𝓝 (0 : V → ℂ), f y = 0 := by
  classical
  have hc : ∀ᶠ y in 𝓝 (0 : V → ℂ), ContinuousAt f y :=
    hf.eventually_analyticAt.mono fun y hy => hy.continuousAt
  filter_upwards [hc, h.eventually_nhds] with y hcy hzy
  by_cases hyi : y i = 0
  · have hT : Tendsto (fun t : ℂ => y + t • Pi.single i (1 : ℂ)) (𝓝[≠] 0) (𝓝 y) := by
      have hγ : Continuous fun t : ℂ => y + t • Pi.single i (1 : ℂ) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have := hγ.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim := hcy.tendsto.comp hT
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (y + t • Pi.single i 1) = 0 := by
      filter_upwards [hT.eventually hzy, self_mem_nhdsWithin] with t ht ht0
      have hti : (y + t • Pi.single i (1 : ℂ) : V → ℂ) i = t := by simp [hyi]
      rw [hti] at ht
      exact (mul_eq_zero.1 ht).resolve_left ht0
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  · exact (mul_eq_zero.1 hzy.self_of_nhds).resolve_left hyi

/-- **Coordinates are nonzerodivisors in ℂ{w}.** -/
theorem coord_mul_eq_zero {i : V} {φ : analyticGerms V} (h : coord i * φ = 0) : φ = 0 := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  have h0 : germOf (fun _ => (0 : ℂ)) analyticAt_const = (0 : analyticGerms V) := rfl
  rw [← h0, germOf_eq_iff]
  rw [← h0, coord, ← germOf_mul (analyticAt_coord i 0) hf ((analyticAt_coord i 0).mul hf),
    germOf_eq_iff] at h
  exact eventually_eq_zero_of_coord_mul hf i h

/-- Cancellation of a coordinate germ. -/
theorem coord_mul_cancel {i : V} {φ ψ : analyticGerms V} (h : coord i * φ = coord i * ψ) :
    φ = ψ :=
  sub_eq_zero.1 (coord_mul_eq_zero (by rw [mul_sub, h, sub_self]))

/-- The truncation ideal (w_i^{r_i} : i ∈ V) of the analytic germ algebra. -/
noncomputable def truncGermIdeal (r : V → ℕ) : Ideal (analyticGerms V) :=
  Ideal.span (Set.range fun i => coord i ^ r i)

/-- Polynomial evaluation maps the polynomial truncation ideal into the germ truncation ideal. -/
theorem aeval_mem_truncGermIdeal (r : V → ℕ) {P : MvPolynomial V ℂ} (hP : P ∈ truncIdeal ℂ r) :
    aeval coord P ∈ truncGermIdeal r := by
  rw [truncIdeal_eq_span_X_pow] at hP
  have hle : Ideal.span (Set.range fun i => (X i ^ r i : MvPolynomial V ℂ)) ≤
      (truncGermIdeal r).comap (aeval coord : MvPolynomial V ℂ →ₐ[ℂ] analyticGerms V) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change aeval coord (X i ^ r i) ∈ truncGermIdeal r
    rw [map_pow, aeval_X]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hle hP

end Germs

section Pullback

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Composition of germs with a map sending 0 to 0 continuously, as an algebra map. -/
noncomputable def germComp (Φ : (V → ℂ) → (W → ℂ)) (hΦ : Tendsto Φ (𝓝 0) (𝓝 0)) :
    Germ (𝓝 (0 : W → ℂ)) ℂ →ₐ[ℂ] Germ (𝓝 (0 : V → ℂ)) ℂ where
  toFun φ := φ.compTendsto Φ hΦ
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  commutes' _ := rfl

/-- An analytic map fixing the origin tends to the origin. -/
theorem tendsto_zero_of_analyticAt {Φ : (V → ℂ) → (W → ℂ)} (hΦ : AnalyticAt ℂ Φ 0)
    (h0 : Φ 0 = 0) : Tendsto Φ (𝓝 0) (𝓝 0) := by
  have := hΦ.continuousAt.tendsto
  rwa [h0] at this

/-- Composing a function analytic at 0 with an analytic map fixing 0 gives a function analytic
at 0. -/
theorem analyticAt_comp_zero {f : (W → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0)
    {Φ : (V → ℂ) → (W → ℂ)} (hΦ : AnalyticAt ℂ Φ 0) (h0 : Φ 0 = 0) :
    AnalyticAt ℂ (fun y => f (Φ y)) 0 := by
  rw [← h0] at hf
  exact hf.comp hΦ

/-- **Pullback of analytic germs** along an analytic map Φ with Φ(0) = 0: φ ↦ φ ∘ Φ. -/
noncomputable def pullback (Φ : (V → ℂ) → (W → ℂ)) (hΦ : AnalyticAt ℂ Φ 0) (h0 : Φ 0 = 0) :
    analyticGerms W →ₐ[ℂ] analyticGerms V :=
  ((germComp Φ (tendsto_zero_of_analyticAt hΦ h0)).comp (analyticGerms W).val).codRestrict
    (analyticGerms V) fun φ => by
      obtain ⟨f, hf, rfl⟩ := exists_germOf φ
      exact ⟨f ∘ Φ, analyticAt_comp_zero hf hΦ h0, rfl⟩

/-- The pullback of the germ of f is the germ of f ∘ Φ. -/
theorem pullback_germOf (Φ : (V → ℂ) → (W → ℂ)) (hΦ : AnalyticAt ℂ Φ 0) (h0 : Φ 0 = 0)
    (f : (W → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    pullback Φ hΦ h0 (germOf f hf) =
      germOf (fun y => f (Φ y)) (analyticAt_comp_zero hf hΦ h0) := rfl

/-- The pullback depends only on the map. -/
theorem pullback_congr {Φ Φ' : (V → ℂ) → (W → ℂ)} (h : Φ = Φ') (hΦ : AnalyticAt ℂ Φ 0)
    (h0 : Φ 0 = 0) (hΦ' : AnalyticAt ℂ Φ' 0) (h0' : Φ' 0 = 0) (φ : analyticGerms W) :
    pullback Φ hΦ h0 φ = pullback Φ' hΦ' h0' φ := by
  subst h
  rfl

/-- **Functoriality** of the pullback. -/
theorem pullback_pullback {U : Type*} [Fintype U] (Φ : (U → ℂ) → (V → ℂ))
    (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0 = 0) (Ψ : (V → ℂ) → (W → ℂ)) (hΨ : AnalyticAt ℂ Ψ 0)
    (hΨ0 : Ψ 0 = 0) (hΨΦ : AnalyticAt ℂ (fun x => Ψ (Φ x)) 0) (hΨΦ0 : Ψ (Φ 0) = 0)
    (φ : analyticGerms W) :
    pullback Φ hΦ hΦ0 (pullback Ψ hΨ hΨ0 φ) = pullback (fun x => Ψ (Φ x)) hΨΦ hΨΦ0 φ := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  rfl

/-- The pullback along a map which is the identity near 0 is the identity. -/
theorem pullback_eq_self {Φ : (V → ℂ) → (V → ℂ)} (hΦ : AnalyticAt ℂ Φ 0) (h0 : Φ 0 = 0)
    (hid : ∀ᶠ x in 𝓝 0, Φ x = x) (φ : analyticGerms V) : pullback Φ hΦ h0 φ = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  rw [pullback_germOf Φ hΦ h0 f hf, germOf_eq_iff]
  filter_upwards [hid] with x hx
  rw [hx]

/-- **Analytic coordinate changes.** An analytic map Φ fixing 0 with an analytic inverse Ψ near 0
induces an algebra isomorphism of analytic germ algebras, φ ↦ φ ∘ Φ, with inverse φ ↦ φ ∘ Ψ. -/
noncomputable def pullbackEquiv {Φ Ψ : (V → ℂ) → (V → ℂ)} (hΦ : AnalyticAt ℂ Φ 0)
    (hΨ : AnalyticAt ℂ Ψ 0) (hΦ0 : Φ 0 = 0) (hΨ0 : Ψ 0 = 0) (hΨΦ : ∀ᶠ x in 𝓝 0, Ψ (Φ x) = x)
    (hΦΨ : ∀ᶠ x in 𝓝 0, Φ (Ψ x) = x) : analyticGerms V ≃ₐ[ℂ] analyticGerms V :=
  AlgEquiv.ofAlgHom (pullback Φ hΦ hΦ0) (pullback Ψ hΨ hΨ0)
    (AlgHom.ext fun φ => by
      change pullback Φ hΦ hΦ0 (pullback Ψ hΨ hΨ0 φ) = φ
      rw [pullback_pullback Φ hΦ hΦ0 Ψ hΨ hΨ0 (by rw [← hΦ0] at hΨ; exact hΨ.comp hΦ)
        (by rw [hΦ0, hΨ0])]
      exact pullback_eq_self _ _ hΨΦ φ)
    (AlgHom.ext fun φ => by
      change pullback Ψ hΨ hΨ0 (pullback Φ hΦ hΦ0 φ) = φ
      rw [pullback_pullback Ψ hΨ hΨ0 Φ hΦ hΦ0 (by rw [← hΨ0] at hΦ; exact hΦ.comp hΨ)
        (by rw [hΨ0, hΦ0])]
      exact pullback_eq_self _ _ hΦΨ φ)

/-- The isomorphism `pullbackEquiv` is composition with Φ. -/
theorem pullbackEquiv_apply {Φ Ψ : (V → ℂ) → (V → ℂ)} (hΦ : AnalyticAt ℂ Φ 0)
    (hΨ : AnalyticAt ℂ Ψ 0) (hΦ0 : Φ 0 = 0) (hΨ0 : Ψ 0 = 0) (hΨΦ : ∀ᶠ x in 𝓝 0, Ψ (Φ x) = x)
    (hΦΨ : ∀ᶠ x in 𝓝 0, Φ (Ψ x) = x) (φ : analyticGerms V) :
    pullbackEquiv hΦ hΨ hΦ0 hΨ0 hΨΦ hΦΨ φ = pullback Φ hΦ hΦ0 φ := rfl

end Pullback

end BoundaryAlgebra

end BPFixedPoints
