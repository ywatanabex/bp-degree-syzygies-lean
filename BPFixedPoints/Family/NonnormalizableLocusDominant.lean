import BPFixedPoints.Family.NonnormalizableLocusSmooth
import BPFixedPoints.Incidence.Matching
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Dominance of the parameter map on the chart (ν ≥ 1)

Over ℂ, the parameter map (a,x) ↦ (a, b(a,x)), b_i = −1/Φ_i(a,x), from the chart to the
parameter space ℂ^{E ⊕ V} is dominant when G is connected with ν(G) ≥ 1, i.e. |V| ≤ |E|. This is
the rank computation in the proof of `supp:nonnormalizable-dim`.

Choose an injection f : V → E with f(v) incident to v (`exists_incident_injection`; this exists
exactly because |V| ≤ |E| on a connected graph). Restrict the chart to the slice where x_e = −1
for e ∉ f(V) and use z = (a, (x_{f(v)})_v) as coordinates (`sliceMap`). At the point a_e = 3,
x_{f(v)} = ±1 (`slicePoint`; the sign is −1 exactly when v = fst f(v) ≠ snd f(v)), the derivative
of the slice map is block triangular with the identity on the a-block, and its x-block is the
n × n matrix (∂ log Φ_i/∂x_{f(w)}) up to invertible diagonal factors. That matrix is strictly
column diagonally dominant (diagonal entries of modulus 1 or 2, one off-diagonal entry of
modulus 1/2 or 1 per column), so it is invertible (`det_sliceLogJac_ne_zero`). This replaces the
paper's choice of orientation of the edges by a choice of signs of x.

By the inverse function theorem the image of the chart contains a nonempty open set, so a
polynomial in (a,b) vanishing on the image is zero: the parameter family is algebraically
independent, i.e. the ℂ-algebra map ℂ[a,b] → ChartRing ℂ is injective
(`chartRingFamily_algebraicIndependent`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial Filter Topology Metric

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section LogJac

variable {K : Type*} [Field K]

/-- The logarithmic Jacobian ∂ log Φ_i/∂x_e: [fst e = i]/x_e +
[snd e = i](a_e² − 1)/((1 − a_e x_e)(a_e − x_e)). -/
def chartLogJac (a x : E → K) : Matrix V E K := fun i e =>
  (if G.fst e = i then 1 / x e else 0) +
    (if G.snd e = i then (a e ^ 2 - 1) / ((1 - a e * x e) * (a e - x e)) else 0)

theorem chartJac_eq_mul_logJac (a x : E → K) (i : V) (e : E) :
    G.chartJac a x i e = G.chartField a x i * G.chartLogJac a x i e := by
  unfold chartJac chartLogJac
  split_ifs <;> ring

end LogJac

section Slice

variable (f : V → E)

/-- The a-coordinates of a slice point z. -/
def sliceA (z : E ⊕ V → ℂ) : E → ℂ := fun e => z (Sum.inl e)

/-- The x-coordinates of a slice point: x_{f(v)} = z_v and x_e = −1 off the image of f. -/
noncomputable def sliceX (z : E ⊕ V → ℂ) : E → ℂ :=
  Function.extend f (fun v => z (Sum.inr v)) (fun _ => -1)

/-- The slice parameter map z ↦ (a, −1/Φ(a,x)). -/
noncomputable def sliceMap (z : E ⊕ V → ℂ) : E ⊕ V → ℂ :=
  Sum.elim (sliceA z) (fun i => -(G.chartField (sliceA z) (sliceX f z) i)⁻¹)

/-- Signs of the base point: −1 when v = fst f(v) ≠ snd f(v), and 1 otherwise. -/
def sliceSign (v : V) : ℂ := if G.fst (f v) = v ∧ G.snd (f v) ≠ v then -1 else 1

/-- The base point a_e = 3, x_{f(v)} = ±1. -/
def slicePoint : E ⊕ V → ℂ := Sum.elim (fun _ => 3) (G.sliceSign f)

variable {f}

theorem sliceX_apply_f (hf : Function.Injective f) (z : E ⊕ V → ℂ) (v : V) :
    sliceX f z (f v) = z (Sum.inr v) :=
  hf.extend_apply _ _ v

theorem sliceX_apply_of_not_mem {e : E} (he : ∀ v, f v ≠ e) (z : E ⊕ V → ℂ) :
    sliceX f z e = -1 :=
  Function.extend_apply' _ _ e (fun ⟨v, hv⟩ => he v hv)

theorem sliceX_slicePoint (hf : Function.Injective f) (e : E) :
    sliceX f (G.slicePoint f) e = 1 ∨ sliceX f (G.slicePoint f) e = -1 := by
  by_cases he : ∃ v, f v = e
  · obtain ⟨v, rfl⟩ := he
    rw [sliceX_apply_f hf]
    simp only [slicePoint, Sum.elim_inr, sliceSign]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · push Not at he
    exact Or.inr (sliceX_apply_of_not_mem he _)

theorem isChartPoint_slicePoint (hf : Function.Injective f) :
    IsChartPoint (sliceA (G.slicePoint f)) (sliceX f (G.slicePoint f)) := by
  intro e
  have ha : sliceA (G.slicePoint f) e = 3 := rfl
  rw [ha]
  rcases G.sliceX_slicePoint hf e with h | h <;> rw [h] <;> norm_num

/-- The x-block of the logarithmic Jacobian at the base point: N_{i,w} = ∂ log Φ_i/∂x_{f(w)}. -/
noncomputable def sliceLogJac (f : V → E) : Matrix V V ℂ := fun i w =>
  G.chartLogJac (sliceA (G.slicePoint f)) (sliceX f (G.slicePoint f)) i (f w)

theorem sum_erase_norm_ite_le {w : V} (c₁ c₂ : ℂ) (u₁ u₂ : V) :
    ∑ i ∈ Finset.univ.erase w, ‖(if u₁ = i then c₁ else 0) + (if u₂ = i then c₂ else 0)‖ ≤
      (if u₁ ≠ w then ‖c₁‖ else 0) + (if u₂ ≠ w then ‖c₂‖ else 0) := by
  calc ∑ i ∈ Finset.univ.erase w, ‖(if u₁ = i then c₁ else 0) + (if u₂ = i then c₂ else 0)‖
      ≤ ∑ i ∈ Finset.univ.erase w, (‖(if u₁ = i then c₁ else 0 : ℂ)‖ +
          ‖(if u₂ = i then c₂ else 0 : ℂ)‖) :=
        Finset.sum_le_sum fun i _ => norm_add_le _ _
    _ = (if u₁ ≠ w then ‖c₁‖ else 0) + (if u₂ ≠ w then ‖c₂‖ else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [apply_ite norm, norm_zero, Finset.sum_ite_eq, Finset.mem_erase,
          Finset.mem_univ, and_true]

/-- **The rank computation.** The matrix (∂ log Φ_i/∂x_{f(w)}) at the base point is strictly
column diagonally dominant, hence invertible. -/
theorem det_sliceLogJac_ne_zero (hf : Function.Injective f) (hinc : ∀ v, G.Incident (f v) v) :
    (G.sliceLogJac f).det ≠ 0 := by
  apply det_ne_zero_of_sum_col_lt_diag
  intro w
  have hx : sliceX f (G.slicePoint f) (f w) = G.sliceSign f w := sliceX_apply_f hf _ w
  have ha : sliceA (G.slicePoint f) (f w) = 3 := rfl
  simp only [sliceLogJac, chartLogJac, hx, ha]
  refine lt_of_le_of_lt (sum_erase_norm_ite_le _ _ _ _) ?_
  rcases hinc w with h1 | h2
  · by_cases h2 : G.snd (f w) = w
    · have hs : G.sliceSign f w = 1 := by simp [sliceSign, h2]
      simp only [h1, h2, hs, ne_eq, not_true_eq_false, ite_false, ite_true]
      norm_num
    · have hs : G.sliceSign f w = -1 := by simp [sliceSign, h1, h2]
      simp only [h1, h2, hs, ne_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true]
      norm_num
  · by_cases h1 : G.fst (f w) = w
    · have hs : G.sliceSign f w = 1 := by simp [sliceSign, h2]
      simp only [h1, h2, hs, ne_eq, not_true_eq_false, ite_false, ite_true]
      norm_num
    · have hs : G.sliceSign f w = 1 := by simp [sliceSign, h1]
      simp only [h1, h2, hs, ne_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true]
      norm_num

theorem contDiff_sliceX (hf : Function.Injective f) (n : WithTop ℕ∞) (e : E) :
    ContDiff ℂ n (fun z => sliceX f z e) := by
  by_cases he : ∃ v, f v = e
  · obtain ⟨v, rfl⟩ := he
    have h2 : (fun z => sliceX f z (f v)) = fun z : E ⊕ V → ℂ => z (Sum.inr v) :=
      funext fun z => sliceX_apply_f hf z v
    rw [h2]
    exact contDiff_apply (𝕜 := ℂ) (F' := fun _ : E ⊕ V => ℂ) (Sum.inr v)
  · push Not at he
    have : (fun z => sliceX f z e) = fun _ => (-1 : ℂ) :=
      funext fun z => sliceX_apply_of_not_mem he z
    rw [this]
    exact contDiff_const

theorem contDiff_sliceA (n : WithTop ℕ∞) (e : E) :
    ContDiff ℂ n (fun z : E ⊕ V → ℂ => sliceA z e) :=
  contDiff_apply (𝕜 := ℂ) (F' := fun _ : E ⊕ V => ℂ) (Sum.inl e)

theorem contDiffAt_chartField_slice (hf : Function.Injective f) (n : WithTop ℕ∞)
    {z : E ⊕ V → ℂ} (hz : IsChartPoint (sliceA z) (sliceX f z)) (i : V) :
    ContDiffAt ℂ n (fun z => G.chartField (sliceA z) (sliceX f z) i) z := by
  show ContDiffAt ℂ n (fun z => ∏ e, (if G.fst e = i then sliceX f z e else 1) *
    (if G.snd e = i then edgeInvolution (sliceA z e) (sliceX f z e) else 1)) z
  refine contDiffAt_prod (fun e _ => ?_)
  refine ContDiffAt.mul ?_ ?_
  · split_ifs
    · exact (contDiff_sliceX hf n e).contDiffAt
    · exact contDiffAt_const
  · split_ifs
    · unfold edgeInvolution
      refine ContDiffAt.div ?_ ?_ (one_sub_mul_ne_zero (hz e).2.2)
      · exact (contDiff_sliceA n e).contDiffAt.sub (contDiff_sliceX hf n e).contDiffAt
      · exact contDiffAt_const.sub
          ((contDiff_sliceA n e).contDiffAt.mul (contDiff_sliceX hf n e).contDiffAt)
    · exact contDiffAt_const

/-- The slice map is smooth at every slice point that is a chart point. -/
theorem contDiffAt_sliceMap (hf : Function.Injective f) (n : WithTop ℕ∞) {z : E ⊕ V → ℂ}
    (hz : IsChartPoint (sliceA z) (sliceX f z)) : ContDiffAt ℂ n (G.sliceMap f) z := by
  apply contDiffAt_pi'
  rintro (e | i)
  · exact (contDiff_sliceA n e).contDiffAt
  · simp only [sliceMap, Sum.elim_inr]
    exact ((G.contDiffAt_chartField_slice hf n hz i).inv (G.chartField_ne_zero hz i)).neg

/-- Moving along the coordinate x_{f(w)} of the slice. -/
theorem sliceX_add_single (hf : Function.Injective f) (z : E ⊕ V → ℂ) (w : V) (t : ℂ) :
    sliceX f (z + t • Pi.single (Sum.inr w) 1) =
      Function.update (sliceX f z) (f w) (sliceX f z (f w) + t) := by
  funext e
  by_cases he : ∃ v, f v = e
  · obtain ⟨v, rfl⟩ := he
    rw [sliceX_apply_f hf, sliceX_apply_f hf]
    by_cases hv : v = w
    · subst hv
      simp
    · rw [Function.update_of_ne (fun h => hv (hf h)), sliceX_apply_f hf]
      simp [hv]
  · push Not at he
    rw [sliceX_apply_of_not_mem he, Function.update_of_ne (fun h => he w h.symm),
      sliceX_apply_of_not_mem he]

theorem sliceA_add_single (z : E ⊕ V → ℂ) (w : V) (t : ℂ) :
    sliceA (z + t • Pi.single (Sum.inr w) 1) = sliceA z := by
  funext e
  simp [sliceA]

/-- Derivative of the b_i-component of the slice map along the coordinate x_{f(w)}. -/
theorem hasDerivAt_sliceMap_line (hf : Function.Injective f) {z : E ⊕ V → ℂ}
    (hz : IsChartPoint (sliceA z) (sliceX f z)) (w i : V) :
    HasDerivAt (fun t : ℂ => G.sliceMap f (z + t • Pi.single (Sum.inr w) 1) (Sum.inr i))
      (G.chartJac (sliceA z) (sliceX f z) i (f w) /
        G.chartField (sliceA z) (sliceX f z) i ^ 2) 0 := by
  have hfun : (fun t : ℂ => G.sliceMap f (z + t • Pi.single (Sum.inr w) 1) (Sum.inr i)) =
      fun t => -(G.chartField (sliceA z)
        (Function.update (sliceX f z) (f w) (sliceX f z (f w) + t)) i)⁻¹ := by
    funext t
    simp only [sliceMap, Sum.elim_inr, sliceA_add_single, sliceX_add_single hf]
  rw [hfun]
  have h1 := G.hasDerivAt_chartField_update (sliceA z) (sliceX f z) hz i (f w)
  have h2 : HasDerivAt (fun t => G.chartField (sliceA z)
      (Function.update (sliceX f z) (f w) (sliceX f z (f w) + t)) i)
      (G.chartJac (sliceA z) (sliceX f z) i (f w)) 0 :=
    HasDerivAt.comp_const_add (sliceX f z (f w)) 0 (by rwa [add_zero])
  have hne : G.chartField (sliceA z)
      (Function.update (sliceX f z) (f w) (sliceX f z (f w) + 0)) i ≠ 0 := by
    rw [add_zero, Function.update_eq_self]
    exact G.chartField_ne_zero hz i
  have h3 := (h2.inv hne).neg
  rw [add_zero, Function.update_eq_self] at h3
  convert h3 using 1
  ring

/-- Points near a chart point are chart points. -/
theorem eventually_isChartPoint (hf : Function.Injective f) {z₀ : E ⊕ V → ℂ}
    (hz : IsChartPoint (sliceA z₀) (sliceX f z₀)) :
    ∀ᶠ z in 𝓝 z₀, IsChartPoint (sliceA z) (sliceX f z) := by
  refine Filter.eventually_all.mpr fun e => ?_
  have hA := (contDiff_sliceA (V := V) 0 e).continuous.continuousAt (x := z₀)
  have hX := (contDiff_sliceX hf 0 e).continuous.continuousAt (x := z₀)
  obtain ⟨h0, h1, h2⟩ := hz e
  refine ((hX.eventually_ne h0).and ((hX.sub hA).eventually_ne (sub_ne_zero.mpr h1))).and
    ((hA.mul hX).eventually_ne h2) |>.mono fun z hz => ⟨hz.1.1, ?_, hz.2⟩
  exact sub_ne_zero.mp hz.1.2

/-- **Invertibility of the derivative at the base point.** -/
theorem fderiv_sliceMap_injective (hf : Function.Injective f)
    (hinc : ∀ v, G.Incident (f v) v) :
    Function.Injective (fderiv ℂ (G.sliceMap f) (G.slicePoint f)) := by
  set z₀ := G.slicePoint f with hz₀def
  set D := fderiv ℂ (G.sliceMap f) z₀
  have hz₀ : IsChartPoint (sliceA z₀) (sliceX f z₀) := G.isChartPoint_slicePoint hf
  have hD : HasFDerivAt (G.sliceMap f) D z₀ :=
    ((G.contDiffAt_sliceMap hf 1 hz₀).differentiableAt (by norm_num)).hasFDerivAt
  have hinl : ∀ (v : E ⊕ V → ℂ) (e : E), D v (Sum.inl e) = v (Sum.inl e) := by
    intro v e
    have h1 := hasFDerivAt_pi'.mp hD (Sum.inl e)
    have h2 : HasFDerivAt (fun z : E ⊕ V → ℂ => G.sliceMap f z (Sum.inl e))
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : E ⊕ V => ℂ) (Sum.inl e)) z₀ :=
      hasFDerivAt_apply (Sum.inl e) z₀
    have := h1.unique h2
    exact congrArg (fun L => L v) this
  have hinr : ∀ w i, D (Pi.single (Sum.inr w) 1) (Sum.inr i) =
      G.chartJac (sliceA z₀) (sliceX f z₀) i (f w) /
        G.chartField (sliceA z₀) (sliceX f z₀) i ^ 2 := by
    intro w i
    have h1 := hasFDerivAt_pi'.mp hD (Sum.inr i)
    have hγ : HasDerivAt (fun t : ℂ => z₀ + t • Pi.single (Sum.inr w) (1 : ℂ))
        (Pi.single (Sum.inr w) 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single (Sum.inr w) (1 : ℂ))).const_add z₀
    have h1' : HasFDerivAt (fun z => G.sliceMap f z (Sum.inr i))
        ((ContinuousLinearMap.proj (Sum.inr i)).comp D)
        (z₀ + (0 : ℂ) • Pi.single (Sum.inr w) 1) := by
      simpa using h1
    have h2 := h1'.comp_hasDerivAt (0 : ℂ) hγ
    exact h2.unique (G.hasDerivAt_sliceMap_line hf hz₀ w i)
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hva : ∀ e, v (Sum.inl e) = 0 := fun e => by
    have := hinl v e
    rw [hv] at this
    simpa using this.symm
  have hdecomp : v = ∑ w, v (Sum.inr w) • Pi.single (Sum.inr w) (1 : ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [Fintype.sum_sum_type]
    simp only [hva, Pi.single_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hrow : ∀ i, ∑ w, G.sliceLogJac f i w * v (Sum.inr w) = 0 := by
    intro i
    have h := congrFun (congrArg D hdecomp ▸ hv) (Sum.inr i)
    rw [map_sum] at h
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hinr,
      Pi.zero_apply] at h
    have hΦ := G.chartField_ne_zero hz₀ i
    have h' : ∑ w, G.sliceLogJac f i w * v (Sum.inr w) =
        G.chartField (sliceA z₀) (sliceX f z₀) i *
          ∑ w, v (Sum.inr w) * (G.chartJac (sliceA z₀) (sliceX f z₀) i (f w) /
            G.chartField (sliceA z₀) (sliceX f z₀) i ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [chartJac_eq_mul_logJac]
      simp only [sliceLogJac, ← hz₀def]
      field_simp
    rw [h', h, mul_zero]
  have hu : (fun w => v (Sum.inr w)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (G.det_sliceLogJac_ne_zero hf hinc) (funext hrow)
  funext k
  rcases k with e | w
  · exact hva e
  · exact congrFun hu w

/-- **Inverse function theorem on the slice.** The image of the chart points of the slice
contains a ball around the image of the base point. -/
theorem exists_ball_subset_image (hf : Function.Injective f)
    (hinc : ∀ v, G.Incident (f v) v) :
    ∃ ε > 0, ball (G.sliceMap f (G.slicePoint f)) ε ⊆
      G.sliceMap f '' {z | IsChartPoint (sliceA z) (sliceX f z)} := by
  set z₀ := G.slicePoint f
  have hz₀ : IsChartPoint (sliceA z₀) (sliceX f z₀) := G.isChartPoint_slicePoint hf
  set D := fderiv ℂ (G.sliceMap f) z₀
  have hS : HasStrictFDerivAt (G.sliceMap f) D z₀ :=
    (G.contDiffAt_sliceMap hf 1 hz₀).hasStrictFDerivAt (by norm_num)
  have hinj : Function.Injective D := G.fderiv_sliceMap_injective hf hinc
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f := (D : (E ⊕ V → ℂ) →ₗ[ℂ] (E ⊕ V → ℂ)))).mp hinj
  let L := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hS' : HasStrictFDerivAt (G.sliceMap f) (L : (E ⊕ V → ℂ) →L[ℂ] (E ⊕ V → ℂ)) z₀ := by
    rwa [ContinuousLinearEquiv.coe_ofBijective]
  have hmap := hS'.map_nhds_eq_of_equiv
  have hU : {z | IsChartPoint (sliceA z) (sliceX f z)} ∈ 𝓝 z₀ :=
    eventually_isChartPoint hf hz₀
  have himg : G.sliceMap f '' {z | IsChartPoint (sliceA z) (sliceX f z)} ∈
      𝓝 (G.sliceMap f z₀) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  exact Metric.mem_nhds_iff.mp himg

end Slice

section Dominance

variable {k : Type*} [CommRing k] {K : Type*} [Field K] [Algebra k K]

/-- Evaluation at a chart point commutes with evaluation of polynomials over the base ring. -/
theorem chartRingEval_aeval {a x : E → K} (hx : IsChartPoint a x) {ι : Type*}
    (g : ι → ChartRing (E := E) k) (P : MvPolynomial ι k) :
    chartRingEval a x hx (aeval g P) = aeval (chartRingEval a x hx ∘ g) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, aeval_C, IsScalarTower.algebraMap_apply k (MvPolynomial (E ⊕ E) k),
      chartRingEval_algebraMap, MvPolynomial.algebraMap_eq, aeval_C]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p z hp => rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Function.comp_apply]

/-- **Dominance (`supp:nonnormalizable-dim`).** If G is connected and |V| ≤ |E| (ν(G) ≥ 1), the
parameter functions a_e and b_i = −1/Φ_i on the complex chart ring are algebraically
independent; equivalently the parameter map from the chart to ℂ^{E ⊕ V} is dominant. -/
theorem chartRingFamily_algebraicIndependent (hc : G.Connected)
    (hcard : Fintype.card V ≤ Fintype.card E) :
    AlgebraicIndependent ℂ (G.chartRingFamily ℂ) := by
  obtain ⟨f₀, hf₀, hinc₀⟩ := G.exists_incident_injection hc Finset.univ (Or.inr hcard)
  set f : V → E := fun v => f₀ ⟨v, Finset.mem_univ v⟩
  have hf : Function.Injective f := fun v w h => by
    have := hf₀ h
    simpa using congrArg Subtype.val this
  have hinc : ∀ v, G.Incident (f v) v := fun v => hinc₀ ⟨v, Finset.mem_univ v⟩
  obtain ⟨ε, hε, hball⟩ := G.exists_ball_subset_image hf hinc
  rw [algebraicIndependent_iff]
  intro P hP
  set c := G.sliceMap f (G.slicePoint f)
  apply MvPolynomial.funext_set (fun i => ball (c i) ε)
    (fun i => infinite_of_mem_nhds (c i) (ball_mem_nhds _ hε))
  intro y hy
  have hyball : y ∈ ball c ε := by
    rw [ball_pi _ hε]
    exact hy
  obtain ⟨z, hz, rfl⟩ := hball hyball
  have h := congrArg (chartRingEval (k := ℂ) (sliceA z) (sliceX f z) hz) hP
  rw [chartRingEval_aeval, map_zero, chartRingEval_comp_family] at h
  simp only [map_zero]
  rw [← h]
  rfl

end Dominance

end Multigraph

end BPFixedPoints
