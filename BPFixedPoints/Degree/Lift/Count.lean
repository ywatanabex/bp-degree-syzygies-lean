import BPFixedPoints.Degree.Boundary.ValuedField
import BPFixedPoints.Degree.Lift.ValuedTaylor
import BPFixedPoints.Degree.Lift.Formal

/-!
# Complete solution count over a Puiseux-type valued field

For `P:PuiseuxField K`, with algebraically closed characteristic-zero L,
valuation v, embedding `ofPS` of K⟦t⟧ and residue field K, auxiliary parameters
s_e=1+t c_e and β_i∈K with c_e≠0, β_i≠0,−1 have exactly Q(G) admissible L-solutions.
Each lift `liftOf` maps through `ofPS` to a distinct admissible solution.
Conversely boundary exclusion makes every admissible solution integral and a
unit in each coordinate; its residue is a limit point. The solution and that
point's lift agree modulo the maximal ideal and have unit Jacobian, so agree
by `unique_of_cong`. Only `PuiseuxField` hypotheses are used; existence is
`newtonPuiseux_exists` in `Degree/Boundary/ValuedFieldExists.lean`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

universe u

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type u} [Field K] [DecidableEq K] (P : PuiseuxField K)

/-! ### Parameters and solution sets -/

/-- Parameter s_e=1+t c_e in L. -/
noncomputable def sP (c : E → K) (e : E) : P.L := 1 + P.t * P.ofK (c e)

/-- Parameter β_i in L. -/
noncomputable def βP (β : V → K) (i : V) : P.L := P.ofK (β i)

theorem sP_eq (c : E → K) (e : E) :
    sP P c e = P.ofPS (1 + PowerSeries.X * PowerSeries.C (c e)) := by
  simp [sP, map_add, map_mul, map_one, P.ofPS_X, P.ofPS_C]

theorem βP_eq (β : V → K) (i : V) : βP P β i = P.ofPS (PowerSeries.C (β i)) := by
  simp [βP, P.ofPS_C]

/-- Set of auxiliary L-solutions. -/
def PuiseuxSolutions (c : E → K) (β : V → K) : Type _ :=
  {p : (Dart E → P.L) × (V → P.L) // G.IsAuxSolution (sP P c) (βP P β) p.1 p.2}

theorem val_sP_sub_one_lt (c : E → K) (e : E) : P.v (sP P c e - 1) < 1 := by
  rw [sP_eq, ← map_one P.ofPS, ← map_sub, P.val_ofPS_lt_one_iff]
  simp

theorem val_βP (β : V → K) (hβ0 : ∀ i, β i ≠ 0) (i : V) : P.v (βP P β i) = 1 :=
  P.val_ofK _ (hβ0 i)

theorem val_βP_add_one (β : V → K) (hβ1 : ∀ i, β i ≠ -1) (i : V) : P.v (βP P β i + 1) = 1 := by
  unfold βP
  rw [← map_one P.ofK, ← map_add]
  exact P.val_ofK _ (fun h => hβ1 i (by linear_combination h))

/-! ### Mapping the one-parameter system by a ring homomorphism -/

/-- An injective ring homomorphism from K[[t]] to L' sends a family root to an admissible auxiliary root. -/
theorem isAuxSolution_map_of_weakSolution {L' : Type*} [Field L'] (φ : K⟦X⟧ →+* L')
    (hφ : Function.Injective φ) (c : E → K) (β : V → K) {x : Var V E → K⟦X⟧}
    (hx : ∀ v, eval x (G.weakSystem c β v) = 0)
    (hA0 : ∀ α, x (Sum.inl α) ≠ 0) (hA1 : ∀ α, x (Sum.inl α) + 1 ≠ 0)
    (hF0 : ∀ i, x (Sum.inr i) ≠ 0) (hF1 : ∀ i, x (Sum.inr i) + 1 ≠ 0) :
    G.IsAuxSolution (fun e => φ (1 + PowerSeries.X * PowerSeries.C (c e)))
      (fun i => φ (PowerSeries.C (β i))) (fun α => φ (x (Sum.inl α)))
      (fun i => φ (x (Sum.inr i))) where
  A_ne_zero α h := hA0 α (hφ (by rw [h, map_zero]))
  A_ne_neg_one α h := by
    apply hA1 α
    apply hφ
    rw [map_add, map_one, h, map_zero]
    ring
  F_ne_zero i h := hF0 i (hφ (by rw [h, map_zero]))
  F_ne_neg_one i h := by
    apply hF1 i
    apply hφ
    rw [map_add, map_one, h, map_zero]
    ring
  edge α := by
    have h := hx (Sum.inl α)
    simp only [weakSystem, edgePoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, map_one] at h
    have key : x (Sum.inr (G.tail α)) * (1 + x (Sum.inl (rev α))) =
        x (Sum.inl α) * (1 + (1 + PowerSeries.X * PowerSeries.C (c α.1)) * x (Sum.inl (rev α))) := by
      linear_combination -h
    have := congrArg φ key
    simpa using this
  vertex i := by
    have h := hx (Sum.inr i)
    simp only [weakSystem, vertexPoly, eval_sub, eval_mul, eval_X, eval_prod, eval_C,
      eval_pow] at h
    have key : x (Sum.inr i) * ∏ α ∈ G.inDarts i, x (Sum.inl (rev α)) =
        PowerSeries.C (β i) * x (Sum.inr i) ^ G.degree i := by linear_combination h
    have key' : φ (x (Sum.inr i)) * ∏ α ∈ G.inDarts i, φ (x (Sum.inl (rev α))) =
        φ (PowerSeries.C (β i)) * φ (x (Sum.inr i)) ^ G.degree i := by
      have := congrArg φ key
      simpa using this
    have hF : φ (x (Sum.inr i)) ≠ 0 := fun h => hF0 i (hφ (by rw [h, map_zero]))
    rw [zpow_sub₀ hF, zpow_one, zpow_natCast, div_mul_eq_mul_div, key', mul_div_assoc,
      div_self (pow_ne_zero _ hF), mul_one]

section Lift

variable [CharZero K] (c : E → K) (β : V → K) (hβ1 : ∀ i, β i ≠ -1)

/-- Interpret a limit point's lift as a solution over L. -/
noncomputable def liftToPuiseux (q : G.LimitParams β) : (Dart E → P.L) × (V → P.L) :=
  (fun α => P.ofPS (G.liftOf c β hβ1 q (Sum.inl α)), fun i => P.ofPS (G.liftOf c β hβ1 q (Sum.inr i)))

theorem isAuxSolution_liftToPuiseux (hc : ∀ e, c e ≠ 0) (q : G.LimitParams β) :
    G.IsAuxSolution (sP P c) (βP P β) (G.liftToPuiseux P c β hβ1 q).1
      (G.liftToPuiseux P c β hβ1 q).2 := by
  obtain ⟨h0, hsol⟩ := G.liftOf_spec c β hβ1 q
  obtain ⟨hA0, hA1, hF0, hF1⟩ := G.lift_admissible hc hβ1 q.2 _ h0 hsol
  have := G.isAuxSolution_map_of_weakSolution P.ofPS P.ofPS_injective c β hsol hA0 hA1 hF0 hF1
  have hs : (fun e => P.ofPS (1 + PowerSeries.X * PowerSeries.C (c e))) = sP P c := by
    funext e; rw [sP_eq]
  have hb : (fun i => P.ofPS (PowerSeries.C (β i))) = βP P β := by
    funext i; rw [βP_eq]
  rw [hs, hb] at this
  exact this

/-- Map from limit points to L-solutions. -/
noncomputable def toPuiseuxSolution (hc : ∀ e, c e ≠ 0) (q : G.LimitParams β) :
    G.PuiseuxSolutions P c β :=
  ⟨G.liftToPuiseux P c β hβ1 q, G.isAuxSolution_liftToPuiseux P c β hβ1 hc q⟩

theorem toPuiseuxSolution_injective (hc : ∀ e, c e ≠ 0) :
    Function.Injective (G.toPuiseuxSolution P c β hβ1 hc) := by
  intro p q hpq
  apply G.liftOf_injective c β hβ1
  have h := congrArg (fun s : G.PuiseuxSolutions P c β => s.1) hpq
  simp only [toPuiseuxSolution, liftToPuiseux] at h
  funext j
  rcases j with α | i
  · exact P.ofPS_injective (congrFun (congrArg Prod.fst h) α)
  · exact P.ofPS_injective (congrFun (congrArg Prod.snd h) i)

end Lift

/-! ### Residues and congruences -/

section Residue

variable {P}

theorem val_ofK_le_one (a : K) : P.v (P.ofK a) ≤ 1 := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · exact (P.val_ofK a h).le

theorem cong_ofK_iff {a b : K} : Cong P.v (P.ofK a) (P.ofK b) ↔ a = b :=
  ⟨fun h => P.eq_of_val_ofK_sub_lt h, fun h => h ▸ Cong.refl _⟩

theorem cong_ofPS_ofK (f : K⟦X⟧) :
    Cong P.v (P.ofPS f) (P.ofK (PowerSeries.constantCoeff f)) := by
  unfold Cong
  rw [← P.ofPS_C, ← map_sub, P.val_ofPS_lt_one_iff]
  simp

theorem Cong.sum {ι : Type*} (s : Finset ι) (f g : ι → P.L)
    (h : ∀ i ∈ s, Cong P.v (f i) (g i)) : Cong P.v (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Cong.refl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Evaluating a power-series polynomial after `ofPS` at an integral point gives an integral element congruent to the constant-coefficient evaluation. -/
theorem eval_map_ofPS_spec {ι : Type*} (g : MvPolynomial ι K⟦X⟧) {x : ι → P.L} {x₀ : ι → K}
    (hx : ∀ j, P.v (x j) ≤ 1) (hc : ∀ j, Cong P.v (x j) (P.ofK (x₀ j))) :
    P.v (eval x (map P.ofPS g)) ≤ 1 ∧
      Cong P.v (eval x (map P.ofPS g))
        (P.ofK (eval x₀ (map PowerSeries.constantCoeff g))) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp only [map_C, eval_C]
    exact ⟨P.val_ofPS_le_one a, cong_ofPS_ofK a⟩
  | add p q hp hq =>
    simp only [map_add, eval_add]
    exact ⟨P.v.map_add_le hp.1 hq.1, hp.2.add hq.2⟩
  | mul_X p n hp =>
    simp only [map_mul, map_X, eval_mul, eval_X]
    refine ⟨?_, hp.2.mul hp.1 (val_ofK_le_one _) (hc n)⟩
    calc P.v (eval x (map P.ofPS p)) * P.v (x n) ≤ 1 * 1 := mul_le_mul' hp.1 (hx n)
      _ = 1 := one_mul 1

end Residue

/-! ### Systems and Jacobians over the valuation ring -/

section Integral

/-- K⟦t⟧ → 𝒪 = v.integer。 -/
noncomputable def ofPSO : K⟦X⟧ →+* P.v.integer :=
  P.ofPS.codRestrict P.v.integer fun f => (Valuation.mem_integer_iff _ _).2 (P.val_ofPS_le_one f)

theorem subtype_comp_ofPSO : P.v.integer.subtype.comp (ofPSO P) = P.ofPS := by
  ext f; rfl

variable (c : E → K) (β : V → K)

/-- View the one-parameter system over the valuation ring. -/
noncomputable def weakSystemO (w : Var V E) : MvPolynomial (Var V E) P.v.integer :=
  map (ofPSO P) (G.weakSystem c β w)

theorem coe_eval_weakSystemO (xO : Var V E → P.v.integer) (w : Var V E) :
    ((eval xO (G.weakSystemO P c β w) : P.v.integer) : P.L) =
      eval (fun j => (xO j : P.L)) (map P.ofPS (G.weakSystem c β w)) := by
  change P.v.integer.subtype _ = _
  rw [weakSystemO, map_eval', map_map, subtype_comp_ofPSO]
  rfl

theorem coe_eval_pderiv_weakSystemO (xO : Var V E → P.v.integer) (i j : Var V E) :
    ((eval xO (pderiv j (G.weakSystemO P c β i)) : P.v.integer) : P.L) =
      eval (fun k => (xO k : P.L)) (map P.ofPS (pderiv j (G.weakSystem c β i))) := by
  change P.v.integer.subtype _ = _
  rw [weakSystemO, pderiv_map, map_eval', map_map, subtype_comp_ofPSO]
  rfl

/-- The integral Jacobian determinant is congruent to the limit-system determinant at the residue point. -/
theorem cong_det_jacO {xO : Var V E → P.v.integer} {x₀ : Var V E → K}
    (hc : ∀ j, Cong P.v (xO j : P.L) (P.ofK (x₀ j))) :
    Cong P.v (((Matrix.of fun i j => eval xO (pderiv j (G.weakSystemO P c β i))).det :
        P.v.integer) : P.L) (P.ofK (G.jacLimit c β x₀).det) := by
  have hx : ∀ j, P.v (xO j : P.L) ≤ 1 := fun j => (xO j).2
  change Cong P.v (P.v.integer.subtype (Matrix.det _)) _
  rw [RingHom.map_det, Matrix.det_apply', Matrix.det_apply', map_sum]
  apply Cong.sum
  intro σ _
  rw [map_mul, map_intCast]
  have hε : P.v (((Equiv.Perm.sign σ : ℤ) : P.L)) ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine Cong.mul hε (val_ofK_le_one _) (Cong.refl _) ?_
  rw [map_prod]
  refine Cong.prod _ _ _ ?_ (fun i _ => val_ofK_le_one _) ?_
  · intro i _
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact (eval xO (pderiv i (G.weakSystemO P c β (σ i)))).2
  · intro i _
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, jacLimit]
    change Cong P.v ((eval xO (pderiv i (G.weakSystemO P c β (σ i))) : P.v.integer) : P.L) _
    rw [coe_eval_pderiv_weakSystemO]
    have := (eval_map_ofPS_spec (pderiv i (G.weakSystem c β (σ i))) hx hc).2
    rw [← map_constantCoeff_weakSystem, pderiv_map]
    exact this

end Integral

/-! ### Every L-solution is a lift -/

section Surj

variable [CharZero K] (c : E → K) (β : V → K)

/-- The coordinates of an L-solution form a zero of the one-parameter polynomial system over L. -/
theorem eval_map_ofPS_weakSystem_eq_zero {A : Dart E → P.L} {F : V → P.L}
    (h : G.IsAuxSolution (sP P c) (βP P β) A F) (w : Var V E) :
    eval (Sum.elim A F) (map P.ofPS (G.weakSystem c β w)) = 0 := by
  rcases w with α | i
  · simp only [weakSystem, edgePoly, map_add, map_mul, map_sub, map_X, map_C, map_one,
      eval_add, eval_mul, eval_sub, eval_X, eval_C, Sum.elim_inl, Sum.elim_inr, P.ofPS_X,
      P.ofPS_C]
    have he := h.edge α
    simp only [sP] at he
    linear_combination -he
  · simp only [weakSystem, vertexPoly, map_sub, map_mul, map_X, map_C, map_pow, map_prod,
      eval_sub, eval_mul, eval_X, eval_C, eval_pow, eval_prod, Sum.elim_inl, Sum.elim_inr,
      P.ofPS_C]
    have hv := h.vertex i
    simp only [βP] at hv
    have hF : F i ≠ 0 := h.F_ne_zero i
    rw [hv, zpow_sub₀ hF, zpow_one, zpow_natCast]
    field_simp
    ring

/-- Every admissible L-root equals the image of the lift of its residue limit point. -/
theorem exists_lift_of_puiseuxSolution (hc : ∀ e, c e ≠ 0) (hβ0 : ∀ i, β i ≠ 0)
    (hβ1 : ∀ i, β i ≠ -1) (p : G.PuiseuxSolutions P c β) :
    ∃ q : G.LimitParams β, G.toPuiseuxSolution P c β hβ1 hc q = p := by
  obtain ⟨⟨A, F⟩, h⟩ := p
  change G.IsAuxSolution (sP P c) (βP P β) A F at h
  obtain ⟨hFu, hAu, hF1u⟩ := boundary_exclusion P.v (val_sP_sub_one_lt P c) (val_βP P β hβ0)
    (val_βP_add_one P β hβ1) h
  -- Take residues.
  choose a₀ ha₀ using fun α => P.residue (A α) (hAu α).le
  choose f₀ hf₀ using fun i => P.residue (F i) (hFu i).le
  have hcA : ∀ α, Cong P.v (A α) (P.ofK (a₀ α)) := ha₀
  have hcF : ∀ i, Cong P.v (F i) (P.ofK (f₀ i)) := hf₀
  have hf₀0 : ∀ i, f₀ i ≠ 0 := by
    intro i h0
    have := hcF i
    rw [h0, map_zero] at this
    unfold Cong at this
    rw [sub_zero, hFu i] at this
    exact lt_irrefl _ this
  have hf₀1 : ∀ i, f₀ i ≠ -1 := by
    intro i h1
    have := hcF i
    rw [h1, map_neg, map_one] at this
    rw [cong_neg_one_iff, hF1u i] at this
    exact lt_irrefl _ this
  have hcs : ∀ e, Cong P.v (sP P c e) 1 := fun e => val_sP_sub_one_lt P c e
  -- The residue point solves the limit system.
  have hL : G.IsLimitSolution β a₀ f₀ := by
    refine ⟨hf₀0, hf₀1, ?_, ?_⟩
    · intro α
      have he := h.edge α
      -- F_i (1 + B) = A (1 + s B)
      have h1 : Cong P.v (F (G.tail α) * (1 + A (rev α)))
          (P.ofK (f₀ (G.tail α) * (1 + a₀ (rev α)))) := by
        rw [map_mul, map_add, map_one]
        exact (hcF _).mul (hFu _).le (by rw [← map_one P.ofK, ← map_add]; exact val_ofK_le_one _)
          ((Cong.refl 1).add (hcA _))
      have h2 : Cong P.v (A α * (1 + sP P c α.1 * A (rev α)))
          (P.ofK (a₀ α * (1 + a₀ (rev α)))) := by
        rw [map_mul, map_add, map_one]
        refine (hcA α).mul (hAu α).le (by rw [← map_one P.ofK, ← map_add]; exact val_ofK_le_one _)
          ((Cong.refl 1).add ?_)
        have := (hcs α.1).mul (val_eq_one_of_cong_one P.v (hcs α.1)).le (val_ofK_le_one _)
          (hcA (rev α))
        rwa [one_mul] at this
      rw [he] at h1
      have := cong_ofK_iff.1 (h1.symm.trans h2)
      linear_combination -this
    · intro i
      have hv := h.vertex i
      have hF : F i ≠ 0 := h.F_ne_zero i
      -- β F^d = F ∏ A
      have hv' : βP P β i * F i ^ G.degree i = F i * ∏ α ∈ G.inDarts i, A (rev α) := by
        rw [hv, zpow_sub₀ hF, zpow_one, zpow_natCast]
        field_simp
      have h1 : Cong P.v (βP P β i * F i ^ G.degree i) (P.ofK (β i * f₀ i ^ G.degree i)) := by
        rw [map_mul, map_pow]
        exact (Cong.refl _).mul (val_βP P β hβ0 i).le (by rw [← map_pow]; exact val_ofK_le_one _)
          ((hcF i).pow (hFu i).le (val_ofK_le_one _) _)
      have h2 : Cong P.v (F i * ∏ α ∈ G.inDarts i, A (rev α))
          (P.ofK (f₀ i * ∏ α ∈ G.inDarts i, a₀ (rev α))) := by
        rw [map_mul, map_prod]
        exact (hcF i).mul (hFu i).le (by rw [← map_prod]; exact val_ofK_le_one _)
          (Cong.prod _ _ _ (fun α _ => (hAu _).le) (fun α _ => val_ofK_le_one _)
            (fun α _ => hcA (rev α)))
      rw [hv'] at h1
      have := cong_ofK_iff.1 (h1.symm.trans h2)
      rw [zpow_sub₀ (hf₀0 i), zpow_one, zpow_natCast, eq_comm, div_mul_eq_mul_div,
        div_eq_iff (pow_ne_zero _ (hf₀0 i))]
      linear_combination -this
  have hFlim : ∀ i, VertexLimitEq (G.deg (activeSet a₀) i) (β i) (f₀ i) :=
    fun i => hL.vertexLimitEq i
  let q : G.LimitParams β := ⟨(activeSet a₀, f₀), hFlim⟩
  have hx₀ : G.limitPoint (activeSet a₀) f₀ = Sum.elim a₀ f₀ := by
    funext j
    rcases j with α | i
    · exact (congrFun hL.eq_limitCoords α).symm
    · rfl
  -- Point over the valuation ring.
  let xO : Var V E → P.v.integer := fun j =>
    ⟨Sum.elim A F j, (Valuation.mem_integer_iff _ _).2 (by
      rcases j with α | i
      · exact (hAu α).le
      · exact (hFu i).le)⟩
  obtain ⟨hy0, hysol⟩ := G.liftOf_spec c β hβ1 q
  let yO : Var V E → P.v.integer := fun j => ofPSO P (G.liftOf c β hβ1 q j)
  have hcong : ∀ j, Cong P.v (xO j : P.L) (P.ofK (Sum.elim a₀ f₀ j)) := by
    intro j
    rcases j with α | i
    · exact hcA α
    · exact hcF i
  have hcongy : ∀ j, Cong P.v (yO j : P.L) (P.ofK (Sum.elim a₀ f₀ j)) := by
    intro j
    have := cong_ofPS_ofK (P := P) (G.liftOf c β hβ1 q j)
    rw [hy0 j, hx₀] at this
    exact this
  have hJ : P.v (((Matrix.of fun i j => eval xO (pderiv j (G.weakSystemO P c β i))).det :
      P.v.integer) : P.L) = 1 := by
    have hcd := G.cong_det_jacO P c β hcong
    rw [← hx₀, ← jacRes_weakSystem] at hcd
    exact hcd.val_eq_one (P.val_ofK _ (G.det_jacRes_weakSystem_ne_zero hβ1 hFlim))
  have hxsol : ∀ w, eval xO (G.weakSystemO P c β w) = 0 := by
    intro w
    apply Subtype.ext
    rw [coe_eval_weakSystemO]
    exact G.eval_map_ofPS_weakSystem_eq_zero P c β h w
  have hysol' : ∀ w, eval yO (G.weakSystemO P c β w) = 0 := by
    intro w
    show eval ((ofPSO P) ∘ G.liftOf c β hβ1 q) (map (ofPSO P) (G.weakSystem c β w)) = 0
    rw [← map_eval' (ofPSO P) (G.liftOf c β hβ1 q), hysol w, map_zero]
  have hxy : xO = yO := by
    apply unique_of_cong P.v hxsol hysol' ?_ hJ
    intro j
    show P.v ((yO j : P.L) - (xO j : P.L)) < 1
    exact (hcongy j).trans (hcong j).symm
  refine ⟨q, ?_⟩
  apply Subtype.ext
  simp only [toPuiseuxSolution, liftToPuiseux]
  have hcoe : ∀ j, P.ofPS (G.liftOf c β hβ1 q j) = Sum.elim A F j := by
    intro j
    have := congrArg (fun x => (x j : P.L)) hxy
    exact this.symm
  exact Prod.ext (funext fun α => hcoe (Sum.inl α)) (funext fun i => hcoe (Sum.inr i))

end Surj

/-- **Complete Puiseux-type count.** For algebraically closed characteristic-zero K, `P:PuiseuxField K`, c_e≠0 and β_i≠0,−1, the auxiliary system with s_e=1+t c_e has exactly Q(G) admissible L-solutions. -/
theorem card_puiseuxSolutions [IsAlgClosed K] [CharZero K] (c : E → K) (hc : ∀ e, c e ≠ 0)
    (β : V → K) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    Nat.card (G.PuiseuxSolutions P c β) = G.Q := by
  have hbij : Function.Bijective (G.toPuiseuxSolution P c β hβ1 hc) :=
    ⟨G.toPuiseuxSolution_injective P c β hβ1 hc,
      fun p => G.exists_lift_of_puiseuxSolution P c β hc hβ0 hβ1 p⟩
  rw [← Nat.card_eq_of_bijective _ hbij, ← Nat.card_congr (G.limitSolutionsEquiv β hβ1),
    G.card_limitSolutions β hβ0 hβ1]

end Multigraph

end BPFixedPoints
