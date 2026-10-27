import BPFixedPoints.StrongField.Exhaustion
import BPFixedPoints.Real.Count

/-!
# BP spin gauge and strong-field counts in all field orthants (`real:spin-gauge`)

Swap spin labels at η:V→Bool, true meaning exponent −1. For signs η_i=±1,
a'_e=a_e^{η_iη_j}, b'_i=b_i^{η_i}, y'_{j→i}=y_{j→i}^{η_i}, F'_i=F_i^{η_i}.
The update identity g_{a^{st}}(X^s)=g_a(X)^t gives a bijection of admissible
BP solutions (`isAdmissibleSolution_gauge`, `gaugeEquiv`).
The gauge also corresponds Jacobian kernels via logarithmic derivative
κ'=±κ (`gauge_kappa`) and preserves simplicity (`isSimpleSolution_gauge`).
It extends `strong_field_exactly_Q_simple` to all external-field signs: each
|b_i| sufficiently large or small gives Q simple complex solutions
(`strong_field_exactly_Q_simple_of_orthant`). For real a_e>0,a_e≠1 and all
|log b_i| sufficiently large, the complex/real/positive counts are (Q,#H₁,1),
all complex roots simple (`strong_field_three_counts`), or (Q,2^ν,1) if connected.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Flip

variable {K : Type*} [Field K] (η : V → Bool)

/-- x^{±1}: take the reciprocal when s=true. -/
def flipPow (s : Bool) (x : K) : K := if s then x⁻¹ else x

@[simp] theorem flipPow_flipPow (s : Bool) (x : K) : flipPow s (flipPow s x) = x := by
  cases s <;> simp [flipPow]

theorem flipPow_ne_zero {s : Bool} {x : K} (hx : x ≠ 0) : flipPow s x ≠ 0 := by
  cases s <;> simp [flipPow, hx]

theorem flipPow_mul (s : Bool) (x y : K) : flipPow s (x * y) = flipPow s x * flipPow s y := by
  cases s
  · simp [flipPow]
  · simp only [flipPow, ite_true]; rw [mul_inv]

theorem flipPow_prod {ι : Type*} (s : Bool) (t : Finset ι) (f : ι → K) :
    flipPow s (∏ i ∈ t, f i) = ∏ i ∈ t, flipPow s (f i) := by
  cases s <;> simp [flipPow, Finset.prod_inv_distrib]

/-- a'_e = a_e^{η_iη_j}。 -/
def gaugeA (a : E → K) (e : E) : K := flipPow (xor (η (G.fst e)) (η (G.snd e))) (a e)

/-- b'_i = b_i^{η_i}。 -/
def gaugeB (b : V → K) (i : V) : K := flipPow (η i) (b i)

/-- y'_α = y_α^{η_{h(α)}}。 -/
def gaugeY (y : Dart E → K) (α : Dart E) : K := flipPow (η (G.head α)) (y α)

variable {G}

theorem xor_head_tail (α : Dart E) :
    xor (η (G.fst α.1)) (η (G.snd α.1)) = xor (η (G.tail α)) (η (G.head α)) := by
  rcases α with ⟨e, _ | _⟩
  · simp [tail, head, Bool.xor_comm]
  · simp [tail, head]

theorem cavity_gauge (b : V → K) (y : Dart E → K) (α : Dart E) :
    G.cavity (gaugeB η b) (G.gaugeY η y) α = flipPow (η (G.tail α)) (G.cavity b y α) := by
  unfold cavity gaugeB gaugeY
  rw [flipPow_mul, flipPow_prod]
  congr 1
  refine Finset.prod_congr rfl fun γ hγ => ?_
  have : G.head γ = G.tail α := by
    have := (Finset.mem_erase.1 hγ).2
    simpa [inDarts] using this
  rw [this]

theorem totalField_gauge (b : V → K) (y : Dart E → K) (i : V) :
    G.totalField (gaugeB η b) (G.gaugeY η y) i = flipPow (η i) (G.totalField b y i) := by
  unfold totalField gaugeB gaugeY
  rw [flipPow_mul, flipPow_prod]
  congr 1
  refine Finset.prod_congr rfl fun γ hγ => ?_
  have : G.head γ = i := by simpa [inDarts] using hγ
  rw [this]

/-- Update symmetry: y(X+a)=aX+1 implies y^t(X^s+a^{st})=a^{st}X^s+1. -/
theorem update_flip {a X y : K} (ha : a ≠ 0) (hX : X ≠ 0) (hy : y ≠ 0) (hXa : X + a ≠ 0)
    (h : y * (X + a) = a * X + 1) (s t : Bool) :
    flipPow t y * (flipPow s X + flipPow (xor s t) a) = flipPow (xor s t) a * flipPow s X + 1 := by
  have h1 : a * X + 1 ≠ 0 := by rw [← h]; exact mul_ne_zero hy hXa
  cases s <;> cases t <;> simp only [flipPow, Bool.xor_false, Bool.xor_true, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true]
  · exact h
  · field_simp; linear_combination (-1 : K) * h
  · field_simp; linear_combination h
  · field_simp; linear_combination (-1 : K) * h

theorem flipPow_add_ne_zero {a X y : K} (ha : a ≠ 0) (hX : X ≠ 0) (hy : y ≠ 0)
    (hXa : X + a ≠ 0) (h : y * (X + a) = a * X + 1) (s t : Bool) :
    flipPow s X + flipPow (xor s t) a ≠ 0 := by
  have h1 : a * X + 1 ≠ 0 := by rw [← h]; exact mul_ne_zero hy hXa
  cases s <;> cases t <;> simp only [flipPow, Bool.xor_false, Bool.xor_true, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true]
  · exact hXa
  · intro h0; apply h1; field_simp at h0; linear_combination h0
  · intro h0; apply hXa; field_simp at h0; linear_combination h0
  · intro h0; apply h1; field_simp at h0; linear_combination h0

/-- **Spin gauge preserves admissible BP solutions.** -/
theorem isAdmissibleSolution_gauge {a : E → K} {b : V → K} {y : Dart E → K} (ha : ∀ e, a e ≠ 0)
    (hb : ∀ i, b i ≠ 0) (hy : G.IsAdmissibleSolution a b y) :
    G.IsAdmissibleSolution (G.gaugeA η a) (gaugeB η b) (G.gaugeY η y) := by
  obtain ⟨hfix, hy0, hden, hF1⟩ := hy
  have hX0 : ∀ α, G.cavity b y α ≠ 0 := fun α => by
    unfold cavity
    exact mul_ne_zero (hb _) (Finset.prod_ne_zero_iff.2 fun γ _ => hy0 γ)
  have heq : ∀ α, y α * (G.cavity b y α + a α.1) = a α.1 * G.cavity b y α + 1 := fun α => by
    have := hfix α; unfold bpPoly at this; linear_combination this
  have hxor : ∀ α, G.gaugeA η a α.1 = flipPow (xor (η (G.tail α)) (η (G.head α))) (a α.1) :=
    fun α => by unfold gaugeA; rw [xor_head_tail]
  refine ⟨fun α => ?_, fun α => flipPow_ne_zero (hy0 α), fun α => ?_, fun i => ?_⟩
  · unfold bpPoly
    rw [cavity_gauge, hxor]
    have := update_flip (ha α.1) (hX0 α) (hy0 α) (hden α) (heq α) (η (G.tail α)) (η (G.head α))
    unfold gaugeY
    linear_combination this
  · rw [cavity_gauge, hxor]
    exact flipPow_add_ne_zero (ha α.1) (hX0 α) (hy0 α) (hden α) (heq α) _ _
  · rw [totalField_gauge]
    have hF0 := G.totalField_ne_zero b y hb hy0 i
    cases η i
    · exact hF1 i
    · simp only [flipPow, ite_true]
      intro h0
      apply hF1 i
      field_simp at h0
      linear_combination h0

@[simp] theorem gaugeA_gaugeA (a : E → K) : G.gaugeA η (G.gaugeA η a) = a := by
  funext e; simp [gaugeA]

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
@[simp] theorem gaugeB_gaugeB (b : V → K) : gaugeB η (gaugeB η b) = b := by
  funext i; simp [gaugeB]

@[simp] theorem gaugeY_gaugeY (y : Dart E → K) : G.gaugeY η (G.gaugeY η y) = y := by
  funext α; simp [gaugeY]

theorem gaugeA_ne_zero {a : E → K} (ha : ∀ e, a e ≠ 0) (e : E) : G.gaugeA η a e ≠ 0 :=
  flipPow_ne_zero (ha e)

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
theorem gaugeB_ne_zero {b : V → K} (hb : ∀ i, b i ≠ 0) (i : V) : gaugeB η b i ≠ 0 :=
  flipPow_ne_zero (hb i)

/-- **Spin-gauge bijection.** -/
def gaugeEquiv {a : E → K} {b : V → K} (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0) :
    {y : Dart E → K // G.IsAdmissibleSolution a b y} ≃
      {y : Dart E → K // G.IsAdmissibleSolution (G.gaugeA η a) (gaugeB η b) y} where
  toFun y := ⟨G.gaugeY η y.1, isAdmissibleSolution_gauge η ha hb y.2⟩
  invFun y := ⟨G.gaugeY η y.1, by
    have := isAdmissibleSolution_gauge η (G.gaugeA_ne_zero η ha) (gaugeB_ne_zero η hb) y.2
    simpa using this⟩
  left_inv y := Subtype.ext (gaugeY_gaugeY η y.1)
  right_inv y := Subtype.ext (gaugeY_gaugeY η y.1)

/-! ### Preservation of simplicity -/

/-- Jacobian kernel row: for u=w/y, P_αu_α+R_αΣ_{N(α)}u_γ, with P=y(X+a), R=(y−a)X. -/
theorem jacobian_mulVec_row {a : E → K} {b : V → K} {y : Dart E → K} (hy0 : ∀ γ, y γ ≠ 0)
    (w : Dart E → K) (α : Dart E) :
    (G.jacobian a b y).mulVec w α =
      y α * (G.cavity b y α + a α.1) * (w α / y α) +
        (y α - a α.1) * G.cavity b y α *
          ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ := by
  rw [mulVec_apply']
  have h1 := G.bpMvPoly_dirDeriv b y a α w
  have h2 := G.cavity_dirDeriv b y hy0 α w
  simp only [jacobian]
  rw [h1, h2]
  field_simp [hy0 α]

/-- Form κ'=tsκ: R'P=tsRP', with P=aX+1, R=(y−a)X, y(X+a)=aX+1. -/
theorem gauge_kappa {a X y : K} (ha : a ≠ 0) (hX : X ≠ 0) (hy : y ≠ 0) (hXa : X + a ≠ 0)
    (h : y * (X + a) = a * X + 1) (s t : Bool) :
    (flipPow t y - flipPow (xor s t) a) * flipPow s X * (y * (X + a)) =
      (if xor s t then -1 else 1) * ((y - a) * X *
        (flipPow t y * (flipPow s X + flipPow (xor s t) a))) := by
  have h1 : a * X + 1 ≠ 0 := by rw [← h]; exact mul_ne_zero hy hXa
  have hy' : y = (a * X + 1) / (X + a) := by rw [eq_div_iff hXa]; exact h
  subst hy'
  cases s <;> cases t <;> simp only [flipPow, Bool.xor_false, Bool.xor_true, Bool.not_true,
    Bool.not_false, ite_true, ite_false, Bool.false_eq_true] <;> field_simp <;> ring

/-- **Spin gauge preserves simplicity.** -/
theorem isSimpleSolution_gauge {a : E → K} {b : V → K} {y : Dart E → K} (ha : ∀ e, a e ≠ 0)
    (hb : ∀ i, b i ≠ 0) (hy : G.IsAdmissibleSolution a b y)
    (hs : G.IsSimpleSolution a b y) :
    G.IsSimpleSolution (G.gaugeA η a) (gaugeB η b) (G.gaugeY η y) := by
  classical
  have hy' := isAdmissibleSolution_gauge η ha hb hy
  obtain ⟨hfix, hy0, hden, -⟩ := hy
  have hy0' : ∀ γ, G.gaugeY η y γ ≠ 0 := hy'.2.1
  have hX0 : ∀ α, G.cavity b y α ≠ 0 := fun α => by
    unfold cavity
    exact mul_ne_zero (hb _) (Finset.prod_ne_zero_iff.2 fun γ _ => hy0 γ)
  have heq : ∀ α, y α * (G.cavity b y α + a α.1) = a α.1 * G.cavity b y α + 1 := fun α => by
    have := hfix α; unfold bpPoly at this; linear_combination this
  have hxor : ∀ α, G.gaugeA η a α.1 = flipPow (xor (η (G.tail α)) (η (G.head α))) (a α.1) :=
    fun α => by unfold gaugeA; rw [xor_head_tail]
  unfold IsSimpleSolution
  intro h0
  obtain ⟨w', hw'0, hw'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  -- u' = w'/y'、u = t·u'
  set sg : Bool → K := fun s => if s then -1 else 1
  have hsg : ∀ s, sg s * sg s = 1 := fun s => by cases s <;> simp [sg]
  set u : Dart E → K := fun γ => sg (η (G.head γ)) * (w' γ / G.gaugeY η y γ)
  set w : Dart E → K := fun γ => u γ * y γ
  apply hs
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, ?_, ?_⟩
  · intro hw
    apply hw'0
    funext γ
    have := congrFun hw γ
    simp only [w, u, Pi.zero_apply, mul_eq_zero, hy0 γ, or_false] at this
    rcases this with h | h
    · simp only [sg] at h
      split_ifs at h <;> norm_num at h
    · rcases div_eq_zero_iff.1 h with h' | h'
      · exact h'
      · exact absurd h' (hy0' γ)
  · funext α
    rw [Pi.zero_apply, G.jacobian_mulVec_row hy0 w α]
    have hrow := congrFun hw' α
    rw [Pi.zero_apply, G.jacobian_mulVec_row hy0' w' α, cavity_gauge, hxor] at hrow
    set s := η (G.tail α)
    set t := η (G.head α)
    have hsum : ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w' γ / G.gaugeY η y γ =
        sg s * ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      have hh : G.head γ = G.tail α := by
        have := (Finset.mem_erase.1 hγ).2; simpa [inDarts] using this
      simp only [w, u, hh, mul_div_assoc, div_self (hy0 γ), mul_one]
      rw [← mul_assoc, hsg, one_mul]
    have hu : w α / y α = sg t * (w' α / G.gaugeY η y α) := by
      simp only [w, u]; rw [mul_div_assoc, div_self (hy0 α), mul_one]
    rw [hsum] at hrow
    rw [hu]
    have hk := gauge_kappa (ha α.1) (hX0 α) (hy0 α) (hden α) (heq α) s t
    -- hrow: P'u'_α+R' sg(s)Σu=0; goal: P sg(t)u'_α+RΣu=0.
    set P := y α * (G.cavity b y α + a α.1)
    set R := (y α - a α.1) * G.cavity b y α
    set P' := G.gaugeY η y α * (flipPow s (G.cavity b y α) + flipPow (xor s t) (a α.1))
    set R' := (G.gaugeY η y α - flipPow (xor s t) (a α.1)) * flipPow s (G.cavity b y α)
    set U := w' α / G.gaugeY η y α
    set Sg := ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ
    have hP' : P' ≠ 0 := mul_ne_zero (hy0' α) (by
      have := hy'.2.2.1 α; rwa [cavity_gauge, hxor] at this)
    have hP : P ≠ 0 := mul_ne_zero (hy0 α) (hden α)
    have hgy : G.gaugeY η y α = flipPow t (y α) := rfl
    have hxs : (if xor s t then (-1 : K) else 1) = sg s * sg t := by
      cases s <;> cases t <;> simp [sg]
    rw [hxs] at hk
    -- hk : R'·P = (sg s sg t)·R·P'
    have hk' : R' * P = sg s * sg t * (R * P') := by
      simp only [R', P, R, P', hgy]; exact hk
    have hss := hsg s
    have hst := hsg t
    have key : P' * (P * (sg t * U) + R * Sg) = 0 := by
      linear_combination (sg t * P) * hrow - (sg t * sg s * Sg) * hk' -
        (R * P' * Sg * (sg t * sg t)) * hss - (R * P' * Sg) * hst
    exact (mul_eq_zero.1 key).resolve_left hP'

end Flip

section Orthant

omit [DecidableEq V] [Fintype V] in
theorem gaugeA_sq_ne_one (η : V → Bool) {a : E → ℂ} (_ha : ∀ e, a e ≠ 0) (ha1 : ∀ e, a e ^ 2 ≠ 1)
    (e : E) : G.gaugeA η a e ^ 2 ≠ 1 := by
  unfold gaugeA flipPow
  split_ifs
  · rw [inv_pow]
    intro h
    exact ha1 e (inv_eq_one.1 h)
  · exact ha1 e

/-- **Strong-field complex roots in every orthant.** If each vertex has ‖b_i⁻¹‖<ε or ‖b_i‖<ε, there are exactly Q simple admissible complex BP solutions. -/
theorem strong_field_exactly_Q_simple_of_orthant (hG : G.Loopless) {a : E → ℂ}
    (ha : ∀ e, a e ≠ 0) (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ ε > 0, ∀ b : V → ℂ, (∀ i, b i ≠ 0) → (∀ i, ‖(b i)⁻¹‖ < ε ∨ ‖b i‖ < ε) →
      Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = G.Q ∧
      ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  classical
  have h := fun η : V → Bool =>
    strong_field_exactly_Q_simple hG (G.gaugeA_ne_zero η ha) (G.gaugeA_sq_ne_one η ha ha1)
  choose ε hε hcount using h
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun b hb hbε => ?_⟩
  set η : V → Bool := fun i => decide (‖b i‖ < min δ 1)
  have hp : ∀ i, ‖(gaugeB η b i)⁻¹‖ < ε η := by
    intro i
    refine lt_of_lt_of_le ?_ (hδle η)
    simp only [gaugeB, flipPow, η]
    by_cases h1 : ‖b i‖ < min δ 1
    · simp only [h1, decide_true, ite_true, inv_inv]
      exact lt_of_lt_of_le h1 (min_le_left _ _)
    · simp only [h1, decide_false, Bool.false_eq_true, ite_false]
      rcases hbε i with h2 | h2
      · exact lt_of_lt_of_le h2 (min_le_left _ _)
      · exact absurd h2 h1
  obtain ⟨hc, hsimp⟩ := hcount η (fun i => (gaugeB η b i)⁻¹)
    (fun i => inv_ne_zero (gaugeB_ne_zero η hb i)) hp
  simp only [inv_inv] at hc hsimp
  refine ⟨?_, fun y hy => ?_⟩
  · rw [Nat.card_congr (G.gaugeEquiv η ha hb)]
    exact hc
  · have h1 := hsimp _ (isAdmissibleSolution_gauge η ha hb hy)
    have h2 := G.isSimpleSolution_gauge η (G.gaugeA_ne_zero η ha) (gaugeB_ne_zero η hb)
      (isAdmissibleSolution_gauge η ha hb hy) h1
    simpa using h2

/-- Strong-field complex count in all external-field orthants. -/
theorem card_strong_field_eq_Q_of_orthant (hG : G.Loopless) {a : E → ℂ} (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ ε > 0, ∀ b : V → ℂ, (∀ i, b i ≠ 0) → (∀ i, ‖(b i)⁻¹‖ < ε ∨ ‖b i‖ < ε) →
      Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = G.Q := by
  obtain ⟨ε, hε, h⟩ := G.strong_field_exactly_Q_simple_of_orthant hG ha ha1
  exact ⟨ε, hε, fun b hb hbε => (h b hb hbε).1⟩

/-- **Three strong-field counts (`real:strong-field-count`, `thm:real` (ii)).** Fix real a_e>0,a_e≠1. If all |log b_i| are sufficiently large, there are Q admissible complex roots, #H₁ real roots and one root with all messages positive. -/
theorem strong_field_three_counts (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      Nat.card {y : Dart E → ℂ //
          G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y} = G.Q ∧
      (∀ y, G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y →
        G.IsSimpleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y) ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} =
          (Finset.univ.filter G.IsEvenSet).card ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  have haC : ∀ e, ((a e : ℂ)) ≠ 0 := fun e => by exact_mod_cast (ha e).ne'
  have haC1 : ∀ e, ((a e : ℂ)) ^ 2 ≠ 1 := by
    intro e h
    have h' : a e ^ 2 = 1 := by exact_mod_cast h
    have : (a e - 1) * (a e + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 this with h1 | h1
    · exact ha1 e (by linarith)
    · linarith [ha e]
  obtain ⟨ε, hε, hC⟩ := G.strong_field_exactly_Q_simple_of_orthant hG haC haC1
  obtain ⟨HR, hR⟩ := card_real_strong_field ha ha1 hG
  refine ⟨max HR (|Real.log ε| + 1), fun b hb hbH => ?_⟩
  obtain ⟨h1, h2⟩ := hR b hb fun i => le_trans (le_max_left _ _) (hbH i)
  suffices hsuff : ∀ i, ‖((b i : ℂ))⁻¹‖ < ε ∨ ‖(b i : ℂ)‖ < ε by
    obtain ⟨hc1, hc2⟩ := hC _ (fun i => by exact_mod_cast (hb i).ne') hsuff
    exact ⟨hc1, hc2, h1, h2⟩
  intro i
  have hH := le_trans (le_max_right _ _) (hbH i)
  have hlogε : -(|Real.log ε| + 1) < Real.log ε := by
    have := neg_abs_le (Real.log ε); linarith
  rcases le_abs'.1 hH with hneg | hpos
  · -- log b ≤ −H：b < ε
    right
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb i)]
    have : Real.log (b i) < Real.log ε := by linarith
    exact (Real.log_lt_log_iff (hb i) hε).1 this
  · -- log b ≥ H：1/b < ε
    left
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hb i))]
    have : Real.log (b i)⁻¹ < Real.log ε := by
      rw [Real.log_inv]; linarith
    exact (Real.log_lt_log_iff (inv_pos.2 (hb i)) hε).1 this

/-- For connected G, strong-field complex/real/positive counts are (Q,2^ν,1). -/
theorem strong_field_three_counts_of_connected (hG : G.Loopless) (hc : G.Connected) {a : E → ℝ}
    (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      Nat.card {y : Dart E → ℂ //
          G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y} = G.Q ∧
      (∀ y, G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y →
        G.IsSimpleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y) ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 2 ^ G.cycleRank ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  rw [← G.card_evenSets_of_connected hc]
  exact G.strong_field_three_counts hG ha ha1

end Orthant

end Multigraph

end BPFixedPoints
