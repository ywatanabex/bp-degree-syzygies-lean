import BPFixedPoints.Degree.GenericDegree

/-!
# `ex:triangle-admissible`: why 1+F_i≠0 matters

Take a_e=b_i=2 on C₃ (`Examples.triangle`), with edges 0→1, 1→2, 2→0.
Each orientation updates by T(x)=(4x+1)/(2x+2) (`triangle_cavity`), and
T³(x)−x=−5(2x²−2x−1)/(10x+4) (`triT_iter_three_sub`). Rational fixed points
with nonzero update denominators carry constant messages per orientation,
chosen from x±=(1±√3)/2 (`triangle_isRationalFixedPoint_iff`). There are four
real solutions (`card_triangle_rational`), all with nonzero messages and update
denominators; messages also avoid −1, allowing normalization to sum one
(`triSol_ne_neg_one`). Total fields are F_i=2x_cw x_ccw (`triangle_totalField_triSol`).
Equal roots give 2±√3; mixed roots give −1 (`triangle_totalField_mixed`).
Admissibility excludes the two mixed solutions, leaving two
(`triangle_isAdmissibleSolution_iff`, `card_triangle_admissible`), equal to N(C₃)
(`triangle_N`). Algebraic identities hold over any characteristic-zero field;
real counts use the explicit roots.
-/

namespace BPFixedPoints.Examples

set_option linter.unusedSectionVars false

open Multigraph BP

/-! ### Darts of the triangle -/

/-- Preceding dart in the same orientation: the unique incoming dart other than the reverse dart. -/
def triPrev (α : Dart (Fin 3)) : Dart (Fin 3) :=
  if α.2 then (α.1 + 2, true) else (α.1 + 1, false)

theorem triangle_inDarts_erase (α : Dart (Fin 3)) :
    (triangle.inDarts (triangle.tail α)).erase (rev α) = {triPrev α} := by
  revert α; decide

theorem triangle_inDarts (i : Fin 3) : triangle.inDarts i = {(i + 2, true), (i, false)} := by
  revert i; decide

section Field

variable {K : Type*} [Field K]

theorem triangle_cavity (b : Fin 3 → K) (y : Dart (Fin 3) → K) (α : Dart (Fin 3)) :
    triangle.cavity b y α = b (triangle.tail α) * y (triPrev α) := by
  rw [cavity, triangle_inDarts_erase, Finset.prod_singleton]

/-- One-direction update T(x)=(4x+1)/(2x+2), with a=b=2. -/
def triT (x : K) : K := (4 * x + 1) / (2 * x + 2)

/-- **T³(x)−x=−5(2x²−2x−1)/(10x+4)** when all intermediate denominators 2x+2, 2T(x)+2, 2T²(x)+2 are nonzero. -/
theorem triT_iter_three_sub [CharZero K] {x : K} (h1 : 2 * x + 2 ≠ 0) (h2 : 2 * x + 1 ≠ 0)
    (h3 : 10 * x + 4 ≠ 0) :
    triT (triT (triT x)) - x = -5 * (2 * x ^ 2 - 2 * x - 1) / (10 * x + 4) := by
  have h6 : (6 : K) ≠ 0 := by norm_num
  have hy1 : triT x = (4 * x + 1) / (2 * x + 2) := rfl
  have hn1 : 4 * triT x + 1 = 6 * (3 * x + 1) / (2 * x + 2) := by
    rw [hy1, eq_div_iff h1, add_mul, mul_assoc, div_mul_cancel₀ _ h1]; ring
  have hd1 : 2 * triT x + 2 = 6 * (2 * x + 1) / (2 * x + 2) := by
    rw [hy1, eq_div_iff h1, add_mul, mul_assoc, div_mul_cancel₀ _ h1]; ring
  have hy2 : triT (triT x) = (3 * x + 1) / (2 * x + 1) := by
    rw [triT, hn1, hd1, div_div_div_cancel_right₀ h1, mul_div_mul_left _ _ h6]
  have hn2 : 4 * triT (triT x) + 1 = (14 * x + 5) / (2 * x + 1) := by
    rw [hy2, eq_div_iff h2, add_mul, mul_assoc, div_mul_cancel₀ _ h2]; ring
  have hd2 : 2 * triT (triT x) + 2 = (10 * x + 4) / (2 * x + 1) := by
    rw [hy2, eq_div_iff h2, add_mul, mul_assoc, div_mul_cancel₀ _ h2]; ring
  have hy3 : triT (triT (triT x)) = (14 * x + 5) / (10 * x + 4) := by
    rw [triT, hn2, hd2, div_div_div_cancel_right₀ h2]
  rw [hy3, eq_div_iff h3, sub_mul, div_mul_cancel₀ _ h3]
  ring

/-- Messages constant in each orientation: s clockwise and s' counterclockwise. -/
def triSol (s s' : K) : Dart (Fin 3) → K := fun α => if α.2 then s else s'

@[simp] theorem triSol_true (s s' : K) (e : Fin 3) : triSol s s' (e, true) = s := rfl
@[simp] theorem triSol_false (s s' : K) (e : Fin 3) : triSol s s' (e, false) = s' := rfl

theorem triSol_triPrev (s s' : K) (α : Dart (Fin 3)) : triSol s s' (triPrev α) = triSol s s' α := by
  rcases α with ⟨e, _ | _⟩ <;> rfl

/-- Total field F_i=2ss'. -/
theorem triangle_totalField_triSol (s s' : K) (i : Fin 3) :
    triangle.totalField (fun _ => (2 : K)) (triSol s s') i = 2 * (s * s') := by
  rw [totalField, triangle_inDarts, Finset.prod_pair (by simp)]
  rfl

variable [CharZero K]

/-- Roots of 2x²−2x−1 avoid 0 and −1. -/
theorem triRoot_ne_zero {s : K} (hs : 2 * s ^ 2 - 2 * s - 1 = 0) : s ≠ 0 := by
  rintro rfl; norm_num at hs

theorem triRoot_add_one_ne_zero {s : K} (hs : 2 * s ^ 2 - 2 * s - 1 = 0) : 2 * s + 2 ≠ 0 := by
  intro h
  have : s = -1 := by linear_combination h / 2
  subst this; norm_num at hs

theorem triSol_ne_neg_one {s s' : K} (hs : 2 * s ^ 2 - 2 * s - 1 = 0)
    (hs' : 2 * s' ^ 2 - 2 * s' - 1 = 0) (α : Dart (Fin 3)) : triSol s s' α ≠ -1 := by
  have h1 := triRoot_add_one_ne_zero hs
  have h2 := triRoot_add_one_ne_zero hs'
  rcases α with ⟨e, _ | _⟩
  · intro h; apply h2; simp at h; rw [h]; ring
  · intro h; apply h1; simp at h; rw [h]; ring

/-- Three updates in one orientation force constant messages at a root of 2x²−2x−1. -/
theorem tri_cycle {x₀ x₁ x₂ : K} (h1 : x₁ * (2 * x₀ + 2) = 4 * x₀ + 1)
    (h2 : x₂ * (2 * x₁ + 2) = 4 * x₁ + 1) (h3 : x₀ * (2 * x₂ + 2) = 4 * x₂ + 1) :
    2 * x₀ ^ 2 - 2 * x₀ - 1 = 0 ∧ x₁ = x₀ ∧ x₂ = x₀ := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (2 * x₀ * x₂ / 15 - 4 * x₀ / 15 - 4 * x₂ / 15 + 8 / 15) * h1 +
      (-2 * x₀ ^ 2 / 15 + 2 * x₀ / 15 + 4 / 15) * h2 + (2 * x₀ / 5 + 1 / 5) * h3
  · linear_combination (1 / 5 : K) * h1 + (x₀ / 15 - 2 / 15) * h2 + (-x₁ / 15 - 1 / 15) * h3
  · linear_combination (2 / 15 - x₂ / 15) * h1 + (x₀ / 15 + 1 / 15) * h2 + (-1 / 5 : K) * h3

/-- Clear the denominator in y=(2·(2y')+1)/(2y'+2). -/
theorem tri_update {y y' : K} (hd : 2 * y' + 2 ≠ 0)
    (h : y = (2 * (2 * y') + 1) / (2 * y' + 2)) : y * (2 * y' + 2) = 4 * y' + 1 := by
  rw [h, div_mul_cancel₀ _ hd]; ring

/-- **Rational triangle BP solutions.** For a=b=2, rational fixed points with nonzero update denominators carry a constant root of 2x²−2x−1=0 in each orientation. -/
theorem triangle_isRationalFixedPoint_iff (y : Dart (Fin 3) → K) :
    triangle.IsRationalFixedPoint (fun _ => (2 : K)) (fun _ => (2 : K)) y ↔
      ∃ s s' : K, 2 * s ^ 2 - 2 * s - 1 = 0 ∧ 2 * s' ^ 2 - 2 * s' - 1 = 0 ∧
        y = triSol s s' := by
  simp only [IsRationalFixedPoint, triangle_cavity]
  constructor
  · intro h
    have e : ∀ α, y α * (2 * y (triPrev α) + 2) = 4 * y (triPrev α) + 1 := fun α =>
      tri_update (h α).1 (h α).2
    have e1 : y (1, true) * (2 * y (0, true) + 2) = 4 * y (0, true) + 1 := e (1, true)
    have e2 : y (2, true) * (2 * y (1, true) + 2) = 4 * y (1, true) + 1 := e (2, true)
    have e0 : y (0, true) * (2 * y (2, true) + 2) = 4 * y (2, true) + 1 := e (0, true)
    have f2 : y (2, false) * (2 * y (0, false) + 2) = 4 * y (0, false) + 1 := e (2, false)
    have f1 : y (1, false) * (2 * y (2, false) + 2) = 4 * y (2, false) + 1 := e (1, false)
    have f0 : y (0, false) * (2 * y (1, false) + 2) = 4 * y (1, false) + 1 := e (0, false)
    obtain ⟨hr, h1, h2⟩ := tri_cycle e1 e2 e0
    obtain ⟨hr', h1', h2'⟩ := tri_cycle f2 f1 f0
    refine ⟨y (0, true), y (0, false), hr, hr', ?_⟩
    funext ⟨k, d⟩
    fin_cases k <;> cases d <;> simp [triSol, h1, h2, h1', h2']
  · rintro ⟨s, s', hs, hs', rfl⟩ α
    have hd : ∀ t : K, 2 * t ^ 2 - 2 * t - 1 = 0 →
        2 * t + 2 ≠ 0 ∧ t = (2 * (2 * t) + 1) / (2 * t + 2) := fun t ht =>
      ⟨triRoot_add_one_ne_zero ht, by
        rw [eq_div_iff (triRoot_add_one_ne_zero ht)]; linear_combination ht⟩
    rw [triSol_triPrev]
    rcases α with ⟨e, _ | _⟩
    · exact hd s' hs'
    · exact hd s hs

/-- Mixed solutions, with different roots in the two orientations, have F_i=−1. -/
theorem triangle_totalField_mixed {s s' : K} (hs : 2 * s ^ 2 - 2 * s - 1 = 0)
    (hs' : 2 * s' ^ 2 - 2 * s' - 1 = 0) (hne : s ≠ s') (i : Fin 3) :
    triangle.totalField (fun _ => (2 : K)) (triSol s s') i = -1 := by
  rw [triangle_totalField_triSol]
  have : (s - s') * (s + s' - 1) = 0 := by linear_combination (hs - hs') / 2
  have h2 : s + s' - 1 = 0 := (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have : s' = 1 - s := by linear_combination h2
  subst this
  linear_combination -hs

/-- Equal roots give F_i=2s²=2s+1, namely 2±√3 over ℝ. -/
theorem triangle_totalField_same {s : K} (hs : 2 * s ^ 2 - 2 * s - 1 = 0) (i : Fin 3) :
    triangle.totalField (fun _ => (2 : K)) (triSol s s) i = 2 * s + 1 := by
  rw [triangle_totalField_triSol]
  linear_combination hs

/-- **Admissible triangle solutions.** At a=b=2, exactly the two choices with the same root in both orientations are admissible. -/
theorem triangle_isAdmissibleSolution_iff (y : Dart (Fin 3) → K) :
    triangle.IsAdmissibleSolution (fun _ => (2 : K)) (fun _ => (2 : K)) y ↔
      ∃ s : K, 2 * s ^ 2 - 2 * s - 1 = 0 ∧ y = triSol s s := by
  constructor
  · rintro ⟨hfix, hy0, hden, hF⟩
    have hrat := (triangle.isFixedPoint_iff_isRationalFixedPoint _ _ _ hden).1 hfix
    obtain ⟨s, s', hs, hs', rfl⟩ := (triangle_isRationalFixedPoint_iff _).1 hrat
    by_cases hss : s = s'
    · exact ⟨s, hs, by rw [hss]⟩
    · exfalso
      apply hF 0
      rw [triangle_totalField_mixed hs hs' hss]; ring
  · rintro ⟨s, hs, rfl⟩
    have hrat : triangle.IsRationalFixedPoint (fun _ => (2 : K)) (fun _ => (2 : K))
        (triSol s s) := (triangle_isRationalFixedPoint_iff _).2 ⟨s, s, hs, hs, rfl⟩
    have hden : ∀ α, triangle.cavity (fun _ => (2 : K)) (triSol s s) α + 2 ≠ 0 :=
      fun α => (hrat α).1
    refine ⟨(triangle.isFixedPoint_iff_isRationalFixedPoint _ _ _ hden).2 hrat, ?_, hden, ?_⟩
    · intro α
      rcases α with ⟨e, _ | _⟩ <;> exact triRoot_ne_zero hs
    · intro i
      rw [triangle_totalField_same hs]
      intro h
      apply triRoot_add_one_ne_zero hs
      linear_combination h

end Field

/-! ### Counts over ℝ -/

/-- Real roots of 2x²−2x−1 are (1±√3)/2. -/
theorem triRoot_iff (s : ℝ) :
    2 * s ^ 2 - 2 * s - 1 = 0 ↔ s = (1 + √3) / 2 ∨ s = (1 - √3) / 2 := by
  have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have : (s - (1 + √3) / 2) * (s - (1 - √3) / 2) = 0 := by linear_combination h / 2 - h3 / 4
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rintro (rfl | rfl) <;> linear_combination h3 / 2

/-- Choose a root: true ↦ (1+√3)/2, false ↦ (1−√3)/2. -/
noncomputable def triRoot (b : Bool) : ℝ := if b then (1 + √3) / 2 else (1 - √3) / 2

theorem triRoot_spec (b : Bool) : 2 * triRoot b ^ 2 - 2 * triRoot b - 1 = 0 := by
  rw [triRoot_iff]; cases b <;> simp [triRoot]

theorem triRoot_injective : Function.Injective triRoot := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  intro b₁ b₂ h
  cases b₁ <;> cases b₂ <;> simp [triRoot] at h ⊢ <;> linarith

theorem exists_triRoot {s : ℝ} (hs : 2 * s ^ 2 - 2 * s - 1 = 0) : ∃ b, triRoot b = s := by
  rcases (triRoot_iff s).1 hs with h | h
  · exact ⟨true, by simp [triRoot, h]⟩
  · exact ⟨false, by simp [triRoot, h]⟩

theorem triSol_injective {s₁ s₁' s₂ s₂' : ℝ} (h : triSol s₁ s₁' = triSol s₂ s₂') :
    s₁ = s₂ ∧ s₁' = s₂' :=
  ⟨congrFun h (0, true), congrFun h (0, false)⟩

/-- **There are four real rational BP solutions.** -/
theorem card_triangle_rational :
    Nat.card {y : Dart (Fin 3) → ℝ //
      triangle.IsRationalFixedPoint (fun _ => (2 : ℝ)) (fun _ => (2 : ℝ)) y} = 4 := by
  have e : Bool × Bool ≃ {y : Dart (Fin 3) → ℝ //
      triangle.IsRationalFixedPoint (fun _ => (2 : ℝ)) (fun _ => (2 : ℝ)) y} :=
    Equiv.ofBijective
      (fun p => ⟨triSol (triRoot p.1) (triRoot p.2), (triangle_isRationalFixedPoint_iff _).2
        ⟨_, _, triRoot_spec p.1, triRoot_spec p.2, rfl⟩⟩)
      ⟨fun p q h => by
        have := triSol_injective (congrArg Subtype.val h)
        exact Prod.ext (triRoot_injective this.1) (triRoot_injective this.2),
       fun ⟨y, hy⟩ => by
        obtain ⟨s, s', hs, hs', rfl⟩ := (triangle_isRationalFixedPoint_iff y).1 hy
        obtain ⟨b, rfl⟩ := exists_triRoot hs
        obtain ⟨b', rfl⟩ := exists_triRoot hs'
        exact ⟨(b, b'), rfl⟩⟩
  rw [← Nat.card_congr e]
  simp

/-- **There are two admissible solutions.** The two mixed solutions are excluded because F_i=−1. -/
theorem card_triangle_admissible :
    Nat.card {y : Dart (Fin 3) → ℝ //
      triangle.IsAdmissibleSolution (fun _ => (2 : ℝ)) (fun _ => (2 : ℝ)) y} = 2 := by
  have e : Bool ≃ {y : Dart (Fin 3) → ℝ //
      triangle.IsAdmissibleSolution (fun _ => (2 : ℝ)) (fun _ => (2 : ℝ)) y} :=
    Equiv.ofBijective
      (fun b => ⟨triSol (triRoot b) (triRoot b), (triangle_isAdmissibleSolution_iff _).2
        ⟨_, triRoot_spec b, rfl⟩⟩)
      ⟨fun p q h => triRoot_injective (triSol_injective (congrArg Subtype.val h)).1,
       fun ⟨y, hy⟩ => by
        obtain ⟨s, hs, rfl⟩ := (triangle_isAdmissibleSolution_iff y).1 hy
        obtain ⟨b, rfl⟩ := exists_triRoot hs
        exact ⟨b, rfl⟩⟩
  rw [← Nat.card_congr e]
  simp

/-- Total fields of admissible solutions are 2±√3. -/
theorem triangle_admissible_totalField (b : Bool) (i : Fin 3) :
    triangle.totalField (fun _ => (2 : ℝ)) (triSol (triRoot b) (triRoot b)) i =
      if b then 2 + √3 else 2 - √3 := by
  rw [triangle_totalField_same (triRoot_spec b)]
  cases b <;> simp [triRoot] <;> ring

end BPFixedPoints.Examples
