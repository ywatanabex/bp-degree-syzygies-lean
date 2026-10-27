import Mathlib

/-!
# Two real BP edge branches (`real:edge-branches`)

Fix a>0 and endpoint total fields F_h,F_t>0. For incoming messages p=y_{t→h}
and q=y_{h→t}, use cavities F_t/q,F_h/p and clear denominators:
p(F_t+aq)=aF_t+q (E1), q(F_h+ap)=aF_h+p (E2).
Eliminating q gives `msgQuad`:
a(1+F_t)p²+(F_h F_t+a²(F_h−F_t)−1)p−aF_h(1+F_t)=0 (`msgQuad_eq_zero`).
The roots have product −F_h, so there is one positive root `posMsg` and one
negative root −F_h/posMsg. The positive pair in both orientations satisfies
(E1)–(E2) (`posMsg_edge`), as does its negative counterpart (`negMsg_edge`).
Every solution belongs to the positive or negative pair according to the sign
of p (`eq_posMsg_of_pos`, `eq_negMsg_of_neg`).
For a≠1, `posMsg_between` puts the positive branch strictly between a and 1/a.
In coordinates F=e^{2u}, z⁺=½log posMsg is C¹ (`contDiff_zPlus`), bounded by
|½log a|, and satisfies z⁺_h=g_a(u_t−z⁺_t) (`zPlus_eq_g`), where
g_a(x)=½log((ae^{2x}+1)/(e^{2x}+a)). On either half-line |x|≥L, g_a has
Lipschitz constant (|a²−1|/a)e^{−2L} (`g_lipschitz_Ici`, `g_lipschitz_Iic`).
-/

namespace BPFixedPoints

namespace BP

open Real

section Quadratic

/-- Positive root of a quadratic with leading coefficient A>0 and constant term −C<0. -/
noncomputable def quadPosRoot (A B C : ℝ) : ℝ := (-B + √(B ^ 2 + 4 * A * C)) / (2 * A)

theorem quadPosRoot_spec {A B C : ℝ} (hA : 0 < A) (hC : 0 < C) :
    A * quadPosRoot A B C ^ 2 + B * quadPosRoot A B C - C = 0 ∧ 0 < quadPosRoot A B C := by
  have hd : 0 ≤ B ^ 2 + 4 * A * C := by positivity
  have hs := Real.sq_sqrt hd
  have hlt : |B| < √(B ^ 2 + 4 * A * C) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  constructor
  · unfold quadPosRoot
    set t := √(B ^ 2 + 4 * A * C)
    have key : A * ((-B + t) / (2 * A)) ^ 2 + B * ((-B + t) / (2 * A)) - C =
        (t ^ 2 - (B ^ 2 + 4 * A * C)) / (4 * A) := by
      field_simp; ring
    rw [key, hs, sub_self, zero_div]
  · unfold quadPosRoot
    apply div_pos _ (by positivity)
    linarith [le_abs_self B]

/-- A quadratic root is the positive root r or its Vieta partner −C/(Ar). -/
theorem quad_root_cases {A B C x : ℝ} (hA : 0 < A) (hC : 0 < C)
    (hx : A * x ^ 2 + B * x - C = 0) :
    x = quadPosRoot A B C ∨ x = -C / (A * quadPosRoot A B C) := by
  obtain ⟨hr, hrpos⟩ := quadPosRoot_spec (B := B) hA hC
  set r := quadPosRoot A B C
  have hfac : A * x ^ 2 + B * x - C = (x - r) * (A * x + C / r) := by
    have hCr : C / r = A * r + B := by
      rw [div_eq_iff hrpos.ne']; linarith
    rw [hCr]; linear_combination hr
  rw [hfac] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact Or.inl (by linarith)
  · right
    field_simp
    have : A * x * r + C = 0 := by
      have := h; field_simp at this; linarith
    linarith

end Quadratic

section Edge

/-- Quadratic for p after eliminating q from (E1)–(E2). -/
def msgQuad (a Fh Ft p : ℝ) : ℝ :=
  a * (1 + Ft) * p ^ 2 + (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) * p - a * Fh * (1 + Ft)

/-- A solution of (E1)–(E2) satisfies the p-quadratic, by a polynomial identity. -/
theorem msgQuad_eq_zero {a Fh Ft p q : ℝ} (h1 : p * (Ft + a * q) = a * Ft + q)
    (h2 : q * (Fh + a * p) = a * Fh + p) : msgQuad a Fh Ft p = 0 := by
  unfold msgQuad
  linear_combination (Fh + a * p) * h1 - (a * p - 1) * h2

/-- Positive-branch message toward h: the positive root of the p-quadratic. -/
noncomputable def posMsg (a Fh Ft : ℝ) : ℝ :=
  quadPosRoot (a * (1 + Ft)) (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) (a * Fh * (1 + Ft))

variable {a Fh Ft : ℝ}

theorem posMsg_spec (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    msgQuad a Fh Ft (posMsg a Fh Ft) = 0 ∧ 0 < posMsg a Fh Ft := by
  obtain ⟨h, hpos⟩ := quadPosRoot_spec (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1)
    (by positivity : 0 < a * (1 + Ft)) (by positivity : 0 < a * Fh * (1 + Ft))
  exact ⟨by unfold msgQuad posMsg; linarith, hpos⟩

theorem posMsg_pos (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) : 0 < posMsg a Fh Ft :=
  (posMsg_spec ha hFh hFt).2

/-- The quadratic has exactly one positive root. -/
theorem eq_posMsg_of_msgQuad (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) {p : ℝ}
    (hp : msgQuad a Fh Ft p = 0) (hp0 : 0 < p) : p = posMsg a Fh Ft := by
  have hA : 0 < a * (1 + Ft) := by positivity
  have hC : 0 < a * Fh * (1 + Ft) := by positivity
  rcases quad_root_cases (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1) (x := p) hA hC
    (by unfold msgQuad at hp; linarith) with h | h
  · exact h
  · exfalso
    have hr := (quadPosRoot_spec (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1) hA hC).2
    have : -(a * Fh * (1 + Ft)) / (a * (1 + Ft) * quadPosRoot (a * (1 + Ft))
        (Fh * Ft + a ^ 2 * (Fh - Ft) - 1) (a * Fh * (1 + Ft))) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith

/-- Its negative root is −F_h/posMsg. -/
theorem eq_negMsg_of_msgQuad (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) {p : ℝ}
    (hp : msgQuad a Fh Ft p = 0) (hp0 : p < 0) : p = -Fh / posMsg a Fh Ft := by
  have hA : 0 < a * (1 + Ft) := by positivity
  have hC : 0 < a * Fh * (1 + Ft) := by positivity
  have hr := (quadPosRoot_spec (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1) hA hC).2
  rcases quad_root_cases (B := Fh * Ft + a ^ 2 * (Fh - Ft) - 1) (x := p) hA hC
    (by unfold msgQuad at hp; linarith) with h | h
  · exfalso; rw [h] at hp0; linarith
  · rw [h]
    unfold posMsg
    have h1 : a * (1 + Ft) ≠ 0 := hA.ne'
    field_simp

/-- **The positive branch satisfies the edge equations.** -/
theorem posMsg_edge (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    posMsg a Fh Ft * (Ft + a * posMsg a Ft Fh) = a * Ft + posMsg a Ft Fh ∧
      posMsg a Ft Fh * (Fh + a * posMsg a Fh Ft) = a * Fh + posMsg a Fh Ft := by
  obtain ⟨hQ, hp⟩ := posMsg_spec ha hFh hFt
  set p := posMsg a Fh Ft
  have hden : 0 < Fh + a * p := by positivity
  set q' := (a * Fh + p) / (Fh + a * p)
  have hq'pos : 0 < q' := by positivity
  have h2 : q' * (Fh + a * p) = a * Fh + p := div_mul_cancel₀ _ hden.ne'
  -- Derive (E1) from the quadratic.
  have h1 : p * (Ft + a * q') = a * Ft + q' := by
    have hid : msgQuad a Fh Ft p =
        (Fh + a * p) * (p * (Ft + a * q') - a * Ft - q') - (a * p - 1) *
          (q' * (Fh + a * p) - a * Fh - p) := by
      unfold msgQuad; ring
    have hr2 : q' * (Fh + a * p) - a * Fh - p = 0 := by linarith
    rw [hQ, hr2, mul_zero, sub_zero] at hid
    have := (mul_eq_zero.1 hid.symm).resolve_left hden.ne'
    linarith
  -- q' is the positive root of the t-side quadratic.
  have hQt : msgQuad a Ft Fh q' = 0 := msgQuad_eq_zero h2 h1
  have hq : q' = posMsg a Ft Fh := eq_posMsg_of_msgQuad ha hFt hFh hQt hq'pos
  rw [← hq]
  exact ⟨h1, h2⟩

/-- **The negative branch also satisfies the edge equations.** The transformation (p,q)↦(−F_h/p,−F_t/q) interchanges (E1) and (E2). -/
theorem negMsg_edge (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (-Fh / posMsg a Fh Ft) * (Ft + a * (-Ft / posMsg a Ft Fh)) = a * Ft + (-Ft / posMsg a Ft Fh) ∧
      (-Ft / posMsg a Ft Fh) * (Fh + a * (-Fh / posMsg a Fh Ft)) =
        a * Fh + (-Fh / posMsg a Fh Ft) := by
  obtain ⟨h1, h2⟩ := posMsg_edge ha hFh hFt
  have hp := (posMsg_pos ha hFh hFt).ne'
  have hq := (posMsg_pos ha hFt hFh).ne'
  set p := posMsg a Fh Ft
  set q := posMsg a Ft Fh
  have e1 : (-Fh / p) * (Ft + a * (-Ft / q)) - (a * Ft + (-Ft / q)) =
      -Ft / (p * q) * (q * (Fh + a * p) - (a * Fh + p)) := by
    field_simp; ring
  have e2 : (-Ft / q) * (Fh + a * (-Fh / p)) - (a * Fh + (-Fh / p)) =
      -Fh / (p * q) * (p * (Ft + a * q) - (a * Ft + q)) := by
    field_simp; ring
  rw [h2, sub_self, mul_zero, sub_eq_zero] at e1
  rw [h1, sub_self, mul_zero, sub_eq_zero] at e2
  exact ⟨e1, e2⟩

/-- An edge-equation solution with p>0 is the positive branch. -/
theorem eq_posMsg_of_pos (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) {p q : ℝ}
    (h1 : p * (Ft + a * q) = a * Ft + q) (h2 : q * (Fh + a * p) = a * Fh + p) (hp : 0 < p) :
    p = posMsg a Fh Ft :=
  eq_posMsg_of_msgQuad ha hFh hFt (msgQuad_eq_zero h1 h2) hp

/-- An edge-equation solution with p<0 is the negative branch. -/
theorem eq_negMsg_of_neg (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) {p q : ℝ}
    (h1 : p * (Ft + a * q) = a * Ft + q) (h2 : q * (Fh + a * p) = a * Fh + p) (hp : p < 0) :
    p = -Fh / posMsg a Fh Ft :=
  eq_negMsg_of_msgQuad ha hFh hFt (msgQuad_eq_zero h1 h2) hp

/-- The positive branch is (aX+1)/(X+a), where X=F_t/q⁺>0. -/
theorem posMsg_eq_update (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    posMsg a Fh Ft = (a * (Ft / posMsg a Ft Fh) + 1) / (Ft / posMsg a Ft Fh + a) := by
  obtain ⟨h1, -⟩ := posMsg_edge ha hFh hFt
  have hq := posMsg_pos ha hFt hFh
  have hden : 0 < Ft / posMsg a Ft Fh + a := by positivity
  rw [eq_div_iff hden.ne']
  field_simp
  linarith

/-- For X>0 and a≠1, f=(aX+1)/(X+a) lies strictly between a and 1/a: (f−a)(f−1/a)<0. -/
theorem update_between {X : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hX : 0 < X) :
    ((a * X + 1) / (X + a) - a) * ((a * X + 1) / (X + a) - 1 / a) < 0 := by
  have hden : 0 < X + a := by linarith
  have h1 : (a * X + 1) / (X + a) - a = (1 - a ^ 2) / (X + a) := by
    field_simp; ring
  have h2 : (a * X + 1) / (X + a) - 1 / a = (a ^ 2 - 1) * X / (a * (X + a)) := by
    field_simp; ring
  rw [h1, h2]
  have hsq : 0 < (1 - a ^ 2) ^ 2 := by
    have : 1 - a ^ 2 ≠ 0 := by
      intro h
      have : (a - 1) * (a + 1) = 0 := by linear_combination -h
      rcases mul_eq_zero.1 this with h' | h'
      · exact ha1 (by linarith)
      · linarith
    positivity
  have : (1 - a ^ 2) / (X + a) * ((a ^ 2 - 1) * X / (a * (X + a))) =
      -((1 - a ^ 2) ^ 2 * X / (a * (X + a) ^ 2)) := by
    field_simp; ring
  rw [this, neg_lt_zero]
  positivity

theorem posMsg_between (ha : 0 < a) (ha1 : a ≠ 1) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    (posMsg a Fh Ft - a) * (posMsg a Fh Ft - 1 / a) < 0 := by
  rw [posMsg_eq_update ha hFh hFt]
  exact update_between ha ha1 (div_pos hFt (posMsg_pos ha hFt hFh))

theorem posMsg_ne (ha : 0 < a) (ha1 : a ≠ 1) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    posMsg a Fh Ft ≠ a := by
  intro h
  have := posMsg_between ha ha1 hFh hFt
  rw [h, sub_self, zero_mul] at this
  exact lt_irrefl 0 this

/-- |log posMsg| ≤ |log a|。 -/
theorem abs_log_posMsg_le (ha : 0 < a) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    |Real.log (posMsg a Fh Ft)| ≤ |Real.log a| := by
  have hp := posMsg_pos ha hFh hFt
  rcases eq_or_ne a 1 with h1 | h1
  · -- If a=1, posMsg=1.
    subst h1
    have := posMsg_eq_update (a := 1) one_pos hFh hFt
    have hq := posMsg_pos (a := 1) one_pos hFt hFh
    rw [this, Real.log_one, abs_zero]
    have hden : Ft / posMsg 1 Ft Fh + 1 ≠ 0 := by positivity
    rw [one_mul, div_self hden, Real.log_one, abs_zero]
  · have hb := posMsg_between ha h1 hFh hFt
    set p := posMsg a Fh Ft
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · -- a < 1 < 1/a：a < p < 1/a
      have h1a : a < 1 / a := by rw [lt_div_iff₀ ha]; nlinarith
      have hlo : a < p := by
        by_contra h; push Not at h
        have : 0 ≤ (p - a) * (p - 1 / a) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        linarith
      have hhi : p < 1 / a := by
        by_contra h; push Not at h
        have : 0 ≤ (p - a) * (p - 1 / a) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hla : Real.log a < 0 := Real.log_neg ha hlt
      rw [abs_of_neg hla, abs_le]
      constructor
      · linarith [Real.log_lt_log ha hlo]
      · have := Real.log_lt_log hp hhi
        rw [one_div, Real.log_inv] at this
        linarith
    · have h1a : 1 / a < a := by rw [div_lt_iff₀ ha]; nlinarith
      have hlo : 1 / a < p := by
        by_contra h; push Not at h
        have : 0 ≤ (p - a) * (p - 1 / a) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        linarith
      have hhi : p < a := by
        by_contra h; push Not at h
        have : 0 ≤ (p - a) * (p - 1 / a) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hla : 0 < Real.log a := Real.log_pos hgt
      rw [abs_of_pos hla, abs_le]
      constructor
      · have := Real.log_lt_log (by positivity) hlo
        rw [one_div, Real.log_inv] at this
        linarith
      · linarith [Real.log_lt_log hp hhi]

end Edge

section LogCoordinates

/-- Positive branch in logarithmic coordinates: z⁺=½log posMsg(a,e^{2u_h},e^{2u_t}). -/
noncomputable def zPlus (a uh ut : ℝ) : ℝ :=
  Real.log (posMsg a (Real.exp (2 * uh)) (Real.exp (2 * ut))) / 2

/-- Logarithmic update g_a(x)=½log((ae^{2x}+1)/(e^{2x}+a)). -/
noncomputable def gUpd (a x : ℝ) : ℝ :=
  Real.log ((a * Real.exp (2 * x) + 1) / (Real.exp (2 * x) + a)) / 2

variable {a : ℝ}

theorem abs_zPlus_le (ha : 0 < a) (uh ut : ℝ) : |zPlus a uh ut| ≤ |Real.log a| / 2 := by
  unfold zPlus
  rw [abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_log_posMsg_le ha (Real.exp_pos _) (Real.exp_pos _))
    zero_le_two

/-- If a≠1, |log posMsg|<|log a|, the strict `posMsg_between` bound. -/
theorem abs_log_posMsg_lt {Fh Ft : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hFh : 0 < Fh) (hFt : 0 < Ft) :
    |Real.log (posMsg a Fh Ft)| < |Real.log a| := by
  have hp := posMsg_pos ha hFh hFt
  have hb := posMsg_between ha ha1 hFh hFt
  have hia : 0 < 1 / a := by positivity
  have hlog_inv : Real.log (1 / a) = -Real.log a := by
    rw [Real.log_div one_ne_zero ha.ne', Real.log_one, zero_sub]
  rcases mul_neg_iff.1 hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- a<p<1/a, hence a<1.
    have hap : a < posMsg a Fh Ft := by linarith
    have hpa : posMsg a Fh Ft < 1 / a := by linarith
    have ha1' : a < 1 := by
      by_contra h
      push Not at h
      have : 1 / a ≤ a := by rw [div_le_iff₀ ha]; nlinarith
      linarith
    have hla : Real.log a < 0 := Real.log_neg ha ha1'
    rw [abs_of_neg hla, abs_lt]
    constructor
    · have := Real.log_lt_log ha hap
      linarith
    · have := Real.log_lt_log hp hpa
      rw [hlog_inv] at this
      linarith
  · -- 1/a<p<a, hence 1<a.
    have hpa : posMsg a Fh Ft < a := by linarith
    have hap : 1 / a < posMsg a Fh Ft := by linarith
    have ha1' : 1 < a := by
      by_contra h
      push Not at h
      have : a ≤ 1 / a := by rw [le_div_iff₀ ha]; nlinarith
      linarith
    have hla : 0 < Real.log a := Real.log_pos ha1'
    rw [abs_of_pos hla, abs_lt]
    constructor
    · have := Real.log_lt_log hia hap
      rw [hlog_inv] at this
      linarith
    · have := Real.log_lt_log hp hpa
      linarith

/-- Strict `real:edge-bound`: J_e≠0 (a≠1) gives |z⁺|<|J_e|=|½log a|. -/
theorem abs_zPlus_lt (ha : 0 < a) (ha1 : a ≠ 1) (uh ut : ℝ) :
    |zPlus a uh ut| < |Real.log a| / 2 := by
  unfold zPlus
  rw [abs_div, abs_two]
  exact div_lt_div_of_pos_right (abs_log_posMsg_lt ha ha1 (Real.exp_pos _) (Real.exp_pos _))
    two_pos

theorem exp_two_zPlus (ha : 0 < a) (uh ut : ℝ) :
    Real.exp (2 * zPlus a uh ut) = posMsg a (Real.exp (2 * uh)) (Real.exp (2 * ut)) := by
  unfold zPlus
  rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (posMsg_pos ha (Real.exp_pos _) (Real.exp_pos _))]

/-- z⁺_h = g_a(u_t − z⁺_t)。 -/
theorem zPlus_eq_g (ha : 0 < a) (uh ut : ℝ) : zPlus a uh ut = gUpd a (ut - zPlus a ut uh) := by
  unfold gUpd
  have hX : Real.exp (2 * (ut - zPlus a ut uh)) =
      Real.exp (2 * ut) / posMsg a (Real.exp (2 * ut)) (Real.exp (2 * uh)) := by
    rw [mul_sub, Real.exp_sub, exp_two_zPlus ha]
  rw [hX, ← posMsg_eq_update ha (Real.exp_pos _) (Real.exp_pos _)]
  rfl

/-- The positive branch is C¹ in u. -/
theorem contDiff_zPlus (ha : 0 < a) {n : ℕ∞} : ContDiff ℝ n fun u : ℝ × ℝ => zPlus a u.1 u.2 := by
  unfold zPlus posMsg quadPosRoot
  have hFh : ContDiff ℝ n fun u : ℝ × ℝ => Real.exp (2 * u.1) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  have hFt : ContDiff ℝ n fun u : ℝ × ℝ => Real.exp (2 * u.2) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)
  have hB : ContDiff ℝ n fun u : ℝ × ℝ =>
      Real.exp (2 * u.1) * Real.exp (2 * u.2) +
        a ^ 2 * (Real.exp (2 * u.1) - Real.exp (2 * u.2)) - 1 :=
    ((hFh.mul hFt).add (contDiff_const.mul (hFh.sub hFt))).sub contDiff_const
  have hD : ContDiff ℝ n fun u : ℝ × ℝ =>
      (Real.exp (2 * u.1) * Real.exp (2 * u.2) +
        a ^ 2 * (Real.exp (2 * u.1) - Real.exp (2 * u.2)) - 1) ^ 2 +
      4 * (a * (1 + Real.exp (2 * u.2))) * (a * Real.exp (2 * u.1) * (1 + Real.exp (2 * u.2))) :=
    (hB.pow 2).add ((contDiff_const.mul (contDiff_const.mul (contDiff_const.add hFt))).mul
      ((contDiff_const.mul hFh).mul (contDiff_const.add hFt)))
  have hDpos : ∀ u : ℝ × ℝ, (Real.exp (2 * u.1) * Real.exp (2 * u.2) +
        a ^ 2 * (Real.exp (2 * u.1) - Real.exp (2 * u.2)) - 1) ^ 2 +
      4 * (a * (1 + Real.exp (2 * u.2))) * (a * Real.exp (2 * u.1) * (1 + Real.exp (2 * u.2)))
        ≠ 0 := fun u => by positivity
  have hN : ContDiff ℝ n fun u : ℝ × ℝ => -(Real.exp (2 * u.1) * Real.exp (2 * u.2) +
        a ^ 2 * (Real.exp (2 * u.1) - Real.exp (2 * u.2)) - 1) +
      √((Real.exp (2 * u.1) * Real.exp (2 * u.2) +
        a ^ 2 * (Real.exp (2 * u.1) - Real.exp (2 * u.2)) - 1) ^ 2 +
      4 * (a * (1 + Real.exp (2 * u.2))) * (a * Real.exp (2 * u.1) * (1 + Real.exp (2 * u.2)))) :=
    hB.neg.add (hD.sqrt hDpos)
  have hden2 : ContDiff ℝ n fun u : ℝ × ℝ => 2 * (a * (1 + Real.exp (2 * u.2))) :=
    contDiff_const.mul (contDiff_const.mul (contDiff_const.add hFt))
  have hQ := hN.div hden2 (fun u => by positivity)
  refine (hQ.log fun u => ?_).div_const 2
  exact (posMsg_pos ha (Real.exp_pos (2 * u.1)) (Real.exp_pos (2 * u.2))).ne'

/-- Derivative of g_a. -/
theorem hasDerivAt_gUpd (ha : 0 < a) (x : ℝ) :
    HasDerivAt (gUpd a) ((a ^ 2 - 1) * Real.exp (2 * x) /
      ((a * Real.exp (2 * x) + 1) * (Real.exp (2 * x) + a))) x := by
  have hE : HasDerivAt (fun x => Real.exp (2 * x)) (Real.exp (2 * x) * 2) x := by
    have := ((hasDerivAt_id x).const_mul 2).exp
    simpa using this
  have hEpos := Real.exp_pos (2 * x)
  have hnum : HasDerivAt (fun x => a * Real.exp (2 * x) + 1) (a * (Real.exp (2 * x) * 2)) x :=
    (hE.const_mul a).add_const 1
  have hden : HasDerivAt (fun x => Real.exp (2 * x) + a) (Real.exp (2 * x) * 2) x :=
    hE.add_const a
  have hd1 : Real.exp (2 * x) + a ≠ 0 := by positivity
  have hd2 : a * Real.exp (2 * x) + 1 ≠ 0 := by positivity
  have h := ((hnum.div hden hd1).log (by simp only [Pi.div_apply]; positivity)).div_const 2
  simp only [Pi.div_apply] at h
  show HasDerivAt (fun y => Real.log ((a * Real.exp (2 * y) + 1) / (Real.exp (2 * y) + a)) / 2) _ x
  refine h.congr_deriv ?_
  field_simp
  ring

/-- Derivative bound |g'(x)|≤(|a²−1|/a)e^{−2|x|}, expressed separately for x≥L and x≤−L. -/
theorem abs_deriv_gUpd_le_of_ge (ha : 0 < a) {L x : ℝ} (hx : L ≤ x) :
    |(a ^ 2 - 1) * Real.exp (2 * x) / ((a * Real.exp (2 * x) + 1) * (Real.exp (2 * x) + a))| ≤
      |a ^ 2 - 1| / a * Real.exp (-(2 * L)) := by
  set E := Real.exp (2 * x)
  have hE : 0 < E := Real.exp_pos _
  have hE1 : Real.exp (2 * L) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hden : a * E * E ≤ (a * E + 1) * (E + a) := by
    have h1 : (a * E + 1) * (E + a) = a * E * E + (a ^ 2 * E + E + a) := by ring
    have h2 : 0 < a ^ 2 * E + E + a := by positivity
    linarith
  rw [abs_div, abs_mul, abs_of_pos hE, abs_of_pos (by positivity : 0 < (a * E + 1) * (E + a))]
  rw [div_le_iff₀ (by positivity)]
  have hexp : Real.exp (-(2 * L)) * E ≥ 1 := by
    rw [Real.exp_neg]
    rw [ge_iff_le, le_inv_mul_iff₀ (Real.exp_pos _)]
    simpa using hE1
  calc |a ^ 2 - 1| * E = |a ^ 2 - 1| / a * (a * E * E) * (1 / E) := by field_simp
    _ ≤ |a ^ 2 - 1| / a * ((a * E + 1) * (E + a)) * (Real.exp (-(2 * L))) := by
        gcongr
        rw [div_le_iff₀ hE]; linarith
    _ = |a ^ 2 - 1| / a * Real.exp (-(2 * L)) * ((a * E + 1) * (E + a)) := by ring

theorem abs_deriv_gUpd_le_of_le (ha : 0 < a) {L x : ℝ} (hx : x ≤ -L) :
    |(a ^ 2 - 1) * Real.exp (2 * x) / ((a * Real.exp (2 * x) + 1) * (Real.exp (2 * x) + a))| ≤
      |a ^ 2 - 1| / a * Real.exp (-(2 * L)) := by
  set E := Real.exp (2 * x)
  have hE : 0 < E := Real.exp_pos _
  have hE1 : E ≤ Real.exp (-(2 * L)) := Real.exp_le_exp.2 (by linarith)
  have hden : a ≤ (a * E + 1) * (E + a) := by
    have h1 : (a * E + 1) * (E + a) = a + (a * E * E + a ^ 2 * E + E) := by ring
    have h2 : 0 < a * E * E + a ^ 2 * E + E := by positivity
    linarith
  rw [abs_div, abs_mul, abs_of_pos hE, abs_of_pos (by positivity : 0 < (a * E + 1) * (E + a))]
  rw [div_le_iff₀ (by positivity)]
  calc |a ^ 2 - 1| * E = |a ^ 2 - 1| / a * E * a := by field_simp
    _ ≤ |a ^ 2 - 1| / a * Real.exp (-(2 * L)) * ((a * E + 1) * (E + a)) := by
        gcongr

/-- g_a is Lipschitz on [L,∞) with constant (|a²−1|/a)e^{−2L}. -/
theorem g_lipschitz_Ici (ha : 0 < a) {L x y : ℝ} (hx : L ≤ x) (hy : L ≤ y) :
    |gUpd a x - gUpd a y| ≤ |a ^ 2 - 1| / a * Real.exp (-(2 * L)) * |x - y| := by
  have := (convex_Ici L).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := gUpd a) (fun z _ => (hasDerivAt_gUpd ha z).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact abs_deriv_gUpd_le_of_ge ha hz) hy hx
  simpa [Real.norm_eq_abs] using this

/-- g_a is Lipschitz on (−∞,−L] with constant (|a²−1|/a)e^{−2L}. -/
theorem g_lipschitz_Iic (ha : 0 < a) {L x y : ℝ} (hx : x ≤ -L) (hy : y ≤ -L) :
    |gUpd a x - gUpd a y| ≤ |a ^ 2 - 1| / a * Real.exp (-(2 * L)) * |x - y| := by
  have := (convex_Iic (-L)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := gUpd a) (fun z _ => (hasDerivAt_gUpd ha z).hasDerivWithinAt)
    (fun z hz => by rw [Real.norm_eq_abs]; exact abs_deriv_gUpd_le_of_le ha hz) hy hx
  simpa [Real.norm_eq_abs] using this

end LogCoordinates

end BP

end BPFixedPoints
