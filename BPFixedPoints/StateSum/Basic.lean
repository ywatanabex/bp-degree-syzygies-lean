import BPFixedPoints.Graph.Basic

/-!
# Candidate sum Q and polynomials 𝒬

Define φ(0)=1, φ(k)=k−1 for k≥1; Q(G)=Σ_{S⊆E}∏_vφ(d_S(v));
𝒬_G(t)=Σ_S t^{|S|}∏_vφ(d_S(v)); and
𝒬_G(x,z)=Σ_S x^{|S|}z^{v(S)}∏_vφ(d_S(v)), where v(S) counts positive-degree
vertices. The basic form `QOn A` specifies a subgraph's edge set; the whole
graph uses A=Finset.univ. Also define the Watanabe–Fukumizu θ local coefficients
at γ=2: f₀=1, f₁=0, f_{d+2}=2f_{d+1}+f_d.
-/

namespace BPFixedPoints

/-- φ(0)=1、φ(k+1)=k。 -/
def phi : ℕ → ℕ
  | 0 => 1
  | k + 1 => k

@[simp] theorem phi_zero : phi 0 = 1 := rfl
@[simp] theorem phi_succ (k : ℕ) : phi (k + 1) = k := rfl
theorem phi_one : phi 1 = 0 := rfl

theorem phi_of_pos {k : ℕ} (hk : 0 < k) : phi k = k - 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp

theorem phi_pos_of_ne_one {k : ℕ} (hk : k ≠ 1) : 0 < phi k := by
  rcases k with _ | _ | k <;> simp_all

/-- For all a,b, φ(a)φ(b)+ab=φ(a+b)+2·1_{a≥2,b≥2}φ(a)φ(b). -/
theorem phi_local (a b : ℕ) :
    phi a * phi b + a * b = phi (a + b) + 2 * (if 2 ≤ a ∧ 2 ≤ b then phi a * phi b else 0) := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b
  · simp
  · simp
  · simp
  · simp
  · simp
  · have : 1 + (b + 2) = (b + 2) + 1 := by omega
    rw [this]; simp
  · simp
  · have : a + 2 + 1 = (a + 2) + 1 := rfl
    simp
  · have h : a + 2 + (b + 2) = (a + b + 3) + 1 := by omega
    have hc : 2 ≤ a + 2 ∧ 2 ≤ b + 2 := ⟨by omega, by omega⟩
    rw [h]
    simp only [hc, and_self, ite_true, phi_succ]
    ring

/-- φ(a+b)≤φ(a)φ(b)+ab: local contraction monotonicity. -/
theorem phi_add_le (a b : ℕ) : phi (a + b) ≤ phi a * phi b + a * b := by
  rw [phi_local]; omega

/-- Local θ coefficients at γ=2: f₀=1, f₁=0, f_{d+2}=2f_{d+1}+f_d. -/
def f2 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | d + 2 => 2 * f2 (d + 1) + f2 d

@[simp] theorem f2_zero : f2 0 = 1 := rfl
@[simp] theorem f2_one : f2 1 = 0 := rfl
theorem f2_add_two (d : ℕ) : f2 (d + 2) = 2 * f2 (d + 1) + f2 d := rfl
theorem f2_two : f2 2 = 1 := rfl
theorem f2_three : f2 3 = 2 := rfl
theorem f2_four : f2 4 = 5 := rfl

/-- f_{a+1}f_{b+1}+f_a f_b=f_{a+b}: the local identity giving pure deletion–contraction for θ at γ=2. -/
theorem f2_local (a b : ℕ) : f2 (a + 1) * f2 (b + 1) + f2 a * f2 b = f2 (a + b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases a with _ | _ | a
    · simp
    · rw [Nat.add_comm 1 b]; simp [f2_two]
    · have h1 := ih (a + 1) (by omega) b
      have h0 := ih a (by omega) b
      have e1 : a + 2 + 1 = (a + 1) + 2 := by omega
      have e2 : a + 2 + b = (a + b) + 2 := by omega
      have e3 : a + 1 + b = (a + b) + 1 := by omega
      rw [e3] at h1
      rw [e2, f2_add_two (a + b), ← h1, ← h0, f2_add_two (a + 1), f2_add_two a]
      ring

/-- For d≤3, φ(d)=f_d(2). -/
theorem f2_eq_phi_of_le_three {d : ℕ} (hd : d ≤ 3) : f2 d = phi d := by
  rcases d with _ | _ | _ | _ | d
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

theorem f2_ge_phi_aux (d : ℕ) : d + 1 ≤ f2 (d + 2) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp [f2_two]
    · simp [f2_three]
    · have h1 := ih (d + 1) (by omega)
      have h0 := ih d (by omega)
      rw [show d + 1 + 2 = d + 2 + 1 by omega] at h1
      rw [f2_add_two]
      omega

/-- For every d, φ(d)≤f_d(2). -/
theorem phi_le_f2 (d : ℕ) : phi d ≤ f2 d := by
  rcases d with _ | _ | d
  · simp
  · simp
  · simpa using f2_ge_phi_aux d

theorem f2_gt_phi_aux (d : ℕ) : d + 4 < f2 (d + 4) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases d with _ | _ | d
    · simp [f2_four]
    · simp [show f2 5 = 12 by rfl]
    · have h1 := ih (d + 1) (by omega)
      have h0 := ih d (by omega)
      rw [show d + 1 + 4 = d + 4 + 1 by omega] at h1
      rw [show d + 2 + 4 = (d + 4) + 2 by omega, f2_add_two]
      omega

/-- For d≥4, φ(d)<f_d(2). -/
theorem phi_lt_f2_of_four_le {d : ℕ} (hd : 4 ≤ d) : phi d < f2 d := by
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 4 := ⟨d - 4, by omega⟩
  have h := f2_gt_phi_aux j
  simp only [phi_succ]
  omega

theorem f2_pos_of_ne_one {k : ℕ} (hk : k ≠ 1) : 0 < f2 k :=
  lt_of_lt_of_le (phi_pos_of_ne_one hk) (phi_le_f2 k)

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] (G : Multigraph V E)

/-- Weight ∏_v g(d_S(v)) of an edge set S for local weights g. -/
def wt (g : ℕ → ℕ) (S : Finset E) : ℕ := ∏ v, g (G.deg S v)

/-- Candidate sum Q=Σ_{S⊆A}∏_v φ(d_S(v)) for the subgraph with edge set A. -/
def QOn (A : Finset E) : ℕ := ∑ S ∈ A.powerset, G.wt phi S

/-- Candidate sum Q(G) for the whole graph. -/
def Q [Fintype E] : ℕ := G.QOn Finset.univ

/-- θ_G(1,2)=Σ_{S⊆A}∏_v f_{d_S(v)}(2)。 -/
def thetaOn (A : Finset E) : ℕ := ∑ S ∈ A.powerset, G.wt f2 S

def theta [Fintype E] : ℕ := G.thetaOn Finset.univ

open Polynomial in
/-- Univariate polynomial 𝒬_A(t)=Σ_{S⊆A}t^{|S|}∏_v φ(d_S(v))∈ℤ[t]. -/
noncomputable def QpolyOn (A : Finset E) : ℤ[X] :=
  ∑ S ∈ A.powerset, (X : ℤ[X]) ^ S.card * (G.wt phi S : ℤ[X])

open Polynomial in
noncomputable def Qpoly [Fintype E] : ℤ[X] := G.QpolyOn Finset.univ

open Polynomial in
/-- θ_A(t,2)=Σ_{S⊆A} t^{|S|}∏_v f_{d_S(v)}(2) ∈ ℤ[t]。 -/
noncomputable def thetaPolyOn (A : Finset E) : ℤ[X] :=
  ∑ S ∈ A.powerset, (X : ℤ[X]) ^ S.card * (G.wt f2 S : ℤ[X])

/-- Number v(S) of positive-degree vertices. -/
def support (S : Finset E) : Finset V := Finset.univ.filter fun v => 0 < G.deg S v

open MvPolynomial in
/-- Bivariate polynomial 𝒬_A(x,z)=Σ_S x^{|S|}z^{v(S)}∏_v φ(d_S(v)); variable 0 is x and variable 1 is z. -/
noncomputable def Qpoly2On (A : Finset E) : MvPolynomial (Fin 2) ℤ :=
  ∑ S ∈ A.powerset, X 0 ^ S.card * X 1 ^ (G.support S).card * (G.wt phi S : MvPolynomial (Fin 2) ℤ)

noncomputable def Qpoly2 [Fintype E] : MvPolynomial (Fin 2) ℤ := G.Qpoly2On Finset.univ

section Eval

open Polynomial

theorem QpolyOn_eval_one (A : Finset E) : (G.QpolyOn A).eval 1 = (G.QOn A : ℤ) := by
  simp [QpolyOn, QOn, eval_finsetSum]

theorem thetaPolyOn_eval_one (A : Finset E) : (G.thetaPolyOn A).eval 1 = (G.thetaOn A : ℤ) := by
  simp [thetaPolyOn, thetaOn, eval_finsetSum]

/-- 𝒬_A(t) is 𝒬_A(x,z) evaluated at z=1. -/
theorem Qpoly2On_aeval (A : Finset E) :
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (X : ℤ[X]) else 1) (G.Qpoly2On A) =
      G.QpolyOn A := by
  simp [Qpoly2On, QpolyOn, map_sum]

/-- Q(G)=𝒬_G(1,1)。 -/
theorem Qpoly2On_eval_one (A : Finset E) :
    MvPolynomial.eval (fun _ : Fin 2 => (1 : ℤ)) (G.Qpoly2On A) = (G.QOn A : ℤ) := by
  simp [Qpoly2On, QOn, map_sum]

end Eval

section Monotone

/-- QOn is monotone in its edge set, since all summands are nonnegative. -/
theorem QOn_mono {A B : Finset E} (h : A ⊆ B) : G.QOn A ≤ G.QOn B :=
  Finset.sum_le_sum_of_subset (Finset.powerset_mono.2 h)

theorem wt_pos_of_forall_ne_one (g : ℕ → ℕ) (hg : ∀ k, k ≠ 1 → 0 < g k) {S : Finset E}
    (hS : ∀ v, G.deg S v ≠ 1) : 0 < G.wt g S :=
  Finset.prod_pos fun v _ => hg _ (hS v)

/-- A vertex of degree one makes the φ-weight zero. -/
theorem wt_phi_eq_zero_of_deg_eq_one {S : Finset E} {v : V} (hv : G.deg S v = 1) :
    G.wt phi S = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

theorem wt_f2_eq_zero_of_deg_eq_one {S : Finset E} {v : V} (hv : G.deg S v = 1) :
    G.wt f2 S = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

/-- Local weights at least φ give weights at least those of Q. -/
theorem wt_phi_le_wt_f2 (S : Finset E) : G.wt phi S ≤ G.wt f2 S :=
  Finset.prod_le_prod fun _ _ => phi_le_f2 _

end Monotone

end Multigraph

end BPFixedPoints
