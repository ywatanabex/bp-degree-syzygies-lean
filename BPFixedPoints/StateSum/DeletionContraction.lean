import BPFixedPoints.StateSum.Basic

/-!
# Deletion, contraction, vertex deletion and contraction monotonicity

For a non-loop edge e=uv, prove
𝒬_G(t)=(1−t)𝒬_{G−e}(t)+t𝒬_{G/e}(t)+2tR(t), with
R=𝒬_{G−e}−𝒬_{G−u}−𝒬_{G−v}+𝒬_{G−{u,v}}.
Represent G−e by A.erase e; G−u by filtering out incident edges, leaving u
isolated with φ(0)=1; and G/e by `G.contractMap e` on A.erase e.
Define R by summing terms of degree at least two at both u,v, so its coefficients
are nonnegative, and derive inclusion–exclusion. The same framework proves
pure deletion–contraction for θ(·,2), the γ=2 Watanabe–Fukumizu case.
-/

namespace BPFixedPoints

namespace Multigraph

open Polynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] (G : Multigraph V E)

/-- Product of local weights away from u and v. -/
def restWt (g : ℕ → ℕ) (u v : V) (S : Finset E) : ℕ :=
  ∏ w ∈ (Finset.univ.erase u).erase v, g (G.deg S w)

omit [DecidableEq E] in
theorem wt_eq_mul_restWt (g : ℕ → ℕ) {u v : V} (huv : u ≠ v) (S : Finset E) :
    G.wt g S = g (G.deg S u) * g (G.deg S v) * G.restWt g u v S := by
  unfold wt restWt
  rw [← Finset.mul_prod_erase Finset.univ (fun w => g (G.deg S w)) (Finset.mem_univ u),
    ← Finset.mul_prod_erase (Finset.univ.erase u) (fun w => g (G.deg S w))
      (Finset.mem_erase.2 ⟨huv.symm, Finset.mem_univ v⟩), mul_assoc]

section Edge

variable {G} {e : E}

theorem restWt_insert (g : ℕ → ℕ) {T : Finset E} (hT : e ∉ T) :
    G.restWt g (G.fst e) (G.snd e) (insert e T) = G.restWt g (G.fst e) (G.snd e) T := by
  unfold restWt
  apply Finset.prod_congr rfl
  intro w hw
  rw [Finset.mem_erase, Finset.mem_erase] at hw
  rw [G.deg_insert hT, G.endCount_of_ne_ne (Ne.symm hw.2.1) (Ne.symm hw.1), add_zero]

omit [DecidableEq E] in
theorem restWt_contractMap (g : ℕ → ℕ) (T : Finset E) :
    (G.contractMap e).restWt g (G.fst e) (G.snd e) T = G.restWt g (G.fst e) (G.snd e) T := by
  unfold restWt
  apply Finset.prod_congr rfl
  intro w hw
  rw [Finset.mem_erase, Finset.mem_erase] at hw
  rw [contractMap_deg_of_ne _ hw.2.1 hw.1]

variable (he : G.fst e ≠ G.snd e)
include he

theorem wt_eq_of_edge (g : ℕ → ℕ) (T : Finset E) :
    G.wt g T = g (G.deg T (G.fst e)) * g (G.deg T (G.snd e)) * G.restWt g (G.fst e) (G.snd e) T :=
  G.wt_eq_mul_restWt g he T

theorem wt_insert_eq (g : ℕ → ℕ) {T : Finset E} (hT : e ∉ T) :
    G.wt g (insert e T) =
      g (G.deg T (G.fst e) + 1) * g (G.deg T (G.snd e) + 1) * G.restWt g (G.fst e) (G.snd e) T := by
  rw [G.wt_eq_mul_restWt g he, restWt_insert g hT, G.deg_insert hT, G.deg_insert hT,
    G.endCount_fst_of_ne he, G.endCount_snd_of_ne he]

theorem contractMap_wt_eq (g : ℕ → ℕ) (T : Finset E) :
    (G.contractMap e).wt g T =
      g (G.deg T (G.fst e) + G.deg T (G.snd e)) * g 0 * G.restWt g (G.fst e) (G.snd e) T := by
  rw [(G.contractMap e).wt_eq_mul_restWt g he, restWt_contractMap, contractMap_deg_fst he,
    contractMap_deg_snd he]

end Edge

/-- Local identity φ(a)φ(b)+ab=φ(a+b)+2·1_{a≥2,b≥2}φ(a)φ(b), multiplied by r. -/
theorem phi_local_mul (a b r : ℕ) :
    phi a * phi b * r + a * b * r =
      phi (a + b) * r + 2 * (if 2 ≤ a ∧ 2 ≤ b then phi a * phi b * r else 0) := by
  have key := phi_local a b
  split_ifs at key ⊢
  · calc phi a * phi b * r + a * b * r = (phi a * phi b + a * b) * r := by ring
      _ = (phi (a + b) + 2 * (phi a * phi b)) * r := by rw [key]
      _ = _ := by ring
  · calc phi a * phi b * r + a * b * r = (phi a * phi b + a * b) * r := by ring
      _ = (phi (a + b) + 2 * 0) * r := by rw [key]
      _ = _ := by ring

section Pair

variable {G} {e : E} (he : G.fst e ≠ G.snd e)
include he

/-- Paired subsets excluding and including e: their φ weights equal the contracted weight plus a correction. -/
theorem wt_phi_pair {T : Finset E} (hT : e ∉ T) :
    G.wt phi T + G.wt phi (insert e T) =
      (G.contractMap e).wt phi T +
        2 * (if 2 ≤ G.deg T (G.fst e) ∧ 2 ≤ G.deg T (G.snd e) then G.wt phi T else 0) := by
  rw [wt_eq_of_edge he phi T, wt_insert_eq he phi hT, contractMap_wt_eq he phi T]
  simp only [phi_succ, phi_zero, mul_one]
  exact phi_local_mul _ _ _

/-- For f₂ weights the paired-subset identity has no correction. -/
theorem wt_f2_pair {T : Finset E} (hT : e ∉ T) :
    G.wt f2 T + G.wt f2 (insert e T) = (G.contractMap e).wt f2 T := by
  rw [wt_eq_of_edge he f2 T, wt_insert_eq he f2 hT, contractMap_wt_eq he f2 T]
  simp only [f2_zero, mul_one]
  rw [← add_mul, add_comm, f2_local]

end Pair

/-- R(1): sum of φ weights with degrees at u and v both at least two. -/
def ROn (e : E) (B : Finset E) : ℕ :=
  ∑ S ∈ B.powerset,
    if 2 ≤ G.deg S (G.fst e) ∧ 2 ≤ G.deg S (G.snd e) then G.wt phi S else 0

/-- Correction polynomial R(t), with degrees at u and v at least two and nonnegative integer coefficients. -/
noncomputable def RpolyOn (e : E) (B : Finset E) : ℤ[X] :=
  ∑ S ∈ B.powerset,
    if 2 ≤ G.deg S (G.fst e) ∧ 2 ≤ G.deg S (G.snd e) then
      (X : ℤ[X]) ^ S.card * (G.wt phi S : ℤ[X]) else 0

section Recurrence

variable {G} {e : E} {A : Finset E} (he : G.fst e ≠ G.snd e) (hA : e ∈ A)
include he hA

/-- At t=1, Q(G)=Q(G/e)+2R(1). -/
theorem QOn_eq_contract_add_two_mul :
    G.QOn A = (G.contractMap e).QOn (A.erase e) + 2 * G.ROn e (A.erase e) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase e A) (fun S => G.wt phi S)
  rw [Finset.insert_erase hA] at h
  unfold QOn ROn
  rw [h, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  exact wt_phi_pair he fun h => Finset.notMem_erase e A (hT h)

/-- Contraction monotonicity: Q(G)≥Q(G/e). -/
theorem contractMap_QOn_le : (G.contractMap e).QOn (A.erase e) ≤ G.QOn A := by
  rw [QOn_eq_contract_add_two_mul he hA]; omega

/-- Equality holds if one endpoint of e has degree at most two. -/
theorem QOn_eq_contractMap_of_deg_le_two
    (hdeg : G.deg A (G.fst e) ≤ 2 ∨ G.deg A (G.snd e) ≤ 2) :
    G.QOn A = (G.contractMap e).QOn (A.erase e) := by
  rw [QOn_eq_contract_add_two_mul he hA]
  have hR : G.ROn e (A.erase e) = 0 := by
    unfold ROn
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_powerset] at hS
    split_ifs with hc
    · exfalso
      obtain ⟨h1, h2⟩ := hc
      rcases hdeg with hd | hd
      · have := G.deg_mono hS (G.fst e); have := G.deg_erase_fst hA he; omega
      · have := G.deg_mono hS (G.snd e); have := G.deg_erase_snd hA he; omega
    · rfl
  omega

/-- Polynomial deletion–contraction: 𝒬_G=(1−t)𝒬_{G−e}+t𝒬_{G/e}+2tR. -/
theorem QpolyOn_deletion_contraction :
    G.QpolyOn A = (1 - X) * G.QpolyOn (A.erase e) + X * (G.contractMap e).QpolyOn (A.erase e) +
      2 * X * G.RpolyOn e (A.erase e) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase e A)
    (fun S => (X : ℤ[X]) ^ S.card * (G.wt phi S : ℤ[X]))
  rw [Finset.insert_erase hA] at h
  unfold QpolyOn RpolyOn
  rw [h, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hT' : e ∉ T := fun h => Finset.notMem_erase e A (hT h)
  rw [Finset.card_insert_of_notMem hT']
  have key := wt_phi_pair he hT'
  have key' : ((G.wt phi (insert e T) : ℕ) : ℤ[X]) =
      ((G.contractMap e).wt phi T : ℤ[X]) +
        2 * (if 2 ≤ G.deg T (G.fst e) ∧ 2 ≤ G.deg T (G.snd e) then (G.wt phi T : ℤ[X]) else 0) -
        (G.wt phi T : ℤ[X]) := by
    have := congrArg (fun n : ℕ => (n : ℤ[X])) key
    push_cast at this
    linear_combination this
  rw [key']
  split_ifs <;> ring

/-- θ(1,2) is contraction-invariant, the t=1, γ=2 deletion–contraction identity. -/
theorem thetaOn_eq_contractMap : G.thetaOn A = (G.contractMap e).thetaOn (A.erase e) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase e A) (fun S => G.wt f2 S)
  rw [Finset.insert_erase hA] at h
  unfold thetaOn
  rw [h, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  exact wt_f2_pair he fun h => Finset.notMem_erase e A (hT h)

/-- Pure deletion–contraction for θ(t,2): θ_G=(1−t)θ_{G−e}+tθ_{G/e}, at γ=2. -/
theorem thetaPolyOn_deletion_contraction :
    G.thetaPolyOn A =
      (1 - X) * G.thetaPolyOn (A.erase e) + X * (G.contractMap e).thetaPolyOn (A.erase e) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_erase e A)
    (fun S => (X : ℤ[X]) ^ S.card * (G.wt f2 S : ℤ[X]))
  rw [Finset.insert_erase hA] at h
  unfold thetaPolyOn
  rw [h, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powerset] at hT
  have hT' : e ∉ T := fun h => Finset.notMem_erase e A (hT h)
  rw [Finset.card_insert_of_notMem hT']
  have key := wt_f2_pair he hT'
  have key' : ((G.wt f2 (insert e T) : ℕ) : ℤ[X]) =
      ((G.contractMap e).wt f2 T : ℤ[X]) - (G.wt f2 T : ℤ[X]) := by
    have := congrArg (fun n : ℕ => (n : ℤ[X])) key
    push_cast at this
    linear_combination this
  rw [key']
  ring

end Recurrence

section InclusionExclusion

omit [DecidableEq E] [Fintype V] in
/-- Subsets with degree zero are exactly subsets excluding all incident edges. -/
theorem powerset_filter_deg_zero (B : Finset E) (u : V) :
    B.powerset.filter (fun S => G.deg S u = 0) = (B.filter fun f => ¬ G.Incident f u).powerset := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, deg_eq_zero_iff, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ f hf
    exact ⟨h1 hf, h2 f hf⟩
  · intro h
    exact ⟨fun f hf => (h hf).1, fun f hf => (h hf).2⟩

omit [DecidableEq E] [Fintype V] in
theorem powerset_filter_deg_zero_two (B : Finset E) (u v : V) :
    B.powerset.filter (fun S => G.deg S u = 0 ∧ G.deg S v = 0) =
      (B.filter fun f => ¬ G.Incident f u ∧ ¬ G.Incident f v).powerset := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, deg_eq_zero_iff, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ f hf
    exact ⟨h1 hf, h2 f hf, h3 f hf⟩
  · intro h
    exact ⟨fun f hf => (h hf).1, fun f hf => (h hf).2.1, fun f hf => (h hf).2.2⟩

/--
Inclusion-exclusion for indicators: for a,b∈{0}∪[2,∞),
1_{a≥2,b≥2}=1-1_{a=0}-1_{b=0}+1_{a=0,b=0}.
Terms with a=1 or b=1 have F=0 and satisfy the weighted identity as well.
-/
theorem ite_inclusion_exclusion {R : Type*} [CommRing R] (a b : ℕ) (F : R)
    (hF : a = 1 ∨ b = 1 → F = 0) :
    (if 2 ≤ a ∧ 2 ≤ b then F else 0) =
      F - (if a = 0 then F else 0) - (if b = 0 then F else 0) + (if a = 0 ∧ b = 0 then F else 0) := by
  by_cases ha1 : a = 1
  · rw [hF (Or.inl ha1)]; simp
  by_cases hb1 : b = 1
  · rw [hF (Or.inr hb1)]; simp
  split_ifs <;> first | (exfalso; omega) | ring1

variable {G}

/-- Inclusion–exclusion expression R=𝒬_{G−e}−𝒬_{G−u}−𝒬_{G−v}+𝒬_{G−{u,v}}. -/
theorem RpolyOn_eq_inclusion_exclusion (e : E) (B : Finset E) :
    G.RpolyOn e B =
      G.QpolyOn B - G.QpolyOn (B.filter fun f => ¬ G.Incident f (G.fst e)) -
        G.QpolyOn (B.filter fun f => ¬ G.Incident f (G.snd e)) +
        G.QpolyOn (B.filter fun f => ¬ G.Incident f (G.fst e) ∧ ¬ G.Incident f (G.snd e)) := by
  unfold RpolyOn QpolyOn
  rw [← G.powerset_filter_deg_zero B (G.fst e), ← G.powerset_filter_deg_zero B (G.snd e),
    ← G.powerset_filter_deg_zero_two B (G.fst e) (G.snd e), Finset.sum_filter, Finset.sum_filter,
    Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  apply ite_inclusion_exclusion
  rintro (h | h)
  · simp [G.wt_phi_eq_zero_of_deg_eq_one h]
  · simp [G.wt_phi_eq_zero_of_deg_eq_one h]

/-- The coefficients of R(t) are nonnegative. -/
theorem RpolyOn_coeff_nonneg (e : E) (B : Finset E) (k : ℕ) : 0 ≤ (G.RpolyOn e B).coeff k := by
  unfold RpolyOn
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · rw [Polynomial.coeff_X_pow_mul', Polynomial.coeff_natCast_ite]
    split_ifs <;> simp
  · simp

/-- At t=1, R(1)=Q(G-e)-Q(G-u)-Q(G-v)+Q(G-{u,v}) as integers. -/
theorem ROn_eq_inclusion_exclusion (e : E) (B : Finset E) :
    (G.ROn e B : ℤ) =
      (G.QOn B : ℤ) - G.QOn (B.filter fun f => ¬ G.Incident f (G.fst e)) -
        G.QOn (B.filter fun f => ¬ G.Incident f (G.snd e)) +
        G.QOn (B.filter fun f => ¬ G.Incident f (G.fst e) ∧ ¬ G.Incident f (G.snd e)) := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (G.RpolyOn_eq_inclusion_exclusion e B)
  simp only [Polynomial.eval_add, Polynomial.eval_sub, QpolyOn_eval_one] at h
  rw [← h]
  unfold RpolyOn ROn
  simp [Polynomial.eval_finsetSum, apply_ite (Polynomial.eval (1 : ℤ))]

end InclusionExclusion

end Multigraph

end BPFixedPoints
