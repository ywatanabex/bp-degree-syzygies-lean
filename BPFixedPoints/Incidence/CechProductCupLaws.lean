import BPFixedPoints.Incidence.CechCupFormula

/-!
# Algebra laws of the multi-vertex Čech cup product

Pure algebra over a commutative ring: chain-level associativity of the full
Čech chain product `chainCup`, the per-vertex constant section as a two-sided
chain unit, and the resulting associativity and unit laws of `cohomologyCup`.
Graded commutativity holds in cohomology with the sign (−1)^(deg x·deg y),
where the degree of a state is the cohomological degree of its twist vector;
the Alexander–Whitney chain product itself is not commutative.
Twist vectors enter the state module `H R d`, so cohomology statements use an
explicit transport `castH` along equalities of twist vectors.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

section Cast

variable {V : Type*}

/-- Transport of state cohomology along an equality of twist vectors. -/
noncomputable def castH {d d' : V → ℕ} (h : d = d') : H R d ≃ₗ[R] H R d' :=
  h ▸ LinearEquiv.refl R (H R d)

/-- Transport along the reflexive equality is the identity. -/
@[simp] theorem castH_rfl (d : V → ℕ) (x : H R d) : castH R (rfl : d = d) x = x := rfl

/-- Transport only changes the type, not the element. -/
theorem castH_heq {d d' : V → ℕ} (h : d = d') (x : H R d) : HEq (castH R h x) x := by
  subst h
  rfl

/-- Successive transports compose. -/
@[simp] theorem castH_castH {d d' d'' : V → ℕ} (h : d = d') (h' : d' = d'') (x : H R d) :
    castH R h' (castH R h x) = castH R (h.trans h') x := by
  subst h
  subst h'
  rfl

/-- Transport back along the reversed equality. -/
@[simp] theorem castH_symm_apply {d d' : V → ℕ} (h : d = d') (x : H R d') :
    castH R h (castH R h.symm x) = x := by
  subst h
  rfl

/-- Transport along any self-equality is definitionally the identity. -/
theorem castH_self {d : V → ℕ} (h : d = d) (x : H R d) : castH R h x = x := rfl

/-- Transport of a basis vector. -/
theorem castH_single {d d' : V → ℕ} (h : d = d') (κ : HBasis d) (r : R) :
    castH R h (single κ r) = single (cast (congrArg HBasis h) κ) r := by
  subst h
  rfl

/-- Heterogeneous equality of states is transport. -/
theorem eq_castH_of_heq {d d' : V → ℕ} (h : d = d') {x : H R d} {y : H R d'}
    (hxy : HEq x y) : y = castH R h x := by
  subst h
  exact (eq_of_heq hxy).symm

end Cast

section Projection

variable {V : Type*} [Fintype V]

/-- The contraction projection commutes with transport of twist vectors. -/
theorem castH_contraction_p {d d' : V → ℕ} (h : d = d') (c : C R V) :
    castH R h ((contraction R d).p c) = (contraction R d').p c := by
  subst h
  rfl

end Projection

/-! ## Associativity of the one-vertex monomial product -/

/-- Monomial associativity of one-vertex Alexander–Whitney products, including vanishing
terms and twists. -/
theorem lineCupBasis_assoc (e f : ℕ) (a b c : Basis) :
    (lineCupBasis e a b).bind (fun w => lineCupBasis f w c) =
      (lineCupBasis f b c).bind (fun u => lineCupBasis (e + f) a u) := by
  rcases a with a | a | a <;> rcases b with b | b | b <;> rcases c with c | c | c <;>
    simp only [lineCupBasis, Option.bind_some, Option.bind_none, Option.some.injEq,
      Sum.inl.injEq, Sum.inr.injEq] <;>
    push_cast <;> ring

/-- The crossing exponent is additive in the degrees, giving associativity of the Koszul signs. -/
theorem finCupCross_assoc (n : ℕ) (x y z w u : Fin n → Basis)
    (hw : ∀ v, lineDegree (w v) = lineDegree (x v) + lineDegree (y v))
    (hu : ∀ v, lineDegree (u v) = lineDegree (y v) + lineDegree (z v)) :
    finCupCross n w z + finCupCross n x y = finCupCross n x u + finCupCross n y z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih (Fin.tail x) (Fin.tail y) (Fin.tail z) (Fin.tail w) (Fin.tail u)
      (fun v => hw v.succ) (fun v => hu v.succ)
    have hcw : cechDegree (Fin.tail w) = cechDegree (Fin.tail x) + cechDegree (Fin.tail y) := by
      simp only [cechDegree, Fin.tail, hw, Finset.sum_add_distrib]
    simp only [finCupCross, hcw, hu 0]
    nlinarith [h]

/-- The crossing exponent vanishes when every left factor has Čech degree zero. -/
theorem finCupCross_eq_zero_of_left_degree (n : ℕ) (x y : Fin n → Basis)
    (h : ∀ v, lineDegree (x v) = 0) : finCupCross n x y = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc : cechDegree (Fin.tail x) = 0 := by
      simp only [cechDegree, Fin.tail, h, Finset.sum_const_zero]
    rw [finCupCross, hc, zero_mul, zero_add]
    exact ih _ _ (fun v => h v.succ)

/-- The crossing exponent vanishes when every right factor has Čech degree zero. -/
theorem finCupCross_eq_zero_of_right_degree (n : ℕ) (x y : Fin n → Basis)
    (h : ∀ v, lineDegree (y v) = 0) : finCupCross n x y = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finCupCross, h 0, mul_zero, zero_add]
    exact ih _ _ (fun v => h v.succ)

section Vertex

variable {V : Type*} [Fintype V]

/-- Degrees add along a defined monomial product. -/
theorem cupBasis_degree {e : V → ℕ} {x y z : V → Basis} (h : cupBasis e x y = some z) (v : V) :
    lineDegree (z v) = lineDegree (x v) + lineDegree (y v) :=
  lineCupBasis_degree _ ((cupBasis_some_iff _ _ _ _).mp h v)

/-- Pointwise description of a two-step product of monomials. -/
theorem cupBasis_bind_eq_some_iff (e f : V → ℕ) (a b c t : V → Basis) :
    (cupBasis e a b).bind (fun w => cupBasis f w c) = some t ↔
      ∀ v, (lineCupBasis (e v) (a v) (b v)).bind (fun w => lineCupBasis (f v) w (c v)) =
        some (t v) := by
  simp only [Option.bind_eq_some_iff, cupBasis_some_iff]
  constructor
  · rintro ⟨w, hw, ht⟩ v
    exact ⟨w v, hw v, ht v⟩
  · intro h
    choose w hw ht using h
    exact ⟨w, hw, ht⟩

/-- Associativity of the monomial product on an arbitrary finite vertex set. -/
theorem cupBasis_assoc (e f : V → ℕ) (a b c : V → Basis) :
    (cupBasis e a b).bind (fun w => cupBasis f w c) =
      (cupBasis f b c).bind (fun u => cupBasis (e + f) a u) := by
  apply Option.ext
  intro t
  have hr : (cupBasis f b c).bind (fun u => cupBasis (e + f) a u) = some t ↔
      ∀ v, (lineCupBasis (f v) (b v) (c v)).bind (fun u => lineCupBasis (e v + f v) (a v) u) =
        some (t v) := by
    simp only [Option.bind_eq_some_iff, cupBasis_some_iff, Pi.add_apply]
    constructor
    · rintro ⟨u, hu, ht⟩ v
      exact ⟨u v, hu v, ht v⟩
    · intro h
      choose u hu ht using h
      exact ⟨u, hu, ht⟩
  rw [cupBasis_bind_eq_some_iff, hr]
  simp only [lineCupBasis_assoc]

/-- Associativity of the Koszul crossing exponent on an arbitrary finite vertex set. -/
theorem cupCross_assoc (x y z w u : V → Basis)
    (hw : ∀ v, lineDegree (w v) = lineDegree (x v) + lineDegree (y v))
    (hu : ∀ v, lineDegree (u v) = lineDegree (y v) + lineDegree (z v)) :
    cupCross w z + cupCross x y = cupCross x u + cupCross y z :=
  finCupCross_assoc _ _ _ _ _ _ (fun _ => hw _) (fun _ => hu _)

/-- The crossing exponent vanishes against a left factor of degree zero. -/
theorem cupCross_eq_zero_of_left_degree (x y : V → Basis) (h : ∀ v, lineDegree (x v) = 0) :
    cupCross x y = 0 :=
  finCupCross_eq_zero_of_left_degree _ _ _ (fun _ => h _)

/-- The crossing exponent vanishes against a right factor of degree zero. -/
theorem cupCross_eq_zero_of_right_degree (x y : V → Basis) (h : ∀ v, lineDegree (y v) = 0) :
    cupCross x y = 0 :=
  finCupCross_eq_zero_of_right_degree _ _ _ (fun _ => h _)

/-! ## Chain-level associativity -/

/-- Associativity on monomials. -/
theorem chainCup_assoc_single (d e f : V → ℕ) (a b c : V → Basis) (r s t : R) :
    chainCup R (d + e) f (chainCup R d e (single a r) (single b s)) (single c t) =
      chainCup R d (e + f) (single a r) (chainCup R e f (single b s) (single c t)) := by
  have hassoc := cupBasis_assoc e f a b c
  rw [chainCup_single, chainCup_single]
  cases h₁ : cupBasis e a b with
  | none =>
    rw [h₁, Option.bind_none] at hassoc
    cases h₂ : cupBasis f b c with
    | none => simp
    | some u =>
      rw [h₂, Option.bind_some] at hassoc
      simp only [Option.elim, map_zero, LinearMap.zero_apply]
      rw [chainCup_single, ← hassoc]
      rfl
  | some w =>
    rw [h₁, Option.bind_some] at hassoc
    cases h₂ : cupBasis f b c with
    | none =>
      rw [h₂, Option.bind_none] at hassoc
      simp only [Option.elim, map_zero]
      rw [chainCup_single, hassoc]
      rfl
    | some u =>
      rw [h₂, Option.bind_some] at hassoc
      simp only [Option.elim]
      rw [chainCup_single, chainCup_single, hassoc]
      cases h₃ : cupBasis (e + f) a u with
      | none => rfl
      | some z =>
        simp only [Option.elim]
        congr 1
        have hc := cupCross_assoc a b c w u (cupBasis_degree h₁) (cupBasis_degree h₂)
        calc (-1 : R) ^ cupCross w c * ((-1) ^ cupCross a b * (r * s) * t)
            = (-1) ^ (cupCross w c + cupCross a b) * (r * s * t) := by ring
          _ = (-1) ^ (cupCross a u + cupCross b c) * (r * s * t) := by rw [hc]
          _ = (-1) ^ cupCross a u * (r * ((-1) ^ cupCross b c * (s * t))) := by ring

/-- Chain-level associativity of the full multi-vertex Čech product, with twists added. -/
theorem chainCup_assoc (d e f : V → ℕ) (x y z : C R V) :
    chainCup R (d + e) f (chainCup R d e x y) z =
      chainCup R d (e + f) x (chainCup R e f y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | single b s =>
      induction z using Finsupp.induction_linear with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | single c t => exact chainCup_assoc_single R d e f a b c r s t

/-! ## The chain unit -/

/-- One-vertex constant section in monomials: `true` is the left chart, `false` the right chart. -/
def unitBasis : Bool → Basis
  | true => Sum.inl 0
  | false => Sum.inr (Sum.inl 0)

/-- Both chart constants have Čech degree zero. -/
@[simp] theorem lineDegree_unitBasis (s : Bool) : lineDegree (unitBasis s) = 0 := by
  cases s <;> rfl

/-- The chart a left unit factor must use against a given monomial. -/
def unitLeftChoice : Basis → Bool
  | Sum.inr (Sum.inl _) => false
  | _ => true

/-- The chart a right unit factor must use against a given monomial. -/
def unitRightChoice : Basis → Bool
  | Sum.inl _ => true
  | _ => false

/-- A left chart constant multiplies a monomial exactly when it uses the matching chart. -/
theorem lineCupBasis_unit_left (e : ℕ) (s : Bool) (y : Basis) :
    lineCupBasis e (unitBasis s) y = if s = unitLeftChoice y then some y else none := by
  rcases y with y | y | y <;> cases s <;> simp [lineCupBasis, unitBasis, unitLeftChoice]

/-- A right chart constant of twist zero multiplies a monomial exactly when it uses the
matching chart. -/
theorem lineCupBasis_unit_right (x : Basis) (s : Bool) :
    lineCupBasis 0 x (unitBasis s) = if s = unitRightChoice x then some x else none := by
  rcases x with x | x | x <;> cases s <;> simp [lineCupBasis, unitBasis, unitRightChoice]

/-- Product of the one-vertex constant sections: the sum of all chart choices. -/
noncomputable def chainUnit : C R V := by
  classical
  exact ∑ s : V → Bool, single (fun v => unitBasis (s v)) 1

/-- Exactly one chart choice of the left unit multiplies a given monomial, returning it. -/
theorem cupBasis_unit_left (e : V → ℕ) (s : V → Bool) (y : V → Basis) :
    cupBasis e (fun v => unitBasis (s v)) y =
      if s = fun v => unitLeftChoice (y v) then some y else none := by
  split_ifs with hs
  · apply (cupBasis_some_iff _ _ _ _).mpr
    intro v
    rw [lineCupBasis_unit_left, ite_eq_left (congrFun hs v)]
  · cases h : cupBasis e (fun v => unitBasis (s v)) y with
    | none => rfl
    | some z =>
      exfalso
      apply hs
      funext v
      have hv := (cupBasis_some_iff _ _ _ _).mp h v
      rw [lineCupBasis_unit_left] at hv
      by_contra hne
      rw [ite_eq_right hne] at hv
      cases hv

/-- Exactly one chart choice of the right unit multiplies a given monomial, returning it. -/
theorem cupBasis_unit_right (x : V → Basis) (s : V → Bool) :
    cupBasis 0 x (fun v => unitBasis (s v)) =
      if s = fun v => unitRightChoice (x v) then some x else none := by
  split_ifs with hs
  · apply (cupBasis_some_iff _ _ _ _).mpr
    intro v
    rw [Pi.zero_apply, lineCupBasis_unit_right, ite_eq_left (congrFun hs v)]
  · cases h : cupBasis 0 x (fun v => unitBasis (s v)) with
    | none => rfl
    | some z =>
      exfalso
      apply hs
      funext v
      have hv := (cupBasis_some_iff _ _ _ _).mp h v
      rw [Pi.zero_apply, lineCupBasis_unit_right] at hv
      by_contra hne
      rw [ite_eq_right hne] at hv
      cases hv

/-- Left unit law at chain level, for every pair of twists. -/
theorem chainCup_unit_left (d e : V → ℕ) (x : C R V) : chainCup R d e (chainUnit R) x = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single y t =>
    unfold chainUnit
    rw [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_eq_single (fun v => unitLeftChoice (y v))]
    · rw [chainCup_single, cupBasis_unit_left, ite_eq_left rfl,
        cupCross_eq_zero_of_left_degree _ _ (fun v => lineDegree_unitBasis _)]
      simp
    · intro s _ hs
      rw [chainCup_single, cupBasis_unit_left, ite_eq_right hs]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- Right unit law at chain level; the unit carries twist zero. -/
theorem chainCup_unit_right (d : V → ℕ) (x : C R V) : chainCup R d 0 x (chainUnit R) = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single y t =>
    unfold chainUnit
    rw [map_sum]
    rw [Finset.sum_eq_single (fun v => unitRightChoice (y v))]
    · rw [chainCup_single, cupBasis_unit_right, ite_eq_left rfl,
        cupCross_eq_zero_of_right_degree _ _ (fun v => lineDegree_unitBasis _)]
      simp
    · intro s _ hs
      rw [chainCup_single, cupBasis_unit_right, ite_eq_right hs]
      rfl
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The chain unit is fixed by the parity operator. -/
theorem contraction_sign_chainUnit (d : V → ℕ) :
    (contraction R d).sign (chainUnit R) = chainUnit R := by
  classical
  unfold chainUnit
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [contraction_sign_single]
  have h0 : cechDegree (fun v => unitBasis (s v)) = 0 := by
    simp [cechDegree]
  rw [h0, pow_zero, one_smul]

/-- The chain unit is a cocycle for the twist-zero differential. -/
theorem contraction_d_chainUnit : (contraction R (0 : V → ℕ)).d (chainUnit R) = 0 := by
  have h := chainCup_leibniz R (0 : V → ℕ) 0 (chainUnit R) (chainUnit R)
  rw [chainCup_unit_left, add_zero, chainCup_unit_right, contraction_sign_chainUnit,
    chainCup_unit_left] at h
  simpa using h

/-! ## Cohomology-level laws -/

/-- Cohomology class of the chain unit, in the state module of twist zero. -/
noncomputable def cohomologyUnit : H R (0 : V → ℕ) := (contraction R 0).p (chainUnit R)

/-- The chosen inclusion of a state is a cocycle. -/
theorem contraction_d_i (d : V → ℕ) (x : H R d) :
    (contraction R d).d ((contraction R d).i x) = 0 :=
  LinearMap.congr_fun (contraction R d).d_i x

/-- Projection of the chosen inclusion returns the state. -/
theorem contraction_p_i (d : V → ℕ) (x : H R d) :
    (contraction R d).p ((contraction R d).i x) = x :=
  LinearMap.congr_fun (contraction R d).p_i x

/-- Left unit law in cohomology, transported along `0 + d = d`. -/
theorem cohomologyCup_unit_left (d : V → ℕ) (x : H R d) :
    castH R (zero_add d) (cohomologyCup R 0 d (cohomologyUnit R) x) = x := by
  have h := cohomologyCup_chain_projection R 0 d (contraction_d_chainUnit R)
    (contraction_d_i R d x)
  rw [contraction_p_i, chainCup_unit_left] at h
  rw [cohomologyUnit, h, castH_contraction_p, contraction_p_i]

/-- Left unit law in cohomology as a heterogeneous equality. -/
theorem cohomologyCup_unit_left_heq (d : V → ℕ) (x : H R d) :
    HEq (cohomologyCup R 0 d (cohomologyUnit R) x) x := by
  conv_rhs => rw [← cohomologyCup_unit_left R d x]
  exact (castH_heq R _ _).symm

/-- Right unit law in cohomology; `d + 0` is definitionally `d`. -/
theorem cohomologyCup_unit_right (d : V → ℕ) (x : H R d) :
    cohomologyCup R d 0 x (cohomologyUnit R) = x := by
  have h := cohomologyCup_chain_projection R d 0 (contraction_d_i R d x)
    (contraction_d_chainUnit R)
  rw [contraction_p_i, chainCup_unit_right] at h
  rw [cohomologyUnit, h]
  exact contraction_p_i R d x

/-- Associativity in cohomology for arbitrary cocycle representatives: the left bracketing. -/
theorem cohomologyCup_triple_projection_left (d e f : V → ℕ) {x y z : C R V}
    (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0)
    (hz : (contraction R f).d z = 0) :
    cohomologyCup R (d + e) f
        (cohomologyCup R d e ((contraction R d).p x) ((contraction R e).p y))
        ((contraction R f).p z) =
      (contraction R (d + e + f)).p (chainCup R (d + e) f (chainCup R d e x y) z) := by
  rw [cohomologyCup_chain_projection R d e hx hy,
    cohomologyCup_chain_projection R (d + e) f (chainCup_cycles R d e hx hy) hz]

/-- Associativity in cohomology for arbitrary cocycle representatives: the right bracketing. -/
theorem cohomologyCup_triple_projection_right (d e f : V → ℕ) {x y z : C R V}
    (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0)
    (hz : (contraction R f).d z = 0) :
    cohomologyCup R d (e + f) ((contraction R d).p x)
        (cohomologyCup R e f ((contraction R e).p y) ((contraction R f).p z)) =
      (contraction R (d + (e + f))).p (chainCup R d (e + f) x (chainCup R e f y z)) := by
  rw [cohomologyCup_chain_projection R e f hy hz,
    cohomologyCup_chain_projection R d (e + f) hx (chainCup_cycles R e f hy hz)]

/-- Associativity of the multi-vertex cohomology cup product, transported along `add_assoc`. -/
theorem cohomologyCup_assoc (d e f : V → ℕ) (x : H R d) (y : H R e) (z : H R f) :
    castH R (add_assoc d e f) (cohomologyCup R (d + e) f (cohomologyCup R d e x y) z) =
      cohomologyCup R d (e + f) x (cohomologyCup R e f y z) := by
  have hl := cohomologyCup_triple_projection_left R d e f
    (contraction_d_i R d x) (contraction_d_i R e y) (contraction_d_i R f z)
  have hr := cohomologyCup_triple_projection_right R d e f
    (contraction_d_i R d x) (contraction_d_i R e y) (contraction_d_i R f z)
  simp only [contraction_p_i] at hl hr
  rw [hl, hr, chainCup_assoc, castH_contraction_p]

/-- Associativity of the multi-vertex cohomology cup product as a heterogeneous equality. -/
theorem cohomologyCup_assoc_heq (d e f : V → ℕ) (x : H R d) (y : H R e) (z : H R f) :
    HEq (cohomologyCup R (d + e) f (cohomologyCup R d e x y) z)
      (cohomologyCup R d (e + f) x (cohomologyCup R e f y z)) := by
  rw [← cohomologyCup_assoc]
  exact (castH_heq R _ _).symm

end Vertex

end BPFixedPoints.CechProduct

/-! ## Commutativity of the one-vertex cohomology product -/

namespace BPFixedPoints.CechLine

open CechProduct

variable {R : Type*} [CommRing R]

/-- A twist-zero cocycle without overlap term commutes with every chain. -/
theorem cup_comm_of_zero_cocycle (d e : ℕ) {x : CechProduct.LineC R} (y : CechProduct.LineC R)
    (hx2 : x.2 = 0) (hx : CechProduct.lineD R 0 x = 0) :
    cup e 0 y x = cup d e x y := by
  have hd : rightRestriction R 0 x.1.2 = leftRestriction R x.1.1 := by
    have h := congrArg Prod.snd hx
    simp only [CechProduct.lineD_apply, differential, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] at h
    exact sub_eq_zero.mp h
  simp only [cup, hx2, convolution_zero_left, convolution_zero_right, zero_add, add_zero, hd]
  rw [convolution_comm y.1.1, convolution_comm y.1.2, convolution_comm y.2]

/-- The degree-zero representative of a twist-zero class has no overlap term. -/
theorem lineI_zero_snd (x : CechProduct.LineH R 0) : (CechProduct.lineI R 0 x).2 = 0 := by
  have hx : x.2 = 0 := by ext i; exact Fin.elim0 i
  simp [hx]

/-- One-vertex cohomology products commute up to the identification of `e + d` with `d + e`. -/
theorem cohomologyCup_comm (d e : ℕ) (x : CechProduct.LineH R d) (y : CechProduct.LineH R e) :
    HEq (cohomologyCup e d y x) (cohomologyCup d e x y) := by
  by_cases hd : d = 0
  · subst d
    unfold cohomologyCup
    rw [cup_comm_of_zero_cocycle 0 e _ (lineI_zero_snd x) (lineD_lineI 0 x)]
    exact lineP_heq (Nat.add_comm e 0) _
  · by_cases he : e = 0
    · subst e
      unfold cohomologyCup
      rw [← cup_comm_of_zero_cocycle 0 d _ (lineI_zero_snd y) (lineD_lineI 0 y)]
      exact lineP_heq (Nat.add_comm 0 d) _
    · rw [cohomologyCup_eq_zero_of_pos e d (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hd),
        cohomologyCup_eq_zero_of_pos d e (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero he)]
      have h0 : ∀ m, (0 : CechProduct.LineH R m) = CechProduct.lineP R m 0 := fun m =>
        (map_zero (CechProduct.lineP R m)).symm
      rw [h0, h0]
      exact lineP_heq (Nat.add_comm e d) _

end BPFixedPoints.CechLine

/-! ## Graded commutativity of the multi-vertex cohomology product -/

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

/-- Transport of one-vertex state coordinates along an equality of twists. -/
noncomputable def lineCastH {d d' : ℕ} (h : d = d') :
    (Fin (phi d) →₀ R) ≃ₗ[R] (Fin (phi d') →₀ R) :=
  h ▸ LinearEquiv.refl R _

/-- Heterogeneously equal one-vertex states have transported coordinates. -/
theorem lineHBasisEquiv_heq {m m' : ℕ} (h : m = m') {z : LineH R m} {z' : LineH R m'}
    (hz : HEq z z') : lineHBasisEquiv R m' z' = lineCastH R h (lineHBasisEquiv R m z) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

/-- One-vertex commutativity in free state coordinates. -/
theorem lineCyclePairing_cup_comm (d e : ℕ) (x : Fin (phi d) →₀ R) (y : Fin (phi e) →₀ R) :
    (lineCyclePairing R e d).cup y x =
      lineCastH R (Nat.add_comm d e) ((lineCyclePairing R d e).cup x y) := by
  rw [lineCyclePairing, lineCyclePairing, CyclePairing.congr_cup_apply,
    CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup, CechLine.cyclePairing_cup]
  exact lineHBasisEquiv_heq R _ (CechLine.cohomologyCup_comm _ _ _ _).symm

/-- Transport commutes with splitting off the first vertex. -/
theorem castH_consEquiv {n : ℕ} {D D' : Fin (n + 1) → ℕ} (h : D = D')
    (a : Fin (phi (D 0)) →₀ R) (b : H R (Fin.tail D)) :
    castH R h (consEquiv R (fun i => Fin (phi (D i))) (a ⊗ₜ[R] b)) =
      consEquiv R (fun i => Fin (phi (D' i)))
        (lineCastH R (congrFun h 0) a ⊗ₜ[R] castH R (congrArg Fin.tail h) b) := by
  subst h
  rfl

/-- An even correction does not change a power of `-1`. -/
theorem neg_one_pow_add_two_mul (a b : ℕ) : (-1 : R) ^ (a + 2 * b) = (-1) ^ a := by
  rw [pow_add, pow_mul]
  simp

/-- Unless both twists are positive, at most one local factor has degree one. -/
theorem lineCohomologyDegree_mul_eq_zero {d e : ℕ} (h : ¬ (0 < d ∧ 0 < e)) :
    lineCohomologyDegree d * lineCohomologyDegree e = 0 := by
  unfold lineCohomologyDegree
  split_ifs <;> omega

/-- On the empty vertex set the product of basis vectors multiplies coefficients. -/
theorem emptyCohomologyCup_single (d e : Fin 0 → ℕ) (a : HBasis d) (b : HBasis e) (r s : R) :
    emptyCohomologyCup R d e (single a r) (single b s) =
      single (fun i => Fin.elim0 i) (r * s) := by
  simp [emptyCohomologyCup]

/-- Specialization of `castH_consEquiv` to the commutation of twist vectors. -/
theorem castH_add_comm_consEquiv {n : ℕ} (d e : Fin (n + 1) → ℕ)
    (a : Fin (phi (d 0 + e 0)) →₀ R) (b : H R (Fin.tail d + Fin.tail e)) :
    castH R (add_comm d e) (consEquiv R (fun i => Fin (phi ((d + e) i))) (a ⊗ₜ[R] b)) =
      consEquiv R (fun i => Fin (phi ((e + d) i)))
        (lineCastH R (Nat.add_comm (d 0) (e 0)) a ⊗ₜ[R]
          castH R (add_comm (Fin.tail d) (Fin.tail e)) b) :=
  castH_consEquiv R (add_comm d e) a b

/-- Inductive step of graded commutativity on pure tensors. -/
theorem finCyclePairing_cup_comm_cons {n : ℕ}
    (ih : ∀ (d e : Fin n → ℕ) (x : H R d) (y : H R e),
      (finCyclePairing R n e d).cup y x =
        (-1 : R) ^ (cohomologyDegree d * cohomologyDegree e) •
          castH R (add_comm d e) ((finCyclePairing R n d e).cup x y))
    (d e : Fin (n + 1) → ℕ) (x0 : Fin (phi (d 0)) →₀ R) (x' : H R (Fin.tail d))
    (y0 : Fin (phi (e 0)) →₀ R) (y' : H R (Fin.tail e)) :
    (finCyclePairing R (n + 1) e d).cup (consEquiv R _ (y0 ⊗ₜ[R] y'))
        (consEquiv R _ (x0 ⊗ₜ[R] x')) =
      (-1 : R) ^ (cohomologyDegree d * cohomologyDegree e) •
        castH R (add_comm d e) ((finCyclePairing R (n + 1) d e).cup
          (consEquiv R _ (x0 ⊗ₜ[R] x')) (consEquiv R _ (y0 ⊗ₜ[R] y'))) := by
  rw [finCyclePairing_cup_cons R e d y0 y' x0 x', finCyclePairing_cup_cons R d e x0 x' y0 y']
  rw [lineCyclePairing_cup_comm R (d 0) (e 0) x0 y0, ih (Fin.tail d) (Fin.tail e) x' y']
  rw [map_smul, map_smul, map_smul, castH_add_comm_consEquiv, TensorProduct.tmul_smul, map_smul,
    smul_smul, smul_smul]
  by_cases hpos : 0 < d 0 ∧ 0 < e 0
  · rw [lineCyclePairing_cup_eq_zero R (d 0) (e 0) hpos.1 hpos.2]
    simp only [LinearMap.zero_apply, map_zero, TensorProduct.zero_tmul, smul_zero]
  · have hexp : cohomologyDegree d * cohomologyDegree e +
        cohomologyDegree (Fin.tail d) * lineCohomologyDegree (e 0) =
        (cohomologyDegree (Fin.tail e) * lineCohomologyDegree (d 0) +
          cohomologyDegree (Fin.tail d) * cohomologyDegree (Fin.tail e)) +
        2 * (cohomologyDegree (Fin.tail d) * lineCohomologyDegree (e 0)) := by
      have h0 := lineCohomologyDegree_mul_eq_zero hpos
      rw [cohomologyDegree_cons d, cohomologyDegree_cons e]
      nlinarith [h0]
    rw [← pow_add, ← pow_add, hexp, neg_one_pow_add_two_mul]

/-- Graded commutativity for the enumerated vertex set. -/
theorem finCyclePairing_cup_comm (n : ℕ) (d e : Fin n → ℕ) (x : H R d) (y : H R e) :
    (finCyclePairing R n e d).cup y x =
      (-1 : R) ^ (cohomologyDegree d * cohomologyDegree e) •
        castH R (add_comm d e) ((finCyclePairing R n d e).cup x y) := by
  induction n with
  | zero =>
    have hcd : cohomologyDegree d = 0 := by simp [cohomologyDegree]
    rw [hcd, zero_mul, pow_zero, one_smul]
    have key : ∀ (d e : Fin 0 → ℕ) (x : H R d) (y : H R e),
        (finCyclePairing R 0 d e).cup x y = emptyCohomologyCup R d e x y := fun d e x y =>
      LinearMap.congr_fun (empty R (d + e)).p_i _
    rw [key, key]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | single a r =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
      | single b s =>
        rw [emptyCohomologyCup_single, emptyCohomologyCup_single, castH_single, mul_comm s r]
        congr 1
        funext i
        exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨x, rfl⟩ := (consEquiv R (fun i => Fin (phi (d i)))).surjective x
    obtain ⟨y, rfl⟩ := (consEquiv R (fun i => Fin (phi (e i)))).surjective y
    induction x using TensorProduct.inductionOn with
    | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, smul_add]
    | tmul x0 x' =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, smul_add]
      | tmul y0 y' => exact finCyclePairing_cup_comm_cons R ih d e x0 x' y0 y'

/-- Transport commutes with re-indexing the vertex set. -/
theorem castH_mapDomain_piCongrLeft {V W : Type*} (σ : W ≃ V) {D D' : V → ℕ} (h : D = D')
    (z : H R (fun i => D (σ i))) :
    castH R h (Finsupp.mapDomain.linearEquiv R R
        (Equiv.piCongrLeft (fun v => Fin (phi (D v))) σ) z) =
      Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun v => Fin (phi (D' v))) σ)
        (castH R (congrArg (fun D : V → ℕ => fun i => D (σ i)) h) z) := by
  subst h
  rfl

section VertexComm

variable {V : Type*} [Fintype V]

/-- The cohomological degree is invariant under re-indexing the vertex set. -/
theorem cohomologyDegree_comp_equiv {W : Type*} [Fintype W] (σ : W ≃ V) (d : V → ℕ) :
    cohomologyDegree (fun i => d (σ i)) = cohomologyDegree d :=
  σ.sum_comp (fun v => lineCohomologyDegree (d v))

/-- Graded commutativity of the multi-vertex cohomology cup product, transported along
`add_comm`; the sign is (−1)^(deg x·deg y) with deg the cohomological degree of the twist. -/
theorem cohomologyCup_comm (d e : V → ℕ) (x : H R d) (y : H R e) :
    cohomologyCup R e d y x =
      (-1 : R) ^ (cohomologyDegree d * cohomologyDegree e) •
        castH R (add_comm d e) (cohomologyCup R d e x y) := by
  unfold cohomologyCup cyclePairing
  rw [CyclePairing.congr_cup_apply, CyclePairing.congr_cup_apply, finCyclePairing_cup_comm,
    map_smul, cohomologyDegree_comp_equiv, cohomologyDegree_comp_equiv]
  congr 1
  exact (castH_mapDomain_piCongrLeft R _ (add_comm d e) _).symm

/-- Graded commutativity with the transport on the other side. -/
theorem castH_cohomologyCup_comm (d e : V → ℕ) (x : H R d) (y : H R e) :
    castH R (add_comm e d) (cohomologyCup R e d y x) =
      (-1 : R) ^ (cohomologyDegree d * cohomologyDegree e) • cohomologyCup R d e x y := by
  rw [cohomologyCup_comm, map_smul, castH_castH, castH_self]

end VertexComm

end BPFixedPoints.CechProduct
