import BPFixedPoints.Incidence.VertexMapPullbackSigns
import BPFixedPoints.Incidence.CechProductCupLaws

/-!
# Pullback of product Čech chains along an injective vertex function

Let `j : V → W` be an injective map of finite vertex sets. Pulling back along the coordinate
projection `(ℙ¹)^W → (ℙ¹)^V`, `(x_w) ↦ (x_{j v})`, sends a product Čech chain on `(ℙ¹)^V` to the
product of the same chain on the image coordinates with the constant section `1` on every other
coordinate. In the monomial basis of `CechProduct` the constant section of one factor is the sum
of its two chart constants `unitBasis true` and `unitBasis false`, so a monomial `b : V → Basis`
goes to the sum, over all chart choices `s` off the image (`unitChoices`), of the monomials
`extendMonomial j b s` which are `b` on the image and `unitBasis (s w)` elsewhere. The tensor
factors are enumerated by `Fintype.equivFin V` and `Fintype.equivFin W`, so the degree-one factors
are reordered, with the Koszul sign `vertexMapSign R j (overlapVertices b)`. This is
`cechExtend R j`.

For twists `d : V → ℕ` and `d' : W → ℕ` with `d' ∘ j = d` and `d' = 0` off the image we prove:
* it commutes with the product Čech differentials (`cechExtend_d`): at an image vertex this is the
  insertion identity `vertexMapSign_insert`; at a vertex off the image the two chart constants
  have opposite boundary coefficients and cancel (the constant section is a cocycle);
* it commutes with the Čech parities (`cechExtend_sign`) and with the monomial section actions
  extended by zero (`cechExtend_multiply`), and preserves Čech degrees
  (`cechExtend_mem_supported`);
* its coefficients (`cechExtend_apply_of_unitOff`, `cechExtend_apply_of_not_unitOff`), and the
  state formula `(contraction R d').p (cechExtend R j ((contraction R d).i x)) κ' =
  vertexMapSign R j (twistSupport d) * x (hPull hd κ')` (`contraction_p_cechExtend_i`), where
  `hPull` restricts a state index of twist `d'` to the image.

Not covered: vertex functions that identify vertices (the pullback along a diagonal needs the Čech
cup product of the identified factors), and compatibility with the cup product of chains.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

/-! ## Monomials -/

section Monomials

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {j : V → W}

/-- The two chart constants are different monomials. -/
theorem unitBasis_injective : Function.Injective unitBasis := by
  intro s t h
  cases s <;> cases t <;> first | rfl | exact absurd h (by simp [unitBasis])

variable (j) in
/-- The extension of a product monomial along a vertex function: the monomial `b` at the image
vertices and the chart constant `unitBasis (s w)` at every other vertex `w`. -/
noncomputable def extendMonomial (b : V → Basis) (s : W → Bool) : W → Basis :=
  Function.extend j b fun w => unitBasis (s w)

variable (j) in
/-- The chart choices for the vertices off the image of `j`: functions `W → Bool` which are `true`
on the image (where the choice is irrelevant). -/
noncomputable def unitChoices : Finset (W → Bool) :=
  Finset.univ.filter fun s => ∀ v, s (j v) = true

theorem mem_unitChoices {s : W → Bool} : s ∈ unitChoices j ↔ ∀ v, s (j v) = true := by
  simp [unitChoices]

theorem extendMonomial_apply_image (hj : Function.Injective j) (b : V → Basis) (s : W → Bool)
    (v : V) : extendMonomial j b s (j v) = b v :=
  hj.extend_apply _ _ v

theorem extendMonomial_apply_of_not_mem (b : V → Basis) (s : W → Bool) {w : W}
    (hw : ∀ v, j v ≠ w) : extendMonomial j b s w = unitBasis (s w) :=
  Function.extend_apply' _ _ _ fun ⟨v, hv⟩ => hw v hv

/-- A sum over `W` of a function vanishing off the image of `j` is the sum over `V`. -/
theorem sum_eq_sum_image {M : Type*} [AddCommMonoid M] (hj : Function.Injective j) (g : W → M)
    (hg : ∀ w, (∀ v, j v ≠ w) → g w = 0) : ∑ w, g w = ∑ v, g (j v) :=
  (Fintype.sum_of_injective j hj (fun v => g (j v)) g
    (fun w hw => hg w fun v hv => hw ⟨v, hv⟩) fun _ => rfl).symm

/-- Extension preserves Čech degrees. -/
theorem cechDegree_extendMonomial (hj : Function.Injective j) (b : V → Basis) (s : W → Bool) :
    cechDegree (extendMonomial j b s) = cechDegree b := by
  unfold cechDegree
  rw [sum_eq_sum_image hj]
  · simp only [extendMonomial_apply_image hj]
  · intro w hw
    rw [extendMonomial_apply_of_not_mem b s hw, lineDegree_unitBasis]

/-- Extension commutes with updating a value at a vertex of the source. -/
theorem extendMonomial_update (hj : Function.Injective j) (b : V → Basis) (s : W → Bool) (v : V)
    (x : Basis) :
    extendMonomial j (Function.update b v x) s =
      Function.update (extendMonomial j b s) (j v) x := by
  funext w
  by_cases hw : ∃ u, j u = w
  · obtain ⟨u, rfl⟩ := hw
    rw [extendMonomial_apply_image hj]
    by_cases huv : u = v
    · subst huv
      simp
    · rw [Function.update_of_ne huv, Function.update_of_ne (hj.ne huv),
        extendMonomial_apply_image hj]
  · push Not at hw
    rw [extendMonomial_apply_of_not_mem _ _ hw, Function.update_of_ne (fun h => hw v h.symm),
      extendMonomial_apply_of_not_mem _ _ hw]

/-- Changing the chart choice at a vertex off the image changes the extension there. -/
theorem extendMonomial_update_choice (hj : Function.Injective j) (b : V → Basis) (s : W → Bool)
    {w : W} (hw : ∀ v, j v ≠ w) (t : Bool) :
    extendMonomial j b (Function.update s w t) =
      Function.update (extendMonomial j b s) w (unitBasis t) := by
  funext w'
  by_cases hw' : w' = w
  · subst hw'
    rw [Function.update_self, extendMonomial_apply_of_not_mem _ _ hw, Function.update_self]
  · rw [Function.update_of_ne hw']
    by_cases h : ∃ u, j u = w'
    · obtain ⟨u, rfl⟩ := h
      rw [extendMonomial_apply_image hj, extendMonomial_apply_image hj]
    · push Not at h
      rw [extendMonomial_apply_of_not_mem _ _ h, extendMonomial_apply_of_not_mem _ _ h,
        Function.update_of_ne hw']

/-- The prefix degree of the product Čech differential, as a count of earlier overlap vertices. -/
theorem boundaryPrefix_eq_sum_overlap (b : V → Basis) (v : V) :
    boundaryPrefix b v = ∑ u ∈ overlapVertices b,
      if Fintype.equivFin V u < Fintype.equivFin V v then 1 else 0 := by
  rw [sum_overlapVertices, boundaryPrefix]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> simp

/-- The prefix degree of an extended monomial at an image vertex counts the overlap vertices of the
original monomial whose images come earlier. -/
theorem boundaryPrefix_extendMonomial (hj : Function.Injective j) (b : V → Basis) (s : W → Bool)
    (v : V) :
    boundaryPrefix (extendMonomial j b s) (j v) = ∑ u ∈ overlapVertices b,
      if Fintype.equivFin W (j u) < Fintype.equivFin W (j v) then 1 else 0 := by
  rw [sum_overlapVertices, boundaryPrefix, sum_eq_sum_image hj]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [extendMonomial_apply_image hj]
    split_ifs <;> simp
  · intro w hw
    rw [extendMonomial_apply_of_not_mem _ _ hw, lineDegree_unitBasis]
    simp

/-- The prefix degree at a vertex does not see the value at that vertex. -/
theorem boundaryPrefix_update_self (b : W → Basis) (w : W) (x : Basis) :
    boundaryPrefix (Function.update b w x) w = boundaryPrefix b w := by
  unfold boundaryPrefix
  refine Finset.sum_congr rfl fun w' _ => ?_
  by_cases h : Fintype.equivFin W w' < Fintype.equivFin W w
  · have hne : w' ≠ w := fun h' => (lt_irrefl _) (h' ▸ h)
    rw [ite_eq_left h, ite_eq_left h, Function.update_of_ne hne]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Every chart constant has boundary monomial the constant overlap monomial for twist zero. -/
theorem boundaryStep_unitBasis (s : Bool) :
    boundaryStep 0 (unitBasis s) = Sum.inr (Sum.inr 0) := by
  cases s <;> rfl

/-- The boundary coefficients of the two chart constants are opposite. -/
theorem boundaryCoefficient_unitBasis_not (R : Type*) [CommRing R] (s : Bool) :
    boundaryCoefficient R (unitBasis (!s)) = -boundaryCoefficient R (unitBasis s) := by
  cases s <;> simp [unitBasis, boundaryCoefficient]

/-- A monomial is a chart constant at every vertex off the image of `j`. -/
def UnitOff (j : V → W) (b : W → Basis) : Prop :=
  ∀ w, (∀ v, j v ≠ w) → ∃ t, b w = unitBasis t

theorem unitOff_extendMonomial (b : V → Basis) (s : W → Bool) :
    UnitOff j (extendMonomial j b s) :=
  fun w hw => ⟨s w, extendMonomial_apply_of_not_mem b s hw⟩

/-- A monomial which is a chart constant off the image is the extension of its restriction. -/
theorem exists_extendMonomial_eq (hj : Function.Injective j) {b : W → Basis} (hb : UnitOff j b) :
    ∃ s ∈ unitChoices j, extendMonomial j (fun v => b (j v)) s = b := by
  classical
  refine ⟨fun w => if ∃ v, j v = w then true else decide (b w = unitBasis true), ?_, ?_⟩
  · rw [mem_unitChoices]
    intro v
    simp
  · funext w
    by_cases hw : ∃ v, j v = w
    · obtain ⟨v, rfl⟩ := hw
      rw [extendMonomial_apply_image hj]
    · push Not at hw
      rw [extendMonomial_apply_of_not_mem _ _ hw]
      obtain ⟨t, ht⟩ := hb w hw
      have hn : ¬ ∃ v, j v = w := fun ⟨v, hv⟩ => hw v hv
      simp only [hn, ite_false, ht]
      cases t <;> simp [unitBasis]

/-- Extensions with different chart choices are different. -/
theorem extendMonomial_injective (b b' : V → Basis) {s s' : W → Bool} (hs : s ∈ unitChoices j)
    (hs' : s' ∈ unitChoices j) (h : extendMonomial j b s = extendMonomial j b' s') : s = s' := by
  funext w
  by_cases hw : ∃ v, j v = w
  · obtain ⟨v, rfl⟩ := hw
    rw [mem_unitChoices.1 hs v, mem_unitChoices.1 hs' v]
  · push Not at hw
    have h' := congrFun h w
    rw [extendMonomial_apply_of_not_mem _ _ hw, extendMonomial_apply_of_not_mem _ _ hw] at h'
    exact unitBasis_injective h'

end Monomials

/-! ## The extension of product Čech chains -/

section Chains

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (R : Type) [CommRing R] (j : V → W)

/-- **Pullback of product Čech chains along an injective vertex function**: a monomial `b` goes
to the Koszul sign of its overlap vertices times the sum of its extensions by chart constants. -/
noncomputable def cechExtend : C R V →ₗ[R] C R W :=
  Finsupp.lsum R fun b => vertexMapSign R j (overlapVertices b) •
    ∑ s ∈ unitChoices j, Finsupp.lsingle (extendMonomial j b s)

theorem cechExtend_single (b : V → Basis) (r : R) :
    cechExtend R j (single b r) = ∑ s ∈ unitChoices j,
      single (extendMonomial j b s) (vertexMapSign R j (overlapVertices b) * r) := by
  simp [cechExtend, Finsupp.smul_single, smul_eq_mul, Finset.smul_sum]

variable {j}

/-- **Coefficients** of an extended chain at a monomial which is a chart constant off the image:
the Koszul sign times the coefficient of the restricted monomial. -/
theorem cechExtend_apply_of_unitOff (hj : Function.Injective j) (c : C R V) {b : W → Basis}
    (hb : UnitOff j b) :
    cechExtend R j c b =
      vertexMapSign R j (overlapVertices fun v => b (j v)) * c (fun v => b (j v)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single a r =>
    rw [cechExtend_single, Finset.sum_apply']
    by_cases ha : a = fun v => b (j v)
    · subst ha
      obtain ⟨s₀, hs₀, he⟩ := exists_extendMonomial_eq hj hb
      rw [Finset.sum_eq_single s₀, he, single_eq_same, single_eq_same]
      · intro s hs hne
        rw [single_eq_of_ne]
        intro h
        exact hne (extendMonomial_injective _ _ hs hs₀ (h.symm.trans he.symm))
      · intro h
        exact absurd hs₀ h
    · rw [single_eq_of_ne (Ne.symm ha), mul_zero]
      refine Finset.sum_eq_zero fun s _ => single_eq_of_ne ?_
      intro h
      apply ha
      funext v
      rw [h, extendMonomial_apply_image hj]

/-- Coefficients of an extended chain vanish at monomials which are not chart constants off the
image. -/
theorem cechExtend_apply_of_not_unitOff (c : C R V) {b : W → Basis} (hb : ¬ UnitOff j b) :
    cechExtend R j c b = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, add_zero]
  | single a r =>
    rw [cechExtend_single, Finset.sum_apply']
    refine Finset.sum_eq_zero fun s _ => single_eq_of_ne ?_
    intro h
    apply hb
    rw [h]
    exact unitOff_extendMonomial a s

/-- Extension preserves the supports by Čech degree. -/
theorem cechExtend_mem_supported (hj : Function.Injective j) {m : ℤ} {c : C R V}
    (hc : c ∈ supported R R {b | (cechDegree b : ℤ) = m}) :
    cechExtend R j c ∈ supported R R {b | (cechDegree b : ℤ) = m} := by
  rw [mem_supported'] at hc ⊢
  intro b hb
  by_cases hu : UnitOff j b
  · rw [cechExtend_apply_of_unitOff R hj c hu, hc, mul_zero]
    intro h
    apply hb
    obtain ⟨s, _, he⟩ := exists_extendMonomial_eq hj hu
    change (cechDegree b : ℤ) = m
    rw [← he, cechDegree_extendMonomial hj]
    exact h
  · exact cechExtend_apply_of_not_unitOff R c hu

/-- Extension commutes with the Čech parities. -/
theorem cechExtend_sign (hj : Function.Injective j) (d : V → ℕ) (d' : W → ℕ) (c : C R V) :
    cechExtend R j ((contraction R d).sign c) = (contraction R d').sign (cechExtend R j c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b r =>
    rw [contraction_sign_single, map_smul, cechExtend_single, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [contraction_sign_single, cechDegree_extendMonomial hj]

/-- Extension commutes with the monomial section actions, extended by zero off the image. -/
theorem cechExtend_multiply (hj : Function.Injective j) (a b : V → ℕ) (a' b' : W → ℕ)
    (ha : ∀ v, a' (j v) = a v) (hb : ∀ v, b' (j v) = b v)
    (ha0 : ∀ w, (∀ v, j v ≠ w) → a' w = 0) (hb0 : ∀ w, (∀ v, j v ≠ w) → b' w = 0) (c : C R V) :
    cechExtend R j (multiply R a b c) = multiply R a' b' (cechExtend R j c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single f r =>
    rw [multiply_single, cechExtend_single, cechExtend_single, map_sum]
    have hov : overlapVertices (fun v => shift (a v) (b v) (f v)) = overlapVertices f := by
      unfold overlapVertices
      simp only [lineDegree_shift]
    rw [hov]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [multiply_single]
    congr 1
    funext w
    by_cases hw : ∃ v, j v = w
    · obtain ⟨v, rfl⟩ := hw
      rw [extendMonomial_apply_image hj, extendMonomial_apply_image hj, ha, hb]
    · push Not at hw
      rw [extendMonomial_apply_of_not_mem _ _ hw, extendMonomial_apply_of_not_mem _ _ hw,
        ha0 w hw, hb0 w hw, shift_zero]

/-- At a vertex off the image the two chart constants cancel in the differential of an extended
monomial. -/
theorem sum_unitChoices_boundary_off (hj : Function.Injective j) (b : V → Basis) (K : R) {w : W}
    (hw : ∀ v, j v ≠ w)
    (d' : W → ℕ) (hd0 : d' w = 0) :
    ∑ s ∈ unitChoices j, single (Function.update (extendMonomial j b s) w
        (boundaryStep (d' w) (extendMonomial j b s w)))
        ((-1 : R) ^ boundaryPrefix (extendMonomial j b s) w *
          (boundaryCoefficient R (extendMonomial j b s w) * K)) = 0 := by
  have hterm : ∀ s ∈ unitChoices j, single (Function.update (extendMonomial j b s) w
        (boundaryStep (d' w) (extendMonomial j b s w)))
        ((-1 : R) ^ boundaryPrefix (extendMonomial j b s) w *
          (boundaryCoefficient R (extendMonomial j b s w) * K)) =
      single (Function.update (extendMonomial j b s) w (Sum.inr (Sum.inr 0)))
        ((-1 : R) ^ boundaryPrefix (extendMonomial j b s) w *
          (boundaryCoefficient R (unitBasis (s w)) * K)) := by
    intro s _
    rw [extendMonomial_apply_of_not_mem _ _ hw, hd0, boundaryStep_unitBasis]
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_involution (fun s _ => Function.update s w (!s w)) ?_ ?_ ?_ ?_
  · intro s _
    rw [extendMonomial_update_choice hj _ _ hw, Function.update_idem,
      boundaryPrefix_update_self, Function.update_self, boundaryCoefficient_unitBasis_not,
      ← single_add]
    convert single_zero (M := R) _ using 2
    ring
  · intro s _ _ h
    have h' := congrFun h w
    rw [Function.update_self] at h'
    cases hsw : s w <;> rw [hsw] at h' <;> exact absurd h' (by decide)
  · intro s hs
    rw [mem_unitChoices] at hs ⊢
    intro v
    rw [Function.update_of_ne (hw v), hs v]
  · intro s _
    rw [Function.update_idem, Function.update_self, Bool.not_not, Function.update_eq_self]

/-- **Extension commutes with the product Čech differentials**, for twists `d` on `V` and `d'` on
`W` with `d' ∘ j = d` and `d' = 0` off the image of `j`. -/
theorem cechExtend_d (hj : Function.Injective j) (d : V → ℕ) (d' : W → ℕ)
    (hd : ∀ v, d' (j v) = d v) (hd0 : ∀ w, (∀ v, j v ≠ w) → d' w = 0) (c : C R V) :
    cechExtend R j ((contraction R d).d c) = (contraction R d').d (cechExtend R j c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single b r =>
    rw [contraction_d_single, map_sum, cechExtend_single, map_sum]
    simp only [contraction_d_single]
    rw [Finset.sum_comm]
    apply Fintype.sum_of_injective j hj
    · intro w hw
      exact sum_unitChoices_boundary_off R hj b _ (fun v hv => hw ⟨v, hv⟩) d' (hd0 w
        fun v hv => hw ⟨v, hv⟩)
    · intro v
      rw [cechExtend_single]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [extendMonomial_apply_image hj, hd v, extendMonomial_update hj]
      congr 1
      rcases hbv : b v with k | k | k
      · -- a left chart monomial
        have hov : overlapVertices (Function.update b v (boundaryStep (d v) (Sum.inl k))) =
            insert v (overlapVertices b) := by
          ext u
          by_cases hu : u = v
          · subst hu
            simp [mem_overlapVertices, hbv, boundaryStep, lineDegree]
          · simp [mem_overlapVertices, hu]
        have hv : v ∉ overlapVertices b := by
          rw [mem_overlapVertices, hbv]
          simp [lineDegree]
        have hs := vertexMapSign_insert R j hv (hj.injOn)
        rw [hov, boundaryPrefix_eq_sum_overlap, boundaryPrefix_extendMonomial hj]
        linear_combination (boundaryCoefficient R (Sum.inl k) * r) * hs
      · -- a right chart monomial
        have hov :
            overlapVertices (Function.update b v (boundaryStep (d v) (Sum.inr (Sum.inl k)))) =
            insert v (overlapVertices b) := by
          ext u
          by_cases hu : u = v
          · subst hu
            simp [mem_overlapVertices, hbv, boundaryStep, lineDegree]
          · simp [mem_overlapVertices, hu]
        have hv : v ∉ overlapVertices b := by
          rw [mem_overlapVertices, hbv]
          simp [lineDegree]
        have hs := vertexMapSign_insert R j hv (hj.injOn)
        rw [hov, boundaryPrefix_eq_sum_overlap, boundaryPrefix_extendMonomial hj]
        linear_combination (boundaryCoefficient R (Sum.inr (Sum.inl k)) * r) * hs
      · simp [boundaryCoefficient]

end Chains

/-! ## States -/

section States

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (R : Type) [CommRing R] {j : V → W}

/-- Restriction of a state index of twist `d'` to the image of `j`, for `d' ∘ j = d`. -/
def hPull {d : V → ℕ} {d' : W → ℕ} (hd : ∀ v, d' (j v) = d v) (κ : HBasis d') : HBasis d :=
  fun v => Fin.cast (congrArg phi (hd v)) (κ (j v))

@[simp] theorem hPull_apply_val {d : V → ℕ} {d' : W → ℕ} (hd : ∀ v, d' (j v) = d v)
    (κ : HBasis d') (v : V) : (hPull hd κ v).val = (κ (j v)).val := rfl

/-- Projection monomials of cast state indices agree. -/
theorem lineProjectionMonomial_fin_cast {n m : ℕ} (h : n = m) (k : Fin (phi n)) :
    lineProjectionMonomial m (Fin.cast (congrArg phi h) k) = lineProjectionMonomial n k := by
  subst h
  rfl

/-- For twist zero the projection monomial is the right chart constant. -/
theorem lineProjectionMonomial_of_eq_zero {n : ℕ} (h : n = 0) (k : Fin (phi n)) :
    lineProjectionMonomial n k = unitBasis false := by
  subst h
  unfold lineProjectionMonomial
  split
  · rfl
  · rename_i i _
    exact absurd i.isLt (Nat.not_lt_zero _)

/-- **The state formula of the extension.** The projected extension of an included state of twist
`d` reads, at a state index of twist `d'`, the Koszul sign of the twist support times the
coefficient at the restricted index. -/
theorem contraction_p_cechExtend_i (hj : Function.Injective j) (d : V → ℕ) (d' : W → ℕ)
    (hd : ∀ v, d' (j v) = d v) (hd0 : ∀ w, (∀ v, j v ≠ w) → d' w = 0) (x : H R d)
    (κ : HBasis d') :
    (contraction R d').p (cechExtend R j ((contraction R d).i x)) κ =
      vertexMapSign R j (twistSupport d) * x (hPull hd κ) := by
  have hunit : UnitOff j (stateProjectionMonomial d' κ) := by
    intro w hw
    exact ⟨false, lineProjectionMonomial_of_eq_zero (hd0 w hw) _⟩
  have hcomp : (fun v => stateProjectionMonomial d' κ (j v)) =
      stateProjectionMonomial d (hPull hd κ) := by
    funext v
    exact (lineProjectionMonomial_fin_cast (hd v) (κ (j v))).symm
  rw [contraction_p_coefficient, cechExtend_apply_of_unitOff R hj _ hunit, hcomp,
    overlapVertices_stateProjectionMonomial, ← contraction_p_coefficient, contraction_p_i]

end States

end BPFixedPoints.Multigraph
