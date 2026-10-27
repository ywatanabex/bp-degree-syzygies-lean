import BPFixedPoints.Degree.Generic.Fiber
import BPFixedPoints.Degree.Generic.PointIdeal

/-!
# Shape certificates and algebraically closed root counts

For a square system f and denominator D over S, use the Rabinowitsch
system h_some(i)=f_i and h_none=T D-1 in variables Option ι.
A `ShapeCert f D Q` consists of a separating element u, a monic degree-Q
polynomial χ with a Bezout separability identity, coordinate expressions
w_z with χ dividing h(w) and u(w)-Y, identities χ(u)∈J and
X_z-w_z(u)∈J, and an inverse of the original Jacobian determinant modulo J.
Ideal membership is supplied by explicit combinations of the generators,
so certificates map along arbitrary ring homomorphisms. Over an algebraically
closed field, λ↦w(λ) bijects roots of χ with admissible roots of f;
there are Q of them, all simple.
-/

namespace BPFixedPoints.BP

set_option linter.unusedSectionVars false

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Defs

variable {S : Type*} [CommRing S]

/-- Rabinowitsch system in variables Option ι, with none representing T=1/D. -/
noncomputable def ratSystem (f : ι → MvPolynomial ι S) (D : MvPolynomial ι S) :
    Option ι → MvPolynomial (Option ι) S
  | some i => rename some (f i)
  | none => X none * rename some D - 1

/-- Jacobian determinant det(∂_j f_i) of f. -/
noncomputable def jacDet (f : ι → MvPolynomial ι S) : MvPolynomial ι S :=
  (Matrix.of fun i j => pderiv j (f i)).det

/-- Shape-lemma certificate described in the module introduction. -/
structure ShapeCert (f : ι → MvPolynomial ι S) (D : MvPolynomial ι S) (Q : ℕ) where
  u : MvPolynomial (Option ι) S
  χ : Polynomial S
  monic : χ.Monic
  natDegree_eq : χ.natDegree = Q
  sa : Polynomial S
  sb : Polynomial S
  sep : sa * χ + sb * Polynomial.derivative χ = 1
  w : Option ι → Polynomial S
  qs : Option ι → Polynomial S
  sys_eq : ∀ z, eval₂ Polynomial.C w (ratSystem f D z) = χ * qs z
  qu : Polynomial S
  u_eq : eval₂ Polynomial.C w u - Polynomial.X = χ * qu
  Aχ : Option ι → MvPolynomial (Option ι) S
  χ_eq : Polynomial.eval₂ C u χ = ∑ z, Aχ z * ratSystem f D z
  Aw : Option ι → Option ι → MvPolynomial (Option ι) S
  w_eq : ∀ z, X z - Polynomial.eval₂ C u (w z) = ∑ z', Aw z z' * ratSystem f D z'
  v : MvPolynomial (Option ι) S
  Aδ : Option ι → MvPolynomial (Option ι) S
  δ_eq : rename some (jacDet f) * v - 1 = ∑ z, Aδ z * ratSystem f D z

end Defs

/-! ### Compatibility with ring homomorphisms -/

section Map

variable {S S' : Type*} [CommRing S] [CommRing S'] (φ : S →+* S')

theorem map_ratSystem (f : ι → MvPolynomial ι S) (D : MvPolynomial ι S) (z : Option ι) :
    map φ (ratSystem f D z) = ratSystem (fun i => map φ (f i)) (map φ D) z := by
  cases z with
  | none => simp [ratSystem, map_rename]
  | some i => simp [ratSystem, map_rename]

theorem map_jacDet (f : ι → MvPolynomial ι S) :
    map φ (jacDet f) = jacDet fun i => map φ (f i) := by
  rw [jacDet, jacDet, RingHom.map_det]
  congr 1
  ext i j
  simp [pderiv_map]

theorem map_mvEval₂ (w : Option ι → Polynomial S) (p : MvPolynomial (Option ι) S) :
    Polynomial.map φ (eval₂ Polynomial.C w p) =
      eval₂ Polynomial.C (fun z => (w z).map φ) (map φ p) := by
  have h1 := eval₂_comp_left (Polynomial.mapRingHom φ) Polynomial.C w p
  rw [eval₂_map]
  have h2 : (Polynomial.mapRingHom φ).comp Polynomial.C = Polynomial.C.comp φ := by
    ext a; simp
  rw [h2] at h1
  exact h1

theorem map_polyEval₂ (u : MvPolynomial (Option ι) S) (χ : Polynomial S) :
    map φ (Polynomial.eval₂ C u χ) = Polynomial.eval₂ C (map φ u) (χ.map φ) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext a
  simp

variable {f : ι → MvPolynomial ι S} {D : MvPolynomial ι S} {Q : ℕ}

/-- Map a certificate along a ring homomorphism. -/
noncomputable def ShapeCert.map [Nontrivial S'] (c : ShapeCert f D Q) :
    ShapeCert (fun i => MvPolynomial.map φ (f i)) (MvPolynomial.map φ D) Q where
  u := MvPolynomial.map φ c.u
  χ := c.χ.map φ
  monic := c.monic.map φ
  natDegree_eq := by rw [c.monic.natDegree_map, c.natDegree_eq]
  sa := c.sa.map φ
  sb := c.sb.map φ
  sep := by
    rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add,
      c.sep, Polynomial.map_one]
  w := fun z => (c.w z).map φ
  qs := fun z => (c.qs z).map φ
  sys_eq := fun z => by
    rw [← map_ratSystem, ← map_mvEval₂, c.sys_eq, Polynomial.map_mul]
  qu := c.qu.map φ
  u_eq := by
    rw [← map_mvEval₂, ← Polynomial.map_X φ, ← Polynomial.map_sub, c.u_eq, Polynomial.map_mul]
  Aχ := fun z => MvPolynomial.map φ (c.Aχ z)
  χ_eq := by
    rw [← map_polyEval₂, c.χ_eq, map_sum]
    simp only [map_mul, map_ratSystem]
  Aw := fun z z' => MvPolynomial.map φ (c.Aw z z')
  w_eq := fun z => by
    have := congrArg (MvPolynomial.map φ) (c.w_eq z)
    rw [map_sub, map_X, map_polyEval₂, map_sum] at this
    simpa only [map_mul, map_ratSystem] using this
  v := MvPolynomial.map φ c.v
  Aδ := fun z => MvPolynomial.map φ (c.Aδ z)
  δ_eq := by
    have := congrArg (MvPolynomial.map φ) c.δ_eq
    rw [map_sub, map_mul, map_one, map_rename, map_jacDet, map_sum] at this
    simpa only [map_mul, map_ratSystem] using this

end Map

/-! ### Counting over an algebraically closed field -/

section Count

variable {κ : Type*} [Field κ] {f : ι → MvPolynomial ι κ} {D : MvPolynomial ι κ} {Q : ℕ}

/-- Extend a solution y by T=1/D(y). -/
noncomputable def extPt (D : MvPolynomial ι κ) (y : ι → κ) : Option ι → κ :=
  fun z => Option.elim z (eval y D)⁻¹ y

theorem eval_ratSystem_extPt {y : ι → κ} (hf : ∀ i, eval y (f i) = 0) (hD : eval y D ≠ 0)
    (z : Option ι) : eval (extPt D y) (ratSystem f D z) = 0 := by
  have hc : extPt D y ∘ some = y := rfl
  cases z with
  | some i => simp [ratSystem, eval_rename, hc, hf i]
  | none => simp [ratSystem, eval_rename, hc, extPt, inv_mul_cancel₀ hD]

theorem eval_sum_ratSystem {P : Option ι → κ} (hP : ∀ z, eval P (ratSystem f D z) = 0)
    (A : Option ι → MvPolynomial (Option ι) κ) : eval P (∑ z, A z * ratSystem f D z) = 0 := by
  simp [map_sum, hP]

theorem eval_mvEval₂ (w : Option ι → Polynomial κ) (p : MvPolynomial (Option ι) κ) (a : κ) :
    (eval₂ Polynomial.C w p).eval a = eval (fun z => (w z).eval a) p := by
  have := eval₂_comp_left (Polynomial.evalRingHom a) Polynomial.C w p
  rw [Polynomial.coe_evalRingHom] at this
  rw [this]
  have h2 : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id κ := by ext; simp
  rw [h2]
  rfl

theorem eval_polyEval₂ (P : Option ι → κ) (u : MvPolynomial (Option ι) κ) (χ : Polynomial κ) :
    eval P (Polynomial.eval₂ C u χ) = χ.eval (eval P u) := by
  rw [Polynomial.hom_eval₂]
  have h2 : (eval P).comp C = RingHom.id κ := by ext; simp
  rw [h2]
  rfl

theorem eval_jacDet (y : ι → κ) :
    eval y (jacDet f) = (Matrix.of fun i j => eval y (pderiv j (f i))).det := by
  rw [jacDet, RingHom.map_det]
  rfl

namespace ShapeCert

variable (c : ShapeCert f D Q)

/-- Point w(a) corresponding to a root a. -/
noncomputable def pt (a : κ) : Option ι → κ := fun z => (c.w z).eval a

theorem eval_ratSystem_pt {a : κ} (ha : c.χ.eval a = 0) (z : Option ι) :
    eval (c.pt a) (ratSystem f D z) = 0 := by
  rw [show c.pt a = fun z => (c.w z).eval a from rfl, ← eval_mvEval₂, c.sys_eq,
    Polynomial.eval_mul, ha, zero_mul]

theorem eval_u_pt {a : κ} (ha : c.χ.eval a = 0) : eval (c.pt a) c.u = a := by
  have := congrArg (Polynomial.eval a) c.u_eq
  rw [Polynomial.eval_sub, eval_mvEval₂, Polynomial.eval_X, Polynomial.eval_mul, ha, zero_mul,
    sub_eq_zero] at this
  exact this

theorem f_pt {a : κ} (ha : c.χ.eval a = 0) (i : ι) : eval (c.pt a ∘ some) (f i) = 0 := by
  have := c.eval_ratSystem_pt ha (some i)
  rwa [ratSystem, eval_rename] at this

theorem D_pt_mul {a : κ} (ha : c.χ.eval a = 0) : c.pt a none * eval (c.pt a ∘ some) D = 1 := by
  have := c.eval_ratSystem_pt ha none
  rw [ratSystem, map_sub, map_mul, eval_X, eval_rename, map_one, sub_eq_zero] at this
  exact this

/-- Every solution comes from a root: λ=u(y,T) is a root and y=w(λ). -/
theorem root_of_sol {y : ι → κ} (hf : ∀ i, eval y (f i) = 0) (hD : eval y D ≠ 0) :
    c.χ.eval (eval (extPt D y) c.u) = 0 ∧ c.pt (eval (extPt D y) c.u) = extPt D y := by
  have hP := eval_ratSystem_extPt hf hD
  refine ⟨?_, ?_⟩
  · rw [← eval_polyEval₂, c.χ_eq]
    exact eval_sum_ratSystem hP _
  · funext z
    have := congrArg (eval (extPt D y)) (c.w_eq z)
    rw [eval_sum_ratSystem hP, map_sub, eval_X, eval_polyEval₂, sub_eq_zero] at this
    exact this.symm

/-- Finite set of roots. -/
noncomputable def rootFinset [DecidableEq κ] : Finset κ := c.χ.roots.toFinset

theorem mem_rootFinset [DecidableEq κ] {a : κ} : a ∈ c.rootFinset ↔ c.χ.eval a = 0 := by
  rw [rootFinset, Multiset.mem_toFinset, Polynomial.mem_roots c.monic.ne_zero, Polynomial.IsRoot.def]

variable [IsAlgClosed κ]

theorem card_rootFinset [DecidableEq κ] : c.rootFinset.card = Q := by
  have hsep : c.χ.Separable := ⟨c.sa, c.sb, c.sep⟩
  rw [rootFinset, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    IsAlgClosed.card_roots_eq_natDegree, c.natDegree_eq]

include c in
/-- Counting theorem: a certificate over an algebraically closed field gives exactly Q roots. -/
theorem card_eq :
    Nat.card {y : ι → κ // (∀ i, eval y (f i) = 0) ∧ eval y D ≠ 0} = Q := by
  classical
  let toSol : c.rootFinset → {y : ι → κ // (∀ i, eval y (f i) = 0) ∧ eval y D ≠ 0} :=
    fun a => ⟨c.pt a ∘ some, c.f_pt (c.mem_rootFinset.1 a.2), fun h0 => by
      have := c.D_pt_mul (c.mem_rootFinset.1 a.2)
      rw [h0, mul_zero] at this
      exact zero_ne_one this⟩
  have hbij : Function.Bijective toSol := by
    constructor
    · intro a b hab
      have hab' : c.pt a ∘ some = c.pt b ∘ some := congrArg Subtype.val hab
      have ha := c.mem_rootFinset.1 a.2
      have hb := c.mem_rootFinset.1 b.2
      have hpt : c.pt a = c.pt b := by
        funext z
        cases z with
        | some i => exact congrFun hab' i
        | none =>
          have h1 := c.D_pt_mul ha
          have h2 := c.D_pt_mul hb
          rw [hab'] at h1
          have hne : eval (c.pt b ∘ some) D ≠ 0 := fun h0 => by
            rw [h0, mul_zero] at h2; exact zero_ne_one h2
          exact (mul_right_cancel₀ hne (h1.trans h2.symm))
      apply Subtype.ext
      rw [← c.eval_u_pt ha, ← c.eval_u_pt hb, hpt]
    · intro y
      obtain ⟨hroot, hpt⟩ := c.root_of_sol y.2.1 y.2.2
      refine ⟨⟨_, c.mem_rootFinset.2 hroot⟩, Subtype.ext ?_⟩
      show c.pt _ ∘ some = y.1
      rw [hpt]
      rfl
  rw [← Nat.card_congr (Equiv.ofBijective toSol hbij), Nat.card_eq_fintype_card,
    Fintype.card_coe, c.card_rootFinset]

include c in
/-- Simplicity theorem: a certificate over an algebraically closed field makes every root's Jacobian determinant nonzero. -/
theorem det_ne_zero {y : ι → κ} (hf : ∀ i, eval y (f i) = 0) (hD : eval y D ≠ 0) :
    (Matrix.of fun i j => eval y (pderiv j (f i))).det ≠ 0 := by
  have hP := eval_ratSystem_extPt hf hD
  have := congrArg (eval (extPt D y)) c.δ_eq
  rw [eval_sum_ratSystem hP, map_sub, map_mul, eval_rename, map_one, sub_eq_zero] at this
  have hc : extPt D y ∘ some = y := rfl
  rw [hc, eval_jacDet] at this
  exact left_ne_zero_of_mul_eq_one this

end ShapeCert

end Count

end BPFixedPoints.BP
