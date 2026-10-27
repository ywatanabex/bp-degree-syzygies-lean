import BPFixedPoints.Degree.Generic.ShapeCert

/-!
# Constructing a shape certificate from finitely many simple roots

Let F embed into algebraically closed Ω, with F of characteristic zero.
For f,D over F, assume finitely many admissible Ω-roots, all simple.
Their Rabinowitsch extensions P_y=(y,1/D(y)) are exactly the simple zeros
of the enlarged system; the finite-simple-zero ideal theorem identifies J_Ω.
Choose a natural N so u=sum_z N^{e(z)} X_z separates these points.
Lagrange interpolation and a Jacobian inverse give identities over Ω.
These identities are linear in unknown coefficients; a coefficientwise
F-linear retraction π:Ω→F descends them. The descended monic degree-Q
χ has all Q distinct λ_y as roots, hence equals product_y(Y-λ_y) and is
separable. Vanishing at all λ_y implies divisibility by χ over Ω and,
by monicity, over F. This constructs `exists_shapeCert`.
-/

namespace BPFixedPoints.BP

set_option linter.unusedSectionVars false

open MvPolynomial

/-! ### Linear descent -/

section Descent

variable {σ F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (π : Ω →ₗ[F] F)

/-- Apply π coefficientwise. -/
noncomputable def coeffProj (p : MvPolynomial σ Ω) : MvPolynomial σ F :=
  ∑ m ∈ p.support, monomial m (π (p.coeff m))

theorem coeff_coeffProj (p : MvPolynomial σ Ω) (n : σ →₀ ℕ) :
    (coeffProj π p).coeff n = π (p.coeff n) := by
  classical
  rw [coeffProj, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

/-- Additive-homomorphism version of `coeffProj`. -/
noncomputable def coeffProjHom : MvPolynomial σ Ω →+ MvPolynomial σ F where
  toFun := coeffProj π
  map_zero' := by ext; simp [coeff_coeffProj]
  map_add' p q := by ext; simp [coeff_coeffProj]

@[simp] theorem coeffProjHom_apply (p : MvPolynomial σ Ω) : coeffProjHom π p = coeffProj π p :=
  rfl

variable {π} (hπ : ∀ c, π (algebraMap F Ω c) = c)
include hπ

theorem π_mul_algebraMap (a : Ω) (b : F) : π (a * algebraMap F Ω b) = π a * b := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem coeffProj_map (q : MvPolynomial σ F) : coeffProj π (map (algebraMap F Ω) q) = q := by
  ext n
  rw [coeff_coeffProj, coeff_map, hπ]

theorem coeffProj_mul_map (A : MvPolynomial σ Ω) (q : MvPolynomial σ F) :
    coeffProj π (A * map (algebraMap F Ω) q) = coeffProj π A * q := by
  classical
  ext n
  rw [coeff_coeffProj, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, π_mul_algebraMap hπ, coeff_coeffProj]

theorem coeffProj_C_mul_map (c : Ω) (q : MvPolynomial σ F) :
    coeffProj π (C c * map (algebraMap F Ω) q) = C (π c) * q := by
  ext n
  rw [coeff_coeffProj, coeff_C_mul, coeff_C_mul, coeff_map, π_mul_algebraMap hπ]

/--
Linear descent: applying π coefficientwise descends an Ω-identity
P₀=sum c_j B_j+sum A_z h_z to the F-identity with projected coefficients,
when P₀,B,h are defined over F.
-/
theorem descent {β τ : Type*} [Fintype τ] (s : Finset β) (P₀ : MvPolynomial σ F)
    (B : β → MvPolynomial σ F) (c : β → Ω) (h : τ → MvPolynomial σ F) (A : τ → MvPolynomial σ Ω)
    (heq : map (algebraMap F Ω) P₀ = ∑ j ∈ s, C (c j) * map (algebraMap F Ω) (B j) +
      ∑ z, A z * map (algebraMap F Ω) (h z)) :
    P₀ = ∑ j ∈ s, C (π (c j)) * B j + ∑ z, coeffProj π (A z) * h z := by
  have := congrArg (coeffProjHom π) heq
  simp only [map_add, map_sum, coeffProjHom_apply] at this
  simpa only [coeffProj_map hπ, coeffProj_C_mul_map hπ, coeffProj_mul_map hπ] using this

end Descent

/-! ### Separating element -/

section Separate

/-- In characteristic zero, a linear form with coefficients N^{e(z)} for some natural N separates finitely many distinct points P_t∈Ω^τ. -/
theorem exists_separating {τ T Ω : Type*} [Fintype τ] [Fintype T] [Field Ω] [CharZero Ω]
    (P : T → τ → Ω) (hP : Function.Injective P) :
    ∃ N : ℕ, Function.Injective fun t => ∑ z, (N : Ω) ^ (Fintype.equivFin τ z : ℕ) * P t z := by
  classical
  let e : τ → ℕ := fun z => (Fintype.equivFin τ z : ℕ)
  have he : Function.Injective e := fun a b h =>
    (Fintype.equivFin τ).injective (Fin.ext h)
  let Pol : T → Polynomial Ω := fun t => ∑ z, Polynomial.C (P t z) * Polynomial.X ^ e z
  have hcoeff : ∀ t z, (Pol t).coeff (e z) = P t z := by
    intro t z
    simp only [Pol, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single z]
    · simp
    · intro b _ hb; rw [ite_eq_right]; exact fun h => hb (he h).symm
    · intro h; exact absurd (Finset.mem_univ z) h
  have hPol : Function.Injective Pol := by
    intro t t' h
    apply hP
    funext z
    rw [← hcoeff, ← hcoeff, h]
  let bad : Finset Ω := Finset.univ.biUnion fun p : T × T =>
    if p.1 = p.2 then ∅ else (Pol p.1 - Pol p.2).roots.toFinset
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset
    (bad.preimage (Nat.cast : ℕ → Ω) (Nat.cast_injective.injOn))
  refine ⟨N, fun t t' h => ?_⟩
  by_contra hne
  apply hN
  rw [Finset.mem_preimage, Finset.mem_biUnion]
  refine ⟨(t, t'), Finset.mem_univ _, ?_⟩
  rw [ite_eq_right hne, Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.2 fun e => hne (hPol e)),
    Polynomial.IsRoot.def, Polynomial.eval_sub, sub_eq_zero]
  simp only [Pol, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  simpa only [mul_comm] using h

end Separate

/-! ### Simplicity of Rabinowitsch points -/

section Simple

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Field κ]

theorem pderiv_none_rename {S : Type*} [CommRing S] (p : MvPolynomial ι S) :
    pderiv none (rename some p) = 0 := by
  classical
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.1 (vars_rename some p h)
  exact Option.some_ne_none j hj

theorem det_jac_ratSystem_ne_zero {f : ι → MvPolynomial ι κ} {D : MvPolynomial ι κ} {y : ι → κ}
    (hD : eval y D ≠ 0) (hdet : (Matrix.of fun i j => eval y (pderiv j (f i))).det ≠ 0) :
    (Matrix.of fun z z' => eval (extPt D y) (pderiv z' (ratSystem f D z))).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hc : extPt D y ∘ some = y := rfl
  have hnone : extPt D y none = (eval y D)⁻¹ := rfl
  have hss : ∀ i j, eval (extPt D y) (pderiv (some j) (ratSystem f D (some i))) =
      eval y (pderiv j (f i)) := by
    intro i j
    rw [ratSystem, pderiv_rename (Option.some_injective _), eval_rename, hc]
  have hsn : ∀ i, eval (extPt D y) (pderiv none (ratSystem f D (some i))) = 0 := by
    intro i
    rw [ratSystem, pderiv_none_rename, map_zero]
  have hns : ∀ j, eval (extPt D y) (pderiv (some j) (ratSystem f D none)) =
      (eval y D)⁻¹ * eval y (pderiv j D) := by
    intro j
    rw [ratSystem, map_sub, pderiv_mul, pderiv_X, pderiv_rename (Option.some_injective _),
      Derivation.map_one_eq_zero]
    simp [eval_rename, hc, hnone]
  have hnn : eval (extPt D y) (pderiv none (ratSystem f D none)) = eval y D := by
    rw [ratSystem, map_sub, pderiv_mul, pderiv_X, pderiv_none_rename, Derivation.map_one_eq_zero]
    simp [eval_rename, hc]
  have hw : Matrix.mulVec (Matrix.of fun i j => eval y (pderiv j (f i))) (v ∘ some) = 0 := by
    funext i
    have := congrFun hv (some i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_option, hsn, hss,
      zero_mul, zero_add, Pi.zero_apply] at this
    simpa [Matrix.mulVec, dotProduct] using this
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  have hs : ∀ j, v (some j) = 0 := fun j => congrFun hw0 j
  have hn : v none = 0 := by
    have := congrFun hv none
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_option, hnn, hns, hs,
      mul_zero, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hD
  apply hv0
  funext z
  cases z with
  | none => exact hn
  | some j => exact hs j

end Simple

/-! ### Certificate construction -/

section Construct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F Ω : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra F Ω]

/-- A polynomial vanishing at distinct λ_t is divisible by product_t(Y-λ_t). -/
theorem prod_X_sub_C_dvd {T : Type*} [Fintype T] (lam : T → Ω) (hlam : Function.Injective lam)
    (G : Polynomial Ω) (hG : ∀ t, G.eval (lam t) = 0) :
    (∏ t, (Polynomial.X - Polynomial.C (lam t))) ∣ G :=
  Finset.prod_dvd_of_coprime (fun _ _ _ _ hab => Polynomial.pairwise_coprime_X_sub_C hlam hab)
    fun t _ => Polynomial.dvd_iff_isRoot.2 (hG t)

variable (f : ι → MvPolynomial ι F) (D : MvPolynomial ι F)

/-- Certificate existence: finitely many simple Ω-roots yield an F-valued certificate with Q equal to the root count. -/
theorem exists_shapeCert
    [Finite {y : ι → Ω // (∀ i, eval y (map (algebraMap F Ω) (f i)) = 0) ∧
      eval y (map (algebraMap F Ω) D) ≠ 0}]
    (hsimple : ∀ y : {y : ι → Ω // (∀ i, eval y (map (algebraMap F Ω) (f i)) = 0) ∧
      eval y (map (algebraMap F Ω) D) ≠ 0},
      (Matrix.of fun i j => eval y.1 (pderiv j (map (algebraMap F Ω) (f i)))).det ≠ 0) :
    Nonempty (ShapeCert f D (Nat.card {y : ι → Ω // (∀ i, eval y (map (algebraMap F Ω) (f i)) = 0) ∧
      eval y (map (algebraMap F Ω) D) ≠ 0})) := by
  classical
  set Sol := {y : ι → Ω // (∀ i, eval y (map (algebraMap F Ω) (f i)) = 0) ∧ eval y (map (algebraMap F Ω) D) ≠ 0} with hSol
  have : Fintype Sol := Fintype.ofFinite Sol
  set fΩ : ι → MvPolynomial ι Ω := fun i => map (algebraMap F Ω) (f i) with hfΩ
  set DΩ := map (algebraMap F Ω) D with hDΩ
  set hF := ratSystem f D with hhF
  set hΩ := ratSystem fΩ DΩ with hhΩ
  have hmapsys : ∀ z, map (algebraMap F Ω) (hF z) = hΩ z := fun z => map_ratSystem (algebraMap F Ω) f D z
  set Q := Nat.card Sol with hQdef
  have hQ : Fintype.card Sol = Q := Nat.card_eq_fintype_card.symm
  -- Choose an F-linear retraction π.
  obtain ⟨π, hπ'⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap F Ω).injective)
  have hπ : ∀ c, π (algebraMap F Ω c) = c := fun c => LinearMap.congr_fun hπ' c
  -- Rabinowitsch points.
  let Pt : Sol → Option ι → Ω := fun y => extPt DΩ y.1
  have hPt_sys : ∀ y z, eval (Pt y) (hΩ z) = 0 := fun y => eval_ratSystem_extPt y.2.1 y.2.2
  have hPt_some : ∀ y, Pt y ∘ some = y.1 := fun y => rfl
  have hPt_inj : Function.Injective Pt := fun y y' h =>
    Subtype.ext (by rw [← hPt_some y, ← hPt_some y', h])
  -- Vanishing ideal.
  have hvan : ∀ p : MvPolynomial (Option ι) Ω, (∀ y, eval (Pt y) p = 0) →
      ∃ A : Option ι → MvPolynomial (Option ι) Ω, p = ∑ z, A z * hΩ z := by
    intro p hp
    have hmem : p ∈ Ideal.span (Set.range hΩ) := by
      refine mem_span_of_forall_eval_eq_zero hΩ (Finset.univ.image Pt) ?_ ?_ ?_ ?_
      · intro P hP
        have hf : ∀ i, eval (P ∘ some) (fΩ i) = 0 := fun i => by
          have := hP (some i)
          rwa [hhΩ, ratSystem, eval_rename] at this
        have hT : P none * eval (P ∘ some) DΩ = 1 := by
          have := hP none
          rw [hhΩ, ratSystem, map_sub, map_mul, eval_X, eval_rename, map_one, sub_eq_zero] at this
          exact this
        have hD : eval (P ∘ some) DΩ ≠ 0 := fun h0 => by
          rw [h0, mul_zero] at hT; exact zero_ne_one hT
        refine Finset.mem_image.2 ⟨⟨P ∘ some, hf, hD⟩, Finset.mem_univ _, ?_⟩
        funext z
        cases z with
        | some i => rfl
        | none => exact (eq_inv_of_mul_eq_one_left hT).symm
      · intro P hP
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hP
        exact hPt_sys y
      · intro P hP
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hP
        exact det_jac_ratSystem_ne_zero y.2.2 (hsimple y)
      · intro P hP
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hP
        exact hp y
    obtain ⟨A, hA⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
    exact ⟨A, hA.symm⟩
  -- Separating element u.
  obtain ⟨N, hN⟩ := exists_separating Pt hPt_inj
  let e : Option ι → ℕ := fun z => (Fintype.equivFin (Option ι) z : ℕ)
  let u : MvPolynomial (Option ι) F := ∑ z, C ((N : F) ^ e z) * X z
  have huΩ : ∀ P, eval P (map (algebraMap F Ω) u) = ∑ z, (N : Ω) ^ e z * P z := by
    intro P
    simp [u, map_sum]
  let lam : Sol → Ω := fun y => eval (Pt y) (map (algebraMap F Ω) u)
  have hlam : Function.Injective lam := by
    intro y y' h
    apply hN
    simp only [lam, huΩ] at h
    exact h
  -- χ_Ω = ∏(Y − λ_y)
  let χΩ : Polynomial Ω := ∏ y, (Polynomial.X - Polynomial.C (lam y))
  have hχΩ_monic : χΩ.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun y _ => Polynomial.monic_X_sub_C _
  have hχΩ_deg : χΩ.natDegree = Q := by
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, hQ]
  have hχΩ_root : ∀ y, χΩ.eval (lam y) = 0 := by
    intro y
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp)
  obtain ⟨A₁, hA₁⟩ := hvan (Polynomial.eval₂ C (map (algebraMap F Ω) u) χΩ) fun y => by
    rw [eval_polyEval₂]; exact hχΩ_root y
  have hexp : Polynomial.eval₂ C (map (algebraMap F Ω) u) χΩ =
      (map (algebraMap F Ω) u) ^ Q + ∑ j ∈ Finset.range Q, C (χΩ.coeff j) * (map (algebraMap F Ω) u) ^ j := by
    conv_lhs => rw [hχΩ_monic.as_sum, hχΩ_deg]
    simp [Polynomial.eval₂_finsetSum]
  have hdesc := descent hπ (Finset.range Q) (u ^ Q) (fun j => u ^ j) (fun j => -χΩ.coeff j) hF A₁
    (by
      simp only [map_pow, hmapsys, map_neg, neg_mul, Finset.sum_neg_distrib]
      rw [← hA₁, hexp]
      ring)
  -- χ_F
  let d : ℕ → F := fun j => π (-χΩ.coeff j)
  let χF : Polynomial F :=
    Polynomial.X ^ Q - ∑ j ∈ Finset.range Q, Polynomial.C (d j) * Polynomial.X ^ j
  have hdeg_lt : (∑ j ∈ Finset.range Q, Polynomial.C (d j) * Polynomial.X ^ j).degree < (Q : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right]
    intro h
    have := Finset.mem_range.1 hj
    omega
  have hχF_monic : χF.Monic := Polynomial.monic_X_pow_sub hdeg_lt
  have hχF_deg : χF.natDegree = Q := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  have hχ_eq : Polynomial.eval₂ C u χF = ∑ z, coeffProj π (A₁ z) * hF z := by
    simp only [χF, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [hdesc]
    ring
  have hχF_root : ∀ y, (χF.map (algebraMap F Ω)).eval (lam y) = 0 := by
    intro y
    have := congrArg (fun p => eval (Pt y) (map (algebraMap F Ω) p)) hχ_eq
    simp only [map_polyEval₂, eval_polyEval₂, map_sum, map_mul, hmapsys, hPt_sys, mul_zero,
      Finset.sum_const_zero] at this
    exact this
  have hχmap : χF.map (algebraMap F Ω) = χΩ := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hχΩ_monic (hχF_monic.map (algebraMap F Ω))
    · exact prod_X_sub_C_dvd lam hlam _ hχF_root
    · rw [hχF_monic.natDegree_map, hχF_deg, hχΩ_deg]
  have hsepΩ : χΩ.Separable :=
    Polynomial.separable_prod_X_sub_C_iff'.2 fun a _ b _ h => hlam h
  have hsepF : χF.Separable := (Polynomial.separable_map (algebraMap F Ω)).1 (hχmap ▸ hsepΩ)
  obtain ⟨sa, sb, hsab⟩ := hsepF
  have hdvdF : ∀ G : Polynomial F, (∀ y, (G.map (algebraMap F Ω)).eval (lam y) = 0) → ∃ q, G = χF * q := by
    intro G hG
    have h1 : χF.map (algebraMap F Ω) ∣ G.map (algebraMap F Ω) := hχmap ▸ prod_X_sub_C_dvd lam hlam _ hG
    exact (Polynomial.map_dvd_map (algebraMap F Ω) (algebraMap F Ω).injective hχF_monic).1 h1
  -- Coordinate expressions w_z.
  have hw : ∀ z, ∃ wz : Polynomial F, ∃ Az : Option ι → MvPolynomial (Option ι) F,
      X z - Polynomial.eval₂ C u wz = ∑ z', Az z' * hF z' := by
    intro z
    let W : Polynomial Ω := Lagrange.interpolate Finset.univ lam (fun y => Pt y z)
    have hW : ∀ y, W.eval (lam y) = Pt y z := fun y =>
      Lagrange.eval_interpolate_at_node _ hlam.injOn (Finset.mem_univ y)
    obtain ⟨A₂, hA₂⟩ := hvan (X z - Polynomial.eval₂ C (map (algebraMap F Ω) u) W) fun y => by
      rw [map_sub, eval_X, eval_polyEval₂, hW, sub_self]
    have hexpW : Polynomial.eval₂ C (map (algebraMap F Ω) u) W =
        ∑ j ∈ Finset.range (W.natDegree + 1), C (W.coeff j) * (map (algebraMap F Ω) u) ^ j := by
      conv_lhs => rw [W.as_sum_range_C_mul_X_pow]
      simp [Polynomial.eval₂_finsetSum]
    have hd := descent hπ (Finset.range (W.natDegree + 1)) (X z) (fun j => u ^ j)
      (fun j => W.coeff j) hF A₂ (by
        simp only [map_X, map_pow, hmapsys]
        rw [← hexpW]
        linear_combination hA₂)
    refine ⟨∑ j ∈ Finset.range (W.natDegree + 1), Polynomial.C (π (W.coeff j)) * Polynomial.X ^ j,
      fun z' => coeffProj π (A₂ z'), ?_⟩
    simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow]
    linear_combination hd
  choose w Aw hw_eq using hw
  have hw_at : ∀ z y, ((w z).map (algebraMap F Ω)).eval (lam y) = Pt y z := by
    intro z y
    have := congrArg (fun p => eval (Pt y) (map (algebraMap F Ω) p)) (hw_eq z)
    simp only [map_sub, map_X, eval_X, map_polyEval₂, eval_polyEval₂, map_sum, map_mul, hmapsys,
      hPt_sys, mul_zero, Finset.sum_const_zero, sub_eq_zero] at this
    exact this.symm
  have hw_fun : ∀ y, (fun z => ((w z).map (algebraMap F Ω)).eval (lam y)) = Pt y := fun y =>
    funext fun z => hw_at z y
  -- χ ∣ h(w(Y))、χ ∣ u(w(Y)) − Y
  have hqs : ∀ z, ∃ q, eval₂ Polynomial.C w (hF z) = χF * q := by
    intro z
    apply hdvdF
    intro y
    rw [map_mvEval₂, eval_mvEval₂, hmapsys, hw_fun]
    exact hPt_sys y z
  choose qs hqs using hqs
  obtain ⟨qu, hqu⟩ : ∃ q, eval₂ Polynomial.C w u - Polynomial.X = χF * q := by
    apply hdvdF
    intro y
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_X, map_mvEval₂,
      eval_mvEval₂, hw_fun, sub_eq_zero]
  -- Inverse of the Jacobian determinant.
  have hδmap : map (algebraMap F Ω) (rename some (jacDet f)) = rename some (jacDet fΩ) := by
    rw [map_rename, map_jacDet]
  have hδne : ∀ y, eval (Pt y) (rename some (jacDet fΩ)) ≠ 0 := by
    intro y
    rw [eval_rename, hPt_some, eval_jacDet]
    exact hsimple y
  let V : Polynomial Ω := Lagrange.interpolate Finset.univ lam
    (fun y => (eval (Pt y) (rename some (jacDet fΩ)))⁻¹)
  have hV : ∀ y, V.eval (lam y) = (eval (Pt y) (rename some (jacDet fΩ)))⁻¹ := fun y =>
    Lagrange.eval_interpolate_at_node _ hlam.injOn (Finset.mem_univ y)
  obtain ⟨A₃, hA₃⟩ := hvan (rename some (jacDet fΩ) * Polynomial.eval₂ C (map (algebraMap F Ω) u) V - 1) fun y => by
    rw [map_sub, map_mul, eval_polyEval₂, hV, mul_inv_cancel₀ (hδne y), map_one, sub_self]
  have hexpV : Polynomial.eval₂ C (map (algebraMap F Ω) u) V =
      ∑ j ∈ Finset.range (V.natDegree + 1), C (V.coeff j) * (map (algebraMap F Ω) u) ^ j := by
    conv_lhs => rw [V.as_sum_range_C_mul_X_pow]
    simp [Polynomial.eval₂_finsetSum]
  have hdV := descent hπ (Finset.range (V.natDegree + 1)) 1
    (fun j => rename some (jacDet f) * u ^ j) (fun j => V.coeff j) hF (fun z => -A₃ z) (by
      simp only [map_one, map_mul, map_pow, hδmap, hmapsys]
      have h1 : ∑ j ∈ Finset.range (V.natDegree + 1),
          C (V.coeff j) * (rename some (jacDet fΩ) * (map (algebraMap F Ω) u) ^ j) =
          rename some (jacDet fΩ) * Polynomial.eval₂ C (map (algebraMap F Ω) u) V := by
        rw [hexpV, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h1]
      simp only [neg_mul, Finset.sum_neg_distrib]
      linear_combination -hA₃)
  let vF : MvPolynomial (Option ι) F :=
    ∑ j ∈ Finset.range (V.natDegree + 1), C (π (V.coeff j)) * u ^ j
  have hδ_eq : rename some (jacDet f) * vF - 1 =
      ∑ z, (-coeffProj π (-A₃ z)) * hF z := by
    have h2 : rename some (jacDet f) * vF = ∑ j ∈ Finset.range (V.natDegree + 1),
        C (π (V.coeff j)) * (rename some (jacDet f) * u ^ j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    simp only [neg_mul, Finset.sum_neg_distrib]
    linear_combination -hdV
  exact ⟨{
    u := u
    χ := χF
    monic := hχF_monic
    natDegree_eq := hχF_deg
    sa := sa
    sb := sb
    sep := hsab
    w := w
    qs := qs
    sys_eq := hqs
    qu := qu
    u_eq := hqu
    Aχ := fun z => coeffProj π (A₁ z)
    χ_eq := hχ_eq
    Aw := Aw
    w_eq := hw_eq
    v := vF
    Aδ := fun z => -coeffProj π (-A₃ z)
    δ_eq := hδ_eq }⟩

end Construct

end BPFixedPoints.BP
