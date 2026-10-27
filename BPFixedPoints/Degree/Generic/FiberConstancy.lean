import BPFixedPoints.Degree.Generic.ShapeCertExists

/-!
# Proof of generic fiber constancy

Prove the former axiom `generic_fiber_constancy` using a shape certificate.
Injectivity of θ₀ makes R a domain; extend θ₀ to F=Frac R→Ω. A finite simple
Ω-fiber has a certificate over F (`exists_shapeCert`). Clearing finitely many
denominators gives one over R[1/g] for g≠0 (`ShapeCert.lift`); injectivity
into F lifts the identities. For θ(g)≠0 extend θ to R[1/g]→κ, transport the
certificate and use `ShapeCert.card_eq` and `ShapeCert.det_ne_zero`.
The proof adds `CharZero Ω` (a separating element with natural coefficients)
and explicit finiteness to the former axiom. Both hold in N=Q, where Ω is
Puiseux-type and Q(G)>0.
-/

namespace BPFixedPoints.BP

set_option linter.unusedSectionVars false

open MvPolynomial

universe u v w x

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Finite coefficient sets and lifting -/

section Lift

/-- Finite set of all certificate coefficients. -/
noncomputable def ShapeCert.coeffSet {S : Type*} [CommRing S] [DecidableEq S]
    {f : ι → MvPolynomial ι S} {D : MvPolynomial ι S} {Q : ℕ} (c : ShapeCert f D Q) : Finset S :=
  c.u.coeffs ∪ c.χ.coeffs ∪ c.sa.coeffs ∪ c.sb.coeffs ∪ c.qu.coeffs ∪ c.v.coeffs ∪
    Finset.univ.biUnion fun z => (c.w z).coeffs ∪ (c.qs z).coeffs ∪ (c.Aχ z).coeffs ∪
      (c.Aδ z).coeffs ∪ Finset.univ.biUnion fun z' => (c.Aw z z').coeffs

variable {S S' : Type*} [CommRing S] [CommRing S'] (ψ : S →+* S')

theorem exists_mv_lift {σ : Type*} {p' : MvPolynomial σ S'} (h : ↑p'.coeffs ⊆ Set.range ψ) :
    ∃ p : MvPolynomial σ S, MvPolynomial.map ψ p = p' :=
  mem_range_map_iff_coeffs_subset.2 h

theorem exists_poly_lift {p' : Polynomial S'} (h : ↑p'.coeffs ⊆ Set.range ψ) :
    ∃ p : Polynomial S, p.map ψ = p' := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  by_cases hn : p'.coeff n = 0
  · rw [hn]; exact ⟨0, map_zero ψ⟩
  · exact h (Polynomial.coeff_mem_coeffs hn)

variable [DecidableEq S'] {Q : ℕ}

/-- Lift a certificate when ψ is injective and every coefficient of the specialized certificate lies in its image. -/
theorem ShapeCert.lift (hψ : Function.Injective ψ) (f : ι → MvPolynomial ι S) (D : MvPolynomial ι S)
    {f' : ι → MvPolynomial ι S'} {D' : MvPolynomial ι S'}
    (hf : (fun i => MvPolynomial.map ψ (f i)) = f') (hD : MvPolynomial.map ψ D = D')
    (c : ShapeCert f' D' Q) (hc : ↑c.coeffSet ⊆ Set.range ψ) : Nonempty (ShapeCert f D Q) := by
  classical
  subst hf hD
  have liftMv : ∀ p' : MvPolynomial (Option ι) S', (∀ x ∈ p'.coeffs, x ∈ c.coeffSet) →
      ∃ p, MvPolynomial.map ψ p = p' := fun p' h => exists_mv_lift ψ fun x hx => hc (h x hx)
  have liftPoly : ∀ p' : Polynomial S', (∀ x ∈ p'.coeffs, x ∈ c.coeffSet) →
      ∃ p : Polynomial S, p.map ψ = p' := fun p' h => exists_poly_lift ψ fun x hx => hc (h x hx)
  have inZ : ∀ z {x : S'}, x ∈ (c.w z).coeffs ∪ (c.qs z).coeffs ∪ (c.Aχ z).coeffs ∪
      (c.Aδ z).coeffs ∪ Finset.univ.biUnion (fun z' => (c.Aw z z').coeffs) → x ∈ c.coeffSet :=
    fun z x hx => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, Finset.mem_univ _, hx⟩)
  obtain ⟨u, hu⟩ := liftMv c.u fun x hx => by simp [ShapeCert.coeffSet, hx]
  obtain ⟨χ, hχ⟩ := liftPoly c.χ fun x hx => by simp [ShapeCert.coeffSet, hx]
  obtain ⟨sa, hsa⟩ := liftPoly c.sa fun x hx => by simp [ShapeCert.coeffSet, hx]
  obtain ⟨sb, hsb⟩ := liftPoly c.sb fun x hx => by simp [ShapeCert.coeffSet, hx]
  obtain ⟨qu, hqu⟩ := liftPoly c.qu fun x hx => by simp [ShapeCert.coeffSet, hx]
  obtain ⟨v, hv⟩ := liftMv c.v fun x hx => by simp [ShapeCert.coeffSet, hx]
  have hw : ∀ z, ∃ p : Polynomial S, p.map ψ = c.w z := fun z => liftPoly _ fun x hx => inZ z (by simp [hx])
  have hqs : ∀ z, ∃ p : Polynomial S, p.map ψ = c.qs z := fun z => liftPoly _ fun x hx => inZ z (by simp [hx])
  have hAχ : ∀ z, ∃ p, MvPolynomial.map ψ p = c.Aχ z := fun z => liftMv _ fun x hx => inZ z (by simp [hx])
  have hAδ : ∀ z, ∃ p, MvPolynomial.map ψ p = c.Aδ z := fun z => liftMv _ fun x hx => inZ z (by simp [hx])
  have hAw : ∀ z z', ∃ p, MvPolynomial.map ψ p = c.Aw z z' := fun z z' => liftMv _ fun x hx =>
    inZ z (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z', Finset.mem_univ _, hx⟩))
  choose w hw using hw
  choose qs hqs using hqs
  choose Aχ hAχ using hAχ
  choose Aδ hAδ using hAδ
  choose Aw hAw using hAw
  have hwf : (fun z => (w z).map ψ) = c.w := funext hw
  refine ⟨{
    u := u
    χ := χ
    monic := Polynomial.monic_of_injective hψ (hχ ▸ c.monic)
    natDegree_eq := (Polynomial.natDegree_map_eq_of_injective hψ χ).symm.trans (hχ ▸ c.natDegree_eq)
    sa := sa
    sb := sb
    sep := ?_
    w := w
    qs := qs
    sys_eq := ?_
    qu := qu
    u_eq := ?_
    Aχ := Aχ
    χ_eq := ?_
    Aw := Aw
    w_eq := ?_
    v := v
    Aδ := Aδ
    δ_eq := ?_ }⟩
  · apply Polynomial.map_injective ψ hψ
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      hχ, hsa, hsb, c.sep, Polynomial.map_one]
  · intro z
    apply Polynomial.map_injective ψ hψ
    rw [map_mvEval₂, hwf, map_ratSystem, c.sys_eq, Polynomial.map_mul, hχ, hqs]
  · apply Polynomial.map_injective ψ hψ
    rw [Polynomial.map_sub, map_mvEval₂, hwf, hu, Polynomial.map_X, c.u_eq, Polynomial.map_mul, hχ,
      hqu]
  · apply MvPolynomial.map_injective ψ hψ
    rw [map_polyEval₂, hu, hχ, c.χ_eq, map_sum]
    simp only [map_mul, map_ratSystem, hAχ]
  · intro z
    apply MvPolynomial.map_injective ψ hψ
    rw [map_sub, map_X, map_polyEval₂, hu, hw, c.w_eq, map_sum]
    simp only [map_mul, map_ratSystem, hAw]
  · apply MvPolynomial.map_injective ψ hψ
    rw [map_sub, map_mul, map_one, map_rename, map_jacDet, hv, c.δ_eq, map_sum]
    simp only [map_mul, map_ratSystem, hAδ]

end Lift

/-! ### Main theorem -/

/-- **Generic fiber constancy.** If an injective θ₀ to an algebraically closed characteristic-zero field has a finite fiber of exactly Q simple solutions, some nonzero g∈R guarantees exactly Q simple solutions over every algebraically closed θ with θ(g)≠0. -/
theorem generic_fiber_constancy {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ι → MvPolynomial ι R) (D : MvPolynomial ι R) (Q : ℕ)
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (θ₀ : R →+* Ω)
    (hθ₀ : Function.Injective θ₀) (hfin : Finite (SystemSolutions f D θ₀))
    (hcard : Nat.card (SystemSolutions f D θ₀) = Q)
    (hsimple : ∀ y : SystemSolutions f D θ₀, IsSimpleAt f θ₀ y.1) :
    ∃ g : R, g ≠ 0 ∧ ∀ (κ : Type x) [Field κ] [IsAlgClosed κ] (θ : R →+* κ), θ g ≠ 0 →
      Nat.card (SystemSolutions f D θ) = Q ∧ ∀ y : SystemSolutions f D θ, IsSimpleAt f θ y.1 := by
  classical
  have : IsDomain R := hθ₀.isDomain θ₀
  let φ : (FractionRing R) →+* Ω := IsFractionRing.lift hθ₀
  let _ : Algebra (FractionRing R) Ω := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (FractionRing R) Ω (algebraMap R (FractionRing R) r) = θ₀ r := IsFractionRing.lift_algebraMap hθ₀
  have hmapF : ∀ p : MvPolynomial ι R,
      map (algebraMap (FractionRing R) Ω) (map (algebraMap R (FractionRing R)) p) = map θ₀ p := by
    intro p
    rw [map_map, show (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) = θ₀ from RingHom.ext hφ]
  let fF : ι → MvPolynomial ι (FractionRing R) := fun i => map (algebraMap R (FractionRing R)) (f i)
  let DF : MvPolynomial ι (FractionRing R) := map (algebraMap R (FractionRing R)) D
  have hpred : ∀ y : ι → Ω, ((∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0) ↔
      ((∀ i, eval y (map θ₀ (f i)) = 0) ∧ eval y (map θ₀ D) ≠ 0) := by
    intro y
    simp only [fF, DF, hmapF]
  let eqv := Equiv.subtypeEquivRight hpred
  have : Finite {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0} := Finite.of_equiv _ eqv.symm
  have hcardF : Nat.card {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0} = Q := (Nat.card_congr eqv).trans hcard
  have hsimpleF : ∀ y : {y : ι → Ω // (∀ i, eval y (map (algebraMap (FractionRing R) Ω) (fF i)) = 0) ∧
      eval y (map (algebraMap (FractionRing R) Ω) DF) ≠ 0},
      (Matrix.of fun i j => eval y.1 (pderiv j (map (algebraMap (FractionRing R) Ω) (fF i)))).det ≠ 0 := by
    intro y
    have := hsimple ⟨y.1, (hpred y.1).1 y.2⟩
    simpa only [IsSimpleAt, fF, hmapF] using this
  obtain ⟨cF⟩ := exists_shapeCert fF DF hsimpleF
  rw [hcardF] at cF
  -- Choose a common denominator g.
  obtain ⟨⟨g, hg⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    cF.coeffSet
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  let Rg := Localization.Away g
  have hgu : IsUnit (algebraMap R (FractionRing R) g) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hg0)
  let ψ : Rg →+* (FractionRing R) := IsLocalization.Away.lift g hgu
  have hψ_alg : ∀ r : R, ψ (algebraMap R Rg r) = algebraMap R (FractionRing R) r :=
    IsLocalization.Away.lift_eq g hgu
  have hψ_inv : ψ (IsLocalization.Away.invSelf g) = (algebraMap R (FractionRing R) g)⁻¹ := by
    have h1 := congrArg ψ (IsLocalization.Away.mul_invSelf (S := Rg) g)
    rw [map_mul, map_one, hψ_alg] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers g) a
    have hr : algebraMap R (FractionRing R) r = 0 := by
      rw [← hψ_alg, ← hrm, map_mul, ha, zero_mul]
    have hr0 : r = 0 := (map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))).1 hr
    rw [hr0, map_zero] at hrm
    exact (IsLocalization.map_units Rg m).mul_left_eq_zero.1 hrm
  have hrange : ↑cF.coeffSet ⊆ Set.range ψ := by
    intro a ha
    obtain ⟨r, hr⟩ := hint a ha
    refine ⟨algebraMap R Rg r * IsLocalization.Away.invSelf g, ?_⟩
    rw [map_mul, hψ_alg, hψ_inv, hr, Algebra.smul_def]
    field_simp [hgu.ne_zero]
  -- Certificate over R[1/g].
  let fg : ι → MvPolynomial ι Rg := fun i => map (algebraMap R Rg) (f i)
  let Dg : MvPolynomial ι Rg := map (algebraMap R Rg) D
  have hψcomp : ψ.comp (algebraMap R Rg) = algebraMap R (FractionRing R) := IsLocalization.Away.lift_comp g hgu
  have hfg : (fun i => map ψ (fg i)) = fF := by
    funext i
    simp only [fg, fF, map_map, hψcomp]
  have hDg : map ψ Dg = DF := by simp only [Dg, DF, map_map, hψcomp]
  obtain ⟨cg⟩ := ShapeCert.lift ψ hψ_inj fg Dg hfg hDg cF hrange
  refine ⟨g, hg0, fun κ _ _ θ hθg => ?_⟩
  -- Specialization to κ.
  have hθu : IsUnit (θ g) := isUnit_iff_ne_zero.2 hθg
  let θg : Rg →+* κ := IsLocalization.Away.lift g hθu
  have hθcomp : θg.comp (algebraMap R Rg) = θ := IsLocalization.Away.lift_comp g hθu
  have cκ := cg.map θg
  have hfκ : (fun i => map θg (fg i)) = fun i => map θ (f i) := by
    funext i
    simp only [fg, map_map, hθcomp]
  have hDκ : map θg Dg = map θ D := by simp only [Dg, map_map, hθcomp]
  rw [hfκ, hDκ] at cκ
  exact ⟨cκ.card_eq, fun y => cκ.det_ne_zero y.2.1 y.2.2⟩

end BPFixedPoints.BP
