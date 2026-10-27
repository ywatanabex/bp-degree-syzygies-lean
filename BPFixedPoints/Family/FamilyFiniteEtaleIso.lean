import BPFixedPoints.Family.FamilyFiniteEtaleCert
import BPFixedPoints.Family.Points
import BPFixedPoints.Degree.Main

/-!
# The admissible BP family over a principal open set of the parameter space

Let R=ℂ[a,b] (variables a_e, b_i; `MvPolynomial (E ⊕ V) ℂ`) and let
`paramToFamily : R → A_G` be the coordinate-ring map of the projection
π_G : 𝒳_G → P_G, where A_G is `FamilyRing`. For s∈R the ring
B_s=A_G[1/π_G(s)] (`FamilyAway`) is an algebra over R[1/s]
(`familyAwayAlgebra`); Spec B_s=π_G⁻¹(D(s)). The shortcut instance
`familyRingSelfAction` keeps instance search for modules over localizations
of A_G from timing out.

* `famSplit` separates parameters from messages; `paramResidual` and
  `paramDen` are the residuals f_α and the full denominator ∏a·∏b·D as
  polynomials in the messages over R. At a field point with nonzero
  parameters, their solutions with nonzero denominator are the admissible BP
  solutions (`split_solution_iff`), and simplicity is nonvanishing of the BP
  Jacobian (`split_isSimpleAt_iff`).
* `exists_paramShapeCert`: for loopless G some nonzero g∈R carries a shape
  certificate of degree Q(G) for this system over R[1/g]. The input is the
  counting theorem `exists_generic_count_eq_Q` with
  `isSimpleSolution_of_isSimpleAuxSolution`, applied at the generic point
  R→(algebraic closure of Frac R), and `exists_shapeCert_away`.
* `certEquivFamilyAway`: a certificate (u,χ,w,…) over S=R[1/s] gives an
  S-algebra isomorphism S[Y]/(χ)≅B_s, Y↦u(y,1/(∏a·∏b·D)). Hence
  `familyAway_finite_etale_of_cert`: B_s is finite, free of rank deg χ and
  étale over S.

The main statements are in `FamilyFiniteEtale.lean`.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial BP
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-! ### Parameter ring and the projection π_G -/

/-- Parameter coordinates (a_e,b_i) among the total-space variables. -/
def famParamVar : E ⊕ V → FamVar V E := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)

/-- The projection π_G on coordinate rings: ℂ[a,b]→A_G, a_e↦a_e, b_i↦b_i. -/
noncomputable def paramToFamily : MvPolynomial (E ⊕ V) ℂ →+* G.FamilyRing :=
  (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing).comp (rename famParamVar).toRingHom

/-- Shortcut instance: A_G acts on itself by multiplication. Without it, instance search for
modules over localizations of A_G times out. -/
noncomputable instance familyRingSelfAction : DistribMulAction G.FamilyRing G.FamilyRing :=
  Module.toDistribMulAction

/-- Coordinate ring of π_G⁻¹(D(s)): the family ring with the image of s∈ℂ[a,b] inverted. -/
abbrev FamilyAway (s : MvPolynomial (E ⊕ V) ℂ) := Localization.Away (G.paramToFamily s)

/-- B_s is an algebra over ℂ[a,b][1/s] through π_G. -/
noncomputable instance familyAwayAlgebra (s : MvPolynomial (E ⊕ V) ℂ) :
    Algebra (Localization.Away s) (G.FamilyAway s) :=
  (Localization.awayMap G.paramToFamily s).toAlgebra

/-- Split the total-space variables into parameters and messages: ℂ[a,b,y]→ℂ[a,b][y]. -/
noncomputable def famSplit :
    MvPolynomial (FamVar V E) ℂ →ₐ[ℂ] MvPolynomial (Dart E) (MvPolynomial (E ⊕ V) ℂ) :=
  aeval (Sum.elim (fun e => C (X (Sum.inl e))) (Sum.elim (fun i => C (X (Sum.inr i))) X))

/-- The BP residual f_α as a polynomial in the messages over ℂ[a,b]. -/
noncomputable def paramResidual (α : Dart E) : MvPolynomial (Dart E) (MvPolynomial (E ⊕ V) ℂ) :=
  famSplit (G.famResidual α)

/-- The admissibility denominator ∏a·∏b·D as a polynomial in the messages over ℂ[a,b]. -/
noncomputable def paramDen : MvPolynomial (Dart E) (MvPolynomial (E ⊕ V) ℂ) :=
  famSplit G.famDen

theorem famSplit_rename (x : MvPolynomial (E ⊕ V) ℂ) :
    famSplit (V := V) (E := E) (rename famParamVar x) = C x := by
  have h : (famSplit (V := V) (E := E)).comp (rename famParamVar) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial (E ⊕ V) ℂ)
        (MvPolynomial (Dart E) (MvPolynomial (E ⊕ V) ℂ)) := by
    apply MvPolynomial.algHom_ext
    rintro (e | i) <;> simp [famSplit, famParamVar]
  have := congrArg (fun φ => φ x) h
  simpa using this

/-- Evaluating the split polynomial of p at a ring hom φ on ℂ[a,b] and messages pt. -/
theorem eval₂_famSplit {T : Type*} [CommRing T] (φ : MvPolynomial (E ⊕ V) ℂ →+* T)
    (pt : Dart E → T) (ψ : MvPolynomial (FamVar V E) ℂ →+* T)
    (hC : ∀ c : ℂ, ψ (C c) = φ (C c)) (ha : ∀ e, ψ (famA e) = φ (X (Sum.inl e)))
    (hb : ∀ i, ψ (famB i) = φ (X (Sum.inr i))) (hy : ∀ α, ψ (famY α) = pt α)
    (p : MvPolynomial (FamVar V E) ℂ) :
    eval₂ φ pt (famSplit p) = ψ p := by
  have h : (eval₂Hom φ pt).comp (famSplit (V := V) (E := E)).toRingHom = ψ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [famSplit, hC, MvPolynomial.algebraMap_apply]
    · rintro (e | i | α)
      · simp [famSplit, ← ha e, famA]
      · simp [famSplit, ← hb i, famB]
      · simp [famSplit, ← hy α, famY]
  exact congrArg (fun f => f p) h


/-! ### Fibers of the split system -/

section Fibers

variable {K : Type*} [Field K] (θ : MvPolynomial (E ⊕ V) ℂ →+* K)

theorem map_paramResidual (α : Dart E) :
    map θ (G.paramResidual α) =
      G.bpMvPoly (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))) α := by
  simp [paramResidual, famResidual, famCavity, famSplit, famA, famB, famY, bpMvPoly, cavityPoly,
    map_prod]

theorem eval_map_paramDen (y : Dart E → K) :
    eval y (map θ G.paramDen) =
      (∏ e, θ (X (Sum.inl e))) * (∏ i, θ (X (Sum.inr i))) * (∏ α, y α) *
        (∏ α, (G.cavity (fun i => θ (X (Sum.inr i))) y α + θ (X (Sum.inl α.1)))) *
        ∏ i, (1 + G.totalField (fun i => θ (X (Sum.inr i))) y i) := by
  simp [paramDen, famDen, famCavity, famTotalField, famSplit, famA, famB, famY, map_prod, cavity,
    totalField]

/-- At nonzero parameters, solutions of the split system with nonzero denominator are exactly the admissible BP solutions. -/
theorem split_solution_iff (ha : ∀ e, θ (X (Sum.inl e)) ≠ 0) (hb : ∀ i, θ (X (Sum.inr i)) ≠ 0)
    (y : Dart E → K) :
    ((∀ α, eval y (map θ (G.paramResidual α)) = 0) ∧ eval y (map θ G.paramDen) ≠ 0) ↔
      G.IsAdmissibleSolution (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))) y := by
  simp only [map_paramResidual, eval_map_paramDen, IsAdmissibleSolution, Admissible,
    ← isFixedPoint_iff_eval, ne_eq, mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, not_or, not_exists]
  simp [ha, hb, and_assoc]

/-- Simplicity in the split system is simplicity of the BP Jacobian. -/
theorem split_isSimpleAt_iff (y : Dart E → K) :
    IsSimpleAt G.paramResidual θ y ↔
      G.IsSimpleSolution (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))) y := by
  simp only [IsSimpleAt, IsSimpleSolution, map_paramResidual]
  rfl

end Fibers

/-! ### A shape certificate for the split BP system -/

/-- The generic parameter point: ℂ[a,b] into an algebraic closure of ℂ(a,b). -/
noncomputable def genericParam :
    MvPolynomial (E ⊕ V) ℂ →+* AlgebraicClosure (FractionRing (MvPolynomial (E ⊕ V) ℂ)) :=
  (algebraMap (FractionRing (MvPolynomial (E ⊕ V) ℂ))
    (AlgebraicClosure (FractionRing (MvPolynomial (E ⊕ V) ℂ)))).comp
    (algebraMap (MvPolynomial (E ⊕ V) ℂ) (FractionRing (MvPolynomial (E ⊕ V) ℂ)))

theorem genericParam_injective : Function.Injective (genericParam (E := E) (V := V)) :=
  (algebraMap (FractionRing (MvPolynomial (E ⊕ V) ℂ))
    (AlgebraicClosure (FractionRing (MvPolynomial (E ⊕ V) ℂ)))).injective.comp
    (IsFractionRing.injective _ _)

/-- **Certificate over ℂ[a,b][1/g].** For a loopless graph, some nonzero g∈ℂ[a,b] carries a shape certificate of degree Q(G) for the split BP system (f_α, ∏a·∏b·D). -/
theorem exists_paramShapeCert (hG : G.Loopless) :
    ∃ g : MvPolynomial (E ⊕ V) ℂ, g ≠ 0 ∧
      Nonempty (ShapeCert (fun α => map (algebraMap _ (Localization.Away g)) (G.paramResidual α))
        (map (algebraMap _ (Localization.Away g)) G.paramDen) G.Q) := by
  obtain ⟨P, hP0, hP⟩ := G.exists_generic_count_eq_Q hG
  set θ := genericParam (E := E) (V := V) with hθdef
  have hθ : Function.Injective θ := genericParam_injective
  have ha : ∀ e, θ (X (Sum.inl e)) ≠ 0 := fun e h =>
    X_ne_zero (R := ℂ) (Sum.inl e) (hθ (by rw [map_zero]; exact h))
  have hb : ∀ i, θ (X (Sum.inr i)) ≠ 0 := fun i h =>
    X_ne_zero (R := ℂ) (Sum.inr i) (hθ (by rw [map_zero]; exact h))
  have hPne : eval (Sum.elim (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))))
      (map (Int.castRingHom _) P) ≠ 0 := by
    have hfun : Sum.elim (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))) =
        θ ∘ X := by
      funext j; rcases j with e | i <;> rfl
    have hev : eval (θ ∘ X) (map (Int.castRingHom _) P) = θ (map (Int.castRingHom ℂ) P) := by
      have h : eval₂Hom (Int.castRingHom _) (θ ∘ X) = θ.comp (map (Int.castRingHom ℂ)) := by
        apply MvPolynomial.ringHom_ext
        · intro n; simp
        · intro j; simp
      rw [eval_map, ← coe_eval₂Hom, h]
      rfl
    rw [hfun, hev]
    intro h
    apply hP0
    apply MvPolynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    rw [map_zero]
    exact hθ (by rw [h, map_zero])
  obtain ⟨hcard, hsimp⟩ := hP _ _ _ ha hb hPne
  let eqv : SystemSolutions G.paramResidual G.paramDen θ ≃
      {y // G.IsAdmissibleSolution (fun e => θ (X (Sum.inl e))) (fun i => θ (X (Sum.inr i))) y} :=
    Equiv.subtypeEquivRight fun y => G.split_solution_iff θ ha hb y
  have hcard' : Nat.card (SystemSolutions G.paramResidual G.paramDen θ) = G.Q :=
    (Nat.card_congr eqv).trans hcard
  refine exists_shapeCert_away G.paramResidual G.paramDen G.Q θ hθ
    (Nat.finite_of_card_ne_zero (by rw [hcard']; exact G.Q_pos.ne')) hcard' fun y => ?_
  have hy := (G.split_solution_iff θ ha hb y.1).1 y.2
  exact (G.split_isSimpleAt_iff θ y.1).2
    (G.isSimpleSolution_of_isSimpleAuxSolution _ _ y.1 hG ha hb hy (hsimp y.1 hy))


/-! ### The localized family ring B_s -/

section Away

variable (s : MvPolynomial (E ⊕ V) ℂ)

/-- The composite ℂ[a,b,y]→A_G→B_s. -/
noncomputable def toFamilyAway : MvPolynomial (FamVar V E) ℂ →+* G.FamilyAway s :=
  (algebraMap G.FamilyRing (G.FamilyAway s)).comp (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing)

theorem toFamilyAway_den_unit : IsUnit (G.toFamilyAway s G.famDen) :=
  G.familyRing_den_unit.map (algebraMap G.FamilyRing (G.FamilyAway s))

theorem toFamilyAway_residual (α : Dart E) : G.toFamilyAway s (G.famResidual α) = 0 := by
  rw [toFamilyAway, RingHom.comp_apply, G.familyRing_residual α, map_zero]

theorem familyAway_algebraMap (x : MvPolynomial (E ⊕ V) ℂ) :
    algebraMap (Localization.Away s) (G.FamilyAway s)
        (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s) x) =
      algebraMap G.FamilyRing (G.FamilyAway s) (G.paramToFamily x) := by
  rw [RingHom.algebraMap_toAlgebra]
  exact IsLocalization.map_eq _ _

theorem paramToFamily_eq (x : MvPolynomial (E ⊕ V) ℂ) :
    G.paramToFamily x =
      algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing (rename famParamVar x) := rfl

/-- B_s evaluates split polynomials at its own messages. -/
theorem eval₂_famSplit_familyAway (p : MvPolynomial (FamVar V E) ℂ) :
    eval₂ ((algebraMap (Localization.Away s) (G.FamilyAway s)).comp
        (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s)))
      (fun α => G.toFamilyAway s (famY α)) (famSplit p) = G.toFamilyAway s p := by
  apply eval₂_famSplit
  · intro c
    rw [RingHom.comp_apply, familyAway_algebraMap, paramToFamily_eq G (C c), rename_C]
    rfl
  · intro e
    rw [RingHom.comp_apply, familyAway_algebraMap, paramToFamily_eq G (X (Sum.inl e)), rename_X]
    rfl
  · intro i
    rw [RingHom.comp_apply, familyAway_algebraMap, paramToFamily_eq G (X (Sum.inr i)), rename_X]
    rfl
  · intro α
    rfl

/-- The Rabinowitsch point (y,1/(∏a·∏b·D)) of B_s. -/
noncomputable def familyAwayPoint : Option (Dart E) → G.FamilyAway s :=
  fun z => Option.elim z (↑(G.toFamilyAway_den_unit s).unit⁻¹) fun α => G.toFamilyAway s (famY α)

theorem familyAwayPoint_ratSystem (z : Option (Dart E)) :
    eval₂ (algebraMap (Localization.Away s) (G.FamilyAway s)) (G.familyAwayPoint s)
      (ratSystem (fun α => map (algebraMap _ (Localization.Away s)) (G.paramResidual α))
        (map (algebraMap _ (Localization.Away s)) G.paramDen) z) = 0 := by
  have key : ∀ p, eval₂ (algebraMap (Localization.Away s) (G.FamilyAway s))
      (G.familyAwayPoint s ∘ some)
      (map (algebraMap _ (Localization.Away s)) (famSplit p)) = G.toFamilyAway s p := by
    intro p
    rw [eval₂_map]
    exact G.eval₂_famSplit_familyAway s p
  cases z with
  | some α =>
    simp only [ratSystem, eval₂_rename]
    rw [paramResidual, key, toFamilyAway_residual]
  | none =>
    simp only [ratSystem, eval₂_sub, eval₂_mul, eval₂_X, eval₂_rename, eval₂_one]
    rw [paramDen, key]
    simp [familyAwayPoint]

theorem familyAwayPoint_none_mul :
    G.familyAwayPoint s none * G.toFamilyAway s G.famDen = 1 := by
  simp [familyAwayPoint]

end Away

/-! ### A certificate makes B_s monogenic -/

section Monogenic

variable {G} {s : MvPolynomial (E ⊕ V) ℂ} {Q : ℕ}
  (c : ShapeCert (fun α => map (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s))
      (G.paramResidual α)) (map (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s))
      G.paramDen) Q)

theorem eval₂_polyEval₂' {S T : Type*} [CommRing S] [CommRing T] {ι : Type*} (i : S →+* T)
    (pt : ι → T) (u : MvPolynomial ι S) (p : Polynomial S) :
    eval₂ i pt (Polynomial.eval₂ C u p) = Polynomial.eval₂ i (eval₂ i pt u) p := by
  rw [← coe_eval₂Hom, Polynomial.hom_eval₂, eval₂Hom_comp_C]

theorem eval₂_sum_ratSystem {S T : Type*} [CommRing S] [CommRing T] {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial ι S) (D : MvPolynomial ι S) (i : S →+* T) (pt : Option ι → T)
    (h : ∀ z, eval₂ i pt (ratSystem f D z) = 0) (A : Option ι → MvPolynomial (Option ι) S) :
    eval₂ i pt (∑ z, A z * ratSystem f D z) = 0 := by
  rw [← coe_eval₂Hom, map_sum]
  simp only [map_mul, coe_eval₂Hom, h, mul_zero, Finset.sum_const_zero]

/-- The image u(y,1/D) of the separating element in B_s. -/
noncomputable def certRoot : G.FamilyAway s :=
  eval₂ (algebraMap (Localization.Away s) (G.FamilyAway s)) (G.familyAwayPoint s) c.u

theorem certRoot_χ :
    Polynomial.eval₂ (algebraMap (Localization.Away s) (G.FamilyAway s)) (certRoot c) c.χ = 0 := by
  rw [certRoot, ← eval₂_polyEval₂', c.χ_eq]
  exact eval₂_sum_ratSystem _ _ _ _ (G.familyAwayPoint_ratSystem s) _

/-- S[Y]/(χ)→B_s, Y↦u(y,1/D). -/
noncomputable def certToFamilyAway : AdjoinRoot c.χ →+* G.FamilyAway s :=
  AdjoinRoot.lift (algebraMap (Localization.Away s) (G.FamilyAway s)) (certRoot c) (certRoot_χ c)

/-- The certificate point w(Y) of S[Y]/(χ). -/
noncomputable def certPoint : Option (Dart E) → AdjoinRoot c.χ :=
  fun z => AdjoinRoot.mk c.χ (c.w z)

theorem certPoint_ratSystem (z : Option (Dart E)) :
    eval₂ (AdjoinRoot.of c.χ) (certPoint c)
      (ratSystem (fun α => map (algebraMap _ (Localization.Away s)) (G.paramResidual α))
        (map (algebraMap _ (Localization.Away s)) G.paramDen) z) = 0 := by
  have h := congrArg (AdjoinRoot.mk c.χ) (c.sys_eq z)
  rw [map_mul, AdjoinRoot.mk_self, zero_mul, eval₂_comp_left] at h
  exact h

/-- ℂ[a,b,y]→S[Y]/(χ), y_α↦w_α(Y). -/
noncomputable def certPolyHom : MvPolynomial (FamVar V E) ℂ →+* AdjoinRoot c.χ :=
  (eval₂Hom ((AdjoinRoot.of c.χ).comp (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s)))
    (certPoint c ∘ some)).comp (famSplit (V := V) (E := E)).toRingHom

theorem certPolyHom_apply (p : MvPolynomial (FamVar V E) ℂ) :
    certPolyHom c p = eval₂ (AdjoinRoot.of c.χ) (certPoint c ∘ some)
      (map (algebraMap _ (Localization.Away s)) (famSplit p)) := by
  rw [eval₂_map]
  rfl

theorem certPolyHom_residual (α : Dart E) : certPolyHom c (G.famResidual α) = 0 := by
  rw [certPolyHom_apply, ← eval₂_rename]
  exact certPoint_ratSystem c (some α)

theorem certPolyHom_den : certPoint c none * certPolyHom c G.famDen = 1 := by
  have h := certPoint_ratSystem c none
  simp only [ratSystem, eval₂_sub, eval₂_mul, eval₂_X, eval₂_rename, eval₂_one, sub_eq_zero] at h
  rw [certPolyHom_apply]
  exact h

theorem certPolyHom_den_unit : IsUnit (certPolyHom c G.famDen) :=
  IsUnit.of_mul_eq_one_right _ (certPolyHom_den c)

/-- A_G→S[Y]/(χ) induced by the certificate point. -/
noncomputable def certFamilyHom : G.FamilyRing →+* AdjoinRoot c.χ :=
  Ideal.Quotient.lift _ (IsLocalization.Away.lift G.famDen (certPolyHom_den_unit c)) (by
    intro a ha
    refine RingHom.mem_ker.1 ((Ideal.span_le (I := RingHom.ker _)).2 ?_ ha)
    rintro _ ⟨α, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, IsLocalization.Away.lift_eq]
    exact certPolyHom_residual c α)

theorem certFamilyHom_algebraMap (p : MvPolynomial (FamVar V E) ℂ) :
    certFamilyHom c (algebraMap (MvPolynomial (FamVar V E) ℂ) G.FamilyRing p) = certPolyHom c p := by
  change certFamilyHom c (Ideal.Quotient.mk _ (algebraMap _ (Localization.Away G.famDen) p)) = _
  rw [certFamilyHom, Ideal.Quotient.lift_mk, IsLocalization.Away.lift_eq]

theorem certFamilyHom_param (x : MvPolynomial (E ⊕ V) ℂ) :
    certFamilyHom c (G.paramToFamily x) =
      AdjoinRoot.of c.χ (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away s) x) := by
  rw [paramToFamily_eq G x, certFamilyHom_algebraMap, certPolyHom, RingHom.comp_apply]
  change eval₂ _ _ (famSplit (rename famParamVar x)) = _
  rw [famSplit_rename, eval₂_C]
  rfl

/-- B_s→S[Y]/(χ), inverse to `certToFamilyAway`. -/
noncomputable def familyAwayToCert : G.FamilyAway s →+* AdjoinRoot c.χ :=
  IsLocalization.Away.lift (G.paramToFamily s) (g := certFamilyHom c) (by
    rw [certFamilyHom_param]
    exact (IsLocalization.Away.algebraMap_isUnit s).map _)

theorem familyAwayToCert_algebraMap (x : G.FamilyRing) :
    familyAwayToCert c (algebraMap G.FamilyRing (G.FamilyAway s) x) = certFamilyHom c x :=
  IsLocalization.Away.lift_eq _ _ _

theorem familyAwayToCert_toFamilyAway (p : MvPolynomial (FamVar V E) ℂ) :
    familyAwayToCert c (G.toFamilyAway s p) = certPolyHom c p := by
  rw [toFamilyAway, RingHom.comp_apply, familyAwayToCert_algebraMap, certFamilyHom_algebraMap]

theorem familyAwayToCert_comp_algebraMap :
    (familyAwayToCert c).comp (algebraMap (Localization.Away s) (G.FamilyAway s)) =
      AdjoinRoot.of c.χ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  ext x
  · simp only [RingHom.comp_apply, familyAway_algebraMap, familyAwayToCert_algebraMap,
      certFamilyHom_param]
  · simp only [RingHom.comp_apply, familyAway_algebraMap, familyAwayToCert_algebraMap,
      certFamilyHom_param]

theorem certToFamilyAway_certPoint (z : Option (Dart E)) :
    certToFamilyAway c (certPoint c z) = G.familyAwayPoint s z := by
  rw [certPoint, certToFamilyAway, AdjoinRoot.lift_mk, certRoot, ← eval₂_polyEval₂']
  have h := congrArg (eval₂ (algebraMap (Localization.Away s) (G.FamilyAway s))
    (G.familyAwayPoint s)) (c.w_eq z)
  rw [eval₂_sub, eval₂_X, eval₂_sum_ratSystem _ _ _ _ (G.familyAwayPoint_ratSystem s),
    sub_eq_zero] at h
  exact h.symm

theorem certToFamilyAway_comp_of :
    (certToFamilyAway c).comp (AdjoinRoot.of c.χ) =
      algebraMap (Localization.Away s) (G.FamilyAway s) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, certToFamilyAway, AdjoinRoot.lift_of]

theorem certToFamilyAway_certPolyHom (p : MvPolynomial (FamVar V E) ℂ) :
    certToFamilyAway c (certPolyHom c p) = G.toFamilyAway s p := by
  rw [certPolyHom_apply, eval₂_comp_left, certToFamilyAway_comp_of, eval₂_map]
  have h2 : (certToFamilyAway c) ∘ (certPoint c ∘ some) = fun α => G.toFamilyAway s (famY α) := by
    funext α
    exact certToFamilyAway_certPoint c (some α)
  rw [h2, G.eval₂_famSplit_familyAway s p]

theorem familyAwayToCert_familyAwayPoint (z : Option (Dart E)) :
    familyAwayToCert c (G.familyAwayPoint s z) = certPoint c z := by
  cases z with
  | some α =>
    change familyAwayToCert c (G.toFamilyAway s (famY α)) = _
    rw [familyAwayToCert_toFamilyAway, certPolyHom_apply]
    simp [famSplit, famY]
  | none =>
    have h1 : familyAwayToCert c (G.familyAwayPoint s none) * certPolyHom c G.famDen = 1 := by
      rw [← familyAwayToCert_toFamilyAway, ← map_mul, G.familyAwayPoint_none_mul s, map_one]
    have h2 := certPolyHom_den c
    linear_combination (certPoint c none) * h1 -
      (familyAwayToCert c (G.familyAwayPoint s none)) * h2

theorem certToFamilyAway_comp_familyAwayToCert :
    (certToFamilyAway c).comp (familyAwayToCert c) = RingHom.id (G.FamilyAway s) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (G.paramToFamily s))
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers G.famDen)
  refine RingHom.ext fun p => ?_
  change certToFamilyAway c (familyAwayToCert c (G.toFamilyAway s p)) = G.toFamilyAway s p
  rw [familyAwayToCert_toFamilyAway, certToFamilyAway_certPolyHom]

theorem familyAwayToCert_comp_certToFamilyAway :
    (familyAwayToCert c).comp (certToFamilyAway c) = RingHom.id (AdjoinRoot c.χ) := by
  apply AdjoinRoot.ringHom_ext
  · rw [RingHom.comp_assoc, certToFamilyAway_comp_of, familyAwayToCert_comp_algebraMap]
    rfl
  · rw [RingHom.comp_apply, certToFamilyAway, AdjoinRoot.lift_root, RingHom.id_apply, certRoot,
      eval₂_comp_left, familyAwayToCert_comp_algebraMap]
    have h : (familyAwayToCert c) ∘ (G.familyAwayPoint s) = certPoint c := by
      funext z
      exact familyAwayToCert_familyAwayPoint c z
    rw [h]
    have hu := congrArg (AdjoinRoot.mk c.χ) c.u_eq
    rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_eq_zero, eval₂_comp_left,
      AdjoinRoot.mk_X] at hu
    exact hu

/-- **B_s≅S[Y]/(χ).** A shape certificate over S=ℂ[a,b][1/s] identifies B_s with S[Y]/(χ) as S-algebras. -/
noncomputable def certEquivFamilyAway : AdjoinRoot c.χ ≃ₐ[Localization.Away s] G.FamilyAway s :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (certToFamilyAway c) (familyAwayToCert c)
      (certToFamilyAway_comp_familyAwayToCert c) (familyAwayToCert_comp_certToFamilyAway c))
    (fun x => by
      rw [AdjoinRoot.algebraMap_eq]
      exact RingHom.congr_fun (certToFamilyAway_comp_of c) x)

include c in
/-- **Finite étale from a certificate.** A degree-Q shape certificate over S=ℂ[a,b][1/s] makes B_s finite, free of rank Q and étale over S. -/
theorem familyAway_finite_etale_of_cert [Nontrivial (Localization.Away s)] :
    Module.Finite (Localization.Away s) (G.FamilyAway s) ∧
      Module.Free (Localization.Away s) (G.FamilyAway s) ∧
      Module.finrank (Localization.Away s) (G.FamilyAway s) = Q ∧
      Algebra.Etale (Localization.Away s) (G.FamilyAway s) := by
  let e := certEquivFamilyAway c
  have := adjoinRoot_finite c.monic
  have := adjoinRoot_free c.monic
  have := adjoinRoot_etale_of_bezout c.χ c.monic c.sa c.sb c.sep
  refine ⟨Module.Finite.equiv e.toLinearEquiv, Module.Free.of_equiv e.toLinearEquiv, ?_,
    Algebra.Etale.of_equiv e⟩
  rw [← e.toLinearEquiv.finrank_eq, finrank_adjoinRoot c.monic, c.natDegree_eq]

end Monogenic

end BPFixedPoints.Multigraph
