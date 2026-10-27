import BPFixedPoints.Degree.AuxPolySystem
import BPFixedPoints.Degree.Generic.FiberConstancy
import BPFixedPoints.Degree.Lift.Count
import BPFixedPoints.Degree.Boundary.ValuedFieldExists
import BPFixedPoints.Degree.Lift.Correspondence
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Reduction to generic parameters

1. Define `genericAux` over ℤ[s_e,β_i].
2. Let K be an algebraic closure of ℚ(s,β), put c_e=s_e−1 and let L be a
   Puiseux-type field over K. The map θ₀:ℤ[s,β]→L with s_e↦1+t c_e and
   β_i↦β_i is injective (§7 (25)): specialize t=1 and use algebraic independence.
3. `card_puiseuxSolutions` gives exactly Q solutions over θ₀; Hensel lifting
   gives their simplicity.
4. `generic_fiber_constancy` in `Degree/Generic/FiberConstancy.lean` gives a
   nonzero g∈ℤ[s,β] on whose nonvanishing locus every algebraically closed
   fiber has Q simple solutions (`exists_generic_aux_degree_eq_Q`). Both this
   result and `newtonPuiseux_exists` are proved theorems, not axioms.
5. Pull back by s_e=a_e², β_i=b_i/∏_{e∋i}a_e and take a nonzero numerator
   P in ℤ[a,b][1/∏a]. Where P≠0 there are exactly Q admissible BP solutions
   (`exists_generic_count_eq_Q`, using `card_admissible_eq_card_aux`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Parameter ring ℤ[s_e,β_i], with Sum.inl e representing s_e and Sum.inr i representing β_i. -/
abbrev ParamRing (E V : Type*) := MvPolynomial (E ⊕ V) ℤ

/-- Indeterminate s_e. -/
noncomputable def sGen : E → ParamRing E V := fun e => X (Sum.inl e)

/-- Indeterminate β_i. -/
noncomputable def βGen : V → ParamRing E V := fun i => X (Sum.inr i)

/-- Generic auxiliary system over ℤ[s,β]. -/
noncomputable def genericAux : Var V E → MvPolynomial (Var V E) (ParamRing E V) :=
  G.auxSystem sGen βGen

theorem map_genericAux {S : Type*} [CommRing S] (θ : ParamRing E V →+* S) (v : Var V E) :
    map θ (G.genericAux v) = G.auxSystem (θ ∘ sGen) (θ ∘ βGen) v :=
  G.map_auxSystem θ _ _ v

/-- Solutions after applying θ to generic coefficients are auxiliary solutions for parameters (θ s,θ β). -/
noncomputable def genericSolEquiv {κ : Type*} [Field κ] (θ : ParamRing E V →+* κ) :
    SystemSolutions G.genericAux (auxDen V E) θ ≃
      {p : (Dart E → κ) × (V → κ) // G.IsAuxSolution (θ ∘ sGen) (θ ∘ βGen) p.1 p.2} :=
  (Equiv.subtypeEquivRight (fun y => by
    simp only [map_genericAux, map_auxDen])).trans (G.auxSolEquiv _ _)

/-- Evaluation ℤ[s,β]→κ at (s,β). -/
noncomputable def evalParam {κ : Type*} [CommRing κ] (s : E → κ) (β : V → κ) :
    ParamRing E V →+* κ :=
  eval₂Hom (Int.castRingHom κ) (Sum.elim s β)

theorem evalParam_comp_sGen {κ : Type*} [CommRing κ] (s : E → κ) (β : V → κ) :
    evalParam s β ∘ sGen = s := by
  funext e
  simp [evalParam, sGen]

theorem evalParam_comp_βGen {κ : Type*} [CommRing κ] (s : E → κ) (β : V → κ) :
    evalParam s β ∘ βGen = β := by
  funext i
  simp [evalParam, βGen]

theorem evalParam_apply {κ : Type*} [CommRing κ] (s : E → κ) (β : V → κ) (p : ParamRing E V) :
    evalParam s β p = eval (Sum.elim s β) (map (Int.castRingHom κ) p) := by
  rw [evalParam, coe_eval₂Hom, eval_map]

/-! ### Solutions over a Puiseux-type valued field -/

section PuiseuxPoint

variable {K : Type*} [Field K] [DecidableEq K] (P : PuiseuxField K)

/-- Applying ofPS to the one-parameter system gives the auxiliary system with parameters (sP,βP). -/
theorem map_ofPS_weakSystem (c : E → K) (β : V → K) (v : Var V E) :
    map P.ofPS (G.weakSystem c β v) = G.auxSystem (sP P c) (βP P β) v := by
  rw [weakSystem_eq_auxSystem, map_auxSystem]
  have hs : (P.ofPS ∘ fun e => 1 + PowerSeries.X * PowerSeries.C (c e)) = sP P c := by
    funext e
    simp [sP_eq]
  have hb : (P.ofPS ∘ fun i => PowerSeries.C (β i)) = βP P β := by
    funext i
    simp [βP_eq]
  rw [hs, hb]

variable [IsAlgClosed K] [CharZero K] {θ : ParamRing E V →+* P.L} {c : E → K} {β : V → K}

/-- Over θ:ℤ[s,β]→L with s_e↦1+t c_e and β_i fixed, the generic system has exactly Q(G) solutions (`card_puiseuxSolutions`). -/
theorem card_systemSolutions_of_comp (hs : θ ∘ sGen = sP P c) (hb : θ ∘ βGen = βP P β)
    (hc : ∀ e, c e ≠ 0) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    Nat.card (SystemSolutions G.genericAux (auxDen V E) θ) = G.Q := by
  have e := G.genericSolEquiv θ
  rw [hs, hb] at e
  rw [Nat.card_congr e]
  exact G.card_puiseuxSolutions P c hc β hβ0 hβ1

/-- Every solution over this θ is simple: the Hensel lift has invertible Jacobian. -/
theorem isSimpleAt_of_comp (hs : θ ∘ sGen = sP P c) (hb : θ ∘ βGen = βP P β)
    (hc : ∀ e, c e ≠ 0) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1)
    (y : SystemSolutions G.genericAux (auxDen V E) θ) :
    IsSimpleAt G.genericAux θ y.1 := by
  have hsol : G.IsAuxSolution (sP P c) (βP P β) (fun α => y.1 (Sum.inl α))
      (fun i => y.1 (Sum.inr i)) := by
    have := (G.isAuxSolution_iff (θ ∘ sGen) (θ ∘ βGen) y.1).1
      (by simpa only [map_genericAux, map_auxDen] using y.2)
    rwa [hs, hb] at this
  obtain ⟨q, hq⟩ := G.exists_lift_of_puiseuxSolution P c β hc hβ0 hβ1
    ⟨(fun α => y.1 (Sum.inl α), fun i => y.1 (Sum.inr i)), hsol⟩
  have hq' := congrArg (fun p : G.PuiseuxSolutions P c β => p.1) hq
  simp only [toPuiseuxSolution, liftToPuiseux, Prod.mk.injEq] at hq'
  have hA : ∀ α, P.ofPS (G.liftOf c β hβ1 q (Sum.inl α)) = y.1 (Sum.inl α) :=
    fun α => congrFun hq'.1 α
  have hF : ∀ i, P.ofPS (G.liftOf c β hβ1 q (Sum.inr i)) = y.1 (Sum.inr i) :=
    fun i => congrFun hq'.2 i
  have hy : y.1 = P.ofPS ∘ G.liftOf c β hβ1 q := by
    funext v
    cases v with
    | inl α => exact (hA α).symm
    | inr i => exact (hF i).symm
  unfold IsSimpleAt
  rw [hy]
  have hdet : (Matrix.of fun i j => eval (P.ofPS ∘ G.liftOf c β hβ1 q)
      (pderiv j (map θ (G.genericAux i)))) =
      P.ofPS.mapMatrix (jacPS (G.weakSystem c β) (G.liftOf c β hβ1 q)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, jacPS]
    rw [map_genericAux, hs, hb, ← G.map_ofPS_weakSystem P, pderiv_map, ← map_eval']
  rw [hdet, ← RingHom.map_det]
  intro h0
  have hu := isUnit_det_jacPS (f := G.weakSystem c β)
    (G.det_jacRes_weakSystem_ne_zero (c := c) hβ1 q.2)
    (G.liftOf_spec c β hβ1 q).1
  exact hu.ne_zero (P.ofPS_injective (by rw [h0, map_zero]))

end PuiseuxPoint

/-! ### Transcendental parameter field and field embedding (Section 7) -/

section Univ

/-- Algebraic closure of ℚ(s,β), a characteristic-zero algebraically closed field containing the transcendental parameters. -/
abbrev UnivField (E V : Type*) := AlgebraicClosure (FractionRing (MvPolynomial (E ⊕ V) ℚ))

/-- Map from ℚ[s,β] through ℚ(s,β) into its algebraic closure. -/
noncomputable def toUniv : MvPolynomial (E ⊕ V) ℚ →+* UnivField E V :=
  (algebraMap (FractionRing (MvPolynomial (E ⊕ V) ℚ)) (UnivField E V)).comp
    (algebraMap (MvPolynomial (E ⊕ V) ℚ) (FractionRing (MvPolynomial (E ⊕ V) ℚ)))

theorem toUniv_injective : Function.Injective (toUniv (E := E) (V := V)) :=
  (algebraMap (FractionRing (MvPolynomial (E ⊕ V) ℚ)) (UnivField E V)).injective.comp
    (IsFractionRing.injective (MvPolynomial (E ⊕ V) ℚ) (FractionRing (MvPolynomial (E ⊕ V) ℚ)))

/-- Image of c_e=s_e-1. -/
noncomputable def cU : E → UnivField E V := fun e => toUniv (X (Sum.inl e) - 1)

/-- Image of β_i. -/
noncomputable def βU : V → UnivField E V := fun i => toUniv (X (Sum.inr i))

theorem X_sub_one_ne_zero (j : E ⊕ V) : (X j - 1 : MvPolynomial (E ⊕ V) ℚ) ≠ 0 := fun h => by
  have := congrArg (eval fun _ => (0 : ℚ)) h
  simp at this

theorem X_ne_neg_one (j : E ⊕ V) : (X j : MvPolynomial (E ⊕ V) ℚ) ≠ -1 := fun h => by
  have := congrArg (eval fun _ => (0 : ℚ)) h
  simp at this

theorem cU_ne_zero (e : E) : cU (V := V) e ≠ 0 := fun h =>
  X_sub_one_ne_zero (Sum.inl e) (toUniv_injective (by rw [map_zero]; exact h))

theorem βU_ne_zero (i : V) : βU (E := E) i ≠ 0 := fun h =>
  X_ne_zero (Sum.inr i) (toUniv_injective (by rw [map_zero]; exact h))

theorem βU_ne_neg_one (i : V) : βU (E := E) i ≠ -1 := fun h =>
  X_ne_neg_one (Sum.inr i) (toUniv_injective (by rw [map_neg, map_one]; exact h))

/-- ℤ[s,β] → K[X]：s_e ↦ 1 + X c_e、β_i ↦ β_i。 -/
noncomputable def ψPoly : ParamRing E V →+* Polynomial (UnivField E V) :=
  eval₂Hom (Int.castRingHom _)
    (Sum.elim (fun e => 1 + Polynomial.X * Polynomial.C (cU e)) (fun i => Polynomial.C (βU i)))

/-- ℤ[s,β] → K⟦X⟧：s_e ↦ 1 + X c_e、β_i ↦ β_i。 -/
noncomputable def ψPS : ParamRing E V →+* (UnivField E V)⟦X⟧ :=
  eval₂Hom (Int.castRingHom _)
    (Sum.elim (fun e => 1 + PowerSeries.X * PowerSeries.C (cU e))
      (fun i => PowerSeries.C (βU i)))

theorem ψPS_eq :
    (ψPS : ParamRing E V →+* _) = Polynomial.coeToPowerSeries.ringHom.comp ψPoly := by
  apply ringHom_ext
  · intro n
    simp [ψPS, ψPoly]
  · rintro (e | i)
    · simp only [ψPS, ψPoly, RingHom.comp_apply, eval₂Hom_X', Sum.elim_inl,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_add, Polynomial.coe_one,
        Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
    · simp only [ψPS, ψPoly, RingHom.comp_apply, eval₂Hom_X', Sum.elim_inr,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]

/-- Evaluation at t=1: s_e↦1+c_e=s_e and β_i↦β_i, the natural map ℤ[s,β]→ℚ[s,β]→K. -/
theorem evalRingHom_one_comp_ψPoly :
    (Polynomial.evalRingHom (1 : UnivField E V)).comp ψPoly =
      toUniv.comp (map (Int.castRingHom ℚ)) := by
  apply ringHom_ext
  · intro n
    simp [ψPoly]
  · rintro (e | i)
    · rw [RingHom.comp_apply, RingHom.comp_apply, ψPoly, eval₂Hom_X', Sum.elim_inl, map_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, one_mul, cU, map_sub, map_one]
      ring
    · rw [RingHom.comp_apply, RingHom.comp_apply, ψPoly, eval₂Hom_X', Sum.elim_inr, map_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
      rfl

theorem ψPoly_injective : Function.Injective (ψPoly (E := E) (V := V)) := by
  intro H H' h
  have h1 := congrArg (Polynomial.evalRingHom (1 : UnivField E V)) h
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, evalRingHom_one_comp_ψPoly,
    RingHom.comp_apply, RingHom.comp_apply] at h1
  exact map_injective _ Int.cast_injective (toUniv_injective h1)

theorem ψPS_injective : Function.Injective (ψPS (E := E) (V := V)) := by
  intro H H' h
  rw [ψPS_eq, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply] at h
  exact ψPoly_injective (Polynomial.coe_injective _ h)

section Puiseux

variable (P : PuiseuxField (UnivField E V)) [DecidableEq (UnivField E V)]

/-- Generic point θ₀:ℤ[s,β]→L, with s_e↦1+t c_e and β_i fixed (Section 7, (25)). -/
noncomputable def θ₀ : ParamRing E V →+* P.L := P.ofPS.comp ψPS

theorem θ₀_injective : Function.Injective (θ₀ P (E := E) (V := V)) :=
  P.ofPS_injective.comp ψPS_injective

theorem θ₀_comp_sGen : θ₀ P ∘ sGen = sP P (cU (E := E) (V := V)) := by
  funext e
  simp only [θ₀, Function.comp, RingHom.comp_apply, sGen, ψPS, eval₂Hom_X', Sum.elim_inl]
  exact (sP_eq P cU e).symm

theorem θ₀_comp_βGen : θ₀ P ∘ βGen = βP P (βU (E := E) (V := V)) := by
  funext i
  simp only [θ₀, Function.comp, RingHom.comp_apply, βGen, ψPS, eval₂Hom_X', Sum.elim_inr]
  exact (βP_eq P βU i).symm

/-- There are exactly Q(G) solutions over θ₀ (`card_puiseuxSolutions`). -/
theorem card_systemSolutions_θ₀ :
    Nat.card (SystemSolutions G.genericAux (auxDen V E) (θ₀ P)) = G.Q :=
  G.card_systemSolutions_of_comp P (θ₀_comp_sGen P) (θ₀_comp_βGen P) cU_ne_zero βU_ne_zero
    βU_ne_neg_one

/-- Every solution over θ₀ is simple, by invertibility of the Hensel-lift Jacobian. -/
theorem isSimpleAt_θ₀ (y : SystemSolutions G.genericAux (auxDen V E) (θ₀ P)) :
    IsSimpleAt G.genericAux (θ₀ P) y.1 :=
  G.isSimpleAt_of_comp P (θ₀_comp_sGen P) (θ₀_comp_βGen P) cU_ne_zero βU_ne_zero βU_ne_neg_one y

end Puiseux

end Univ

universe w

/-- **Core auxiliary statement.** There is a nonzero g∈ℤ[s,β] such that every algebraically closed fiber with g(s,β)≠0 has exactly Q(G) simple auxiliary solutions. Uses the proved theorems `generic_fiber_constancy` and `newtonPuiseux_exists`. -/
theorem exists_generic_aux_degree_eq_Q :
    ∃ g : MvPolynomial (E ⊕ V) ℤ, g ≠ 0 ∧
      ∀ (κ : Type w) [Field κ] [IsAlgClosed κ] (s : E → κ) (β : V → κ),
        eval (Sum.elim s β) (map (Int.castRingHom κ) g) ≠ 0 →
          Nat.card {p : (Dart E → κ) × (V → κ) // G.IsAuxSolution s β p.1 p.2} = G.Q ∧
          ∀ A F, G.IsAuxSolution s β A F → G.IsSimpleAuxSolution s β A F := by
  classical
  obtain ⟨P⟩ := newtonPuiseux_exists (UnivField E V)
  obtain ⟨g, hg0, hg⟩ := generic_fiber_constancy G.genericAux (auxDen V E) G.Q (θ₀ P)
    (θ₀_injective P)
    (Nat.finite_of_card_ne_zero (by rw [G.card_systemSolutions_θ₀ P]; exact G.Q_pos.ne'))
    (G.card_systemSolutions_θ₀ P) (G.isSimpleAt_θ₀ P)
  refine ⟨g, hg0, ?_⟩
  intro κ _ _ s β hsβ
  have hθg : evalParam s β g ≠ 0 := by
    rw [evalParam_apply]
    exact hsβ
  obtain ⟨hcard, hsimp⟩ := hg κ (evalParam s β) hθg
  have e := G.genericSolEquiv (evalParam s β)
  rw [evalParam_comp_sGen, evalParam_comp_βGen] at e
  refine ⟨(Nat.card_congr e).symm.trans hcard, ?_⟩
  intro A F hAF
  have hy : (∀ i, eval (Sum.elim A F) (map (evalParam s β) (G.genericAux i)) = 0) ∧
      eval (Sum.elim A F) (map (evalParam s β) (auxDen V E)) ≠ 0 := by
    simp only [map_genericAux, map_auxDen, evalParam_comp_sGen, evalParam_comp_βGen]
    exact (G.isAuxSolution_iff s β (Sum.elim A F)).2 hAF
  have := hsimp ⟨Sum.elim A F, hy⟩
  unfold IsSimpleAt at this
  simp only [map_genericAux, evalParam_comp_sGen, evalParam_comp_βGen] at this
  exact this

/-! ### Returning to the original parameters (a,b) -/

section BPParams

/-- Product of all edge parameters, product_e a_e in ℤ[a,b]. -/
noncomputable def allEdges (E V : Type*) [Fintype E] : MvPolynomial (E ⊕ V) ℤ :=
  ∏ e, X (Sum.inl e)

/-- Product over edges incident to vertex i. -/
noncomputable def incProd (i : V) : MvPolynomial (E ⊕ V) ℤ :=
  ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), X (Sum.inl e)

/-- Product over edges not incident to vertex i. -/
noncomputable def nonIncProd (i : V) : MvPolynomial (E ⊕ V) ℤ :=
  ∏ e ∈ Finset.univ.filter (fun e => ¬ G.Incident e i), X (Sum.inl e)

/-- Localization of ℤ[a,b] at product_e a_e. -/
abbrev LocRing (E V : Type*) [Fintype E] := Localization.Away (allEdges E V)

/-- χ : ℤ[s,β] → ℤ[a,b][1/∏a]、s_e ↦ a_e²、β_i ↦ b_i ∏_{e∌i} a_e / ∏_e a_e = b_i / ∏_{e∋i} a_e。 -/
noncomputable def chi : MvPolynomial (E ⊕ V) ℤ →+* LocRing E V :=
  eval₂Hom (algebraMap ℤ (LocRing E V))
    (Sum.elim (fun e => algebraMap (MvPolynomial (E ⊕ V) ℤ) (LocRing E V) (X (Sum.inl e)) ^ 2)
      (fun i => algebraMap (MvPolynomial (E ⊕ V) ℤ) (LocRing E V) (X (Sum.inr i) * G.nonIncProd i) *
        (IsLocalization.Away.invSelf (allEdges E V) : LocRing E V)))

variable {κ : Type*} [Field κ]

theorem evalParam_allEdges (a : E → κ) (b : V → κ) :
    evalParam a b (allEdges E V) = ∏ e, a e := by
  simp only [evalParam, allEdges, map_prod, eval₂Hom_X', Sum.elim_inl]

/-- Evaluation ℤ[a,b][1/product a]→κ at parameters with a_e≠0. -/
noncomputable def evalLoc (a : E → κ) (ha : ∀ e, a e ≠ 0) (b : V → κ) : LocRing E V →+* κ :=
  IsLocalization.Away.lift (allEdges E V) (g := evalParam a b) (by
    rw [evalParam_allEdges, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun e _ => ha e)

theorem evalLoc_algebraMap (a : E → κ) (ha : ∀ e, a e ≠ 0) (b : V → κ)
    (p : MvPolynomial (E ⊕ V) ℤ) :
    evalLoc a ha b (algebraMap (MvPolynomial (E ⊕ V) ℤ) (LocRing E V) p) = evalParam a b p := by
  rw [evalLoc, IsLocalization.Away.lift_eq]

theorem evalLoc_invSelf (a : E → κ) (ha : ∀ e, a e ≠ 0) (b : V → κ) :
    evalLoc a ha b (IsLocalization.Away.invSelf (allEdges E V) : LocRing E V) = (∏ e, a e)⁻¹ := by
  have h : algebraMap (MvPolynomial (E ⊕ V) ℤ) (LocRing E V) (allEdges E V) *
      (IsLocalization.Away.invSelf (allEdges E V) : LocRing E V) = 1 :=
    IsLocalization.Away.mul_invSelf _
  have h' := congrArg (evalLoc a ha b) h
  rw [map_mul, map_one, evalLoc_algebraMap, evalParam_allEdges] at h'
  exact eq_inv_of_mul_eq_one_right h'

theorem evalLoc_comp_chi (a : E → κ) (ha : ∀ e, a e ≠ 0) (b : V → κ) :
    (evalLoc a ha b).comp G.chi = evalParam (fun e => a e ^ 2) (G.auxBeta a b) := by
  apply ringHom_ext
  · intro n
    simp [chi, evalParam]
  · rintro (e | i)
    · simp only [chi, evalParam, RingHom.comp_apply, eval₂Hom_X', Sum.elim_inl, map_pow,
        evalLoc_algebraMap]
    · simp only [chi, RingHom.comp_apply, eval₂Hom_X', Sum.elim_inr, Sum.elim_inl, map_mul,
        evalLoc_algebraMap, evalLoc_invSelf, evalParam, nonIncProd, map_prod, auxBeta]
      have h1 : ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun e _ => ha e
      have h2 : ∏ e ∈ Finset.univ.filter (fun e => ¬ G.Incident e i), a e ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun e _ => ha e
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => G.Incident e i) a]
      field_simp

/-- Nonzero g has nonzero image χ(g), checked at the transcendental point (sqrt(s),β product sqrt(s)). -/
theorem chi_ne_zero_of_ne_zero {g : MvPolynomial (E ⊕ V) ℤ} (hg : g ≠ 0) : G.chi g ≠ 0 := by
  classical
  let s₀ : E → UnivField E V := fun e => toUniv (X (Sum.inl e))
  let β₀ : V → UnivField E V := fun i => toUniv (X (Sum.inr i))
  have hs₀ : ∀ e, s₀ e ≠ 0 := fun e h =>
    X_ne_zero (Sum.inl e) (toUniv_injective (by rw [map_zero]; exact h))
  choose a₀ ha₀ using fun e => IsAlgClosed.exists_pow_nat_eq (s₀ e) two_pos
  have ha₀0 : ∀ e, a₀ e ≠ 0 := fun e h => hs₀ e (by rw [← ha₀ e, h, zero_pow two_ne_zero])
  intro h0
  have h1 := congrArg (evalLoc a₀ ha₀0 (G.reconB a₀ β₀)) h0
  rw [map_zero, ← RingHom.comp_apply, G.evalLoc_comp_chi] at h1
  have hsq : (fun e => a₀ e ^ 2) = s₀ := funext ha₀
  have hab : G.auxBeta a₀ (G.reconB a₀ β₀) = β₀ := funext (G.auxBeta_reconB a₀ ha₀0 β₀)
  rw [hsq, hab] at h1
  have key : evalParam s₀ β₀ = toUniv.comp (map (Int.castRingHom ℚ)) := by
    apply ringHom_ext
    · intro n
      simp [evalParam]
    · rintro (e | i) <;> simp [evalParam, s₀, β₀]
  rw [key, RingHom.comp_apply] at h1
  exact hg (map_injective (Int.castRingHom ℚ) Int.cast_injective
    (toUniv_injective (by rw [map_zero, map_zero]; exact h1)))

end BPParams

/-- **Count over every algebraically closed field.** A nonzero P∈ℤ[a_e,b_i] exists such that for all nonzero parameters with P(a,b)≠0 there are exactly Q(G) admissible BP solutions, and their auxiliary coordinates (A=X/a, F=total field) are simple. -/
theorem exists_generic_count_eq_Q (hG : G.Loopless) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (κ : Type w) [Field κ] [IsAlgClosed κ] (a : E → κ) (b : V → κ),
        (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        eval (Sum.elim a b) (map (Int.castRingHom κ) P) ≠ 0 →
          Nat.card {y : Dart E → κ // G.IsAdmissibleSolution a b y} = G.Q ∧
          ∀ y, G.IsAdmissibleSolution a b y →
            G.IsSimpleAuxSolution (fun e => a e ^ 2) (G.auxBeta a b) (G.auxA a b y)
              (G.totalField b y) := by
  obtain ⟨g, hg0, hg⟩ := G.exists_generic_aux_degree_eq_Q
  obtain ⟨x, hx⟩ := IsLocalization.surj (Submonoid.powers (allEdges E V)) (G.chi g)
  have hχ := G.chi_ne_zero_of_ne_zero hg0
  refine ⟨x.1, ?_, ?_⟩
  · intro hP
    rw [hP, map_zero] at hx
    exact hχ ((IsLocalization.map_units (LocRing E V) x.2).mul_left_eq_zero.1 hx)
  · intro κ _ _ a b ha hb hP
    have h1 := congrArg (evalLoc a ha b) hx
    rw [map_mul, evalLoc_algebraMap, evalLoc_algebraMap, ← RingHom.comp_apply,
      G.evalLoc_comp_chi] at h1
    have h2 : eval (Sum.elim (fun e => a e ^ 2) (G.auxBeta a b)) (map (Int.castRingHom κ) g) ≠ 0 := by
      intro h0
      rw [← evalParam_apply] at h0
      rw [h0, zero_mul] at h1
      apply hP
      rw [← evalParam_apply]
      exact h1.symm
    have hβ' : ∀ i, G.auxBeta a b i ≠ 0 := fun i =>
      div_ne_zero (hb i) (Finset.prod_ne_zero_iff.2 fun e _ => ha e)
    obtain ⟨hcard, hsimp⟩ := hg κ (fun e => a e ^ 2) (G.auxBeta a b) h2
    have hrec : G.reconB a (G.auxBeta a b) = b := funext (G.reconB_auxBeta a b ha)
    refine ⟨?_, ?_⟩
    · have := G.card_admissible_eq_card_aux hG a ha (G.auxBeta a b) hβ'
      rw [hrec] at this
      rw [this]
      exact hcard
    · intro y hy
      exact hsimp _ _ (G.isAuxSolution_of_admissible hG a b y ha hb hy)

end Multigraph

end BPFixedPoints
