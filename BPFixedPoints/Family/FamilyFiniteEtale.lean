import BPFixedPoints.Family.FamilyFiniteEtaleIso
import BPFixedPoints.Degree.GenericDegree

/-!
# Finite étaleness of the admissible BP family (`prop:bp-family`)

Let G be loopless, R=ℂ[a,b] and A_G=`FamilyRing` the coordinate ring of the
admissible total space 𝒳_G. Both 𝒳_G and P_G=(ℂ*)^{m+n}=D(∏a·∏b) are
affine, so over a principal open set D(s)⊆P_G the projection π_G is the ring
map R[1/s]→B_s=A_G[1/π_G(s)] (`FamilyAway`).

Proved here:

* `familyRing_finite_etale`: there is s∈R with s≠0 and ∏_e a_e ∏_i b_i ∣ s
  such that B_s is a finite (`Module.Finite`), free (`Module.Free`) and étale
  (`Algebra.Etale`) R[1/s]-algebra of rank (`Module.finrank`) Q(G). On the
  same open set D(s) every complex fiber has exactly Q(G) admissible
  solutions, all simple.
* `familyRing_finite_etale_of_hasGenericDegree`: the rank is the generic
  degree N(G) of the counting form `HasGenericDegree`.
* `paramToFamily_injective`: π_G is dominant (R→A_G is injective).

"Generic" means: over the principal open set D(s) of P_G for one nonzero s.
This is a nonempty Zariski open set (s≠0). The element s is only shown to
exist: it is a common denominator of a shape certificate built over the
algebraic closure of ℂ(a,b) and descended by a linear retraction; no explicit
polynomial (such as a discriminant) is given, and D(s) is not claimed to be
the largest open set over which π_G is finite étale. The statements are about
the ring map R[1/s]→B_s; the corresponding properties of the morphism of
schemes Spec B_s→Spec R[1/s] are not restated in Mathlib's scheme language.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial BP
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-! ### Certificates over the torus -/

/-- A certificate over ℂ[a,b][1/g] maps to one over ℂ[a,b][1/(g t)]. -/
theorem exists_cert_mul {g t : MvPolynomial (E ⊕ V) ℂ} {Q : ℕ} (hg0 : g ≠ 0) (ht0 : t ≠ 0)
    (c : ShapeCert (fun α => map (algebraMap _ (Localization.Away g)) (G.paramResidual α))
      (map (algebraMap _ (Localization.Away g)) G.paramDen) Q) :
    Nonempty (ShapeCert (fun α => map (algebraMap _ (Localization.Away (g * t))) (G.paramResidual α))
      (map (algebraMap _ (Localization.Away (g * t))) G.paramDen) Q) := by
  have : IsDomain (Localization.Away (g * t)) := Localization.Away.isDomain (mul_ne_zero hg0 ht0)
  let φ : Localization.Away g →+* Localization.Away (g * t) :=
    IsLocalization.Away.awayToAwayRight (S := Localization.Away g)
      (P := Localization.Away (g * t)) g t
  have hφ : φ.comp (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away g)) =
      algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away (g * t)) := by
    refine RingHom.ext fun x => ?_
    rw [RingHom.comp_apply]
    exact IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away g)
      (P := Localization.Away (g * t)) g t x
  have hf : (fun α => map φ (map (algebraMap _ (Localization.Away g)) (G.paramResidual α))) =
      fun α => map (algebraMap _ (Localization.Away (g * t))) (G.paramResidual α) := by
    funext α
    rw [map_map, hφ]
  have hD : map φ (map (algebraMap _ (Localization.Away g)) G.paramDen) =
      map (algebraMap _ (Localization.Away (g * t))) G.paramDen := by
    rw [map_map, hφ]
  exact ⟨hf ▸ hD ▸ c.map φ⟩


/-- A certificate over ℂ[a,b][1/s] for a nonzero s divisible by ∏_e a_e ∏_i b_i. -/
theorem exists_paramShapeCert_torus (hG : G.Loopless) :
    ∃ s : MvPolynomial (E ⊕ V) ℂ, s ≠ 0 ∧ (∏ j, X j : MvPolynomial (E ⊕ V) ℂ) ∣ s ∧
      Nonempty (ShapeCert (fun α => map (algebraMap _ (Localization.Away s)) (G.paramResidual α))
        (map (algebraMap _ (Localization.Away s)) G.paramDen) G.Q) := by
  obtain ⟨g, hg0, ⟨c⟩⟩ := G.exists_paramShapeCert hG
  have ht0 : (∏ j, X j : MvPolynomial (E ⊕ V) ℂ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => X_ne_zero j
  exact ⟨g * ∏ j, X j, mul_ne_zero hg0 ht0, dvd_mul_left _ g, G.exists_cert_mul hg0 ht0 c⟩

/-- At a complex parameter point off the zero set of s, a certificate over ℂ[a,b][1/s] gives exactly Q admissible solutions, all simple. -/
theorem card_admissible_of_cert {s : MvPolynomial (E ⊕ V) ℂ} {Q : ℕ}
    (hs : (∏ j, X j : MvPolynomial (E ⊕ V) ℂ) ∣ s)
    (c : ShapeCert (fun α => map (algebraMap _ (Localization.Away s)) (G.paramResidual α))
      (map (algebraMap _ (Localization.Away s)) G.paramDen) Q)
    (a : E → ℂ) (b : V → ℂ) (hab : eval (Sum.elim a b) s ≠ 0) :
    Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = Q ∧
      ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  let θ : MvPolynomial (E ⊕ V) ℂ →+* ℂ := eval (Sum.elim a b)
  have hθX : ∀ j, θ (X j) ≠ 0 := by
    obtain ⟨r, hr⟩ := hs
    intro j h0
    apply hab
    change θ s = 0
    rw [hr, map_mul, map_prod]
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ j) h0) _
  have ha : (fun e => θ (X (Sum.inl e))) = a := funext fun e => by simp [θ]
  have hb : (fun i => θ (X (Sum.inr i))) = b := funext fun i => by simp [θ]
  have hu : IsUnit (θ s) := isUnit_iff_ne_zero.2 hab
  let θs : Localization.Away s →+* ℂ := IsLocalization.Away.lift s hu
  have hθs : θs.comp (algebraMap _ (Localization.Away s)) = θ := IsLocalization.Away.lift_comp s hu
  have cθ := c.map θs
  have hf : (fun α => map θs (map (algebraMap _ (Localization.Away s)) (G.paramResidual α))) =
      fun α => map θ (G.paramResidual α) := by
    funext α
    rw [map_map, hθs]
  have hD : map θs (map (algebraMap _ (Localization.Away s)) G.paramDen) = map θ G.paramDen := by
    rw [map_map, hθs]
  rw [hf, hD] at cθ
  have hiff := G.split_solution_iff θ (fun e => hθX _) (fun i => hθX _)
  rw [ha, hb] at hiff
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← cθ.card_eq]
    exact (Nat.card_congr (Equiv.subtypeEquivRight hiff)).symm
  · have h := cθ.det_ne_zero ((hiff y).2 hy).1 ((hiff y).2 hy).2
    have h' := (G.split_isSimpleAt_iff θ y).1 h
    rwa [ha, hb] at h'

/-! ### Main results -/

/-- **Finite étaleness in `prop:bp-family`.** For a loopless graph there is a nonzero s∈ℂ[a,b], divisible by ∏_e a_e ∏_i b_i, such that B_s=A_G[1/s] is a finite, free and étale ℂ[a,b][1/s]-algebra of rank Q(G). Thus π_G is finite étale of degree Q(G)=N(G) over the nonempty Zariski open set D(s)⊆P_G. On the same open set every complex fiber has exactly Q(G) admissible solutions, all simple. -/
theorem familyRing_finite_etale (hG : G.Loopless) :
    ∃ s : MvPolynomial (E ⊕ V) ℂ, s ≠ 0 ∧ (∏ j, X j : MvPolynomial (E ⊕ V) ℂ) ∣ s ∧
      Module.Finite (Localization.Away s) (G.FamilyAway s) ∧
      Module.Free (Localization.Away s) (G.FamilyAway s) ∧
      Module.finrank (Localization.Away s) (G.FamilyAway s) = G.Q ∧
      Algebra.Etale (Localization.Away s) (G.FamilyAway s) ∧
      ∀ (a : E → ℂ) (b : V → ℂ), eval (Sum.elim a b) s ≠ 0 →
        Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = G.Q ∧
        ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  obtain ⟨s, hs0, hdvd, ⟨c⟩⟩ := G.exists_paramShapeCert_torus hG
  have : IsDomain (Localization.Away s) := Localization.Away.isDomain hs0
  obtain ⟨h1, h2, h3, h4⟩ := familyAway_finite_etale_of_cert c
  exact ⟨s, hs0, hdvd, h1, h2, h3, h4, G.card_admissible_of_cert hdvd c⟩

/-- **Rank N(G).** The rank of the finite étale family is the generic degree in the counting form `HasGenericDegree`. -/
theorem familyRing_finite_etale_of_hasGenericDegree (hG : G.Loopless) {n : ℕ}
    (hn : G.HasGenericDegree n) :
    ∃ s : MvPolynomial (E ⊕ V) ℂ, s ≠ 0 ∧ (∏ j, X j : MvPolynomial (E ⊕ V) ℂ) ∣ s ∧
      Module.Finite (Localization.Away s) (G.FamilyAway s) ∧
      Module.Free (Localization.Away s) (G.FamilyAway s) ∧
      Module.finrank (Localization.Away s) (G.FamilyAway s) = n ∧
      Algebra.Etale (Localization.Away s) (G.FamilyAway s) := by
  rw [(G.hasGenericDegree_iff hG).1 hn]
  obtain ⟨s, hs0, hdvd, h1, h2, h3, h4, -⟩ := G.familyRing_finite_etale hG
  exact ⟨s, hs0, hdvd, h1, h2, h3, h4⟩

/-- **Dominance in `prop:bp-family`.** π_G is dominant: ℂ[a,b]→A_G is injective. -/
theorem paramToFamily_injective (hG : G.Loopless) : Function.Injective G.paramToFamily := by
  obtain ⟨g, hg0, ⟨c⟩⟩ := G.exists_paramShapeCert hG
  have : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  have hof : Function.Injective (AdjoinRoot.of c.χ) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree c.monic.ne_zero, c.natDegree_eq]
    exact_mod_cast G.Q_pos.ne'
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : algebraMap (Localization.Away g) (G.FamilyAway g)
      (algebraMap (MvPolynomial (E ⊕ V) ℂ) (Localization.Away g) x) = 0 := by
    rw [familyAway_algebraMap, hx, map_zero]
  rw [← (certEquivFamilyAway c).commutes, AdjoinRoot.algebraMap_eq,
    map_eq_zero_iff _ (certEquivFamilyAway c).injective] at h1
  have h2 := hof (h1.trans (map_zero _).symm)
  exact IsLocalization.injective (Localization.Away g)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg0) (h2.trans (map_zero _).symm)

end BPFixedPoints.Multigraph
