import BPFixedPoints.Incidence.RingCoefficientGrading

/-!
# Coefficient scaling and the natural grading of the incidence ring

The natural coefficient grading of `𝒰_G` (`incidenceCoefficientPiece`, vertex coordinates in
degree `0`, coefficients in degree `1`) is defined chart by chart through the free-coefficient
presentations. This file gives an intrinsic description on the common torus.

* `mvPolynomialScale a` multiplies every variable of a polynomial by `a : ℂ`; it multiplies the
  coefficient of a monomial of degree `k` by `a ^ k` (`coeff_mvPolynomialScale`), so a
  homogeneous polynomial of degree `n` is multiplied by `a ^ n`
  (`mvPolynomialScale_eq_of_isHomogeneous`), and conversely scaling by `2` detects homogeneity
  (`isHomogeneous_of_mvPolynomialScale_two`).
* Coefficient scaling `t_v ↦ t_v`, `s_v ↦ s_v`, `c ↦ a c` is defined on the torus ring
  (`incTorusScale`) and on every chart (`incChartScale`); chart restrictions commute with it
  (`incChartMap_incChartScale`), so it preserves the incidence ring and restricts to
  `incidenceScale a : 𝒰_G →ₐ[ℂ] 𝒰_G`. These need no order on the edges.
* The free-coefficient presentation of each chart intertwines it with `mvPolynomialScale`
  (`incidenceChartPolynomial_incidenceScale`).
* **Scaling characterization** (`mem_incidenceCoefficientPiece_iff_scale`): `x` has natural degree
  `n` iff `incidenceScale a x = a ^ n • x` for all `a : ℂ`; the single scalar `a = 2` suffices
  (`mem_incidenceCoefficientPiece_iff_scale_two`).

Not covered here: graph maps (`IncidenceGradedMaps.lean`) and disjoint unions
(`IncidenceGradedMapsDisjointUnion.lean`). The description is for the chart model `IncidenceRing`;
no statement about sheaf global sections or a `𝔾_m`-action on schemes is made.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

/-! ### Scaling all variables of a polynomial -/

section PolynomialScaling

variable {ι R : Type*} [CommRing R] [Algebra ℂ R]

/-- Multiply every variable of a polynomial by the scalar `a : ℂ`. -/
noncomputable def mvPolynomialScale (a : ℂ) : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  aeval fun i => C (algebraMap ℂ R a) * X i

/-- Scaling multiplies a monomial of degree `k` by `a ^ k`. -/
theorem mvPolynomialScale_monomial (a : ℂ) (d : ι →₀ ℕ) (r : R) :
    mvPolynomialScale a (monomial d r) = monomial d (algebraMap ℂ R (a ^ d.degree) * r) := by
  classical
  rw [mvPolynomialScale, aeval_monomial]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  have h1 : (d.prod fun _ k => (C (algebraMap ℂ R a) : MvPolynomial ι R) ^ k) =
      C (algebraMap ℂ R (a ^ d.degree)) := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← map_pow, ← map_pow, Finsupp.degree_apply]
  have h2 : (d.prod fun i k => (X i : MvPolynomial ι R) ^ k) = monomial d 1 := by
    rw [monomial_eq, map_one, one_mul]
  rw [h1, h2, algebraMap_eq, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one, mul_comm]

/-- Scaling multiplies the coefficient of a monomial of degree `k` by `a ^ k`. -/
theorem coeff_mvPolynomialScale (a : ℂ) (d : ι →₀ ℕ) (p : MvPolynomial ι R) :
    (mvPolynomialScale a p).coeff d = algebraMap ℂ R (a ^ d.degree) * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [mvPolynomialScale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

/-- A homogeneous polynomial of degree `n` is multiplied by `a ^ n` under scaling. -/
theorem mvPolynomialScale_eq_of_isHomogeneous {p : MvPolynomial ι R} {n : ℕ}
    (hp : p.IsHomogeneous n) (a : ℂ) : mvPolynomialScale a p = a ^ n • p := by
  ext d
  rw [coeff_mvPolynomialScale, coeff_smul, Algebra.smul_def]
  by_cases hd : p.coeff d = 0
  · rw [hd, mul_zero, mul_zero]
  · have h : d.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hp hd
    rw [h]

/-- A polynomial over a `ℂ`-algebra that scaling by `2` multiplies by `2 ^ n` is homogeneous of
degree `n`. -/
theorem isHomogeneous_of_mvPolynomialScale_two {p : MvPolynomial ι R} {n : ℕ}
    (h : mvPolynomialScale (2 : ℂ) p = (2 : ℂ) ^ n • p) : p.IsHomogeneous n := by
  intro d hd
  have hc := congrArg (fun q : MvPolynomial ι R => q.coeff d) h
  rw [coeff_mvPolynomialScale, coeff_smul, Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← map_sub,
    ← Algebra.smul_def, smul_eq_zero] at hc
  rcases hc with hc | hc
  · rw [sub_eq_zero] at hc
    have h2 : ((2 ^ d.degree : ℕ) : ℂ) = ((2 ^ n : ℕ) : ℂ) := by push_cast; exact hc
    rw [Nat.cast_inj] at h2
    have h3 : d.degree = n := Nat.pow_right_injective (le_refl 2) h2
    rw [Finsupp.degree_eq_weight_one] at h3
    exact h3
  · exact absurd hc hd

end PolynomialScaling

/-! ### Scaling the coefficients on the torus and on the charts -/

section RingScaling

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- The images of the torus variables under scaling of the coefficients by `a`: `t_v ↦ t_v`,
`s_v ↦ s_v`, `c ↦ a c`. -/
noncomputable def incTorusScaleVal (a : ℂ) : IncTorusVar V E → MvPolynomial (IncTorusVar V E) ℂ
  | Sum.inl v => X (Sum.inl v)
  | Sum.inr (Sum.inl v) => X (Sum.inr (Sum.inl v))
  | Sum.inr (Sum.inr c) => C a * X (Sum.inr (Sum.inr c))

/-- Scaling of the coefficients by `a` on torus polynomials. -/
noncomputable def incTorusScalePoly (a : ℂ) :
    MvPolynomial (IncTorusVar V E) ℂ →ₐ[ℂ] MvPolynomial (IncTorusVar V E) ℂ :=
  aeval (incTorusScaleVal a)

/-- Scaling fixes the vertex relations `t_v s_v - 1`. -/
theorem incTorusScalePoly_incTorusRel_inl (a : ℂ) (v : V) :
    incTorusScalePoly a (G.incTorusRel (Sum.inl v)) = G.incTorusRel (Sum.inl v) := by
  simp [incTorusScalePoly, incTorusRel, incTorusScaleVal]

/-- The edge relations are linear in the coefficients, so scaling multiplies them by `a`. -/
theorem incTorusScalePoly_incTorusRel_inr (a : ℂ) (e : E) :
    incTorusScalePoly a (G.incTorusRel (Sum.inr e)) = C a * G.incTorusRel (Sum.inr e) := by
  simp only [incTorusScalePoly, incTorusRel, incChartEq, map_sum, map_mul,
    rename_X, aeval_X, map_incCoord, Sum.elim_inl, Sum.elim_inr,
    incTorusScaleVal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- Scaling preserves the torus ideal. -/
theorem incTorusIdeal_le_comap_scale (a : ℂ) :
    Ideal.span (Set.range G.incTorusRel) ≤
      (Ideal.span (Set.range G.incTorusRel)).comap (incTorusScalePoly a) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases i with v | e
  · rw [incTorusScalePoly_incTorusRel_inl]
    exact Ideal.subset_span ⟨Sum.inl v, rfl⟩
  · rw [incTorusScalePoly_incTorusRel_inr]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Sum.inr e, rfl⟩)

/-- **Coefficient scaling on the common torus**: `t_v ↦ t_v`, `s_v ↦ s_v`, `c ↦ a c`. -/
noncomputable def incTorusScale (a : ℂ) : G.IncTorusRing →ₐ[ℂ] G.IncTorusRing :=
  Ideal.quotientMapₐ _ (incTorusScalePoly a) (G.incTorusIdeal_le_comap_scale a)

/-- Coefficient scaling on the torus ring is induced by `incTorusScalePoly`. -/
theorem incTorusScale_mk (a : ℂ) (p : MvPolynomial (IncTorusVar V E) ℂ) :
    G.incTorusScale a (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (incTorusScalePoly a p) := rfl

/-- Coefficient scaling fixes the vertex coordinate `t_v`. -/
theorem incTorusScale_t (a : ℂ) (v : V) :
    G.incTorusScale a (Ideal.Quotient.mk _ (X (Sum.inl v))) =
      Ideal.Quotient.mk _ (X (Sum.inl v)) := by
  rw [incTorusScale_mk, incTorusScalePoly, aeval_X]
  rfl

/-- Coefficient scaling fixes the inverse vertex coordinate `s_v`. -/
theorem incTorusScale_s (a : ℂ) (v : V) :
    G.incTorusScale a (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))) := by
  rw [incTorusScale_mk, incTorusScalePoly, aeval_X]
  rfl

/-- Coefficient scaling multiplies a coefficient by `a`. -/
theorem incTorusScale_coeff (a : ℂ) (c : IncCoeffIdx E) :
    G.incTorusScale a (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c)))) =
      a • Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c))) := by
  rw [incTorusScale_mk, incTorusScalePoly, aeval_X,
    show incTorusScaleVal (V := V) a (Sum.inr (Sum.inr c)) = C a * X (Sum.inr (Sum.inr c))
      from rfl, C_mul', ← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]

/-- The images of the chart variables under scaling of the coefficients by `a`. -/
noncomputable def incChartScaleVal (a : ℂ) : IncChartVar V E → MvPolynomial (IncChartVar V E) ℂ
  | Sum.inl v => X (Sum.inl v)
  | Sum.inr c => C a * X (Sum.inr c)

/-- The chart equations are linear in the coefficients. -/
theorem aeval_incChartScaleVal_incChartEq (a : ℂ) (σ : V → Bool) (e : E) :
    aeval (incChartScaleVal a) (G.incChartEq σ e) = C a * G.incChartEq σ e := by
  simp only [incChartEq, map_sum, map_mul, aeval_X, map_incCoord, incChartScaleVal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

/-- Scaling preserves the ideal of a chart. -/
theorem incChartIdeal_le_comap_scale (a : ℂ) (σ : V → Bool) :
    Ideal.span (Set.range (G.incChartEq σ)) ≤
      (Ideal.span (Set.range (G.incChartEq σ))).comap (aeval (incChartScaleVal (V := V) a)) := by
  rw [Ideal.span_le]
  rintro _ ⟨e, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, aeval_incChartScaleVal_incChartEq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e, rfl⟩)

/-- **Coefficient scaling on a chart**: `t_v ↦ t_v`, `c ↦ a c`. -/
noncomputable def incChartScale (σ : V → Bool) (a : ℂ) : G.IncChartRing σ →ₐ[ℂ] G.IncChartRing σ :=
  Ideal.quotientMapₐ _ (aeval (incChartScaleVal a)) (G.incChartIdeal_le_comap_scale a σ)

/-- Coefficient scaling on a chart ring is induced by substitution of polynomials. -/
theorem incChartScale_mk (σ : V → Bool) (a : ℂ) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartScale σ a (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (aeval (incChartScaleVal a) p) := rfl

/-- Chart restriction commutes with coefficient scaling. -/
theorem incChartMap_comp_incChartScale (σ : V → Bool) (a : ℂ) :
    (G.incChartMap σ).comp (G.incChartScale σ a) = (G.incTorusScale a).comp (G.incChartMap σ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro (v | c)
  · change G.incChartMap σ (G.incChartScale σ a (Ideal.Quotient.mk _ (X (Sum.inl v)))) =
      G.incTorusScale a (G.incChartMap σ (Ideal.Quotient.mk _ (X (Sum.inl v))))
    rw [incChartScale_mk, incChartMap_mk, incChartMap_mk, aeval_X, aeval_X]
    simp only [incChartScaleVal, aeval_X, incChartVal]
    split_ifs <;> rw [incTorusScale_mk, incTorusScalePoly, aeval_X] <;> rfl
  · change G.incChartMap σ (G.incChartScale σ a (Ideal.Quotient.mk _ (X (Sum.inr c)))) =
      G.incTorusScale a (G.incChartMap σ (Ideal.Quotient.mk _ (X (Sum.inr c))))
    rw [incChartScale_mk, incChartMap_mk, incChartMap_mk, aeval_X, aeval_X]
    simp only [incChartScaleVal, map_mul, aeval_X, aeval_C, incChartVal]
    rw [incTorusScale_mk, incTorusScalePoly, aeval_X]
    rw [show incTorusScaleVal (V := V) a (Sum.inr (Sum.inr c)) = C a * X (Sum.inr (Sum.inr c))
      from rfl, map_mul]
    rfl

/-- Chart restriction commutes with coefficient scaling, elementwise. -/
theorem incChartMap_incChartScale (σ : V → Bool) (a : ℂ) (y : G.IncChartRing σ) :
    G.incChartMap σ (G.incChartScale σ a y) = G.incTorusScale a (G.incChartMap σ y) :=
  AlgHom.congr_fun (G.incChartMap_comp_incChartScale σ a) y

/-- Coefficient scaling preserves the incidence ring. -/
theorem incTorusScale_mem_incidenceRing (a : ℂ) {x : G.IncTorusRing} (hx : x ∈ G.IncidenceRing) :
    G.incTorusScale a x ∈ G.IncidenceRing := by
  rw [IncidenceRing, Algebra.mem_iInf] at hx ⊢
  intro σ
  obtain ⟨y, rfl⟩ := hx σ
  exact ⟨G.incChartScale σ a y, G.incChartMap_incChartScale σ a y⟩

/-- **Coefficient scaling on the incidence ring** `𝒰_G`: the restriction of `incTorusScale`. -/
noncomputable def incidenceScale (a : ℂ) : G.IncidenceRing →ₐ[ℂ] G.IncidenceRing :=
  ((G.incTorusScale a).comp G.IncidenceRing.val).codRestrict G.IncidenceRing
    fun x => G.incTorusScale_mem_incidenceRing a x.property

/-- Coefficient scaling on `𝒰_G` is the restriction of coefficient scaling on the torus. -/
@[simp] theorem incidenceScale_val (a : ℂ) (x : G.IncidenceRing) :
    (G.incidenceScale a x : G.IncTorusRing) = G.incTorusScale a x.val := rfl

end RingScaling

/-! ### The natural grading is the weight decomposition of coefficient scaling -/

section Characterization

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Restriction to a chart commutes with coefficient scaling. -/
theorem incidenceChartSection_incidenceScale (σ : V → Bool) (a : ℂ) (x : G.IncidenceRing) :
    G.incidenceChartSection σ (G.incidenceScale a x) =
      G.incChartScale σ a (G.incidenceChartSection σ x) := by
  apply G.incChartMap_injective σ
  rw [incChartMap_incidenceChartSection, incChartMap_incChartScale,
    incChartMap_incidenceChartSection]
  rfl

/-- The free-coefficient presentation of a chart ring, as a `ℂ`-algebra map. -/
noncomputable def incChartFreeHom (σ : V → Bool) :
    G.IncChartRing σ →ₐ[ℂ] MvPolynomial (E × Fin 3) (FaceRing ℂ (chartFace σ)) :=
  ((G.incFaceFreeEquiv (chartFace σ)).restrictScalars ℂ).toAlgHom.comp
    (G.incFaceChartEquiv σ).symm.toAlgHom

/-- The chart polynomial of a section is the free-coefficient presentation of its chart
restriction. -/
theorem incidenceChartPolynomial_eq_incChartFreeHom (σ : V → Bool) (x : G.IncidenceRing) :
    G.incidenceChartPolynomial σ x = G.incChartFreeHom σ (G.incidenceChartSection σ x) := rfl

/-- A vertex coordinate of the chart is the corresponding constant of the face presentation. -/
theorem incFaceChartEquiv_symm_vertex (σ : V → Bool) (v : V) :
    (G.incFaceChartEquiv σ).symm (Ideal.Quotient.mk _ (X (Sum.inl v))) =
      Ideal.Quotient.mk _ (C (faceVariable ℂ (chartFace σ) v)) := by
  rw [AlgEquiv.symm_apply_eq, incFaceChartEquiv_mk, chartFaceAmbientEquiv_C_variable]

/-- A coefficient of the chart is the corresponding coefficient of the face presentation. -/
theorem incFaceChartEquiv_symm_coeff (σ : V → Bool) (c : IncCoeffIdx E) :
    (G.incFaceChartEquiv σ).symm (Ideal.Quotient.mk _ (X (Sum.inr c))) =
      Ideal.Quotient.mk _ (X c) := by
  rw [AlgEquiv.symm_apply_eq, incFaceChartEquiv_mk, chartFaceAmbientEquiv_X]

/-- The free-coefficient presentation of a chart intertwines coefficient scaling with the scaling
of all free coefficients. -/
theorem incChartFreeHom_comp_incChartScale (σ : V → Bool) (a : ℂ) :
    (G.incChartFreeHom σ).comp (G.incChartScale σ a) =
      ((mvPolynomialScale a).restrictScalars ℂ).comp (G.incChartFreeHom σ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro (v | c)
  · change G.incChartFreeHom σ (G.incChartScale σ a (Ideal.Quotient.mk _ (X (Sum.inl v)))) =
      mvPolynomialScale a (G.incChartFreeHom σ (Ideal.Quotient.mk _ (X (Sum.inl v))))
    rw [incChartScale_mk, aeval_X]
    change G.incFaceFreeEquiv _
        ((G.incFaceChartEquiv σ).symm (Ideal.Quotient.mk _ (X (Sum.inl v)))) =
      mvPolynomialScale a (G.incFaceFreeEquiv _
        ((G.incFaceChartEquiv σ).symm (Ideal.Quotient.mk _ (X (Sum.inl v)))))
    rw [incFaceChartEquiv_symm_vertex, incFaceFreeEquiv_C, mvPolynomialScale, aeval_C,
      algebraMap_eq]
  · change G.incChartFreeHom σ (G.incChartScale σ a (Ideal.Quotient.mk _ (X (Sum.inr c)))) =
      mvPolynomialScale a (G.incChartFreeHom σ (Ideal.Quotient.mk _ (X (Sum.inr c))))
    rw [incChartScale_mk, aeval_X,
      show incChartScaleVal (V := V) a (Sum.inr c) = C a * X (Sum.inr c) from rfl, map_mul,
      map_mul]
    have hC : G.incChartFreeHom σ (Ideal.Quotient.mk _ (C a)) =
        algebraMap ℂ (MvPolynomial (E × Fin 3) (FaceRing ℂ (chartFace σ))) a :=
      (G.incChartFreeHom σ).commutes a
    have hX : G.incChartFreeHom σ (Ideal.Quotient.mk _ (X (Sum.inr c))) =
        G.incFaceFreeEquiv (chartFace σ) (Ideal.Quotient.mk _ (X c)) := by
      change G.incFaceFreeEquiv _
          ((G.incFaceChartEquiv σ).symm (Ideal.Quotient.mk _ (X (Sum.inr c)))) = _
      rw [incFaceChartEquiv_symm_coeff]
    rw [hC, hX, mvPolynomialScale_eq_of_isHomogeneous
      (G.incFaceFreeEquiv_mk_homogeneous _ (isHomogeneous_X _ c)), pow_one,
      Algebra.smul_def]

/-- The chart polynomials of a scaled section are the scaled chart polynomials. -/
theorem incidenceChartPolynomial_incidenceScale (σ : V → Bool) (a : ℂ) (x : G.IncidenceRing) :
    G.incidenceChartPolynomial σ (G.incidenceScale a x) =
      mvPolynomialScale a (G.incidenceChartPolynomial σ x) := by
  rw [incidenceChartPolynomial_eq_incChartFreeHom, incidenceChartSection_incidenceScale]
  exact AlgHom.congr_fun (G.incChartFreeHom_comp_incChartScale σ a) _

/-- **Scaling characterization of the natural grading.** A section has natural coefficient degree
`n` iff scaling all coefficients by `a` multiplies it by `a ^ n`, for every `a : ℂ`. -/
theorem mem_incidenceCoefficientPiece_iff_scale (n : ℕ) (x : G.IncidenceRing) :
    x ∈ G.incidenceCoefficientPiece n ↔ ∀ a : ℂ, G.incidenceScale a x = a ^ n • x := by
  constructor
  · intro hx a
    apply G.incidenceChartPolynomial_injective (fun _ => false)
    rw [incidenceChartPolynomial_incidenceScale, map_smul]
    exact mvPolynomialScale_eq_of_isHomogeneous ((G.mem_incidenceCoefficientPiece n x).mp hx _) a
  · intro h
    rw [G.mem_incidenceCoefficientPiece]
    intro σ
    apply isHomogeneous_of_mvPolynomialScale_two
    rw [← incidenceChartPolynomial_incidenceScale, h 2, map_smul]

/-- The single scalar `2` already detects the natural degree. -/
theorem mem_incidenceCoefficientPiece_iff_scale_two (n : ℕ) (x : G.IncidenceRing) :
    x ∈ G.incidenceCoefficientPiece n ↔ G.incidenceScale 2 x = (2 : ℂ) ^ n • x := by
  refine ⟨fun hx => (G.mem_incidenceCoefficientPiece_iff_scale n x).mp hx 2, fun h => ?_⟩
  rw [G.mem_incidenceCoefficientPiece]
  intro σ
  apply isHomogeneous_of_mvPolynomialScale_two
  rw [← incidenceChartPolynomial_incidenceScale, h, map_smul]

end Characterization

end BPFixedPoints.Multigraph
