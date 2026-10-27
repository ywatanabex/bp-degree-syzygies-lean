import BPFixedPoints.Real.ProperDegreeIntegral
import BPFixedPoints.Real.SectorOddness

/-!
# Brouwer degree of the sector vertex maps (`real:sector-degree`)

Write the vertex map as 𝔥_S(u) = D_S u − Ψ_S(u), with D_S = diag(1 − k_i), k_i = d_S(i)
(`sectorDiag`), and Ψ_S bounded by Σ_α |log a_α|/2 (`norm_sectorField_sub_sectorDiag_le`).
D_S is invertible exactly when no vertex has S-degree one (`det_sectorDiag_ne_zero_iff`), in
particular for Eulerian S (`IsEvenSet.deg_ne_one`). Then exactly the v(S) vertices incident to S
have negative diagonal entries (`filter_sectorDiag_neg`), so
sign det D_S = deg D_S = (−1)^{v(S)} (`sign_det_sectorDiag`, `brouwerDegree_sectorDiag`). Here
v(S) = #`support S`, the number of vertices incident to S (`support_eq_filter_incident`).

The degree theory of `ProperDegree` then gives, for a_e > 0 and no vertex of S-degree one:

* 𝔥_S is proper (`isCompact_preimage_sectorField`) and surjective (`surjective_sectorField`);
* at every regular value h, Σ_{𝔥_S(u)=h} sign det D𝔥_S(u) = (−1)^{v(S)}
  (`signedFiberCount_sectorField`), with D𝔥_S the Jacobian of the vertex map;
* deg 𝔥_S = (−1)^{v(S)} (`brouwerDegree_sectorField`), along the whole homotopy
  H_t = D_S − tΨ_S (`brouwerDegree_sectorHomotopy`), uniformly proper for t ∈ [0,1]
  (`norm_le_of_sectorHomotopy_eq`).

For every additive Haar measure μ on ℝ^V and continuous compactly supported ψ,
∫ ψ(𝔥_S u) det D𝔥_S(u) dμ(u) = (−1)^{v(S)} ∫ ψ dμ (`integral_sectorField_mul_det`). This
determinant-integral form of the degree needs no regular value, so it also computes the degree
from test functions concentrated near a critical value (`degreeIntegral_sectorField`).

If every admissible BP solution of sign sector S is simple, h = ½ log b is a regular value and the
signed count of the sector solutions in vertex coordinates is (−1)^{v(S)}
(`signedFiberCount_sectorField_of_simple`).
-/

namespace BPFixedPoints

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V]

section Diag

variable (G : Multigraph V E)

/-- The diagonal linear part D_S = diag(1 − k_i) of the vertex map 𝔥_S, where k_i = d_S(i). -/
noncomputable def sectorDiag (S : Finset E) : (V → ℝ) →L[ℝ] (V → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (1 - (G.deg S i : ℝ))).comp
      (ContinuousLinearMap.proj i)

variable {G}

/-- (D_S u)_i = (1 − k_i) u_i. -/
theorem sectorDiag_apply (S : Finset E) (u : V → ℝ) (i : V) :
    G.sectorDiag S u i = (1 - (G.deg S i : ℝ)) * u i := by
  simp [sectorDiag, mul_comm]

/-- An Eulerian edge set has no vertex of degree one. -/
theorem IsEvenSet.deg_ne_one {S : Finset E} (hS : G.IsEvenSet S) (i : V) : G.deg S i ≠ 1 := by
  intro h
  exact Nat.not_even_one (h ▸ hS i)

/-- The diagonal entries 1 − k_i are nonzero when no vertex has S-degree one. -/
theorem one_sub_deg_ne_zero {S : Finset E} (hS : ∀ i, G.deg S i ≠ 1) (i : V) :
    1 - (G.deg S i : ℝ) ≠ 0 := by
  intro h
  have h1 : (G.deg S i : ℝ) = 1 := by linarith
  exact hS i (by exact_mod_cast h1)

/-- D_S as a linear isomorphism, when no vertex has S-degree one. -/
noncomputable def sectorDiagEquiv (S : Finset E) (hS : ∀ i, G.deg S i ≠ 1) :
    (V → ℝ) ≃L[ℝ] (V → ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (G.sectorDiag S)
    (ContinuousLinearMap.pi fun i =>
      (ContinuousLinearMap.toSpanSingleton ℝ (1 - (G.deg S i : ℝ))⁻¹).comp
        (ContinuousLinearMap.proj i))
    (fun u => by
      funext i
      have h := one_sub_deg_ne_zero hS i
      simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        sectorDiag_apply]
      field_simp)
    (fun u => by
      funext i
      have h := one_sub_deg_ne_zero hS i
      simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        sectorDiag_apply]
      field_simp)

/-- The underlying linear map of `sectorDiagEquiv` is D_S. -/
@[simp]
theorem coe_sectorDiagEquiv {S : Finset E} (hS : ∀ i, G.deg S i ≠ 1) :
    (G.sectorDiagEquiv S hS : (V → ℝ) →L[ℝ] (V → ℝ)) = G.sectorDiag S :=
  rfl

variable [Fintype V]

/-- det D_S = ∏_i (1 − k_i). -/
theorem det_sectorDiag (S : Finset E) :
    (G.sectorDiag S).det = ∏ i, (1 - (G.deg S i : ℝ)) := by
  rw [sectorDiag, ContinuousLinearMap.det_pi]
  simp only [ContinuousLinearMap.det_toSpanSingleton]

/-- D_S is invertible exactly when no vertex has S-degree one. -/
theorem det_sectorDiag_ne_zero_iff (S : Finset E) :
    (G.sectorDiag S).det ≠ 0 ↔ ∀ i, G.deg S i ≠ 1 := by
  rw [det_sectorDiag, Finset.prod_ne_zero_iff]
  constructor
  · intro h i hi
    exact h i (Finset.mem_univ i) (by rw [hi, Nat.cast_one, sub_self])
  · intro h i _
    exact one_sub_deg_ne_zero h i

/-- v(S) is the number of vertices incident to an edge of S. -/
theorem support_eq_filter_incident (S : Finset E) :
    G.support S = Finset.univ.filter fun i => ∃ e ∈ S, G.Incident e i := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Nat.pos_iff_ne_zero, ne_eq,
    G.deg_eq_zero_iff, not_forall, not_not, exists_prop]

/-- If no vertex has S-degree one, the negative diagonal entries 1 − k_i of D_S are exactly those
at the v(S) vertices incident to S. -/
theorem filter_sectorDiag_neg {S : Finset E} (hS : ∀ i, G.deg S i ≠ 1) :
    (Finset.univ.filter fun i => 1 - (G.deg S i : ℝ) < 0) = G.support S := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have h1 : (1 : ℝ) < G.deg S i := by linarith
    have h2 : 1 < G.deg S i := by exact_mod_cast h1
    omega
  · intro h
    have h2 : 2 ≤ G.deg S i := by
      have := hS i
      omega
    have h3 : (2 : ℝ) ≤ G.deg S i := by exact_mod_cast h2
    linarith

/-- **Sign of det D_S.** If no vertex has S-degree one, sign det D_S = (−1)^{v(S)}. -/
theorem sign_det_sectorDiag {S : Finset E} (hS : ∀ i, G.deg S i ≠ 1) :
    (SignType.sign (G.sectorDiag S).det : ℤ) = (-1) ^ (G.support S).card := by
  have hsign : ∀ i, SignType.sign (1 - (G.deg S i : ℝ)) =
      if i ∈ G.support S then -1 else 1 := by
    intro i
    rw [← filter_sectorDiag_neg hS]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact sign_neg h
    · exact sign_pos (lt_of_le_of_ne (not_lt.1 h) (one_sub_deg_ne_zero hS i).symm)
  have hprod : SignType.sign (G.sectorDiag S).det = (-1) ^ (G.support S).card := by
    rw [det_sectorDiag, ← signHom_apply, map_prod]
    simp only [signHom_apply, hsign]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [hprod, SignType.coe_pow, SignType.coe_neg_one]

/-- Normalization: deg D_S = sign det D_S = (−1)^{v(S)}. -/
theorem brouwerDegree_sectorDiag {S : Finset E} (hS : ∀ i, G.deg S i ≠ 1) :
    brouwerDegree (G.sectorDiag S) = (-1) ^ (G.support S).card := by
  have h := brouwerDegree_continuousLinearEquiv (G.sectorDiagEquiv S hS)
  rw [coe_sectorDiagEquiv, sign_det_sectorDiag hS] at h
  exact h

end Diag

section Sector

variable [Fintype V] [DecidableEq E] [Fintype E] {G : Multigraph V E} {a : E → ℝ} {S : Finset E}

/-- The vertex map is at bounded distance from its diagonal part:
‖𝔥_S(u) − D_S u‖_∞ ≤ Σ_α |log a_α|/2. -/
theorem norm_sectorField_sub_sectorDiag_le (ha : ∀ e, 0 < a e) (S : Finset E) (u : V → ℝ) :
    ‖G.sectorField a S u - G.sectorDiag S u‖ ≤ ∑ α : Dart E, |Real.log (a α.1)| / 2 := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun α _ => by positivity)).2 fun i => ?_
  rw [Pi.sub_apply, sectorDiag_apply, Real.norm_eq_abs, abs_sub_comm]
  exact (abs_diag_sub_sectorField_le ha i).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun α _ _ => by positivity)

/-- 𝔥_S is proper when no vertex has S-degree one: preimages of compact sets are compact. -/
theorem isCompact_preimage_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1)
    {K : Set (V → ℝ)} (hK : IsCompact K) : IsCompact (G.sectorField a S ⁻¹' K) :=
  isCompact_preimage_of_bounded (contDiff_sectorField (n := 1) ha S).continuous
    (G.sectorDiagEquiv S hS) (norm_sectorField_sub_sectorDiag_le ha S) hK

/-- At a regular value the fiber of 𝔥_S is finite. -/
theorem finite_fiber_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1)
    {h : V → ℝ} (hh : IsRegularValue (G.sectorField a S) h) :
    (G.sectorField a S ⁻¹' {h}).Finite :=
  finite_fiber_of_bounded (contDiff_sectorField ha S) (G.sectorDiagEquiv S hS)
    (norm_sectorField_sub_sectorDiag_le ha S) hh

/-- At every regular value h of the vertex map, Σ_{𝔥_S(u)=h} sign det D𝔥_S(u) = sign det D_S. -/
theorem signedFiberCount_sectorField_eq_sign_det (ha : ∀ e, 0 < a e)
    (hS : ∀ i, G.deg S i ≠ 1) {h : V → ℝ} (hh : IsRegularValue (G.sectorField a S) h) :
    signedFiberCount (G.sectorField a S) h = SignType.sign (G.sectorDiag S).det := by
  rw [signedFiberCount_eq_sign_det_of_bounded (contDiff_sectorField ha S)
    (G.sectorDiagEquiv S hS) (norm_sectorField_sub_sectorDiag_le ha S) hh,
    coe_sectorDiagEquiv]

/-- **`real:sector-degree`, signed count.** For a_e > 0 and no vertex of S-degree one (in
particular S Eulerian), at every regular value h of the vertex map,
Σ_{𝔥_S(u)=h} sign det D𝔥_S(u) = sign det D_S = (−1)^{v(S)}. -/
theorem signedFiberCount_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1)
    {h : V → ℝ} (hh : IsRegularValue (G.sectorField a S) h) :
    signedFiberCount (G.sectorField a S) h = (-1) ^ (G.support S).card := by
  rw [signedFiberCount_sectorField_eq_sign_det ha hS hh]
  exact sign_det_sectorDiag hS

/-- **`real:sector-degree`.** For a_e > 0 and no vertex of S-degree one (in particular S
Eulerian), the vertex map has Brouwer degree deg 𝔥_S = (−1)^{v(S)}. -/
theorem brouwerDegree_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1) :
    brouwerDegree (G.sectorField a S) = (-1) ^ (G.support S).card := by
  rw [brouwerDegree_eq_sign_det_of_bounded (G.sectorDiagEquiv S hS) (contDiff_sectorField ha S)
    (norm_sectorField_sub_sectorDiag_le ha S), coe_sectorDiagEquiv]
  exact sign_det_sectorDiag hS

/-- Existence from the degree: 𝔥_S is surjective, since its degree (−1)^{v(S)} is nonzero. -/
theorem surjective_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1) :
    Function.Surjective (G.sectorField a S) :=
  surjective_of_bounded (G.sectorDiagEquiv S hS) (contDiff_sectorField ha S)
    (norm_sectorField_sub_sectorDiag_le ha S)

/-- `real:sector-degree` for an Eulerian sector. -/
theorem brouwerDegree_sectorField_of_isEvenSet (ha : ∀ e, 0 < a e) (hS : G.IsEvenSet S) :
    brouwerDegree (G.sectorField a S) = (-1) ^ (G.support S).card :=
  brouwerDegree_sectorField ha hS.deg_ne_one

/-- Signed count at a regular value of an Eulerian vertex map. -/
theorem signedFiberCount_sectorField_of_isEvenSet (ha : ∀ e, 0 < a e) (hS : G.IsEvenSet S)
    {h : V → ℝ} (hh : IsRegularValue (G.sectorField a S) h) :
    signedFiberCount (G.sectorField a S) h = (-1) ^ (G.support S).card :=
  signedFiberCount_sectorField ha hS.deg_ne_one hh

/-- The degree is the signed count at every regular value: it does not depend on h. -/
theorem signedFiberCount_sectorField_eq_brouwerDegree (ha : ∀ e, 0 < a e)
    (hS : ∀ i, G.deg S i ≠ 1) {h : V → ℝ} (hh : IsRegularValue (G.sectorField a S) h) :
    signedFiberCount (G.sectorField a S) h = brouwerDegree (G.sectorField a S) := by
  rw [signedFiberCount_sectorField ha hS hh, brouwerDegree_sectorField ha hS]

/-- **`real:sector-degree`, determinant-integral form.** For every additive Haar measure μ on ℝ^V
and continuous compactly supported ψ, ∫ ψ(𝔥_S u) det D𝔥_S(u) dμ(u) = (−1)^{v(S)} ∫ ψ dμ. -/
theorem integral_sectorField_mul_det (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1)
    (μ : MeasureTheory.Measure (V → ℝ)) [μ.IsAddHaarMeasure] {ψ : (V → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ u, ψ (G.sectorField a S u) * (fderiv ℝ (G.sectorField a S) u).det ∂μ =
      (-1) ^ (G.support S).card * ∫ y, ψ y ∂μ := by
  rw [integral_comp_mul_det_eq_brouwerDegree_mul μ (contDiff_sectorField ha S)
    (G.sectorDiagEquiv S hS) (norm_sectorField_sub_sectorDiag_le ha S) hψ hψs,
    brouwerDegree_sectorField ha hS]
  push_cast
  rfl

/-- The determinant-integral degree of 𝔥_S against any normalized test function, supported near a
regular or a critical value, is (−1)^{v(S)}. -/
theorem degreeIntegral_sectorField (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1)
    (μ : MeasureTheory.Measure (V → ℝ)) [μ.IsAddHaarMeasure] {ψ : (V → ℝ) → ℝ}
    (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ1 : ∫ y, ψ y ∂μ = 1) :
    degreeIntegral μ (G.sectorField a S) ψ = (-1) ^ (G.support S).card := by
  rw [degreeIntegral, integral_sectorField_mul_det ha hS μ hψ hψs, hψ1, mul_one]

/-- The homotopy H_t = D_S − tΨ_S, Ψ_S = D_S − 𝔥_S, from D_S (t = 0) to 𝔥_S (t = 1). -/
noncomputable def sectorHomotopy (G : Multigraph V E) (a : E → ℝ) (S : Finset E) (t : ℝ)
    (u : V → ℝ) : V → ℝ :=
  G.sectorDiag S u - t • (G.sectorDiag S u - G.sectorField a S u)

omit [Fintype V] in
/-- H_0 = D_S. -/
theorem sectorHomotopy_zero : G.sectorHomotopy a S 0 = G.sectorDiag S := by
  funext u
  simp [sectorHomotopy]

omit [Fintype V] in
/-- H_1 = 𝔥_S. -/
theorem sectorHomotopy_one : G.sectorHomotopy a S 1 = G.sectorField a S := by
  funext u
  simp [sectorHomotopy]

/-- **Uniform properness of the homotopy.** For t ∈ [0,1], every solution of H_t(u) = h
satisfies ‖u‖ ≤ ‖D_S⁻¹‖ (‖h‖ + Σ_α |log a_α|/2). -/
theorem norm_le_of_sectorHomotopy_eq (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {u h : V → ℝ} (hu : G.sectorHomotopy a S t u = h) :
    ‖u‖ ≤ ‖((G.sectorDiagEquiv S hS).symm : (V → ℝ) →L[ℝ] (V → ℝ))‖ *
      (‖h‖ + ∑ α : Dart E, |Real.log (a α.1)| / 2) :=
  norm_le_of_linear_sub_smul_eq (G.sectorDiagEquiv S hS)
    (B := fun u => G.sectorDiag S u - G.sectorField a S u)
    (fun u => by rw [norm_sub_rev]; exact norm_sectorField_sub_sectorDiag_le ha S u) ht hu

/-- **Degree along the homotopy.** Every H_t = D_S − tΨ_S has degree (−1)^{v(S)}, from
deg D_S = sign det D_S at t = 0 to deg 𝔥_S at t = 1. -/
theorem brouwerDegree_sectorHomotopy (ha : ∀ e, 0 < a e) (hS : ∀ i, G.deg S i ≠ 1) (t : ℝ) :
    brouwerDegree (G.sectorHomotopy a S t) = (-1) ^ (G.support S).card := by
  have h := brouwerDegree_linear_sub_smul (G.sectorDiagEquiv S hS)
    (B := fun u => G.sectorDiag S u - G.sectorField a S u)
    ((G.sectorDiag S).contDiff.sub (contDiff_sectorField ha S))
    (fun u => by rw [norm_sub_rev]; exact norm_sectorField_sub_sectorDiag_le ha S u) t
  rw [coe_sectorDiagEquiv, sign_det_sectorDiag hS] at h
  exact h

/-- **Signed count of BP solutions in a sign sector.** If every admissible real BP solution with
negative edge set S is simple, then h = ½ log b is a regular value of 𝔥_S and the solutions of
sector S, in vertex coordinates, satisfy Σ sign det D𝔥_S(u) = (−1)^{v(S)}. -/
theorem signedFiberCount_sectorField_of_simple (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) (hS : G.IsEvenSet S)
    (hnd : ∀ y, G.IsAdmissibleSolution a b y → negSupport y = S →
      G.IsSimpleSolution a b y) :
    signedFiberCount (G.sectorField a S) (fun i => Real.log (b i) / 2) =
      (-1) ^ (G.support S).card := by
  apply signedFiberCount_sectorField_of_isEvenSet ha hS
  intro u hu
  exact det_fderiv_sectorField_ne_zero hG ha ha1 hb hS (congrFun hu)
    (hnd _ (isAdmissibleSolution_sectorMsg ha ha1 hG hS hb (congrFun hu))
      (negSupport_sectorMsg ha ha1))

end Sector

end Multigraph

end BPFixedPoints
