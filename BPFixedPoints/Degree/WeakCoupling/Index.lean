import BPFixedPoints.Degree.WeakCoupling.Branches
import BPFixedPoints.StrongField.StateMatrix

/-!
# BP indices of weak-coupling real roots (index part of main theorem D)

In auxiliary coordinates define `logJac` as 𝕁=diag(ℓ)M, with nonbacktracking
matrix `nbMatrix` and ℓ_α=δ_e A_α/((1+s_e A_α)(1+A_α)), δ_e=s_e−1.
Multiplying active rows of I−𝕁 by δ_e gives `normJac`, with active row
δ_e e_α−κ_α M_α and κ_α=(A_ᾱ−F_{h(α)})²/(A_α A_ᾱ F_{h(α)}).
Use `sub_one_mul_ellAux` and `normDiag_mul_one_sub_logJac` to get
`det_normJac_eq`: det(normJac)=∏_{e∈S}δ_e² det(I−𝕁).

At a limit point, active rows are −c_{h(α)}M_α with c_j=(1+F_j)²/F_j;
other rows are identity rows. `det_normJac_limitPoint` gives
(−1)^{|S|+v(S)}w(S)∏_v c_v^{d_S(v)}. For real limit points with β>0,
degrees are even and F>0, giving sign (−1)^{|S|+v(S)}
(`pos_sign_det_normJac_limitPoint`). The determinant is continuous at these
points (`continuousAt_normJac`).
For real c_e≠0, β_i>0 and small real t≠0, every real solution along s_e=1+t c_e
is near an even-degree real limit point (`exists_near_real_limit`) and
sgn det(I−𝕁)=(−1)^{|S|−v(S)} (`sign_det_one_sub_logJac_weak_coupling`).
`BPJacobian.lean` identifies 𝕁 up to similarity with the rational BP derivative.
Instability ρ(𝕁)→∞ and uniformity in a full neighborhood are not treated.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Algebra

variable {K : Type*} [Field K]

/-- ℓ_α=δ_e A_α/((1+s_e A_α)(1+A_α)) in auxiliary coordinates, with δ_e=s_e−1. -/
def ellAux (s : E → K) (z : Var V E → K) (α : Dart E) : K :=
  (s α.1 - 1) * z (Sum.inl α) / ((1 + s α.1 * z (Sum.inl α)) * (1 + z (Sum.inl α)))

/-- BP Jacobian in logarithmic derivative coordinates: 𝕁=diag(ℓ)M. -/
def logJac (s : E → K) (z : Var V E → K) : Matrix (Dart E) (Dart E) K :=
  diagonal (ellAux s z) * G.nbMatrix K

/-- Right side of `kappa_eq`: (A_ᾱ−F_{h(α)})²/(A_α A_ᾱ F_{h(α)}). -/
def kappaAux (z : Var V E → K) (α : Dart E) : K :=
  (z (Sum.inl (rev α)) - z (Sum.inr (G.head α))) ^ 2 /
    (z (Sum.inl α) * z (Sum.inl (rev α)) * z (Sum.inr (G.head α)))

/-- Diagonal matrix multiplying active-dart rows by δ_e. -/
def normDiag (S : Finset E) (s : E → K) : Matrix (Dart E) (Dart E) K :=
  diagonal fun α => if α.1 ∈ S then s α.1 - 1 else 1

/-- Normalized I-𝕁, with active rows δ_e e_α-κ_α M_α and other rows e_α-ℓ_α M_α. -/
def normJac (S : Finset E) (s : E → K) (z : Var V E → K) : Matrix (Dart E) (Dart E) K :=
  normDiag S s - diagonal (fun α => if α.1 ∈ S then G.kappaAux z α else ellAux s z α) * G.nbMatrix K

theorem normJac_apply (S : Finset E) (s : E → K) (z : Var V E → K) (α γ : Dart E) :
    G.normJac S s z α γ =
      (if α = γ then (if α.1 ∈ S then s α.1 - 1 else 1) else 0) -
        (if α.1 ∈ S then G.kappaAux z α else ellAux s z α) * G.nbMatrix K α γ := by
  simp only [normJac, normDiag, Matrix.sub_apply, diagonal_apply, diagonal_mul]

/-- On auxiliary solutions, δ_e ℓ_α=κ_α. -/
theorem sub_one_mul_ellAux {s : E → K} {β : V → K} {z : Var V E → K} (h : G.IsAuxPt s β z)
    (α : Dart E) : (s α.1 - 1) * ellAux s z α = G.kappaAux z α := by
  have hA := h.A_ne_zero α
  have hA' := h.A_ne_zero (rev α)
  have hF := h.F_ne_zero (G.head α)
  have hA1 : 1 + z (Sum.inl α) ≠ 0 := fun h0 => h.A_ne_neg_one α (by linear_combination h0)
  have he := h.edge (rev α)
  simp only [rev_rev, tail_rev, rev_fst] at he
  -- he : F_h (1 + A_α) = A_ᾱ (1 + s A_α)
  have hs : 1 + s α.1 * z (Sum.inl α) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    exact mul_ne_zero hF hA1 he
  simp only [ellAux, kappaAux]
  field_simp
  apply mul_left_cancel₀ hA'
  set A := z (Sum.inl α)
  set A' := z (Sum.inl (rev α))
  set F := z (Sum.inr (G.head α))
  set σ := s α.1
  linear_combination (-2 * F * (F - A') * (1 + A) + (F * (1 + A) - A' * (1 + σ * A)) * F +
    (1 + A) * (A' - F) ^ 2) * he

/-- `det(normDiag) = ∏_{e∈S} δ_e²`。 -/
theorem det_normDiag (S : Finset E) (s : E → K) :
    (normDiag S s).det = ∏ e ∈ S, (s e - 1) ^ 2 := by
  rw [normDiag, det_diagonal, Fintype.prod_prod_type]
  simp only [Fintype.prod_bool]
  rw [← Fintype.prod_ite_mem S (fun e => (s e - 1) ^ 2)]
  exact Finset.prod_congr rfl fun e _ => by split_ifs <;> ring

/-- On auxiliary solutions, normDiag times (I-𝕁) equals normJac. -/
theorem normDiag_mul_one_sub_logJac {s : E → K} {β : V → K} {z : Var V E → K} (h : G.IsAuxPt s β z)
    (S : Finset E) : normDiag S s * (1 - G.logJac s z) = G.normJac S s z := by
  rw [Matrix.mul_sub, Matrix.mul_one, logJac, ← Matrix.mul_assoc, normJac]
  congr 2
  rw [normDiag, diagonal_mul_diagonal]
  congr 1
  funext α
  split_ifs
  · exact G.sub_one_mul_ellAux h α
  · ring

/-- `det(I − 𝕁) · ∏_{e∈S} δ_e² = det(normJac)`。 -/
theorem det_normJac_eq {s : E → K} {β : V → K} {z : Var V E → K} (h : G.IsAuxPt s β z)
    (S : Finset E) :
    (G.normJac S s z).det = (∏ e ∈ S, (s e - 1) ^ 2) * (1 - G.logJac s z).det := by
  rw [← G.normDiag_mul_one_sub_logJac h S, det_mul, det_normDiag]

/-- Identify the active-dart subtype with the darts of the state graph. -/
def activeDartEquiv (S : Finset E) : Dart S ≃ {α : Dart E // α.1 ∈ S} where
  toFun α := ⟨(α.1.1, α.2), α.1.2⟩
  invFun α := (⟨α.1.1, α.2⟩, α.1.2)
  left_inv := by rintro ⟨⟨e, he⟩, d⟩; rfl
  right_inv := by rintro ⟨⟨e, d⟩, he⟩; rfl

/-- At a limit point the normalized matrix has active rows -c_headα M_α, c_j=(1+F_j)²/F_j, and unit rows elsewhere. -/
theorem normJac_limitPoint [DecidableEq K] (S : Finset E) (F : V → K) :
    G.normJac S (fun _ => 1) (G.limitPoint S F) =
      diagonal (fun α => if α.1 ∈ S then 0 else 1) -
        diagonal (fun α => if α.1 ∈ S then (1 + F (G.head α)) ^ 2 / F (G.head α) else 0) *
          G.nbMatrix K := by
  rw [normJac, normDiag]
  congr 2
  · funext α; split_ifs <;> ring
  · congr 1; funext α
    split_ifs with hα
    · simp only [kappaAux, limitPoint, limitCoords, rev_fst, hα, ↓reduceIte]
      ring
    · simp [ellAux]

/-- **Determinant at a limit point:** (−1)^{|S|+v(S)}w(S)∏_v c_v^{d_S(v)}. -/
theorem det_normJac_limitPoint [DecidableEq K] (S : Finset E) (F : V → K) :
    (G.normJac S (fun _ => 1) (G.limitPoint S F)).det =
      (-1) ^ (S.card + (G.support S).card) * (∏ v ∈ G.support S, ((G.deg S v : K) - 1)) *
        ∏ v, ((1 + F v) ^ 2 / F v) ^ G.deg S v := by
  rw [normJac_limitPoint]
  set c : V → K := fun v => (1 + F v) ^ 2 / F v
  set N := diagonal (fun α : Dart E => if α.1 ∈ S then (0 : K) else 1) -
    diagonal (fun α => if α.1 ∈ S then c (G.head α) else 0) * G.nbMatrix K
  let e := Equiv.sumCompl (fun α : Dart E => α.1 ∈ S)
  have hblock : N.submatrix e e =
      fromBlocks (N.submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E) Subtype.val)
        (N.submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E)
          (Subtype.val : {α : Dart E // α.1 ∉ S} → Dart E)) 0 1 := by
    ext (⟨α, hα⟩ | ⟨α, hα⟩) (⟨γ, hγ⟩ | ⟨γ, hγ⟩)
    · rfl
    · rfl
    · simp [N, e, hα, diagonal_apply, Matrix.sub_apply]
      rintro rfl; exact hα hγ
    · simp [N, e, hα, diagonal_apply, Matrix.sub_apply, one_apply, Subtype.ext_iff]
  rw [← det_submatrix_equiv_self e, hblock, det_fromBlocks_zero₂₁, det_one, mul_one,
    ← det_submatrix_equiv_self (activeDartEquiv S)]
  have hA : (N.submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E) Subtype.val).submatrix
      (activeDartEquiv S) (activeDartEquiv S) =
      -(diagonal fun α : Dart S => c ((G.restrict S).head α)) * G.stateMatrix K S := by
    rw [stateMatrix_eq_submatrix]
    ext ⟨⟨a, ha⟩, d⟩ ⟨⟨b, hb⟩, d'⟩
    simp [N, activeDartEquiv, diagonal_apply, Matrix.sub_apply, ha, Matrix.mul_apply, restrict,
      head]
  rw [hA, det_neg_diagonal_mul_stateMatrix, det_stateMatrix_eq_w]

end Algebra

section Real

/-- A real vertex root for β>0 has even active degree and positive F. -/
theorem even_and_pos_of_vertexLimitEq_real {k : ℕ} {β F : ℝ} (hβ : 0 < β)
    (h : VertexLimitEq k β F) : Even k ∧ 0 < F := by
  have hk : Even k := by
    by_contra hk
    exact (isEmpty_vertexLimitEq_real hk hβ).false ⟨F, h⟩
  refine ⟨hk, ?_⟩
  obtain ⟨hF0, hβF⟩ := h
  rw [hk.neg_one_pow, one_mul] at hβF
  by_contra hF
  have hFn : F < 0 := lt_of_le_of_ne (not_lt.1 hF) hF0
  have hodd : Odd ((1 : ℤ) - k) := by
    obtain ⟨m, hm⟩ := hk
    exact ⟨-m, by rw [hm]; push_cast; ring⟩
  have : F ^ ((1 : ℤ) - k) < 0 := hodd.zpow_neg_iff.2 hFn
  linarith

/-- At real limit points the normalized determinant has sign (-1)^{|S|+v(S)}, since c_v,w(S)>0. -/
theorem pos_sign_det_normJac_limitPoint {β : V → ℝ} (hβ : ∀ i, 0 < β i) {S : Finset E}
    {F : V → ℝ} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    0 < (-1) ^ (S.card + (G.support S).card) *
      (G.normJac S (fun _ => 1) (G.limitPoint S F)).det := by
  rw [det_normJac_limitPoint, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  have hpos : ∀ i, Even (G.deg S i) ∧ 0 < F i := fun i =>
    even_and_pos_of_vertexLimitEq_real (hβ i) (hF i)
  refine mul_pos (Finset.prod_pos fun v hv => ?_) (Finset.prod_pos fun v _ => ?_)
  · simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨k, hk⟩ := (hpos v).1
    have : (2 : ℝ) ≤ G.deg S v := by exact_mod_cast (by omega : 2 ≤ G.deg S v)
    linarith
  · exact pow_pos (div_pos (pow_pos (by linarith [(hpos v).2]) 2) (hpos v).2) _

/-- The normalized matrix is continuous at (0,x₀), with denominators nonzero there. -/
theorem continuousAt_normJac (c : E → ℝ) {S : Finset E} {F : V → ℝ} (hF0 : ∀ i, F i ≠ 0)
    (hF1 : ∀ i, F i ≠ -1) :
    ContinuousAt (fun q : ℝ × (Var V E → ℝ) => G.normJac S (fun e => 1 + q.1 * c e) q.2)
      ((0 : ℝ), G.limitPoint S F) := by
  set p : ℝ × (Var V E → ℝ) := ((0 : ℝ), G.limitPoint S F)
  have hz : ∀ v, ContinuousAt (fun q : ℝ × (Var V E → ℝ) => q.2 v) p := fun v =>
    ((continuous_apply v).comp continuous_snd).continuousAt
  have ht : ContinuousAt (fun q : ℝ × (Var V E → ℝ) => q.1) p := continuous_fst.continuousAt
  have hs : ∀ e, ContinuousAt (fun q : ℝ × (Var V E → ℝ) => 1 + q.1 * c e) p := fun e =>
    continuousAt_const.add (ht.mul continuousAt_const)
  refine continuousAt_pi.2 fun α => continuousAt_pi.2 fun γ => ?_
  simp only [normJac_apply]
  have hdiag : ContinuousAt (fun q : ℝ × (Var V E → ℝ) =>
      if α = γ then (if α.1 ∈ S then 1 + q.1 * c α.1 - 1 else 1) else (0 : ℝ)) p := by
    split_ifs
    · exact (hs _).sub continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
  refine hdiag.sub (ContinuousAt.mul ?_ continuousAt_const)
  by_cases hα : α.1 ∈ S
  · simp only [hα, ↓reduceIte, kappaAux]
    refine (((hz _).sub (hz _)).pow 2).div (((hz _).mul (hz _)).mul (hz _)) ?_
    simp only [p, limitPoint, limitCoords, rev_fst, hα, ↓reduceIte]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by norm_num)) (hF0 _)
  · simp only [hα, ↓reduceIte, ellAux]
    refine (((hs _).sub continuousAt_const).mul (hz _)).div
      (((continuousAt_const.add ((hs _).mul (hz _)))).mul (continuousAt_const.add (hz _))) ?_
    simp only [p, limitPoint, limitCoords, hα, ↓reduceIte, zero_mul, add_zero, one_mul]
    exact mul_ne_zero (fun h => hF1 _ (by linear_combination h))
      (fun h => hF1 _ (by linear_combination h))

/-- Near a limit point, in both parameter and coordinates, the normalized determinant has sign (-1)^{|S|+v(S)}. -/
theorem exists_nhds_pos_sign_normJac (c : E → ℝ) {β : V → ℝ} (hβ : ∀ i, 0 < β i)
    {S : Finset E} {F : V → ℝ} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    ∃ r > 0, ∀ t : ℝ, ∀ z : Var V E → ℝ, |t| < r → ‖z - G.limitPoint S F‖ < r →
      0 < (-1) ^ (S.card + (G.support S).card) *
        (G.normJac S (fun e => 1 + t * c e) z).det := by
  have hβ1 : ∀ i, β i ≠ -1 := fun i => by linarith [hβ i]
  have hL := G.isLimitSolution_limitCoords hβ1 hF
  set f : ℝ × (Var V E → ℝ) → ℝ := fun q => (-1 : ℝ) ^ (S.card + (G.support S).card) *
      (G.normJac S (fun e => 1 + q.1 * c e) q.2).det with hf
  have hM := G.continuousAt_normJac c (S := S) hL.ne_zero hL.ne_neg_one
  have hdet : ContinuousAt (fun q : ℝ × (Var V E → ℝ) =>
      (G.normJac S (fun e => 1 + q.1 * c e) q.2).det) ((0 : ℝ), G.limitPoint S F) :=
    (Continuous.matrix_det continuous_id).continuousAt.comp hM
  have hcont : ContinuousAt f ((0 : ℝ), G.limitPoint S F) := continuousAt_const.mul hdet
  have h1 : (fun e : E => 1 + (0 : ℝ) * c e) = fun _ => 1 := by funext e; simp
  have h0 : 0 < f ((0 : ℝ), G.limitPoint S F) := by
    have := G.pos_sign_det_normJac_limitPoint hβ hF
    simp only [hf]
    rw [h1]
    exact this
  have hev : ∀ᶠ q in nhds ((0 : ℝ), G.limitPoint S F), 0 < f q :=
    (continuousAt_const (y := (0 : ℝ))).eventually_lt hcont h0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r, hr, fun t z ht hz => ?_⟩
  have hd : dist (t, z) ((0 : ℝ), G.limitPoint S F) < r := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    exact ⟨ht, hz⟩
  have := hball hd
  simpa only [hf] using this

theorem norm_cplxPt_sub (x y : Var V E → ℝ) : ‖cplxPt x - cplxPt y‖ = ‖x - y‖ := by
  have h : cplxPt x - cplxPt y = cplxPt (x - y) := by
    funext v; simp [cplxPt]
  rw [h]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_
    simp only [cplxPt, Complex.norm_real]
    exact norm_le_pi_norm (x - y) v
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_
    rw [show ‖(x - y) v‖ = ‖cplxPt (x - y) v‖ from (Complex.norm_real _).symm]
    exact norm_le_pi_norm _ v

/-- Every real auxiliary root on a sufficiently small nonzero real parameter lies near some real limit point. -/
theorem exists_near_real_limit (c : E → ℝ) (hc : ∀ e, c e ≠ 0) (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    ∀ η > 0, ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ → ∀ z : Var V E → ℝ,
      G.IsAuxPt (fun e => 1 + t * c e) β z → ∃ P : G.LimitSolutions β, ‖z - G.limPt P‖ < η := by
  classical
  intro η hη
  set cC : E → ℂ := fun e => (c e : ℂ)
  set βC : V → ℂ := fun i => (β i : ℂ)
  have hcC : ∀ e, cC e ≠ 0 := fun e => by simpa [cC] using hc e
  have hβ0 : ∀ i, βC i ≠ 0 := fun i => by simpa [βC] using (hβ i).ne'
  have hβ1 : ∀ i, βC i ≠ -1 := fun i => by
    intro h
    have := congrArg Complex.re h
    simp [βC] at this
    linarith [hβ i]
  obtain ⟨η₀, hη₀, hsep, hmain⟩ := G.weak_coupling_master cC hcC βC hβ0 hβ1
  obtain ⟨ε₀, hε₀, hε⟩ := hmain (min η η₀) (lt_min hη hη₀) (min_le_right _ _)
  refine ⟨ε₀, hε₀, fun t ht0 ht z hz => ?_⟩
  have hε0 : (t : ℂ) ≠ 0 := by simpa using ht0
  have hεn : ‖(t : ℂ)‖ < ε₀ := by simpa [Complex.norm_real] using ht
  obtain ⟨hall, -, -⟩ := hε (t : ℂ) hε0 hεn
  have hzc : G.IsAuxPt (fun e => 1 + (t : ℂ) * cC e) βC (cplxPt z) := by
    have := hz.map Complex.ofRealHom
    unfold IsAuxPt at this ⊢
    convert this using 1 <;> funext x <;> simp [cC, βC, cplxPt]
  obtain ⟨p, hp⟩ := hall _ hzc
  -- The limit point p is real.
  have hreal : star (G.limPt p) = G.limPt p := by
    let p' : G.LimitSolutions βC :=
      ⟨(fun α => starRingEnd ℂ (p.1.1 α), fun i => starRingEnd ℂ (p.1.2 i)), by
        have := p.2.map (starRingEnd ℂ)
        convert this using 1 <;> first | rfl | (funext i; simp [βC])⟩
    have hp' : G.limPt p' = star (G.limPt p) := by
      funext v; rcases v with α | i <;> rfl
    have h1 : ‖cplxPt z - G.limPt p'‖ < min η η₀ := by
      rw [hp', ← star_cplxPt z, norm_star_sub_star]; exact hp
    have : p = p' := hsep p p' (by
      calc ‖G.limPt p - G.limPt p'‖ = ‖(cplxPt z - G.limPt p') - (cplxPt z - G.limPt p)‖ := by
            congr 1; abel
        _ ≤ ‖cplxPt z - G.limPt p'‖ + ‖cplxPt z - G.limPt p‖ := norm_sub_le _ _
        _ < 2 * η₀ := by linarith [min_le_right η η₀])
    rw [← hp', ← this]
  refine ⟨(G.realLimitEquiv β).symm ⟨p, hreal⟩, ?_⟩
  have hP : cplxPt (G.limPt ((G.realLimitEquiv β).symm ⟨p, hreal⟩)) = G.limPt p := by
    have h := (G.realLimitEquiv β).apply_symm_apply ⟨p, hreal⟩
    have h2 := congrArg (fun q => G.limPt q.1) h
    simp only at h2
    rw [← h2]
    funext v; rcases v with α | i <;> rfl
  rw [← norm_cplxPt_sub, hP]
  exact lt_of_lt_of_le hp (min_le_left _ _)

/-- **Index of each weak-coupling real root along a line.** For real c_e≠0, β_i>0 and sufficiently small real t≠0, each real auxiliary solution z along s_e=1+t c_e lies near a real limit solution with even-degree active set S, and sgn det(I−𝕁(z))=(−1)^{|S|−v(S)}, where 𝕁=diag(ℓ)M is the logarithmic-coordinate Jacobian. -/
theorem sign_det_one_sub_logJac_weak_coupling (c : E → ℝ) (hc : ∀ e, c e ≠ 0) (β : V → ℝ)
    (hβ : ∀ i, 0 < β i) :
    ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ → ∀ z : Var V E → ℝ,
      G.IsAuxPt (fun e => 1 + t * c e) β z →
        ∃ P : G.LimitSolutions β, G.IsEvenSet (activeSet P.1.1) ∧
          0 < (-1) ^ ((activeSet P.1.1).card + (G.support (activeSet P.1.1)).card) *
            (1 - G.logJac (fun e => 1 + t * c e) z).det := by
  classical
  have hcard := G.card_real_limitSolutions β hβ
  have : Finite (G.LimitSolutions β) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : Fintype (G.LimitSolutions β) := Fintype.ofFinite _
  have hnb : ∀ P : G.LimitSolutions β, ∃ r > 0, ∀ t : ℝ, ∀ z : Var V E → ℝ, |t| < r →
      ‖z - G.limPt P‖ < r → 0 < (-1) ^ ((activeSet P.1.1).card + (G.support (activeSet P.1.1)).card) *
        (G.normJac (activeSet P.1.1) (fun e => 1 + t * c e) z).det := by
    intro P
    rw [limPt_eq_limitPoint]
    exact G.exists_nhds_pos_sign_normJac c hβ P.2.vertexLimitEq
  choose r hr hrP using hnb
  obtain ⟨η, hη, hηle⟩ := exists_pos_forall_le r hr
  obtain ⟨ε₁, hε₁, hnear⟩ := G.exists_near_real_limit c hc β hβ η hη
  refine ⟨min ε₁ η, lt_min hε₁ hη, fun t ht0 ht z hz => ?_⟩
  obtain ⟨P, hP⟩ := hnear t ht0 (lt_of_lt_of_le ht (min_le_left _ _)) z hz
  set S := activeSet P.1.1
  have heven : G.IsEvenSet S := fun i =>
    (even_and_pos_of_vertexLimitEq_real (hβ i) (P.2.vertexLimitEq i)).1
  refine ⟨P, heven, ?_⟩
  have h1 := hrP P t z (lt_of_lt_of_le (lt_of_lt_of_le ht (min_le_right _ _)) (hηle P))
    (lt_of_lt_of_le hP (hηle P))
  rw [G.det_normJac_eq hz] at h1
  have hprod : 0 < ∏ e ∈ S, ((1 + t * c e) - 1) ^ 2 := Finset.prod_pos fun e _ => by
    have : (1 + t * c e) - 1 ≠ 0 := by simpa using mul_ne_zero ht0 (hc e)
    positivity
  have : 0 < (∏ e ∈ S, ((1 + t * c e) - 1) ^ 2) *
      ((-1) ^ (S.card + (G.support S).card) * (1 - G.logJac (fun e => 1 + t * c e) z).det) := by
    linarith [h1, show (-1 : ℝ) ^ (S.card + (G.support S).card) *
      ((∏ e ∈ S, ((1 + t * c e) - 1) ^ 2) * (1 - G.logJac (fun e => 1 + t * c e) z).det) =
      (∏ e ∈ S, ((1 + t * c e) - 1) ^ 2) *
      ((-1) ^ (S.card + (G.support S).card) * (1 - G.logJac (fun e => 1 + t * c e) z).det) by ring]
  exact pos_of_mul_pos_right this hprod.le

end Real

end Multigraph

end BPFixedPoints
