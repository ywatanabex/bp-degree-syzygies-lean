import BPFixedPoints.Real.BoundedParity
import BPFixedPoints.Real.SectorRegularity

/-!
# Odd nondegenerate solution counts in Eulerian sign sectors

Normalize the vertex map by its diagonal linear part and apply oddness for
bounded perturbations of identity. The coordinate correspondence has inverse
given by logarithms of total fields.
-/

namespace BPFixedPoints

open Set

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  {G : Multigraph V E} {a : E → ℝ}

/-- A regular Eulerian vertex fiber has odd cardinality. -/
theorem odd_card_sectorField_fiber (ha : ∀ e, 0 < a e) {S : Finset E}
    (hS : G.IsEvenSet S) (h : V → ℝ)
    (hnd : ∀ u, G.sectorField a S u = h →
      Function.Injective (fderiv ℝ (G.sectorField a S) u)) :
    Odd (Nat.card {u : V → ℝ // G.sectorField a S u = h}) := by
  classical
  have hk : ∀ i, (1 - (G.deg S i : ℝ)) ≠ 0 := by
    intro i hz
    have : (G.deg S i : ℝ) = 1 := by linarith
    have h1 : G.deg S i = 1 := by exact_mod_cast this
    exact Nat.not_even_one (h1 ▸ hS i)
  have hk1 : ∀ i, 1 ≤ |1 - (G.deg S i : ℝ)| := by
    intro i
    obtain ⟨m, hm⟩ := hS i
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [hm]
    · have : (2 : ℝ) ≤ G.deg S i := by exact_mod_cast (by omega : 2 ≤ G.deg S i)
      rw [abs_of_nonpos (by linarith)]; linarith
  let B : (V → ℝ) → (V → ℝ) := fun u i =>
    (∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α) / (1 - (G.deg S i : ℝ))
  have hBc : ContDiff ℝ 1 B := by
    refine contDiff_pi.2 fun i => ?_
    refine ContDiff.div_const ?_ _
    exact ContDiff.sum fun α _ => contDiff_const.mul (contDiff_zP ha α)
  let M : ℝ := ∑ α : Dart E, |Real.log (a α.1)| / 2
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun α _ => by positivity
  have hBb : ∀ u, ‖B u‖ ≤ M := by
    intro u
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    simp only [B]
    rw [abs_div]
    calc |∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α| / |1 - (G.deg S i : ℝ)|
        ≤ |∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α| :=
          div_le_self (abs_nonneg _) (hk1 i)
      _ ≤ ∑ α ∈ G.inDarts i, |sgnS S α * G.zP a u α| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [abs_mul]
          have : |sgnS S α| = 1 := by unfold sgnS; split_ifs <;> simp
          rw [this, one_mul]
          exact abs_zPlus_le (ha α.1) _ _
      _ ≤ M := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun α _ _ => by positivity)
  let L : (V → ℝ) →L[ℝ] (V → ℝ) := ContinuousLinearMap.pi fun i =>
    (1 - (G.deg S i : ℝ)) • ContinuousLinearMap.proj i
  have hfun : G.sectorField a S = L ∘ (fun u => u - B u) := by
    funext u i
    change (1 - (G.deg S i : ℝ)) * u i - _ =
      (1 - (G.deg S i : ℝ)) * (u i - _ / (1 - (G.deg S i : ℝ)))
    field_simp [hk i]
  have heq : ∀ u, u - B u = (fun i => h i / (1 - (G.deg S i : ℝ))) ↔
      G.sectorField a S u = h := by
    intro u
    constructor
    · intro hu
      funext i
      have hi := congrFun hu i
      simp only [B, Pi.sub_apply] at hi
      unfold sectorField
      have := hk i
      field_simp at hi
      linear_combination hi
    · intro hu
      funext i
      have hi := congrFun hu i
      simp only [sectorField] at hi
      change u i - _ / (1 - (G.deg S i : ℝ)) = h i / (1 - (G.deg S i : ℝ))
      field_simp [hk i]
      linear_combination hi
  have hBnd : ∀ u, u - B u = (fun i => h i / (1 - (G.deg S i : ℝ))) →
      Function.Injective (fderiv ℝ (fun u => u - B u) u) := by
    intro u hu v w hvw
    have hinj := hnd u ((heq u).1 hu)
    apply hinj
    have hd : HasFDerivAt (G.sectorField a S)
        (L.comp (fderiv ℝ (fun u => u - B u) u)) u := by
      rw [hfun]
      exact L.hasFDerivAt.comp u
        (((contDiff_id.sub hBc).differentiable one_ne_zero u).hasFDerivAt)
    rw [hd.fderiv]
    exact congrArg L hvw
  have ho := odd_card_fiber_sub_of_bounded hBc hBb
    (fun i => h i / (1 - (G.deg S i : ℝ))) hBnd
  let e : {u : V → ℝ // u - B u = (fun i => h i / (1 - (G.deg S i : ℝ)))} ≃
      {u : V → ℝ // G.sectorField a S u = h} := Equiv.subtypeEquivRight heq
  rwa [Nat.card_congr e] at ho

/-- Equivalence between vertex coordinates and admissible BP solutions in a sign sector. -/
noncomputable def sectorFieldFiberEquiv (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S) :
    {u : V → ℝ // G.sectorField a S u = fun i => Real.log (b i) / 2} ≃
      {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = S} where
  toFun u := ⟨G.sectorMsg a S u.1,
    isAdmissibleSolution_sectorMsg ha ha1 hG hS hb (congrFun u.2),
    negSupport_sectorMsg ha ha1⟩
  invFun y := ⟨fun i => Real.log (G.totalField b y.1 i) / 2, by
    obtain ⟨_, hu⟩ := eq_sectorMsg ha ha1 hG hb y.2.1
    rw [y.2.2] at hu
    exact funext hu⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    have ht := (totalField_sectorMsg_iff ha hG hS hb i).2 (congrFun u.2 i)
    change Real.log (G.totalField b (G.sectorMsg a S u.1) i) / 2 = u.1 i
    rw [ht, Real.log_exp]
    ring
  right_inv y := by
    apply Subtype.ext
    obtain ⟨hy, _⟩ := eq_sectorMsg ha ha1 hG hb y.2.1
    rw [y.2.2] at hy
    exact hy.symm

/-- A sector with nondegenerate BP Jacobians has an odd number of solutions. -/
theorem odd_card_sector_solutions (hG : G.Loopless) (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E}
    (hS : G.IsEvenSet S)
    (hnd : ∀ y, G.IsAdmissibleSolution a b y → negSupport y = S →
      G.IsSimpleSolution a b y) :
    Odd (Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = S}) := by
  have ho := odd_card_sectorField_fiber ha hS (fun i => Real.log (b i) / 2) (by
    intro u hu
    apply fderiv_sectorField_injective_of_isSimpleSolution hG ha ha1 hb hS (congrFun hu)
    exact hnd _ (isAdmissibleSolution_sectorMsg ha ha1 hG hS hb (congrFun hu))
      (negSupport_sectorMsg ha ha1))
  rwa [Nat.card_congr (sectorFieldFiberEquiv hG ha ha1 hb hS)] at ho

end Multigraph

end BPFixedPoints
