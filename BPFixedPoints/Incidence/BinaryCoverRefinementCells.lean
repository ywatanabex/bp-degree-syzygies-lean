import BPFixedPoints.Incidence.CechCubicalCellBoundary
import BPFixedPoints.Incidence.CechCubicalCellMaps
import BPFixedPoints.Incidence.CechCubicalCellDegree

/-! # Forgetting cubical directions along an injective relabelling of directions

Let `ι : I → K` be an injective map of finite direction sets. A cell
`q : K → Fin 3` of the `K`-cube is sent to its restriction `q ∘ ι` when every
overlap coordinate of `q` lies in the image of `ι`, and to zero otherwise. On
one interval direction outside the image this is `l, r ↦ 1` and `e ↦ 0`: the
boundary `l - r` of the overlap edge is killed.

The cell boundaries use the enumerations `Fintype.equivFin I` and
`Fintype.equivFin K`, and their prefix signs count earlier overlap coordinates
in these two different orders. The restriction therefore carries the explicit
sign `(-1)^N`, where `N` (`relabelInversions`) counts the ordered pairs of
overlap coordinates of `q ∘ ι` whose order in the enumeration of `I` is
reversed in the enumeration of `K`. No enumeration is assumed to be compatible
with `ι`.

Proved here, on free cells with coefficients in any commutative ring:
* the sign step `relabel_sign_step` relating the two prefix signs;
* `relabelCells_d`: the signed restriction commutes with the two cell boundaries;
* `relabelCells_degree`: it preserves the overlap degree;
* `relabelCells_p`: it is compatible with the two component augmentations.

Nothing about sheaves, covers or availability is proved in this module.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct Function
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
variable (R : Type*) [CommRing R]

/-- Removing one element from a finite set ordered in two ways: the inversion count and the two
prefix counts of the removed element differ by an even number. -/
theorem inversion_insert_count {X : Type*} [DecidableEq X] (α β : X → ℕ)
    (hα : Injective α) (hβ : Injective β) (S : Finset X) (i : X) (hi : i ∉ S) :
    (∑ a ∈ insert i S, ∑ b ∈ insert i S, if α a < α b ∧ β b < β a then 1 else 0) +
        (∑ a ∈ insert i S, if α a < α i then 1 else 0) =
      (∑ a ∈ S, ∑ b ∈ S, if α a < α b ∧ β b < β a then 1 else 0) +
        (∑ a ∈ insert i S, if β a < β i then 1 else 0) +
          2 * ∑ a ∈ S, if α a < α i ∧ β i < β a then 1 else 0 := by
  simp only [Finset.sum_insert hi, lt_irrefl, and_false, ite_false, zero_add]
  have key : ∀ a ∈ S, ((if α i < α a ∧ β a < β i then 1 else 0) +
      (if α a < α i ∧ β i < β a then 1 else 0) + (if α a < α i then 1 else 0) : ℕ) =
      (if β a < β i then 1 else 0) + 2 * (if α a < α i ∧ β i < β a then 1 else 0) := by
    intro a ha
    have hai : a ≠ i := fun h => hi (h ▸ ha)
    have h1 : α a ≠ α i := hα.ne hai
    have h2 : β a ≠ β i := hβ.ne hai
    split_ifs <;> omega
  have hs := Finset.sum_congr rfl key
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [Finset.sum_add_distrib]
  omega

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- The overlap coordinates of a cell. -/
def overlapSet (p : I → Fin 3) : Finset I := Finset.univ.filter fun a => p a = 2

/-- Ordered pairs of overlap coordinates of `p` whose order in the enumeration of `I` is reversed
by the enumeration of `K` along `ι`. -/
noncomputable def relabelInversions (ι : I → K) (p : I → Fin 3) : ℕ :=
  ∑ a ∈ overlapSet p, ∑ b ∈ overlapSet p,
    if (Fintype.equivFin I a : ℕ) < Fintype.equivFin I b ∧
      (Fintype.equivFin K (ι b) : ℕ) < Fintype.equivFin K (ι a) then 1 else 0

/-- The coefficient of the signed restriction: zero if some overlap coordinate lies outside the
image of `ι`, and otherwise the inversion sign of the restricted cell. -/
noncomputable def relabelCoefficient (ι : I → K) (q : K → Fin 3) : R :=
  if ∀ k, q k = 2 → ∃ a, ι a = k then (-1 : R)^relabelInversions ι (q ∘ ι) else 0

/-- The signed restriction of cells along `ι`, forgetting the directions outside its image. -/
noncomputable def relabelCells (ι : I → K) : Cells R K →ₗ[R] Cells R I :=
  Finsupp.linearCombination R (fun q => single (q ∘ ι) (relabelCoefficient R ι q))

/-- The signed restriction on one cell. -/
theorem relabelCells_single (ι : I → K) (q : K → Fin 3) (r : R) :
    relabelCells R ι (single q r) = single (q ∘ ι) (r * relabelCoefficient R ι q) := by
  rw [relabelCells, linearCombination_single, smul_single, smul_eq_mul]

/-- The prefix in the enumeration of `I` counts earlier overlap coordinates of the cell. -/
theorem faceBoundaryPrefix_eq_sum (p : I → Fin 3) (i : I) :
    faceBoundaryPrefix p i = ∑ a ∈ overlapSet p,
      if (Fintype.equivFin I a : ℕ) < Fintype.equivFin I i then 1 else 0 := by
  rw [overlapSet, Finset.sum_filter]
  unfold faceBoundaryPrefix
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : p a = 2 <;> simp [h]

/-- When all overlap coordinates lie in the image, the prefix in the enumeration of `K` counts
earlier overlap coordinates of the restricted cell in the order induced from `K`. -/
theorem faceBoundaryPrefix_relabel (ι : I → K) (hι : Injective ι) (q : K → Fin 3)
    (hq : ∀ k, q k = 2 → ∃ a, ι a = k) (i : I) :
    faceBoundaryPrefix q (ι i) = ∑ a ∈ overlapSet (q ∘ ι),
      if (Fintype.equivFin K (ι a) : ℕ) < Fintype.equivFin K (ι i) then 1 else 0 := by
  rw [overlapSet, Finset.sum_filter]
  unfold faceBoundaryPrefix
  symm
  apply Fintype.sum_of_injective ι hι
  · intro k hk
    have h : q k ≠ 2 := fun h => hk (hq k h)
    simp [h]
  · intro a
    by_cases h : q (ι a) = 2 <;> simp [h]

/-- Replacing an overlap coordinate by an endpoint removes it from the overlap set. -/
theorem overlapSet_update (p : I → Fin 3) (i : I) (c : Fin 3) (hc : c ≠ 2) :
    overlapSet (update p i c) = (overlapSet p).erase i := by
  ext a
  by_cases h : a = i
  · subst h
    simp [overlapSet, hc]
  · simp [overlapSet, h]

/-- The sign step: the inversion sign times the prefix sign in `I` equals the inversion sign of
the endpoint face times the prefix sign in `K`. -/
theorem relabel_sign_step (ι : I → K) (hι : Injective ι) (q : K → Fin 3)
    (hq : ∀ k, q k = 2 → ∃ a, ι a = k) (i : I) (hi : q (ι i) = 2) (c : Fin 3) (hc : c ≠ 2) :
    (-1 : R)^relabelInversions ι (q ∘ ι) * (-1)^faceBoundaryPrefix (q ∘ ι) i =
      (-1)^relabelInversions ι (update (q ∘ ι) i c) * (-1)^faceBoundaryPrefix q (ι i) := by
  have hiS : i ∈ overlapSet (q ∘ ι) := by simp [overlapSet, hi]
  have hS := Finset.insert_erase hiS
  have hα : Injective fun a : I => (Fintype.equivFin I a : ℕ) :=
    Fin.val_injective.comp (Fintype.equivFin I).injective
  have hβ : Injective fun a : I => (Fintype.equivFin K (ι a) : ℕ) :=
    Fin.val_injective.comp ((Fintype.equivFin K).injective.comp hι)
  have h := inversion_insert_count _ _ hα hβ ((overlapSet (q ∘ ι)).erase i) i
    (Finset.notMem_erase i _)
  rw [hS] at h
  rw [← pow_add, ← pow_add, faceBoundaryPrefix_eq_sum, faceBoundaryPrefix_relabel ι hι q hq i]
  unfold relabelInversions
  rw [overlapSet_update _ i c hc, h, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- An overlap coordinate outside the image kills the coefficient. -/
theorem relabelCoefficient_of_outside (ι : I → K) (q : K → Fin 3) (k : K) (hk : q k = 2)
    (hout : ∀ a, ι a ≠ k) : relabelCoefficient R ι q = 0 := by
  rw [relabelCoefficient, ite_eq_right]
  intro h
  obtain ⟨a, ha⟩ := h k hk
  exact hout a ha

/-- Changing an image coordinate keeps all overlap coordinates in the image. -/
theorem relabelCoefficient_update_image (ι : I → K) (hι : Injective ι) (q : K → Fin 3)
    (hq : ∀ k, q k = 2 → ∃ a, ι a = k) (i : I) (c : Fin 3) :
    relabelCoefficient R ι (update q (ι i) c) =
      (-1 : R)^relabelInversions ι (update (q ∘ ι) i c) := by
  rw [relabelCoefficient, ite_eq_left, update_comp_eq_of_injective _ hι]
  intro k hk
  by_cases hk' : k = ι i
  · exact ⟨i, hk'.symm⟩
  · rw [update_of_ne hk'] at hk
    exact hq k hk

/-- Changing a coordinate outside the image does not change the restricted cell. -/
theorem update_comp_outside (ι : I → K) (q : K → Fin 3) (k : K) (hout : ∀ a, ι a ≠ k)
    (c : Fin 3) : update q k c ∘ ι = q ∘ ι := by
  funext a
  exact update_of_ne (hout a) c q

/-- Changing a coordinate outside the image to an endpoint gives a coefficient independent of
the endpoint. -/
theorem relabelCoefficient_update_outside (ι : I → K) (q : K → Fin 3) (k : K)
    (hout : ∀ a, ι a ≠ k) (c c' : Fin 3) (hc : c ≠ 2) (hc' : c' ≠ 2) :
    relabelCoefficient R ι (update q k c) = relabelCoefficient R ι (update q k c') := by
  have hcond : ∀ d : Fin 3, d ≠ 2 → ((∀ k', update q k d k' = 2 → ∃ a, ι a = k') ↔
      ∀ k', k' ≠ k → q k' = 2 → ∃ a, ι a = k') := by
    intro d hd
    constructor
    · intro h k' hk' hq
      exact h k' (by rw [update_of_ne hk']; exact hq)
    · intro h k' hq
      by_cases hk' : k' = k
      · subst hk'
        rw [Function.update_self] at hq
        exact (hd hq).elim
      · rw [update_of_ne hk'] at hq
        exact h k' hk' hq
  unfold relabelCoefficient
  rw [update_comp_outside ι q k hout c, update_comp_outside ι q k hout c']
  by_cases h : ∀ k', k' ≠ k → q k' = 2 → ∃ a, ι a = k'
  · rw [ite_eq_left ((hcond c hc).mpr h), ite_eq_left ((hcond c' hc').mpr h)]
  · rw [ite_eq_right (fun h' => h ((hcond c hc).mp h')), ite_eq_right (fun h' => h ((hcond c' hc').mp h'))]

/-- The signed restriction commutes with the two cell boundaries. -/
theorem relabelCells_d (ι : I → K) (hι : Injective ι) :
    (relabelCells R ι).comp (contraction R (fun _ : K => 0)).d =
      (contraction R (fun _ : I => 0)).d.comp (relabelCells R ι) := by
  apply Finsupp.lhom_ext
  intro q r
  simp only [LinearMap.comp_apply, relabelCells_single, contraction_d_single, map_sum, map_sub]
  by_cases hq : ∀ k, q k = 2 → ∃ a, ι a = k
  · rw [relabelCoefficient, ite_eq_left hq]
    symm
    apply Fintype.sum_of_injective ι hι
    · intro k hk
      have h : q k ≠ 2 := fun h => hk (hq k h)
      simp [h]
    · intro i
      by_cases hi : q (ι i) = 2
      · have h0 := relabel_sign_step R ι hι q hq i hi 0 (by decide)
        have h1 := relabel_sign_step R ι hι q hq i hi 1 (by decide)
        rw [relabelCoefficient_update_image R ι hι q hq i 0,
          relabelCoefficient_update_image R ι hι q hq i 1,
          update_comp_eq_of_injective _ hι, update_comp_eq_of_injective _ hι]
        simp only [comp_apply, hi, ite_true, one_mul]
        congr 2
        · linear_combination r * h0
        · linear_combination r * h1
      · simp [hi]
  · push Not at hq
    obtain ⟨k, hk, hout⟩ := hq
    rw [relabelCoefficient_of_outside R ι q k hk hout]
    simp only [mul_zero, single_zero, sub_self, Finset.sum_const_zero]
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : v = k
    · subst hv
      rw [update_comp_outside ι q v hout 0, update_comp_outside ι q v hout 1,
        relabelCoefficient_update_outside R ι q v hout 0 1 (by decide) (by decide), sub_self]
    · have h0 : relabelCoefficient R ι (update q v 0) = 0 :=
        relabelCoefficient_of_outside R ι _ k (by rw [update_of_ne (Ne.symm hv)]; exact hk) hout
      have h1 : relabelCoefficient R ι (update q v 1) = 0 :=
        relabelCoefficient_of_outside R ι _ k (by rw [update_of_ne (Ne.symm hv)]; exact hk) hout
      rw [h0, h1]
      simp

/-- A linear map of free modules carrying each generator of `s` into `supported t` carries
`supported s` into `supported t`. -/
theorem map_supported_of_single {α β : Type*} {f : (α →₀ R) →ₗ[R] (β →₀ R)} {s : Set α}
    {t : Set β} (h : ∀ a ∈ s, f (single a 1) ∈ supported R R t) {x : α →₀ R}
    (hx : x ∈ supported R R s) : f x ∈ supported R R t := by
  have hle : supported R R s ≤ (supported R R t).comap f := by
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  exact hle hx

/-- When all overlap coordinates lie in the image, the restriction has the same overlap degree. -/
theorem faceDegree_comp_of_image (ι : I → K) (hι : Injective ι) (q : K → Fin 3)
    (hq : ∀ k, q k = 2 → ∃ a, ι a = k) : faceDegree (q ∘ ι) = faceDegree q := by
  unfold faceDegree
  apply Fintype.sum_of_injective ι hι
  · intro k hk
    have h : q k ≠ 2 := fun h => hk (hq k h)
    simp [h]
  · intro a
    rfl

/-- The signed restriction preserves the overlap degree. -/
theorem relabelCells_degree (ι : I → K) (hι : Injective ι) (n : ℤ) {x : Cells R K}
    (hx : x ∈ supported R R {q | cellDegree q = n}) :
    relabelCells R ι x ∈ supported R R {p : I → Fin 3 | cellDegree p = n} := by
  refine map_supported_of_single R (fun q hq => ?_) hx
  rw [relabelCells_single]
  by_cases hc : ∀ k, q k = 2 → ∃ a, ι a = k
  · apply single_mem_supported R
    change cellDegree (q ∘ ι) = n
    rw [cellDegree, faceDegree_comp_of_image ι hι q hc]
    exact hq
  · rw [relabelCoefficient, ite_eq_right hc, mul_zero, single_zero]
    exact Submodule.zero_mem _

/-- The labelled component projection kills exactly the cells with an overlap coordinate. -/
theorem contraction_p_single {V : Type*} [Fintype V] (b : V → Fin 2) (q : V → Fin 3) (r : R) :
    (contraction R b).p (single q r) = if ∃ v, q v = 2 then 0 else single (fun _ => 0) r := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  let eh := e.arrowCongr (Equiv.refl (Fin 1))
  change (Finsupp.mapDomain.linearEquiv R R eh)
    ((finContraction R (Fintype.card V) (fun i => b (e i))).p
      ((Finsupp.mapDomain.linearEquiv R R ep).symm (single q r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain eh ((finContraction R (Fintype.card V) (fun i => b (e i))).p
    (mapDomain ep.symm (single q r))) = _
  rw [mapDomain_single, finContraction_p_single]
  have hex : (∃ v, (ep.symm q) v = 2) ↔ ∃ v, q v = 2 := by
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨e v, hv⟩
    · rintro ⟨v, hv⟩
      refine ⟨e.symm v, ?_⟩
      change q (e (e.symm v)) = 2
      rw [Equiv.apply_symm_apply]
      exact hv
  by_cases h : ∃ v, q v = 2
  · rw [ite_eq_left (hex.mpr h), ite_eq_left h, mapDomain_zero]
  · rw [ite_eq_right (mt hex.mp h), ite_eq_right h, mapDomain_single]
    congr 1

/-- The signed restriction is compatible with the two component augmentations. -/
theorem relabelCells_p (ι : I → K) :
    (contraction R (fun _ : I => 0)).p.comp (relabelCells R ι) =
      (Finsupp.lmapDomain R R (fun f : K → Fin 1 => f ∘ ι)).comp
        (contraction R (fun _ : K => 0)).p := by
  apply Finsupp.lhom_ext
  intro q r
  simp only [LinearMap.comp_apply, relabelCells_single, contraction_p_single,
    Finsupp.lmapDomain_apply]
  by_cases h0 : ∃ v, q v = 2
  · rw [ite_eq_left h0, mapDomain_zero]
    by_cases hq : ∀ k, q k = 2 → ∃ a, ι a = k
    · obtain ⟨v, hv⟩ := h0
      obtain ⟨a, rfl⟩ := hq v hv
      rw [ite_eq_left ⟨a, hv⟩]
    · rw [relabelCoefficient, ite_eq_right hq, mul_zero, single_zero]
      split_ifs <;> rfl
  · have hq : ∀ k, q k = 2 → ∃ a, ι a = k := fun k hk => (h0 ⟨k, hk⟩).elim
    have h0' : ¬∃ a, (q ∘ ι) a = 2 := fun ⟨a, ha⟩ => h0 ⟨ι a, ha⟩
    have hS : overlapSet (q ∘ ι) = ∅ := by
      ext a
      simp only [overlapSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      exact fun ha => h0' ⟨a, ha⟩
    rw [ite_eq_right h0', ite_eq_right h0, mapDomain_single, relabelCoefficient, ite_eq_left hq,
      relabelInversions, hS, Finset.sum_empty, pow_zero, mul_one]
    rfl

end BPFixedPoints.CechCubicalCell
