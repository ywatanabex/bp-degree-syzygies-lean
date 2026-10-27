import BPFixedPoints.Incidence.IncidenceUniversalKoszulSection
import BPFixedPoints.Incidence.Koszul
import BPFixedPoints.Incidence.SchemeModuleOpenRestrictions

/-! # The universal Koszul complex as a complex of sheaves of modules

The paper's universal Koszul complex (eq. `alg:universal-koszul`)
`K_G^{-k} = ∧^k F_G^∨ ⊗ S_G(-k)`, `d = ι_{s^univ}`, as an actual chain complex of sheaves of
modules on `(ℙ¹)^V` over the coefficient ring (cohomological degree `-k` is homological degree
`k`). Everything works over an arbitrary commutative base ring `R` with arbitrary edge
coefficients `κ`; `incUniversalKoszulComplex` is the case `R = S_G`, `κ = c`.

* **Graded Koszul algebra.** `gradedKoszul f k` is the Koszul differential on families indexed
  by `(k+1)`-element edge subsets, `(K y)_T = Σ_{e ∉ T} sign(T, e) f_e y_{T ∪ {e}}`, with the
  exterior sign `Koszul.sign T e` of `Koszul.erase` (`koszul_differential_apply` is the closed
  form of `Koszul.differential`). `koszulEmbed` and `koszulProj` compare it with the total
  exterior module `Koszul.Space E A` (`koszul_differential_embed`, `koszulProj_differential`); it
  squares to zero (`gradedKoszul_gradedKoszul`), commutes with ring maps (`gradedKoszul_map`),
  is exact in positive degrees whenever the total Koszul complex has a contraction whose
  projection only sees the empty edge set (`gradedKoszul_exact_of_contraction`), and its
  degree-zero image is the ideal of the `f_e` (`gradedKoszul_zero_range`).
* **The differential of sheaves.** `univKoszulDifferential κ k : ∧^{k+1} F^∨ ⟶ ∧^k F^∨` has
  component `sign(T, e) · s_e : O(-d_{T ∪ {e}}) ⟶ O(-d_T)` for `e ∉ T` and zero otherwise
  (`univKoszulDifferential_app`); `s_e` is `edgeSectionMul` of
  `IncidenceUniversalKoszulSection.lean`. The signs are those of `incKoszulPerturbation`.
* **Frames.** On every subopen of a chart, in the chart frames, the differential is the graded
  Koszul differential of the chart functions of the edge sections (`univKoszulDifferential_chart`);
  on every face open, in the frame of the face's own chart, it is the graded Koszul differential
  of the face edge sections `edgeFaceSection κ e q` (`univKoszulDifferential_face`).
* **The complex.** `d ∘ d = 0` (`univKoszulDifferential_comp`, checked in chart frames on the
  chart cover), and `univKoszulComplex κ` is the chain complex of sheaves of modules;
  `incUniversalKoszulComplex` is `K_G`.

Exactness on charts and faces and the comparison with the face and total complexes are in
`IncidenceUniversalKoszulFaces.lean` and `IncidenceUniversalKoszulCech.lean`. The internal grading
`S_G(-k)` is not part of the sheaf-level complex here (it is compared on the Čech model).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8000

/-! ### The graded Koszul differential on families indexed by edge subsets -/

section Graded

variable {E : Type} [LinearOrder E] [Fintype E] {A : Type*} [CommRing A]

/-- Insert an edge outside a `k`-element edge subset, giving a `(k+1)`-element edge subset. -/
def powersetCardInsert {k : ℕ} (T : Set.powersetCard E k) (e : E) (he : e ∉ (T : Finset E)) :
    Set.powersetCard E (k + 1) :=
  ⟨insert e (T : Finset E), by
    rw [Set.powersetCard.mem_iff, Finset.card_insert_of_notMem he, Set.powersetCard.card_eq]⟩

/-- The underlying edge set of `powersetCardInsert T e he` is `insert e T`. -/
@[simp] theorem powersetCardInsert_coe {k : ℕ} (T : Set.powersetCard E k) (e : E)
    (he : e ∉ (T : Finset E)) : (powersetCardInsert T e he : Finset E) = insert e (T : Finset E) :=
  rfl

/-- **The graded Koszul differential.** For `f : E → A`, the map from families indexed by
`(k+1)`-element edge subsets to families indexed by `k`-element subsets,
`(K y)_T = Σ_{e ∉ T} sign(T, e) f_e y_{T ∪ {e}}`, with the exterior sign `Koszul.sign T e` of
removing `e` from `T ∪ {e}`. -/
noncomputable def gradedKoszul (f : E → A) (k : ℕ) :
    (Set.powersetCard E (k + 1) → A) →ₗ[A] (Set.powersetCard E k → A) :=
  LinearMap.pi fun T => ∑ e : E, if h : e ∉ (T : Finset E) then
    (Koszul.sign (T : Finset E) e * f e) • LinearMap.proj (powersetCardInsert T e h) else 0

/-- The graded Koszul differential at a `k`-element edge subset `T`. -/
theorem gradedKoszul_apply (f : E → A) (k : ℕ) (y : Set.powersetCard E (k + 1) → A)
    (T : Set.powersetCard E k) :
    gradedKoszul f k y T = ∑ e : E, if h : e ∉ (T : Finset E) then
      Koszul.sign (T : Finset E) e * f e * y (powersetCardInsert T e h) else 0 := by
  simp only [gradedKoszul, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [smul_eq_mul]

/-- The family indexed by `k`-element edge subsets as an element of the total exterior module
`Koszul.Space E A`. -/
noncomputable def koszulEmbed (k : ℕ) : (Set.powersetCard E k → A) →ₗ[A] Koszul.Space E A :=
  ∑ T : Set.powersetCard E k, (Finsupp.lsingle (T : Finset E)).comp (LinearMap.proj T)

/-- The `k`-th graded piece of an element of the total exterior module. -/
noncomputable def koszulProj (k : ℕ) : Koszul.Space E A →ₗ[A] (Set.powersetCard E k → A) :=
  LinearMap.pi fun T => Finsupp.lapply (T : Finset E)

/-- The `k`-th graded piece reads the coefficients of the `k`-element edge subsets. -/
@[simp] theorem koszulProj_apply (k : ℕ) (z : Koszul.Space E A) (T : Set.powersetCard E k) :
    koszulProj k z T = z (T : Finset E) := rfl

/-- The embedding puts the family on the edge subsets of cardinality `k` and zero elsewhere. -/
theorem koszulEmbed_apply (k : ℕ) (y : Set.powersetCard E k → A) (S : Finset E) :
    koszulEmbed k y S = if h : S.card = k then y ⟨S, h⟩ else 0 := by
  simp only [koszulEmbed, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Finsupp.lsingle_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨S, h⟩]
    · simp
    · intro T _ hT
      rw [Finsupp.single_eq_of_ne]
      intro hTS
      exact hT (Subtype.ext hTS.symm)
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  · refine Finset.sum_eq_zero fun T _ => ?_
    rw [Finsupp.single_eq_of_ne]
    intro hTS
    exact h (hTS ▸ T.2)

/-- The `k`-th graded piece of the embedding of a family of degree `k` is the family. -/
@[simp] theorem koszulProj_koszulEmbed (k : ℕ) (y : Set.powersetCard E k → A) :
    koszulProj k (koszulEmbed k y) = y := by
  funext T
  rw [koszulProj_apply, koszulEmbed_apply, dite_eq_left (Set.powersetCard.card_eq T)]

/-- The contraction `erase e` evaluated at a subset `T`. -/
theorem koszul_erase_apply (e : E) (z : Koszul.Space E A) (T : Finset E) :
    Koszul.erase e z T = if e ∉ T then Koszul.sign T e * z (insert e T) else 0 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    split_ifs <;> ring
  | single S a =>
    rw [Koszul.erase_single]
    by_cases heT : e ∈ T
    · have hn : ¬ (e ∉ T) := not_not.mpr heT
      simp only [hn, ite_false]
      split_ifs with he
      · rw [Finsupp.single_apply, ite_eq_right]
        intro h
        rw [← h] at heT
        exact Finset.notMem_erase e S heT
      · rfl
    · simp only [heT, not_false_eq_true, ite_true]
      split_ifs with he
      · rw [Finsupp.single_apply, Finsupp.single_apply]
        by_cases hT : S.erase e = T
        · subst hT
          rw [ite_eq_left rfl, Finset.insert_erase he, ite_eq_left rfl, Koszul.sign_erase_self]
        · rw [ite_eq_right hT, ite_eq_right, mul_zero]
          intro hins
          apply hT
          rw [hins, Finset.erase_insert heT]
      · rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply, ite_eq_right, mul_zero]
        intro hins
        exact he (hins ▸ Finset.mem_insert_self e T)

/-- **The Koszul differential in closed form.** At a subset `T`, the Koszul differential is
`Σ_{e ∉ T} sign(T, e) f_e z_{T ∪ {e}}`. -/
theorem koszul_differential_apply (f : E → A) (z : Koszul.Space E A) (T : Finset E) :
    Koszul.differential f z T = ∑ e : E, if e ∉ T then
      Koszul.sign T e * f e * z (insert e T) else 0 := by
  simp only [Koszul.differential, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, koszul_erase_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> ring

/-- Projection to the `k`-th piece intertwines the Koszul differential with the graded one. -/
theorem koszulProj_differential (f : E → A) (k : ℕ) (z : Koszul.Space E A) :
    koszulProj k (Koszul.differential f z) = gradedKoszul f k (koszulProj (k + 1) z) := by
  funext T
  rw [koszulProj_apply, koszul_differential_apply, gradedKoszul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · rw [ite_eq_left h, dite_eq_left h]
    rfl
  · rw [ite_eq_right h, dite_eq_right h]

/-- The embedding intertwines the graded Koszul differential with the Koszul differential. -/
theorem koszul_differential_embed (f : E → A) (k : ℕ) (y : Set.powersetCard E (k + 1) → A) :
    Koszul.differential f (koszulEmbed (k + 1) y) = koszulEmbed k (gradedKoszul f k y) := by
  ext T
  rw [koszul_differential_apply, koszulEmbed_apply]
  split_ifs with hT
  · rw [gradedKoszul_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : e ∉ T
    · rw [ite_eq_left he, dite_eq_left he, koszulEmbed_apply,
        dite_eq_left (by rw [Finset.card_insert_of_notMem he, hT])]
      rfl
    · rw [ite_eq_right he, dite_eq_right he]
  · refine Finset.sum_eq_zero fun e _ => ?_
    by_cases he : e ∉ T
    · rw [ite_eq_left he, koszulEmbed_apply, dite_eq_right, mul_zero]
      rw [Finset.card_insert_of_notMem he]
      omega
    · rw [ite_eq_right he]

/-- **The graded Koszul differential squares to zero.** -/
theorem gradedKoszul_gradedKoszul (f : E → A) (k : ℕ) (y : Set.powersetCard E (k + 2) → A) :
    gradedKoszul f k (gradedKoszul f (k + 1) y) = 0 := by
  rw [← koszulProj_koszulEmbed (k + 2) y, ← koszulProj_differential, ← koszulProj_differential,
    Koszul.differential_differential, map_zero]

/-- The graded Koszul differential commutes with ring homomorphisms applied entrywise. -/
theorem gradedKoszul_map {B : Type*} [CommRing B] (φ : A →+* B) (f : E → A) (k : ℕ)
    (y : Set.powersetCard E (k + 1) → A) :
    gradedKoszul (fun e => φ (f e)) k (fun S => φ (y S)) = fun T => φ (gradedKoszul f k y T) := by
  funext T
  rw [gradedKoszul_apply, gradedKoszul_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e ∉ (T : Finset E)
  · rw [dite_eq_left he, dite_eq_left he, map_mul, map_mul, Koszul.sign, Koszul.sign, map_pow,
      map_neg, map_one]
  · rw [dite_eq_right he, dite_eq_right he, map_zero]

/-- **Exactness from a contraction.** If the total Koszul complex of `f` has a contraction
whose projection vanishes on elements without empty-set component, the graded Koszul complex is
exact in every positive degree: a cycle of degree `k+1` is the boundary of a family of degree
`k+2`. -/
theorem gradedKoszul_exact_of_contraction {R' H : Type*} [CommRing R'] [Module R' A]
    [AddCommGroup H] [Module R' H] (f : E → A)
    (C : IncidencePerturbation.Contraction R' (Koszul.Space E A) H)
    (hd : ∀ z, C.d z = Koszul.differential f z) (hp : ∀ z : Koszul.Space E A, z ∅ = 0 → C.p z = 0)
    (k : ℕ) (y : Set.powersetCard E (k + 1) → A) (hy : gradedKoszul f k y = 0) :
    ∃ y' : Set.powersetCard E (k + 2) → A, gradedKoszul f (k + 1) y' = y := by
  let z := koszulEmbed (k + 1) y
  have hdz : C.d z = 0 := by
    rw [hd, koszul_differential_embed, hy, map_zero]
  have hz0 : z ∅ = 0 := by
    rw [koszulEmbed_apply, dite_eq_right]
    simp
  have hh := LinearMap.congr_fun C.homotopy z
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.comp_apply, hdz, map_zero,
    hp z hz0, add_zero, Module.End.one_apply] at hh
  refine ⟨koszulProj (k + 2) (C.h z), ?_⟩
  rw [← koszulProj_differential, ← hd, hh, koszulProj_koszulEmbed]

/-- The family indexed by the unique empty edge subset, as an element of `A`. -/
theorem gradedKoszul_zero_apply (f : E → A) (y : Set.powersetCard E 1 → A)
    (T : Set.powersetCard E 0) :
    gradedKoszul f 0 y T = ∑ e : E, f e * y (Set.powersetCard.ofSingleton e) := by
  have hT : (T : Finset E) = ∅ := Finset.card_eq_zero.mp (Set.powersetCard.card_eq T)
  rw [gradedKoszul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  have he : e ∉ (T : Finset E) := by rw [hT]; exact Finset.notMem_empty e
  rw [dite_eq_left he]
  have hs : Koszul.sign (A := A) (T : Finset E) e = 1 := by
    simp [Koszul.sign, Koszul.index, hT]
  have hi : powersetCardInsert T e he = Set.powersetCard.ofSingleton e := by
    apply Subtype.ext
    change insert e (T : Finset E) = {e}
    rw [hT]
    rfl
  rw [hs, one_mul, hi]

/-- **The degree-zero cokernel.** The image of the graded Koszul differential in degree zero,
read at the empty edge subset, is the ideal generated by the `f_e`. -/
theorem gradedKoszul_zero_range (f : E → A) (T : Set.powersetCard E 0) (x : A) :
    x ∈ Ideal.span (Set.range f) ↔ ∃ y, gradedKoszul f 0 y T = x := by
  rw [Ideal.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun S => c (Classical.choose (Finset.card_eq_one.mp (Set.powersetCard.card_eq S))), ?_⟩
    rw [gradedKoszul_zero_apply, ← hc]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h := Classical.choose_spec (Finset.card_eq_one.mp
      (Set.powersetCard.card_eq (Set.powersetCard.ofSingleton e)))
    have he : Classical.choose (Finset.card_eq_one.mp
        (Set.powersetCard.card_eq (Set.powersetCard.ofSingleton e))) = e := by
      have h' : ({e} : Finset E) = {Classical.choose (Finset.card_eq_one.mp
          (Set.powersetCard.card_eq (Set.powersetCard.ofSingleton e)))} := h
      exact (Finset.singleton_injective h').symm
    rw [he, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨fun e => y (Set.powersetCard.ofSingleton e), ?_⟩
    rw [gradedKoszul_zero_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

/-- The integral exterior sign acts on a ring as multiplication by the sign of the ring. -/
theorem koszulSign_zsmul (T : Finset E) (e : E) (z : A) :
    Koszul.sign (A := ℤ) T e • z = Koszul.sign T e * z := by
  simp [Koszul.sign, zsmul_eq_mul]

end Graded

/-! ### Sections of sheaf morphisms -/

section Sections

universe u₁ v₁ u

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Sections of an integer multiple of a morphism of sheaves of modules are the integer multiples
of the sections. -/
theorem sheafOfModules_zsmul_app_apply {M N : SheafOfModules.{u} R} (n : ℤ) (f : M ⟶ N)
    (X : Cᵒᵖ) (x : M.val.obj X) :
    ((n • f).val.app X).hom x = n • (f.val.app X).hom x :=
  congrArg (fun g => g.hom x)
    (Functor.map_zsmul (SheafOfModules.evaluation R X) (f := f) (r := n))

end Sections

/-- A morphism of sheaves of modules is linear on sections for the geometric action of the base
ring. -/
noncomputable def schemeBaseOpenHomLinear {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    SchemeTools.schemeBaseOpenSectionModule f M U →ₗ[R]
      SchemeTools.schemeBaseOpenSectionModule f N U := by
  letI := SchemeTools.schemeBaseOpenModuleSections f M U
  letI := SchemeTools.schemeBaseOpenModuleSections f N U
  change Γ(M, U) →ₗ[R] Γ(N, U)
  exact { toFun := (φ.val.app (op U)).hom
          map_add' := map_add _
          map_smul' := fun r x => (φ.val.app (op U)).hom.map_smul
            (SchemeTools.schemeBaseCoefficientAt f U r) x }

/-- The base-linear map on sections is the map of sections of the morphism. -/
@[simp] theorem schemeBaseOpenHomLinear_apply {X : Scheme.{0}} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (x : SchemeTools.schemeBaseOpenSectionModule f M U) :
    schemeBaseOpenHomLinear f φ U x = (φ.val.app (op U)).hom x := rfl

/-! ### The universal Koszul complex of sheaves -/

section Sheaf

variable {R : Type} [CommRing R] {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E]
  [Fintype E] (G : Multigraph V E)

/-- Adding an edge outside `T` adds its endpoint count to the twist: `-d_T = -d_{T ∪ {e}} + d_e`. -/
theorem exteriorTwist_insert {T : Finset E} {e : E} (he : e ∉ T) :
    (fun v => -(G.deg T v : ℤ)) =
      (fun v => -(G.deg (insert e T) v : ℤ)) + fun v => (G.endCount e v : ℤ) := by
  funext v
  simp only [Pi.add_apply, G.deg_insert he, Nat.cast_add]
  ring

/-- **The Koszul component** `O(-d_{T ∪ {e}}) ⟶ O(-d_T)`: multiplication by the edge section
`s_e` with coefficients `κ`. -/
noncomputable def univKoszulComponent (κ : IncCoeffIdx E → R) {k : ℕ} (T : Set.powersetCard E k)
    (e : E) (he : e ∉ (T : Finset E)) :
    G.exteriorSummand R (powersetCardInsert T e he) ⟶ G.exteriorSummand R T :=
  G.edgeSectionMul κ e (G.exteriorTwist_insert he)

/-- **The Koszul differential** `d = ι_s : ∧^{k+1} F^∨ ⟶ ∧^k F^∨` of the section with
coefficients `κ`. Its component from the summand of `T ∪ {e}` to the summand of `T` (for
`e ∉ T`) is `sign(T, e) · s_e`, where `sign(T, e) = Koszul.sign T e` is the sign of removing `e`
from `T ∪ {e}` in the increasing order of the edges (the convention of `Koszul.erase` and of
`incKoszulPerturbation`); all other components are zero. -/
noncomputable def univKoszulDifferential (κ : IncCoeffIdx E → R) (k : ℕ) :
    G.exteriorBundle R (k + 1) ⟶ G.exteriorBundle R k :=
  biproduct.lift (C := SheafOfModules (vertexScheme R V).ringCatSheaf) fun T =>
    ∑ e : E, if h : e ∉ (T : Finset E) then
      Koszul.sign (A := ℤ) (T : Finset E) e •
        (biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
          (fun S : Set.powersetCard E (k + 1) => G.exteriorSummand R S)
          (powersetCardInsert T e h) ≫ G.univKoszulComponent κ T e h)
    else 0

/-- **The Koszul differential on sections.** On every open, the `T`-component of `d x` is
`Σ_{e ∉ T} sign(T, e) s_e x_{T ∪ {e}}`. -/
theorem univKoszulDifferential_app (κ : IncCoeffIdx E → R) (k : ℕ)
    (W : (vertexScheme R V).Opens) (x : Γ(G.exteriorBundle R (k + 1), W))
    (T : Set.powersetCard E k) :
    ((biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
        (fun S : Set.powersetCard E k => G.exteriorSummand R S) T).val.app (op W)).hom
        (((G.univKoszulDifferential κ k).val.app (op W)).hom x) =
      ∑ e : E, if h : e ∉ (T : Finset E) then
        Koszul.sign (A := ℤ) (T : Finset E) e •
          ((G.univKoszulComponent κ T e h).val.app (op W)).hom
            (((biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
              (fun S : Set.powersetCard E (k + 1) => G.exteriorSummand R S)
              (powersetCardInsert T e h)).val.app (op W)).hom x)
      else 0 := by
  have hl := congrArg (fun φ => (φ.val.app (op W)).hom x)
    (biproduct.lift_π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
      (fun T : Set.powersetCard E k => ∑ e : E, if h : e ∉ (T : Finset E) then
        Koszul.sign (A := ℤ) (T : Finset E) e •
          (biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
            (fun S : Set.powersetCard E (k + 1) => G.exteriorSummand R S)
            (powersetCardInsert T e h) ≫ G.univKoszulComponent κ T e h)
      else 0) T)
  refine hl.trans ?_
  rw [sheafOfModules_sum_app_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · rw [dite_eq_left h, dite_eq_left h, sheafOfModules_zsmul_app_apply]
    rfl
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

/-- The chart frame of the `k`-th exterior bundle on a subopen `W` of the chart `σ`: the chart
coefficients of the components of a section. -/
noncomputable def exteriorChartEquiv (k : ℕ) (σ : V → Bool) (W : (vertexScheme R V).Opens)
    (hW : W ≤ univChartOpen R V σ) :
    Γ(G.exteriorBundle R k, W) ≃ₗ[Γ(vertexScheme R V, W)]
      (Set.powersetCard E k → Γ(vertexScheme R V, W)) :=
  (schemeBiproductSectionsEquiv (fun S : Set.powersetCard E k => G.exteriorSummand R S) W).trans
    (LinearEquiv.piCongrRight fun S =>
      vertexTwistChartCoefficientEquiv R V (fun v => -(G.deg S v : ℤ)) (vertexBooleanPivot V σ)
        W hW)

/-- The chart frame reads the chart coefficient of each component. -/
theorem exteriorChartEquiv_apply (k : ℕ) (σ : V → Bool) (W : (vertexScheme R V).Opens)
    (hW : W ≤ univChartOpen R V σ) (x : Γ(G.exteriorBundle R k, W)) (S : Set.powersetCard E k) :
    G.exteriorChartEquiv k σ W hW x S =
      vertexTwistSheafChartCoefficient R V (fun v => -(G.deg S v : ℤ)) (vertexBooleanPivot V σ)
        W hW (((biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
          (fun S : Set.powersetCard E k => G.exteriorSummand R S) S).val.app (op W)).hom x) :=
  rfl

/-- **The Koszul differential in a chart frame.** On every subopen `W` of the chart `σ`, the
Koszul differential is the graded Koszul differential of the chart functions of the edge
sections, restricted to `W`: the Koszul complex of the chart edge equations. -/
theorem univKoszulDifferential_chart (κ : IncCoeffIdx E → R) (k : ℕ) (σ : V → Bool)
    (W : (vertexScheme R V).Opens) (hW : W ≤ univChartOpen R V σ)
    (x : Γ(G.exteriorBundle R (k + 1), W)) :
    G.exteriorChartEquiv k σ W hW (((G.univKoszulDifferential κ k).val.app (op W)).hom x) =
      gradedKoszul (fun e => (vertexScheme R V).presheaf.map (homOfLE hW).op
        (twistChartFunction (G.edgeFaceSection κ e) σ)) k (G.exteriorChartEquiv (k + 1) σ W hW x) := by
  funext T
  rw [exteriorChartEquiv_apply, univKoszulDifferential_app, map_sum, gradedKoszul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · rw [dite_eq_left h, dite_eq_left h, map_zsmul, univKoszulComponent, edgeSectionMul]
    erw [twistMul_coefficient]
    rw [koszulSign_zsmul, exteriorChartEquiv_apply]
    ring
  · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- The face coordinate of a section of a multi-twist over a face open: its coefficient in the
frame of the face's own chart, read in the face ring. -/
noncomputable def twistFaceCoordinate (a : V → ℤ) (q : V → Fin 3) :
    Γ(vertexTwistSheaf R V a, univFaceOpen R V q) ≃+ FaceRing R q :=
  (vertexTwistChartCoefficientEquiv R V a (vertexBooleanPivot V (vertexFaceBaseChoice V q))
    (univFaceOpen R V q) (univFaceOpen_le_baseChart R V q)).toAddEquiv.trans
    (vertexFaceSectionsEquiv R V q).toAddEquiv

/-- The face coordinate is the chart coefficient in the face's own chart, read in the face ring. -/
theorem twistFaceCoordinate_apply (a : V → ℤ) (q : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a, univFaceOpen R V q)) :
    twistFaceCoordinate a q x = vertexFaceSectionsEquiv R V q
      (vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V (vertexFaceBaseChoice V q))
        (univFaceOpen R V q) (univFaceOpen_le_baseChart R V q) x) := rfl

/-- **Multiplication by a section of a twist in face coordinates.** -/
theorem twistMul_faceCoordinate {a b c : V → ℤ} (hc : c = a + b)
    {g : ∀ q : V → Fin 3, FaceRing R q} (hg : IsTwistFaceFamily R b g) (q : V → Fin 3)
    (x : Γ(vertexTwistSheaf R V a, univFaceOpen R V q)) :
    twistFaceCoordinate c q (((twistMul hc hg).val.app (op _)).hom x) =
      twistFaceCoordinate a q x * g q := by
  rw [twistFaceCoordinate_apply, twistFaceCoordinate_apply,
    twistMul_faceCoefficient hc hg q _ le_rfl x, map_mul]
  congr 1
  change vertexFaceSectionsEquiv R V q ((vertexScheme R V).presheaf.map (𝟙 _).op
    (twistFaceFunction g q)) = g q
  rw [op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply, twistFaceFunction,
    RingEquiv.apply_symm_apply]

/-- The face frame of the `k`-th exterior bundle on the face open of `q`: the face coordinates
(in the frame of the face's own chart) of the components of a section. -/
noncomputable def exteriorFaceEquiv (k : ℕ) (q : V → Fin 3) :
    Γ(G.exteriorBundle R k, univFaceOpen R V q) ≃+ (Set.powersetCard E k → FaceRing R q) :=
  (schemeBiproductSectionsEquiv (fun S : Set.powersetCard E k => G.exteriorSummand R S)
    (univFaceOpen R V q)).toAddEquiv.trans
    (AddEquiv.piCongrRight fun S => twistFaceCoordinate (fun v => -(G.deg S v : ℤ)) q)

/-- The face frame reads the face coordinate of each component. -/
theorem exteriorFaceEquiv_apply (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle R k, univFaceOpen R V q)) (S : Set.powersetCard E k) :
    G.exteriorFaceEquiv k q x S =
      twistFaceCoordinate (fun v => -(G.deg S v : ℤ)) q
        (((biproduct.π (C := SheafOfModules (vertexScheme R V).ringCatSheaf)
          (fun S : Set.powersetCard E k => G.exteriorSummand R S) S).val.app (op _)).hom x) :=
  rfl

/-- **The Koszul differential in a face frame.** On the face open of `q`, in the frame of the
face's own chart, the Koszul differential is the graded Koszul differential of the face edge
sections `edgeFaceSection κ e q`. -/
theorem univKoszulDifferential_face (κ : IncCoeffIdx E → R) (k : ℕ) (q : V → Fin 3)
    (x : Γ(G.exteriorBundle R (k + 1), univFaceOpen R V q)) :
    G.exteriorFaceEquiv k q (((G.univKoszulDifferential κ k).val.app (op _)).hom x) =
      gradedKoszul (fun e => G.edgeFaceSection κ e q) k (G.exteriorFaceEquiv (k + 1) q x) := by
  funext T
  rw [exteriorFaceEquiv_apply, univKoszulDifferential_app, map_sum, gradedKoszul_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · rw [dite_eq_left h, dite_eq_left h, map_zsmul, univKoszulComponent, edgeSectionMul]
    erw [twistMul_faceCoordinate]
    rw [koszulSign_zsmul, exteriorFaceEquiv_apply]
    ring
  · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- **The Koszul differential squares to zero.** -/
theorem univKoszulDifferential_comp (κ : IncCoeffIdx E → R) (k : ℕ) :
    G.univKoszulDifferential κ (k + 1) ≫ G.univKoszulDifferential κ k = 0 := by
  apply moduleHom_ext_of_cover (vertexScheme R V) _ _ (univChartOpen R V)
    (univChartOpen_iSup_top R V)
  intro σ
  rw [Functor.map_zero]
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((G.univKoszulDifferential κ k).val.app (op S.unop.left)).hom
    (((G.univKoszulDifferential κ (k + 1)).val.app (op S.unop.left)).hom x) = 0
  apply (G.exteriorChartEquiv k σ S.unop.left S.unop.hom.le).injective
  rw [univKoszulDifferential_chart, univKoszulDifferential_chart, gradedKoszul_gradedKoszul,
    map_zero]

/-- **The universal Koszul complex** of the section with coefficients `κ`, as a chain complex of
sheaves of modules on `(ℙ¹)^V` over `R`: the `k`-th exterior bundle `∧^k F^∨` in homological
degree `k` (cohomological degree `-k`), with differential `d = ι_s`. -/
noncomputable def univKoszulComplex (κ : IncCoeffIdx E → R) :
    ChainComplex (SheafOfModules (vertexScheme R V).ringCatSheaf) ℕ :=
  ChainComplex.of (fun k => G.exteriorBundle R k) (fun k => G.univKoszulDifferential κ k)
    (fun k => G.univKoszulDifferential_comp κ k)

/-- The terms of the universal Koszul complex are the exterior bundles. -/
theorem univKoszulComplex_X (κ : IncCoeffIdx E → R) (k : ℕ) :
    (G.univKoszulComplex κ).X k = G.exteriorBundle R k := rfl

/-- The differentials of the universal Koszul complex are the Koszul differentials. -/
theorem univKoszulComplex_d (κ : IncCoeffIdx E → R) (k : ℕ) :
    (G.univKoszulComplex κ).d (k + 1) k = G.univKoszulDifferential κ k := by
  simp [univKoszulComplex]

end Sheaf

section Universal

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- **The universal Koszul complex `K_G`** (paper eq. `alg:universal-koszul`): over
`S_G = IncCoeffRing E`, the Koszul complex of the universal section `s^univ`, with terms
`∧^k F_G^∨` and differential the contraction with `s^univ`. -/
noncomputable def incUniversalKoszulComplex :
    ChainComplex (SheafOfModules (vertexScheme (IncCoeffRing E) V).ringCatSheaf) ℕ :=
  G.univKoszulComplex MvPolynomial.X

end Universal

end BPFixedPoints.Multigraph
