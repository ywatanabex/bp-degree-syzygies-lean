import BPFixedPoints.StrongField.BoundaryAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The residue pairing on the boundary algebra of one vertex (`sf:serre-comparison`, algebra)

For a field K and r : ℕ, `TruncLine K r` is B = K[w]/(w^r) (as `AdjoinRoot (X ^ r)`), the
boundary algebra of one active vertex. For a single vertex it is the truncated algebra of
`BoundaryAlgebra.lean` (`truncEquivTruncLine`). The residue functional
`truncLineResidue` reads the coefficient of w^{r−1} of the reduced representative, and
`truncLinePairing` is the pairing (f, g) ↦ [w^{r−1}](fg).

Proved:
* on the monomial basis w^i (`truncLineBasis`) the pairing is the antidiagonal matrix
  (`truncLinePairing_gen_pow`);
* for 0 ≤ a ≤ r the orthogonal of w^a B is w^{r−a} B
  (`truncLinePairing_orthogonal_powSubmodule`);
* the pairing is perfect (`truncLinePairing_isPerfPair`, Mathlib's `LinearMap.IsPerfPair`), hence
  nondegenerate, and gives B ≃ B^* (`truncLineDualEquiv`), which carries w^{r−a} B onto the
  annihilator of w^a B (`map_truncLineDualEquiv_powSubmodule`).

Not claimed: the pairing depends on the coordinate w; nothing here is canonical, and no
statement about Serre duality is made in this file. The comparison with the cup product on ℙ¹
is `Incidence/SerreComparisonProjectiveLine.lean`.
-/

namespace BPFixedPoints

namespace SerreComparison

open Polynomial

set_option linter.unusedSectionVars false

section Algebra

variable (K : Type*) [Field K] (r : ℕ)

/-- The one-variable boundary algebra B = K[w]/(w^r) of an active vertex, as `AdjoinRoot`. -/
abbrev TruncLine : Type _ := AdjoinRoot (X ^ r : K[X])

/-- The coordinate w of B, the class of the variable. -/
noncomputable abbrev truncLineGen : TruncLine K r := AdjoinRoot.root (X ^ r : K[X])

/-- The residue functional [w^{r−1}] on B: the coefficient of w^{r−1} of the reduced
representative of degree < r. -/
noncomputable def truncLineResidue : TruncLine K r →ₗ[K] K :=
  (lcoeff K (r - 1)).comp (AdjoinRoot.modByMonicHom (monic_X_pow r))

/-- Reduction modulo w^r does not change the coefficients below r. -/
theorem coeff_modByMonic_X_pow (f : K[X]) {i : ℕ} (hi : i < r) :
    (f %ₘ X ^ r).coeff i = f.coeff i := by
  conv_rhs => rw [← modByMonic_add_div f (X ^ r)]
  rw [coeff_add, coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

/-- For r ≥ 1 the residue of the class of a polynomial is its coefficient of w^{r−1}. -/
theorem truncLineResidue_mk (hr : 0 < r) (f : K[X]) :
    truncLineResidue K r (AdjoinRoot.mk _ f) = f.coeff (r - 1) := by
  rw [truncLineResidue, LinearMap.comp_apply, AdjoinRoot.modByMonicHom_mk, lcoeff_apply,
    coeff_modByMonic_X_pow K r f (by omega)]

/-- The pairing (f, g) ↦ [w^{r−1}](fg) on B. -/
noncomputable def truncLinePairing : LinearMap.BilinForm K (TruncLine K r) :=
  (LinearMap.mul K (TruncLine K r)).compr₂ (truncLineResidue K r)

/-- The pairing is the residue of the product. -/
theorem truncLinePairing_apply (f g : TruncLine K r) :
    truncLinePairing K r f g = truncLineResidue K r (f * g) := rfl

/-- On classes of polynomials, the pairing is the coefficient of w^{r−1} of the product. -/
theorem truncLinePairing_mk_mk (hr : 0 < r) (f g : K[X]) :
    truncLinePairing K r (AdjoinRoot.mk _ f) (AdjoinRoot.mk _ g) = (f * g).coeff (r - 1) := by
  rw [truncLinePairing_apply, ← map_mul, truncLineResidue_mk K r hr]

/-- The pairing is symmetric. -/
theorem truncLinePairing_comm (f g : TruncLine K r) :
    truncLinePairing K r f g = truncLinePairing K r g f := by
  rw [truncLinePairing_apply, truncLinePairing_apply, mul_comm]

/-- **Gram matrix.** On the monomial basis 1, w, …, w^{r−1} the pairing is the antidiagonal
matrix: ⟨w^i, w^j⟩ = 1 if i + j = r − 1 and 0 otherwise. -/
theorem truncLinePairing_gen_pow (hr : 0 < r) (i j : ℕ) :
    truncLinePairing K r (truncLineGen K r ^ i) (truncLineGen K r ^ j) =
      if i + j = r - 1 then 1 else 0 := by
  unfold truncLineGen
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_pow, truncLinePairing_mk_mk K r hr, ← pow_add,
    coeff_X_pow]
  simp only [eq_comm]

/-- The monomial basis 1, w, …, w^{r−1} of B. -/
noncomputable def truncLineBasis : Module.Basis (Fin r) K (TruncLine K r) :=
  (AdjoinRoot.powerBasis' (monic_X_pow r)).basis.reindex (finCongr (natDegree_X_pow r))

/-- The basis vector of index i is w^i. -/
theorem truncLineBasis_apply (i : Fin r) : truncLineBasis K r i = truncLineGen K r ^ (i : ℕ) := by
  rw [truncLineBasis, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  rfl

/-- The K-subspace w^a B of B, the image of the ideal (w^a). -/
noncomputable def truncLinePowSubmodule (a : ℕ) : Submodule K (TruncLine K r) :=
  (Ideal.span {truncLineGen K r ^ a}).restrictScalars K

/-- **Membership in w^a B.** For a ≤ r, the class of f lies in w^a B iff w^a divides f, that is
iff the coefficients of f below a vanish. -/
theorem mk_mem_truncLinePowSubmodule {a : ℕ} (ha : a ≤ r) (f : K[X]) :
    AdjoinRoot.mk _ f ∈ truncLinePowSubmodule K r a ↔ ∀ d < a, f.coeff d = 0 := by
  rw [← X_pow_dvd_iff, truncLinePowSubmodule, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
    unfold truncLineGen at hc
    rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul, AdjoinRoot.mk_eq_mk] at hc
    obtain ⟨h, hh⟩ := hc
    refine ⟨g + X ^ (r - a) * h, ?_⟩
    have hr : (X ^ r : K[X]) = X ^ a * X ^ (r - a) := by rw [← pow_add, Nat.add_sub_cancel' ha]
    rw [sub_eq_iff_eq_add] at hh
    rw [hh, hr]
    ring
  · rintro ⟨g, rfl⟩
    exact ⟨AdjoinRoot.mk _ g, by rw [map_mul, map_pow, AdjoinRoot.mk_X]⟩

/-- The product of w^a B and w^b B lies in w^{a+b} B. -/
theorem mul_mem_truncLinePowSubmodule {a b : ℕ} {f g : TruncLine K r}
    (hf : f ∈ truncLinePowSubmodule K r a) (hg : g ∈ truncLinePowSubmodule K r b) :
    f * g ∈ truncLinePowSubmodule K r (a + b) := by
  rw [truncLinePowSubmodule, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hf hg ⊢
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨e, rfl⟩ := hg
  exact ⟨c * e, by ring⟩

/-- w^r B = 0. -/
theorem truncLinePowSubmodule_self : truncLinePowSubmodule K r r = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective f
  rw [mk_mem_truncLinePowSubmodule K r le_rfl, ← X_pow_dvd_iff] at hf
  rw [Submodule.mem_bot, AdjoinRoot.mk_eq_zero]
  exact hf

/-- w^0 B = B. -/
theorem truncLinePowSubmodule_zero : truncLinePowSubmodule K r 0 = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [truncLinePowSubmodule, Submodule.restrictScalars_mem, pow_zero, Ideal.span_singleton_one]
  trivial

/-- **Dual filtrations.** For 0 ≤ a ≤ r, the orthogonal of w^a B for the pairing
(f, g) ↦ [w^{r−1}](fg) is w^{r−a} B. -/
theorem truncLinePairing_orthogonal_powSubmodule {a : ℕ} (ha : a ≤ r) :
    (truncLinePairing K r).orthogonal (truncLinePowSubmodule K r a) =
      truncLinePowSubmodule K r (r - a) := by
  ext g
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hg
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have ha0 : a = 0 := by omega
      subst ha0
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective g
      rw [mk_mem_truncLinePowSubmodule K 0 le_rfl]
      intro d hd
      omega
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective g
    rw [mk_mem_truncLinePowSubmodule K r (Nat.sub_le r a)]
    intro d hd
    have hmem : AdjoinRoot.mk (X ^ r : K[X]) (X ^ (r - 1 - d)) ∈ truncLinePowSubmodule K r a := by
      rw [mk_mem_truncLinePowSubmodule K r ha]
      intro i hi
      rw [coeff_X_pow, ite_eq_right (by omega)]
    have h := hg _ hmem
    rw [truncLinePairing_mk_mk K r hr, coeff_X_pow_mul', ite_eq_left (by omega)] at h
    have he : r - 1 - (r - 1 - d) = d := by omega
    rwa [he] at h
  · intro hg f hf
    have hmul := mul_mem_truncLinePowSubmodule K r hf hg
    rw [Nat.add_sub_cancel' ha, truncLinePowSubmodule_self, Submodule.mem_bot] at hmul
    rw [truncLinePairing_apply, hmul, map_zero]

/-- B is finite-dimensional over K. -/
instance instModuleFiniteTruncLine : Module.Finite K (TruncLine K r) :=
  (monic_X_pow r).finite_adjoinRoot

/-- The pairing is injective as a map B → B^*: only 0 is orthogonal to all of B. -/
theorem truncLinePairing_injective : Function.Injective (truncLinePairing K r) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro g hg
  have hmem : g ∈ (truncLinePairing K r).orthogonal (truncLinePowSubmodule K r 0) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro f _
    rw [truncLinePairing_comm]
    exact congrArg (fun φ : TruncLine K r →ₗ[K] K => φ f) (LinearMap.mem_ker.1 hg)
  rwa [truncLinePairing_orthogonal_powSubmodule K r (Nat.zero_le r), Nat.sub_zero,
    truncLinePowSubmodule_self] at hmem

/-- The pairing equals its flip. -/
theorem truncLinePairing_flip : LinearMap.flip (truncLinePairing K r) = truncLinePairing K r := by
  ext f g
  exact truncLinePairing_comm K r g f

/-- **Perfect pairing.** (f, g) ↦ [w^{r−1}](fg) is a perfect pairing on B. -/
instance truncLinePairing_isPerfPair : (truncLinePairing K r).IsPerfPair :=
  .of_injective (truncLinePairing_injective K r)
    (by rw [truncLinePairing_flip]; exact truncLinePairing_injective K r)

/-- The pairing on B is nondegenerate. -/
theorem truncLinePairing_nondegenerate : (truncLinePairing K r).Nondegenerate :=
  LinearMap.IsPerfPair.nondegenerate inferInstance

/-- **B ≅ B^*.** The identification of B with its dual given by the pairing. -/
noncomputable def truncLineDualEquiv : TruncLine K r ≃ₗ[K] Module.Dual K (TruncLine K r) :=
  (truncLinePairing K r).toPerfPair

/-- The identification sends g to the functional f ↦ [w^{r−1}](gf). -/
theorem truncLineDualEquiv_apply (g f : TruncLine K r) :
    truncLineDualEquiv K r g f = truncLineResidue K r (g * f) := rfl

/-- **Dual filtrations in B^*.** For 0 ≤ a ≤ r, the identification B ≅ B^* carries w^{r−a} B
onto the annihilator of w^a B. -/
theorem map_truncLineDualEquiv_powSubmodule {a : ℕ} (ha : a ≤ r) :
    (truncLinePowSubmodule K r (r - a)).map (truncLineDualEquiv K r : _ →ₗ[K] _) =
      (truncLinePowSubmodule K r a).dualAnnihilator := by
  ext φ
  obtain ⟨g, rfl⟩ := (truncLineDualEquiv K r).surjective φ
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_dualAnnihilator,
    ← truncLinePairing_orthogonal_powSubmodule K r ha, LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun f _ => ?_
  rw [truncLineDualEquiv_apply, ← truncLinePairing_apply, truncLinePairing_comm]

/-- For a single vertex, the boundary truncation ideal of `BoundaryAlgebra` is (w^r). -/
theorem map_truncIdeal_unique (σ : Type*) [Unique σ] :
    (BoundaryAlgebra.truncIdeal K (fun _ : σ => r)).map
        (MvPolynomial.uniqueAlgEquiv K σ : MvPolynomial σ K →+* K[X]) =
      Ideal.span {(X ^ r : K[X])} := by
  rw [BoundaryAlgebra.truncIdeal_eq_span_X_pow, Ideal.map_span]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    simp
  · rintro rfl
    exact ⟨_, ⟨default, rfl⟩, by simp⟩

/-- **The one-vertex boundary algebra.** For a single vertex, the truncated algebra
K[w]/(w^r) of `BoundaryAlgebra` is B. -/
noncomputable def truncEquivTruncLine (σ : Type*) [Unique σ] :
    (MvPolynomial σ K ⧸ BoundaryAlgebra.truncIdeal K (fun _ : σ => r)) ≃ₐ[K] TruncLine K r :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.uniqueAlgEquiv K σ) (map_truncIdeal_unique K r σ).symm

/-- The identification sends the class of the vertex variable to w. -/
theorem truncEquivTruncLine_mk_X (σ : Type*) [Unique σ] (i : σ) :
    truncEquivTruncLine K r σ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = truncLineGen K r := by
  have h : truncEquivTruncLine K r σ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      AdjoinRoot.mk (X ^ r : K[X]) (MvPolynomial.uniqueAlgEquiv K σ (MvPolynomial.X i)) := rfl
  rw [h, MvPolynomial.uniqueAlgEquiv_apply, MvPolynomial.eval₂_X, AdjoinRoot.mk_X]

end Algebra

end SerreComparison

end BPFixedPoints
