import BPFixedPoints.Incidence.SerreComparisonLineCup

/-!
# Concrete Serre duality on ℙ¹ for one active vertex (`sf:serre-comparison`)

One vertex (`V = Unit`), a field K (for the paper, K = ℂ), k = s + 2 ≥ 2 and r = k − 1 = s + 1.
Cohomology is the repository's Ext-defined sheaf cohomology `Sheaf.H` of the twist sheaves on
ℙ¹ over K, with the geometric base action (`h1Module`, `h0Module`), and the product is the
standard product `vertexTwistStandardClassCup`. B = K[w]/(w^r) is `TruncLine K r` with the residue
pairing `truncLinePairing` (f, g) ↦ [w^{r−1}](fg) of `StrongField/SerreComparison.lean`.

Proved:
* `h0LinearEquiv`: H^0(ℙ¹, O(k−2)) ≅ B, sending the section z ↦ P(z) (deg P ≤ r − 1) to the
  class of P (`h0LinearEquiv_h0OfPoly`): global sections are the polynomials of degree ≤ r − 1.
* `h1LinearEquiv`: H^1(ℙ¹, O(−k)) ≅ B, sending the Laurent gap class z^{−j−1} (0 ≤ j ≤ r − 1) to
  w^{r−1−j} (`h1LinearEquiv_apply`, with `gapCoord`).
* `minusTwoTrace_bijective`: H^1(ℙ¹, O(−2)) ≅ K by the state coordinate of z^{−1}.
* `serreCupLinear` (bilinear, for the geometric actions): the cup product
  H^1(O(−k)) × H^0(O(k−2)) → H^1(O(−2)), transported along −k + (k−2) = −2, followed by the
  trace. Under the two isomorphisms with B it is exactly the residue pairing
  (`serreCupLinear_eq_truncLinePairing`).
* Hence it is a perfect pairing (`serreCupLinear_isPerfPair`, Mathlib's `LinearMap.IsPerfPair`),
  giving H^1(ℙ¹, O(−k)) ≅ H^0(ℙ¹, O(k−2))^* (`serreDualityEquiv`), and the dual filtrations
  (w^a B)^⊥ = w^{r−a} B hold for the cup pairing (`serreCup_orthogonal_iff`).

Not claimed, as in the remark:
* no general Serre duality: Mathlib has no dualizing sheaf, and ω_{ℙ¹} ≅ O(−2) is not formalized;
  the twist −2 is used directly;
* the scalar identifications use the chosen chart coordinate and frames: the trace on
  H^1(O(−2)) is the chosen state coordinate, and B is matched with H^0 and H^1 through the
  coordinate z; nothing here is canonical;
* the cup product is identified with the multiplication of B only through the stated pairing;
  no algebra identification with B or with a Tor summand is made;
* only a single vertex is treated.
-/

namespace BPFixedPoints.SerreComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools SheafTools.BinaryCells ProjectiveLine CechProduct ExtResolutionTools Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

variable (K : Type) [Field K]

noncomputable local instance serreDualityHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme K Unit)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The geometric base action of K on H^1(ℙ¹, O(−(s+2))). -/
@[instance_reducible] noncomputable def h1Module (s : ℕ) :
    Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :=
  SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit)
    (vertexTwistSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1

/-- The geometric base action of K on H^0(ℙ¹, O(s)). -/
@[instance_reducible] noncomputable def h0Module (s : ℕ) :
    Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :=
  SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit (posTwist s)) 0

/-- Transport of cohomology along an equality of twists is linear for the geometric actions. -/
theorem vertexTwistHCast_smul {a a' : Unit → ℤ} (h : a = a') (n : ℕ) (c : K)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n) :
    letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit a) n
    letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a') n) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit a') n
    vertexTwistHCast K Unit h n (c • z) = c • vertexTwistHCast K Unit h n z := by
  subst h
  rfl

/-- The same statement for the underlying additive map. -/
theorem vertexTwistHCast_toAddMonoidHom_smul {a a' : Unit → ℤ} (h : a = a') (n : ℕ) (c : K)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n) :
    letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a) n) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit a) n
    letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit a') n) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit) (vertexTwistSheaf K Unit a') n
    (vertexTwistHCast K Unit h n).toAddMonoidHom (c • z) =
      c • (vertexTwistHCast K Unit h n).toAddMonoidHom z :=
  vertexTwistHCast_smul K h n c z

/-- The gap coordinates are linear. -/
theorem gapCoord_smul (s : ℕ) (j : Fin (s + 1)) (c : K)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :
    letI := h1Module K s
    gapCoord K s j (c • x) = c * gapCoord K s j x := by
  let _ := vertexTwistStateCohomologyModule K Unit (negTwist s) 1
  rw [gapCoord_apply, gapCoord_apply, ← vertexTwistStateLinearEquiv_eq_actualStateAt,
    ← vertexTwistStateLinearEquiv_eq_actualStateAt]
  change ((vertexTwistStateLinearEquiv K Unit (negTwist s) 1) (c • x)).val (fun _ => j) = _
  rw [map_smul]
  rfl

/-- The trace is linear. -/
theorem minusTwoTraceAt_smul (n : ℕ) (c : K)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ))) n) :
    letI : Module K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit
        (fun v => -((negTwist 0 v : ℕ) : ℤ))) n) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase K Unit)
        (vertexTwistSheaf K Unit (fun v => -((negTwist 0 v : ℕ) : ℤ))) n
    minusTwoTraceAt K n (c • z) = c * minusTwoTraceAt K n z := by
  let _ := vertexTwistStateCohomologyModule K Unit (negTwist 0) n
  rw [minusTwoTraceAt_apply, minusTwoTraceAt_apply, ← vertexTwistStateLinearEquiv_eq_actualStateAt,
    ← vertexTwistStateLinearEquiv_eq_actualStateAt]
  change ((vertexTwistStateLinearEquiv K Unit (negTwist 0) n) (c • z)).val (fun _ => (0 : Fin 1)) = _
  rw [map_smul]
  rfl

/-- The cup pairing is linear in its first argument. -/
theorem serreCup_smul_left (s : ℕ) (c : K)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h1Module K s
    serreCup K s (c • x) y = c * serreCup K s x y := by
  let _ := h1Module K s
  rw [serreCup, AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply, AddMonoidHom.compr₂_apply,
    AddMonoidHom.comp_apply,
    vertexTwistStandardClassCup_smul_left, vertexTwistHCast_toAddMonoidHom_smul, minusTwoTraceAt_smul]

/-- The cup pairing is linear in its second argument. -/
theorem serreCup_smul_right (s : ℕ) (c : K)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h0Module K s
    serreCup K s x (c • y) = c * serreCup K s x y := by
  let _ := h0Module K s
  rw [serreCup, AddMonoidHom.compr₂_apply, AddMonoidHom.comp_apply, AddMonoidHom.compr₂_apply,
    AddMonoidHom.comp_apply,
    vertexTwistStandardClassCup_smul_right, vertexTwistHCast_toAddMonoidHom_smul, minusTwoTraceAt_smul]


/-- **The cup pairing as a K-bilinear map** H^1(ℙ¹, O(−(s+2))) × H^0(ℙ¹, O(s)) → K, for the
geometric base actions. -/
noncomputable def serreCupLinear (s : ℕ) :
    letI := h1Module K s
    letI := h0Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 →ₗ[K]
      Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 →ₗ[K] K := by
  letI := h1Module K s
  letI := h0Module K s
  exact LinearMap.mk₂ K (fun x y => serreCup K s x y)
    (fun x x' y => by rw [map_add, AddMonoidHom.add_apply])
    (fun c x y => by rw [serreCup_smul_left, smul_eq_mul])
    (fun x y y' => map_add _ y y')
    (fun c x y => by rw [serreCup_smul_right, smul_eq_mul])

/-- The bilinear map is the cup pairing. -/
theorem serreCupLinear_apply (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h1Module K s
    letI := h0Module K s
    serreCupLinear K s x y = serreCup K s x y := rfl

/-- The gap coordinate j as a linear form on H^1(ℙ¹, O(−(s+2))). -/
noncomputable def gapLinear (s : ℕ) (j : Fin (s + 1)) :
    letI := h1Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 →ₗ[K] K := by
  letI := h1Module K s
  exact { toFun := gapCoord K s j, map_add' := map_add _, map_smul' := gapCoord_smul K s j }

/-- **Coordinates on H^1(ℙ¹, O(−(s+2))).** The element Σ_i gap_{s−i}(x) w^i of
B = K[w]/(w^{s+1}); the gap monomial z^{−j−1} goes to w^{s−j}. -/
noncomputable def h1CoordLinear (s : ℕ) :
    letI := h1Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 →ₗ[K]
      TruncLine K (s + 1) := by
  letI := h1Module K s
  exact (truncLineBasis K (s + 1)).equivFun.symm.toLinearMap ∘ₗ
    LinearMap.pi (fun i => gapLinear K s (Fin.rev i))

/-- The coordinate of x is Σ_i gap_{s−i}(x) w^i. -/
theorem h1CoordLinear_apply (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :
    letI := h1Module K s
    h1CoordLinear K s x =
      ∑ i : Fin (s + 1), gapCoord K s (Fin.rev i) x • truncLineGen K (s + 1) ^ (i : ℕ) := by
  let _ := h1Module K s
  rw [h1CoordLinear, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [truncLineBasis_apply]
  rfl

/-- ⟨w^i, P⟩ = P_{s−i} for i ≤ s. -/
theorem truncLinePairing_gen_pow_mk (s : ℕ) {i : ℕ} (hi : i ≤ s) (P : K[X]) :
    truncLinePairing K (s + 1) (truncLineGen K (s + 1) ^ i) (AdjoinRoot.mk _ P) = P.coeff (s - i) := by
  unfold truncLineGen
  rw [← AdjoinRoot.mk_X, ← map_pow, truncLinePairing_mk_mk K (s + 1) (Nat.succ_pos s),
    Nat.add_sub_cancel, coeff_X_pow_mul', ite_eq_left hi]

/-- The residue pairing of the coordinates of x with a polynomial P of degree at most s. -/
theorem truncLinePairing_h1Coord (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (P : K[X]) :
    truncLinePairing K (s + 1) (h1CoordLinear K s x) (AdjoinRoot.mk _ P) =
      ∑ j : Fin (s + 1), P.coeff j * gapCoord K s j x := by
  rw [h1CoordLinear_apply, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.revPerm_apply, Fin.rev_rev, truncLinePairing_gen_pow_mk K s (by
    have := (Fin.rev j).isLt
    omega) P, Fin.val_rev, mul_comm]
  congr 2
  have := j.isLt
  omega

/-- **The cup pairing is the residue pairing.** For x ∈ H^1(ℙ¹, O(−(s+2))) and
y ∈ H^0(ℙ¹, O(s)), the cup pairing is (f, g) ↦ [w^s](fg) applied to their coordinates in B. -/
theorem serreCup_eq_truncLinePairing (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    serreCup K s x y = truncLinePairing K (s + 1) (h1CoordLinear K s x) (h0Coord K s y) := by
  obtain ⟨P, hP, rfl⟩ := exists_h0OfPoly K s y
  rw [serreCup_h0OfPoly, h0Coord_h0OfPoly, truncLinePairing_h1Coord]

/-- Every state of twist −(s+2) lies in degree one. -/
theorem mem_stateDegreePiece_negTwist (s : ℕ) (t : H K (negTwist s)) :
    t ∈ stateDegreePiece K (negTwist s) 1 := by
  rw [stateDegreePiece, Finsupp.mem_supported]
  intro κ _
  simp [cohomologyDegree, lineCohomologyDegree]

/-- The gap coordinates determine a class of H^1(ℙ¹, O(−(s+2))). -/
theorem eq_zero_of_gapCoord (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (h : ∀ j, gapCoord K s j x = 0) : x = 0 := by
  apply vertexTwistActualStateAt_injective K Unit (negTwist s) 1
  rw [map_zero]
  apply Subtype.ext
  ext κ
  have hκ : κ = fun _ => κ () := rfl
  rw [hκ]
  exact h (κ ())

/-- Every vector of gap coordinates is attained. -/
theorem exists_gapCoord (s : ℕ) (c : Fin (s + 1) → K) :
    ∃ x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1,
      ∀ j, gapCoord K s j x = c j := by
  let _ := vertexTwistStateCohomologyModule K Unit (negTwist s) 1
  let t : H K (negTwist s) := Finsupp.equivFunOnFinite.symm fun κ => c (κ ())
  refine ⟨(vertexTwistStateLinearEquiv K Unit (negTwist s) 1).symm
    ⟨t, mem_stateDegreePiece_negTwist K s t⟩, fun j => ?_⟩
  rw [gapCoord_apply, ← vertexTwistStateLinearEquiv_eq_actualStateAt, LinearEquiv.apply_symm_apply]
  rfl

/-- **H^1(ℙ¹, O(−(s+2))) ≅ B.** The coordinate map is bijective. -/
theorem h1CoordLinear_bijective (s : ℕ) : Function.Bijective (h1CoordLinear K s) := by
  let _ := h1Module K s
  have hpi : Function.Bijective (LinearMap.pi (fun i => gapLinear K s (Fin.rev i))) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_bot]
      apply eq_zero_of_gapCoord K s x
      intro j
      have := congrFun hx (Fin.rev j)
      simp only [LinearMap.pi_apply, Fin.rev_rev, Pi.zero_apply] at this
      exact this
    · intro v
      obtain ⟨x, hx⟩ := exists_gapCoord K s (fun j => v (Fin.rev j))
      refine ⟨x, funext fun i => ?_⟩
      change gapCoord K s (Fin.rev i) x = v i
      rw [hx, Fin.rev_rev]
  exact (truncLineBasis K (s + 1)).equivFun.symm.bijective.comp hpi

/-- The coordinate map of H^0(ℙ¹, O(s)) is linear for the geometric action. It is deduced from the
bilinearity of the cup product and the nondegeneracy of the residue pairing. -/
theorem h0Coord_smul (s : ℕ) (c : K) (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h0Module K s
    h0Coord K s (c • y) = c • h0Coord K s y := by
  let _ := h0Module K s
  apply truncLinePairing_injective K (s + 1)
  ext g
  obtain ⟨x, rfl⟩ := (h1CoordLinear_bijective K s).2 g
  rw [truncLinePairing_comm, ← serreCup_eq_truncLinePairing, serreCup_smul_right,
    serreCup_eq_truncLinePairing, map_smul, LinearMap.smul_apply, smul_eq_mul,
    truncLinePairing_comm]

/-- **Coordinates on H^0(ℙ¹, O(s)) as a linear map.** -/
noncomputable def h0CoordLinear (s : ℕ) :
    letI := h0Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 →ₗ[K] TruncLine K (s + 1) := by
  letI := h0Module K s
  exact { toFun := h0Coord K s, map_add' := map_add _, map_smul' := h0Coord_smul K s }

/-- **H^1(ℙ¹, O(−k)) ≅ B**, k = s + 2, r = s + 1, through the gap coordinates. -/
noncomputable def h1LinearEquiv (s : ℕ) :
    letI := h1Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 ≃ₗ[K]
      TruncLine K (s + 1) := by
  letI := h1Module K s
  exact LinearEquiv.ofBijective (h1CoordLinear K s) (h1CoordLinear_bijective K s)

/-- **H^0(ℙ¹, O(k−2)) ≅ polynomials of degree ≤ r − 1 ≅ B**, through the left chart polynomial. -/
noncomputable def h0LinearEquiv (s : ℕ) :
    letI := h0Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0 ≃ₗ[K] TruncLine K (s + 1) := by
  letI := h0Module K s
  exact LinearEquiv.ofBijective (h0CoordLinear K s) (h0Coord_bijective K s)

/-- The section z ↦ P(z) has coordinate the class of P. -/
theorem h0LinearEquiv_h0OfPoly (s : ℕ) (P : K[X]) (hP : P.natDegree ≤ s) :
    letI := h0Module K s
    h0LinearEquiv K s (h0OfPoly K s P hP) = AdjoinRoot.mk _ P :=
  h0Coord_h0OfPoly K s P hP

/-- The coordinate of x ∈ H^1 is Σ_i gap_{s−i}(x) w^i. -/
theorem h1LinearEquiv_apply (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :
    letI := h1Module K s
    h1LinearEquiv K s x =
      ∑ i : Fin (s + 1), gapCoord K s (Fin.rev i) x • truncLineGen K (s + 1) ^ (i : ℕ) :=
  h1CoordLinear_apply K s x

/-- **Matching with the residue pairing.** The cup pairing is (f, g) ↦ [w^{r−1}](fg) under the
coordinate isomorphisms with B. -/
theorem serreCupLinear_eq_truncLinePairing (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h1Module K s
    letI := h0Module K s
    serreCupLinear K s x y = truncLinePairing K (s + 1) (h1LinearEquiv K s x) (h0LinearEquiv K s y) :=
  serreCup_eq_truncLinePairing K s x y

/-- **Concrete Serre duality on ℙ¹.** For k = s + 2 ≥ 2, the cup pairing
H^1(ℙ¹, O(−k)) × H^0(ℙ¹, O(k−2)) → H^1(ℙ¹, O(−2)) → K is a perfect pairing. -/
theorem serreCupLinear_isPerfPair (s : ℕ) :
    letI := h1Module K s
    letI := h0Module K s
    (serreCupLinear K s).IsPerfPair := by
  let _ := h1Module K s
  let _ := h0Module K s
  refine LinearMap.IsPerfPair.congr (truncLinePairing K (s + 1)) (h1LinearEquiv K s)
    (h0LinearEquiv K s) (serreCupLinear K s) ?_
  ext f g
  rw [LinearMap.compl₁₂_apply, serreCupLinear_eq_truncLinePairing, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- **H^1(ℙ¹, O(−k)) ≅ H^0(ℙ¹, O(k−2))^*** given by the cup pairing. -/
noncomputable def serreDualityEquiv (s : ℕ) :
    letI := h1Module K s
    letI := h0Module K s
    Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1 ≃ₗ[K]
      Module.Dual K (Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) := by
  letI := h1Module K s
  letI := h0Module K s
  haveI := serreCupLinear_isPerfPair K s
  exact (serreCupLinear K s).toPerfPair

/-- The duality isomorphism is the cup pairing. -/
theorem serreDualityEquiv_apply (s : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (posTwist s)) 0) :
    letI := h1Module K s
    letI := h0Module K s
    serreDualityEquiv K s x y = serreCup K s x y := rfl

/-- **Dual filtrations in cohomology.** For 0 ≤ a ≤ r = s + 1, the classes of H^1(ℙ¹, O(−k))
orthogonal under the cup pairing to the sections with coordinate in w^a B are those with
coordinate in w^{r−a} B. -/
theorem serreCup_orthogonal_iff (s : ℕ) {a : ℕ} (ha : a ≤ s + 1)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf K Unit (fun v => -((negTwist s v : ℕ) : ℤ))) 1) :
    letI := h1Module K s
    letI := h0Module K s
    (∀ y, h0LinearEquiv K s y ∈ truncLinePowSubmodule K (s + 1) a → serreCupLinear K s x y = 0) ↔
      h1LinearEquiv K s x ∈ truncLinePowSubmodule K (s + 1) (s + 1 - a) := by
  let _ := h1Module K s
  let _ := h0Module K s
  rw [← truncLinePairing_orthogonal_powSubmodule K (s + 1) ha,
    LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h g hg
    obtain ⟨y, rfl⟩ := (h0LinearEquiv K s).surjective g
    rw [truncLinePairing_comm, ← serreCupLinear_eq_truncLinePairing]
    exact h y hg
  · intro h y hy
    rw [serreCupLinear_eq_truncLinePairing, truncLinePairing_comm]
    exact h _ hy

/-- **H^1(ℙ¹, O(−2)) ≅ K.** The trace is bijective. -/
theorem minusTwoTrace_bijective : Function.Bijective (minusTwoTrace K) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    apply vertexTwistActualStateAt_injective K Unit (negTwist 0) 1
    rw [map_zero]
    apply Subtype.ext
    ext κ
    have hκ : κ = fun _ => (0 : Fin 1) := _root_.funext fun v => @Subsingleton.elim (Fin 1) _ (κ v) 0
    rw [hκ]
    exact hz
  · intro c
    obtain ⟨z, hz⟩ := exists_gapCoord K 0 (fun _ => c)
    exact ⟨z, hz 0⟩

end BPFixedPoints.SerreComparison
