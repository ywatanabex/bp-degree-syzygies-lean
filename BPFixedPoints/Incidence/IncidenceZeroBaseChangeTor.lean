import BPFixedPoints.Incidence.IncidenceZeroBaseChangeModel

/-! # Tor is the cohomology of the Čech model base-changed to the coefficient origin

Let `K̄ = ZbcModule V E` with the Čech differential over `ℂ` of `zbcContraction`; by
`IncidenceZeroBaseChangeModel` this is `ℂ ⊗_{S_G} K` for the bounded Čech–Koszul model `K`
(`zbcBaseChangeEquiv`), and the Koszul part of the differential vanishes at the origin.

* **Bigrading.** `zbcPiece V E p q` consists of the chains with exterior degree `|S| = q` and
  Čech degree `q - p` (total degree `-p` in the cohomological convention, homological degree
  `p` here). The Čech differential maps `zbcPiece (p+1) q` to `zbcPiece p q`
  (`zbcContraction_d_mem`). A chain over `S_G` of total degree `p` and internal degree `q`
  specializes into `zbcPiece p q`, because coefficients of positive degree vanish at the origin
  (`zbcSpecialize_mem`).
* **Cohomology.** `ZbcCohomology p q` is the quotient of the cycles `zbcCycles p q` by the image
  of `zbcPiece (p+1) q` (`zbcBoundary`), with the class map `zbcClass` and the descent `zbcLift`.
* **The comparison.** `zbcTorToCohomology p q` sends a Tor class of bidegree `(p, q)` to the class
  of `zbcTorCycle p x`, the base change of the perturbed inclusion `ι : F → K` of the existing
  homological perturbation, composed with the derived-functor identification
  `Tor_p ≅ ℂ ⊗_{S_G} F_p`.
* **Theorem.** `zbcTorEquiv p q : Tor_p(𝒰_G, ℂ)_q ≃ₗ[ℂ] ZbcCohomology p q`. The proof uses only
  the base change of the existing perturbation data `(ι, P, H)` exhibiting `F` as a deformation
  retract of `K` over `S_G`, the freeness of `K` (`zbcBaseChangeEquiv`), and the minimality of
  `F` (the base change of its differential is zero, `zbc_baseChange_resolutionDifferential`):
  - injectivity: the base-changed projection `zbcProjectionMap` is a left inverse of the
    base-changed comparison (`P ι = 1`, `zbcProjectionMap_torCycle`) and kills boundaries
    (`P D = ∂ P` and `∂ ⊗ ℂ = 0`, `zbcProjectionMap_d`), and `incidenceTorToFull` is injective;
  - surjectivity: the base change of `D H + H D + ι P = 1` (`zbcHomotopyMap_identity`); the
    base-changed `P` and `H` respect the bigrading because `P` and `H` preserve the total and
    internal degrees over `S_G` (`zbcProjectionMap_mem`, `zbcHomotopyMap_mem`).
  No state basis, state coordinate, or state comparison of cohomology is used.
-/

namespace BPFixedPoints.Multigraph

open CechProduct IncidencePerturbation Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- The Čech chains of degree `n` over `ℂ`. -/
abbrev zbcCechPiece (V : Type) [Fintype V] (n : ℤ) : Submodule ℂ (CechProduct.C ℂ V) :=
  supported ℂ ℂ {b : V → CechProduct.Basis | (cechDegree b : ℤ) = n}

/-- The slot of an edge subset in bidegree `(p, q)`: the Čech chains of degree `q - p` if the
edge subset has `q` elements, and zero otherwise. -/
def zbcSlot (V : Type) [Fintype V] (p q : ℕ) (S : Finset E) : Submodule ℂ (CechProduct.C ℂ V) :=
  if S.card = q then zbcCechPiece V ((q : ℤ) - p) else ⊥

theorem mem_zbcSlot_iff (p q : ℕ) (S : Finset E) (x : CechProduct.C ℂ V) :
    x ∈ zbcSlot V p q S ↔ (S.card = q → x ∈ zbcCechPiece V ((q : ℤ) - p)) ∧ (S.card ≠ q → x = 0) := by
  unfold zbcSlot
  by_cases h : S.card = q
  · simp [h]
  · simp [h]

/-- The piece of total homological degree `p` and internal degree `q` of the base-changed model:
exterior degree `|S| = q` and Čech degree `q - p`. -/
def zbcPiece (V E : Type) [Fintype V] [DecidableEq E] (p q : ℕ) : Submodule ℂ (ZbcModule V E) where
  carrier := {x | ∀ S, x S ∈ zbcSlot V p q S}
  zero_mem' := fun _ => Submodule.zero_mem _
  add_mem' hx hy := fun S => Submodule.add_mem _ (hx S) (hy S)
  smul_mem' c _ hx := fun S => Submodule.smul_mem _ c (hx S)

theorem mem_zbcPiece_iff (p q : ℕ) (x : ZbcModule V E) :
    x ∈ zbcPiece V E p q ↔ ∀ S, x S ∈ zbcSlot V p q S := Iff.rfl

/-- The Čech differential lowers the homological degree of the bigrading by one. -/
theorem zbcContraction_d_mem (p q : ℕ) {x : ZbcModule V E} (hx : x ∈ zbcPiece V E (p + 1) q) :
    G.zbcContraction.d x ∈ zbcPiece V E p q := by
  intro S
  have h := (mem_zbcSlot_iff (p + 1) q S (x S)).mp (hx S)
  rw [mem_zbcSlot_iff, zbcContraction_d_apply]
  refine ⟨fun hS => ?_, fun hS => by rw [h.2 hS, map_zero]⟩
  have hd := contraction_d_degree ℂ (G.deg S) _ (x S) (h.1 hS)
  have he : ((q : ℤ) - ((p + 1 : ℕ) : ℤ)) + 1 = (q : ℤ) - p := by push_cast; ring
  rw [he] at hd
  exact hd

/-- The cycles of the base-changed model in homological degree `p` and internal degree `q`. -/
def zbcCycles (p q : ℕ) : Submodule ℂ (ZbcModule V E) :=
  zbcPiece V E p q ⊓ LinearMap.ker G.zbcContraction.d

@[reducible] local instance zbcCyclesAddCommGroup (p q : ℕ) : AddCommGroup (G.zbcCycles p q) :=
  (G.zbcCycles p q).addCommGroup

@[reducible] local instance zbcCyclesModule (p q : ℕ) : Module ℂ (G.zbcCycles p q) :=
  (G.zbcCycles p q).module

@[reducible] local instance zbcPieceAddCommGroup (p q : ℕ) : AddCommGroup (zbcPiece V E p q) :=
  (zbcPiece V E p q).addCommGroup

@[reducible] local instance zbcPieceModule (p q : ℕ) : Module ℂ (zbcPiece V E p q) :=
  (zbcPiece V E p q).module

/-- The differential from bidegree `(p + 1, q)` into the cycles of bidegree `(p, q)`. -/
def zbcBoundary (p q : ℕ) : zbcPiece V E (p + 1) q →ₗ[ℂ] G.zbcCycles p q :=
  (G.zbcContraction.d.comp (zbcPiece V E (p + 1) q).subtype).codRestrict _ fun y =>
    ⟨G.zbcContraction_d_mem p q y.property, LinearMap.congr_fun G.zbcContraction.d_sq y.val⟩

@[simp] theorem zbcBoundary_val (p q : ℕ) (y : zbcPiece V E (p + 1) q) :
    (G.zbcBoundary p q y).val = G.zbcContraction.d y.val := rfl

/-- The cohomology of the base-changed model `ℂ ⊗_{S_G} K` in homological degree `p` (total
degree `-p`) and internal degree `q`. -/
abbrev ZbcCohomology (p q : ℕ) := G.zbcCycles p q ⧸ LinearMap.range (G.zbcBoundary p q)

/-- The class of a cycle. -/
def zbcClass (p q : ℕ) : G.zbcCycles p q →ₗ[ℂ] G.ZbcCohomology p q :=
  (LinearMap.range (G.zbcBoundary p q)).mkQ

theorem zbcClass_surjective (p q : ℕ) : Function.Surjective (G.zbcClass p q) :=
  Submodule.mkQ_surjective _

theorem zbcClass_eq_zero_iff (p q : ℕ) (z : G.zbcCycles p q) :
    G.zbcClass p q z = 0 ↔ ∃ y ∈ zbcPiece V E (p + 1) q, G.zbcContraction.d y = z.val := by
  rw [zbcClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy, hdy⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩

theorem zbcClass_eq_iff (p q : ℕ) (z w : G.zbcCycles p q) :
    G.zbcClass p q z = G.zbcClass p q w ↔
      ∃ y ∈ zbcPiece V E (p + 1) q, G.zbcContraction.d y = z.val - w.val := by
  rw [← sub_eq_zero, ← map_sub, zbcClass_eq_zero_iff]
  rfl

/-- Descend a linear map on cycles that kills the boundaries. -/
def zbcLift {N : Type*} [AddCommGroup N] [Module ℂ N] (p q : ℕ) (f : G.zbcCycles p q →ₗ[ℂ] N)
    (hf : ∀ y : zbcPiece V E (p + 1) q, f (G.zbcBoundary p q y) = 0) :
    G.ZbcCohomology p q →ₗ[ℂ] N :=
  (LinearMap.range (G.zbcBoundary p q)).liftQ f (by
    rintro _ ⟨y, rfl⟩
    exact hf y)

@[simp] theorem zbcLift_class {N : Type*} [AddCommGroup N] [Module ℂ N] (p q : ℕ)
    (f : G.zbcCycles p q →ₗ[ℂ] N)
    (hf : ∀ y : zbcPiece V E (p + 1) q, f (G.zbcBoundary p q y) = 0) (z : G.zbcCycles p q) :
    G.zbcLift p q f hf (G.zbcClass p q z) = f z := rfl

/-- A chain that is homogeneous of total degree `p` and internal degree `q` over `S_G` specializes
into the piece of bidegree `(p, q)`: coefficients of positive degree vanish at the origin. -/
theorem zbcSpecialize_mem {p q : ℕ} {x : IncTotalModule (V := V) (E := E)}
    (hp : x ∈ incTotalPiece (p : ℤ)) (hq : x ∈ incTotalInternalPiece (q : ℤ)) :
    zbcSpecialize x ∈ zbcPiece V E p q := by
  intro S
  rw [mem_zbcSlot_iff, zbcSpecialize_apply]
  refine ⟨fun hS => ?_, fun hS => ?_⟩
  · rw [mem_supported']
    intro b hb
    rw [mapRange_apply]
    have h0 : x S b = 0 := by
      apply (mem_supported' _ _).mp (hp S) b
      change ¬ ((cechDegree b : ℤ) = (S.card : ℤ) - p)
      rw [hS]
      exact hb
    rw [h0, map_zero]
  · ext b
    rw [mapRange_apply, Finsupp.zero_apply]
    apply ResolutionTools.constantCoeff_eq_zero_of_homogeneous (hq S b)
    omega

/-- The perturbed homotopy preserves the internal degree. -/
theorem zbcHomotopy_internal_degree (q : ℤ) {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) : G.incResolutionHomotopy x ∈ incTotalInternalPiece q :=
  G.incCechContraction.contractingHomotopy_mem_of_preserves G.incKoszulPerturbation
    (incTotalInternalPiece q)
    (fun _ hx => G.incKoszulPerturbation_internal_degree q hx)
    (fun _ hx => G.incCechContraction_h_internal_degree q hx)
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩ hx

/-- The basis chain of an exterior state `S` and a Čech monomial `b`, with coefficient one. -/
abbrev zbcBasisChain (S : Finset E) (b : V → CechProduct.Basis) : IncTotalModule (V := V) (E := E) :=
  single S (single b 1)

theorem zbcBasisChain_mem_total {p q : ℕ} {S : Finset E} {b : V → CechProduct.Basis}
    (hS : S.card = q) (hb : (cechDegree b : ℤ) = (q : ℤ) - p) :
    zbcBasisChain S b ∈ incTotalPiece (p : ℤ) := by
  apply incTotalPiece_single
  apply single_mem_supported (IncCoeffRing E) 1
  change (cechDegree b : ℤ) = (S.card : ℤ) - p
  rw [hS]
  exact hb

theorem zbcBasisChain_mem_internal {q : ℕ} {S : Finset E} (b : V → CechProduct.Basis)
    (hS : S.card = q) : zbcBasisChain S b ∈ incTotalInternalPiece (q : ℤ) := by
  apply incTotalInternalPiece_single
  intro b'
  have h1 : (1 : IncCoeffRing E) ∈ ResolutionTools.homogeneousCoeffPiece ((q : ℤ) - (S.card : ℤ)) := by
    rw [hS, sub_self, ← Nat.cast_zero, ResolutionTools.homogeneousCoeffPiece_nat]
    exact MvPolynomial.isHomogeneous_one _ _
  by_cases hb : b' = b
  · subst hb
    rw [single_eq_same]
    exact h1
  · rw [single_eq_of_ne hb]
    exact Submodule.zero_mem _

/-- A submodule containing every single chain of bidegree `(p, q)` contains the whole piece. -/
theorem zbcPiece_le_of_single {p q : ℕ} (N : Submodule ℂ (ZbcModule V E))
    (h : ∀ (S : Finset E) (b : V → CechProduct.Basis) (c : ℂ), S.card = q →
      (cechDegree b : ℤ) = (q : ℤ) - p → single S (single b c) ∈ N) :
    zbcPiece V E p q ≤ N := by
  intro z hz
  rw [← z.sum_single]
  apply Submodule.finsuppSum_mem
  intro S _
  by_cases hS : S.card = q
  · have hzS := ((mem_zbcSlot_iff p q S (z S)).mp (hz S)).1 hS
    rw [← (z S).sum_single, ← Finsupp.lsingle_apply (R := ℂ), map_finsuppSum]
    apply Submodule.finsuppSum_mem
    intro b hb
    rw [Finsupp.lsingle_apply]
    apply h S b _ hS
    by_contra hne
    exact hb ((mem_supported' ℂ _).mp hzS b hne)
  · rw [((mem_zbcSlot_iff p q S (z S)).mp (hz S)).2 hS, single_zero]
    exact Submodule.zero_mem _

/-- The base-changed comparison sends a Tor class of bidegree `(p, q)` to a cycle of bidegree
`(p, q)`: `ι` preserves both degrees, and `ι` of a boundary of the minimal resolution vanishes at
the origin. -/
theorem zbcTorCycle_mem {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    G.zbcTorCycle p x.val ∈ G.zbcCycles p q := by
  obtain ⟨f, hf, hfx⟩ := x.property
  rw [← hfx, zbcTorCycle_class]
  refine ⟨zbcSpecialize_mem (G.incResolutionInclusion_degree p f.val f.property)
    (G.incResolutionInclusion_internal_degree q ((G.mem_incFreeTermInternalPiece_iff p q f).mp hf)), ?_⟩
  change G.zbcContraction.d (zbcSpecialize (G.incResolutionInclusion f.val)) = 0
  have hc : G.incTotalDifferential (G.incResolutionInclusion f.val) =
      G.incResolutionInclusion (G.incResolutionDifferential f.val) :=
    LinearMap.congr_fun G.incResolutionInclusion_chain f.val
  rw [← zbcSpecialize_total, hc]
  exact zbc_map_eq_zero_of_mem zbcSpecialize
    (ResolutionTools.map_mem_ideal_smul_top _ G.incResolutionInclusion (G.incResolutionDifferential_minimal f.val))

/-- The base change of the comparison chain map, on the bigraded pieces of Tor. -/
def zbcTorToCohomology (p q : ℕ) : G.incidenceTorInternalPiece p q →ₗ[ℂ] G.ZbcCohomology p q :=
  G.zbcClass p q ∘ₗ
    LinearMap.codRestrict (G.zbcCycles p q)
      ((G.zbcTorCycle p).comp (G.incidenceTorInternalPiece p q).subtype)
      (fun x => G.zbcTorCycle_mem x)

theorem zbcTorToCohomology_apply {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    G.zbcTorToCohomology p q x = G.zbcClass p q ⟨G.zbcTorCycle p x.val, G.zbcTorCycle_mem x⟩ := rfl

section BaseChange

open scoped TensorProduct

local instance zeroBaseChangeTorAlgebra : Algebra (IncCoeffRing E) ℂ := (zbcOrigin E).toAlgebra

/-- `v ↦ c ⊗ v` is semilinear over the coefficient origin. -/
def zbcTmul {M : Type*} [AddCommMonoid M] [Module (IncCoeffRing E) M] (c : ℂ) :
    M →ₛₗ[zbcOrigin E] ℂ ⊗[IncCoeffRing E] M where
  toFun v := c ⊗ₜ v
  map_add' := TensorProduct.tmul_add c
  map_smul' r v := by
    change c ⊗ₜ[IncCoeffRing E] (r • v) = zbcOrigin E r • (c ⊗ₜ[IncCoeffRing E] v)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
    rfl

/-- The base change of the transferred differential of the minimal resolution is zero. -/
theorem zbc_baseChange_resolutionDifferential :
    G.incResolutionDifferential.baseChange ℂ = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c f
  rw [LinearMap.baseChange_tmul, LinearMap.zero_apply]
  exact zbc_map_eq_zero_of_mem (zbcTmul c) (G.incResolutionDifferential_minimal f)

theorem zbcBaseChangeEquiv_symm_single (S : Finset E) (b : V → CechProduct.Basis) (c : ℂ) :
    zbcBaseChangeEquiv.symm (single S (single b c)) =
      c ⊗ₜ[IncCoeffRing E] zbcBasisChain (V := V) S b := by
  apply zbcBaseChangeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, zbcBaseChangeEquiv_tmul]
  ext T b'
  rw [Finsupp.smul_apply, Finsupp.smul_apply, zbcSpecialize_apply]
  by_cases hT : S = T
  · subst hT
    rw [single_eq_same, single_eq_same, mapRange_apply]
    by_cases hb : b = b'
    · subst hb
      rw [single_eq_same, single_eq_same, map_one, smul_eq_mul, mul_one]
    · rw [single_eq_of_ne' hb, single_eq_of_ne' hb, map_zero, smul_zero]
  · rw [single_eq_of_ne' hT, single_eq_of_ne' hT]
    simp

/-- The base change of the perturbed projection, read on the base-changed model. -/
def zbcProjectionMap : ZbcModule V E →ₗ[ℂ] ℂ ⊗[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  (G.incResolutionProjection.baseChange ℂ) ∘ₗ zbcBaseChangeEquiv.symm.toLinearMap

/-- The base change of the perturbed homotopy, read on the base-changed model. -/
def zbcHomotopyMap : Module.End ℂ (ZbcModule V E) :=
  zbcBaseChangeEquiv.toLinearMap ∘ₗ (G.incResolutionHomotopy.baseChange ℂ) ∘ₗ
    zbcBaseChangeEquiv.symm.toLinearMap

/-- The base-changed projection is a left inverse of the base-changed comparison. -/
theorem zbcProjectionMap_torCycle (p : ℕ) (x : G.incidenceTor p) :
    G.zbcProjectionMap (G.zbcTorCycle p x) = G.incidenceTorToFull p x := by
  change (G.incResolutionProjection.baseChange ℂ)
    (zbcBaseChangeEquiv.symm (zbcBaseChangeEquiv
      ((G.incResolutionInclusion.baseChange ℂ) (G.incidenceTorToFull p x)))) = _
  rw [LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    G.incResolutionProjection_inclusion, LinearMap.baseChange_id, LinearMap.id_apply]

/-- The base-changed projection kills the boundaries of the base-changed model. -/
theorem zbcProjectionMap_d (y : ZbcModule V E) :
    G.zbcProjectionMap (G.zbcContraction.d y) = 0 := by
  have hy : zbcBaseChangeEquiv.symm (G.zbcContraction.d y) =
      G.incTotalDifferential.baseChange ℂ (zbcBaseChangeEquiv.symm y) := by
    apply zbcBaseChangeEquiv.injective
    rw [LinearEquiv.apply_symm_apply, zbcBaseChangeEquiv_differential, LinearEquiv.apply_symm_apply]
  change (G.incResolutionProjection.baseChange ℂ) (zbcBaseChangeEquiv.symm (G.zbcContraction.d y)) = 0
  rw [hy, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, G.incResolutionProjection_chain,
    LinearMap.baseChange_comp, LinearMap.comp_apply, zbc_baseChange_resolutionDifferential,
    LinearMap.zero_apply]

/-- The base change of the perturbed homotopy identity `D H + H D + ι P = 1`. -/
theorem zbcHomotopyMap_identity (z : ZbcModule V E) (hz : G.zbcContraction.d z = 0) :
    z = G.zbcContraction.d (G.zbcHomotopyMap z) +
      zbcBaseChangeEquiv ((G.incResolutionInclusion.baseChange ℂ) (G.zbcProjectionMap z)) := by
  have hid := congrArg (fun f => f.baseChange ℂ) G.incResolutionHomotopy_identity
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_comp, LinearMap.baseChange_id] at hid
  have h := LinearMap.congr_fun hid (zbcBaseChangeEquiv.symm z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
  have hD : G.incTotalDifferential.baseChange ℂ (zbcBaseChangeEquiv.symm z) = 0 := by
    apply zbcBaseChangeEquiv.injective
    rw [zbcBaseChangeEquiv_differential, LinearEquiv.apply_symm_apply, hz,
      LinearEquiv.map_zero]
  rw [hD, LinearMap.map_zero, add_zero] at h
  have h2 := congrArg zbcBaseChangeEquiv h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_add, zbcBaseChangeEquiv_differential] at h2
  exact h2.symm

/-- The base-changed projection maps the piece of bidegree `(p, q)` into the base change of the
bigraded piece of Tor. -/
theorem zbcProjectionMap_mem {p q : ℕ} {z : ZbcModule V E} (hz : z ∈ zbcPiece V E p q) :
    G.zbcProjectionMap z ∈ (G.incidenceTorInternalPiece p q).map (G.incidenceTorToFull p) := by
  refine (zbcPiece_le_of_single
    (((G.incidenceTorInternalPiece p q).map (G.incidenceTorToFull p)).comap G.zbcProjectionMap)
    fun S b c hS hb => ?_) hz
  rw [Submodule.mem_comap]
  have he := zbcBasisChain_mem_total (V := V) hS hb
  have hi := zbcBasisChain_mem_internal (V := V) b hS
  let f : G.IncFreeTerm p :=
    ⟨G.incResolutionProjection (zbcBasisChain S b), G.incResolutionProjection_degree p _ he⟩
  have hf : f ∈ G.incFreeTermInternalPiece p q :=
    (G.mem_incFreeTermInternalPiece_iff p q f).mpr (G.incResolutionProjection_internal_degree q hi)
  refine ⟨c • G.incFreeTermToTor p f, Submodule.smul_mem _ c ⟨f, hf, rfl⟩, ?_⟩
  change G.incidenceTorToFull p (c • G.incFreeTermToTor p f) =
    (G.incResolutionProjection.baseChange ℂ) (zbcBaseChangeEquiv.symm (single S (single b c)))
  rw [map_smul, incidenceTorToFull_class, zbcBaseChangeEquiv_symm_single, LinearMap.baseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The base-changed homotopy raises the homological degree of the bigrading by one. -/
theorem zbcHomotopyMap_mem {p q : ℕ} {z : ZbcModule V E} (hz : z ∈ zbcPiece V E p q) :
    G.zbcHomotopyMap z ∈ zbcPiece V E (p + 1) q := by
  refine (zbcPiece_le_of_single ((zbcPiece V E (p + 1) q).comap G.zbcHomotopyMap)
    fun S b c hS hb => ?_) hz
  have he := zbcBasisChain_mem_total (V := V) hS hb
  have hi := zbcBasisChain_mem_internal (V := V) b hS
  rw [Submodule.mem_comap]
  change zbcBaseChangeEquiv ((G.incResolutionHomotopy.baseChange ℂ)
    (zbcBaseChangeEquiv.symm (single S (single b c)))) ∈ zbcPiece V E (p + 1) q
  rw [zbcBaseChangeEquiv_symm_single, LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul]
  apply Submodule.smul_mem
  apply zbcSpecialize_mem _ (G.zbcHomotopy_internal_degree _ hi)
  have h := G.incResolutionHomotopy_shifts (p : ℤ) _ he
  push_cast
  exact h

theorem zbcTorToCohomology_injective (p q : ℕ) :
    Function.Injective (G.zbcTorToCohomology p q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [zbcTorToCohomology_apply, zbcClass_eq_zero_iff] at hx
  obtain ⟨y, -, hy⟩ := hx
  have h := congrArg G.zbcProjectionMap hy
  change G.zbcProjectionMap (G.zbcContraction.d y) = G.zbcProjectionMap (G.zbcTorCycle p x.val) at h
  rw [zbcProjectionMap_d, zbcProjectionMap_torCycle] at h
  apply Subtype.ext
  apply G.incidenceTorToFull_injective p
  rw [← h, Submodule.coe_zero, map_zero]

theorem zbcTorToCohomology_surjective (p q : ℕ) :
    Function.Surjective (G.zbcTorToCohomology p q) := by
  intro c
  obtain ⟨z, rfl⟩ := G.zbcClass_surjective p q c
  obtain ⟨x, hx, hTx⟩ := G.zbcProjectionMap_mem z.property.1
  refine ⟨⟨x, hx⟩, ?_⟩
  rw [zbcTorToCohomology_apply, zbcClass_eq_iff]
  refine ⟨-(G.zbcHomotopyMap z.val), neg_mem (G.zbcHomotopyMap_mem z.property.1), ?_⟩
  have hid := G.zbcHomotopyMap_identity z.val z.property.2
  change G.zbcContraction.d (-(G.zbcHomotopyMap z.val)) = G.zbcTorCycle p x - z.val
  have hc : G.zbcTorCycle p x =
      zbcBaseChangeEquiv ((G.incResolutionInclusion.baseChange ℂ) (G.zbcProjectionMap z.val)) := by
    rw [← hTx]
    rfl
  rw [map_neg, hc]
  set a := G.zbcContraction.d (G.zbcHomotopyMap z.val)
  set b := zbcBaseChangeEquiv ((G.incResolutionInclusion.baseChange ℂ) (G.zbcProjectionMap z.val))
  rw [hid]
  abel

end BaseChange

/-- **Tor is computed by the base-changed Čech model.** The base change of the comparison chain
map `ι : F → K` along the coefficient origin is an isomorphism from the bigraded piece of actual
Tor (Mathlib's left derived extension of scalars) onto the cohomology of `ℂ ⊗_{S_G} K` in
homological degree `p` and internal degree `q`. -/
def zbcTorEquiv (p q : ℕ) : G.incidenceTorInternalPiece p q ≃ₗ[ℂ] G.ZbcCohomology p q :=
  LinearEquiv.ofBijective (G.zbcTorToCohomology p q)
    ⟨G.zbcTorToCohomology_injective p q, G.zbcTorToCohomology_surjective p q⟩

theorem zbcTorEquiv_apply {p q : ℕ} (x : G.incidenceTorInternalPiece p q) :
    G.zbcTorEquiv p q x = G.zbcClass p q ⟨G.zbcTorCycle p x.val, G.zbcTorCycle_mem x⟩ := rfl

end

end BPFixedPoints.Multigraph
