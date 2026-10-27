import BPFixedPoints.Incidence.IncidenceUniversalKoszulCech
import BPFixedPoints.Incidence.ResolutionAugmentation

/-! # Cohomology of the Čech–Koszul total complex of `K_G`: concentration in degree zero

The Čech–Koszul total complex of `K_G` on the face cover (`IncidenceUniversalKoszulCech.lean`)
has cohomology concentrated in total degree zero, where it is the universal incidence ring
`𝒰_G = IncidenceRing` (the Čech side of Theorem `alg:resolution`). The proofs transport, along
the comparison `univCechKoszulEquiv`, results on the existing incidence total complex, using the
existing local Koszul contraction (`incKoszulContraction`, onto the Čech complex of the face
incidence rings) and the existing exact finite free model (`incResolutionInclusion`,
`incResolutionProjection`, `incResolutionHomotopy`).

* **Existing total complex.** Exactness in negative homological total degree, i.e. positive
  cohomological degree (`incTotalDifferential_exact_of_neg`, through the free model, which has no
  negative terms), hence in every nonzero degree (`incTotalDifferential_exact_of_ne_zero`, with
  the existing `incTotalDifferential_exact`). The torus augmentation `incTotalTorusAugmentation`
  sends degree-zero cycles into `𝒰_G` (`incTotalTorusAugmentation_mem`), onto it
  (`exists_incTotal_cycle_of_incidence`), with kernel the boundaries
  (`incTotalTorusAugmentation_exact`).
* **Sections of `K_G`.** In every total degree `n ≠ 0` the cycles of the Čech–Koszul total
  complex of `K_G` are boundaries (`univCechKoszul_exact_of_ne_zero`). The `S_G`-linear
  augmentation `univCechKoszulAugmentation` of degree-zero cycles to `𝒰_G` is the torus value of
  the face augmentation of sections on the all-left chart
  (`univCechKoszulTorusAugmentation_apply`); it is surjective
  (`univCechKoszulAugmentation_surjective`) with kernel the boundaries
  (`univCechKoszulAugmentation_eq_zero_iff`), so `H^0 ≅ 𝒰_G` (`univCechKoszulH0Equiv`).

Not proved here: that this Čech total complex computes the derived global sections
`RΓ(X_G × B_G, K_G)`; with it, these statements would be the concentration part of
`alg:resolution`.
-/

namespace BPFixedPoints.Multigraph

open CechProduct ResolutionTools IncidencePerturbation

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance univKoszulTorusAlgebra : Algebra (IncCoeffRing E) G.IncTorusRing :=
  G.incTorusCoeffHom.toRingHom.toAlgebra

noncomputable local instance univKoszulIncidenceAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

/-! ### Cohomology of the existing incidence total complex -/

section Existing

/-- **Exactness in negative total degrees.** In homological total degree `n < 0` (positive
cohomological degree), every cycle of the incidence total complex is a boundary: the finite free
model has no terms of negative degree, and the total complex retracts onto it. -/
theorem incTotalDifferential_exact_of_neg {n : ℤ} (hn : n < 0)
    (x : IncTotalModule (V := V) (E := E)) (hx : x ∈ incTotalPiece n)
    (hDx : G.incTotalDifferential x = 0) :
    ∃ y, y ∈ incTotalPiece (n + 1) ∧ G.incTotalDifferential y = x := by
  have hp : G.incResolutionProjection x = 0 := by
    have h := G.incResolutionProjection_shifts n x hx
    rw [add_zero, incResolutionPiece, Finsupp.mem_supported] at h
    refine Finsupp.ext fun b => ?_
    by_contra hb
    have hb' := h (Finsupp.mem_support_iff.mpr hb)
    simp only [Set.mem_ofPred_eq] at hb'
    omega
  refine ⟨G.incResolutionHomotopy x, G.incResolutionHomotopy_shifts n x hx, ?_⟩
  have hid := LinearMap.congr_fun G.incResolutionHomotopy_identity x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hDx, map_zero, hp, add_zero,
    LinearMap.id_apply] at hid
  exact hid

/-- **Vanishing of the cohomology of the incidence total complex outside degree zero.** -/
theorem incTotalDifferential_exact_of_ne_zero {n : ℤ} (hn : n ≠ 0)
    (x : IncTotalModule (V := V) (E := E)) (hx : x ∈ incTotalPiece n)
    (hDx : G.incTotalDifferential x = 0) :
    ∃ y, y ∈ incTotalPiece (n + 1) ∧ G.incTotalDifferential y = x := by
  rcases lt_or_gt_of_ne hn with h | h
  · exact G.incTotalDifferential_exact_of_neg h x hx hDx
  · exact G.incTotalDifferential_exact h x hx hDx

/-- The value of a total element on the common torus: the all-left face of its projection to the
local incidence rings. -/
noncomputable def incTotalTorusAugmentation :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] G.IncTorusRing :=
  G.incFaceRawEval (chartFace fun _ : V => false)

/-- The torus augmentation is the torus value of the local quotient projection at the all-left
chart. -/
theorem incTotalTorusAugmentation_apply (x : IncTotalModule (V := V) (E := E)) :
    G.incTotalTorusAugmentation x =
      G.incFaceToTorus (chartFace fun _ : V => false)
        (G.incKoszulContraction.p x (chartFace fun _ : V => false)) :=
  G.incFaceRawEval_eq_projection _ _

/-- The local quotient projection of a degree-zero total cycle is a degree-zero quotient Čech
cycle. -/
theorem incKoszulContraction_p_cycle (x : IncTotalModule (V := V) (E := E))
    (hx : x ∈ incTotalPiece 0) (hDx : G.incTotalDifferential x = 0) :
    G.incKoszulContraction.p x ∈ G.incQuotientPiece 0 ∧
      G.incQuotientDifferential (G.incKoszulContraction.p x) = 0 := by
  constructor
  · have h := G.incKoszulContraction_p_shifts 0 x hx
    simpa only [add_zero] using h
  · have h := LinearMap.congr_fun G.incQuotientProjection_chain x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hDx, map_zero] at h
    rw [G.incQuotientProjection_eq] at h
    exact h.symm

/-- Degree-zero total cycles take values in the incidence ring `𝒰_G`. -/
theorem incTotalTorusAugmentation_mem (x : IncTotalModule (V := V) (E := E))
    (hx : x ∈ incTotalPiece 0) (hDx : G.incTotalDifferential x = 0) :
    G.incTotalTorusAugmentation x ∈ G.IncidenceRing := by
  rw [incTotalTorusAugmentation_apply]
  obtain ⟨hp, hdp⟩ := G.incKoszulContraction_p_cycle x hx hDx
  exact G.incQuotientCycle_torus_mem _ hp hdp

/-- Every element of `𝒰_G` is the value of a degree-zero total cycle. -/
theorem exists_incTotal_cycle_of_incidence (u : G.IncidenceRing) :
    ∃ x, x ∈ incTotalPiece (V := V) (E := E) 0 ∧ G.incTotalDifferential x = 0 ∧
      G.incTotalTorusAugmentation x = u.val := by
  obtain ⟨y, hy, hdy, hyu⟩ := G.exists_incQuotientCycle_of_incidence u
  refine ⟨G.incQuotientInclusion y, ?_, ?_, ?_⟩
  · have h := G.incQuotientInclusion_shifts 0 y hy
    simpa only [add_zero, Submodule.restrictScalars_mem] using h
  · have h := LinearMap.congr_fun G.incQuotientInclusion_chain y
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hdy, map_zero] using h
  · rw [incTotalTorusAugmentation_apply]
    have h := LinearMap.congr_fun G.incQuotientProjection_inclusion y
    rw [LinearMap.comp_apply, G.incQuotientProjection_eq, LinearMap.id_apply] at h
    rw [h, hyu]

/-- **`H^0` of the incidence total complex.** A degree-zero total cycle has value zero in `𝒰_G`
exactly when it is a boundary. -/
theorem incTotalTorusAugmentation_exact (x : IncTotalModule (V := V) (E := E))
    (hx : x ∈ incTotalPiece 0) (hDx : G.incTotalDifferential x = 0) :
    G.incTotalTorusAugmentation x = 0 ↔
      ∃ y, y ∈ incTotalPiece (V := V) (E := E) 1 ∧ G.incTotalDifferential y = x := by
  constructor
  · intro h0
    obtain ⟨hp, hdp⟩ := G.incKoszulContraction_p_cycle x hx hDx
    have hpx : G.incKoszulContraction.p x = 0 := by
      apply G.incQuotientCycle_eq_zero_of_torus_eq_zero _ hp hdp
      rw [← incTotalTorusAugmentation_apply]
      exact h0
    obtain ⟨y, hy, hDy⟩ := G.incTotalDifferential_exact_of_projection_zero 0 x hx hDx hpx
    exact ⟨y, by simpa only [zero_add] using hy, hDy⟩
  · rintro ⟨y, hy, rfl⟩
    have hpy : G.incKoszulContraction.p y = 0 := by
      have h := G.incKoszulContraction_p_shifts 1 y hy
      change G.incKoszulContraction.p y ∈ G.incQuotientPiece (1 + 0) at h
      rw [G.incQuotientPiece_eq_bot_of_positive (by norm_num)] at h
      exact h
    have h := LinearMap.congr_fun G.incQuotientProjection_chain y
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
    rw [G.incQuotientProjection_eq, hpy, map_zero] at h
    rw [incTotalTorusAugmentation_apply, h]
    exact map_zero _

end Existing

/-! ### Cohomology of the Čech–Koszul total complex of `K_G` -/

section Sheaf

/-- **Vanishing of the Čech hypercohomology of `K_G` outside degree zero.** On the face cover, a
cycle of the Čech–Koszul total complex of `K_G` of total degree `n ≠ 0` is a boundary. -/
theorem univCechKoszul_exact_of_ne_zero {n : ℤ} (hn : n ≠ 0) (x : G.UnivCechKoszulModule)
    (hx : x ∈ G.univCechKoszulPiece n) (hDx : G.univCechKoszulDifferential x = 0) :
    ∃ y, y ∈ G.univCechKoszulPiece (n + 1) ∧ G.univCechKoszulDifferential y = x := by
  have hx' := (G.univCechKoszulEquiv_mem_piece n x).mpr hx
  have hDx' : G.incTotalDifferential (G.univCechKoszulEquiv x) = 0 := by
    rw [← univCechKoszulEquiv_differential, hDx, map_zero]
  obtain ⟨y', hy', hDy'⟩ := G.incTotalDifferential_exact_of_ne_zero hn _ hx' hDx'
  refine ⟨G.univCechKoszulEquiv.symm y', ?_, ?_⟩
  · apply (G.univCechKoszulEquiv_mem_piece (n + 1) _).mp
    rwa [LinearEquiv.apply_symm_apply]
  · apply G.univCechKoszulEquiv.injective
    rw [univCechKoszulEquiv_differential, LinearEquiv.apply_symm_apply, hDy']

/-- **The augmentation of the Čech–Koszul total complex** to the common torus: the value at the
all-left chart of the face augmentation of the `∅` component (a section of `O` over the chart),
`S_G`-linear. -/
noncomputable def univCechKoszulTorusAugmentation :
    G.UnivCechKoszulModule →ₗ[IncCoeffRing E] G.IncTorusRing :=
  G.incTotalTorusAugmentation.comp G.univCechKoszulEquiv.toLinearMap

/-- The augmentation is the torus value of the face augmentation of sections on the all-left
chart. -/
theorem univCechKoszulTorusAugmentation_apply (x : G.UnivCechKoszulModule) :
    G.univCechKoszulTorusAugmentation x =
      G.incFaceToTorus (chartFace fun _ : V => false)
        (G.univCechKoszulFaceAugmentation x (chartFace fun _ : V => false)) := by
  have hq : faceDegree (chartFace fun _ : V => false) = 0 := by
    simp [faceDegree, chartFace]
  rw [univCechKoszulTorusAugmentation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    incTotalTorusAugmentation_apply, incKoszulContraction_p_univ, hq, pow_zero, one_smul]

/-- The `S_G`-submodule of degree-zero cycles of the Čech–Koszul total complex. -/
noncomputable def univCechKoszulCycles0 : Submodule (IncCoeffRing E) G.UnivCechKoszulModule :=
  G.univCechKoszulPiece 0 ⊓ LinearMap.ker G.univCechKoszulDifferential

/-- **The augmentation `H^0 → 𝒰_G`** on degree-zero cycles, linear over `S_G`. -/
noncomputable def univCechKoszulAugmentation :
    G.univCechKoszulCycles0 →ₗ[IncCoeffRing E] G.IncidenceRing where
  toFun x := ⟨G.univCechKoszulTorusAugmentation x.val, by
    have h1 := (G.univCechKoszulEquiv_mem_piece 0 _).mpr x.property.1
    have h2 : G.incTotalDifferential (G.univCechKoszulEquiv x.val) = 0 := by
      rw [← univCechKoszulEquiv_differential, LinearMap.mem_ker.mp x.property.2, map_zero]
    exact G.incTotalTorusAugmentation_mem _ h1 h2⟩
  map_add' x y := by
    apply Subtype.ext
    exact G.univCechKoszulTorusAugmentation.map_add x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    exact G.univCechKoszulTorusAugmentation.map_smul r x.val

/-- The augmentation of a degree-zero cycle, as an element of the torus ring. -/
@[simp] theorem univCechKoszulAugmentation_val (x : G.univCechKoszulCycles0) :
    (G.univCechKoszulAugmentation x).val = G.univCechKoszulTorusAugmentation x.val := rfl

/-- **The augmentation is surjective onto `𝒰_G`.** -/
theorem univCechKoszulAugmentation_surjective :
    Function.Surjective G.univCechKoszulAugmentation := by
  intro u
  obtain ⟨x', hx', hDx', hxu⟩ := G.exists_incTotal_cycle_of_incidence u
  refine ⟨⟨G.univCechKoszulEquiv.symm x', ?_, ?_⟩, ?_⟩
  · apply (G.univCechKoszulEquiv_mem_piece 0 _).mp
    rwa [LinearEquiv.apply_symm_apply]
  · apply LinearMap.mem_ker.mpr
    apply G.univCechKoszulEquiv.injective
    rw [univCechKoszulEquiv_differential, LinearEquiv.apply_symm_apply, hDx', map_zero]
  · apply Subtype.ext
    rw [univCechKoszulAugmentation_val, univCechKoszulTorusAugmentation, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hxu]

/-- **The kernel of the augmentation is the boundaries.** A degree-zero cycle of the Čech–Koszul
total complex of `K_G` goes to zero in `𝒰_G` exactly when it is a boundary. -/
theorem univCechKoszulAugmentation_eq_zero_iff (x : G.univCechKoszulCycles0) :
    G.univCechKoszulAugmentation x = 0 ↔
      ∃ y, y ∈ G.univCechKoszulPiece 1 ∧ G.univCechKoszulDifferential y = x.val := by
  have hx := x.property
  have hx' := (G.univCechKoszulEquiv_mem_piece 0 _).mpr hx.1
  have hDx' : G.incTotalDifferential (G.univCechKoszulEquiv x.val) = 0 := by
    rw [← univCechKoszulEquiv_differential, LinearMap.mem_ker.mp hx.2, map_zero]
  have he : G.univCechKoszulAugmentation x = 0 ↔
      G.incTotalTorusAugmentation (G.univCechKoszulEquiv x.val) = 0 := by
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [he, G.incTotalTorusAugmentation_exact _ hx' hDx']
  constructor
  · rintro ⟨y', hy', hDy'⟩
    refine ⟨G.univCechKoszulEquiv.symm y', ?_, ?_⟩
    · apply (G.univCechKoszulEquiv_mem_piece 1 _).mp
      rwa [LinearEquiv.apply_symm_apply]
    · apply G.univCechKoszulEquiv.injective
      rw [univCechKoszulEquiv_differential, LinearEquiv.apply_symm_apply, hDy']
  · rintro ⟨y, hy, hDy⟩
    refine ⟨G.univCechKoszulEquiv y, (G.univCechKoszulEquiv_mem_piece 1 y).mpr hy, ?_⟩
    rw [← univCechKoszulEquiv_differential, hDy]

/-- **`H^0` of the Čech–Koszul total complex of `K_G` is `𝒰_G`.** The degree-zero cycles modulo
the kernel of the augmentation (which is the submodule of boundaries,
`univCechKoszulAugmentation_eq_zero_iff`) are `S_G`-linearly isomorphic to `IncidenceRing`. -/
noncomputable def univCechKoszulH0Equiv :
    (G.univCechKoszulCycles0 ⧸ LinearMap.ker G.univCechKoszulAugmentation) ≃ₗ[IncCoeffRing E]
      G.IncidenceRing :=
  LinearMap.quotKerEquivOfSurjective _ G.univCechKoszulAugmentation_surjective

end Sheaf

end BPFixedPoints.Multigraph
