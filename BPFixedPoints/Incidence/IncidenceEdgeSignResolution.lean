import BPFixedPoints.Incidence.IncidenceEdgeSignStates
import BPFixedPoints.Incidence.IncidenceRelabelResolution

/-!
# Edge signs act on the Koszul–Čech total complex and on the incidence resolution

Let `ε` be an edge sign and `τ = edgeSignCoeff ε` the coefficient sign change. The sign change of
total chains (`edgeSignTotal`) replaces every Koszul generator `e` by `ε_e e`: the Čech chain `x`
of an edge set `S` goes to `(∏_{e ∈ S} ε_e) · τ x` at the same edge set. It is `τ`-semilinear and
commutes with the actual total differentials of `G`: with the statewise Čech differentials because
they have integer coefficients, and with the Koszul perturbation because the coefficients of the
edge section of `e` change by `ε_e` under `τ` (`mapRange_incEdgeAction_edgeSign`) and
`∏_{S} ε = ε_e ∏_{S∖e} ε`.

The composite of the perturbed inclusion, the total sign change and the perturbed projection
(`edgeSignResolution`) is a `τ`-semilinear chain map of the actual finite free resolution of the
incidence ring to itself. It preserves homological degrees, lifts the incidence ring automorphism
`edgeSignIncidence` through the augmentation, and at the coefficient origin it is the edge-sign
scaling of states (`mapRange_edgeSignResolution`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct IncidencePerturbation ResolutionTools MvPolynomial

/-- The coefficient sign change as a ring homomorphism. -/
noncomputable def edgeSignCoeffHom {E : Type} (ε : EdgeSign E) : IncCoeffRing E →+* IncCoeffRing E :=
  (edgeSignCoeff ε).toAlgHom.toRingHom

@[simp] theorem edgeSignCoeffHom_apply {E : Type} (ε : EdgeSign E) (p : IncCoeffRing E) :
    edgeSignCoeffHom ε p = edgeSignCoeff ε p := rfl

/-- The coefficient sign change is compatible with the coefficient origin. -/
theorem constantCoeff_comp_edgeSignCoeffHom {E : Type} (ε : EdgeSign E) :
    (constantCoeff : IncCoeffRing E →+* ℂ).comp (edgeSignCoeffHom ε) = constantCoeff := by
  ext p
  · exact constantCoeff_edgeSignCoeff ε (C p)
  · exact constantCoeff_edgeSignCoeff ε (X _)

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (ε : EdgeSign E)

/-- Under the coefficient sign change the edge section action of `e` changes by the sign of `e`. -/
theorem mapRange_incEdgeAction_edgeSign (e : E) (x : IncCechModule (V := V) (E := E)) :
    mapRange (edgeSignCoeffHom ε) (map_zero _) (G.incEdgeAction e x) =
      ((ε e : ℤ) : IncCoeffRing E) •
        G.incEdgeAction e (mapRange (edgeSignCoeffHom ε) (map_zero _) x) := by
  have hsum : ∀ y : IncCechModule (V := V) (E := E),
      G.incEdgeAction e y = ∑ ab : Fin 2 × Fin 2,
        (X (e, ab) : IncCoeffRing E) • multiply (IncCoeffRing E)
          (G.incSectionLeft e ab.1 ab.2) (G.incSectionRight e ab.1 ab.2) y := by
    intro y
    rw [Fintype.sum_prod_type]
    simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hsum, hsum, mapRange_finsetSum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [mapRange_ring_smul, multiply_mapRange, edgeSignCoeffHom_apply, edgeSignCoeff_X, mul_smul]

/-! ## The sign change of the total Koszul–Čech module -/

/-- The sign change of total chains, as an additive map. -/
noncomputable def edgeSignTotalAdd :
    IncTotalModule (V := V) (E := E) →+ IncTotalModule (V := V) (E := E) :=
  Finsupp.liftAddHom fun S =>
    (Finsupp.singleAddHom S).comp
      ((DistribSMul.toAddMonoidHom (IncCechModule (V := V) (E := E))
          (ε.setSign (IncCoeffRing E) S)).comp
        (Finsupp.mapRange.addMonoidHom (edgeSignCoeffHom ε).toAddMonoidHom))

theorem edgeSignTotalAdd_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    edgeSignTotalAdd ε (single S x) =
      single S (ε.setSign (IncCoeffRing E) S • mapRange (edgeSignCoeffHom ε) (map_zero _) x) := by
  simp [edgeSignTotalAdd]

/-- The sign change of total chains: every Koszul generator `e` goes to `ε_e e`, so the chain of an
edge set `S` is multiplied by `∏_{e ∈ S} ε_e`, and coefficients change by the coefficient sign
change. It is semilinear for the coefficient sign change. -/
noncomputable def edgeSignTotal :
    IncTotalModule (V := V) (E := E) →ₛₗ[edgeSignCoeffHom ε] IncTotalModule (V := V) (E := E) where
  toFun := edgeSignTotalAdd ε
  map_add' := map_add _
  map_smul' r z := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]
    | single S x =>
      rw [smul_single, edgeSignTotalAdd_single, edgeSignTotalAdd_single, smul_single,
        mapRange_ring_smul, smul_comm]

@[simp] theorem edgeSignTotal_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    edgeSignTotal ε (single S x) =
      single S (ε.setSign (IncCoeffRing E) S • mapRange (edgeSignCoeffHom ε) (map_zero _) x) :=
  edgeSignTotalAdd_single ε S x

/-- The component of a sign-changed chain at an edge set. -/
theorem edgeSignTotal_apply (z : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    edgeSignTotal ε z S =
      ε.setSign (IncCoeffRing E) S • mapRange (edgeSignCoeffHom ε) (map_zero _) (z S) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, Finsupp.add_apply, hz, hw, Finsupp.add_apply,
      mapRange_add (map_add _), smul_add]
  | single T x =>
    rw [edgeSignTotal_single]
    by_cases h : T = S
    · subst h
      simp
    · rw [single_eq_of_ne (Ne.symm h), single_eq_of_ne (Ne.symm h)]
      simp

/-- The sign change commutes with the statewise Čech differentials. -/
theorem edgeSignTotal_cech (z : IncTotalModule (V := V) (E := E)) :
    edgeSignTotal ε (G.incCechContraction.d z) = G.incCechContraction.d (edgeSignTotal ε z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incCechContraction_d, Koszul.diagonal_single, edgeSignTotal_single, edgeSignTotal_single,
      Koszul.diagonal_single, map_smul, contraction_d_mapRange]

/-- The sign change commutes with the Koszul perturbation. -/
theorem edgeSignTotal_koszul (z : IncTotalModule (V := V) (E := E)) :
    edgeSignTotal ε (G.incKoszulPerturbation z) = G.incKoszulPerturbation (edgeSignTotal ε z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incKoszulPerturbation_single, map_sum, edgeSignTotal_single,
      G.incKoszulPerturbation_single]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [edgeSignTotal_single]
    congr 1
    rw [← contraction_sign_mapRange, mapRange_ring_smul, mapRange_incEdgeAction_edgeSign]
    simp only [map_smul, smul_smul]
    congr 1
    have hk : edgeSignCoeffHom ε (Koszul.sign (A := IncCoeffRing E) S e) =
        Koszul.sign (A := IncCoeffRing E) S e := by
      simp [Koszul.sign]
    rw [hk, ← ε.setSign_erase_mul (IncCoeffRing E) he]
    ring

/-- The sign change commutes with the actual total differentials. -/
theorem edgeSignTotal_differential (z : IncTotalModule (V := V) (E := E)) :
    edgeSignTotal ε (G.incTotalDifferential z) = G.incTotalDifferential (edgeSignTotal ε z) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, edgeSignTotal_cech, edgeSignTotal_koszul,
    LinearMap.add_apply]

/-- The sign change preserves total degrees. -/
theorem edgeSignTotal_mem_incTotalPiece {n : ℤ} {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ incTotalPiece (V := V) (E := E) n) :
    edgeSignTotal ε z ∈ incTotalPiece (V := V) (E := E) n := by
  intro T
  rw [edgeSignTotal_apply]
  apply Submodule.smul_mem
  rw [mem_supported]
  intro b hb
  exact (mem_supported _ _).mp (hz T) (support_mapRange hb)

/-- The sign change preserves the coefficient-origin ideal multiple. -/
theorem edgeSignTotal_mem_ideal {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ RingHom.ker (constantCoeff : IncCoeffRing E →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E)))) :
    edgeSignTotal ε z ∈ RingHom.ker (constantCoeff : IncCoeffRing E →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E))) := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    rw [LinearMap.map_smulₛₗ]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [RingHom.mem_ker] at hr ⊢
    rw [edgeSignCoeffHom_apply, constantCoeff_edgeSignCoeff, hr]
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Included states, sign-changed and projected, are the edge-sign scaling of the coefficientwise
sign-changed states. -/
theorem incCechContraction_p_edgeSignTotal_i (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incCechContraction.p (edgeSignTotal ε (G.incCechContraction.i x)) =
      G.edgeSignState ε (IncCoeffRing E) (mapRange (edgeSignCoeffHom ε) (map_zero _) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, mapRange_add (map_add _), map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [mapRange_single, edgeSignState_single]
    rw [← G.incStateEmbed_single (IncCoeffRing E) S κ r, ← G.incCechContractionOver_incCoeffRing,
      G.incCechContractionOver_i_embed, edgeSignTotal_single, ← contraction_i_mapRange,
      G.incCechContractionOver_p_single, map_smul, contraction_p_i, mapRange_single, map_smul,
      incStateEmbed_single, smul_single, smul_eq_mul]

/-! ## Face evaluation -/

/-- The torus sign change fixes the face vertex units. -/
theorem units_map_incFaceVertexUnit_edgeSign (q : V → Fin 3) (v : V) :
    Units.map (G.edgeSignTorus ε : G.IncTorusRing →* G.IncTorusRing) (G.incFaceVertexUnit q v) =
      G.incFaceVertexUnit q v := by
  apply Units.ext
  rw [Units.coe_map, incFaceVertexUnit_val]
  change G.edgeSignTorus ε (G.incChartVal _ (Sum.inl v)) = _
  rw [edgeSignTorus_incChartVal, EdgeSign.chartVarSign_inl, Units.val_one, Int.cast_one, one_mul]

/-- The torus sign change fixes face evaluation at the face vertex units. -/
theorem edgeSignTorus_faceEvaluate (q : V → Fin 3) (f : CechProduct.FaceRing ℂ q) :
    G.edgeSignTorus ε (faceEvaluate q (G.incFaceVertexUnit q) f) =
      faceEvaluate q (G.incFaceVertexUnit q) f := by
  have h : (G.edgeSignTorus ε).toAlgHom.comp (faceEvaluate q (G.incFaceVertexUnit q)) =
      faceEvaluate q (G.incFaceVertexUnit q) := by
    apply AddMonoidAlgebra.algHom_ext
    swap
    · exact Subsingleton.elim _ _
    intro m
    change G.edgeSignTorus ε (faceEvaluate q (G.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)) =
      faceEvaluate q (G.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)
    rw [faceEvaluate_single, one_smul]
    have key : ∀ u : G.IncTorusRingˣ, G.edgeSignTorus ε (u : G.IncTorusRing) =
        ((Units.map (G.edgeSignTorus ε : G.IncTorusRing →* G.IncTorusRing) u : G.IncTorusRingˣ) :
          G.IncTorusRing) := fun u => rfl
    rw [key]
    congr 1
    simp only [IncidenceLaurent.unitMonomial, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow,
      units_map_incFaceVertexUnit_edgeSign]
  exact AlgHom.congr_fun h f

/-- Face evaluation of coefficientwise sign-changed Čech chains is the torus sign change of face
evaluation. -/
theorem incFaceAmbientToTorus_mapRange_edgeSign (q : V → Fin 3)
    (c : IncCechModule (V := V) (E := E)) :
    G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (mapRange (edgeSignCoeffHom ε) (map_zero _) c) q) =
      G.edgeSignTorus ε (G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) c q)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapRange_add (map_add _), map_add, Pi.add_apply, map_add, hx, hy,
      map_add, Pi.add_apply, map_add, map_add]
  | single b r =>
    obtain ⟨⟨q', m⟩, rfl⟩ := CechProduct.faceBasisEquiv.symm.surjective b
    have hb : CechProduct.faceBasisEquiv.symm ⟨q', m⟩ = embedFace q' m := rfl
    rw [hb, mapRange_single]
    have hr : ∀ s : IncCoeffRing E,
        (single (embedFace q' m) s : IncCechModule (V := V) (E := E)) =
          s • single (embedFace q' m) (1 : IncCoeffRing E) := by
      intro s
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hr (edgeSignCoeffHom ε r), hr r, G.incFaceEval_smul, G.incFaceEval_smul, map_mul,
      edgeSignTorus_incTorusCoeffHom, edgeSignCoeffHom_apply, incFaceAmbientToTorus_single_one]
    congr 1
    split_ifs with h
    · exact (G.edgeSignTorus_faceEvaluate ε q _).symm
    · exact (map_zero _).symm

/-- Face evaluation of sign-changed total chains is the torus sign change of face evaluation. -/
theorem incFaceRawEval_edgeSignTotal (q : V → Fin 3) (z : IncTotalModule (V := V) (E := E)) :
    G.incFaceRawEval q (edgeSignTotal ε z) = G.edgeSignTorus ε (G.incFaceRawEval q z) := by
  rw [incFaceRawEval_apply, incFaceRawEval_apply, edgeSignTotal_apply, EdgeSign.setSign_empty,
    one_smul, incFaceAmbientToTorus_mapRange_edgeSign]

/-! ## The sign-change chain map of the actual free resolution -/

/-- The sign change of the finite free resolution modules: the perturbed inclusion, the sign change
of total chains, and the perturbed projection. -/
noncomputable def edgeSignResolution :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₛₗ[edgeSignCoeffHom ε]
      (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  G.incResolutionProjection.comp ((edgeSignTotal ε).comp G.incResolutionInclusion)

theorem edgeSignResolution_apply (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.edgeSignResolution ε x =
      G.incResolutionProjection (edgeSignTotal ε (G.incResolutionInclusion x)) := rfl

/-- The resolution sign change is a chain map. -/
theorem edgeSignResolution_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incResolutionDifferential (G.edgeSignResolution ε x) =
      G.edgeSignResolution ε (G.incResolutionDifferential x) := by
  rw [edgeSignResolution_apply, edgeSignResolution_apply,
    ← LinearMap.comp_apply G.incResolutionDifferential G.incResolutionProjection,
    ← G.incResolutionProjection_chain, LinearMap.comp_apply, ← edgeSignTotal_differential,
    ← LinearMap.comp_apply G.incTotalDifferential G.incResolutionInclusion,
    G.incResolutionInclusion_chain, LinearMap.comp_apply]

/-- The resolution sign change preserves homological degrees. -/
theorem edgeSignResolution_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    G.edgeSignResolution ε x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n :=
  G.incResolutionProjection_degree n _
    (edgeSignTotal_mem_incTotalPiece ε (G.incResolutionInclusion_degree n x hx))

/-- In degree zero the resolution sign change lifts the torus sign change through the
augmentation. -/
theorem edgeSignResolution_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incResolutionTorusAugmentation (G.edgeSignResolution ε x) =
      G.edgeSignTorus ε (G.incResolutionTorusAugmentation x) := by
  have hcycle : G.incTotalDifferential (edgeSignTotal ε (G.incResolutionInclusion x)) = 0 := by
    rw [← edgeSignTotal_differential,
      show G.incTotalDifferential (G.incResolutionInclusion x) =
        G.incResolutionInclusion (G.incResolutionDifferential x) from
          LinearMap.congr_fun G.incResolutionInclusion_chain x,
      G.incResolutionDifferential_zero_degree x hx, map_zero, map_zero]
  change G.incFaceRawEval 0 (G.incResolutionInclusion (G.edgeSignResolution ε x)) =
    G.edgeSignTorus ε (G.incFaceRawEval 0 (G.incResolutionInclusion x))
  rw [edgeSignResolution_apply, G.incFaceRawEval_inclusion_projection hcycle,
    incFaceRawEval_edgeSignTotal]

/-- At the coefficient origin the resolution sign change is the edge-sign scaling of states. -/
theorem mapRange_edgeSignResolution (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) (G.edgeSignResolution ε x) =
      G.edgeSignState ε ℂ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x) := by
  have hI : G.incResolutionInclusion x - G.incCechContraction.i x ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have ha : G.incResolutionProjection (edgeSignTotal ε (G.incResolutionInclusion x)) -
      G.incCechContraction.p (edgeSignTotal ε (G.incResolutionInclusion x)) ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation
      (edgeSignTotal ε (G.incResolutionInclusion x))
  have hb := map_mem_ideal_smul_top (incCoeffAugmentationIdeal E) G.incCechContraction.p
    (edgeSignTotal_mem_ideal ε hI)
  rw [map_sub (edgeSignTotal ε), map_sub G.incCechContraction.p] at hb
  have hsum := Submodule.add_mem _ ha hb
  rw [sub_add_sub_cancel] at hsum
  have h0 := EdgeRelabel.mapRange_constantCoeff_eq_zero hsum
  rw [mapRange_sub (map_sub _), sub_eq_zero] at h0
  rw [edgeSignResolution_apply, h0, incCechContraction_p_edgeSignTotal_i, ← edgeSignState_mapRange]
  congr 1
  ext b
  simp only [mapRange_apply]
  exact RingHom.congr_fun (constantCoeff_comp_edgeSignCoeffHom ε) (x b)

/-- The resolution sign change on one homological term of the actual free resolution. -/
noncomputable def edgeSignFreeTerm (n : ℕ) :
    G.IncFreeTerm n →ₛₗ[edgeSignCoeffHom ε] G.IncFreeTerm n where
  toFun x := ⟨G.edgeSignResolution ε x.val, G.edgeSignResolution_degree ε n x.property⟩
  map_add' x y := Subtype.ext (map_add (G.edgeSignResolution ε) x.val y.val)
  map_smul' r x := Subtype.ext (LinearMap.map_smulₛₗ (G.edgeSignResolution ε) r x.val)

@[simp] theorem edgeSignFreeTerm_val (n : ℕ) (x : G.IncFreeTerm n) :
    (G.edgeSignFreeTerm ε n x).val = G.edgeSignResolution ε x.val := rfl

/-- The termwise sign change commutes with the differentials of the actual free resolution. -/
theorem edgeSignFreeTerm_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    G.incFreeTermDifferential n (G.edgeSignFreeTerm ε (n + 1) x) =
      G.edgeSignFreeTerm ε n (G.incFreeTermDifferential n x) := by
  apply Subtype.ext
  exact G.edgeSignResolution_differential ε x.val

/-- In degree zero the termwise sign change lifts the incidence ring automorphism through the
augmentation. -/
theorem edgeSignFreeTerm_augmentation (x : G.IncFreeTerm 0) :
    G.incResolutionAugmentation (G.edgeSignFreeTerm ε 0 x) =
      G.edgeSignIncidence ε (G.incResolutionAugmentation x) := by
  apply Subtype.ext
  exact G.edgeSignResolution_torusAugmentation ε x.property

end BPFixedPoints.Multigraph
