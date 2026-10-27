import BPFixedPoints.Incidence.IncidenceVertexRelabelStates
import BPFixedPoints.Incidence.IncidenceRelabelResolution

/-!
# Vertex relabelings act on the Koszul–Čech total complex and on the incidence resolution

Let `φ : VertexRelabel G H`. The coefficient ring is unchanged. The relabeling of the total
Koszul–Čech module (`totalVertexPerm`) applies the signed reordering `cechVertexPerm` of product
Čech chains (`CechProductPermutation.lean`) to the Čech chain of every edge set, leaving the edge
sets fixed. It is linear over the coefficient ring and commutes with the actual total
differentials: with the statewise Čech differentials because the twist of `S` in `H` is the
transported twist of `S` in `G`, and with the Koszul perturbation because the edge sections of
`H` are the transported edge sections of `G` and the Koszul removal signs only involve edges.

The composite of the perturbed inclusion of `G`, the total relabeling and the perturbed
projection of `H` (`resolutionVertexPerm`) is a chain map between the actual finite free
resolutions of the two incidence rings over the common coefficient ring. It preserves homological
degrees and lifts the incidence ring isomorphism of `φ` through the augmentations (face
evaluation on the all-zero chart). At the coefficient origin it is the signed relabeling of
states `statePerm`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct IncidencePerturbation ResolutionTools MvPolynomial

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)

/-- The edge-section exponents of `H` are the transported exponents of `G`. -/
theorem incSectionLeft_eq (e : E) (α β : Fin 2) :
    H.incSectionLeft e α β = fun w => G.incSectionLeft e α β (φ.vertex.symm w) := by
  funext w
  unfold incSectionLeft
  simp only [φ.fst_edge, φ.snd_edge, Equiv.eq_symm_apply]

theorem incSectionRight_eq (e : E) (α β : Fin 2) :
    H.incSectionRight e α β = fun w => G.incSectionRight e α β (φ.vertex.symm w) := by
  funext w
  unfold incSectionRight
  simp only [φ.fst_edge, φ.snd_edge, Equiv.eq_symm_apply]

/-- The edge action of `H` on reordered chains is the reordered edge action of `G`. -/
theorem incEdgeAction_cechVertexPerm (e : E) (x : IncCechModule (V := V) (E := E)) :
    H.incEdgeAction e (cechVertexPerm (IncCoeffRing E) φ.vertex x) =
      cechVertexPerm (IncCoeffRing E) φ.vertex (G.incEdgeAction e x) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    cechVertexPerm_multiply, φ.incSectionLeft_eq, φ.incSectionRight_eq]

/-! ## The relabeling of the total Koszul–Čech module -/

/-- The relabeling of total chains: the Čech chain of every edge set is reordered with its
Koszul sign. -/
noncomputable def totalVertexPerm :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] IncTotalModule (V := W) (E := E) :=
  Finsupp.mapRange.linearMap (cechVertexPerm (IncCoeffRing E) φ.vertex).toLinearMap

@[simp] theorem totalVertexPerm_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalVertexPerm (single S x) = single S (cechVertexPerm (IncCoeffRing E) φ.vertex x) := by
  simp [totalVertexPerm]

theorem totalVertexPerm_apply (z : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    φ.totalVertexPerm z S = cechVertexPerm (IncCoeffRing E) φ.vertex (z S) := by
  simp [totalVertexPerm]

/-- The relabeling commutes with the statewise Čech differentials. -/
theorem totalVertexPerm_cech (z : IncTotalModule (V := V) (E := E)) :
    φ.totalVertexPerm (G.incCechContraction.d z) = H.incCechContraction.d (φ.totalVertexPerm z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incCechContraction_d, Koszul.diagonal_single, totalVertexPerm_single,
      totalVertexPerm_single, H.incCechContraction_d, Koszul.diagonal_single, φ.deg_eq S,
      cechVertexPerm_d]

/-- The relabeling commutes with the Koszul perturbation. -/
theorem totalVertexPerm_koszul (z : IncTotalModule (V := V) (E := E)) :
    φ.totalVertexPerm (G.incKoszulPerturbation z) =
      H.incKoszulPerturbation (φ.totalVertexPerm z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incKoszulPerturbation_single, map_sum, totalVertexPerm_single,
      H.incKoszulPerturbation_single]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [totalVertexPerm_single, φ.deg_eq (S.erase e), cechVertexPerm_sign, map_smul,
      φ.incEdgeAction_cechVertexPerm]

/-- The relabeling commutes with the actual total differentials. -/
theorem totalVertexPerm_differential (z : IncTotalModule (V := V) (E := E)) :
    φ.totalVertexPerm (G.incTotalDifferential z) =
      H.incTotalDifferential (φ.totalVertexPerm z) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, totalVertexPerm_cech,
    totalVertexPerm_koszul, incTotalDifferential, LinearMap.add_apply]

/-- Reordering preserves supports by Čech degree. -/
theorem cechVertexPerm_mem_supported {m : ℤ} {c : IncCechModule (V := V) (E := E)}
    (hc : c ∈ supported (IncCoeffRing E) (IncCoeffRing E) {b | (cechDegree b : ℤ) = m}) :
    cechVertexPerm (IncCoeffRing E) φ.vertex c ∈
      supported (IncCoeffRing E) (IncCoeffRing E) {b | (cechDegree b : ℤ) = m} := by
  rw [mem_supported'] at hc ⊢
  intro b hb
  rw [cechVertexPerm_apply_apply, hc, mul_zero]
  intro hb'
  apply hb
  have h := cechDegree_comp φ.vertex (fun v => b (φ.vertex v))
  simp only [Equiv.apply_symm_apply] at h
  change ((cechDegree b : ℕ) : ℤ) = m
  rw [h]
  exact hb'

/-- The relabeling preserves total degrees. -/
theorem totalVertexPerm_mem_incTotalPiece {n : ℤ} {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ incTotalPiece (V := V) (E := E) n) :
    φ.totalVertexPerm z ∈ incTotalPiece (V := W) (E := E) n := by
  intro S
  rw [totalVertexPerm_apply]
  exact φ.cechVertexPerm_mem_supported (hz S)

/-- Included states, relabeled and projected, are the signed relabeling of the states. -/
theorem incCechContraction_p_totalVertexPerm_i (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incCechContraction.p (φ.totalVertexPerm (G.incCechContraction.i x)) =
      φ.statePerm (IncCoeffRing E) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [← G.incStateEmbed_single (IncCoeffRing E) S κ r, ← G.incCechContractionOver_incCoeffRing,
      G.incCechContractionOver_i_embed, totalVertexPerm_single, cechVertexPerm_i,
      ← H.incCechContractionOver_incCoeffRing, H.incCechContractionOver_p_single,
      ← castH_contraction_p (IncCoeffRing E) (φ.deg_eq S).symm, contraction_p_i,
      statePerm_incStateEmbed]

/-! ## Face evaluation on the all-zero chart -/

/-- The torus isomorphism carries the face vertex units of `G` on the all-zero face to those of
`H` at the image vertices. -/
theorem units_map_incFaceVertexUnit_zero (v : V) :
    Units.map (φ.torusEquiv : G.IncTorusRing →* H.IncTorusRing) (G.incFaceVertexUnit 0 v) =
      H.incFaceVertexUnit 0 (φ.vertex v) := by
  apply Units.ext
  rw [Units.coe_map, incFaceVertexUnit_val, incFaceVertexUnit_val]
  exact φ.torusEquiv_incChartVal _ (Sum.inl v)

/-- A monomial without overlap factors has no overlap vertices. -/
theorem overlapVertices_embedFace_zero (m : FaceMonoid (0 : V → Fin 3)) :
    overlapVertices (embedFace (0 : V → Fin 3) m) = ∅ := by
  have hdeg := cechDegree_embedFace (0 : V → Fin 3) m
  have hz : faceDegree (0 : V → Fin 3) = 0 := by simp [faceDegree]
  rw [hz, cechDegree, Finset.sum_eq_zero_iff] at hdeg
  ext v
  simp only [mem_overlapVertices, Finset.notMem_empty, iff_false]
  rw [hdeg v (Finset.mem_univ v)]
  simp

/-- Face evaluation of reordered Čech chains on the all-zero face is the torus image of face
evaluation. -/
theorem incFaceAmbientToTorus_cechVertexPerm (c : IncCechModule (V := V) (E := E)) :
    H.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (cechVertexPerm (IncCoeffRing E) φ.vertex c) 0) =
      φ.torusEquiv (G.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E) c 0)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, map_add, hx, hy,
      map_add, Pi.add_apply, map_add, map_add]
  | single b r =>
    obtain ⟨⟨q', m⟩, rfl⟩ := CechProduct.faceBasisEquiv.symm.surjective b
    have hb : CechProduct.faceBasisEquiv.symm ⟨q', m⟩ = embedFace q' m := rfl
    rw [hb, cechVertexPerm_single]
    have hperm : (fun w => embedFace q' m (φ.vertex.symm w)) =
        embedFace (fun w => q' (φ.vertex.symm w)) (fun w => m (φ.vertex.symm w)) := rfl
    rw [hperm]
    have hr : ∀ {X : Type} [Fintype X] (q : X → Fin 3) (n : FaceMonoid q) (s : IncCoeffRing E),
        (single (embedFace q n) s : IncCechModule (V := X) (E := E)) =
          s • single (embedFace q n) (1 : IncCoeffRing E) := by
      intro X _ q n s
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hr _ _ (vertexPermSign (IncCoeffRing E) φ.vertex (overlapVertices (embedFace q' m)) * r),
      hr q' m r, H.incFaceEval_smul, G.incFaceEval_smul, map_mul φ.torusEquiv,
      torusEquiv_incTorusCoeffHom, incFaceAmbientToTorus_single_one,
      incFaceAmbientToTorus_single_one]
    by_cases h : q' = 0
    · subst h
      have h0 : (fun w => (0 : V → Fin 3) (φ.vertex.symm w)) = (0 : W → Fin 3) := rfl
      rw [dite_eq_left h0, dite_eq_left rfl, overlapVertices_embedFace_zero, vertexPermSign_empty,
        one_mul]
      congr 1
      rw [faceEvaluate_single, faceEvaluate_single, one_smul, one_smul]
      have key : ∀ u : G.IncTorusRingˣ, φ.torusEquiv (u : G.IncTorusRing) =
          ((Units.map (φ.torusEquiv : G.IncTorusRing →* H.IncTorusRing) u : H.IncTorusRingˣ) :
            H.IncTorusRing) := fun u => rfl
      rw [key, IncidenceLaurent.unitMonomial_map]
      congr 1
      change (∏ w, H.incFaceVertexUnit 0 w ^ faceToInt 0 (fun w => m (φ.vertex.symm w)) w) =
        ∏ v, Units.map (φ.torusEquiv : G.IncTorusRing →* H.IncTorusRing)
          (G.incFaceVertexUnit 0 v) ^ faceToInt 0 m v
      simp only [units_map_incFaceVertexUnit_zero]
      refine (Fintype.prod_equiv φ.vertex _ _ fun v => ?_).symm
      have hface : faceToInt 0 (fun w => m (φ.vertex.symm w)) (φ.vertex v) = faceToInt 0 m v := by
        change exponentToInt _ (m (φ.vertex.symm (φ.vertex v))) = exponentToInt _ (m v)
        rw [Equiv.symm_apply_apply]
      rw [hface]
    · have h' : (fun w => q' (φ.vertex.symm w)) ≠ 0 := by
        intro h'
        apply h
        funext v
        have hv := congrFun h' (φ.vertex v)
        simpa using hv
      rw [dite_eq_right h, dite_eq_right h', map_zero, mul_zero, mul_zero]

/-- Face evaluation of relabeled total chains is the torus image of face evaluation. -/
theorem incFaceRawEval_totalVertexPerm (z : IncTotalModule (V := V) (E := E)) :
    H.incFaceRawEval 0 (φ.totalVertexPerm z) = φ.torusEquiv (G.incFaceRawEval 0 z) := by
  rw [incFaceRawEval_apply, incFaceRawEval_apply, totalVertexPerm_apply,
    incFaceAmbientToTorus_cechVertexPerm]

/-! ## The relabeling chain map of the actual free resolutions -/

/-- The relabeling of the finite free resolution modules: the perturbed inclusion of `G`, the
relabeling of total chains, and the perturbed projection of `H`. -/
noncomputable def resolutionVertexPerm :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
      (H.IncResolutionBasis →₀ IncCoeffRing E) :=
  H.incResolutionProjection.comp (φ.totalVertexPerm.comp G.incResolutionInclusion)

theorem resolutionVertexPerm_apply (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    φ.resolutionVertexPerm x =
      H.incResolutionProjection (φ.totalVertexPerm (G.incResolutionInclusion x)) := rfl

/-- The resolution relabeling is a chain map. -/
theorem resolutionVertexPerm_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incResolutionDifferential (φ.resolutionVertexPerm x) =
      φ.resolutionVertexPerm (G.incResolutionDifferential x) := by
  rw [resolutionVertexPerm_apply, resolutionVertexPerm_apply,
    ← LinearMap.comp_apply H.incResolutionDifferential H.incResolutionProjection,
    ← H.incResolutionProjection_chain, LinearMap.comp_apply, ← totalVertexPerm_differential,
    ← LinearMap.comp_apply G.incTotalDifferential G.incResolutionInclusion,
    G.incResolutionInclusion_chain, LinearMap.comp_apply]

/-- The resolution relabeling preserves homological degrees. -/
theorem resolutionVertexPerm_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    φ.resolutionVertexPerm x ∈ gradedPiece (IncCoeffRing E) H.incResolutionDegree n :=
  H.incResolutionProjection_degree n _
    (φ.totalVertexPerm_mem_incTotalPiece (G.incResolutionInclusion_degree n x hx))

/-- In degree zero the resolution relabeling lifts the torus isomorphism through the
augmentations. -/
theorem resolutionVertexPerm_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    H.incResolutionTorusAugmentation (φ.resolutionVertexPerm x) =
      φ.torusEquiv (G.incResolutionTorusAugmentation x) := by
  have hcycle : H.incTotalDifferential (φ.totalVertexPerm (G.incResolutionInclusion x)) = 0 := by
    rw [← totalVertexPerm_differential,
      show G.incTotalDifferential (G.incResolutionInclusion x) =
        G.incResolutionInclusion (G.incResolutionDifferential x) from
          LinearMap.congr_fun G.incResolutionInclusion_chain x,
      G.incResolutionDifferential_zero_degree x hx, map_zero, map_zero]
  change H.incFaceRawEval 0 (H.incResolutionInclusion (φ.resolutionVertexPerm x)) =
    φ.torusEquiv (G.incFaceRawEval 0 (G.incResolutionInclusion x))
  rw [resolutionVertexPerm_apply, H.incFaceRawEval_inclusion_projection hcycle,
    incFaceRawEval_totalVertexPerm]

/-- At the coefficient origin the resolution relabeling is the signed relabeling of states. -/
theorem mapRange_resolutionVertexPerm (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) (φ.resolutionVertexPerm x) =
      φ.statePerm ℂ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x) := by
  have hI : G.incResolutionInclusion x - G.incCechContraction.i x ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have ha : H.incResolutionProjection (φ.totalVertexPerm (G.incResolutionInclusion x)) -
      H.incCechContraction.p (φ.totalVertexPerm (G.incResolutionInclusion x)) ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    H.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E)
      H.incKoszulPerturbation H.incKoszulPerturbation_mem_augmentation
      (φ.totalVertexPerm (G.incResolutionInclusion x))
  have hb := map_mem_ideal_smul_top (incCoeffAugmentationIdeal E)
    (H.incCechContraction.p.comp φ.totalVertexPerm) hI
  rw [map_sub (H.incCechContraction.p.comp φ.totalVertexPerm)] at hb
  simp only [LinearMap.comp_apply] at hb
  have hsum := Submodule.add_mem _ ha hb
  rw [sub_add_sub_cancel] at hsum
  have h0 := EdgeRelabel.mapRange_constantCoeff_eq_zero hsum
  rw [mapRange_sub (map_sub _), sub_eq_zero] at h0
  rw [resolutionVertexPerm_apply, h0, incCechContraction_p_totalVertexPerm_i,
    ← statePerm_mapRange]

/-- The resolution relabeling on one homological term of the actual free resolutions. -/
noncomputable def freeTermVertexPerm (n : ℕ) :
    G.IncFreeTerm n →ₗ[IncCoeffRing E] H.IncFreeTerm n where
  toFun x := ⟨φ.resolutionVertexPerm x.val, φ.resolutionVertexPerm_degree n x.property⟩
  map_add' x y := Subtype.ext (map_add φ.resolutionVertexPerm x.val y.val)
  map_smul' r x := Subtype.ext (map_smul φ.resolutionVertexPerm r x.val)

@[simp] theorem freeTermVertexPerm_val (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.freeTermVertexPerm n x).val = φ.resolutionVertexPerm x.val := rfl

/-- The termwise relabeling commutes with the differentials of the actual free resolutions. -/
theorem freeTermVertexPerm_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.freeTermVertexPerm (n + 1) x) =
      φ.freeTermVertexPerm n (G.incFreeTermDifferential n x) := by
  apply Subtype.ext
  exact φ.resolutionVertexPerm_differential x.val

/-- In degree zero the termwise relabeling lifts the incidence ring isomorphism through the
augmentations. -/
theorem freeTermVertexPerm_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.freeTermVertexPerm 0 x) =
      φ.incidenceEquiv (G.incResolutionAugmentation x) := by
  apply Subtype.ext
  exact φ.resolutionVertexPerm_torusAugmentation x.property

end VertexRelabel

end BPFixedPoints.Multigraph
