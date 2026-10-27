import BPFixedPoints.Incidence.IncidenceRelabelResolution
import BPFixedPoints.Incidence.IncidenceEdgeMapRings

/-!
# Edge maps act on the Koszul–Čech total complex and on the incidence resolution

Let `φ : EdgeMap G H` and write `ρ` for the coefficient ring homomorphism. The total
Koszul–Čech map (`totalMap`, the map `T_φ` of the paper) sends the Čech chain `x` of an edge set
`S` to `wedgeSign S` times the coefficientwise image `ρ x`, placed at the image edge set: the
Koszul generator of `e` goes to the generator of `φ e`, so the exterior part is the exterior map of
`EdgeMap.exteriorMap`, which is zero on edge sets where the edge function is not injective. The map
is `ρ`-semilinear and commutes with the actual total differentials:

* with the statewise Čech differentials, because the twists of `S` and `φ S` agree whenever the
  wedge sign of `S` is nonzero and the Čech structure maps have integer coefficients;
* with the Koszul perturbation, because the edge sections of `e` and `φ e` agree after renaming the
  coefficients, the Čech parity does not depend on the twist, and the contraction by an edge `e'`
  of `H` corresponds to the sum of the contractions by the edges above `e'`
  (`EdgeMap.sum_fiber_wedgeSign`). When two edges of `S` have the same image their two terms cancel.

The composite `F_φ` of the perturbed inclusion of `G`, the total map and the perturbed projection of
`H` (`resolutionMap`) is a `ρ`-semilinear chain map between the actual finite free resolutions of
the two incidence rings (`resolutionMap_differential`). It preserves homological degrees and lifts
the incidence ring homomorphism through the augmentations (`freeTermMap_augmentation`). At the
coefficient origin it is the state map of `φ` (`mapRange_resolutionMap`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type) [CommRing R] {V : Type} [Fintype V]

/-- The Čech parity does not depend on the twist. -/
theorem contraction_sign_eq (d d' : V → ℕ) :
    (contraction R d).sign = (contraction R d').sign := by
  apply Finsupp.lhom_ext
  intro b r
  rw [contraction_sign_single, contraction_sign_single]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct IncidencePerturbation ResolutionTools MvPolynomial

namespace EdgeMap

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeMap G H)

/-- The edge sections of an image edge are those of the original edge, with exchanged endpoint
indices for a reversed edge. -/
theorem incSectionLeft_edgeMap (e : E) (ab : Fin 2 × Fin 2) :
    H.incSectionLeft (φ.edge e) (φ.endpointIndex e ab).1 (φ.endpointIndex e ab).2 =
      G.incSectionLeft e ab.1 ab.2 := by
  funext v
  unfold incSectionLeft endpointIndex
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · simp
  · simp only [ite_true, Prod.fst_swap, Prod.snd_swap]
    omega

/-- The right edge sections of an image edge, as for `incSectionLeft_edgeMap`. -/
theorem incSectionRight_edgeMap (e : E) (ab : Fin 2 × Fin 2) :
    H.incSectionRight (φ.edge e) (φ.endpointIndex e ab).1 (φ.endpointIndex e ab).2 =
      G.incSectionRight e ab.1 ab.2 := by
  funext v
  unfold incSectionRight endpointIndex
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · simp
  · simp only [ite_true, Prod.fst_swap, Prod.snd_swap]
    omega

/-- The edge section action of an image edge on renamed chains is the renamed edge action. -/
theorem incEdgeAction_edgeMap (e : E) (x : IncCechModule (V := V) (E := E)) :
    H.incEdgeAction (φ.edge e) (mapRange φ.coeffRingHom (map_zero _) x) =
      mapRange φ.coeffRingHom (map_zero _) (G.incEdgeAction e x) := by
  have hsum : ∀ (K : Type) [Fintype K] [LinearOrder K] (M : Multigraph V K) (k : K)
      (y : IncCechModule (V := V) (E := K)),
      M.incEdgeAction k y = ∑ ab : Fin 2 × Fin 2,
        (X (k, ab) : IncCoeffRing K) • multiply (IncCoeffRing K)
          (M.incSectionLeft k ab.1 ab.2) (M.incSectionRight k ab.1 ab.2) y := by
    intro K _ _ M k y
    rw [Fintype.sum_prod_type]
    simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hsum, hsum, mapRange_finsetSum, ← (φ.endpointIndexEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun ab _ => ?_
  change (X (φ.edge e, φ.endpointIndex e ab) : IncCoeffRing E') • multiply (IncCoeffRing E')
      (H.incSectionLeft (φ.edge e) (φ.endpointIndex e ab).1 (φ.endpointIndex e ab).2)
      (H.incSectionRight (φ.edge e) (φ.endpointIndex e ab).1 (φ.endpointIndex e ab).2)
      (mapRange φ.coeffRingHom (map_zero _) x) = _
  rw [incSectionLeft_edgeMap, incSectionRight_edgeMap, mapRange_ring_smul, multiply_mapRange,
    coeffRingHom_apply, coeffAlgHom_X, coeffIdxMap_apply]

/-- The coefficient ring homomorphism maps Koszul removal signs to removal signs. -/
@[simp] theorem coeffRingHom_koszulSign (S : Finset E) (e : E) :
    φ.coeffRingHom (Koszul.sign (A := IncCoeffRing E) S e) =
      Koszul.sign (A := IncCoeffRing E') S e := by
  simp [Koszul.sign]

/-! ## The total Koszul–Čech map -/

/-- The total map of total chains, as an additive map. -/
noncomputable def totalMapAdd :
    IncTotalModule (V := V) (E := E) →+ IncTotalModule (V := V) (E := E') :=
  Finsupp.liftAddHom fun S =>
    (Finsupp.singleAddHom (φ.edgeSet S)).comp
      ((DistribSMul.toAddMonoidHom (IncCechModule (V := V) (E := E'))
          ((φ.wedgeSign S : ℤ) : IncCoeffRing E')).comp
        (Finsupp.mapRange.addMonoidHom φ.coeffRingHom.toAddMonoidHom))

theorem totalMapAdd_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalMapAdd (single S x) =
      single (φ.edgeSet S) (((φ.wedgeSign S : ℤ) : IncCoeffRing E') •
        mapRange φ.coeffRingHom (map_zero _) x) := by
  simp [totalMapAdd]

/-- **The total Koszul–Čech map `T_φ`.** The chain of an edge set goes to its wedge sign times
its renamed chain, at the image edge set; in particular it goes to zero when the edge function is
not injective on the edge set. It is semilinear for the coefficient ring homomorphism. -/
noncomputable def totalMap :
    IncTotalModule (V := V) (E := E) →ₛₗ[φ.coeffRingHom] IncTotalModule (V := V) (E := E') where
  toFun := φ.totalMapAdd
  map_add' := map_add _
  map_smul' r z := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]
    | single S x =>
      rw [smul_single, totalMapAdd_single, totalMapAdd_single, smul_single,
        mapRange_ring_smul, smul_comm]

@[simp] theorem totalMap_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalMap (single S x) =
      single (φ.edgeSet S) (((φ.wedgeSign S : ℤ) : IncCoeffRing E') •
        mapRange φ.coeffRingHom (map_zero _) x) :=
  φ.totalMapAdd_single S x

/-- The total map on a chain of an edge set where the edge function is not injective is zero. -/
theorem totalMap_single_of_not_injOn {S : Finset E} (h : ¬ Set.InjOn φ.edge S)
    (x : IncCechModule (V := V) (E := E)) : φ.totalMap (single S x) = 0 := by
  rw [totalMap_single, wedgeSign_of_not_injOn φ h, Int.cast_zero, zero_smul, single_zero]

/-- The empty-edge component of the total map is the renamed empty-edge component. -/
theorem totalMap_apply_empty (z : IncTotalModule (V := V) (E := E)) :
    φ.totalMap z ∅ = mapRange φ.coeffRingHom (map_zero _) (z ∅) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, Finsupp.add_apply, hz, hw, Finsupp.add_apply,
      mapRange_add (map_add _)]
  | single S x =>
    rw [totalMap_single]
    by_cases h : S = ∅
    · subst h
      simp
    · rw [single_eq_of_ne (fun h' => h (φ.edgeSet_eq_empty_iff.mp h'.symm)),
        single_eq_of_ne (fun h' => h h'.symm), mapRange_zero]

/-- The total map commutes with the statewise Čech differentials. -/
theorem totalMap_cech (z : IncTotalModule (V := V) (E := E)) :
    φ.totalMap (G.incCechContraction.d z) = H.incCechContraction.d (φ.totalMap z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incCechContraction_d, Koszul.diagonal_single, totalMap_single, totalMap_single,
      H.incCechContraction_d, Koszul.diagonal_single]
    by_cases h : Set.InjOn φ.edge S
    · rw [φ.deg_edgeSet h, map_smul, contraction_d_mapRange]
    · rw [wedgeSign_of_not_injOn φ h, Int.cast_zero, zero_smul, zero_smul, map_zero]

/-- Placing an integer state vector of `H` against a fixed Čech chain. -/
noncomputable def placeHom (y : IncCechModule (V := V) (E := E')) :
    Koszul.Space E' ℤ →+ IncTotalModule (V := V) (E := E') :=
  Finsupp.mapRange.addMonoidHom
    ((LinearMap.toSpanSingleton (IncCoeffRing E') _ y).toAddMonoidHom.comp
      (Int.castAddHom (IncCoeffRing E')))

/-- Placing a basis vector. -/
theorem placeHom_single (y : IncCechModule (V := V) (E := E')) (U : Finset E') (c : ℤ) :
    placeHom y (single U c) = single U ((c : IncCoeffRing E') • y) := by
  simp [placeHom]

/-- The exterior part of the total map is the exterior map of states: the chain `x` of an edge
set `S` goes to the renamed chain placed against the image under `EdgeMap.exteriorMap` of the
exterior basis vector of `S`, that is, against the wedge of the generators `e_{φ e}`, `e ∈ S`. -/
theorem totalMap_single_eq_placeHom (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalMap (single S x) =
      placeHom (mapRange φ.coeffRingHom (map_zero _) x) (φ.exteriorMap ℤ (single S 1)) := by
  rw [exteriorMap_single, mul_one, Int.cast_id, placeHom_single, totalMap_single]

/-- **The total map commutes with the Koszul perturbation.** -/
theorem totalMap_koszul (z : IncTotalModule (V := V) (E := E)) :
    φ.totalMap (G.incKoszulPerturbation z) = H.incKoszulPerturbation (φ.totalMap z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incKoszulPerturbation_single, map_sum, totalMap_single,
      H.incKoszulPerturbation_single]
    let Y : E' → IncCechModule (V := V) (E := E') := fun e' =>
      (CechProduct.contraction (IncCoeffRing E') (H.deg ((φ.edgeSet S).erase e'))).sign
        (H.incEdgeAction e' (mapRange φ.coeffRingHom (map_zero _) x))
    have hl : ∀ e ∈ S, φ.totalMap (single (S.erase e)
        ((CechProduct.contraction (IncCoeffRing E) (G.deg (S.erase e))).sign
          (Koszul.sign (A := IncCoeffRing E) S e • G.incEdgeAction e x))) =
        placeHom (Y (φ.edge e))
          (single (φ.edgeSet (S.erase e)) (φ.wedgeSign (S.erase e) * Koszul.sign (A := ℤ) S e)) := by
      intro e _
      rw [totalMap_single, placeHom_single, ← contraction_sign_mapRange,
        contraction_sign_eq (IncCoeffRing E') (G.deg (S.erase e))
          (H.deg ((φ.edgeSet S).erase (φ.edge e))),
        mapRange_ring_smul, coeffRingHom_koszulSign, ← incEdgeAction_edgeMap, map_smul,
        smul_smul, ← Koszul.intCast_sign, ← Int.cast_mul]
    have hr : ∀ e' ∈ φ.edgeSet S, single ((φ.edgeSet S).erase e')
        ((CechProduct.contraction (IncCoeffRing E') (H.deg ((φ.edgeSet S).erase e'))).sign
          (Koszul.sign (A := IncCoeffRing E') (φ.edgeSet S) e' •
            H.incEdgeAction e' (((φ.wedgeSign S : ℤ) : IncCoeffRing E') •
              mapRange φ.coeffRingHom (map_zero _) x))) =
        placeHom (Y e')
          (single ((φ.edgeSet S).erase e') (Koszul.sign (A := ℤ) (φ.edgeSet S) e' * φ.wedgeSign S)) := by
      intro e' _
      rw [placeHom_single, map_smul, map_smul, map_smul, smul_smul, ← Koszul.intCast_sign,
        ← Int.cast_mul]
    rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hr,
      ← Finset.sum_fiberwise_of_maps_to (g := φ.edge) (t := φ.edgeSet S)
        (fun e he => φ.mem_edgeSet_of_mem he)]
    refine Finset.sum_congr rfl fun e' he' => ?_
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.mp he).2]), ← map_sum,
      sum_fiber_wedgeSign, ite_eq_left he']

/-- The total map commutes with the actual total differentials. -/
theorem totalMap_differential (z : IncTotalModule (V := V) (E := E)) :
    φ.totalMap (G.incTotalDifferential z) = H.incTotalDifferential (φ.totalMap z) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, totalMap_cech, totalMap_koszul,
    incTotalDifferential, LinearMap.add_apply]

/-- The total map preserves total degrees. -/
theorem totalMap_mem_incTotalPiece {n : ℤ} {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ incTotalPiece (V := V) (E := E) n) :
    φ.totalMap z ∈ incTotalPiece (V := V) (E := E') n := by
  have hsingle : ∀ S, φ.totalMap (single S (z S)) ∈ incTotalPiece (V := V) (E := E') n := by
    intro S U
    rw [totalMap_single]
    by_cases hU : φ.edgeSet S = U
    · subst hU
      rw [single_eq_same]
      by_cases h : Set.InjOn φ.edge S
      · apply Submodule.smul_mem
        rw [mem_supported, φ.card_edgeSet h]
        intro b hb
        exact (mem_supported _ _).mp (hz S) (support_mapRange hb)
      · rw [wedgeSign_of_not_injOn φ h, Int.cast_zero, zero_smul]
        exact Submodule.zero_mem _
    · rw [single_eq_of_ne (Ne.symm hU)]
      exact Submodule.zero_mem _
  rw [← z.sum_single, Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun S _ => hsingle S

/-- The total map sends the coefficient-origin ideal multiple to the coefficient-origin ideal
multiple. -/
theorem totalMap_mem_ideal {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ RingHom.ker (constantCoeff : IncCoeffRing E →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E)))) :
    φ.totalMap z ∈ RingHom.ker (constantCoeff : IncCoeffRing E' →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E') (IncTotalModule (V := V) (E := E'))) := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    rw [LinearMap.map_smulₛₗ]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [RingHom.mem_ker] at hr ⊢
    rw [constantCoeff_coeffRingHom, hr]
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Included states, mapped and projected, are the state map of the renamed states. -/
theorem incCechContraction_p_totalMap_i (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incCechContraction.p (φ.totalMap (G.incCechContraction.i x)) =
      φ.stateMap (IncCoeffRing E') (mapRange φ.coeffRingHom (map_zero _) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, mapRange_add (map_add _), map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [mapRange_single, stateMap_single]
    rw [← G.incStateEmbed_single (IncCoeffRing E) S κ r, ← G.incCechContractionOver_incCoeffRing,
      G.incCechContractionOver_i_embed, totalMap_single]
    split_ifs with h
    · rw [← contraction_i_mapRange, ← H.incCechContractionOver_incCoeffRing,
        H.incCechContractionOver_p_single, map_smul,
        ← castH_contraction_p (IncCoeffRing E') (φ.deg_edgeSet h).symm, contraction_p_i,
        mapRange_single, castH_single, map_smul, incStateEmbed_single, smul_single, smul_eq_mul]
      rfl
    · rw [wedgeSign_of_not_injOn φ h, Int.cast_zero, zero_smul, single_zero, map_zero]

/-! ## Face evaluation -/

/-- The torus homomorphism carries the face vertex units of `G` to those of `H`. -/
theorem units_map_incFaceVertexUnit (q : V → Fin 3) (v : V) :
    Units.map (φ.torusHom : G.IncTorusRing →* H.IncTorusRing) (G.incFaceVertexUnit q v) =
      H.incFaceVertexUnit q v := by
  apply Units.ext
  rw [Units.coe_map, incFaceVertexUnit_val, incFaceVertexUnit_val]
  exact φ.torusHom_incChartVal _ (Sum.inl v)

/-- The torus homomorphism carries face evaluation at the units of `G` to face evaluation at the
units of `H`. -/
theorem torusHom_faceEvaluate (q : V → Fin 3) (f : CechProduct.FaceRing ℂ q) :
    φ.torusHom (faceEvaluate q (G.incFaceVertexUnit q) f) =
      faceEvaluate q (H.incFaceVertexUnit q) f := by
  have h : φ.torusHom.comp (faceEvaluate q (G.incFaceVertexUnit q)) =
      faceEvaluate q (H.incFaceVertexUnit q) := by
    apply AddMonoidAlgebra.algHom_ext
    swap
    · exact Subsingleton.elim _ _
    intro m
    change φ.torusHom (faceEvaluate q (G.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)) =
      faceEvaluate q (H.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)
    rw [faceEvaluate_single, faceEvaluate_single, one_smul, one_smul]
    have key : ∀ u : G.IncTorusRingˣ, φ.torusHom (u : G.IncTorusRing) =
        ((Units.map (φ.torusHom : G.IncTorusRing →* H.IncTorusRing) u : H.IncTorusRingˣ) :
          H.IncTorusRing) := fun u => rfl
    rw [key]
    congr 1
    simp only [IncidenceLaurent.unitMonomial, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow,
      units_map_incFaceVertexUnit]
  exact AlgHom.congr_fun h f

/-- Face evaluation of renamed Čech chains is the torus image of face evaluation. -/
theorem incFaceAmbientToTorus_mapRange (q : V → Fin 3) (c : IncCechModule (V := V) (E := E)) :
    H.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E')
        (mapRange φ.coeffRingHom (map_zero _) c) q) =
      φ.torusHom (G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) c q)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapRange_add (map_add _), map_add, Pi.add_apply, map_add, hx, hy,
      map_add, Pi.add_apply, map_add, map_add]
  | single b r =>
    obtain ⟨⟨q', m⟩, rfl⟩ := CechProduct.faceBasisEquiv.symm.surjective b
    have hb : CechProduct.faceBasisEquiv.symm ⟨q', m⟩ = embedFace q' m := rfl
    rw [hb, mapRange_single]
    have hr : ∀ (K : Type) [Fintype K] [LinearOrder K] (s : IncCoeffRing K),
        (single (embedFace q' m) s : IncCechModule (V := V) (E := K)) =
          s • single (embedFace q' m) (1 : IncCoeffRing K) := by
      intro K _ _ s
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hr E' (φ.coeffRingHom r), hr E r, H.incFaceEval_smul, G.incFaceEval_smul, map_mul,
      torusHom_incTorusCoeffHom, coeffRingHom_apply, incFaceAmbientToTorus_single_one,
      incFaceAmbientToTorus_single_one]
    congr 1
    split_ifs with h
    · exact (φ.torusHom_faceEvaluate q _).symm
    · exact (map_zero _).symm

/-- Face evaluation of mapped total chains is the torus image of face evaluation. -/
theorem incFaceRawEval_totalMap (q : V → Fin 3) (z : IncTotalModule (V := V) (E := E)) :
    H.incFaceRawEval q (φ.totalMap z) = φ.torusHom (G.incFaceRawEval q z) := by
  rw [incFaceRawEval_apply, incFaceRawEval_apply, totalMap_apply_empty,
    incFaceAmbientToTorus_mapRange]

/-! ## The chain map `F_φ` of the actual free resolutions -/

/-- **The free-resolution map `F_φ`**: the perturbed inclusion of `G`, the total map, and the
perturbed projection of `H`. -/
noncomputable def resolutionMap :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₛₗ[φ.coeffRingHom]
      (H.IncResolutionBasis →₀ IncCoeffRing E') :=
  H.incResolutionProjection.comp (φ.totalMap.comp G.incResolutionInclusion)

theorem resolutionMap_apply (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    φ.resolutionMap x =
      H.incResolutionProjection (φ.totalMap (G.incResolutionInclusion x)) := rfl

/-- `F_φ` is a chain map. -/
theorem resolutionMap_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incResolutionDifferential (φ.resolutionMap x) =
      φ.resolutionMap (G.incResolutionDifferential x) := by
  rw [resolutionMap_apply, resolutionMap_apply,
    ← LinearMap.comp_apply H.incResolutionDifferential H.incResolutionProjection,
    ← H.incResolutionProjection_chain, LinearMap.comp_apply, ← totalMap_differential,
    ← LinearMap.comp_apply G.incTotalDifferential G.incResolutionInclusion,
    G.incResolutionInclusion_chain, LinearMap.comp_apply]

/-- `F_φ` preserves homological degrees. -/
theorem resolutionMap_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    φ.resolutionMap x ∈ gradedPiece (IncCoeffRing E') H.incResolutionDegree n :=
  H.incResolutionProjection_degree n _
    (φ.totalMap_mem_incTotalPiece (G.incResolutionInclusion_degree n x hx))

/-- In degree zero `F_φ` lifts the torus homomorphism through the augmentations. -/
theorem resolutionMap_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    H.incResolutionTorusAugmentation (φ.resolutionMap x) =
      φ.torusHom (G.incResolutionTorusAugmentation x) := by
  have hcycle : H.incTotalDifferential (φ.totalMap (G.incResolutionInclusion x)) = 0 := by
    rw [← totalMap_differential,
      show G.incTotalDifferential (G.incResolutionInclusion x) =
        G.incResolutionInclusion (G.incResolutionDifferential x) from
          LinearMap.congr_fun G.incResolutionInclusion_chain x,
      G.incResolutionDifferential_zero_degree x hx, map_zero, map_zero]
  change H.incFaceRawEval 0 (H.incResolutionInclusion (φ.resolutionMap x)) =
    φ.torusHom (G.incFaceRawEval 0 (G.incResolutionInclusion x))
  rw [resolutionMap_apply, H.incFaceRawEval_inclusion_projection hcycle,
    incFaceRawEval_totalMap]

/-- At the coefficient origin `F_φ` is the state map of `φ`. -/
theorem mapRange_resolutionMap (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    mapRange (constantCoeff : IncCoeffRing E' →+* ℂ) (map_zero _) (φ.resolutionMap x) =
      φ.stateMap ℂ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x) := by
  have hI : G.incResolutionInclusion x - G.incCechContraction.i x ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have ha : H.incResolutionProjection (φ.totalMap (G.incResolutionInclusion x)) -
      H.incCechContraction.p (φ.totalMap (G.incResolutionInclusion x)) ∈
      incCoeffAugmentationIdeal E' • ⊤ :=
    H.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E')
      H.incKoszulPerturbation H.incKoszulPerturbation_mem_augmentation
      (φ.totalMap (G.incResolutionInclusion x))
  have hb := map_mem_ideal_smul_top (incCoeffAugmentationIdeal E') H.incCechContraction.p
    (φ.totalMap_mem_ideal hI)
  rw [map_sub φ.totalMap, map_sub H.incCechContraction.p] at hb
  have hsum := Submodule.add_mem _ ha hb
  rw [sub_add_sub_cancel] at hsum
  have h0 := EdgeRelabel.mapRange_constantCoeff_eq_zero hsum
  rw [mapRange_sub (map_sub _), sub_eq_zero] at h0
  rw [resolutionMap_apply, h0, incCechContraction_p_totalMap_i, ← stateMap_mapRange]
  congr 1
  ext b
  simp only [mapRange_apply]
  exact RingHom.congr_fun φ.constantCoeff_comp_coeffRingHom (x b)

/-- `F_φ` on one homological term of the actual free resolutions. -/
noncomputable def freeTermMap (n : ℕ) :
    G.IncFreeTerm n →ₛₗ[φ.coeffRingHom] H.IncFreeTerm n where
  toFun x := ⟨φ.resolutionMap x.val, φ.resolutionMap_degree n x.property⟩
  map_add' x y := Subtype.ext (map_add φ.resolutionMap x.val y.val)
  map_smul' r x := Subtype.ext (LinearMap.map_smulₛₗ φ.resolutionMap r x.val)

@[simp] theorem freeTermMap_val (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.freeTermMap n x).val = φ.resolutionMap x.val := rfl

/-- The termwise map commutes with the differentials of the actual free resolutions. -/
theorem freeTermMap_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.freeTermMap (n + 1) x) =
      φ.freeTermMap n (G.incFreeTermDifferential n x) := by
  apply Subtype.ext
  exact φ.resolutionMap_differential x.val

/-- In degree zero the termwise map lifts the incidence ring homomorphism through the
augmentations. -/
theorem freeTermMap_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.freeTermMap 0 x) =
      φ.incidenceHom (G.incResolutionAugmentation x) := by
  apply Subtype.ext
  exact φ.resolutionMap_torusAugmentation x.property

end EdgeMap

end BPFixedPoints.Multigraph
