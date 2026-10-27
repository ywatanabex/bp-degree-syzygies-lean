import BPFixedPoints.Incidence.IncidenceRelabelRings
import BPFixedPoints.Incidence.ResolutionCupAugmentation
import BPFixedPoints.Incidence.CechCubicalBoundary
import BPFixedPoints.Incidence.PerturbationProductSpecialization
import BPFixedPoints.Incidence.StateExteriorCup
import BPFixedPoints.Incidence.ResolutionTor

/-!
# Edge relabelings act on the Koszul–Čech total complex and on the incidence resolution

Let `φ : EdgeRelabel G H` and write `σ` for the coefficient ring isomorphism. The relabeling of
the total Koszul–Čech module (`totalRelabel`) sends the Čech chain `x` of an edge set `S` to the
relabeling sign of `S` times the coefficientwise image `σ x`, placed at the image edge set. It is
`σ`-semilinear and commutes with the actual total differentials: with the statewise Čech
differentials because the twists of `S` and `φ S` agree and the Čech structure maps have integer
coefficients, and with the Koszul perturbation because the edge sections of `e` and `φ e` agree
after renaming the coefficients and the Koszul removal signs transform by the relabeling signs.

The composite of the perturbed inclusion of `G`, the total relabeling and the perturbed
projection of `H` (`resolutionRelabel`) is a `σ`-semilinear chain map between the actual finite
free resolutions of the two incidence rings. It preserves homological degrees and lifts the
incidence ring isomorphism through the augmentations. At the coefficient origin it is the signed
relabeling of states.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.CechProduct

open Finsupp

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {V : Type} [Fintype V]

/-- A ring homomorphism maps the integer boundary coefficients to the boundary coefficients. -/
theorem map_boundaryCoefficient (b : Basis) : f (boundaryCoefficient R b) = boundaryCoefficient R' b := by
  rcases b with k | k | k <;> simp [boundaryCoefficient]

/-- Coefficientwise ring change commutes with the product Čech differential. -/
theorem contraction_d_mapRange [DecidableEq V] (d : V → ℕ) (x : C R V) :
    (contraction R' d).d (mapRange f (map_zero f) x) =
      mapRange f (map_zero f) ((contraction R d).d x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapRange_add (map_add f), map_add, hx, hy, map_add, mapRange_add (map_add f)]
  | single b r =>
    rw [mapRange_single, contraction_d_single, contraction_d_single, mapRange_finsetSum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mapRange_single, map_mul, map_mul, map_pow, map_neg, map_one, map_boundaryCoefficient]

/-- Coefficientwise ring change commutes with the Čech parity. -/
theorem contraction_sign_mapRange (d : V → ℕ) (x : C R V) :
    (contraction R' d).sign (mapRange f (map_zero f) x) =
      mapRange f (map_zero f) ((contraction R d).sign x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [mapRange_add (map_add f), map_add, hx, hy, map_add, mapRange_add (map_add f)]
  | single b r =>
    rw [mapRange_single, contraction_sign_single, contraction_sign_single, smul_single,
      smul_single, mapRange_single, smul_eq_mul, smul_eq_mul, map_mul, map_pow, map_neg, map_one]

/-- Coefficientwise ring change commutes with multiplication by a monomial section. -/
theorem multiply_mapRange (a b : V → ℕ) (x : C R V) :
    multiply R' a b (mapRange f (map_zero f) x) = mapRange f (map_zero f) (multiply R a b x) := by
  simp only [multiply, lmapDomain_apply]
  exact mapDomain_mapRange _ x f (map_zero f) (map_add f)

/-- Coefficientwise ring change is semilinear. -/
theorem mapRange_ring_smul {α : Type*} (r : R) (x : α →₀ R) :
    mapRange f (map_zero f) (r • x) = f r • mapRange f (map_zero f) x :=
  mapRange_smul' r (f r) x (fun z => by rw [smul_eq_mul, smul_eq_mul, map_mul])

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct IncidencePerturbation ResolutionTools MvPolynomial

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- The coefficient ring isomorphism as a ring homomorphism. -/
noncomputable def coeffRingHom : IncCoeffRing E →+* IncCoeffRing E' :=
  φ.coeffEquiv.toAlgHom.toRingHom

@[simp] theorem coeffRingHom_apply (p : IncCoeffRing E) : φ.coeffRingHom p = φ.coeffEquiv p := rfl

/-- The coefficient ring isomorphism preserves the coefficient origin. -/
theorem constantCoeff_comp_coeffRingHom :
    (constantCoeff : IncCoeffRing E' →+* ℂ).comp φ.coeffRingHom = constantCoeff := by
  ext p
  · exact φ.constantCoeff_coeffEquiv (C p)
  · exact φ.constantCoeff_coeffEquiv (X _)

/-- The edge sections of an image edge are those of the original edge, with exchanged endpoint
indices for a reversed edge. -/
theorem incSectionLeft_relabel (e : E) (ab : Fin 2 × Fin 2) :
    H.incSectionLeft (φ.edge e) (φ.endpointIndex e ab).1 (φ.endpointIndex e ab).2 =
      G.incSectionLeft e ab.1 ab.2 := by
  funext v
  unfold incSectionLeft endpointIndex
  rw [φ.fst_edge, φ.snd_edge]
  cases φ.reversed e
  · simp
  · simp only [ite_true, Prod.fst_swap, Prod.snd_swap]
    omega

theorem incSectionRight_relabel (e : E) (ab : Fin 2 × Fin 2) :
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
theorem incEdgeAction_relabel (e : E) (x : IncCechModule (V := V) (E := E)) :
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
  rw [incSectionLeft_relabel, incSectionRight_relabel, mapRange_ring_smul, multiply_mapRange,
    coeffRingHom_apply, coeffEquiv_X, coeffIdxEquiv_apply]

/-! ## The relabeling of the total Koszul–Čech module -/

/-- The relabeling of total chains, as an additive map. -/
noncomputable def totalRelabelAdd :
    IncTotalModule (V := V) (E := E) →+ IncTotalModule (V := V) (E := E') :=
  Finsupp.liftAddHom fun S =>
    (Finsupp.singleAddHom (φ.edgeSet S)).comp
      ((DistribSMul.toAddMonoidHom (IncCechModule (V := V) (E := E')) (φ.sign (IncCoeffRing E') S)).comp
        (Finsupp.mapRange.addMonoidHom φ.coeffRingHom.toAddMonoidHom))

theorem totalRelabelAdd_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalRelabelAdd (single S x) =
      single (φ.edgeSet S) (φ.sign (IncCoeffRing E') S • mapRange φ.coeffRingHom (map_zero _) x) := by
  simp [totalRelabelAdd]

/-- The relabeling of total chains: the chain of an edge set goes to the relabeling sign times its
renamed chain, at the image edge set. It is semilinear for the coefficient isomorphism. -/
noncomputable def totalRelabel :
    IncTotalModule (V := V) (E := E) →ₛₗ[φ.coeffRingHom] IncTotalModule (V := V) (E := E') where
  toFun := φ.totalRelabelAdd
  map_add' := map_add _
  map_smul' r z := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]
    | single S x =>
      rw [smul_single, totalRelabelAdd_single, totalRelabelAdd_single, smul_single,
        mapRange_ring_smul, smul_comm]

@[simp] theorem totalRelabel_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalRelabel (single S x) =
      single (φ.edgeSet S) (φ.sign (IncCoeffRing E') S • mapRange φ.coeffRingHom (map_zero _) x) :=
  φ.totalRelabelAdd_single S x

/-- The component of a relabeled chain at an image edge set. -/
theorem totalRelabel_apply_edgeSet (z : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    φ.totalRelabel z (φ.edgeSet S) = φ.sign (IncCoeffRing E') S • mapRange φ.coeffRingHom (map_zero _) (z S) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, Finsupp.add_apply, hz, hw, Finsupp.add_apply,
      mapRange_add (map_add _), smul_add]
  | single T x =>
    rw [totalRelabel_single]
    by_cases h : T = S
    · subst h
      simp
    · rw [single_eq_of_ne (fun h' => h (φ.edgeSet_injective h'.symm)), single_eq_of_ne (Ne.symm h)]
      simp

/-- Every edge set of `H` is an image edge set. -/
theorem edgeSet_preimage (T : Finset E') : φ.edgeSet (T.map φ.edge.symm.toEmbedding) = T := by
  simp [edgeSet_def, Finset.map_map]

/-- The relabeling commutes with the statewise Čech differentials. -/
theorem totalRelabel_cech (z : IncTotalModule (V := V) (E := E)) :
    φ.totalRelabel (G.incCechContraction.d z) = H.incCechContraction.d (φ.totalRelabel z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incCechContraction_d, Koszul.diagonal_single, totalRelabel_single, totalRelabel_single,
      H.incCechContraction_d, Koszul.diagonal_single, φ.deg_edgeSet, map_smul,
      contraction_d_mapRange]

/-- The relabeling commutes with the Koszul perturbation. -/
theorem totalRelabel_koszul (z : IncTotalModule (V := V) (E := E)) :
    φ.totalRelabel (G.incKoszulPerturbation z) = H.incKoszulPerturbation (φ.totalRelabel z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]
  | single S x =>
    rw [G.incKoszulPerturbation_single, map_sum, totalRelabel_single,
      H.incKoszulPerturbation_single, edgeSet_def, Finset.sum_map, ← edgeSet_def]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [totalRelabel_single, Equiv.coe_toEmbedding, ← edgeSet_erase, φ.deg_edgeSet]
    congr 1
    simp only [map_smul]
    rw [φ.incEdgeAction_relabel, contraction_sign_mapRange, mapRange_ring_smul, smul_smul,
      smul_smul]
    congr 1
    have h := φ.sign_erase_mul_koszulSign (IncCoeffRing E') he
    rw [show φ.coeffRingHom (Koszul.sign (A := IncCoeffRing E) S e) =
        Koszul.sign (A := IncCoeffRing E') S e by simp [Koszul.sign]]
    rw [mul_comm (φ.sign (IncCoeffRing E') (S.erase e)), h]

/-- The relabeling commutes with the actual total differentials. -/
theorem totalRelabel_differential (z : IncTotalModule (V := V) (E := E)) :
    φ.totalRelabel (G.incTotalDifferential z) = H.incTotalDifferential (φ.totalRelabel z) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, totalRelabel_cech, totalRelabel_koszul,
    incTotalDifferential, LinearMap.add_apply]

/-- The relabeling preserves total degrees. -/
theorem totalRelabel_mem_incTotalPiece {n : ℤ} {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ incTotalPiece (V := V) (E := E) n) :
    φ.totalRelabel z ∈ incTotalPiece (V := V) (E := E') n := by
  intro T
  rw [← φ.edgeSet_preimage T, totalRelabel_apply_edgeSet, card_edgeSet]
  apply Submodule.smul_mem
  rw [mem_supported]
  intro b hb
  exact (mem_supported _ _).mp (hz (T.map φ.edge.symm.toEmbedding))
    (support_mapRange hb)

/-- The relabeling sends the coefficient-origin ideal multiple to the coefficient-origin ideal
multiple. -/
theorem totalRelabel_mem_ideal {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ RingHom.ker (constantCoeff : IncCoeffRing E →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E)))) :
    φ.totalRelabel z ∈ RingHom.ker (constantCoeff : IncCoeffRing E' →+* ℂ) •
      (⊤ : Submodule (IncCoeffRing E') (IncTotalModule (V := V) (E := E'))) := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    rw [LinearMap.map_smulₛₗ]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    rw [RingHom.mem_ker] at hr ⊢
    rw [coeffRingHom_apply, constantCoeff_coeffEquiv, hr]
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Included states, relabeled and projected, are the signed relabeling of the renamed states. -/
theorem incCechContraction_p_totalRelabel_i (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incCechContraction.p (φ.totalRelabel (G.incCechContraction.i x)) =
      φ.stateRelabel (IncCoeffRing E') (mapRange φ.coeffRingHom (map_zero _) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, mapRange_add (map_add _), map_add]
  | single b r =>
    obtain ⟨S, κ⟩ := b
    rw [mapRange_single, stateRelabel_single, stateIndex_mk]
    rw [← G.incStateEmbed_single (IncCoeffRing E) S κ r, ← G.incCechContractionOver_incCoeffRing,
      G.incCechContractionOver_i_embed, totalRelabel_single, ← contraction_i_mapRange,
      ← H.incCechContractionOver_incCoeffRing, H.incCechContractionOver_p_single, map_smul,
      ← castH_contraction_p (IncCoeffRing E') (φ.deg_edgeSet S).symm, contraction_p_i,
      mapRange_single, castH_single, map_smul, incStateEmbed_single, smul_single, smul_eq_mul]

end EdgeRelabel

/-! ## Face evaluation -/

section Face

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

/-- On a face monomial with coefficient one, face evaluation of a graph is the evaluation of the
face monomial at the face vertex units; on other faces it vanishes. -/
theorem incFaceAmbientToTorus_single_one (K : Multigraph V E) (q q' : V → Fin 3)
    (m : CechProduct.FaceMonoid q') :
    K.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (single (embedFace q' m) (1 : IncCoeffRing E)) q) =
      if h : q' = q then faceEvaluate q (K.incFaceVertexUnit q)
        (AddMonoidAlgebra.single (h ▸ m) (1 : ℂ)) else 0 := by
  by_cases h : q' = q
  · subst h
    rw [dite_eq_left rfl, polynomialFaceEquiv_apply, faceEquiv_single_same, facePolynomialEquiv,
      AddMonoidAlgebra.commAlgEquiv_single_zero]
    exact facePolynomialEvaluate_C _ _ _ _
  · rw [dite_eq_right h, polynomialFaceEquiv_apply, faceEquiv_single_ne _ (Ne.symm h), map_zero, map_zero]

end Face

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'} (φ : EdgeRelabel G H)

/-- The torus isomorphism carries the face vertex units of `G` to those of `H`. -/
theorem units_map_incFaceVertexUnit (q : V → Fin 3) (v : V) :
    Units.map (φ.torusEquiv : G.IncTorusRing →* H.IncTorusRing) (G.incFaceVertexUnit q v) =
      H.incFaceVertexUnit q v := by
  apply Units.ext
  rw [Units.coe_map, incFaceVertexUnit_val, incFaceVertexUnit_val]
  exact φ.torusEquiv_incChartVal _ (Sum.inl v)

/-- The torus isomorphism carries face evaluation at the units of `G` to face evaluation at the
units of `H`. -/
theorem torusEquiv_faceEvaluate (q : V → Fin 3) (f : CechProduct.FaceRing ℂ q) :
    φ.torusEquiv (faceEvaluate q (G.incFaceVertexUnit q) f) =
      faceEvaluate q (H.incFaceVertexUnit q) f := by
  have h : φ.torusEquiv.toAlgHom.comp (faceEvaluate q (G.incFaceVertexUnit q)) =
      faceEvaluate q (H.incFaceVertexUnit q) := by
    apply AddMonoidAlgebra.algHom_ext
    swap
    · exact Subsingleton.elim _ _
    intro m
    change φ.torusEquiv (faceEvaluate q (G.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)) =
      faceEvaluate q (H.incFaceVertexUnit q) (AddMonoidAlgebra.single m 1)
    rw [faceEvaluate_single, faceEvaluate_single, one_smul, one_smul]
    have key : ∀ u : G.IncTorusRingˣ, φ.torusEquiv (u : G.IncTorusRing) =
        ((Units.map (φ.torusEquiv : G.IncTorusRing →* H.IncTorusRing) u : H.IncTorusRingˣ) :
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
      φ.torusEquiv (G.incFaceAmbientToTorus q (polynomialFaceEquiv ℂ (IncCoeffIdx E) c q)) := by
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
      torusEquiv_incTorusCoeffHom, coeffRingHom_apply, incFaceAmbientToTorus_single_one,
      incFaceAmbientToTorus_single_one]
    congr 1
    split_ifs with h
    · exact (φ.torusEquiv_faceEvaluate q _).symm
    · exact (map_zero _).symm

/-- Face evaluation of relabeled total chains is the torus image of face evaluation. -/
theorem incFaceRawEval_totalRelabel (q : V → Fin 3) (z : IncTotalModule (V := V) (E := E)) :
    H.incFaceRawEval q (φ.totalRelabel z) = φ.torusEquiv (G.incFaceRawEval q z) := by
  rw [incFaceRawEval_apply, incFaceRawEval_apply, ← φ.edgeSet_empty, totalRelabel_apply_edgeSet,
    sign_empty, one_smul, incFaceAmbientToTorus_mapRange]

/-! ## The relabeling chain map of the actual free resolutions -/

/-- The relabeling of the finite free resolution modules: the perturbed inclusion of `G`, the
relabeling of total chains, and the perturbed projection of `H`. -/
noncomputable def resolutionRelabel :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₛₗ[φ.coeffRingHom]
      (H.IncResolutionBasis →₀ IncCoeffRing E') :=
  H.incResolutionProjection.comp (φ.totalRelabel.comp G.incResolutionInclusion)

theorem resolutionRelabel_apply (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    φ.resolutionRelabel x =
      H.incResolutionProjection (φ.totalRelabel (G.incResolutionInclusion x)) := rfl

/-- The resolution relabeling is a chain map. -/
theorem resolutionRelabel_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incResolutionDifferential (φ.resolutionRelabel x) =
      φ.resolutionRelabel (G.incResolutionDifferential x) := by
  rw [resolutionRelabel_apply, resolutionRelabel_apply,
    ← LinearMap.comp_apply H.incResolutionDifferential H.incResolutionProjection,
    ← H.incResolutionProjection_chain, LinearMap.comp_apply, ← totalRelabel_differential,
    ← LinearMap.comp_apply G.incTotalDifferential G.incResolutionInclusion,
    G.incResolutionInclusion_chain, LinearMap.comp_apply]

/-- The resolution relabeling preserves homological degrees. -/
theorem resolutionRelabel_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    φ.resolutionRelabel x ∈ gradedPiece (IncCoeffRing E') H.incResolutionDegree n :=
  H.incResolutionProjection_degree n _
    (φ.totalRelabel_mem_incTotalPiece (G.incResolutionInclusion_degree n x hx))

/-- In degree zero the resolution relabeling lifts the torus isomorphism through the
augmentations. -/
theorem resolutionRelabel_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    H.incResolutionTorusAugmentation (φ.resolutionRelabel x) =
      φ.torusEquiv (G.incResolutionTorusAugmentation x) := by
  have hcycle : H.incTotalDifferential (φ.totalRelabel (G.incResolutionInclusion x)) = 0 := by
    rw [← totalRelabel_differential,
      show G.incTotalDifferential (G.incResolutionInclusion x) =
        G.incResolutionInclusion (G.incResolutionDifferential x) from
          LinearMap.congr_fun G.incResolutionInclusion_chain x,
      G.incResolutionDifferential_zero_degree x hx, map_zero, map_zero]
  change H.incFaceRawEval 0 (H.incResolutionInclusion (φ.resolutionRelabel x)) =
    φ.torusEquiv (G.incFaceRawEval 0 (G.incResolutionInclusion x))
  rw [resolutionRelabel_apply, H.incFaceRawEval_inclusion_projection hcycle,
    incFaceRawEval_totalRelabel]

/-- Elements of the coefficient-origin ideal multiple specialize to zero. -/
theorem mapRange_constantCoeff_eq_zero {K B : Type} {z : B →₀ IncCoeffRing K}
    (hz : z ∈ incCoeffAugmentationIdeal K •
      (⊤ : Submodule (IncCoeffRing K) (B →₀ IncCoeffRing K))) :
    mapRange (constantCoeff : IncCoeffRing K →+* ℂ) (map_zero _) z = 0 := by
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr w _
    rw [mapRange_ring_smul, RingHom.mem_ker.mp hr, zero_smul]
  · intro x y hx hy
    rw [mapRange_add (map_add _), hx, hy, add_zero]

/-- At the coefficient origin the resolution relabeling is the signed relabeling of states. -/
theorem mapRange_resolutionRelabel (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    mapRange (constantCoeff : IncCoeffRing E' →+* ℂ) (map_zero _) (φ.resolutionRelabel x) =
      φ.stateRelabel ℂ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x) := by
  have hI : G.incResolutionInclusion x - G.incCechContraction.i x ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have ha : H.incResolutionProjection (φ.totalRelabel (G.incResolutionInclusion x)) -
      H.incCechContraction.p (φ.totalRelabel (G.incResolutionInclusion x)) ∈
      incCoeffAugmentationIdeal E' • ⊤ :=
    H.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E')
      H.incKoszulPerturbation H.incKoszulPerturbation_mem_augmentation
      (φ.totalRelabel (G.incResolutionInclusion x))
  have hb := map_mem_ideal_smul_top (incCoeffAugmentationIdeal E') H.incCechContraction.p
    (φ.totalRelabel_mem_ideal hI)
  rw [map_sub φ.totalRelabel, map_sub H.incCechContraction.p] at hb
  have hsum := Submodule.add_mem _ ha hb
  rw [sub_add_sub_cancel] at hsum
  have h0 := mapRange_constantCoeff_eq_zero hsum
  rw [mapRange_sub (map_sub _), sub_eq_zero] at h0
  rw [resolutionRelabel_apply, h0, incCechContraction_p_totalRelabel_i, ← stateRelabel_mapRange]
  congr 1
  ext b
  simp only [mapRange_apply]
  exact RingHom.congr_fun φ.constantCoeff_comp_coeffRingHom (x b)

/-- The resolution relabeling on one homological term of the actual free resolutions. -/
noncomputable def freeTermRelabel (n : ℕ) :
    G.IncFreeTerm n →ₛₗ[φ.coeffRingHom] H.IncFreeTerm n where
  toFun x := ⟨φ.resolutionRelabel x.val, φ.resolutionRelabel_degree n x.property⟩
  map_add' x y := Subtype.ext (map_add φ.resolutionRelabel x.val y.val)
  map_smul' r x := Subtype.ext (LinearMap.map_smulₛₗ φ.resolutionRelabel r x.val)

@[simp] theorem freeTermRelabel_val (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.freeTermRelabel n x).val = φ.resolutionRelabel x.val := rfl

/-- The termwise relabeling commutes with the differentials of the actual free resolutions. -/
theorem freeTermRelabel_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.freeTermRelabel (n + 1) x) =
      φ.freeTermRelabel n (G.incFreeTermDifferential n x) := by
  apply Subtype.ext
  exact φ.resolutionRelabel_differential x.val

/-- In degree zero the termwise relabeling lifts the incidence ring isomorphism through the
augmentations. -/
theorem freeTermRelabel_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.freeTermRelabel 0 x) =
      φ.incidenceEquiv (G.incResolutionAugmentation x) := by
  apply Subtype.ext
  exact φ.resolutionRelabel_torusAugmentation x.property

end EdgeRelabel

end BPFixedPoints.Multigraph
