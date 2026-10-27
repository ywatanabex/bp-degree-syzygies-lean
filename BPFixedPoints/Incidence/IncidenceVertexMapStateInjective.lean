import BPFixedPoints.Incidence.VertexMapPullbackCech
import BPFixedPoints.Incidence.IncidenceVertexMapSupport

/-!
# The state formula for injective vertex maps

Let `φ : VertexMap G H` be a vertex map whose vertex function is injective. Since the edges are
unchanged, every vertex of `H` off the image of `φ` is isolated, so for every edge set `S` the
twist of `S` in `H` is the twist in `G` at the image vertices and zero elsewhere
(`deg_vertex_of_injective`, `deg_eq_zero_of_not_mem_range`), and the same holds for the edge
sections.

**Chain level.** Applying the pullback of product Čech chains `cechExtend` (`VertexMapPullbackCech`)
to the Čech chain of every edge set gives a map of total Koszul–Čech modules (`totalExtend`). It
commutes with the statewise Čech differentials, the Čech parities and the edge actions, hence with
the total differentials (`totalExtend_differential`), preserves total degrees, and on the all-zero
face it evaluates to the torus image of the face evaluation (`incFaceRawEval_totalExtend`). The
composite of the perturbed inclusion of `G`, `totalExtend` and the perturbed projection of `H`
(`resolutionExtend`) is a chain map of the actual free resolutions lifting the incidence ring map
`φ.incidenceHom` through the augmentations.

**States.** Restricting a state index of `H` to the image gives a bijection of resolution states
(`stateEquiv`, built from `statePull`): the edge set is unchanged, the local index at `v` is the
index at `φ v`, and the vertices off the image only carry the `H⁰` index. The signed state map
`statePush` sends the state `⟨S, κ⟩` of `G` to `vertexMapSign φ.vertex (twistSupport (G.deg S))`
times the corresponding state of `H`. At the coefficient origin `resolutionExtend` is `statePush`
(`mapRange_resolutionExtend`), so:

* **state formula** (`incidenceTorFullState_vertexMap_of_injective`,
  `incidenceTorFullState_vertexMap_apply_of_injective`): the full state vector of the image of a
  Tor class under the Tor map `φ.incidenceTorMap` (Mathlib's derived functor functoriality, not
  defined through states) is the signed state map of its full state vector.

Only injective vertex functions are treated here; the general non-colliding case is reduced to this
one in `IncidenceVertexMapStateFormula`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory Finsupp CechProduct IncidencePerturbation ResolutionTools MvPolynomial

/-! ## Face evaluation of monomials -/

section Face

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

/-- The integer exponent of a one-vertex Čech monomial. -/
def basisExponent : Basis → ℤ
  | Sum.inl k => k
  | Sum.inr (Sum.inl k) => k
  | Sum.inr (Sum.inr k) => k

theorem exponentToInt_eq_basisExponent (k : Fin 3) (x : FaceExponent k) :
    exponentToInt k x = basisExponent (vertexFaceEquiv.symm ⟨k, x⟩) := by
  fin_cases k <;> rfl

/-- Face exponents read from the monomial. -/
theorem faceToInt_eq_basisExponent (q : V → Fin 3) (m : FaceMonoid q) (v : V) :
    faceToInt q m v = basisExponent (embedFace q m v) :=
  exponentToInt_eq_basisExponent (q v) (m v)

/-- A face monomial lies on the left chart at every vertex exactly for the all-zero face. -/
theorem embedFace_left_iff (q : V → Fin 3) (m : FaceMonoid q) :
    (∀ v, ∃ k, embedFace q m v = Sum.inl k) ↔ q = 0 := by
  have hk : ∀ (k : Fin 3) (x : FaceExponent k),
      (∃ n, vertexFaceEquiv.symm ⟨k, x⟩ = Sum.inl n) ↔ k = 0 := by
    intro k x
    fin_cases k
    · exact ⟨fun _ => rfl, fun _ => ⟨x, rfl⟩⟩
    · simp [vertexFaceEquiv]
    · simp [vertexFaceEquiv]
  constructor
  · intro h
    funext v
    exact (hk (q v) (m v)).1 (h v)
  · intro h v
    exact (hk (q v) (m v)).2 (congrFun h v)

/-- Face evaluation on the all-zero face of a left chart monomial: the product of the face vertex
units to the exponents of the monomial. -/
theorem incFaceAmbientToTorus_zero_single_of_left (K : Multigraph V E) (b : V → Basis)
    (hb : ∀ v, ∃ k, b v = Sum.inl k) :
    K.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (single b (1 : IncCoeffRing E)) 0) =
      ((∏ v, K.incFaceVertexUnit 0 v ^ basisExponent (b v) : K.IncTorusRingˣ) :
        K.IncTorusRing) := by
  obtain ⟨⟨q, m⟩, rfl⟩ := CechProduct.faceBasisEquiv.symm.surjective b
  change K.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E)
    (single (embedFace q m) (1 : IncCoeffRing E)) 0) = _
  have hq : q = 0 := (embedFace_left_iff q m).1 hb
  subst hq
  rw [incFaceAmbientToTorus_single_one, dite_eq_left rfl, faceEvaluate_single, one_smul]
  change ((∏ v, K.incFaceVertexUnit 0 v ^ faceToInt 0 m v : K.IncTorusRingˣ) : K.IncTorusRing) = _
  simp only [faceToInt_eq_basisExponent]
  rfl

/-- Face evaluation on the all-zero face vanishes on monomials leaving the left chart. -/
theorem incFaceAmbientToTorus_zero_single_of_not_left (K : Multigraph V E) (b : V → Basis)
    (hb : ¬ ∀ v, ∃ k, b v = Sum.inl k) (r : IncCoeffRing E) :
    K.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E) (single b r) 0) = 0 := by
  obtain ⟨⟨q, m⟩, rfl⟩ := CechProduct.faceBasisEquiv.symm.surjective b
  change K.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E) (single (embedFace q m) r)
    0) = 0
  have hq : q ≠ 0 := fun h => hb ((embedFace_left_iff q m).2 h)
  rw [polynomialFaceEquiv_apply, faceEquiv_single_ne _ (Ne.symm hq), map_zero, map_zero]

end Face

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Twists and sections of an injective vertex map -/

/-- For an injective vertex function the degree of an image vertex is the original degree. -/
theorem deg_vertex_of_injective (hφ : Function.Injective φ.vertex) (S : Finset E) (v : V) :
    H.deg S (φ.vertex v) = G.deg S v := by
  rw [φ.deg_eq_sum_fiber]
  refine Finset.sum_eq_single_of_mem v ((φ.mem_fiber).2 rfl) fun v' hv' hne => ?_
  exact absurd (hφ ((φ.mem_fiber).1 hv')) hne

/-- A vertex off the image of the vertex function has degree zero. -/
theorem deg_eq_zero_of_not_mem_range (S : Finset E) {w : W} (hw : ∀ v, φ.vertex v ≠ w) :
    H.deg S w = 0 := by
  rw [φ.deg_eq_sum_fiber]
  refine Finset.sum_eq_zero fun v hv => ?_
  exact absurd ((φ.mem_fiber).1 hv) (hw v)

theorem incSectionLeft_vertex (hφ : Function.Injective φ.vertex) (e : E) (α β : Fin 2) (v : V) :
    H.incSectionLeft e α β (φ.vertex v) = G.incSectionLeft e α β v := by
  unfold incSectionLeft
  simp only [φ.fst_edge, φ.snd_edge, hφ.eq_iff]

theorem incSectionRight_vertex (hφ : Function.Injective φ.vertex) (e : E) (α β : Fin 2) (v : V) :
    H.incSectionRight e α β (φ.vertex v) = G.incSectionRight e α β v := by
  unfold incSectionRight
  simp only [φ.fst_edge, φ.snd_edge, hφ.eq_iff]

theorem incSectionLeft_of_not_mem_range (e : E) (α β : Fin 2) {w : W}
    (hw : ∀ v, φ.vertex v ≠ w) : H.incSectionLeft e α β w = 0 := by
  unfold incSectionLeft
  simp [φ.fst_edge, φ.snd_edge, hw]

theorem incSectionRight_of_not_mem_range (e : E) (α β : Fin 2) {w : W}
    (hw : ∀ v, φ.vertex v ≠ w) : H.incSectionRight e α β w = 0 := by
  unfold incSectionRight
  simp [φ.fst_edge, φ.snd_edge, hw]

/-- The edge action of `H` on extended chains is the extended edge action of `G`. -/
theorem incEdgeAction_cechExtend (hφ : Function.Injective φ.vertex) (e : E)
    (x : IncCechModule (V := V) (E := E)) :
    H.incEdgeAction e (cechExtend (IncCoeffRing E) φ.vertex x) =
      cechExtend (IncCoeffRing E) φ.vertex (G.incEdgeAction e x) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [cechExtend_multiply (IncCoeffRing E) hφ _ _ (H.incSectionLeft e α β)
    (H.incSectionRight e α β) (φ.incSectionLeft_vertex hφ e α β)
    (φ.incSectionRight_vertex hφ e α β)
    (fun w hw => φ.incSectionLeft_of_not_mem_range e α β hw)
    (fun w hw => φ.incSectionRight_of_not_mem_range e α β hw)]

/-! ## The total Koszul–Čech map -/

/-- The pullback of total chains along a vertex map: the Čech chain of every edge set is extended by
constant sections off the image (`cechExtend`). It is a chain map when the vertex function is
injective. -/
noncomputable def totalExtend :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] IncTotalModule (V := W) (E := E) :=
  Finsupp.mapRange.linearMap (cechExtend (IncCoeffRing E) φ.vertex)

@[simp] theorem totalExtend_single (S : Finset E) (x : IncCechModule (V := V) (E := E)) :
    φ.totalExtend (single S x) = single S (cechExtend (IncCoeffRing E) φ.vertex x) := by
  simp [totalExtend]

theorem totalExtend_apply (z : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    φ.totalExtend z S = cechExtend (IncCoeffRing E) φ.vertex (z S) := by
  simp [totalExtend]

variable (hφ : Function.Injective φ.vertex)

include hφ in
/-- The total pullback commutes with the statewise Čech differentials. -/
theorem totalExtend_cech (z : IncTotalModule (V := V) (E := E)) :
    φ.totalExtend (G.incCechContraction.d z) = H.incCechContraction.d (φ.totalExtend z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single S x =>
    rw [G.incCechContraction_d, Koszul.diagonal_single, totalExtend_single,
      totalExtend_single, H.incCechContraction_d, Koszul.diagonal_single,
      cechExtend_d (IncCoeffRing E) hφ (G.deg S) (H.deg S) (φ.deg_vertex_of_injective hφ S)
        (fun w hw => φ.deg_eq_zero_of_not_mem_range S hw)]

include hφ in
/-- The total pullback commutes with the Koszul perturbation. -/
theorem totalExtend_koszul (z : IncTotalModule (V := V) (E := E)) :
    φ.totalExtend (G.incKoszulPerturbation z) = H.incKoszulPerturbation (φ.totalExtend z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single S x =>
    rw [G.incKoszulPerturbation_single, map_sum, totalExtend_single,
      H.incKoszulPerturbation_single]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [totalExtend_single, cechExtend_sign (IncCoeffRing E) hφ (G.deg (S.erase e))
      (H.deg (S.erase e)), map_smul, φ.incEdgeAction_cechExtend hφ]

include hφ in
/-- The total pullback commutes with the actual total differentials. -/
theorem totalExtend_differential (z : IncTotalModule (V := V) (E := E)) :
    φ.totalExtend (G.incTotalDifferential z) = H.incTotalDifferential (φ.totalExtend z) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, φ.totalExtend_cech hφ,
    φ.totalExtend_koszul hφ, incTotalDifferential, LinearMap.add_apply]

include hφ in
/-- The total pullback preserves total degrees. -/
theorem totalExtend_mem_incTotalPiece {n : ℤ} {z : IncTotalModule (V := V) (E := E)}
    (hz : z ∈ incTotalPiece (V := V) (E := E) n) :
    φ.totalExtend z ∈ incTotalPiece (V := W) (E := E) n := by
  intro S
  rw [totalExtend_apply]
  exact cechExtend_mem_supported (IncCoeffRing E) hφ (hz S)

/-! ## Face evaluation on the all-zero chart -/

/-- The torus map carries the face vertex units of `G` on the all-zero face to those of `H` at the
image vertices. -/
theorem units_map_incFaceVertexUnit_zero (v : V) :
    Units.map (φ.torusHom : G.IncTorusRing →* H.IncTorusRing) (G.incFaceVertexUnit 0 v) =
      H.incFaceVertexUnit 0 (φ.vertex v) := by
  apply Units.ext
  rw [Units.coe_map, incFaceVertexUnit_val, incFaceVertexUnit_val]
  exact φ.torusHom_incChartVal (faceOrientation (0 : W → Fin 3)) (Sum.inl v)

include hφ in
/-- Face evaluation of extended Čech chains on the all-zero face is the torus image of face
evaluation. -/
theorem incFaceAmbientToTorus_cechExtend (c : IncCechModule (V := V) (E := E)) :
    H.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E)
        (cechExtend (IncCoeffRing E) φ.vertex c) 0) =
      φ.torusHom (G.incFaceAmbientToTorus 0 (polynomialFaceEquiv ℂ (IncCoeffIdx E) c 0)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, map_add, hx, hy,
      map_add, Pi.add_apply, map_add, map_add]
  | single b r =>
    have hr : ∀ {X : Type} [Fintype X] (a : X → Basis) (s : IncCoeffRing E),
        (single a s : IncCechModule (V := X) (E := E)) = s • single a (1 : IncCoeffRing E) := by
      intro X _ a s
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hr b r, map_smul, H.incFaceEval_smul, G.incFaceEval_smul, map_mul,
      φ.torusHom_incTorusCoeffHom]
    congr 1
    rw [cechExtend_single, map_sum, Finset.sum_apply, map_sum]
    by_cases hb : ∀ v, ∃ k, b v = Sum.inl k
    · have hov : overlapVertices b = ∅ := by
        ext v
        obtain ⟨k, hk⟩ := hb v
        simp [mem_overlapVertices, hk, lineDegree]
      let s₁ : W → Bool := fun _ => true
      have hs₁ : s₁ ∈ unitChoices φ.vertex := mem_unitChoices.2 fun _ => rfl
      rw [Finset.sum_eq_single s₁]
      · rw [hov, vertexMapSign_empty, mul_one]
        have hleft : ∀ w, ∃ k, extendMonomial φ.vertex b s₁ w = Sum.inl k := by
          intro w
          by_cases hw : ∃ v, φ.vertex v = w
          · obtain ⟨v, rfl⟩ := hw
            rw [extendMonomial_apply_image hφ]
            exact hb v
          · push Not at hw
            rw [extendMonomial_apply_of_not_mem _ _ hw]
            exact ⟨0, rfl⟩
        rw [incFaceAmbientToTorus_zero_single_of_left H _ hleft,
          incFaceAmbientToTorus_zero_single_of_left G _ hb]
        change _ = ((Units.map (φ.torusHom : G.IncTorusRing →* H.IncTorusRing)
          (∏ v, G.incFaceVertexUnit 0 v ^ basisExponent (b v)) : H.IncTorusRingˣ) : H.IncTorusRing)
        rw [map_prod]
        simp only [map_zpow, units_map_incFaceVertexUnit_zero]
        congr 1
        refine (Fintype.prod_of_injective φ.vertex hφ _ _ ?_ ?_).symm
        · intro w hw
          have hw' : ∀ v, φ.vertex v ≠ w := fun v hv => hw ⟨v, hv⟩
          rw [extendMonomial_apply_of_not_mem _ _ hw']
          change H.incFaceVertexUnit 0 w ^ (0 : ℤ) = 1
          exact zpow_zero _
        · intro v
          rw [extendMonomial_apply_image hφ]
      · intro s hs hne
        have hex : ∃ w, s w = false := by
          by_contra hall
          push Not at hall
          exact hne (funext fun w => by simpa using hall w)
        obtain ⟨w, hw⟩ := hex
        have hwr : ∀ v, φ.vertex v ≠ w := by
          intro v hv
          rw [← hv, mem_unitChoices.1 hs v] at hw
          exact Bool.noConfusion hw
        apply incFaceAmbientToTorus_zero_single_of_not_left
        intro hall
        obtain ⟨k, hk⟩ := hall w
        rw [extendMonomial_apply_of_not_mem _ _ hwr, hw] at hk
        exact absurd hk (by simp [unitBasis])
      · intro h
        exact absurd hs₁ h
    · rw [incFaceAmbientToTorus_zero_single_of_not_left G b hb, map_zero]
      refine Finset.sum_eq_zero fun s _ => ?_
      apply incFaceAmbientToTorus_zero_single_of_not_left
      intro hall
      apply hb
      intro v
      obtain ⟨k, hk⟩ := hall (φ.vertex v)
      rw [extendMonomial_apply_image hφ] at hk
      exact ⟨k, hk⟩

include hφ in
/-- Face evaluation of pulled-back total chains is the torus image of face evaluation. -/
theorem incFaceRawEval_totalExtend (z : IncTotalModule (V := V) (E := E)) :
    H.incFaceRawEval 0 (φ.totalExtend z) = φ.torusHom (G.incFaceRawEval 0 z) := by
  rw [incFaceRawEval_apply, incFaceRawEval_apply, totalExtend_apply,
    φ.incFaceAmbientToTorus_cechExtend hφ]

/-! ## The chain map of the actual free resolutions -/

/-- The pullback of the finite free resolution modules: the perturbed inclusion of `G`, the total
pullback, and the perturbed projection of `H`. -/
noncomputable def resolutionExtend :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E]
      (H.IncResolutionBasis →₀ IncCoeffRing E) :=
  H.incResolutionProjection.comp (φ.totalExtend.comp G.incResolutionInclusion)

theorem resolutionExtend_apply (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    φ.resolutionExtend x =
      H.incResolutionProjection (φ.totalExtend (G.incResolutionInclusion x)) := rfl

include hφ in
/-- The resolution pullback is a chain map. -/
theorem resolutionExtend_differential (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incResolutionDifferential (φ.resolutionExtend x) =
      φ.resolutionExtend (G.incResolutionDifferential x) := by
  rw [resolutionExtend_apply, resolutionExtend_apply,
    ← LinearMap.comp_apply H.incResolutionDifferential H.incResolutionProjection,
    ← H.incResolutionProjection_chain, LinearMap.comp_apply, ← φ.totalExtend_differential hφ,
    ← LinearMap.comp_apply G.incTotalDifferential G.incResolutionInclusion,
    G.incResolutionInclusion_chain, LinearMap.comp_apply]

include hφ in
/-- The resolution pullback preserves homological degrees. -/
theorem resolutionExtend_degree (n : ℕ) {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n) :
    φ.resolutionExtend x ∈ gradedPiece (IncCoeffRing E) H.incResolutionDegree n :=
  H.incResolutionProjection_degree n _
    (φ.totalExtend_mem_incTotalPiece hφ (G.incResolutionInclusion_degree n x hx))

include hφ in
/-- In degree zero the resolution pullback lifts the torus map through the augmentations. -/
theorem resolutionExtend_torusAugmentation {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    H.incResolutionTorusAugmentation (φ.resolutionExtend x) =
      φ.torusHom (G.incResolutionTorusAugmentation x) := by
  have hcycle : H.incTotalDifferential (φ.totalExtend (G.incResolutionInclusion x)) = 0 := by
    rw [← φ.totalExtend_differential hφ,
      show G.incTotalDifferential (G.incResolutionInclusion x) =
        G.incResolutionInclusion (G.incResolutionDifferential x) from
          LinearMap.congr_fun G.incResolutionInclusion_chain x,
      G.incResolutionDifferential_zero_degree x hx, map_zero, map_zero]
  change H.incFaceRawEval 0 (H.incResolutionInclusion (φ.resolutionExtend x)) =
    φ.torusHom (G.incFaceRawEval 0 (G.incResolutionInclusion x))
  rw [resolutionExtend_apply, H.incFaceRawEval_inclusion_projection hcycle,
    φ.incFaceRawEval_totalExtend hφ]

/-- The resolution pullback on one homological term of the actual free resolutions. -/
noncomputable def freeTermExtend (n : ℕ) :
    G.IncFreeTerm n →ₗ[IncCoeffRing E] H.IncFreeTerm n where
  toFun x := ⟨φ.resolutionExtend x.val, φ.resolutionExtend_degree hφ n x.property⟩
  map_add' x y := Subtype.ext (map_add φ.resolutionExtend x.val y.val)
  map_smul' r x := Subtype.ext (map_smul φ.resolutionExtend r x.val)

@[simp] theorem freeTermExtend_val (n : ℕ) (x : G.IncFreeTerm n) :
    (φ.freeTermExtend hφ n x).val = φ.resolutionExtend x.val := rfl

/-- The termwise pullback commutes with the differentials of the actual free resolutions. -/
theorem freeTermExtend_differential (n : ℕ) (x : G.IncFreeTerm (n + 1)) :
    H.incFreeTermDifferential n (φ.freeTermExtend hφ (n + 1) x) =
      φ.freeTermExtend hφ n (G.incFreeTermDifferential n x) := by
  apply Subtype.ext
  exact φ.resolutionExtend_differential hφ x.val

/-- In degree zero the termwise pullback lifts the incidence ring map through the
augmentations. -/
theorem freeTermExtend_augmentation (x : G.IncFreeTerm 0) :
    H.incResolutionAugmentation (φ.freeTermExtend hφ 0 x) =
      φ.incidenceHom (G.incResolutionAugmentation x) := by
  apply Subtype.ext
  exact φ.resolutionExtend_torusAugmentation hφ x.property

/-- The pullback chain map of the actual free resolutions. -/
noncomputable def resolutionExtendChainMap :
    G.incFreeResolution.complex ⟶ H.incFreeResolution.complex where
  f n := ModuleCat.ofHom (φ.freeTermExtend hφ n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    ext x
    change H.incFreeResolution.complex.d (j + 1) j (φ.freeTermExtend hφ (j + 1) x) =
      φ.freeTermExtend hφ j (G.incFreeResolution.complex.d (j + 1) j x)
    rw [incFreeResolution_d, incFreeResolution_d]
    exact φ.freeTermExtend_differential hφ j x

/-- The pullback chain map lifts the incidence module map. -/
theorem resolutionExtendChainMap_comm_zero :
    (φ.resolutionExtendChainMap hφ).f 0 ≫ H.incFreeResolution.π.f 0 =
      G.incFreeResolution.π.f 0 ≫ φ.incidenceModuleHom := by
  ext x
  change H.incResolutionAugmentation (φ.freeTermExtend hφ 0 x) =
    φ.incidenceHom (G.incResolutionAugmentation x)
  exact φ.freeTermExtend_augmentation hφ x

/-- The Tor map of an injective vertex map is computed by the pullback chain map. -/
theorem incidenceTorHom_eq_extend (p : ℕ) :
    φ.incidenceTorHom p =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).map (φ.resolutionExtendChainMap hφ)) p ≫
          (H.incFreeResolution.isoLeftDerivedObj
            (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).inv := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality φ.incidenceModuleHom
    G.incFreeResolution H.incFreeResolution (φ.resolutionExtendChainMap hφ)
    (φ.resolutionExtendChainMap_comm_zero hφ)
    (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p
  rw [← Iso.eq_comp_inv] at h
  rw [incidenceTorHom, h]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc]

/-- In free-term coordinates the Tor map is the specialization of the pullback chain map. -/
theorem incidenceTorIsoFreeTerm_extend (p : ℕ) :
    φ.incidenceTorHom p ≫ (H.incidenceTorIsoFreeTerm p).hom =
      (G.incidenceTorIsoFreeTerm p).hom ≫
        (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).map
          ((φ.resolutionExtendChainMap hφ).f p) := by
  have hG : (G.incidenceTorIsoFreeTerm p).hom =
      (G.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).obj G.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (G.incFreeResolution_minimal i j)) p).hom := rfl
  have hH : (H.incidenceTorIsoFreeTerm p).hom =
      (H.incFreeResolution.isoLeftDerivedObj
          (ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)) p).hom ≫
        (homologyIsoTermOfZeroDifferentials
          (((ModuleCat.extendScalars (constantCoeff : IncCoeffRing E →+* ℂ)).mapHomologicalComplex
            _).obj H.incFreeResolution.complex)
          (fun i j => extendScalars_map_eq_zero _ _ (H.incFreeResolution_minimal i j)) p).hom := rfl
  rw [hG, hH, φ.incidenceTorHom_eq_extend hφ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [homologyIsoTermOfZeroDifferentials_naturality]
  rfl

/-- The Tor map sends the specialization of a free-resolution element to the specialization of its
pullback. -/
theorem incidenceTorMap_class_extend (p : ℕ) (x : G.IncFreeTerm p) :
    φ.incidenceTorMap p (G.incFreeTermToTor p x) =
      H.incFreeTermToTor p (φ.freeTermExtend hφ p x) := by
  apply (H.incidenceTorIsoFreeTerm p).toLinearEquiv.injective
  change (H.incidenceTorIsoFreeTerm p).hom ((φ.incidenceTorHom p) (G.incFreeTermToTor p x)) =
    (H.incidenceTorIsoFreeTerm p).hom (H.incFreeTermToTor p (φ.freeTermExtend hφ p x))
  rw [← ConcreteCategory.comp_apply, φ.incidenceTorIsoFreeTerm_extend hφ,
    ConcreteCategory.comp_apply, incFreeTermToTor_eq_tmul, incFreeTermToTor_eq_tmul]
  rfl

/-! ## Resolution states -/

/-- **The restriction of a resolution state** of `H` to `G` along an injective vertex map: the edge
set is kept and the local index at `v` is the index at `φ v`. -/
def statePull (b : H.IncResolutionBasis) : G.IncResolutionBasis :=
  ⟨b.1, hPull (φ.deg_vertex_of_injective hφ b.1) b.2⟩

@[simp] theorem statePull_fst (b : H.IncResolutionBasis) : (φ.statePull hφ b).1 = b.1 := rfl

theorem statePull_snd_val (b : H.IncResolutionBasis) (v : V) :
    ((φ.statePull hφ b).2 v).val = (b.2 (φ.vertex v)).val := rfl

/-- Restriction of states is injective: off the image the twist is zero and only the `H⁰` index
occurs. -/
theorem statePull_injective : Function.Injective (φ.statePull hφ) := by
  rintro ⟨S, κ⟩ ⟨T, κ'⟩ h
  have hST : S = T := congrArg Sigma.fst h
  subst hST
  have hκ : hPull (φ.deg_vertex_of_injective hφ S) κ = hPull (φ.deg_vertex_of_injective hφ S) κ' :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  congr 1
  funext w
  apply Fin.ext
  by_cases hw : ∃ v, φ.vertex v = w
  · obtain ⟨v, rfl⟩ := hw
    have h1 := congrArg Fin.val (congrFun hκ v)
    exact h1
  · push Not at hw
    have h1 : phi (H.deg S w) = 1 := by rw [φ.deg_eq_zero_of_not_mem_range S hw, phi_zero]
    have hlt := (κ w).isLt
    have hlt' := (κ' w).isLt
    omega

include hφ in
/-- The numbers of resolution states of `G` and `H` agree. -/
theorem card_incResolutionBasis_of_injective :
    Fintype.card H.IncResolutionBasis = Fintype.card G.IncResolutionBasis := by
  rw [Fintype.card_sigma, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun S _ => φ.card_stateFibre_eq_of_injOn hφ.injOn

/-- Restriction of states is bijective. -/
theorem statePull_bijective : Function.Bijective (φ.statePull hφ) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨φ.statePull_injective hφ, φ.card_incResolutionBasis_of_injective hφ⟩

/-- The bijection of resolution states of an injective vertex map. -/
noncomputable def stateEquiv : H.IncResolutionBasis ≃ G.IncResolutionBasis :=
  Equiv.ofBijective _ (φ.statePull_bijective hφ)

@[simp] theorem stateEquiv_apply (b : H.IncResolutionBasis) :
    φ.stateEquiv hφ b = φ.statePull hφ b := rfl

@[simp] theorem stateEquiv_symm_fst (b : G.IncResolutionBasis) :
    ((φ.stateEquiv hφ).symm b).1 = b.1 := by
  conv_rhs => rw [← (φ.stateEquiv hφ).apply_symm_apply b]
  rfl

variable (R : Type) [CommRing R]

/-- **The signed state map** of an injective vertex map: the state `⟨S, κ⟩` of `G` goes to the
Koszul sign of the twist support of `S` times the state of `H` restricting to it. -/
noncomputable def statePush : (G.IncResolutionBasis →₀ R) →ₗ[R] (H.IncResolutionBasis →₀ R) :=
  Finsupp.lsum R fun b => vertexMapSign R φ.vertex (twistSupport (G.deg b.1)) •
    Finsupp.lsingle ((φ.stateEquiv hφ).symm b)

theorem statePush_single (b : G.IncResolutionBasis) (r : R) :
    φ.statePush hφ R (single b r) =
      single ((φ.stateEquiv hφ).symm b)
        (vertexMapSign R φ.vertex (twistSupport (G.deg b.1)) * r) := by
  simp [statePush, Finsupp.smul_single, smul_eq_mul]

/-- **Coefficients of the signed state map**: at a state of `H` it reads the sign times the
coefficient at the restricted state. -/
theorem statePush_apply (z : G.IncResolutionBasis →₀ R) (b : H.IncResolutionBasis) :
    φ.statePush hφ R z b =
      vertexMapSign R φ.vertex (twistSupport (G.deg b.1)) * z (φ.statePull hφ b) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single a r =>
    rw [statePush_single]
    by_cases ha : a = φ.statePull hφ b
    · subst ha
      have hb : (φ.stateEquiv hφ).symm (φ.statePull hφ b) = b :=
        (φ.stateEquiv hφ).symm_apply_apply b
      rw [hb, single_eq_same, single_eq_same, statePull_fst]
    · rw [single_eq_of_ne, single_eq_of_ne (Ne.symm ha), mul_zero]
      intro h
      apply ha
      rw [h]
      exact ((φ.stateEquiv hφ).apply_symm_apply a).symm

/-- Coefficientwise ring change commutes with the signed state map. -/
theorem statePush_mapRange {R' : Type} [CommRing R'] (f : R →+* R')
    (z : G.IncResolutionBasis →₀ R) :
    φ.statePush hφ R' (mapRange f (map_zero f) z) =
      mapRange f (map_zero f) (φ.statePush hφ R z) := by
  ext b
  rw [statePush_apply, mapRange_apply, mapRange_apply, statePush_apply, map_mul,
    map_vertexMapSign]

/-- Included states, pulled back and projected, are the signed state map of the states. -/
theorem incCechContraction_p_totalExtend_i (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    H.incCechContraction.p (φ.totalExtend (G.incCechContraction.i x)) =
      φ.statePush hφ (IncCoeffRing E) x := by
  refine Finsupp.ext fun b => ?_
  obtain ⟨S, κ⟩ := b
  rw [statePush_apply]
  change (CechProduct.contraction (IncCoeffRing E) (H.deg S)).p
    ((φ.totalExtend (G.incCechContraction.i x)) S) κ = _
  rw [totalExtend_apply]
  change (CechProduct.contraction (IncCoeffRing E) (H.deg S)).p
    (cechExtend (IncCoeffRing E) φ.vertex ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).i
      ((Finsupp.sigmaFinsuppLEquivPiFinsupp (IncCoeffRing E)) x S))) κ = _
  rw [contraction_p_cechExtend_i (IncCoeffRing E) hφ (G.deg S) (H.deg S)
    (φ.deg_vertex_of_injective hφ S) (fun w hw => φ.deg_eq_zero_of_not_mem_range S hw),
    sigmaFinsuppLEquivPiFinsupp_apply]
  rfl

/-- **At the coefficient origin the resolution pullback is the signed state map.** -/
theorem mapRange_resolutionExtend (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) (φ.resolutionExtend x) =
      φ.statePush hφ ℂ (mapRange (constantCoeff : IncCoeffRing E →+* ℂ) (map_zero _) x) := by
  have hI : G.incResolutionInclusion x - G.incCechContraction.i x ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
      G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have ha : H.incResolutionProjection (φ.totalExtend (G.incResolutionInclusion x)) -
      H.incCechContraction.p (φ.totalExtend (G.incResolutionInclusion x)) ∈
      incCoeffAugmentationIdeal E • ⊤ :=
    H.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E)
      H.incKoszulPerturbation H.incKoszulPerturbation_mem_augmentation
      (φ.totalExtend (G.incResolutionInclusion x))
  have hb := map_mem_ideal_smul_top (incCoeffAugmentationIdeal E)
    (H.incCechContraction.p.comp φ.totalExtend) hI
  rw [map_sub (H.incCechContraction.p.comp φ.totalExtend)] at hb
  simp only [LinearMap.comp_apply] at hb
  have hsum := Submodule.add_mem _ ha hb
  rw [sub_add_sub_cancel] at hsum
  have h0 := EdgeRelabel.mapRange_constantCoeff_eq_zero hsum
  rw [mapRange_sub (map_sub _), sub_eq_zero] at h0
  rw [resolutionExtend_apply, h0, φ.incCechContraction_p_totalExtend_i hφ,
    ← statePush_mapRange]

/-! ## The state formula -/

/-- **State formula for injective vertex maps.** The full state vector of the image of a Tor class
under the Tor map of an injective vertex map is the signed state map of its full state vector. -/
theorem incidenceTorFullState_vertexMap_of_injective (p : ℕ) (y : G.incidenceTor p) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) =
      φ.statePush hφ ℂ (G.incidenceTorFullState p y) := by
  obtain ⟨x, rfl⟩ := G.incFreeTermToTor_surjective p y
  rw [φ.incidenceTorMap_class_extend hφ, incidenceTorFullState_class, incidenceTorFullState_class,
    freeTermExtend_val, mapRange_resolutionExtend]

/-- **State formula for injective vertex maps, in coordinates.** The coefficient of the image at the
state `⟨S, κ⟩` of `H` is the Koszul sign of the twist support of `S` times the coefficient of the
class at the restricted state of `G`. -/
theorem incidenceTorFullState_vertexMap_apply_of_injective (p : ℕ) (y : G.incidenceTor p)
    (b : H.IncResolutionBasis) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
      vertexMapSign ℂ φ.vertex (twistSupport (G.deg b.1)) *
        G.incidenceTorFullState p y (φ.statePull hφ b) := by
  rw [φ.incidenceTorFullState_vertexMap_of_injective hφ, statePush_apply]

include hφ in
/-- Every Tor class of `H` is the image of a Tor class of `G` under the Tor map of an injective
vertex map. -/
theorem incidenceTorMap_surjective_of_injective (p : ℕ) :
    Function.Surjective (φ.incidenceTorMap p) := by
  intro y
  let z : G.IncResolutionBasis →₀ ℂ := Finsupp.equivFunOnFinite.symm fun a =>
    vertexMapSign ℂ φ.vertex (twistSupport (G.deg a.1)) *
      H.incidenceTorFullState p y ((φ.stateEquiv hφ).symm a)
  have hz : ∀ a : G.IncResolutionBasis, G.incResolutionDegree a ≠ p → z a = 0 := by
    intro a ha
    change vertexMapSign ℂ φ.vertex (twistSupport (G.deg a.1)) *
      H.incidenceTorFullState p y ((φ.stateEquiv hφ).symm a) = 0
    rw [H.incidenceTorFullState_apply_of_ne p y _ ?_, mul_zero]
    intro hdeg
    apply ha
    rw [← hdeg]
    unfold incResolutionDegree
    rw [stateEquiv_symm_fst, φ.support_eq_image, Finset.card_image_of_injective _ hφ]
  obtain ⟨x, hx⟩ := G.exists_incidenceTorFullState_eq p z hz
  refine ⟨x, H.incidenceTorFullState_injective p ?_⟩
  ext b
  rw [φ.incidenceTorFullState_vertexMap_apply_of_injective hφ, hx]
  change vertexMapSign ℂ φ.vertex (twistSupport (G.deg b.1)) *
    (vertexMapSign ℂ φ.vertex (twistSupport (G.deg (φ.statePull hφ b).1)) *
      H.incidenceTorFullState p y ((φ.stateEquiv hφ).symm (φ.statePull hφ b))) = _
  have hb : (φ.stateEquiv hφ).symm (φ.statePull hφ b) = b := (φ.stateEquiv hφ).symm_apply_apply b
  rw [hb, statePull_fst, ← mul_assoc, vertexMapSign_mul_self, one_mul]

end VertexMap

end BPFixedPoints.Multigraph
