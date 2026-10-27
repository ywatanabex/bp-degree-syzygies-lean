import BPFixedPoints.Incidence.VertexMapPullbackTwist
import BPFixedPoints.Incidence.IncidenceVertexMapStateFormula
import BPFixedPoints.Incidence.IncidenceTorExteriorIsomorphism

/-!
# The geometric map of exterior cohomology of a vertex map: states and naturality

Let `φ : VertexMap G H` and let `φ.exteriorCohomologyPullback` be the map of exterior cohomology
induced by the coordinate map `a_φ` (`VertexMapPullbackTwist`, built from the actual morphism of
schemes; it is not defined through states). Its state vector is computed here as far as the
available multi-twist information allows, and compared with the Tor map `φ.incidenceTorMap`
through the Tor–cohomology isomorphism `incidenceTorExteriorEquiv`.

**Colliding states, unconditionally.** At every state `b` of `H` whose edge set has a vertex
support in `G` on which `φ` is not injective, the state coordinate of the geometric image vanishes
(`exteriorCohomologyState_pullback_of_not_injOn`): the summand of that edge set is sent by the
multi-twist pullback into a cohomology group concentrated in a smaller degree. Consequently the
naturality square of `incidenceTorExteriorEquiv` holds on every colliding edge-set piece, both sides
being zero (`incidenceTorExteriorEquiv_vertexMap_of_not_injOn`).

**Non-colliding states, from the multi-twist formula.** `VertexMapTwistStateFormula R f` is the
statement that, for a nonnegative twist `d` on `V` whose support is not collided by `f`, the state
coordinates of the multi-twist pullback (`vertexTwistHPullback`) are the Koszul sign
`vertexMapSign R f (twistSupport d)` times the state coordinates at the pulled-back index
(`hPullTwist`). It is proved as `vertexMapTwistStateFormula` in
`VertexMapTwistStateFormula.lean`, where the unconditional forms are stated. From it:
* the exterior state formula (`exteriorCohomologyState_pullback_of`) has the same sign and the same
  restriction of states as the Tor-side formula `incidenceTorFullState_vertexMap_apply_of_injOn`;
* **the naturality square** of `incidenceTorExteriorEquiv` for vertex maps holds
  (`incidenceTorExteriorEquiv_vertexMap_of`).

Not proved here: `VertexMapTwistStateFormula` itself. It needs the effect of the inverse image of
abelian sheaves on the cubical-cell Yoneda representatives of multi-twist cohomology (for a
projection: tensoring with the augmentation on the coordinates off the image; for identified
coordinates: an Alexander–Whitney diagonal), which is not formalized.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Finsupp CechProduct
open ProjectiveLine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable local instance vertexMapExteriorHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-! ## Coefficients of exterior state vectors -/

section Coefficients

variable {U E : Type} [DecidableEq U] [Fintype U] [LinearOrder E] [Fintype E] (K : Multigraph U E)
  (R : Type) [CommRing R] [IsNoetherianRing R]

/-- The coefficient of the state vector of an exterior class at a state of the edge set `S` is the
state coordinate of the summand projection of `S`. -/
theorem exteriorCohomologyState_apply_summand (q j : ℕ)
    (z : Sheaf.H.{1} (K.exteriorBundleAbelian R q) j) (S : Set.powersetCard E q)
    (κ : HBasis (K.deg S)) :
    K.exteriorCohomologyState R q j z ⟨S, κ⟩ =
      (vertexTwistActualStateAt R U (K.deg S) j
        (Sheaf.H.map (K.exteriorProj R q S) j z)).val κ := by
  rw [exteriorCohomologyState_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (f := fun T : Set.powersetCard E q => K.incStateEmbed R T
      (vertexTwistActualStateAt R U (K.deg T) j (Sheaf.H.map (K.exteriorProj R q T) j z)).val
        ⟨S, κ⟩) S]
  · exact K.incStateEmbed_apply_same R S _ κ
  · intro T _ hT
    exact K.incStateEmbed_apply_of_ne R (fun h => hT (Subtype.ext h)) _ κ
  · intro h
    exact absurd (Finset.mem_univ S) h

/-- The state vector of a class of the `q`-th exterior bundle vanishes at states whose edge set
does not have `q` elements. -/
theorem exteriorCohomologyState_apply_of_card_ne (q j : ℕ)
    (z : Sheaf.H.{1} (K.exteriorBundleAbelian R q) j) (b : K.IncResolutionBasis)
    (hb : b.1.card ≠ q) : K.exteriorCohomologyState R q j z b = 0 := by
  rw [exteriorCohomologyState_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun T _ => ?_
  obtain ⟨S, κ⟩ := b
  refine K.incStateEmbed_apply_of_ne R (fun h => hb ?_) _ κ
  change S.card = q
  rw [← h]
  exact Set.powersetCard.card_eq T

/-- A summand projection vanishes when the state vector vanishes on the states of its edge set. -/
theorem exteriorProj_eq_zero_of_state (q j : ℕ) (z : Sheaf.H.{1} (K.exteriorBundleAbelian R q) j)
    (S : Set.powersetCard E q)
    (h : ∀ κ : HBasis (K.deg S), K.exteriorCohomologyState R q j z ⟨S, κ⟩ = 0) :
    Sheaf.H.map (K.exteriorProj R q S) j z = 0 := by
  apply vertexTwistActualStateAt_injective R U (K.deg S) j
  rw [map_zero]
  apply Subtype.ext
  ext κ
  rw [← exteriorCohomologyState_apply_summand]
  exact h κ

end Coefficients

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Colliding states -/

section Colliding

variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- **Colliding states.** The state coordinate of the geometric image of an exterior class vanishes
at every state of `H` whose edge set has a vertex support in `G` on which `φ` is not injective. -/
theorem exteriorCohomologyState_pullback_of_not_injOn (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) (b : H.IncResolutionBasis)
    (h : ¬ Set.InjOn φ.vertex (G.support b.1)) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyPullback R q j x) b = 0 := by
  by_cases hq : b.1.card = q
  · obtain ⟨S, κ⟩ := b
    let T : Set.powersetCard E q := ⟨S, Set.powersetCard.mem_iff.2 hq⟩
    change H.exteriorCohomologyState R q j (φ.exteriorCohomologyPullback R q j x) ⟨T, κ⟩ = 0
    rw [exteriorCohomologyState_apply_summand, φ.exteriorCohomologyPullback_proj R q j T x]
    by_cases hj : j = cohomologyDegree (G.deg T)
    · subst hj
      have hs : twistSupport (G.deg T) = G.support T := by
        ext v
        rw [mem_twistSupport, mem_support_iff, Nat.pos_iff_ne_zero]
      rw [vertexTwistHPullback_eq_zero_of_not_injOn (R := R) (f := φ.vertex) (d := G.deg T)
        (d' := H.deg T) (fun w => φ.deg_eq_sum_fiber T w) (φ.neg_deg_eq_sum_fiber T) (hs ▸ h)]
      simp
    · rw [vertexTwistCohomology_eq_zero_off_degree R V (G.deg T) j (Ne.symm hj)
        (Sheaf.H.map (G.exteriorProj R q T) j x), map_zero]
      simp
  · exact exteriorCohomologyState_apply_of_card_ne H R q j _ b hq

/-- **Naturality on colliding edge-set pieces.** For a Tor class supported on an edge set `S` on
whose vertex support `φ` is not injective, the naturality square of `incidenceTorExteriorEquiv`
holds: both composites are zero. -/
theorem incidenceTorExteriorEquiv_vertexMap_of_not_injOn {S : Finset E}
    (hS : ¬ Set.InjOn φ.vertex (G.support S)) {p q : ℕ} (h : p ≤ q)
    (y : G.incidenceTorInternalPiece p q) (hy : y.val ∈ G.incidenceTorEdgeSetPiece p S) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalVertexMap p q y) =
      φ.exteriorCohomologyPullback ℂ q (q - p) (G.incidenceTorExteriorEquiv h y) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, incidenceTorInternalVertexMap_val]
  ext b
  by_cases hb : b.1 = S
  · rw [φ.incidenceTorMap_eq_zero_of_not_injOn hS hy, map_zero, Finsupp.zero_apply,
      φ.exteriorCohomologyState_pullback_of_not_injOn ℂ q (q - p) _ b (hb ▸ hS)]
  · rw [(H.mem_incidenceTorEdgeSetPiece_iff p S _).1 (φ.incidenceTorMap_mem_edgeSetPiece hy) b hb]
    by_cases hinj : Set.InjOn φ.vertex (G.support b.1)
    · -- the components of the image only see the summand of `b.1`, which vanishes
      by_cases hq : b.1.card = q
      · obtain ⟨T₀, κ⟩ := b
        let T : Set.powersetCard E q := ⟨T₀, Set.powersetCard.mem_iff.2 hq⟩
        change 0 = H.exteriorCohomologyState ℂ q (q - p)
          (φ.exteriorCohomologyPullback ℂ q (q - p) (G.incidenceTorExteriorEquiv h y)) ⟨T, κ⟩
        rw [exteriorCohomologyState_apply_summand, φ.exteriorCohomologyPullback_proj ℂ q _ T,
          exteriorProj_eq_zero_of_state G ℂ q (q - p) _ T, map_zero]
        · simp
        · intro κ'
          rw [exteriorCohomologyState_incidenceTorExteriorEquiv]
          exact (G.mem_incidenceTorEdgeSetPiece_iff p S y.val).1 hy _ hb
      · exact (exteriorCohomologyState_apply_of_card_ne H ℂ q (q - p) _ b hq).symm
    · exact (φ.exteriorCohomologyState_pullback_of_not_injOn ℂ q (q - p) _ b hinj).symm

end Colliding

end VertexMap

/-! ## The multi-twist state formula and the naturality square -/

section Formula

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The pulled-back state index of a twist `d'` on `W` along `f`, for a twist `d` on `V` with
`d' (f v) = d v` on the support of `d`: the index at `f v` on the support of `d`, and the `H⁰`
index elsewhere. -/
def hPullTwist (f : V → W) {d : V → ℕ} {d' : W → ℕ} (hd : ∀ v, d v ≠ 0 → d' (f v) = d v)
    (κ : HBasis d') : HBasis d :=
  fun v => if hv : d v = 0 then ⟨0, by rw [hv, phi_zero]; exact Nat.one_pos⟩
    else Fin.cast (congrArg phi (hd v hv)) (κ (f v))

theorem hPullTwist_val (f : V → W) {d : V → ℕ} {d' : W → ℕ} (hd : ∀ v, d v ≠ 0 → d' (f v) = d v)
    (κ : HBasis d') (v : V) :
    (hPullTwist f hd κ v).val = if d v = 0 then 0 else (κ (f v)).val := by
  unfold hPullTwist
  split_ifs <;> rfl

/-- **The multi-twist state formula for a vertex function** (the statement). For every nonnegative
twist `d` on `V` and its pushforward `d'` on `W` such that `d' (f v) = d v` on the support of `d`
(equivalently: `f` does not identify two vertices of the support), the state coordinates of the
pullback of a class are the Koszul sign of the support times the state coordinates at the
pulled-back index. It is proved as `vertexMapTwistStateFormula`. -/
def VertexMapTwistStateFormula (R : Type) [CommRing R] [IsNoetherianRing R] (f : V → W) : Prop :=
  ∀ (d : V → ℕ) (d' : W → ℕ)
    (hneg : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => f v = w), -(d v : ℤ))
    (hd : ∀ v, d v ≠ 0 → d' (f v) = d v) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) (κ : HBasis d'),
    (vertexTwistActualStateAt R W d' n
        (vertexTwistHPullback R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n x)).val κ =
      vertexMapSign R f (twistSupport d) *
        (vertexTwistActualStateAt R V d n x).val (hPullTwist f hd κ)

end Formula

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

section Conditional

variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- **Exterior state formula, assuming the multi-twist formula.** At a state `b` of `H` whose edge
set has injective vertex support in `G`, the state coordinate of the geometric image is the Koszul
sign `vertexMapSign R φ.vertex (G.support b.1)` times the coordinate of the class at the restricted
state `φ.statePullOn b h`, exactly as on the Tor side. -/
theorem exteriorCohomologyState_pullback_of (hs : VertexMapTwistStateFormula R φ.vertex)
    (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) (b : H.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support b.1)) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyPullback R q j x) b =
      vertexMapSign R φ.vertex (G.support b.1) *
        G.exteriorCohomologyState R q j x (φ.statePullOn b h) := by
  by_cases hq : b.1.card = q
  · obtain ⟨S, κ⟩ := b
    let T : Set.powersetCard E q := ⟨S, Set.powersetCard.mem_iff.2 hq⟩
    have hd : ∀ v, G.deg T v ≠ 0 → H.deg T (φ.vertex v) = G.deg T v := fun v hv =>
      φ.deg_vertex_of_injOn h ((mem_support_iff G).2 (Nat.pos_of_ne_zero hv))
    have hs' : twistSupport (G.deg T) = G.support T := by
      ext v
      rw [mem_twistSupport, mem_support_iff, Nat.pos_iff_ne_zero]
    have hpull : φ.statePullOn ⟨S, κ⟩ h = ⟨T, hPullTwist φ.vertex hd κ⟩ := by
      refine incResolutionBasis_ext rfl fun v => ?_
      rw [statePullOn_snd_val, hPullTwist_val]
      change (if v ∈ G.support T then (κ (φ.vertex v)).val else 0) =
        if G.deg T v = 0 then 0 else (κ (φ.vertex v)).val
      by_cases hv : G.deg T v = 0
      · have hv' : v ∉ G.support T := by rw [mem_support_iff]; omega
        simp only [hv, hv', ↓reduceIte]
      · have hv' : v ∈ G.support T := by rw [mem_support_iff]; omega
        simp only [hv, hv', ↓reduceIte]
    change H.exteriorCohomologyState R q j (φ.exteriorCohomologyPullback R q j x) ⟨T, κ⟩ =
      vertexMapSign R φ.vertex (G.support T) * G.exteriorCohomologyState R q j x
        (φ.statePullOn ⟨S, κ⟩ h)
    rw [hpull, exteriorCohomologyState_apply_summand, φ.exteriorCohomologyPullback_proj R q j T,
      exteriorCohomologyState_apply_summand, hs (G.deg T) (H.deg T) (φ.neg_deg_eq_sum_fiber T) hd,
      hs']
  · rw [exteriorCohomologyState_apply_of_card_ne H R q j _ b hq,
      exteriorCohomologyState_apply_of_card_ne G R q j _ _ hq, mul_zero]

/-- **The naturality square for vertex maps, assuming the multi-twist formula.** The Tor-to-exterior
isomorphism carries the Tor map of a vertex map (Mathlib's derived functor functoriality) to the
geometric map of exterior cohomology induced by the coordinate map `a_φ`. -/
theorem incidenceTorExteriorEquiv_vertexMap_of (hs : VertexMapTwistStateFormula ℂ φ.vertex)
    {p q : ℕ} (h : p ≤ q) (y : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalVertexMap p q y) =
      φ.exteriorCohomologyPullback ℂ q (q - p) (G.incidenceTorExteriorEquiv h y) := by
  apply H.exteriorCohomologyState_injective ℂ q (q - p)
  rw [exteriorCohomologyState_incidenceTorExteriorEquiv, incidenceTorInternalVertexMap_val]
  ext b
  by_cases hinj : Set.InjOn φ.vertex (G.support b.1)
  · rw [φ.incidenceTorFullState_vertexMap_apply_of_injOn p y.val b hinj,
      φ.exteriorCohomologyState_pullback_of ℂ hs q (q - p) _ b hinj,
      exteriorCohomologyState_incidenceTorExteriorEquiv]
  · rw [φ.exteriorCohomologyState_pullback_of_not_injOn ℂ q (q - p) _ b hinj,
      φ.incidenceTorFullState_vertexMap_component p y.val b,
      φ.incidenceTorMap_eq_zero_of_not_injOn hinj (G.incidenceTorEdgeSetComponent_mem p b.1 y.val),
      map_zero, Finsupp.zero_apply]

end Conditional

end VertexMap

end BPFixedPoints.Multigraph
