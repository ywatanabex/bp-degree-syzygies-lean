import BPFixedPoints.Incidence.DerivedRingMap
import BPFixedPoints.Incidence.IncidenceEdgeSignTor
import BPFixedPoints.Incidence.IncidenceVertexMapCycles

/-!
# Vertex maps in all Tor degrees: edge signs, edge-set components and collisions

Let `φ : VertexMap G H` be a vertex map (edges unchanged, vertices possibly identified) and let
`ε : E → ℤˣ` be an edge sign. This file extends the degree-zero sign-character argument of
`IncidenceVertexMapCycles` to every homological degree. Everything is purely algebraic on the Tor
side: no Tor–cohomology comparison and no naturality of it for vertex maps is used.

**Sign compatibility in every degree.** The Tor map of `φ` commutes with the Tor automorphisms of
every edge sign (`incidenceTorHom_comp_signIso`, `incidenceTorMap_sign`). Both composites are
derived ring maps: the Tor map of `φ` is the derived ring map along the identity of the
coefficient ring (`derivedRingMap_id_eq_map`, `incidenceTorHom_eq_derivedRingMap`), the sign
automorphism is the derived ring map along the coefficient sign change
(`derivedRingChange_hom_eq_derivedRingMap`), and the two composites are derived ring maps along
the same ring homomorphism of elementwise equal module maps, by the ring-side commutation
`incidenceHom_edgeSignIncidence` (`leftDerived_map_comp_derivedRingMap`, a naturality statement for
`derivedRingMap` in the module variable over fixed rings).

**Edge-set pieces.** `incidenceTorEdgeSetPiece p S` is the subspace of Tor classes whose full state
vector is supported on basis states with edge set `S`. Over `ℂ` it is exactly the simultaneous
eigenspace of the edge-sign automorphisms with character `ε ↦ ∏_{e ∈ S} ε_e`
(`mem_incidenceTorEdgeSetPiece_iff_sign`); the converse direction flips one edge of a symmetric
difference and divides by `2` (`eq_zero_of_setSign_mul_eq`). Every class is the sum of its
edge-set components (`incidenceTorEdgeSetComponent`, `sum_incidenceTorEdgeSetComponent`).

**Consequences for vertex maps (over `ℂ`).**
* The Tor map preserves edge-set pieces (`incidenceTorMap_mem_edgeSetPiece`; in coordinates
  `incidenceTorFullState_vertexMap_eq_zero_of_fst_ne`) and commutes with taking edge-set
  components (`incidenceTorMap_edgeSetComponent`).
* It preserves the internal degree `|S|`, hence every bigraded piece
  (`incidenceTorMap_mem_internalPiece`, `incidenceTorInternalVertexMap`).
* **Collision vanishing.** If the vertex function is not injective on `G.support S`, then
  `H.support S = φ(G.support S)` is strictly smaller, so every state of `H` with edge set `S` has
  homological degree `|S| - |H.support S|` strictly larger than the degree `|S| - |G.support S|` of
  the states of `G` with edge set `S` (`incResolutionDegree_lt_of_not_injOn`). Hence the Tor map
  kills every class supported on `S` (`incidenceTorMap_eq_zero_of_not_injOn`), in particular every
  class whose full state is a multiple of a single basis state of `S`
  (`incidenceTorMap_eq_zero_of_fullState_single`).
* **No collision.** If the vertex function is injective on `G.support S`, states of `H` with edge
  set `S` have the same homological degree as those of `G` (`incResolutionDegree_eq_of_injOn`), the
  number of basis states over `S` is the same in `G` and `H` (`card_stateFibre_eq_of_injOn`), and
  the image of a class supported on `S` is supported on states of `H` with edge set `S` of that
  degree (`incidenceTorMap_fullState_support_of_injOn`).

Not covered here: the scalar by which a basis state is sent to the corresponding state of `H` in the
non-colliding case (not even its nonvanishing in positive homological degrees), an explicit
bijection between the basis states of `G` and of `H` over `S` (only their numbers are compared), a
state formula for the Tor map, characteristic-free versions of the edge-set statements (the argument divides by
`2`), and anything on the cohomology or sheaf side. The degree-zero consequences for the
cycle-compatibility algebras are in `IncidenceVertexMapSupportCycles`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp MvPolynomial

/-! ## Derived ring maps along the identity and naturality in the module variable -/

/-- **Derived ring maps along the identity.** The derived ring map along the identity ring
homomorphism of a module map `g` (composed with the identification of a module with its
restriction along the identity) is Mathlib's functoriality of the left derived functor applied to
`g`. This extends `derivedRingMap_id`, which treats only the identity module map. -/
theorem derivedRingMap_id_eq_map {R k : Type} [CommRing R] [CommRing k] (ε : R →+* k)
    {M M' : ModuleCat.{0} R} (g : M ⟶ M') (n : ℕ) :
    derivedRingMap (RingHom.id R) ε ε (RingHom.comp_id ε)
        (g ≫ (ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app M') n =
      ((ModuleCat.extendScalars ε).leftDerived n).map g := by
  let P := projectiveResolution M
  let Q := projectiveResolution M'
  let c := ProjectiveResolution.lift g P Q
  have hc : c.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ g := ProjectiveResolution.lift_commutes_zero _ _ _
  rw [derivedRingMap_eq (RingHom.id R) ε ε (RingHom.comp_id ε) _ P Q
    (c ≫ restrictIdComplexHom Q.complex) (by
      ext x
      exact congrArg (fun f => f.hom x) hc)]
  have hid : ((ModuleCat.extendScalars ε).mapHomologicalComplex _).map
      (restrictIdComplexHom Q.complex) ≫
        restrictExtendComplexHom (RingHom.id R) ε ε (RingHom.comp_id ε) Q.complex = 𝟙 _ := by
    ext i : 1
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rfl
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality g P Q c hc
    (ModuleCat.extendScalars ε) n
  rw [← Iso.eq_comp_inv] at h
  rw [h, Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc,
    ← HomologicalComplex.homologyMap_comp_assoc
      (((ModuleCat.extendScalars ε).mapHomologicalComplex _).map (restrictIdComplexHom Q.complex)),
    hid, HomologicalComplex.homologyMap_id, Category.id_comp]
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map, Category.assoc]

/-- The derived ring map along equal ring homomorphisms of elementwise equal module maps. -/
theorem derivedRingMap_congr {R R' k : Type} [CommRing R] [CommRing R'] [CommRing k]
    {f f' : R →+* R'} (hf : f = f') (ε : R →+* k) (ε' : R' →+* k) (hε : ε'.comp f = ε)
    (hε' : ε'.comp f' = ε) {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj M')
    (g' : M ⟶ (ModuleCat.restrictScalars f').obj M')
    (hg : ∀ x, g' x = g x) (n : ℕ) :
    derivedRingMap f ε ε' hε g n = derivedRingMap f' ε ε' hε' g' n := by
  subst hf
  have h : g' = g := by
    ext x
    exact hg x
  subst h
  rfl

/-- **Naturality of the derived ring map in the module variable.** Let `f : R → R'` be compatible
with the augmentations, `g : M → N` an `R`-linear map, `g' : M' → N'` an `R'`-linear map, and
`a : M → M'`, `b : N → N'` maps along `f` with `b ∘ g = g' ∘ a` elementwise. Then the square of
left derived functors commutes: `L(g) ≫ D(b) = D(a) ≫ L(g')`, where `D` is `derivedRingMap` and
`L` is Mathlib's functoriality of the left derived functors over `R` and `R'`. -/
theorem leftDerived_map_comp_derivedRingMap {R R' k : Type} [CommRing R] [CommRing R']
    [CommRing k] (f : R →+* R') (ε : R →+* k) (ε' : R' →+* k) (hε : ε'.comp f = ε)
    {M N : ModuleCat.{0} R} {M' N' : ModuleCat.{0} R'} (g : M ⟶ N) (g' : M' ⟶ N')
    (a : M ⟶ (ModuleCat.restrictScalars f).obj M')
    (b : N ⟶ (ModuleCat.restrictScalars f).obj N')
    (hab : ∀ x, b (g x) = g' (a x)) (n : ℕ) :
    ((ModuleCat.extendScalars ε).leftDerived n).map g ≫ derivedRingMap f ε ε' hε b n =
      derivedRingMap f ε ε' hε a n ≫ ((ModuleCat.extendScalars ε').leftDerived n).map g' := by
  rw [← derivedRingMap_id_eq_map ε g, ← derivedRingMap_id_eq_map ε' g',
    ← derivedRingMap_comp (RingHom.id R) ε ε (RingHom.comp_id ε) _ f ε' hε b,
    ← derivedRingMap_comp f ε ε' hε a (RingHom.id R') ε' (RingHom.comp_id ε') _]
  exact derivedRingMap_congr (RingHom.ext fun _ => rfl) ε ε' _ _ _ _ (fun x => (hab x).symm) n

/-! ## Edge-set pieces of Tor -/

section EdgeSetPieces

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- **Edge-sign characters separate edge sets.** If `∏_{e ∈ T} ε_e · c = ∏_{e ∈ S} ε_e · c` for
every edge sign `ε` and `T ≠ S`, then `c = 0`: flipping one edge of the symmetric difference gives
`c = -c`, and `2` is invertible in `ℂ`. -/
theorem eq_zero_of_setSign_mul_eq {S T : Finset E} (hST : T ≠ S) {c : ℂ}
    (h : ∀ ε : EdgeSign E, ε.setSign ℂ T * c = ε.setSign ℂ S * c) : c = 0 := by
  obtain ⟨e, he⟩ : ∃ e, ¬ (e ∈ T ↔ e ∈ S) := by
    by_contra h'
    push Not at h'
    exact hST (Finset.ext h')
  have h1 := h (singleEdgeSign e)
  rw [setSign_singleEdgeSign, setSign_singleEdgeSign] at h1
  by_cases hT : e ∈ T
  · have hS : e ∉ S := fun hS => he (iff_of_true hT hS)
    simp only [hT, hS, ite_true, ite_false] at h1
    linear_combination -h1 / 2
  · have hS : e ∈ S := by
      by_contra hS
      exact he (iff_of_false hT hS)
    simp only [hT, hS, ite_true, ite_false] at h1
    linear_combination h1 / 2

/-- **The edge-set piece** of `Tor_p`: the Tor classes whose full state vector vanishes at every
basis state whose edge set is not `S`. -/
noncomputable def incidenceTorEdgeSetPiece (p : ℕ) (S : Finset E) :
    Submodule ℂ (G.incidenceTor p) :=
  (Finsupp.supported ℂ ℂ {b : G.IncResolutionBasis | b.1 = S}).comap (G.incidenceTorFullState p)

theorem mem_incidenceTorEdgeSetPiece_iff (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    y ∈ G.incidenceTorEdgeSetPiece p S ↔
      ∀ b : G.IncResolutionBasis, b.1 ≠ S → G.incidenceTorFullState p y b = 0 := by
  rw [incidenceTorEdgeSetPiece, Submodule.mem_comap, Finsupp.mem_supported']
  rfl

/-- A class whose full state is a multiple of one basis state lies in the edge-set piece of the
edge set of that state. -/
theorem mem_incidenceTorEdgeSetPiece_of_fullState_single {p : ℕ} {y : G.incidenceTor p}
    {b : G.IncResolutionBasis} {r : ℂ} (hy : G.incidenceTorFullState p y = single b r) :
    y ∈ G.incidenceTorEdgeSetPiece p b.1 := by
  rw [mem_incidenceTorEdgeSetPiece_iff]
  intro b' hb'
  rw [hy, single_eq_of_ne (fun h => hb' (congrArg Sigma.fst h))]

/-- An edge sign acts on the edge-set piece of `S` through the character of `S`. -/
theorem incidenceTorSign_of_mem_edgeSetPiece {p : ℕ} {S : Finset E} {y : G.incidenceTor p}
    (hy : y ∈ G.incidenceTorEdgeSetPiece p S) (ε : EdgeSign E) :
    G.incidenceTorSign ε p y = ε.setSign ℂ S • y := by
  rw [mem_incidenceTorEdgeSetPiece_iff] at hy
  apply G.incidenceTorFullState_injective p
  ext b
  rw [incidenceTorFullState_sign_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hb : b.1 = S
  · rw [hb]
  · rw [hy b hb, mul_zero, mul_zero]

/-- **Edge-set pieces are the sign eigenspaces.** Over `ℂ` a Tor class lies in the edge-set piece
of `S` exactly when every edge sign acts on it by the character `ε ↦ ∏_{e ∈ S} ε_e`. -/
theorem mem_incidenceTorEdgeSetPiece_iff_sign (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    y ∈ G.incidenceTorEdgeSetPiece p S ↔
      ∀ ε : EdgeSign E, G.incidenceTorSign ε p y = ε.setSign ℂ S • y := by
  refine ⟨fun hy ε => G.incidenceTorSign_of_mem_edgeSetPiece hy ε, fun h => ?_⟩
  rw [mem_incidenceTorEdgeSetPiece_iff]
  intro b hb
  apply eq_zero_of_setSign_mul_eq hb
  intro ε
  have h1 := congrArg (fun z => G.incidenceTorFullState p z b) (h ε)
  simp only [incidenceTorFullState_sign_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  exact h1

/-- Every Tor class has a component on each edge set: a class whose full state is the restriction
of its full state to the basis states of that edge set. -/
theorem exists_incidenceTorFullState_eq_filter (p : ℕ) (y : G.incidenceTor p) (S : Finset E) :
    ∃ z : G.incidenceTor p,
      G.incidenceTorFullState p z = (G.incidenceTorFullState p y).filter (fun b => b.1 = S) := by
  apply G.exists_incidenceTorFullState_eq p
  intro b hb
  rw [Finsupp.filter_apply]
  split_ifs
  · exact G.incidenceTorFullState_apply_of_ne p y b hb
  · rfl

/-- **The edge-set component** of a Tor class on the edge set `S`: the class whose full state is
the restriction of the full state of the class to the basis states with edge set `S`. -/
noncomputable def incidenceTorEdgeSetComponent (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    G.incidenceTor p :=
  (G.exists_incidenceTorFullState_eq_filter p y S).choose

/-- The full state of the edge-set component is the restriction of the full state. -/
theorem incidenceTorFullState_edgeSetComponent (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    G.incidenceTorFullState p (G.incidenceTorEdgeSetComponent p S y) =
      (G.incidenceTorFullState p y).filter (fun b => b.1 = S) :=
  (G.exists_incidenceTorFullState_eq_filter p y S).choose_spec

/-- The edge-set component on `S` lies in the edge-set piece of `S`. -/
theorem incidenceTorEdgeSetComponent_mem (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    G.incidenceTorEdgeSetComponent p S y ∈ G.incidenceTorEdgeSetPiece p S := by
  rw [mem_incidenceTorEdgeSetPiece_iff]
  intro b hb
  rw [incidenceTorFullState_edgeSetComponent, Finsupp.filter_apply, ite_eq_right hb]

/-- A class determined by the restriction of its full state is the edge-set component. -/
theorem eq_incidenceTorEdgeSetComponent {p : ℕ} {S : Finset E} {y z : G.incidenceTor p}
    (hz : G.incidenceTorFullState p z = (G.incidenceTorFullState p y).filter (fun b => b.1 = S)) :
    z = G.incidenceTorEdgeSetComponent p S y :=
  G.incidenceTorFullState_injective p (by rw [hz, incidenceTorFullState_edgeSetComponent])

/-- A class in the edge-set piece of `S` is its own component on `S`. -/
theorem incidenceTorEdgeSetComponent_of_mem {p : ℕ} {S : Finset E} {y : G.incidenceTor p}
    (hy : y ∈ G.incidenceTorEdgeSetPiece p S) : G.incidenceTorEdgeSetComponent p S y = y := by
  rw [mem_incidenceTorEdgeSetPiece_iff] at hy
  refine (G.eq_incidenceTorEdgeSetComponent ?_).symm
  ext b
  rw [Finsupp.filter_apply]
  split_ifs with hb
  · rfl
  · exact hy b hb

/-- **Decomposition into edge-set components.** Every Tor class is the sum of its components on
all edge sets. -/
theorem sum_incidenceTorEdgeSetComponent (p : ℕ) (y : G.incidenceTor p) :
    ∑ S : Finset E, G.incidenceTorEdgeSetComponent p S y = y := by
  apply G.incidenceTorFullState_injective p
  rw [map_sum]
  ext b
  rw [Finsupp.finsetSum_apply]
  simp only [incidenceTorFullState_edgeSetComponent, Finsupp.filter_apply]
  rw [Finset.sum_ite_eq]
  simp

end EdgeSetPieces

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-! ## Sign compatibility in every degree -/

/-- The Tor map of a vertex map is the derived ring map along the identity of the coefficient ring
of the incidence module map. -/
theorem incidenceTorHom_eq_derivedRingMap (p : ℕ) :
    φ.incidenceTorHom p =
      derivedRingMap (RingHom.id (IncCoeffRing E)) constantCoeff constantCoeff
        (RingHom.comp_id _)
        (φ.incidenceModuleHom ≫
          (ModuleCat.restrictScalarsId' (RingHom.id (IncCoeffRing E)) rfl).inv.app
            (EdgeRelabel.incidenceModule H)) p :=
  (derivedRingMap_id_eq_map _ _ p).symm

/-- **Sign compatibility in every degree, as morphisms.** The Tor map of a vertex map intertwines
the Tor automorphisms of every edge sign on `G` and on `H`. -/
theorem incidenceTorHom_comp_signIso (ε : EdgeSign E) (p : ℕ) :
    φ.incidenceTorHom p ≫ (H.incidenceTorSignIso ε p).hom =
      (G.incidenceTorSignIso ε p).hom ≫ φ.incidenceTorHom p := by
  rw [incidenceTorSignIso, incidenceTorSignIso, incidenceTorTransportIso, incidenceTorTransportIso,
    derivedRingChange_hom_eq_derivedRingMap, derivedRingChange_hom_eq_derivedRingMap,
    incidenceTorHom]
  exact leftDerived_map_comp_derivedRingMap _ _ _ _ _ _ _ _
    (fun x => (φ.incidenceHom_edgeSignIncidence ε x).symm) p

/-- **Sign compatibility in every degree.** For every edge sign `ε` and every homological degree,
`φ_* ∘ ε_G = ε_H ∘ φ_*` on actual Tor. -/
theorem incidenceTorMap_sign (ε : EdgeSign E) (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorMap p (G.incidenceTorSign ε p y) =
      H.incidenceTorSign ε p (φ.incidenceTorMap p y) :=
  (congrArg (fun f => f.hom y) (φ.incidenceTorHom_comp_signIso ε p)).symm

/-- Sign compatibility as an equality of composite linear maps. -/
theorem incidenceTorMap_comp_sign (ε : EdgeSign E) (p : ℕ) :
    φ.incidenceTorMap p ∘ₗ (G.incidenceTorSign ε p).toLinearMap =
      (H.incidenceTorSign ε p).toLinearMap ∘ₗ φ.incidenceTorMap p :=
  LinearMap.ext (φ.incidenceTorMap_sign ε p)

/-! ## Edge-set pieces and internal degrees -/

/-- **The Tor map preserves edge-set pieces** (over `ℂ`): if the full state of `y` is supported on
basis states with edge set `S`, so is the full state of its image. -/
theorem incidenceTorMap_mem_edgeSetPiece {p : ℕ} {S : Finset E} {y : G.incidenceTor p}
    (hy : y ∈ G.incidenceTorEdgeSetPiece p S) :
    φ.incidenceTorMap p y ∈ H.incidenceTorEdgeSetPiece p S := by
  rw [mem_incidenceTorEdgeSetPiece_iff_sign]
  intro ε
  rw [← incidenceTorMap_sign, G.incidenceTorSign_of_mem_edgeSetPiece hy, map_smul]

/-- The preservation of edge-set pieces in coordinates: if the full state of `y` vanishes at every
basis state of `G` whose edge set is not `S`, the full state of its image vanishes at every basis
state of `H` whose edge set is not `S`. -/
theorem incidenceTorFullState_vertexMap_eq_zero_of_fst_ne {p : ℕ} {S : Finset E}
    {y : G.incidenceTor p}
    (hy : ∀ b : G.IncResolutionBasis, b.1 ≠ S → G.incidenceTorFullState p y b = 0)
    (b' : H.IncResolutionBasis) (hb' : b'.1 ≠ S) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b' = 0 :=
  (H.mem_incidenceTorEdgeSetPiece_iff p S _).1
    (φ.incidenceTorMap_mem_edgeSetPiece ((G.mem_incidenceTorEdgeSetPiece_iff p S y).2 hy)) b' hb'

/-- The coefficient of the image of a class at a basis state of `H` only depends on the component
of the class on the edge set of that state. -/
theorem incidenceTorFullState_vertexMap_component (p : ℕ) (y : G.incidenceTor p)
    (b : H.IncResolutionBasis) :
    H.incidenceTorFullState p (φ.incidenceTorMap p y) b =
      H.incidenceTorFullState p
        (φ.incidenceTorMap p (G.incidenceTorEdgeSetComponent p b.1 y)) b := by
  conv_lhs => rw [← G.sum_incidenceTorEdgeSetComponent p y]
  rw [map_sum, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_single b.1 (fun T _ hT => ?_) (fun h => absurd (Finset.mem_univ _) h)
  exact (H.mem_incidenceTorEdgeSetPiece_iff p T _).1
    (φ.incidenceTorMap_mem_edgeSetPiece (G.incidenceTorEdgeSetComponent_mem p T y)) b
    (Ne.symm hT)

/-- **The Tor map commutes with edge-set components.** -/
theorem incidenceTorMap_edgeSetComponent (p : ℕ) (S : Finset E) (y : G.incidenceTor p) :
    φ.incidenceTorMap p (G.incidenceTorEdgeSetComponent p S y) =
      H.incidenceTorEdgeSetComponent p S (φ.incidenceTorMap p y) := by
  apply H.eq_incidenceTorEdgeSetComponent
  ext b
  rw [Finsupp.filter_apply]
  split_ifs with hb
  · rw [φ.incidenceTorFullState_vertexMap_component p y b, hb]
  · exact (H.mem_incidenceTorEdgeSetPiece_iff p S _).1
      (φ.incidenceTorMap_mem_edgeSetPiece (G.incidenceTorEdgeSetComponent_mem p S y)) b hb

/-- **The Tor map preserves internal degrees** in every homological degree: it maps the bigraded
piece `(p, q)` of `G` into the bigraded piece `(p, q)` of `H`. -/
theorem incidenceTorMap_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorMap p x ∈ H.incidenceTorInternalPiece p q := by
  rw [EdgeRelabel.mem_incidenceTorInternalPiece_iff_fullState] at hx ⊢
  intro b hb
  have h0 : G.incidenceTorEdgeSetComponent p b.1 x = 0 := by
    apply G.incidenceTorFullState_injective p
    rw [incidenceTorFullState_edgeSetComponent, map_zero]
    ext b'
    rw [Finsupp.filter_apply, Finsupp.zero_apply]
    split_ifs with hb'
    · apply hx b'
      change b'.1.card ≠ q
      rw [hb']
      exact hb
    · rfl
  rw [φ.incidenceTorFullState_vertexMap_component, h0, map_zero, map_zero, Finsupp.zero_apply]

/-- The Tor map of a vertex map on bigraded pieces. -/
noncomputable def incidenceTorInternalVertexMap (p q : ℕ) :
    G.incidenceTorInternalPiece p q →ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorMap p).restrict fun _ hx => φ.incidenceTorMap_mem_internalPiece hx

@[simp] theorem incidenceTorInternalVertexMap_val (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalVertexMap p q x : H.incidenceTor p) = φ.incidenceTorMap p x.val :=
  rfl

/-! ## Collisions -/

/-- If the vertex function is not injective on the support of `S`, the support of `S` in `H` is
strictly smaller than in `G`. -/
theorem card_support_lt_of_not_injOn {S : Finset E} (h : ¬ Set.InjOn φ.vertex (G.support S)) :
    (H.support S).card < (G.support S).card := by
  rw [φ.support_eq_image]
  exact lt_of_le_of_ne Finset.card_image_le (fun heq => h (Finset.card_image_iff.mp heq))

/-- **Degrees under a collision.** If the vertex function is not injective on the support of the
edge set of a basis state `b` of `G`, every basis state of `H` with the same edge set has strictly
larger homological degree. -/
theorem incResolutionDegree_lt_of_not_injOn {b : G.IncResolutionBasis} {b' : H.IncResolutionBasis}
    (hbb' : b'.1 = b.1) (h : ¬ Set.InjOn φ.vertex (G.support b.1)) :
    G.incResolutionDegree b < H.incResolutionDegree b' := by
  have hlt := φ.card_support_lt_of_not_injOn h
  have hle := G.incResolutionBasis_card_support_le b
  unfold incResolutionDegree
  rw [hbb']
  omega

/-- **Collision vanishing.** If the vertex function is not injective on the support of `S`, the Tor
map kills every class supported on the edge set `S`, in every homological degree. -/
theorem incidenceTorMap_eq_zero_of_not_injOn {p : ℕ} {S : Finset E}
    (h : ¬ Set.InjOn φ.vertex (G.support S)) {y : G.incidenceTor p}
    (hy : y ∈ G.incidenceTorEdgeSetPiece p S) : φ.incidenceTorMap p y = 0 := by
  apply H.incidenceTorFullState_injective p
  rw [map_zero]
  ext b'
  rw [Finsupp.zero_apply]
  by_cases hb' : b'.1 = S
  · by_cases hdeg : H.incResolutionDegree b' = p
    · have hy0 : y = 0 := by
        apply G.incidenceTorFullState_injective p
        rw [map_zero]
        ext b
        rw [Finsupp.zero_apply]
        by_cases hb : b.1 = S
        · by_cases hdb : G.incResolutionDegree b = p
          · exfalso
            have hlt := φ.incResolutionDegree_lt_of_not_injOn (b := b) (b' := b')
              (hb'.trans hb.symm) (by rwa [hb])
            omega
          · exact G.incidenceTorFullState_apply_of_ne p y b hdb
        · exact (G.mem_incidenceTorEdgeSetPiece_iff p S y).1 hy b hb
      rw [hy0, map_zero, map_zero, Finsupp.zero_apply]
    · exact H.incidenceTorFullState_apply_of_ne p _ b' hdeg
  · exact (H.mem_incidenceTorEdgeSetPiece_iff p S _).1 (φ.incidenceTorMap_mem_edgeSetPiece hy) b'
      hb'

/-- **Collision vanishing on basis vectors.** If the full state of `y` is a multiple of a single
basis state `b` and the vertex function is not injective on the support of the edge set of `b`,
then the Tor map kills `y`. -/
theorem incidenceTorMap_eq_zero_of_fullState_single {p : ℕ} {y : G.incidenceTor p}
    {b : G.IncResolutionBasis} {r : ℂ} (hy : G.incidenceTorFullState p y = single b r)
    (h : ¬ Set.InjOn φ.vertex (G.support b.1)) : φ.incidenceTorMap p y = 0 :=
  φ.incidenceTorMap_eq_zero_of_not_injOn h (G.mem_incidenceTorEdgeSetPiece_of_fullState_single hy)

/-- Under a collision on `S` the Tor map vanishes on the whole edge-set piece of `S`. -/
theorem incidenceTorEdgeSetPiece_le_ker_of_not_injOn (p : ℕ) {S : Finset E}
    (h : ¬ Set.InjOn φ.vertex (G.support S)) :
    G.incidenceTorEdgeSetPiece p S ≤ LinearMap.ker (φ.incidenceTorMap p) :=
  fun _ hy => φ.incidenceTorMap_eq_zero_of_not_injOn h hy

/-! ## No collision -/

/-- If the vertex function is injective on the support of the edge set of a basis state `b` of
`G`, every basis state of `H` with the same edge set has the same homological degree. -/
theorem incResolutionDegree_eq_of_injOn {b : G.IncResolutionBasis} {b' : H.IncResolutionBasis}
    (hbb' : b'.1 = b.1) (h : Set.InjOn φ.vertex (G.support b.1)) :
    H.incResolutionDegree b' = G.incResolutionDegree b := by
  unfold incResolutionDegree
  rw [hbb', φ.support_eq_image, Finset.card_image_of_injOn h]

/-- If the vertex function is injective on the support of `S`, the basis states of `G` and of `H`
with edge set `S` are equinumerous: the twist data at a vertex of `H` in the support is the twist
data at its unique preimage in the support, and vertices outside the support carry one state. -/
theorem card_stateFibre_eq_of_injOn {S : Finset E} (h : Set.InjOn φ.vertex (G.support S)) :
    Fintype.card ((w : W) → Fin (phi (H.deg S w))) =
      Fintype.card ((v : V) → Fin (phi (G.deg S v))) := by
  simp only [Fintype.card_pi, Fintype.card_fin]
  have hG : ∏ v, phi (G.deg S v) = ∏ v ∈ G.support S, phi (G.deg S v) := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun v _ hv => ?_).symm
    rw [mem_support_iff, not_lt, Nat.le_zero] at hv
    rw [hv, phi_zero]
  have hH : ∏ w, phi (H.deg S w) = ∏ w ∈ H.support S, phi (H.deg S w) := by
    refine (Finset.prod_subset (Finset.subset_univ _) fun w _ hw => ?_).symm
    rw [mem_support_iff, not_lt, Nat.le_zero] at hw
    rw [hw, phi_zero]
  rw [hG, hH, φ.support_eq_image, Finset.prod_image fun v hv v' hv' => h hv hv']
  exact Finset.prod_congr rfl fun v hv => by rw [φ.deg_vertex_of_injOn h hv]

/-- **No collision.** If the vertex function is injective on the support of `S`, the image of a
class supported on `S` is supported on basis states of `H` with edge set `S`, all of homological
degree `|S| - |G.support S|`, the degree of the basis states of `G` with edge set `S`. -/
theorem incidenceTorMap_fullState_support_of_injOn {p : ℕ} {S : Finset E}
    (h : Set.InjOn φ.vertex (G.support S)) {y : G.incidenceTor p}
    (hy : y ∈ G.incidenceTorEdgeSetPiece p S) (b' : H.IncResolutionBasis)
    (hb' : H.incidenceTorFullState p (φ.incidenceTorMap p y) b' ≠ 0) :
    b'.1 = S ∧ H.incResolutionDegree b' = S.card - (G.support S).card := by
  have hS : b'.1 = S := by
    by_contra hne
    exact hb' ((H.mem_incidenceTorEdgeSetPiece_iff p S _).1
      (φ.incidenceTorMap_mem_edgeSetPiece hy) b' hne)
  refine ⟨hS, ?_⟩
  unfold incResolutionDegree
  rw [hS, φ.support_eq_image, Finset.card_image_of_injOn h]

end VertexMap

end BPFixedPoints.Multigraph
