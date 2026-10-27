import BPFixedPoints.Incidence.IncidenceGraphMapRings
import BPFixedPoints.Incidence.IncidenceSignedEdgeMapTor
import BPFixedPoints.Incidence.IncidenceVertexMapSupport

/-!
# The Tor map of a general graph map

For a graph map `φ : GraphMap G H` the intrinsic coefficient ring map `ρ = φ.coeffRingHom` and the
intrinsic incidence ring map, which is `ρ`-linear on coefficient modules (`incidenceModuleMap`),
give the map of actual Tor spaces
`incidenceTorMap p : Tor_p^{S_G}(𝒰_G, ℂ) → Tor_p^{S_H}(𝒰_H, ℂ)`. It is defined intrinsically as
the derived ring map `derivedRingMap` along `ρ` (`incidenceTorHom`); no flatness of `ρ` is used, and
neither states nor the factorization enter the definition.

**Independence of the factorization.** The Tor map is the Tor map of the vertex factor (Mathlib's
functoriality of the left derived functor) followed by the Tor map of the signed edge factor
(`incidenceTorHom_eq_comp`, `incidenceTorMap_apply_eq`). The vertex Tor map is the derived ring map
along the identity of the coefficient ring (`VertexMap.incidenceTorHom_eq_derivedRingMap`), and the
two derived ring maps are composed by `derivedRingMap_comp`, in the form
`derivedRingMap_comp_of_eq` for a ring homomorphism equal to the composite and a module map agreeing
elementwise with the composite module map.

**Functor laws**, proved through the intrinsic description by `derivedRingMap_id` and
`derivedRingMap_comp`, not through states: the identity graph map acts trivially
(`incidenceTorHom_refl`) and the Tor map of a composite is the composite of the Tor maps
(`incidenceTorHom_trans`). For a vertex map or a signed edge map, regarded as a graph map, the Tor
map is the Tor map of that map (`VertexMap.toGraphMap_incidenceTorHom`,
`SignedEdgeMap.toGraphMap_incidenceTorHom`). Consequently the Tor map is the composite of the Tor
maps of any factorization into a vertex map followed by a signed edge map, not only the canonical
one through `G.pushVertices φ.vertex` (`incidenceTorHom_eq_of_factorization`).

Through the factorization, the Tor map preserves the bigraded pieces
(`incidenceTorInternalMap`), the standard Tor product (`incidenceTorMap_product`) and the unit
(`incidenceTorMap_one`). The Tor map is not an isomorphism in general.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools MvPolynomial

/-! ## Derived ring maps along ring homomorphisms given up to equality -/

/-- The composition law `derivedRingMap_comp` for a ring homomorphism `f₁₂` equal to the composite
`f₂ ∘ f` and a module map along `f₁₂` which agrees elementwise with the composite of the module
maps. -/
theorem derivedRingMap_comp_of_eq {R R' R'' k : Type} [CommRing R] [CommRing R'] [CommRing R'']
    [CommRing k] (f : R →+* R') (ε : R →+* k) (ε' : R' →+* k) (hε : ε'.comp f = ε)
    (f₂ : R' →+* R'') (ε'' : R'' →+* k) (hε₂ : ε''.comp f₂ = ε') (f₁₂ : R →+* R'')
    (hf : f₁₂ = f₂.comp f) (hε₁₂ : ε''.comp f₁₂ = ε)
    {M : ModuleCat.{0} R} {M' : ModuleCat.{0} R'} {M'' : ModuleCat.{0} R''}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj M')
    (g₂ : M' ⟶ (ModuleCat.restrictScalars f₂).obj M'')
    (h : M ⟶ (ModuleCat.restrictScalars f₁₂).obj M'') (hh : ∀ x, h x = g₂ (g x)) (n : ℕ) :
    derivedRingMap f₁₂ ε ε'' hε₁₂ h n =
      derivedRingMap f ε ε' hε g n ≫ derivedRingMap f₂ ε' ε'' hε₂ g₂ n := by
  subst hf
  exact derivedRingMap_comp_of_apply f ε ε' hε f₂ ε'' hε₂ hε₁₂ g g₂ h hh n

/-- The identity law `derivedRingMap_id` for a ring endomorphism equal to the identity and a module
map which is elementwise the identity. -/
theorem derivedRingMap_eq_id_of_eq {R k : Type} [CommRing R] [CommRing k] (f : R →+* R)
    (hf : f = RingHom.id R) (ε : R →+* k) (hε : ε.comp f = ε) {M : ModuleCat.{0} R}
    (g : M ⟶ (ModuleCat.restrictScalars f).obj M) (hg : ∀ x : M, g x = x) (n : ℕ) :
    derivedRingMap f ε ε hε g n = 𝟙 _ := by
  subst hf
  have h : g = (ModuleCat.restrictScalarsId' (RingHom.id R) rfl).inv.app M := by
    ext x
    exact hg x
  subst h
  exact derivedRingMap_id ε M n

namespace GraphMap

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
  {H : Multigraph W E'} (φ : GraphMap G H)

/-! ## The module map and the Tor map -/

/-- The incidence ring map of a graph map as a linear map from the incidence module of `G` to the
incidence module of `H` restricted along the coefficient ring map. -/
noncomputable def incidenceModuleMap :
    EdgeRelabel.incidenceModule G ⟶
      (ModuleCat.restrictScalars φ.coeffRingHom).obj (EdgeRelabel.incidenceModule H) :=
  ModuleCat.ofHom (X := EdgeRelabel.incidenceModule G)
    (Y := (ModuleCat.restrictScalars φ.coeffRingHom).obj (EdgeRelabel.incidenceModule H))
    { toFun := fun x => φ.incidenceHom x
      map_add' := fun x y => map_add φ.incidenceHom x y
      map_smul' := fun r x => φ.incidenceHom_coeff_mul r x }

theorem incidenceModuleMap_apply (x : G.IncidenceRing) :
    φ.incidenceModuleMap x = φ.incidenceHom x := rfl

/-- **The Tor map of a graph map**, as a morphism: the derived ring map along the intrinsic
coefficient ring map of the intrinsic incidence module map. -/
noncomputable def incidenceTorHom (p : ℕ) : G.incidenceTor p ⟶ H.incidenceTor p :=
  derivedRingMap φ.coeffRingHom constantCoeff constantCoeff φ.constantCoeff_comp_coeffRingHom
    φ.incidenceModuleMap p

/-- **The Tor map of a graph map**, as a linear map. -/
noncomputable def incidenceTorMap (p : ℕ) : G.incidenceTor p →ₗ[ℂ] H.incidenceTor p :=
  (φ.incidenceTorHom p).hom

theorem incidenceTorMap_apply (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorMap p y = φ.incidenceTorHom p y := rfl

/-! ## Independence of the factorization -/

/-- **Independence of the factorization.** The Tor map of a graph map is the Tor map of its vertex
factor followed by the Tor map of its signed edge factor. -/
theorem incidenceTorHom_eq_comp (p : ℕ) :
    φ.incidenceTorHom p =
      φ.vertexFactor.incidenceTorHom p ≫ φ.edgeFactor.incidenceTorSignedEdgeMapHom p := by
  rw [VertexMap.incidenceTorHom_eq_derivedRingMap,
    SignedEdgeMap.incidenceTorSignedEdgeMapHom]
  exact derivedRingMap_comp_of_eq _ _ _ _ _ _ _ _
    (φ.coeffRingHom_eq_edgeFactor.trans (RingHom.comp_id _).symm) _ _ _ _
    (fun x => φ.incidenceHom_eq_comp_apply x) p

/-- The Tor map of a graph map is the Tor map of its vertex factor followed by the Tor map of its
signed edge factor, elementwise. -/
theorem incidenceTorMap_apply_eq (p : ℕ) (y : G.incidenceTor p) :
    φ.incidenceTorMap p y =
      φ.edgeFactor.incidenceTorSignedEdgeMap p (φ.vertexFactor.incidenceTorMap p y) := by
  rw [incidenceTorMap, incidenceTorHom_eq_comp]
  rfl

/-- The Tor map of a graph map, as a composite of linear maps. -/
theorem incidenceTorMap_eq_comp (p : ℕ) :
    φ.incidenceTorMap p =
      φ.edgeFactor.incidenceTorSignedEdgeMap p ∘ₗ φ.vertexFactor.incidenceTorMap p :=
  LinearMap.ext (φ.incidenceTorMap_apply_eq p)

/-! ## Identity and composition laws -/

/-- **Identity law.** The Tor map of the identity graph map is the identity. -/
theorem incidenceTorHom_refl (G : Multigraph V E) (p : ℕ) :
    (refl G).incidenceTorHom p = 𝟙 (G.incidenceTor p) :=
  derivedRingMap_eq_id_of_eq _ (coeffRingHom_refl G) _ _ _
    (fun x => incidenceHom_refl_apply G x) p

/-- **Composition law.** The Tor map of a composite of graph maps is the composite of the Tor
maps. -/
theorem incidenceTorHom_trans {X E'' : Type} [DecidableEq X] [Fintype X] [LinearOrder E'']
    [Fintype E''] {K : Multigraph X E''} (ψ : GraphMap H K) (p : ℕ) :
    (φ.trans ψ).incidenceTorHom p = φ.incidenceTorHom p ≫ ψ.incidenceTorHom p :=
  derivedRingMap_comp_of_eq _ _ _ _ _ _ _ _ (coeffRingHom_trans φ ψ) _ _ _ _
    (fun x => incidenceHom_trans_apply φ ψ x) p

/-- **Identity law**, elementwise. -/
theorem incidenceTorMap_refl (G : Multigraph V E) (p : ℕ) (y : G.incidenceTor p) :
    (refl G).incidenceTorMap p y = y := by
  rw [incidenceTorMap_apply, incidenceTorHom_refl]
  rfl

/-- **Composition law**, elementwise. -/
theorem incidenceTorMap_trans {X E'' : Type} [DecidableEq X] [Fintype X] [LinearOrder E'']
    [Fintype E''] {K : Multigraph X E''} (ψ : GraphMap H K) (p : ℕ) (y : G.incidenceTor p) :
    (φ.trans ψ).incidenceTorMap p y = ψ.incidenceTorMap p (φ.incidenceTorMap p y) := by
  rw [incidenceTorMap_apply, incidenceTorHom_trans]
  rfl

/-! ## Bigraded pieces, products and the unit -/

/-- The Tor map of a graph map preserves internal degrees. -/
theorem incidenceTorMap_mem_internalPiece {p q : ℕ} {x : G.incidenceTor p}
    (hx : x ∈ G.incidenceTorInternalPiece p q) :
    φ.incidenceTorMap p x ∈ H.incidenceTorInternalPiece p q := by
  rw [incidenceTorMap_apply_eq]
  exact φ.edgeFactor.incidenceTorSignedEdgeMap_mem_internalPiece
    (φ.vertexFactor.incidenceTorMap_mem_internalPiece hx)

/-- The Tor map of a graph map on bigraded pieces. -/
noncomputable def incidenceTorInternalMap (p q : ℕ) :
    G.incidenceTorInternalPiece p q →ₗ[ℂ] H.incidenceTorInternalPiece p q :=
  (φ.incidenceTorMap p).restrict fun _ hx => φ.incidenceTorMap_mem_internalPiece hx

@[simp] theorem incidenceTorInternalMap_val (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    (φ.incidenceTorInternalMap p q x : H.incidenceTor p) = φ.incidenceTorMap p x.val :=
  rfl

/-- On bigraded pieces the Tor map of a graph map is the bigraded Tor map of the vertex factor
followed by that of the signed edge factor. -/
theorem incidenceTorInternalMap_apply_eq (p q : ℕ) (x : G.incidenceTorInternalPiece p q) :
    φ.incidenceTorInternalMap p q x =
      φ.edgeFactor.incidenceTorInternalSignedEdgeMap p q
        (φ.vertexFactor.incidenceTorInternalVertexMap p q x) :=
  Subtype.ext (φ.incidenceTorMap_apply_eq p x.val)

/-- The Tor map of a graph map preserves the standard Tor product. -/
theorem incidenceTorMap_product (p q : ℕ) (x : G.incidenceTor p) (y : G.incidenceTor q) :
    φ.incidenceTorMap (p + q) (G.incidenceTorProduct p q x y) =
      H.incidenceTorProduct p q (φ.incidenceTorMap p x) (φ.incidenceTorMap q y) := by
  rw [incidenceTorMap_apply_eq, VertexMap.incidenceTorMap_product,
    SignedEdgeMap.incidenceTorSignedEdgeMap_product, incidenceTorMap_apply_eq,
    incidenceTorMap_apply_eq]

/-- The Tor map of a graph map sends the unit of Tor to the unit. -/
theorem incidenceTorMap_one : φ.incidenceTorMap 0 G.incidenceTorOne = H.incidenceTorOne := by
  rw [incidenceTorMap_apply_eq, VertexMap.incidenceTorMap_one,
    SignedEdgeMap.incidenceTorSignedEdgeMap_one]

end GraphMap

/-! ## Vertex maps and signed edge maps -/

/-- **Agreement with vertex maps.** For a vertex map, regarded as a graph map, the Tor map is the
Tor map of the vertex map. -/
theorem VertexMap.toGraphMap_incidenceTorHom {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexMap G H) (p : ℕ) :
    φ.toGraphMap.incidenceTorHom p = φ.incidenceTorHom p := by
  rw [VertexMap.incidenceTorHom_eq_derivedRingMap]
  exact derivedRingMap_congr φ.toGraphMap_coeffRingHom _ _ _ _ _ _
    (fun x => (AlgHom.congr_fun φ.toGraphMap_incidenceHom x).symm) p

/-- **Agreement with vertex maps**, elementwise. -/
theorem VertexMap.toGraphMap_incidenceTorMap {V W E : Type} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E] {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexMap G H) (p : ℕ) (y : G.incidenceTor p) :
    φ.toGraphMap.incidenceTorMap p y = φ.incidenceTorMap p y := by
  rw [GraphMap.incidenceTorMap_apply, VertexMap.toGraphMap_incidenceTorHom]
  rfl

/-- **Agreement with signed edge maps.** For a signed edge map, regarded as a graph map, the Tor map
is the Tor map of the signed edge map. -/
theorem SignedEdgeMap.toGraphMap_incidenceTorHom {V E E' : Type} [DecidableEq V] [Fintype V]
    [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeMap G H) (p : ℕ) :
    φ.toGraphMap.incidenceTorHom p = φ.incidenceTorSignedEdgeMapHom p :=
  derivedRingMap_congr φ.toGraphMap_coeffRingHom _ _ _ _ _ _
    (fun x => (AlgHom.congr_fun φ.toGraphMap_incidenceHom x).symm) p

/-- **Agreement with signed edge maps**, elementwise. -/
theorem SignedEdgeMap.toGraphMap_incidenceTorMap {V E E' : Type} [DecidableEq V] [Fintype V]
    [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeMap G H) (p : ℕ) (y : G.incidenceTor p) :
    φ.toGraphMap.incidenceTorMap p y = φ.incidenceTorSignedEdgeMap p y := by
  rw [GraphMap.incidenceTorMap_apply, SignedEdgeMap.toGraphMap_incidenceTorHom]
  rfl

namespace GraphMap

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] {G : Multigraph V E}
  {H : Multigraph W E'} (φ : GraphMap G H)

/-- **Independence of the factorization.** For every factorization of a graph map into a vertex
map followed by a signed edge map, the Tor map of the graph map is the composite of their Tor
maps. -/
theorem incidenceTorHom_eq_of_factorization {G' : Multigraph W E} (α : VertexMap G G')
    (β : SignedEdgeMap G' H) (hφ : α.toGraphMap.trans β.toGraphMap = φ) (p : ℕ) :
    φ.incidenceTorHom p = α.incidenceTorHom p ≫ β.incidenceTorSignedEdgeMapHom p := by
  subst hφ
  rw [incidenceTorHom_trans, VertexMap.toGraphMap_incidenceTorHom,
    SignedEdgeMap.toGraphMap_incidenceTorHom]

end GraphMap

end BPFixedPoints.Multigraph
