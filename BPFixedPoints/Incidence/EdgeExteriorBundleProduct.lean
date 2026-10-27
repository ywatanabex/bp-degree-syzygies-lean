import BPFixedPoints.Incidence.EdgeExteriorBundleCohomology
import BPFixedPoints.Incidence.BinaryCoverStandardCupNaturality
import BPFixedPoints.Incidence.VertexProjectiveTwistAbelianPairing
import BPFixedPoints.Incidence.VertexProjectiveTwistZeroRouteAgreement
import BPFixedPoints.Incidence.VertexProjectiveTwistProductTransfer
import BPFixedPoints.Incidence.StateExteriorCup

/-! # The exterior product on actual cohomology of the exterior bundle and its state formula

The exterior wedge pairing of the actual exterior bundles of degrees `q` and `q'` projects both
factors to their summands `O(-d_S)` and `O(-d_T)`, multiplies sections with the original
geometric twist product, and applies exterior multiplication of summands: the twist identity
`(-d_S)+(-d_T) = -d_{S∪T}` followed by the inclusion of the summand of `S ∪ T`, times the shuffle
sign, and zero when `S` and `T` share an edge. The exterior product on actual cohomology is the
standard product of this pairing (cup product followed by exterior multiplication) times the
total-complex sign (-1)^(q·j), with `j` the cohomological degree of the second factor; this is
the normalization of the Koszul sign (-1)^(|S|·j_T) of the state product. The product is
geometric; nothing is transported from states.

Naturality of the standard product in compatible pairings reduces it to pairs of summands, where
the state correspondence of the standard twist product applies. Hence the state vector (the state
coordinates of all summands, embedded in the full state module) of the product is the state
product `incStateCup` of the state vectors. The state vector is injective, the unit class of
the empty edge subset has the unit state, and so the exterior product is unital and associative,
with explicit transports of exterior and cohomological degrees.
-/

namespace BPFixedPoints.SheafTools.AbelianTensor
open CategoryTheory TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section
variable {T : Type} [TopologicalSpace T]
variable {F G H F' G' H' : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- Restrict a section pairing along sheaf morphisms into its factors and push it forward
along a sheaf morphism out of its target. -/
def SectionPairing.transfer (b : SectionPairing F G H) (f : F' ⟶ F) (g : G' ⟶ G) (k : H ⟶ H') :
    SectionPairing F' G' H' where
  pairing W := (((b.pairing W).compl₂ (g.hom.app (op W)).hom).compr₂ (k.hom.app (op W)).hom).comp
    (f.hom.app (op W)).hom
  restrict {W U} i x y := by
    change H'.obj.map i.op (k.hom.app (op U) (b.pairing U (f.hom.app (op U) x) (g.hom.app (op U) y))) =
      k.hom.app (op W) (b.pairing W (f.hom.app (op W) (F'.obj.map i.op x))
        (g.hom.app (op W) (G'.obj.map i.op y)))
    rw [← NatTrans.naturality_apply k.hom i.op, b.restrict, NatTrans.naturality_apply f.hom i.op,
      NatTrans.naturality_apply g.hom i.op]

/-- The transferred pairing evaluates the original pairing on the images of the sections. -/
@[simp] theorem SectionPairing.transfer_pairing (b : SectionPairing F G H) (f : F' ⟶ F) (g : G' ⟶ G)
    (k : H ⟶ H') (W : Opens T) (x : F'.obj.obj (op W)) (y : G'.obj.obj (op W)) :
    (b.transfer f g k).pairing W x y = k.hom.app (op W) (b.pairing W (f.hom.app (op W) x) (g.hom.app (op W) y)) :=
  rfl

/-- The sum of a finite family of section pairings with common factors and target. -/
def SectionPairing.sum {ι : Type} [Fintype ι] (b : ι → SectionPairing F G H) : SectionPairing F G H where
  pairing W := ∑ t, (b t).pairing W
  restrict {W U} i x y := by
    simp only [AddMonoidHom.finsetSum_apply]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => (b t).restrict i x y

/-- The sum of section pairings evaluates the sum of the pairings. -/
@[simp] theorem SectionPairing.sum_pairing {ι : Type} [Fintype ι] (b : ι → SectionPairing F G H)
    (W : Opens T) (x : F.obj.obj (op W)) (y : G.obj.obj (op W)) :
    (SectionPairing.sum b).pairing W x y = ∑ t, (b t).pairing W x y := by
  simp only [SectionPairing.sum, AddMonoidHom.finsetSum_apply]

end
end BPFixedPoints.SheafTools.AbelianTensor

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite ProjectiveLine SchemeTools SheafTools SheafTools.AbelianTensor
open SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars true

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

noncomputable local instance exteriorProductHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The actual abelian sheaf morphism of a biproduct projection of the exterior bundle. -/
noncomputable abbrev exteriorProj (q : ℕ) (S : Set.powersetCard E q) :
    G.exteriorBundleAbelian R q ⟶ vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ)) :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)

/-- The actual abelian sheaf morphism of a biproduct inclusion into the exterior bundle. -/
noncomputable abbrev exteriorIncl (q : ℕ) (S : Set.powersetCard E q) :
    vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ)) ⟶ G.exteriorBundleAbelian R q :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.ι (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)

omit [LinearOrder E] in
/-- An inclusion followed by the projection to the same summand is the identity. -/
theorem exteriorIncl_proj_self (q : ℕ) (S : Set.powersetCard E q) :
    G.exteriorIncl R q S ≫ G.exteriorProj R q S = 𝟙 _ := by
  rw [exteriorIncl, exteriorProj, ← Functor.map_comp, biproduct.ι_π_self]
  exact CategoryTheory.Functor.map_id _ _

omit [LinearOrder E] in
/-- An inclusion followed by the projection to another summand is zero. -/
theorem exteriorIncl_proj_ne (q : ℕ) {S S' : Set.powersetCard E q} (h : S ≠ S') :
    G.exteriorIncl R q S ≫ G.exteriorProj R q S' = 0 := by
  rw [exteriorIncl, exteriorProj, ← Functor.map_comp, biproduct.ι_π_ne _ h, Functor.map_zero]

omit [LinearOrder E] in
/-- On sections, an inclusion followed by the projection to the same summand is the identity. -/
theorem exteriorIncl_proj_self_apply (q : ℕ) (S : Set.powersetCard E q) (W : (vertexScheme R V).Opens)
    (x : (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))).obj.obj (op W)) :
    (G.exteriorProj R q S).hom.app (op W) ((G.exteriorIncl R q S).hom.app (op W) x) = x := by
  rw [← NatTrans.comp_app_apply, ← ObjectProperty.FullSubcategory.comp_hom, exteriorIncl_proj_self]
  rfl

omit [LinearOrder E] in
/-- On sections, an inclusion followed by the projection to another summand is zero. -/
theorem exteriorIncl_proj_ne_apply (q : ℕ) {S S' : Set.powersetCard E q} (h : S ≠ S')
    (W : (vertexScheme R V).Opens)
    (x : (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))).obj.obj (op W)) :
    (G.exteriorProj R q S').hom.app (op W) ((G.exteriorIncl R q S).hom.app (op W) x) = 0 := by
  rw [← NatTrans.comp_app_apply, ← ObjectProperty.FullSubcategory.comp_hom, exteriorIncl_proj_ne G R q h]
  rfl

/-- The disjoint union of two edge subsets, as an edge subset of the summed cardinality. -/
def edgeSubsetUnion {q q' : ℕ} (S : Set.powersetCard E q) (T : Set.powersetCard E q')
    (h : Disjoint (S : Finset E) (T : Finset E)) : Set.powersetCard E (q+q') :=
  ⟨(S : Finset E) ∪ T, by
    rw [Set.powersetCard.mem_iff, Finset.card_union_of_disjoint h, Set.powersetCard.card_eq S,
      Set.powersetCard.card_eq T]⟩

omit [Fintype E] in
/-- The underlying edge set of the disjoint union is the union. -/
@[simp] theorem edgeSubsetUnion_coe {q q' : ℕ} (S : Set.powersetCard E q) (T : Set.powersetCard E q')
    (h : Disjoint (S : Finset E) (T : Finset E)) :
    (edgeSubsetUnion S T h : Finset E) = (S : Finset E) ∪ (T : Finset E) := rfl

/-- The sum of the negative twists of disjoint edge sets is the negative twist of their union. -/
theorem exteriorTwist_union {S T : Finset E} (h : Disjoint S T) :
    (fun v => -(G.deg S v : ℤ)) + (fun v => -(G.deg T v : ℤ)) = fun v => -(G.deg (S ∪ T) v : ℤ) := by
  rw [G.deg_union_eq_add h]
  exact vertexTwistNegativeAdd V _ _

/-- The twist identity for disjoint edge subsets, with the target written through the edge subset
of their union. -/
theorem exteriorTwist_edgeSubsetUnion {q q' : ℕ} {S : Set.powersetCard E q}
    {T : Set.powersetCard E q'} (h : Disjoint (S : Finset E) (T : Finset E)) :
    (fun v => -(G.deg S v : ℤ)) + (fun v => -(G.deg T v : ℤ)) =
      fun v => -(G.deg (edgeSubsetUnion S T h : Finset E) v : ℤ) :=
  G.exteriorTwist_union h

/-- Exterior multiplication on one pair of summands: for disjoint edge subsets the twist identity
followed by the inclusion of the union summand, times the shuffle sign; zero when they share an
edge. -/
noncomputable def exteriorWedgeMap {q q' : ℕ} (S : Set.powersetCard E q) (T : Set.powersetCard E q') :
    vertexTwistAbelianSheaf R V ((fun v => -(G.deg S v : ℤ)) + (fun v => -(G.deg T v : ℤ))) ⟶
      G.exteriorBundleAbelian R (q+q') :=
  if h : Disjoint (S : Finset E) (T : Finset E) then
    Koszul.shuffleSign (R := ℤ) (S : Finset E) T •
      (eqToHom (congrArg (vertexTwistAbelianSheaf R V) (G.exteriorTwist_edgeSubsetUnion h)) ≫
        G.exteriorIncl R (q+q') (edgeSubsetUnion S T h))
  else 0

/-- The exterior wedge pairing of actual exterior bundles: project both factors to their
summands, multiply sections with the original twist product, and apply exterior multiplication
of the summands (shuffle sign onto the union summand, zero on a shared edge). -/
noncomputable def exteriorWedgePairing (q q' : ℕ) :
    SectionPairing (G.exteriorBundleAbelian R q) (G.exteriorBundleAbelian R q')
      (G.exteriorBundleAbelian R (q+q')) :=
  SectionPairing.sum fun ST : Set.powersetCard E q × Set.powersetCard E q' =>
    (vertexTwistAbelianSectionPairing R V (fun v => -(G.deg ST.1 v : ℤ))
      (fun v => -(G.deg ST.2 v : ℤ))).transfer
        (G.exteriorProj R q ST.1) (G.exteriorProj R q' ST.2) (G.exteriorWedgeMap R ST.1 ST.2)

/-- On a pair of summands, the exterior wedge pairing is the original twist product followed by
exterior multiplication of the summands. -/
theorem exteriorWedgePairing_compatible {q q' : ℕ} (S : Set.powersetCard E q)
    (T : Set.powersetCard E q') :
    SectionPairing.Compatible
      (vertexTwistAbelianSectionPairing R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)))
      (G.exteriorWedgePairing R q q') (G.exteriorIncl R q S) (G.exteriorIncl R q' T)
      (G.exteriorWedgeMap R S T) := by
  intro W x y
  rw [exteriorWedgePairing, SectionPairing.sum_pairing, Fintype.sum_eq_single (S, T)]
  · rw [SectionPairing.transfer_pairing, exteriorIncl_proj_self_apply, exteriorIncl_proj_self_apply]
  · rintro ⟨S', T'⟩ hST
    rw [SectionPairing.transfer_pairing]
    by_cases hS : S = S'
    · subst hS
      have hT : T ≠ T' := fun h => hST (by rw [h])
      rw [exteriorIncl_proj_ne_apply G R q' hT, map_zero, map_zero]
    · rw [exteriorIncl_proj_ne_apply G R q hS, map_zero, AddMonoidHom.zero_apply, map_zero]

variable [IsNoetherianRing R]

/-- The product on actual cohomology of the exterior bundles: the standard product of the
exterior wedge pairing (cup product followed by exterior multiplication), times the
total-complex sign (-1)^(q·j) of moving the exterior degree `q` of the first factor past the
cohomological degree `j` of the second. -/
noncomputable def exteriorCohomologyProduct (q q' i j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) i →+ Sheaf.H.{1} (G.exteriorBundleAbelian R q') j →+
      Sheaf.H.{1} (G.exteriorBundleAbelian R (q+q')) (i+j) :=
  ((-1 : ℤ) ^ (q * j)) • actualStandardClassCup (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
    (G.exteriorWedgePairing R q q') (G.exteriorBundle_terms_acyclic R q)
    (G.exteriorBundle_terms_acyclic R q') i j

/-- The exterior product evaluates the sign (-1)^(q·j) times the standard product of the exterior
wedge pairing. -/
theorem exteriorCohomologyProduct_apply (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    G.exteriorCohomologyProduct R q q' i j x y =
      ((-1 : ℤ) ^ (q * j)) • actualStandardClassCup (vertexCoordinateOpen R V)
        (vertexCellChartOpen_cover R V) (G.exteriorWedgePairing R q q')
        (G.exteriorBundle_terms_acyclic R q) (G.exteriorBundle_terms_acyclic R q') i j x y := rfl

omit [IsNoetherianRing R] in
/-- On sections, the exterior wedge pairing sums over pairs of summands the exterior
multiplication of the original twist product of the projected sections. -/
theorem exteriorWedgePairing_pairing (q q' : ℕ) (W : (vertexScheme R V).Opens)
    (x : (G.exteriorBundleAbelian R q).obj.obj (op W))
    (y : (G.exteriorBundleAbelian R q').obj.obj (op W)) :
    (G.exteriorWedgePairing R q q').pairing W x y =
      ∑ ST : Set.powersetCard E q × Set.powersetCard E q',
        (G.exteriorWedgeMap R ST.1 ST.2).hom.app (op W)
          ((vertexTwistAbelianSectionPairing R V (fun v => -(G.deg ST.1 v : ℤ))
            (fun v => -(G.deg ST.2 v : ℤ))).pairing W
              ((G.exteriorProj R q ST.1).hom.app (op W) x) ((G.exteriorProj R q' ST.2).hom.app (op W) y)) :=
  SectionPairing.sum_pairing _ W x y

/-- On classes from a pair of summands, the exterior product is the sign (-1)^(q·j) times
exterior multiplication of the summands applied to the standard twist product. -/
theorem exteriorCohomologyProduct_incl {q q' : ℕ} (i j : ℕ) (S : Set.powersetCard E q)
    (T : Set.powersetCard E q')
    (a : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) i)
    (c : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg T v : ℤ))) j) :
    G.exteriorCohomologyProduct R q q' i j (Sheaf.H.map (G.exteriorIncl R q S) i a)
        (Sheaf.H.map (G.exteriorIncl R q' T) j c) =
      ((-1 : ℤ) ^ (q * j)) • Sheaf.H.map (G.exteriorWedgeMap R S T) (i+j)
        (vertexTwistStandardClassCup R V _ _ i j a c) := by
  rw [exteriorCohomologyProduct, AddMonoidHom.smul_apply, AddMonoidHom.smul_apply,
    actualStandardClassCup_natural (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
      (G.exteriorWedgePairing_compatible R S T) (vertexTwistCellSheaf_terms_acyclic R V _)
      (vertexTwistCellSheaf_terms_acyclic R V _)]
  rfl

omit [IsNoetherianRing R] [DecidableEq V] in
/-- Cohomology of a zero sheaf morphism is zero. -/
theorem sheafH_map_zero_apply {F₁ F₂ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (n : ℕ) (z : Sheaf.H.{1} F₁ n) : Sheaf.H.map (0 : F₁ ⟶ F₂) n z = 0 :=
  map_zero (AddMonoidHom.mk' (fun f : F₁ ⟶ F₂ => Sheaf.H.map f n z) (fun f g => Sheaf.H.map_add_apply f g z))

omit [IsNoetherianRing R] [DecidableEq V] in
/-- Cohomology of an integer multiple of a sheaf morphism is that multiple. -/
theorem sheafH_map_zsmul_apply {F₁ F₂ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (m : ℤ) (f : F₁ ⟶ F₂) (n : ℕ) (z : Sheaf.H.{1} F₁ n) :
    Sheaf.H.map (m • f) n z = m • Sheaf.H.map f n z :=
  map_zsmul (AddMonoidHom.mk' (fun f : F₁ ⟶ F₂ => Sheaf.H.map f n z) (fun f g => Sheaf.H.map_add_apply f g z)) m f

omit [IsNoetherianRing R] [DecidableEq V] in
/-- Cohomology of the twist identity morphism is the transport of actual cohomology. -/
theorem vertexTwist_sheafH_map_eqToHom {a a' : V → ℤ} (h : a = a') (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :
    Sheaf.H.map (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h)) n z = vertexTwistHCast R V h n z := by
  subst h
  rw [eqToHom_refl, Sheaf.H.map_id_apply]
  rfl

/-- The state coordinate of a class transported along the twist identity (-d)+(-e) = -d' is the
transported state coordinate of the class transported to the twist -(d+e). -/
theorem vertexTwistActualStateAt_map_eqToHom (d e d' : V → ℕ) (hd : d + e = d')
    (h : (fun v => -(d v : ℤ)) + (fun v => -(e v : ℤ)) = fun v => -(d' v : ℤ)) (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V ((fun v => -(d v : ℤ)) + (fun v => -(e v : ℤ)))) n) :
    (vertexTwistActualStateAt R V d' n
        (Sheaf.H.map (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h)) n z)).val =
      CechProduct.castH R hd (vertexTwistActualStateAt R V (d+e) n
        (vertexTwistHCast R V (vertexTwistNegativeAdd V d e) n z)).val := by
  subst hd
  rw [vertexTwist_sheafH_map_eqToHom]
  rfl

omit [IsNoetherianRing R] in
/-- Exterior multiplication of disjoint summands followed by the projection to the union summand
is the shuffle sign times the twist identity. -/
theorem exteriorWedgeMap_proj_union {q q' : ℕ} {S : Set.powersetCard E q} {T : Set.powersetCard E q'}
    (h : Disjoint (S : Finset E) (T : Finset E)) :
    G.exteriorWedgeMap R S T ≫ G.exteriorProj R (q+q') (edgeSubsetUnion S T h) =
      Koszul.shuffleSign (R := ℤ) (S : Finset E) T •
        eqToHom (congrArg (vertexTwistAbelianSheaf R V) (G.exteriorTwist_edgeSubsetUnion h)) := by
  rw [exteriorWedgeMap, dite_eq_left h, Preadditive.zsmul_comp, Category.assoc, exteriorIncl_proj_self]
  exact congrArg (fun f => Koszul.shuffleSign (R := ℤ) (S : Finset E) T • f) (Category.comp_id _)

omit [IsNoetherianRing R] in
/-- Exterior multiplication followed by the projection to a summand other than the union is zero. -/
theorem exteriorWedgeMap_proj_ne {q q' : ℕ} {S : Set.powersetCard E q} {T : Set.powersetCard E q'}
    {U : Set.powersetCard E (q+q')} (hU : ∀ h : Disjoint (S : Finset E) (T : Finset E),
      edgeSubsetUnion S T h ≠ U) :
    G.exteriorWedgeMap R S T ≫ G.exteriorProj R (q+q') U = 0 := by
  rw [exteriorWedgeMap]
  split_ifs with h
  · rw [Preadditive.zsmul_comp, Category.assoc, exteriorIncl_proj_ne G R _ (hU h), comp_zero,
      smul_zero]
  · rw [zero_comp]

/-- The linear map sending a family of state degree pieces indexed by the `q`-element edge subsets
to the sum of their embeddings in the full state module. -/
noncomputable def exteriorStateTotal (q j : ℕ) :
    (Π S : Set.powersetCard E q, CechProduct.stateDegreePiece R (G.deg S) j) →ₗ[R]
      (G.IncResolutionBasis →₀ R) :=
  ∑ S : Set.powersetCard E q, (G.incStateEmbed R S).comp
    ((CechProduct.stateDegreePiece R (G.deg S) j).subtype.comp (LinearMap.proj S))

omit [IsNoetherianRing R] [LinearOrder E] in
/-- The total state embedding sums the embedded components. -/
theorem exteriorStateTotal_apply (q j : ℕ)
    (s : Π S : Set.powersetCard E q, CechProduct.stateDegreePiece R (G.deg S) j) :
    G.exteriorStateTotal R q j s = ∑ S : Set.powersetCard E q, G.incStateEmbed R S (s S).val := by
  simp [exteriorStateTotal]

omit [IsNoetherianRing R] in
/-- The coefficient of the total state embedding at a state of a `q`-element edge subset is the
coefficient of its component. -/
theorem exteriorStateTotal_apply_index (q j : ℕ)
    (s : Π S : Set.powersetCard E q, CechProduct.stateDegreePiece R (G.deg S) j)
    (S : Set.powersetCard E q) (κ : CechProduct.HBasis (G.deg S)) :
    G.exteriorStateTotal R q j s ⟨S, κ⟩ = (s S).val κ := by
  rw [exteriorStateTotal_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single S]
  · exact G.incStateEmbed_apply_same R S _ κ
  · intro S' _ hS'
    exact G.incStateEmbed_apply_of_ne R (fun h => hS' (Subtype.ext h)) _ κ
  · intro h
    exact absurd (Finset.mem_univ S) h

omit [IsNoetherianRing R] in
/-- The total state embedding is injective. -/
theorem exteriorStateTotal_injective (q j : ℕ) :
    Function.Injective (G.exteriorStateTotal R q j) := by
  intro s t hst
  funext S
  apply Subtype.ext
  ext κ
  rw [← G.exteriorStateTotal_apply_index R q j s S κ, ← G.exteriorStateTotal_apply_index R q j t S κ,
    hst]

/-- The state vector of actual exterior cohomology: the state coordinates of all summand
components, embedded in the full state module of all edge subsets. -/
noncomputable def exteriorCohomologyState (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  letI := G.exteriorBundleCohomologyModule R q j
  (G.exteriorStateTotal R q j).comp (G.exteriorBundleStateLinearEquiv R q j).toLinearMap

omit [LinearOrder E] in
/-- The state vector of an exterior class sums the embedded cell-route state coordinates of its
summand projections. -/
theorem exteriorCohomologyState_apply (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologyState R q j x =
      ∑ S : Set.powersetCard E q, G.incStateEmbed R S
        (vertexTwistActualStateAt R V (G.deg S) j (Sheaf.H.map (G.exteriorProj R q S) j x)).val := by
  let _ := G.exteriorBundleCohomologyModule R q j
  change G.exteriorStateTotal R q j (G.exteriorBundleStateLinearEquiv R q j x) = _
  rw [exteriorStateTotal_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [exteriorBundleStateLinearEquiv_apply, vertexTwistStateLinearEquiv_eq_actualStateAt]
  rfl

/-- The state vector of exterior cohomology is injective. -/
theorem exteriorCohomologyState_injective (q j : ℕ) :
    Function.Injective (G.exteriorCohomologyState R q j) := by
  let _ := G.exteriorBundleCohomologyModule R q j
  exact (G.exteriorStateTotal_injective R q j).comp (G.exteriorBundleStateLinearEquiv R q j).injective

omit [Fintype E] [IsNoetherianRing R] in
/-- The integer shuffle sign maps to the shuffle sign of any commutative ring. -/
theorem intCast_shuffleSign (S T : Finset E) :
    ((Koszul.shuffleSign (R := ℤ) S T : ℤ) : R) = Koszul.shuffleSign (R := R) S T := by
  simp [Koszul.shuffleSign]

/-- The state vector of exterior multiplication of a pair of summands: zero when the edge subsets
share an edge, and otherwise the shuffle sign times the embedding into the union of the
transported state coordinate. -/
theorem exteriorCohomologyState_wedgeMap {q q' : ℕ} (S : Set.powersetCard E q)
    (T : Set.powersetCard E q') (n : ℕ)
    (z : Sheaf.H.{1} (vertexTwistAbelianSheaf R V
      ((fun v => -(G.deg S v : ℤ)) + (fun v => -(G.deg T v : ℤ)))) n) :
    G.exteriorCohomologyState R (q+q') n (Sheaf.H.map (G.exteriorWedgeMap R S T) n z) =
      if h : Disjoint (S : Finset E) (T : Finset E) then
        Koszul.shuffleSign (R := R) (S : Finset E) T •
          G.incStateEmbed R ((S : Finset E) ∪ T) (CechProduct.castH R (G.deg_union_eq_add h).symm
            (vertexTwistActualStateAt R V (G.deg S + G.deg T) n
              (vertexTwistHCast R V (vertexTwistNegativeAdd V _ _) n z)).val)
      else 0 := by
  rw [exteriorCohomologyState_apply]
  by_cases h : Disjoint (S : Finset E) (T : Finset E)
  · rw [dite_eq_left h, Finset.sum_eq_single (edgeSubsetUnion S T h)]
    · rw [← Sheaf.H.map_comp_apply, exteriorWedgeMap_proj_union, sheafH_map_zsmul_apply, map_zsmul,
        Submodule.coe_smul_of_tower, map_zsmul, ← Int.cast_smul_eq_zsmul R, intCast_shuffleSign]
      congr 1
      exact congrArg (G.incStateEmbed R ((S : Finset E) ∪ T))
        (vertexTwistActualStateAt_map_eqToHom R (G.deg S) (G.deg T) (G.deg ((S : Finset E) ∪ T))
          (G.deg_union_eq_add h).symm (G.exteriorTwist_edgeSubsetUnion h) n z)
    · intro U _ hU
      rw [← Sheaf.H.map_comp_apply, exteriorWedgeMap_proj_ne G R (fun h' e => hU e.symm),
        sheafH_map_zero_apply, map_zero, ZeroMemClass.coe_zero, map_zero]
    · intro hU
      exact absurd (Finset.mem_univ _) hU
  · have hw : G.exteriorWedgeMap R S T = 0 := by
      rw [exteriorWedgeMap, dite_eq_right h]
    rw [dite_eq_right h, hw, sheafH_map_zero_apply]
    refine Finset.sum_eq_zero fun U _ => ?_
    rw [map_zero, map_zero, ZeroMemClass.coe_zero, map_zero]

omit [LinearOrder E] [IsNoetherianRing R] in
/-- Every class of the exterior bundle is the sum of the inclusions of its summand projections. -/
theorem exterior_sum_incl_proj (q n : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) n) :
    ∑ S : Set.powersetCard E q,
      Sheaf.H.map (G.exteriorIncl R q S) n (Sheaf.H.map (G.exteriorProj R q S) n x) = x := by
  have hx := (G.exteriorBundleCohomologyEquiv R q n).symm_apply_apply x
  rw [exteriorBundleCohomologyEquiv_symm_apply] at hx
  exact hx

/-- State formula: the state vector of the exterior product of two classes is the state product
of their state vectors. -/
theorem exteriorCohomologyState_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    G.exteriorCohomologyState R (q+q') (i+j) (G.exteriorCohomologyProduct R q q' i j x y) =
      G.incStateCup R (G.exteriorCohomologyState R q i x) (G.exteriorCohomologyState R q' j y) := by
  conv_lhs => rw [← G.exterior_sum_incl_proj R q i x, ← G.exterior_sum_incl_proj R q' j y]
  rw [exteriorCohomologyState_apply G R q i x, exteriorCohomologyState_apply G R q' j y]
  simp only [map_sum, LinearMap.sum_apply, AddMonoidHom.finsetSum_apply]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun S _ => ?_
  rw [exteriorCohomologyProduct_incl, map_zsmul, exteriorCohomologyState_wedgeMap, incStateCup_embed]
  by_cases h : Disjoint (S : Finset E) (T : Finset E)
  · rw [dite_eq_left h, dite_eq_left h]
    have hc := vertexTwistActualStateAt_standardCup R V (G.deg S) (G.deg T) i j
      (Sheaf.H.map (G.exteriorProj R q S) i x) (Sheaf.H.map (G.exteriorProj R q' T) j y)
    rw [hc]
    by_cases hj : CechProduct.cohomologyDegree (G.deg T) = j
    · rw [hj, Set.powersetCard.card_eq S, ← Int.cast_smul_eq_zsmul R, smul_smul]
      congr 1
      push_cast
      ring
    · rw [CechProduct.eq_zero_of_mem_stateDegreePiece R
        (vertexTwistActualStateAt R V (G.deg T) j (Sheaf.H.map (G.exteriorProj R q' T) j y)).property hj]
      simp only [map_zero, smul_zero]
  · rw [dite_eq_right h, dite_eq_right h, smul_zero]

omit [LinearOrder E] in
/-- The state vector of an exterior class sums, over the `q`-element edge subsets, the embedded
components of its public state comparison. -/
theorem exteriorCohomologyState_eq_sum (q j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorCohomologyState R q j x =
      ∑ S : Set.powersetCard E q, G.incStateEmbed R S (G.exteriorBundleStateLinearEquiv R q j x S).val :=
  G.exteriorStateTotal_apply R q j _

/-- State formula through the public state comparison: embedding and summing the state components
of the exterior product of two classes gives the state product of the embedded and summed state
components of the two classes. -/
theorem exteriorBundleStateLinearEquiv_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    ∑ U : Set.powersetCard E (q+q'), G.incStateEmbed R U
        (G.exteriorBundleStateLinearEquiv R (q+q') (i+j) (G.exteriorCohomologyProduct R q q' i j x y) U).val =
      G.incStateCup R
        (∑ S : Set.powersetCard E q, G.incStateEmbed R S (G.exteriorBundleStateLinearEquiv R q i x S).val)
        (∑ T : Set.powersetCard E q', G.incStateEmbed R T (G.exteriorBundleStateLinearEquiv R q' j y T).val) := by
  rw [← exteriorCohomologyState_eq_sum, ← exteriorCohomologyState_eq_sum, ← exteriorCohomologyState_eq_sum,
    exteriorCohomologyState_product]

/-- Transport of actual exterior cohomology along equalities of exterior and cohomological
degrees. -/
noncomputable def exteriorHCast {q q' : ℕ} (hq : q = q') {n n' : ℕ} (hn : n = n') :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) n ≃+ Sheaf.H.{1} (G.exteriorBundleAbelian R q') n' := by
  subst hq
  subst hn
  exact AddEquiv.refl _

omit [LinearOrder E] in
/-- The state vector is unchanged by transport along equalities of degrees. -/
theorem exteriorCohomologyState_cast {q q' : ℕ} (hq : q = q') {n n' : ℕ} (hn : n = n')
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) n) :
    G.exteriorCohomologyState R q' n' (G.exteriorHCast R hq hn x) = G.exteriorCohomologyState R q n x := by
  subst hq
  subst hn
  rfl

/-- The empty edge subset, the unique edge subset of cardinality zero. -/
def emptyEdgeSubset : Set.powersetCard E 0 := ⟨∅, by simp⟩

omit [LinearOrder E] [Fintype E] in
/-- The underlying edge set of the empty edge subset is empty. -/
@[simp] theorem emptyEdgeSubset_coe : ((emptyEdgeSubset : Set.powersetCard E 0) : Finset E) = ∅ := rfl

/-- The empty edge subset has twist zero. -/
theorem deg_emptyEdgeSubset :
    (0 : V → ℕ) = G.deg ((emptyEdgeSubset : Set.powersetCard E 0) : Finset E) :=
  G.deg_empty_eq_zero.symm

/-- The unit of actual exterior cohomology: the original twist-zero unit class in the summand of
the empty edge subset of the zeroth exterior bundle. -/
noncomputable def exteriorCohomologyUnit : Sheaf.H.{1} (G.exteriorBundleAbelian R 0) 0 :=
  Sheaf.H.map (G.exteriorIncl R 0 emptyEdgeSubset) 0
    (vertexNegativeHCast R V (G.deg_emptyEdgeSubset) rfl (vertexNegativeUnit R V))

/-- The state vector of the exterior unit is the unit state. -/
theorem exteriorCohomologyState_unit :
    G.exteriorCohomologyState R 0 0 (G.exteriorCohomologyUnit R) = G.incStateUnit R := by
  rw [exteriorCohomologyState_apply, Fintype.sum_eq_single emptyEdgeSubset]
  · rw [exteriorCohomologyUnit, ← Sheaf.H.map_comp_apply, exteriorIncl_proj_self, Sheaf.H.map_id_apply]
    have hs := vertexTwistActualStateAt_cast R V (G.deg_emptyEdgeSubset) (rfl : 0 = 0)
      (vertexNegativeUnit R V)
    rw [vertexNegativeUnit_state] at hs
    rw [hs]
    rfl
  · intro S hS
    exact absurd (Subsingleton.elim S emptyEdgeSubset) hS

/-- The exterior unit is a left unit for the exterior product, after transport along `0 + q = q`
and `0 + j = j`. -/
theorem exteriorCohomologyProduct_unit_left (q j : ℕ)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorHCast R (zero_add q) (zero_add j)
      (G.exteriorCohomologyProduct R 0 q 0 j (G.exteriorCohomologyUnit R) y) = y := by
  apply G.exteriorCohomologyState_injective R q j
  rw [exteriorCohomologyState_cast, exteriorCohomologyState_product, exteriorCohomologyState_unit,
    incStateCup_unit_left]

/-- The exterior unit is a right unit for the exterior product. -/
theorem exteriorCohomologyProduct_unit_right (q i : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i) :
    G.exteriorCohomologyProduct R q 0 i 0 x (G.exteriorCohomologyUnit R) = x := by
  apply G.exteriorCohomologyState_injective R q i
  have h := G.exteriorCohomologyState_product R q 0 i 0 x (G.exteriorCohomologyUnit R)
  rw [exteriorCohomologyState_unit, incStateCup_unit_right] at h
  exact h

/-- The exterior product is associative, after transport along the associativity of exterior and
cohomological degrees. -/
theorem exteriorCohomologyProduct_assoc (q q' q'' i j k : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j)
    (z : Sheaf.H.{1} (G.exteriorBundleAbelian R q'') k) :
    G.exteriorHCast R (add_assoc q q' q'') (add_assoc i j k)
        (G.exteriorCohomologyProduct R (q+q') q'' (i+j) k (G.exteriorCohomologyProduct R q q' i j x y) z) =
      G.exteriorCohomologyProduct R q (q'+q'') i (j+k) x (G.exteriorCohomologyProduct R q' q'' j k y z) := by
  apply G.exteriorCohomologyState_injective R (q+(q'+q'')) (i+(j+k))
  rw [exteriorCohomologyState_cast, exteriorCohomologyState_product, exteriorCohomologyState_product,
    exteriorCohomologyState_product, exteriorCohomologyState_product, incStateCup_assoc]

end BPFixedPoints.Multigraph
