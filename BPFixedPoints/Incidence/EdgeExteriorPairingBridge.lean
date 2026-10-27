import BPFixedPoints.Incidence.EdgeExteriorBundleProduct
import BPFixedPoints.Incidence.EdgeExteriorChart

/-! # The exterior product pairing is exterior multiplication of sections

The sheaf pairing `exteriorWedgePairing` that defines the product on actual cohomology of the
exterior bundle evaluates, on the sections over every open, to the section exterior pairing
`exteriorSectionPairing` of the chart identification. Both project the factors to their
summands, multiply with the original twist section product, and place the product, with the
shuffle sign, in the summand of the union of disjoint edge subsets; they differ only in how
the union summand and the twist identity are written (`edgeSubsetUnion` with
`exteriorTwist_edgeSubsetUnion` against `Set.powersetCard.disjUnion` with
`exteriorTwist_disjUnion`), and in whether the maps are morphisms of abelian sheaves or
sections of morphisms of sheaves of modules. Hence, on sections over any open and in positive
degrees, the sheaf pairing sends wedges of sections of the dual edge bundle to the wedge of
the concatenated tuple.

The comparison is assembled from small evaluation lemmas, each identifying one abelian sheaf
morphism on sections with the corresponding section map, and the index change from
`edgeSubsetUnion` to `disjUnion` is a separate transport lemma. The definition of
`exteriorWedgeMap` is unfolded through a congruence lemma comparing only the proofs of the twist
identity inside `eqToHom`, so that no kernel check has to unfold integer multiples of morphisms of
abelian sheaves.
-/

namespace BPFixedPoints.Multigraph
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace ProjectiveLine SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars true
noncomputable section
variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

/-! ### Evaluation of abelian sheaf morphisms on sections -/

omit [DecidableEq V] in
/-- On sections, a composite of abelian sheaf morphisms on the vertex product is the composite of
the section maps. -/
theorem vertexAbelianHom_comp_app
    {F₁ F₂ F₃ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) (W : (vertexScheme R V).Opens) (z : F₁.obj.obj (op W)) :
    (f ≫ g).hom.app (op W) z = g.hom.app (op W) (f.hom.app (op W) z) := rfl

omit [DecidableEq V] in
/-- On sections, an integer multiple of an abelian sheaf morphism on the vertex product is that
multiple of the section map. -/
theorem vertexAbelianHom_zsmul_app
    {F₁ F₂ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (n : ℤ) (f : F₁ ⟶ F₂) (W : (vertexScheme R V).Opens) (z : F₁.obj.obj (op W)) :
    (n • f).hom.app (op W) z = n • f.hom.app (op W) z := rfl

omit [DecidableEq V] in
/-- On sections, the zero abelian sheaf morphism on the vertex product vanishes. -/
theorem vertexAbelianHom_zero_app
    {F₁ F₂ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (W : (vertexScheme R V).Opens) (z : F₁.obj.obj (op W)) :
    (0 : F₁ ⟶ F₂).hom.app (op W) z = 0 := rfl

omit [DecidableEq V] in
/-- On sections, the abelian equality morphism of two equal multi-twists is the transport of
twist sections. -/
theorem vertexTwistAbelian_eqToHom_app {a b : V → ℤ} (h : a = b) (W : (vertexScheme R V).Opens)
    (z : Γ(vertexTwistSheaf R V a, W)) :
    (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h)).hom.app (op W) z = vertexTwistCast R h W z := by
  subst h
  rfl

omit [DecidableEq V] in
/-- On sections, the abelian twist pairing is the original twist section product. -/
theorem vertexTwistAbelianSectionPairing_apply (a b : V → ℤ) (W : (vertexScheme R V).Opens)
    (x : Γ(vertexTwistSheaf R V a, W)) (y : Γ(vertexTwistSheaf R V b, W)) :
    (vertexTwistAbelianSectionPairing R V a b).pairing W x y = vertexTwistSectionProduct R V a b W x y :=
  rfl

omit [LinearOrder E] in
/-- On sections, the abelian summand inclusion of the exterior bundle is the section inclusion. -/
theorem exteriorIncl_app (q : ℕ) (W : (vertexScheme R V).Opens) (S : Set.powersetCard E q)
    (z : Γ(vertexTwistSheaf R V (fun v => -(G.deg (S : Finset E) v : ℤ)), W)) :
    (G.exteriorIncl R q S).hom.app (op W) z = G.exteriorSectionInclusion R q W S z := rfl

omit [LinearOrder E] in
/-- On sections, the abelian summand projection of the exterior bundle is the section projection. -/
theorem exteriorProj_app (q : ℕ) (W : (vertexScheme R V).Opens) (S : Set.powersetCard E q)
    (x : Γ(G.exteriorBundle R q, W)) :
    (G.exteriorProj R q S).hom.app (op W) x = G.exteriorSectionProjection R q W S x := rfl

omit [LinearOrder E] in
/-- On sections, the twist identity followed by the abelian summand inclusion is the section
inclusion of the transported section. -/
theorem exteriorIncl_eqToHom_app {q : ℕ} {a : V → ℤ} (S : Set.powersetCard E q)
    (h : a = fun v => -(G.deg (S : Finset E) v : ℤ)) (W : (vertexScheme R V).Opens)
    (z : Γ(vertexTwistSheaf R V a, W)) :
    (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h) ≫ G.exteriorIncl R q S).hom.app (op W) z =
      G.exteriorSectionInclusion R q W S (vertexTwistCast R h W z) :=
  (vertexAbelianHom_comp_app R (eqToHom (congrArg (vertexTwistAbelianSheaf R V) h))
      (G.exteriorIncl R q S) W z).trans
    ((congrArg ((G.exteriorIncl R q S).hom.app (op W)) (vertexTwistAbelian_eqToHom_app R h W z)).trans
      (G.exteriorIncl_app R q W S (vertexTwistCast R h W z)))

/-! ### The two descriptions of the union summand -/

omit [Fintype E] in
/-- The two descriptions of the union summand of disjoint edge subsets agree. -/
theorem edgeSubsetUnion_eq_disjUnion {p q : ℕ} {S : Set.powersetCard E p} {T : Set.powersetCard E q}
    (h : Disjoint (S : Finset E) (T : Finset E)) :
    edgeSubsetUnion S T h = Set.powersetCard.disjUnion h :=
  Subtype.ext (Finset.disjUnion_eq_union _ _ h).symm

omit [LinearOrder E] in
/-- The section inclusion of a transported twist section does not depend on how the summand and
the twist identity are written. -/
theorem exteriorSectionInclusion_cast_congr {n : ℕ} {U₁ U₂ : Set.powersetCard E n} (hU : U₁ = U₂)
    {a : V → ℤ} (h₁ : a = fun v => -(G.deg (U₁ : Finset E) v : ℤ))
    (h₂ : a = fun v => -(G.deg (U₂ : Finset E) v : ℤ)) (W : (vertexScheme R V).Opens)
    (z : Γ(vertexTwistSheaf R V a, W)) :
    G.exteriorSectionInclusion R n W U₁ (vertexTwistCast R h₁ W z) =
      G.exteriorSectionInclusion R n W U₂ (vertexTwistCast R h₂ W z) := by
  subst hU
  rfl

/-! ### Exterior multiplication of summands on sections -/

omit [DecidableEq V] in
/-- An integer multiple of an abelian equality morphism followed by a morphism does not depend on
the proof of the equality. -/
theorem vertexAbelian_zsmul_eqToHom_comp_congr
    {F₁ F₂ F₃ : Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}}
    (n : ℤ) (h₁ h₂ : F₁ = F₂) (g : F₂ ⟶ F₃) :
    n • (eqToHom h₁ ≫ g) = n • (eqToHom h₂ ≫ g) := rfl

/-- For disjoint edge subsets, exterior multiplication of the summands is the shuffle sign times
the twist identity followed by the inclusion of the union summand. -/
theorem exteriorWedgeMap_of_disjoint {p q : ℕ} {S : Set.powersetCard E p} {T : Set.powersetCard E q}
    (h : Disjoint (S : Finset E) (T : Finset E)) :
    G.exteriorWedgeMap R S T = Koszul.shuffleSign (R := ℤ) (S : Finset E) T •
      (eqToHom (congrArg (vertexTwistAbelianSheaf R V) (G.exteriorTwist_edgeSubsetUnion h)) ≫
        G.exteriorIncl R (p+q) (edgeSubsetUnion S T h)) :=
  (dite_eq_left h).trans (vertexAbelian_zsmul_eqToHom_comp_congr R _ _ _ _)

/-- For edge subsets sharing an edge, exterior multiplication of the summands vanishes. -/
theorem exteriorWedgeMap_of_not_disjoint {p q : ℕ} {S : Set.powersetCard E p}
    {T : Set.powersetCard E q} (h : ¬Disjoint (S : Finset E) (T : Finset E)) :
    G.exteriorWedgeMap R S T = 0 :=
  dite_eq_right h

/-- On sections, exterior multiplication of two summands applied to the original twist section
product is the section-level exterior multiplication of the summands. -/
theorem exteriorWedgeMap_app_sectionProduct {p q : ℕ} (S : Set.powersetCard E p)
    (T : Set.powersetCard E q) (W : (vertexScheme R V).Opens) (x : Γ(G.exteriorSummand R S, W))
    (y : Γ(G.exteriorSummand R T, W)) :
    (G.exteriorWedgeMap R S T).hom.app (op W)
        (vertexTwistSectionProduct R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)) W x y) =
      G.exteriorSummandProduct R S T W x y := by
  by_cases h : Disjoint (S : Finset E) (T : Finset E)
  · have hw := congrArg (fun f => f.hom.app (op W)
      (vertexTwistSectionProduct R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)) W x y))
      (G.exteriorWedgeMap_of_disjoint R h)
    refine hw.trans ((vertexAbelianHom_zsmul_app R _ _ W _).trans ?_)
    refine Eq.trans ?_ (G.exteriorSummandProduct_of_disjoint R h W x y).symm
    refine congrArg (fun z => Koszul.shuffleSign (R := ℤ) (S : Finset E) T • z) ?_
    exact (G.exteriorIncl_eqToHom_app R (edgeSubsetUnion S T h) (G.exteriorTwist_edgeSubsetUnion h) W _).trans
      (G.exteriorSectionInclusion_cast_congr R (edgeSubsetUnion_eq_disjUnion h)
        (G.exteriorTwist_edgeSubsetUnion h) (G.exteriorTwist_disjUnion h) W _)
  · have hw := congrArg (fun f => f.hom.app (op W)
      (vertexTwistSectionProduct R V (fun v => -(G.deg S v : ℤ)) (fun v => -(G.deg T v : ℤ)) W x y))
      (G.exteriorWedgeMap_of_not_disjoint R h)
    exact hw.trans ((vertexAbelianHom_zero_app R W _).trans
      (G.exteriorSummandProduct_of_not_disjoint R h W x y).symm)

/-- On sections, one summand of the exterior wedge pairing is the section-level exterior
multiplication of the summand components. -/
theorem exteriorWedgePairing_summand_app {p q : ℕ} (S : Set.powersetCard E p)
    (T : Set.powersetCard E q) (W : (vertexScheme R V).Opens) (x : Γ(G.exteriorBundle R p, W))
    (y : Γ(G.exteriorBundle R q, W)) :
    (G.exteriorWedgeMap R S T).hom.app (op W)
        ((vertexTwistAbelianSectionPairing R V (fun v => -(G.deg S v : ℤ))
          (fun v => -(G.deg T v : ℤ))).pairing W
            ((G.exteriorProj R p S).hom.app (op W) x) ((G.exteriorProj R q T).hom.app (op W) y)) =
      G.exteriorSummandProduct R S T W (G.exteriorSectionProjection R p W S x)
        (G.exteriorSectionProjection R q W T y) :=
  G.exteriorWedgeMap_app_sectionProduct R S T W (G.exteriorSectionProjection R p W S x)
    (G.exteriorSectionProjection R q W T y)

/-! ### The sheaf pairing on sections -/

/-- The sheaf pairing defining the exterior cohomology product evaluates, on the sections over
every open, to the section exterior pairing. -/
theorem exteriorWedgePairing_eq_sectionPairing (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Γ(G.exteriorBundle R p, W)) (y : Γ(G.exteriorBundle R q, W)) :
    (G.exteriorWedgePairing R p q).pairing W x y = G.exteriorSectionPairing R p q W x y :=
  (G.exteriorWedgePairing_pairing R p q W x y).trans
    ((Fintype.sum_prod_type _).trans
      ((Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ =>
        G.exteriorWedgePairing_summand_app R S T W x y).trans
          (G.exteriorSectionPairing_apply R p q W x y).symm))

/-- On sections over any open and in positive degrees, the sheaf pairing of the exterior product
sends wedges of sections of the dual edge bundle to the wedge of the concatenated tuple. -/
theorem exteriorWedgePairing_wedge (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin (p + 1) → Γ(G.edgeDualBundle R, W)) (y : Fin (q + 1) → Γ(G.edgeDualBundle R, W)) :
    (G.exteriorWedgePairing R (p + 1) (q + 1)).pairing W
        (G.exteriorSectionWedge R p W (exteriorPower.ιMulti _ (p + 1) x))
        (G.exteriorSectionWedge R q W (exteriorPower.ιMulti _ (q + 1) y)) =
      G.exteriorSectionWedge R (p + 1 + q) W (exteriorPower.ιMulti _ (p + 1 + q + 1)
        (Fin.append x y : Fin ((p + 1) + (q + 1)) → Γ(G.edgeDualBundle R, W))) :=
  (G.exteriorWedgePairing_eq_sectionPairing R (p + 1) (q + 1) W _ _).trans
    (G.exteriorSectionPairing_wedge R p q W x y)

end
end BPFixedPoints.Multigraph
