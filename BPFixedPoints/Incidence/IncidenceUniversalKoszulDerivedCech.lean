import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedBlocks
import BPFixedPoints.Incidence.IncidenceUniversalKoszulCohomology
import BPFixedPoints.Incidence.EdgeExteriorBundleCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCoefficients
import BPFixedPoints.Incidence.VertexPermutationCellChain

/-! # The Hom complex from the cubical cell resolution to `K_G` is the Čech–Koszul complex

`K_G` (`incUniversalKoszulComplex`) is viewed as a cochain complex of abelian sheaves
(`incUniversalKoszulCochainComplex`, with `∧^k F_G^∨` in degree `-k`). The cubical cell resolution
`P = sheafComplex (vertexCoordinateOpen S_G V)` of `ℤ` on the face cover is placed in nonpositive
degrees (`negativeComplex P`). This file identifies the Hom complex between them with the
Čech–Koszul total complex `UnivCechKoszulModule`, `univCechKoszulDifferential` of
`IncidenceUniversalKoszulCech.lean`:

* `cechOfCochain m`: a cochain of degree `m` goes to the family, over edge subsets `S`, of the face
  sections of its `(|S| + m, |S|)`-block projected to the summand `O(-d_S)`, with the
  totalization sign `koszulTotSign |S| = (-1)^{|S|(|S|-1)/2}`. It lands in total degree `-m`
  (`cechOfCochain_mem_piece`), has the left inverse `cochainOfCech` (`cochainOfCech_cechOfCochain`)
  and is onto that total degree (`cechOfCochain_cochainOfCech`).
* `cechOfCochain_δ`: `Φ(δ z) = (-1)^{m+1} D(Φ z)`; the Čech part of `D` comes from the cubical
  differential (`vertexTwistCellNativeEquiv_d`), the Koszul part from the sheaf differential of
  `K_G` on face sections, and the signs from `koszulTotSign_step`.
* Consequences on Hom-complex cohomology: every cocycle of degree `n ≠ 0` is a coboundary
  (`cocycle_mem_coboundaries_of_ne_zero`, from `univCechKoszul_exact_of_ne_zero`), and in degree
  zero the augmentation `cohomologyClassZeroAugmentation` to `𝒰_G = IncidenceRing` is bijective
  (`cohomologyClassZeroAugmentation_bijective`, from `univCechKoszulAugmentation`).

The derived-category statements are in `IncidenceUniversalKoszulDerivedHypercohomology.lean`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools SheafTools.BinaryCells ExtResolutionTools
open HomologicalComplex ComplexShape CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

/-- The totalization sign `(-1)^{k(k-1)/2}` attached to the exterior degree `k`. -/
def koszulTotSign (k : ℕ) : ℤ := (-1) ^ (k.choose 2)

/-- `ε(k+1) = (-1)^k ε(k)`. -/
theorem koszulTotSign_succ (k : ℕ) : koszulTotSign (k + 1) = (-1) ^ k * koszulTotSign k := by
  rw [koszulTotSign, koszulTotSign, Nat.choose_succ_succ', Nat.choose_one_right, pow_add]

/-- `ε(k)^2 = 1`. -/
theorem koszulTotSign_mul_self (k : ℕ) : koszulTotSign k * koszulTotSign k = 1 := by
  rw [koszulTotSign, ← mul_pow]
  simp

section Projections

variable {V E : Type} [DecidableEq V] [Fintype V] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

/-- The projection of the abelian exterior bundle onto the summand of `S`. -/
noncomputable def exteriorAbelianProj (k : ℕ) (S : Set.powersetCard E k) :
    G.exteriorBundleAbelian R k ⟶ vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ)) :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.π (fun S : Set.powersetCard E k => G.exteriorSummand R S) S)

/-- The inclusion of the summand of `S` into the abelian exterior bundle. -/
noncomputable def exteriorAbelianInj (k : ℕ) (S : Set.powersetCard E k) :
    vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ)) ⟶ G.exteriorBundleAbelian R k :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.ι (fun S : Set.powersetCard E k => G.exteriorSummand R S) S)

/-- The projections and inclusions of the abelian exterior bundle sum to the identity. -/
theorem exteriorAbelian_total (k : ℕ) :
    ∑ S : Set.powersetCard E k, G.exteriorAbelianProj R k S ≫ G.exteriorAbelianInj R k S = 𝟙 _ := by
  have h := congrArg (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
    (biproduct.total (f := fun S : Set.powersetCard E k => G.exteriorSummand R S))
  rw [Functor.map_sum, CategoryTheory.Functor.map_id] at h
  simp only [Functor.map_comp] at h
  exact h

/-- Inclusion followed by projection on the same summand is the identity. -/
@[reassoc] theorem exteriorAbelian_inj_proj_self (k : ℕ) (S : Set.powersetCard E k) :
    G.exteriorAbelianInj R k S ≫ G.exteriorAbelianProj R k S = 𝟙 _ := by
  simp only [exteriorAbelianProj, exteriorAbelianInj, ← Functor.map_comp, biproduct.ι_π_self]
  rfl

/-- Inclusion followed by projection on a different summand is zero. -/
@[reassoc] theorem exteriorAbelian_inj_proj_ne (k : ℕ) {S S' : Set.powersetCard E k} (h : S ≠ S') :
    G.exteriorAbelianInj R k S ≫ G.exteriorAbelianProj R k S' = 0 := by
  simp only [exteriorAbelianProj, exteriorAbelianInj, ← Functor.map_comp, biproduct.ι_π_ne _ h,
    Functor.map_zero]

/-- The abelian exterior bundle vanishes above the number of edges. -/
theorem exteriorBundleAbelian_isZero {k : ℕ} (hk : Fintype.card E < k) :
    IsZero (G.exteriorBundleAbelian R k) := by
  have : IsEmpty (Set.powersetCard E k) := ⟨fun S => by
    have h1 := Set.powersetCard.card_eq S
    have h2 := Finset.card_le_univ (S : Finset E)
    omega⟩
  rw [IsZero.iff_id_eq_zero, ← G.exteriorAbelian_total R k]
  simp

end Projections

section Cells

variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Postcomposition with a morphism of sheaves of modules acts on face sections of cell cochains
by the induced map of sections. -/
theorem vertexTwistCellNativeEquiv_comp {a b : V → ℤ} (n : ℕ) (q : V → Fin 3)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a)
    (φ : vertexTwistSheaf R V a ⟶ vertexTwistSheaf R V b) :
    (vertexTwistCellNativeEquiv R V b n
        (f ≫ (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map φ)).val q =
      schemeBaseOpenHomLinear (vertexToBase R V) φ _ ((vertexTwistCellNativeEquiv R V a n f).val q) := by
  by_cases hq : (faceDegree q : ℤ) = n
  · have h1 := vertexTwistCellNativeEquiv_apply R V b n
      (f ≫ (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map φ) (faceIndexOfDegree V n q hq)
    have h2 := vertexTwistCellNativeEquiv_apply R V a n f (faceIndexOfDegree V n q hq)
    change _ = schemeBaseOpenHomLinear (vertexToBase R V) φ _
      ((vertexTwistCellNativeEquiv R V a n f).val (faceIndexOfDegree V n q hq).val)
    erw [h1, h2, sectionsEquiv_comp]
    rfl
  · rw [vertexTwistCellNativeEquiv_apply_ne R V b n _ q hq,
      vertexTwistCellNativeEquiv_apply_ne R V a n _ q hq, map_zero]

/-- The face-section additive map of cell cochains. -/
noncomputable def cellFace (a : V → ℤ) (n : ℕ) (q : V → Fin 3) :
    (sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a) →+
      vertexTwistCubicalFace R V a q where
  toFun f := (vertexTwistCellNativeEquiv R V a n f).val q
  map_zero' := by rw [map_zero]; rfl
  map_add' f g := by rw [map_add]; rfl

/-- `cellFace` is the face section of the cell cochain. -/
theorem cellFace_apply (a : V → ℤ) (n : ℕ) (q : V → Fin 3)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V a) :
    cellFace R V a n q f = (vertexTwistCellNativeEquiv R V a n f).val q := rfl

/-- The part of a cubical cochain in one face degree. -/
noncomputable def vertexTwistDegreeProj (a : V → ℤ) (n : ℤ) (x : VertexTwistCubicalSections R V a) :
    vertexTwistCubicalDegree R V a n :=
  ⟨fun q => if (faceDegree q : ℤ) = n then x q else 0, fun q hq => by simp [hq]⟩

/-- The degree part of a cochain already of that degree is the cochain itself. -/
theorem vertexTwistDegreeProj_val_of_mem (a : V → ℤ) (n : ℤ) (x : VertexTwistCubicalSections R V a)
    (hx : x ∈ vertexTwistCubicalDegree R V a n) : (vertexTwistDegreeProj R V a n x).val = x := by
  funext q
  change (if (faceDegree q : ℤ) = n then x q else 0) = x q
  by_cases hq : (faceDegree q : ℤ) = n
  · simp [hq]
  · simp only [hq, ite_false]
    exact (hx q hq).symm

/-- A cubical cochain of negative face degree vanishes. -/
theorem vertexTwistCubicalDegree_eq_zero_of_neg (a : V → ℤ) {n : ℤ} (hn : n < 0)
    (x : VertexTwistCubicalSections R V a) (hx : x ∈ vertexTwistCubicalDegree R V a n) : x = 0 := by
  funext q
  exact hx q (by omega)

end Cells

section Koszul

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- **The universal Koszul complex `K_G` as a chain complex of abelian sheaves**: the image of
`incUniversalKoszulComplex` under the forgetful functor to abelian sheaves. -/
noncomputable def incUniversalKoszulAbelianComplex :
    ChainComplex (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat.{0}) ℕ :=
  ((SheafOfModules.toSheaf (vertexScheme (IncCoeffRing E) V).ringCatSheaf).mapHomologicalComplex
    _).obj G.incUniversalKoszulComplex

/-- The terms of the abelian `K_G` are the abelian exterior bundles. -/
theorem incUniversalKoszulAbelianComplex_X (k : ℕ) :
    G.incUniversalKoszulAbelianComplex.X k = G.exteriorBundleAbelian (IncCoeffRing E) k := rfl

/-- The differentials of the abelian `K_G` are the Koszul differentials. -/
theorem incUniversalKoszulAbelianComplex_d (k : ℕ) :
    G.incUniversalKoszulAbelianComplex.d (k + 1) k =
      (SheafOfModules.toSheaf (vertexScheme (IncCoeffRing E) V).ringCatSheaf).map
        (G.univKoszulDifferential MvPolynomial.X k) := by
  simp only [incUniversalKoszulAbelianComplex, Functor.mapHomologicalComplex_obj_d,
    incUniversalKoszulComplex, univKoszulComplex_d]

/-- **The universal Koszul complex `K_G` as a cochain complex of abelian sheaves**, with
`∧^k F_G^∨` in cohomological degree `-k`. -/
noncomputable abbrev incUniversalKoszulCochainComplex :
    CochainComplex (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat.{0}) ℤ :=
  G.incUniversalKoszulAbelianComplex.extend (embeddingUpIntLE 0)

/-- The Koszul differential followed by the projection to the summand of `T`. -/
theorem incUniversalKoszulAbelianComplex_d_proj {k : ℕ}
    {X : Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0}}
    (f : X ⟶ G.exteriorBundleAbelian (IncCoeffRing E) (k + 1)) (T : Set.powersetCard E k) :
    f ≫ G.incUniversalKoszulAbelianComplex.d (k + 1) k ≫ G.exteriorAbelianProj (IncCoeffRing E) k T =
      ∑ e : E, if h : e ∉ (T : Finset E) then
        Koszul.sign (A := ℤ) (T : Finset E) e •
          (f ≫ G.exteriorAbelianProj (IncCoeffRing E) (k + 1) (powersetCardInsert T e h) ≫
            (SheafOfModules.toSheaf (vertexScheme (IncCoeffRing E) V).ringCatSheaf).map
              (G.univKoszulComponent MvPolynomial.X T e h))
      else 0 := by
  rw [incUniversalKoszulAbelianComplex_d, exteriorAbelianProj, ← Functor.map_comp,
    univKoszulDifferential, biproduct.lift_π, Functor.map_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · simp only [h, not_false_eq_true, dite_true, Functor.map_zsmul, Functor.map_comp,
      Preadditive.comp_zsmul]
    rfl
  · simp only [h, dite_false, Functor.map_zero, comp_zero]

end Koszul

section Comparison

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- **From Hom-complex cochains to the Čech–Koszul total module.** A cochain `z` of degree `m`
from the negative cubical cell resolution to `K_G` has, for every edge subset `S`, a block
`P_i ⟶ ∧^{|S|}` with `i = |S| + m`; its projection to the summand `O(-d_S)` is a family of
sections on the faces of degree `i`. The `S`-component of the result is this family, multiplied
by the totalization sign `ε(|S|) = (-1)^{|S|(|S|-1)/2}`. -/
noncomputable def cechOfCochain (m : ℤ) :
    Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m →+ G.UnivCechKoszulModule :=
  AddMonoidHom.mk' (fun z S => if h : 0 ≤ (S.card : ℤ) + m then
      koszulTotSign S.card • (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ))
        ((S.card : ℤ) + m).toNat
        (cochainBlock _ _ ((S.card : ℤ) + m).toNat S.card (by omega) z ≫
          G.exteriorAbelianProj (IncCoeffRing E) S.card ⟨S, rfl⟩)).val
    else 0) (by
      intro z z'
      funext S
      by_cases h : 0 ≤ (S.card : ℤ) + m
      · simp only [h, dite_true, Pi.add_apply, map_add, Preadditive.add_comp, Submodule.coe_add,
          smul_add]
      · simp only [h, dite_false, Pi.add_apply, add_zero])

/-- The components of `cechOfCochain`. -/
theorem cechOfCochain_apply {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) (S : Finset E) :
    G.cechOfCochain m z S = if h : 0 ≤ (S.card : ℤ) + m then
      koszulTotSign S.card • (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ))
        ((S.card : ℤ) + m).toNat
        (cochainBlock _ _ ((S.card : ℤ) + m).toNat S.card (by omega) z ≫
          G.exteriorAbelianProj (IncCoeffRing E) S.card ⟨S, rfl⟩)).val
    else 0 := rfl

/-- The component of `cechOfCochain` at an edge subset of negative total degree vanishes. -/
theorem cechOfCochain_of_neg {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) (S : Finset E) (h : (S.card : ℤ) + m < 0) :
    G.cechOfCochain m z S = 0 := by
  rw [cechOfCochain_apply, dite_eq_right (by omega)]

/-- **The components of `cechOfCochain` are the signed face sections of the blocks.** -/
theorem cechOfCochain_powersetCard {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) (k : ℕ) (S : Set.powersetCard E k) (i : ℕ)
    (h : (i : ℤ) = k + m) :
    G.cechOfCochain m z S = koszulTotSign k •
      (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) i
        (cochainBlock _ _ i k h z ≫ G.exteriorAbelianProj (IncCoeffRing E) k S)).val := by
  have hc : (S : Finset E).card = k := Set.powersetCard.card_eq S
  have key : ∀ (k₁ : ℕ) (_ : k₁ = k) (i₁ : ℕ) (_ : i₁ = i) (h₁ : (i₁ : ℤ) = k₁ + m)
      (hS : (S : Finset E) ∈ Set.powersetCard E k₁),
      (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) i₁
        (cochainBlock _ _ i₁ k₁ h₁ z ≫ G.exteriorAbelianProj (IncCoeffRing E) k₁ ⟨S, hS⟩)).val =
      (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) i
        (cochainBlock _ _ i k h z ≫ G.exteriorAbelianProj (IncCoeffRing E) k S)).val := by
    rintro _ rfl _ rfl _ _
    rfl
  rw [cechOfCochain_apply, dite_eq_left (by omega), key _ hc (((S : Finset E).card : ℤ) + m).toNat (by omega), hc]

/-- **`cechOfCochain` lands in the total degree `-m`** (homological convention of
`univCechKoszulPiece`). -/
theorem cechOfCochain_mem_piece {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) :
    G.cechOfCochain m z ∈ G.univCechKoszulPiece (-m) := by
  intro S q hq
  by_cases h : 0 ≤ (S.card : ℤ) + m
  · rw [cechOfCochain_apply, dite_eq_left h, Pi.smul_apply,
      (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) _ _).property q
        (by omega), smul_zero]
  · rw [cechOfCochain_of_neg G z S (by omega)]
    rfl

/-- **From the Čech–Koszul total module to Hom-complex cochains**: the cochain whose block
`P_i ⟶ ∧^k` has, on the summand of every `k`-element edge subset `S`, the cell cochain with face
sections `ε(k)` times the degree-`i` part of the `S`-component. -/
noncomputable def cochainOfCech (m : ℤ) (y : G.UnivCechKoszulModule) :
    Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m :=
  cochainOfBlocks _ _ fun i k _ => ∑ S : Set.powersetCard E k,
    (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) i).symm
      (vertexTwistDegreeProj (IncCoeffRing E) V _ i (koszulTotSign k • y S)) ≫
        G.exteriorAbelianInj (IncCoeffRing E) k S

/-- **`cochainOfCech` is a left inverse of `cechOfCochain`.** -/
theorem cochainOfCech_cechOfCochain {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) :
    G.cochainOfCech m (G.cechOfCochain m z) = z := by
  apply cochain_ext_of_blocks
  intro i k h
  rw [cochainOfCech, cochainBlock_ofBlocks]
  have hS : ∀ S : Set.powersetCard E k,
      (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ)) i).symm
        (vertexTwistDegreeProj (IncCoeffRing E) V _ i (koszulTotSign k • G.cechOfCochain m z S)) =
      cochainBlock _ _ i k h z ≫ G.exteriorAbelianProj (IncCoeffRing E) k S := by
    intro S
    rw [cechOfCochain_powersetCard G z k S i h, smul_smul, koszulTotSign_mul_self, one_smul]
    apply (AddEquiv.symm_apply_eq _).mpr
    apply Subtype.ext
    exact vertexTwistDegreeProj_val_of_mem _ _ _ _ _ (Submodule.coe_mem _)
  simp only [hS, Category.assoc, ← Preadditive.comp_sum, G.exteriorAbelian_total]
  exact Category.comp_id _

/-- **`cechOfCochain` is onto the total degree `-m`**, with right inverse `cochainOfCech`. -/
theorem cechOfCochain_cochainOfCech {m : ℤ} (y : G.UnivCechKoszulModule)
    (hy : y ∈ G.univCechKoszulPiece (-m)) :
    G.cechOfCochain m (G.cochainOfCech m y) = y := by
  funext S
  by_cases h : 0 ≤ (S.card : ℤ) + m
  · let S' : Set.powersetCard E S.card := ⟨S, rfl⟩
    have hA := cechOfCochain_powersetCard G (G.cochainOfCech m y) S.card S'
      (((S.card : ℤ) + m).toNat) (by omega)
    refine hA.trans ?_
    rw [cochainOfCech, cochainBlock_ofBlocks, Preadditive.sum_comp, Finset.sum_eq_single S']
    · rw [Category.assoc, exteriorAbelian_inj_proj_self, Category.comp_id, AddEquiv.apply_symm_apply,
        vertexTwistDegreeProj_val_of_mem, smul_smul, koszulTotSign_mul_self, one_smul]
      apply Submodule.smul_of_tower_mem
      intro q hq
      exact hy S q (by omega)
    · intro S'' _ hne
      rw [Category.assoc, exteriorAbelian_inj_proj_ne _ _ _ hne, comp_zero]
    · intro hS'
      exact absurd (Finset.mem_univ S') hS'
  · rw [cechOfCochain_of_neg G _ S (by omega)]
    symm
    exact vertexTwistCubicalDegree_eq_zero_of_neg (IncCoeffRing E) V _ (by omega : (S.card : ℤ) + m < 0)
      (y S) (fun q hq => hy S q (by omega))

/-- `cechOfCochain` is injective. -/
theorem cechOfCochain_injective (m : ℤ) : Function.Injective (G.cechOfCochain m) := fun z z' h => by
  rw [← G.cochainOfCech_cechOfCochain z, ← G.cochainOfCech_cechOfCochain z', h]

end Comparison

section Differential

/-- The scalar identity behind the totalization signs: `ε(k) s = (-1)^{m'} (-1)^i s ε(k+1)` when
`i = k + m'`. -/
theorem koszulTotSign_step {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (k i : ℕ) (m' : ℤ) (h : (i : ℤ) = k + m') (idx : ℕ) (A : M) :
    koszulTotSign k • ((-1 : ℤ) ^ idx • A) =
      (m'.negOnePow : ℤ) • (((-1 : R) ^ i * (-1 : R) ^ idx) • (koszulTotSign (k + 1) • A)) := by
  rw [← Int.cast_smul_eq_zsmul R (koszulTotSign k), ← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ idx),
    ← Int.cast_smul_eq_zsmul R (m'.negOnePow : ℤ), ← Int.cast_smul_eq_zsmul R (koszulTotSign (k + 1)),
    smul_smul, smul_smul, smul_smul]
  congr 1
  have hN : ((m'.negOnePow : ℤ) : R) = (-1 : R) ^ i * (-1 : R) ^ k := by
    rw [show m' = ((i : ℕ) : ℤ) - ((k : ℕ) : ℤ) by omega, Int.negOnePow_sub, Units.val_mul,
      Int.cast_mul, Int.cast_negOnePow_natCast, Int.cast_negOnePow_natCast]
  rw [hN, koszulTotSign_succ]
  push_cast
  have h1 := neg_one_pow_mul_self' (A := R) i
  have h2 := neg_one_pow_mul_self' (A := R) k
  linear_combination (-((koszulTotSign k : R) * (-1 : R) ^ idx * ((-1 : R) ^ k * (-1 : R) ^ k))) * h1 -
    ((koszulTotSign k : R) * (-1 : R) ^ idx) * h2

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- Face sections of the Koszul differential of `K_G` applied to a cell cochain. -/
theorem cellFace_koszul {k i : ℕ} (q : V → Fin 3) (T : Set.powersetCard E k)
    (f : sheafTerm (vertexCoordinateOpen (IncCoeffRing E) V) i ⟶
      G.exteriorBundleAbelian (IncCoeffRing E) (k + 1)) :
    (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg T v : ℤ)) i
      (f ≫ G.incUniversalKoszulAbelianComplex.d (k + 1) k ≫
        G.exteriorAbelianProj (IncCoeffRing E) k T)).val q =
    ∑ e : E, if h : e ∉ (T : Finset E) then
      Koszul.sign (A := ℤ) (T : Finset E) e •
        G.univCechKoszulComponent (T : Finset E) e h q
          ((vertexTwistCellNativeEquiv (IncCoeffRing E) V
            (fun v => -(G.deg (insert e (T : Finset E)) v : ℤ)) i
            (f ≫ G.exteriorAbelianProj (IncCoeffRing E) (k + 1) (powersetCardInsert T e h))).val q)
    else 0 := by
  rw [incUniversalKoszulAbelianComplex_d_proj, ← cellFace_apply, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : e ∉ (T : Finset E)
  · rw [dite_eq_left h, dite_eq_left h, map_zsmul, cellFace_apply, ← Category.assoc]
    erw [vertexTwistCellNativeEquiv_comp]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- **`cechOfCochain` intertwines the Hom-complex differential with the Čech–Koszul total
differential**, up to the sign `(-1)^{m'}`: `Φ(δ z) = (-1)^{m'} D(Φ z)`. -/
theorem cechOfCochain_δ {m m' : ℤ} (hm : m + 1 = m')
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) :
    G.cechOfCochain m' (δ m m' z) =
      (m'.negOnePow : ℤ) • G.univCechKoszulDifferential (G.cechOfCochain m z) := by
  funext T q
  rw [Pi.smul_apply, Pi.smul_apply]
  have hD : G.univCechKoszulDifferential (G.cechOfCochain m z) T q =
      vertexTwistCubicalD (IncCoeffRing E) V _ (G.cechOfCochain m z T) q +
        G.univCechKoszulPerturbation (G.cechOfCochain m z) T q := rfl
  rw [hD, univCechKoszulPerturbation_apply]
  let T' : Set.powersetCard E T.card := ⟨T, rfl⟩
  by_cases hk : 0 ≤ (T.card : ℤ) + m'
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = T.card + m' := ⟨_, Int.toNat_of_nonneg hk⟩
    have hins : ∀ (e : E) (he : e ∉ T), G.cechOfCochain m z (insert e T) =
        koszulTotSign (T.card + 1) •
          (vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg (insert e T) v : ℤ)) i
            (cochainBlock _ _ i (T.card + 1) (by omega) z ≫
              G.exteriorAbelianProj (IncCoeffRing E) (T.card + 1) (powersetCardInsert T' e he))).val :=
      fun e he => cechOfCochain_powersetCard G z (T.card + 1) (powersetCardInsert T' e he) i (by omega)
    have hsum : (∑ e : E, if he : e ∉ T then
        ((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
          G.univCechKoszulComponent T e he q (G.cechOfCochain m z (insert e T) q) else 0) =
        ∑ e : E, if he : e ∉ T then
        ((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
          (koszulTotSign (T.card + 1) • G.univCechKoszulComponent T e he q
            ((vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg (insert e T) v : ℤ)) i
              (cochainBlock _ _ i (T.card + 1) (by omega) z ≫
                G.exteriorAbelianProj (IncCoeffRing E) (T.card + 1)
                  (powersetCardInsert T' e he))).val q)) else 0 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∉ T
      · rw [dite_eq_left he, dite_eq_left he, hins e he, Pi.smul_apply, map_zsmul]
      · rw [dite_eq_right he, dite_eq_right he]
    rw [hsum]
    have hL := cechOfCochain_powersetCard G (δ m m' z) T.card T' i hi
    rw [show G.cechOfCochain m' (δ m m' z) T = _ from hL, Pi.smul_apply]
    -- the per-edge sign identity
    have hterm : ∀ (e : E) (he : e ∉ T) (A : vertexTwistCubicalFace (IncCoeffRing E) V
          (fun v => -(G.deg T v : ℤ)) q),
        ((faceDegree q : ℤ) ≠ i → A = 0) →
        koszulTotSign T.card • (Koszul.sign (A := ℤ) T e • A) =
          (m'.negOnePow : ℤ) • (((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
            (koszulTotSign (T.card + 1) • A)) := by
      intro e he A hA
      by_cases hq : (faceDegree q : ℤ) = i
      · have hq' : faceDegree q = i := by omega
        rw [hq']
        exact koszulTotSign_step T.card i m' hi _ A
      · rw [hA hq]
        simp
    have hface : ∀ (e : E) (he : e ∉ T), (faceDegree q : ℤ) ≠ i →
        G.univCechKoszulComponent T e he q
          ((vertexTwistCellNativeEquiv (IncCoeffRing E) V (fun v => -(G.deg (insert e T) v : ℤ)) i
            (cochainBlock _ _ i (T.card + 1) (by omega) z ≫
              G.exteriorAbelianProj (IncCoeffRing E) (T.card + 1)
                (powersetCardInsert T' e he))).val q) = 0 := by
      intro e he hq
      rw [vertexTwistCellNativeEquiv_apply_ne _ _ _ _ _ q hq, map_zero]
    rcases i with _ | j
    · rw [cochainBlock_δ_zero _ _ hm z T.card hi, Category.assoc, cellFace_koszul,
        cechOfCochain_of_neg G z T (by omega), map_zero, Pi.zero_apply, zero_add,
        Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∉ T
      · rw [dite_eq_left he, dite_eq_left he]
        exact hterm e he _ (hface e he)
      · rw [dite_eq_right he, dite_eq_right he, smul_zero, smul_zero]
    · rw [cochainBlock_δ_succ _ _ hm z j T.card hi, Preadditive.add_comp, Units.smul_def,
        Preadditive.zsmul_comp, ← cellFace_apply, map_add, map_zsmul, cellFace_apply, cellFace_apply,
        Category.assoc, cellFace_koszul, Category.assoc,
        show G.cechOfCochain m z T = _ from cechOfCochain_powersetCard G z T.card T' j (by omega),
        map_zsmul, Pi.smul_apply,
        vertexTwistCellNativeEquiv_d (IncCoeffRing E) V (G.deg T) j]
      rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, add_comm]
      congr 1
      · rw [smul_comm]
      · refine Finset.sum_congr rfl fun e _ => ?_
        by_cases he : e ∉ T
        · rw [dite_eq_left he, dite_eq_left he]
          exact hterm e he _ (hface e he)
        · rw [dite_eq_right he, dite_eq_right he, smul_zero, smul_zero]
  · rw [cechOfCochain_of_neg G _ T (by omega), cechOfCochain_of_neg G z T (by omega), map_zero,
      Pi.zero_apply, zero_add]
    have hz : ∀ e : E, (if he : e ∉ T then
        ((-1 : IncCoeffRing E) ^ faceDegree q * Koszul.sign T e) •
          G.univCechKoszulComponent T e he q (G.cechOfCochain m z (insert e T) q) else 0) = 0 := by
      intro e
      by_cases he : e ∉ T
      · rw [dite_eq_left he, cechOfCochain_of_neg G z (insert e T)
          (by rw [Finset.card_insert_of_notMem he]; push_cast; omega), Pi.zero_apply, map_zero,
          smul_zero]
      · rw [dite_eq_right he]
    rw [Finset.sum_eq_zero fun e _ => hz e, smul_zero]

end Differential

section Classes

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- **Cocycles go to cycles.** The image under `cechOfCochain` of a cocycle of the Hom complex is
a cycle of the Čech–Koszul total complex. -/
theorem cechOfCochain_cocycle {n : ℤ}
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex n) :
    G.univCechKoszulDifferential (G.cechOfCochain n (z : Cochain _ _ n)) = 0 := by
  have h := G.cechOfCochain_δ (rfl : n + 1 = n + 1) (z : Cochain _ _ n)
  rw [Cocycle.δ_eq_zero, map_zero] at h
  calc G.univCechKoszulDifferential (G.cechOfCochain n z)
      = (((n + 1).negOnePow * (n + 1).negOnePow : ℤˣ) : ℤ) •
          G.univCechKoszulDifferential (G.cechOfCochain n z) := by
        rw [Int.units_mul_self, Units.val_one, one_smul]
    _ = ((n + 1).negOnePow : ℤ) • (((n + 1).negOnePow : ℤ) •
          G.univCechKoszulDifferential (G.cechOfCochain n z)) := by
        rw [Units.val_mul, mul_smul]
    _ = 0 := by rw [← h, smul_zero]

/-- **Vanishing of Hom-complex cohomology outside degree zero.** For `n ≠ 0`, every cocycle of
degree `n` from the negative cubical cell resolution to `K_G` is a coboundary: transport it to
the Čech–Koszul total complex with `cechOfCochain`, use `univCechKoszul_exact_of_ne_zero`, and
transport the primitive back with `cochainOfCech`. -/
theorem cocycle_mem_coboundaries_of_ne_zero {n : ℤ} (hn : n ≠ 0)
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex n) :
    z ∈ coboundaries _ _ n := by
  rw [mem_coboundaries_iff z (n - 1) (by omega)]
  have hn' : -n ≠ 0 := by omega
  obtain ⟨y, hy, hDy⟩ := G.univCechKoszul_exact_of_ne_zero hn' (G.cechOfCochain n z.1)
    (G.cechOfCochain_mem_piece z.1) (G.cechOfCochain_cocycle z)
  have hy' : y ∈ G.univCechKoszulPiece (-(n - 1)) := by
    rwa [show -(n - 1) = -n + 1 by ring]
  refine ⟨(n.negOnePow : ℤ) • G.cochainOfCech (n - 1) y, ?_⟩
  apply G.cechOfCochain_injective n
  rw [δ_smul, map_zsmul, G.cechOfCochain_δ (by omega : n - 1 + 1 = n),
    G.cechOfCochain_cochainOfCech y hy', hDy, smul_smul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, one_smul]

/-- A degree-zero cocycle gives a degree-zero cycle of the Čech–Koszul total complex. -/
noncomputable def cocycleZeroToCycles :
    Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0 →+ G.univCechKoszulCycles0 where
  toFun z := ⟨G.cechOfCochain 0 z.1, by
    refine ⟨?_, G.cechOfCochain_cocycle z⟩
    have h := G.cechOfCochain_mem_piece z.1
    rwa [neg_zero] at h⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (G.cechOfCochain 0)
  map_add' z z' := by
    apply Subtype.ext
    exact map_add (G.cechOfCochain 0) z.1 z'.1

/-- The underlying Čech–Koszul element of `cocycleZeroToCycles z` is `cechOfCochain 0 z`. -/
@[simp] theorem cocycleZeroToCycles_val
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    (G.cocycleZeroToCycles z).val = G.cechOfCochain 0 z.1 := rfl

/-- **The augmentation of Hom-complex cohomology in degree zero**: the class of a degree-zero
cocycle goes to the augmentation `univCechKoszulAugmentation` of its Čech–Koszul cycle in
`𝒰_G = IncidenceRing`. Coboundaries go to zero by `univCechKoszulAugmentation_eq_zero_iff`. -/
noncomputable def cohomologyClassZeroAugmentation :
    CohomologyClass (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0 →+ G.IncidenceRing :=
  CohomologyClass.descAddMonoidHom
    (G.univCechKoszulAugmentation.toAddMonoidHom.comp G.cocycleZeroToCycles) (by
      intro z hz
      rw [mem_coboundaries_iff z (-1) (by norm_num)] at hz
      obtain ⟨w, hw⟩ := hz
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        univCechKoszulAugmentation_eq_zero_iff]
      refine ⟨G.cechOfCochain (-1) w, ?_, ?_⟩
      · have h := G.cechOfCochain_mem_piece w
        rwa [neg_neg] at h
      · rw [cocycleZeroToCycles_val, ← hw, G.cechOfCochain_δ (by norm_num : (-1 : ℤ) + 1 = 0),
          Int.negOnePow_zero, Units.val_one, one_smul])

/-- The augmentation of the class of a cocycle. -/
theorem cohomologyClassZeroAugmentation_mk
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) :
    G.cohomologyClassZeroAugmentation (CohomologyClass.mk z) =
      G.univCechKoszulAugmentation (G.cocycleZeroToCycles z) := rfl

/-- **Hom-complex cohomology in degree zero is `𝒰_G`**: the augmentation is bijective. -/
theorem cohomologyClassZeroAugmentation_bijective :
    Function.Bijective G.cohomologyClassZeroAugmentation := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := c.mk_surjective
    rw [cohomologyClassZeroAugmentation_mk, univCechKoszulAugmentation_eq_zero_iff] at hc
    obtain ⟨y, hy, hDy⟩ := hc
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff z (-1) (by norm_num)]
    have hy' : y ∈ G.univCechKoszulPiece (-(-1)) := by rwa [neg_neg]
    refine ⟨G.cochainOfCech (-1) y, ?_⟩
    apply G.cechOfCochain_injective 0
    rw [G.cechOfCochain_δ (by norm_num : (-1 : ℤ) + 1 = 0), G.cechOfCochain_cochainOfCech y hy',
      Int.negOnePow_zero, Units.val_one, one_smul, hDy, cocycleZeroToCycles_val]
  · intro u
    obtain ⟨x, hx⟩ := G.univCechKoszulAugmentation_surjective u
    have hx0 : x.val ∈ G.univCechKoszulPiece (-0) := by
      rw [neg_zero]
      exact x.property.1
    have hcoc : δ 0 1 (G.cochainOfCech 0 x.val) = 0 := by
      apply G.cechOfCochain_injective 1
      rw [G.cechOfCochain_δ (by norm_num : (0 : ℤ) + 1 = 1), G.cechOfCochain_cochainOfCech _ hx0,
        LinearMap.mem_ker.mp x.property.2, smul_zero, map_zero]
    refine ⟨CohomologyClass.mk (Cocycle.mk _ 1 (by norm_num) hcoc), ?_⟩
    rw [cohomologyClassZeroAugmentation_mk, ← hx]
    congr 1
    apply Subtype.ext
    rw [cocycleZeroToCycles_val]
    exact G.cechOfCochain_cochainOfCech _ hx0

end Classes

end BPFixedPoints.Multigraph
