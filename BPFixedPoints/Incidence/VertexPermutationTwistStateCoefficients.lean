import BPFixedPoints.Incidence.VertexPermutationCellChain
import BPFixedPoints.Incidence.VertexPermutationTwistFaces
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCoefficients

/-!
# Coefficients of transported cubical cochains

For `ψ : V ≃ W` and a cubical cochain `f` of the cell complex of `(P¹)^V` with values in `O(-d)`,
the transported cochain `vertexCellCochainPerm R ψ d n f` of `(P¹)^W` with values in `O(-d ∘ ψ⁻¹)`
is the comparison chain map `cellChainMap` (for the coordinate covers), followed by the image of `f`
under `vertexSheafPerm R ψ` and the twist transport `vertexTwistAbelianPermIso`. It is a cocycle
when `f` is (`vertexCellCochainPerm_cycle`).

Proved here: its signed coefficient chain (`vertexTwistCellCoefficientEquiv`) is the signed
reordering `cechVertexPerm R ψ` of the coefficient chain of `f`
(`vertexCellCochainPerm_coefficient`). The proof compares face components: the Koszul sign of a
face from the chain map matches the sign of `cechVertexPerm` on face monomials
(`faceEquiv_cechVertexPerm`), and the face coordinates of the twist transport are the renamed face
coordinates (`vertexTwistPermIso_faceSections`).
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite SheafTools SheafTools.BinaryCells
open CechProduct ProjectiveLine Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

section FaceCoordinates

variable {V W : Type} [Fintype V] [Fintype W] (ψ : V ≃ W)

omit [Fintype V] [Fintype W] in
/-- The face monomials pulled back along a vertex bijection. -/
theorem embedFace_perm (q : W → Fin 3) (m : FaceMonoid q) :
    (fun v => embedFace q m (ψ v)) = embedFace (fun v => q (ψ v)) (faceMonoidRename ψ q m) := by
  funext v
  rfl

/-- The overlap vertices of a face monomial are the overlap directions of the face. -/
theorem overlapVertices_embedFace (q : V → Fin 3) (m : FaceMonoid q) :
    overlapVertices (embedFace q m) = faceOverlap q := by
  have hl (k : Fin 3) (a : FaceExponent k) :
      lineDegree (vertexFaceEquiv.symm ⟨k, a⟩) = if k = 2 then 1 else 0 := by
    fin_cases k <;> rfl
  ext v
  rw [mem_overlapVertices]
  simp only [faceOverlap, Finset.mem_filter, Finset.mem_univ, true_and]
  change lineDegree (vertexFaceEquiv.symm ⟨q v, m v⟩) = 1 ↔ q v = 2
  rw [hl]
  split_ifs with h <;> simp [h]

variable (R : Type) [CommRing R]

/-- **Face coordinates of the signed reordering.** The face component of `q` of the signed
reordering of a product Čech chain is the Koszul sign of `q` times the inverse renaming of the face
component of `q ∘ ψ`. -/
theorem faceEquiv_cechVertexPerm (c : C R V) (q : W → Fin 3) :
    faceEquiv R (cechVertexPerm R ψ c) q =
      facePermSign ψ q • (faceRingRename ψ q R).symm (faceEquiv R c (fun v => q (ψ v))) := by
  ext m
  rw [faceEquiv_coeff, cechVertexPerm_apply_apply, AddMonoidAlgebra.coeff_smul_apply,
    faceRingRename, AddMonoidAlgebra.domCongr_symm, AddMonoidAlgebra.coeff_domCongr,
    AddEquiv.symm_symm, faceEquiv_coeff, embedFace_perm, overlapVertices_embedFace, facePermSign,
    zsmul_eq_mul]
  congr 1
  exact (map_vertexPermSign (Int.castRingHom R) ψ _).symm

end FaceCoordinates

section Vertex

open AlgebraicGeometry

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
  [DecidableEq W] (ψ : V ≃ W)

omit [DecidableEq V] [DecidableEq W] in
/-- The homeomorphism underlying `vertexSheafPerm` pulls back the coordinate opens of `ψ v` to the
coordinate opens of `v`. -/
theorem vertexCoordinateOpen_map (v : V) (i : Fin 2) :
    (Opens.map (vertexSchemePermHomeo R ψ).hom).obj (vertexCoordinateOpen R W (ψ v) i) =
      vertexCoordinateOpen R V v i := by
  have h := vertexSchemePerm_preimage_coordinateOpen R ψ.symm (ψ v) i
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- The comparison chain map of the cubical cell complexes of `(P¹)^W` and `(P¹)^V`. -/
noncomputable abbrev vertexCellChainMap :=
  cellChainMap (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V) (vertexCoordinateOpen R W)
    (vertexCoordinateOpen_map R ψ)

variable (d : V → ℕ)

/-- The twist transport used for the state formula: `O(-d)` on `(P¹)^V` to `O(-d ∘ ψ⁻¹)`. -/
noncomputable abbrev vertexNegativeTwistPermIso :
    (vertexSheafPerm R ψ).functor.obj (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) ≅
      vertexTwistAbelianSheaf R W (fun w => -(d (ψ.symm w) : ℤ)) :=
  vertexTwistAbelianPermIso R ψ _ _ (fun v => by simp)

/-- **The transported cubical cochain**: the comparison chain map, the image of the cochain, and
the twist transport. -/
noncomputable def vertexCellCochainPerm (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) :
    sheafTerm (vertexCoordinateOpen R W) n ⟶ vertexTwistAbelianSheaf R W (fun w => -(d (ψ.symm w) : ℤ)) :=
  (show sheafTerm (vertexCoordinateOpen R W) n ⟶
      (vertexSheafPerm R ψ).functor.obj (sheafTerm (vertexCoordinateOpen R V) n) from
    (vertexCellChainMap R ψ).f n) ≫ (vertexSheafPerm R ψ).functor.map f ≫
      (vertexNegativeTwistPermIso R ψ d).hom

/-- The transported cochain of a cocycle is a cocycle. -/
theorem vertexCellCochainPerm_cycle (n : ℕ) (z : vertexTwistCellCycles R V d n) :
    vertexCellCochainPerm R ψ d n z.val ∈
      (cubicalTower (vertexCoordinateOpen R W)).cycles
        (vertexTwistAbelianSheaf R W (fun w => -(d (ψ.symm w) : ℤ))) n := by
  change (cubicalTower (vertexCoordinateOpen R W)).differential n ≫
    vertexCellCochainPerm R ψ d n z.val = 0
  have hz : (cubicalTower (vertexCoordinateOpen R V)).differential n ≫ z.val = 0 := z.property
  rw [ExtResolutionTools.complexTower_differential] at hz ⊢
  have hc := cellChainComponent_comm (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
    (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) n
  rw [vertexCellCochainPerm, ← Category.assoc]
  change ((sheafComplex (vertexCoordinateOpen R W)).d (n+1) n ≫
    cellChainComponent (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
      (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) n) ≫ _ = 0
  rw [← hc, Category.assoc]
  change cellChainComponent (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
      (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) (n+1) ≫
    ((vertexSheafPerm R ψ).functor.map ((sheafComplex (vertexCoordinateOpen R V)).d (n+1) n) ≫
      (vertexSheafPerm R ψ).functor.map z.val ≫ (vertexNegativeTwistPermIso R ψ d).hom) = 0
  rw [← Category.assoc ((vertexSheafPerm R ψ).functor.map _), ← Functor.map_comp, hz,
    Functor.map_zero, zero_comp, comp_zero]

/-- **Coefficients of the transported cochain.** The signed coefficient chain of the transported
cubical cochain is the signed reordering `cechVertexPerm` of the coefficient chain. -/
theorem vertexCellCochainPerm_coefficient (n : ℕ)
    (f : sheafTerm (vertexCoordinateOpen R V) n ⟶ vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) :
    (vertexTwistCellCoefficientEquiv R W (fun w => d (ψ.symm w)) n
        (vertexCellCochainPerm R ψ d n f)).val =
      cechVertexPerm R ψ (vertexTwistCellCoefficientEquiv R V d n f).val := by
  apply (faceEquiv R).injective
  funext q
  rw [faceEquiv_cechVertexPerm]
  change faceEquiv R (vertexTwistCubicalChainEquiv R W (fun w => d (ψ.symm w))
      (vertexTwistCellNativeEquiv R W _ n (vertexCellCochainPerm R ψ d n f)).val) q =
    facePermSign ψ q • (faceRingRename ψ q R).symm (faceEquiv R (vertexTwistCubicalChainEquiv R V d
      (vertexTwistCellNativeEquiv R V _ n f).val) (fun v => q (ψ v)))
  rw [vertexTwistCubicalChainEquiv_face, vertexTwistCubicalChainEquiv_face, faceDegree_perm]
  by_cases hq : (faceDegree q : ℤ) = n
  · let q' : FaceIndex (V := W) n := faceIndexOfDegree W n q hq
    have h1 := vertexTwistCellNativeEquiv_apply R W _ n (vertexCellCochainPerm R ψ d n f) q'
    have h2 := vertexTwistCellNativeEquiv_apply R V _ n f (faceIndexPerm ψ q')
    erw [h1, h2]
    have h3 : sectionsEquiv (vertexCoordinateOpen R W) _ n (vertexCellCochainPerm R ψ d n f) q' =
        (vertexNegativeTwistPermIso R ψ d).hom.hom.app _ (facePermSign ψ q •
          (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj.map
            (homOfLE (faceOpen_map (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
              (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) q).le).op
            (sectionsEquiv (vertexCoordinateOpen R V) _ n f (faceIndexPerm ψ q'))) := by
      have hc := sectionsEquiv_cellChainComponent_comp (vertexSchemePermHomeo R ψ) ψ
        (vertexCoordinateOpen R V) (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) n f q'
      rw [vertexCellCochainPerm, ← Category.assoc, sectionsEquiv_comp]
      exact congrArg _ hc
    rw [h3, map_zsmul, map_zsmul]
    have h4 := vertexTwistPermIso_faceSections R ψ (fun v => -(d v : ℤ))
      (fun w => -(d (ψ.symm w) : ℤ)) (fun v => by simp) q
      ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj.map
            (homOfLE (faceOpen_map (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
              (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) q).le).op
            (sectionsEquiv (vertexCoordinateOpen R V) _ n f (faceIndexPerm ψ q')))
    have h5 := ((faceRingRename ψ q R).symm_apply_apply _).symm.trans
      (congrArg (faceRingRename ψ q R).symm h4)
    erw [h5]
    have h6 : (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj.map
        (homOfLE (vertexSchemePerm_symm_preimage_faceOpen R ψ q).ge).op
        ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj.map
            (homOfLE (faceOpen_map (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
              (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) q).le).op
            (sectionsEquiv (vertexCoordinateOpen R V) _ n f (faceIndexPerm ψ q'))) =
          sectionsEquiv (vertexCoordinateOpen R V) _ n f (faceIndexPerm ψ q') := by
      refine (sheaf_map_map (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) _ _ (𝟙 _) _).trans ?_
      exact (ConcreteCategory.congr_hom
        ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).obj.map_id _) _).trans rfl
    erw [h6]
    rw [map_smul, smul_comm]
  · have hq' : (faceDegree (fun v => q (ψ v)) : ℤ) ≠ n := by rw [faceDegree_perm]; exact hq
    rw [vertexTwistCellNativeEquiv_apply_ne R W _ n _ q hq,
      vertexTwistCellNativeEquiv_apply_ne R V _ n f _ hq', map_zero, map_zero, smul_zero,
      smul_zero, map_zero, smul_zero]

end Vertex

end BPFixedPoints.Multigraph
