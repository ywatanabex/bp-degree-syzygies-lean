import BPFixedPoints.Incidence.VertexPermutationCellConstant
import BPFixedPoints.Incidence.VertexProjectiveTwistZeroRouteAgreement
import BPFixedPoints.Incidence.CechProductPermutation

/-!
# Cubical cell complexes along a homeomorphism and a vertex bijection

Let `h : T ≅ T'` be a homeomorphism, `ψ : V ≃ W` a bijection, and `U`, `U'` binary covers of `T`
and `T'` indexed by `V` and `W` with `h⁻¹ (U' (ψ v) i) = U v i`. Then `h` pulls back the face open
of a face `q` of `W` to the face open of `q ∘ ψ` (`faceOpen_map`).

The comparison of the cubical cell sheaf complexes, `cellChainMap h ψ U U' hU`, goes from the cell
complex of `U'` to the image of the cell complex of `U` under the pushforward
`(topSheafEquivOfIso h).functor`. It is defined through the universal property of the cell terms
(`sectionsEquiv`): the universal section of a face `q` of `W` goes to the Koszul sign
`facePermSign ψ q = vertexPermSign ψ (overlap of q ∘ ψ)` times the universal section of `q ∘ ψ`.

Proved here:
* the Koszul sign identity for cubical boundaries (`facePermSign_boundary`), from the shuffle
  identity `vertexPermSign_union`;
* `cellChainMap` is a chain map (`cellChainComponent_comm`);
* it is compatible with the augmentations through the comparison of the free sheaves on the whole
  spaces (`cellChainComponent_augmentation`);
* the face sections of `cellChainMap` followed by a transported cochain are the signed restricted
  face sections of the cochain (`sectionsEquiv_cellChainComponent_comp`).
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite SheafTools SheafTools.BinaryCells
open CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

section Faces

variable {V W : Type} [Fintype V] [Fintype W] (ψ : V ≃ W)

/-- The overlap directions of a face, as a vertex set. -/
def faceOverlap (q : V → Fin 3) : Finset V := Finset.univ.filter fun v => q v = 2

/-- The overlap degree of a face is the number of its overlap directions. -/
theorem faceDegree_eq_card_faceOverlap (q : V → Fin 3) : faceDegree q = (faceOverlap q).card := by
  rw [faceDegree, faceOverlap, Finset.card_filter]

/-- Faces are transported along a vertex bijection without changing their overlap degree. -/
theorem faceDegree_perm (q : W → Fin 3) : faceDegree (fun v => q (ψ v)) = faceDegree q :=
  Fintype.sum_equiv ψ _ _ (fun _ => rfl)

/-- The Koszul sign of a face of `W` pulled back to `V`: the reordering sign of its overlap
directions. -/
noncomputable def facePermSign (q : W → Fin 3) : ℤ :=
  vertexPermSign ℤ ψ (faceOverlap fun v => q (ψ v))

variable [DecidableEq V] [DecidableEq W]

/-- The pulled back face of a face of `W`, with the same cell degree. -/
def faceIndexPerm {n : ℕ} (q : FaceIndex (V := W) n) : FaceIndex (V := V) n :=
  ⟨fun v => q.val (ψ v), by
    have hq := q.property
    dsimp only [CechCubicalCell.cellDegree] at hq ⊢
    rw [faceDegree_perm]
    exact hq⟩

omit [DecidableEq V] [DecidableEq W] in
/-- The underlying face of a pulled back face. -/
@[simp] theorem faceIndexPerm_val {n : ℕ} (q : FaceIndex (V := W) n) :
    (faceIndexPerm ψ q).val = fun v => q.val (ψ v) := rfl

omit [DecidableEq V] in
/-- The boundary prefix of a face counts its earlier overlap directions. -/
theorem faceBoundaryPrefix_eq_vertexCrossings (q : V → Fin 3) (v : V) :
    faceBoundaryPrefix q v = vertexCrossings (faceOverlap q) {v} := by
  unfold faceBoundaryPrefix vertexCrossings faceOverlap
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_singleton]
  split_ifs <;> rfl

omit [DecidableEq V] [DecidableEq W] in
/-- The overlap directions of a pulled back face are the preimages of the overlap directions. -/
theorem faceOverlap_perm (q : W → Fin 3) :
    faceOverlap q = (faceOverlap fun v => q (ψ v)).map ψ.toEmbedding := by
  ext w
  simp only [faceOverlap, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
  rw [Equiv.apply_symm_apply]

/-- Replacing an overlap direction by an endpoint removes it from the overlap directions. -/
theorem faceOverlap_update (q : V → Fin 3) (v : V) (k : Fin 2) :
    faceOverlap (Function.update q v k.castSucc) = (faceOverlap q).erase v := by
  ext w
  by_cases hw : w = v
  · subst hw
    simp [faceOverlap, endpoint_ne_overlap]
  · simp [faceOverlap, hw]

/-- **Koszul signs of cubical boundaries.** Moving the overlap direction `v` of a face past the
earlier overlap directions in the two vertex orders changes the reordering sign by the two boundary
prefix signs. -/
theorem facePermSign_boundary (q : W → Fin 3) (v : V) (hv : q (ψ v) = 2) (k : Fin 2) :
    (facePermSign ψ q : ℤ) * (-1) ^ faceBoundaryPrefix (fun u => q (ψ u)) v =
      (-1) ^ faceBoundaryPrefix q (ψ v) *
        facePermSign ψ (Function.update q (ψ v) k.castSucc) := by
  set p : V → Fin 3 := fun u => q (ψ u) with hp
  have hpu : (fun u => Function.update q (ψ v) k.castSucc (ψ u)) = Function.update p v k.castSucc := by
    have := Function.update_comp_eq_of_injective q ψ.injective v k.castSucc
    exact this
  have hmem : v ∈ faceOverlap p := by simp [faceOverlap, p, hv]
  have hdisj : Disjoint {v} ((faceOverlap p).erase v) := by simp
  have hs := vertexPermSign_union ℤ ψ hdisj
  rw [vertexPermSign_singleton, one_mul, Finset.map_singleton] at hs
  have hu : ({v} : Finset V) ∪ (faceOverlap p).erase v = faceOverlap p := by
    rw [Finset.union_comm, Finset.erase_union_eq v _ hmem]
  rw [hu] at hs
  have hpre : ∀ {X : Type} [Fintype X] [DecidableEq X] (r : X → Fin 3) (x : X) (y : Fin 3),
      faceBoundaryPrefix (Function.update r x y) x = faceBoundaryPrefix r x := by
    intro X _ _ r x y
    unfold faceBoundaryPrefix
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : w = x
    · subst hw
      simp
    · rw [Function.update_of_ne hw]
  change vertexPermSign ℤ ψ (faceOverlap p) * (-1) ^ faceBoundaryPrefix p v =
    (-1) ^ faceBoundaryPrefix q (ψ v) *
      vertexPermSign ℤ ψ (faceOverlap fun u => Function.update q (ψ v) k.castSucc (ψ u))
  rw [hpu, faceOverlap_update, ← hpre p v k.castSucc, faceBoundaryPrefix_eq_vertexCrossings,
    faceOverlap_update, ← hpre q (ψ v) k.castSucc, faceBoundaryPrefix_eq_vertexCrossings,
    faceOverlap_perm ψ (Function.update q (ψ v) k.castSucc), hpu, faceOverlap_update]
  exact hs

end Faces

section Opens

variable {T T' : TopCat.{0}} (h : T ≅ T') {V W : Type} [Fintype V] [Fintype W] (ψ : V ≃ W)
  (U : V → Fin 2 → Opens T) (U' : W → Fin 2 → Opens T')
  (hU : ∀ v i, (Opens.map h.hom).obj (U' (ψ v) i) = U v i)

include hU in
/-- The homeomorphism pulls back the face open of a face of `W` to the face open of the pulled
back face. -/
theorem faceOpen_map (q : W → Fin 3) :
    (Opens.map h.hom).obj (binaryCoverFaceOpen U' q) = binaryCoverFaceOpen U (fun v => q (ψ v)) := by
  have hf : ∀ v, (Opens.map h.hom).obj (binaryCoverFaceFactor (U' (ψ v)) (q (ψ v))) =
      binaryCoverFaceFactor (U v) (q (ψ v)) := by
    intro v
    unfold binaryCoverFaceFactor
    split_ifs
    · exact hU v 0
    · exact hU v 1
    · rw [← hU v 0, ← hU v 1]
      rfl
  ext x
  simp only [binaryCoverFaceOpen, Opens.map_coe, Opens.coe_iInf, Set.mem_preimage, Set.mem_iInter,
    SetLike.mem_coe]
  constructor
  · intro hx v
    have := congrArg (fun O : Opens T => x ∈ O) (hf v)
    simp only [eq_iff_iff] at this
    exact this.mp (hx (ψ v))
  · intro hx w
    have := congrArg (fun O : Opens T => x ∈ O) (hf (ψ.symm w))
    simp only [eq_iff_iff, Equiv.apply_symm_apply] at this
    have hxw := hx (ψ.symm w)
    rw [Equiv.apply_symm_apply] at hxw
    exact this.mpr hxw

end Opens

section Sections

/-- Two successive restrictions of a section are one restriction. -/
theorem sheaf_map_map {S : Type} [TopologicalSpace S]
    (G : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) {X Y Z : (Opens S)ᵒᵖ}
    (m₂ : X ⟶ Y) (m₁ : Y ⟶ Z) (m₃ : X ⟶ Z) (x : G.obj.obj X) :
    G.obj.map m₁ (G.obj.map m₂ x) = G.obj.map m₃ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (m₂ ≫ m₁) m₃]

variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
  (U : V → Fin 2 → Opens T)

/-- The universal section of a cell sheaf term on the face open of a face. -/
noncomputable def cellGeneratorSection (n : ℕ) (q : FaceIndex (V := V) n) :
    (sheafTerm U n).obj.obj (op (binaryCoverFaceOpen U q.val)) :=
  sectionsEquiv U (sheafTerm U n) n (𝟙 _) q

/-- Face sections of a composite are the images of the face sections. -/
theorem sectionsEquiv_comp (n : ℕ) {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (f : sheafTerm U n ⟶ F) (g : F ⟶ G) (q : FaceIndex (V := V) n) :
    sectionsEquiv U G n (f ≫ g) q = g.hom.app _ (sectionsEquiv U F n f q) := by
  rw [sectionsEquiv_apply, sectionsEquiv_apply, ← Category.assoc]
  rfl

/-- Face sections of a cochain are its values on the universal sections. -/
theorem sectionsEquiv_eq_app (n : ℕ) {F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (f : sheafTerm U n ⟶ F) (q : FaceIndex (V := V) n) :
    sectionsEquiv U F n f q = f.hom.app _ (cellGeneratorSection U n q) := by
  have h := sectionsEquiv_comp U n (𝟙 _) f q
  rw [Category.id_comp] at h
  exact h

end Sections

section Chain

variable {T T' : TopCat.{0}} (h : T ≅ T') {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
  [DecidableEq W] (ψ : V ≃ W) (U : V → Fin 2 → Opens T) (U' : W → Fin 2 → Opens T')
  (hU : ∀ v i, (Opens.map h.hom).obj (U' (ψ v) i) = U v i)

/-- The section defining the comparison of cell complexes on the face open of a face of `W`: the
Koszul sign of the face times the universal section of the pulled back face. -/
noncomputable def cellChainSection (n : ℕ) (q : FaceIndex (V := W) n) :
    ((topSheafEquivOfIso h).functor.obj (sheafTerm U n)).obj.obj (op (binaryCoverFaceOpen U' q.val)) :=
  facePermSign ψ q.val • (sheafTerm U n).obj.map (homOfLE (faceOpen_map h ψ U U' hU q.val).le).op
    (cellGeneratorSection U n (faceIndexPerm ψ q))

/-- **The comparison of cubical cell complexes** in each degree: the cell sheaf term of `W` maps to
the transported cell sheaf term of `V` by sending the universal section of a face to the Koszul
sign times the universal section of the pulled back face. -/
noncomputable def cellChainComponent (n : ℕ) :
    sheafTerm U' n ⟶ (topSheafEquivOfIso h).functor.obj (sheafTerm U n) :=
  (sectionsEquiv U' ((topSheafEquivOfIso h).functor.obj (sheafTerm U n)) n).symm
    (cellChainSection h ψ U U' hU n)

/-- The face sections of the comparison are the specified signed universal sections. -/
theorem sectionsEquiv_cellChainComponent (n : ℕ) :
    sectionsEquiv U' ((topSheafEquivOfIso h).functor.obj (sheafTerm U n)) n
      (cellChainComponent h ψ U U' hU n) = cellChainSection h ψ U U' hU n :=
  AddEquiv.apply_symm_apply _ _

/-- Face sections of the comparison followed by a transported cochain. -/
theorem sectionsEquiv_cellChainComponent_comp (n : ℕ)
    {G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (f : sheafTerm U n ⟶ G)
    (q : FaceIndex (V := W) n) :
    sectionsEquiv U' ((topSheafEquivOfIso h).functor.obj G) n
        (cellChainComponent h ψ U U' hU n ≫ (topSheafEquivOfIso h).functor.map f) q =
      facePermSign ψ q.val • G.obj.map (homOfLE (faceOpen_map h ψ U U' hU q.val).le).op
        (sectionsEquiv U G n f (faceIndexPerm ψ q)) := by
  rw [sectionsEquiv_comp, sectionsEquiv_cellChainComponent]
  change f.hom.app _ (facePermSign ψ q.val • (sheafTerm U n).obj.map _ _) = _
  rw [map_zsmul, sectionsEquiv_eq_app]
  congr 1
  exact ConcreteCategory.congr_hom (f.hom.naturality _) _

/-- Restrictions of universal sections of equal faces agree. -/
theorem cellGeneratorSection_map_eq (n : ℕ) {q₁ q₂ : FaceIndex (V := V) n} (hq : q₁ = q₂)
    {X : (Opens T)ᵒᵖ} (m₁ : op (binaryCoverFaceOpen U q₁.val) ⟶ X)
    (m₂ : op (binaryCoverFaceOpen U q₂.val) ⟶ X) :
    (sheafTerm U n).obj.map m₁ (cellGeneratorSection U n q₁) =
      (sheafTerm U n).obj.map m₂ (cellGeneratorSection U n q₂) := by
  subst hq
  rw [Subsingleton.elim m₁ m₂]

/-- Restrictions of universal sections of equal faces agree, also after a second restriction. -/
theorem cellGeneratorSection_map_map_eq (n : ℕ) {q₁ q₂ : FaceIndex (V := V) n} (hq : q₁ = q₂)
    {X Y : (Opens T)ᵒᵖ} (m₁ : op (binaryCoverFaceOpen U q₁.val) ⟶ Y)
    (m₂ : op (binaryCoverFaceOpen U q₂.val) ⟶ X) (m₃ : X ⟶ Y) :
    (sheafTerm U n).obj.map m₁ (cellGeneratorSection U n q₁) =
      (sheafTerm U n).obj.map m₃ ((sheafTerm U n).obj.map m₂ (cellGeneratorSection U n q₂)) := by
  subst hq
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim m₁ (m₂ ≫ m₃)]

/-- Pulled back endpoints are endpoints of the pulled back face. -/
theorem faceIndexPerm_endpoint {n : ℕ} (p : FaceIndex (V := W) (n+1)) (v : V)
    (hv : p.val (ψ v) = 2) (k : Fin 2) :
    faceIndexPerm ψ (endpoint p (ψ v) hv k) = endpoint (faceIndexPerm ψ p) v hv k := by
  apply Subtype.ext
  exact Function.update_comp_eq_of_injective p.val ψ.injective v k.castSucc

/-- **The comparison of cell complexes is a chain map**, with the Koszul signs of the faces. -/
theorem cellChainComponent_comm (n : ℕ) :
    cellChainComponent h ψ U U' hU (n+1) ≫
        (topSheafEquivOfIso h).functor.map ((sheafComplex U).d (n+1) n) =
      (sheafComplex U').d (n+1) n ≫ cellChainComponent h ψ U U' hU n := by
  apply (sectionsEquiv U' ((topSheafEquivOfIso h).functor.obj (sheafTerm U n)) (n+1)).injective
  funext p
  rw [sectionsEquiv_cellChainComponent_comp, sectionsEquiv_boundary, sectionsEquiv_cellChainComponent]
  have hb := sectionsEquiv_boundary U (sheafTerm U n) n (𝟙 _) (faceIndexPerm ψ p)
  rw [Category.comp_id] at hb
  rw [hb, map_sum, Finset.smul_sum, ← Fintype.sum_equiv ψ _ _ (fun _ => rfl)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : p.val (ψ v) = 2
  · have hv' : (faceIndexPerm ψ p).val v = 2 := hv
    rw [dite_eq_left hv', dite_eq_left hv]
    set X := op ((Opens.map h.hom).obj (binaryCoverFaceOpen U' p.val))
    have hA : ∀ k : Fin 2, ∃ A : (sheafTerm U n).obj.obj X,
        (sheafTerm U n).obj.map (homOfLE (faceOpen_map h ψ U U' hU p.val).le).op
          ((sheafTerm U n).obj.map (homOfLE (endpointOpenLE U (faceIndexPerm ψ p) v hv' k)).op
            (sectionsEquiv U (sheafTerm U n) n (𝟙 _) (endpoint (faceIndexPerm ψ p) v hv' k))) = A ∧
        ((topSheafEquivOfIso h).functor.obj (sheafTerm U n)).obj.map
          (homOfLE (endpointOpenLE U' p (ψ v) hv k)).op
          (cellChainSection h ψ U U' hU n (endpoint p (ψ v) hv k)) =
            facePermSign ψ (Function.update p.val (ψ v) k.castSucc) • A := by
      intro k
      refine ⟨_, rfl, ?_⟩
      change (sheafTerm U n).obj.map _ (facePermSign ψ (Function.update p.val (ψ v) k.castSucc) •
        (sheafTerm U n).obj.map _ (cellGeneratorSection U n (faceIndexPerm ψ (endpoint p (ψ v) hv k)))) = _
      rw [map_zsmul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact cellGeneratorSection_map_map_eq U n (faceIndexPerm_endpoint ψ p v hv k) _ _ _
    obtain ⟨A0, hL0, hR0⟩ := hA 0
    obtain ⟨A1, hL1, hR1⟩ := hA 1
    have hs : ∀ k : Fin 2, facePermSign ψ p.val *
        (-1) ^ faceBoundaryPrefix (faceIndexPerm ψ p).val v =
          (-1) ^ faceBoundaryPrefix p.val (ψ v) *
            facePermSign ψ (Function.update p.val (ψ v) k.castSucc) :=
      fun k => facePermSign_boundary ψ p.val v hv k
    rw [hR0, hR1, map_zsmul, map_sub, hL0, hL1, smul_smul, smul_sub, smul_sub, smul_smul, smul_smul,
      ← hs 0, ← hs 1]
  · have hv' : ¬ (faceIndexPerm ψ p).val v = 2 := hv
    rw [dite_eq_right hv, dite_eq_right hv', map_zero, smul_zero]

/-- **The comparison chain map** from the cubical cell complex of `U'` to the transported cubical
cell complex of `U`. -/
noncomputable def cellChainMap :
    sheafComplex U' ⟶ ((topSheafEquivOfIso h).functor.mapHomologicalComplex _).obj (sheafComplex U) where
  f n := cellChainComponent h ψ U U' hU n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    exact cellChainComponent_comm h ψ U U' hU j

/-- The components of the comparison chain map. -/
theorem cellChainMap_f (n : ℕ) : (cellChainMap h ψ U U' hU).f n = cellChainComponent h ψ U U' hU n :=
  rfl

omit [DecidableEq V] [DecidableEq W] in
/-- A face of overlap degree zero has Koszul sign one. -/
theorem facePermSign_zero (q : FaceIndex (V := W) 0) : facePermSign ψ q.val = 1 := by
  have hq : faceDegree (fun v => q.val (ψ v)) = 0 := by
    have h := q.property
    dsimp only [CechCubicalCell.cellDegree] at h
    rw [faceDegree_perm]
    omega
  rw [faceDegree_eq_card_faceOverlap, Finset.card_eq_zero] at hq
  rw [facePermSign, hq, vertexPermSign_empty]

/-- Face sections of the augmentation are restrictions of the universal global section. -/
theorem sectionsEquiv_augmentation {S : Type} [TopologicalSpace S] {X : Type} [Fintype X]
    [DecidableEq X] (Z : X → Fin 2 → Opens S) (q : FaceIndex (V := X) 0) :
    sectionsEquiv Z _ 0 (augmentation Z) q =
      ((presheafToSheaf (Opens.grothendieckTopology S) AddCommGrpCat).obj
        (yoneda.obj (⊤ : Opens S) ⋙ AddCommGrpCat.free)).obj.map
          (homOfLE (show binaryCoverFaceOpen Z q.val ≤ ⊤ from le_top)).op
        (freeSheafSectionsEquiv _ (⊤ : Opens S) (𝟙 _)) := by
  rw [sectionsEquiv_apply, generator_augmentation, ← freeSheafSectionsEquiv_naturality]
  exact congrArg _ (Category.comp_id _).symm

/-- The comparison chain map is compatible with the augmentations, through the comparison of the
free sheaves on the whole spaces. -/
theorem cellChainComponent_augmentation :
    cellChainComponent h ψ U U' hU 0 ≫ (topSheafEquivOfIso h).functor.map (augmentation U) =
      augmentation U' ≫ topSheafEquivOfIsoFreeTop h := by
  apply (sectionsEquiv U' ((topSheafEquivOfIso h).functor.obj ((presheafToSheaf
    (Opens.grothendieckTopology T) AddCommGrpCat).obj (yoneda.obj (⊤ : Opens T) ⋙
      AddCommGrpCat.free))) 0).injective
  funext q
  rw [sectionsEquiv_cellChainComponent_comp, sectionsEquiv_comp, sectionsEquiv_augmentation,
    sectionsEquiv_augmentation, facePermSign_zero, one_smul]
  have hu : freeSheafSectionsEquiv _ ⊤ (topSheafEquivOfIsoFreeTop h) =
      freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _) := AddEquiv.apply_symm_apply _ _
  have hn := ConcreteCategory.congr_hom ((topSheafEquivOfIsoFreeTop h).hom.naturality
    (homOfLE (show binaryCoverFaceOpen U' q.val ≤ ⊤ from le_top)).op)
    (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _))
  have ha : (topSheafEquivOfIsoFreeTop h).hom.app (op ⊤)
      (freeSheafSectionsEquiv _ (⊤ : Opens T') (𝟙 _)) =
        freeSheafSectionsEquiv _ (⊤ : Opens T) (𝟙 _) := by
    rw [← freeSheafSectionsEquiv_comp, Category.id_comp]
    exact hu
  refine Eq.trans ?_ (Eq.trans (congrArg (fun x => (((topSheafEquivOfIso h).functor.obj
    ((presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free))).obj.map
        (homOfLE (show binaryCoverFaceOpen U' q.val ≤ ⊤ from le_top)).op) x) ha.symm) hn.symm)
  exact sheaf_map_map _ _ _ _ _

end Chain

end BPFixedPoints.Multigraph
