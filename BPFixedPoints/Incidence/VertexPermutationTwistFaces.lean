import BPFixedPoints.Incidence.VertexPermutationTwistSheaf
import BPFixedPoints.Incidence.VertexProjectiveFaceSections
import BPFixedPoints.Incidence.SchemeModuleGeometricCoefficients

/-!
# Mixed face coordinates of the twist transport

For `ψ : V ≃ W` and a face `q : W → Fin 3` of the binary cubical cover of `(P¹)^W`, the coordinate
map `g = a_{ψ⁻¹}` pulls back the face open of `q` to the face open of `q ∘ ψ`
(`vertexSchemePerm_symm_preimage_faceOpen`). The face rings correspond by renaming the vertices
(`faceRingRename : FaceRing R q ≃ₐ[R] FaceRing R (q ∘ ψ)`, which sends the variable of `ψ v` to the
variable of `v`), and the face maps commute with `g` after this renaming (`vertexFaceι_perm`).

Proved here:
* a general formula for affine coordinates of pulled back functions along a morphism of schemes
  (`affineOpenSectionsIsoAt_pullback`);
* face coordinates of pulled back functions are the renamed face coordinates
  (`vertexFaceSectionsEquiv_perm`);
* **face coordinates of the twist transport**: for `b ∘ ψ = a`, the renamed mixed face
  coordinates of the transport in `O(b)` of a section of `O(a)` are the mixed face coordinates of
  the section on the face of `q ∘ ψ` (`vertexTwistPermIso_faceSections`).

Not proved here: the comparison of the cubical cell sheaf complexes of `V` and `W` under the
coordinate map (with the Koszul signs of the cubical boundary), and the resulting naturality of
the cell route to Ext-defined cohomology.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open ProjectiveLine CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000

section Rename

variable {V W : Type} (ψ : V ≃ W) (q : W → Fin 3)

/-- Renaming the exponent vectors of a face along a vertex bijection. -/
def faceMonoidRename : FaceMonoid q ≃+ FaceMonoid (fun v => q (ψ v)) where
  toEquiv := (Equiv.piCongrLeft (fun w => FaceExponent (q w)) ψ).symm
  map_add' m n := by
    funext v
    simp

@[simp] theorem faceMonoidRename_apply (m : FaceMonoid q) (v : V) :
    faceMonoidRename ψ q m v = m (ψ v) := by
  simp [faceMonoidRename]

variable (R : Type) [CommRing R]

/-- **Renaming of face coordinate rings** along a vertex bijection: the face ring of a face `q`
of `W` is the face ring of the face `q ∘ ψ` of `V`, with the variable of `ψ v` going to the variable
of `v`. -/
noncomputable def faceRingRename : FaceRing R q ≃ₐ[R] FaceRing R (fun v => q (ψ v)) :=
  AddMonoidAlgebra.domCongr R R (faceMonoidRename ψ q)

theorem faceRingRename_single (m : FaceMonoid q) (r : R) :
    faceRingRename ψ q R (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (faceMonoidRename ψ q m) r :=
  AddMonoidAlgebra.domCongr_single _ _ _

/-- The renaming sends the variable of `ψ v` to the variable of `v`. -/
theorem faceRingRename_faceVariable [DecidableEq V] [DecidableEq W] (v : V) :
    faceRingRename ψ q R (faceVariable R q (ψ v)) = faceVariable R (fun v => q (ψ v)) v := by
  rw [faceVariable, faceRingRename_single, faceVariable]
  congr 1
  funext v'
  rw [faceMonoidRename_apply]
  by_cases h : v' = v
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (fun e => h (ψ.injective e)), Pi.single_eq_of_ne h]

end Rename

/-- **Affine coordinates along a morphism.** If `g : X ⟶ Y` carries the affine open image of
`fX : Spec A ⟶ X` into that of `fY : Spec B ⟶ Y` compatibly with a ring map `i : B ⟶ A`, then the
affine coordinates of the pullback of a section are `i` of its affine coordinates. -/
theorem affineOpenSectionsIsoAt_pullback {X Y : Scheme.{0}} (g : X ⟶ Y) {A B : CommRingCat.{0}}
    (i : B ⟶ A) (fX : Spec A ⟶ X) (fY : Spec B ⟶ Y) [IsOpenImmersion fX] [IsOpenImmersion fY]
    (h : Spec.map i ≫ fY = fX ≫ g) (UX : X.Opens) (UY : Y.Opens) (hX : fX.opensRange = UX)
    (hY : fY.opensRange = UY) (hU : UX ≤ g ⁻¹ᵁ UY) (y : Γ(Y, UY)) :
    (affineOpenSectionsIsoAt A fX UX hX).hom (X.presheaf.map (homOfLE hU).op (g.app UY y)) =
      i ((affineOpenSectionsIsoAt B fY UY hY).hom y) := by
  rw [affineOpenSectionsIsoAt_hom, affineOpenSectionsIsoAt_hom]
  have eX : ⊤ ≤ fX ⁻¹ᵁ UX := by rw [← hX, fX.preimage_opensRange]
  have eY : ⊤ ≤ fY ⁻¹ᵁ UY := by rw [← hY, fY.preimage_opensRange]
  have e2 : (⊤ : (Spec A).Opens) ≤ Spec.map i ⁻¹ᵁ ⊤ := le_rfl
  have e1 := Scheme.Hom.appLE_comp_appLE fX g UY UX ⊤ hU eX
  have e3 := Scheme.Hom.appLE_comp_appLE (Spec.map i) fY UY ⊤ ⊤ eY e2
  have e4 : (Spec.map i).appLE ⊤ ⊤ e2 = (Spec.map i).appTop := Scheme.Hom.appLE_eq_app _
  have key : g.appLE UY UX hU ≫ fX.appLE UX ⊤ eX ≫ (Scheme.ΓSpecIso A).hom =
      fY.appLE UY ⊤ eY ≫ (Scheme.ΓSpecIso B).hom ≫ i := by
    rw [← Category.assoc, e1, appLE_congr_hom h.symm UY ⊤ _ (e2.trans ((Spec.map i).preimage_mono eY)), ← e3, e4,
      Category.assoc, Scheme.ΓSpecIso_naturality]
  exact congrArg (fun k => k.hom y) key

section Faces

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] (ψ : V ≃ W)

/-- The face map of `q ∘ ψ` followed by the coordinate map of `ψ⁻¹` is the face map of `q`
after renaming the face coordinates. -/
theorem vertexFaceι_perm (q : W → Fin 3) :
    Spec.map (CommRingCat.ofHom (faceRingRename ψ q R).toRingHom) ≫ vertexFaceι R W q =
      vertexFaceι R V (fun v => q (ψ v)) ≫ vertexSchemePerm R ψ.symm := by
  let k : vertexFaceOverBase R V (fun v => q (ψ v)) ⟶ vertexFaceOverBase R W q :=
    Over.homMk (Spec.map (CommRingCat.ofHom (faceRingRename ψ q R).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (faceRingRename ψ q R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R q))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FaceRing R (fun v => q (ψ v)))))
      rw [← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (faceRingRename ψ q R).toAlgHom.comp_algebraMap))
  have he : k ≫ vertexFaceOver R W q =
      vertexFaceOver R V (fun v => q (ψ v)) ≫ vertexOverBasePerm R ψ.symm := by
    apply vertexOverBase_hom_ext R
    intro w
    obtain ⟨v, rfl⟩ := ψ.surjective w
    apply Over.OverMorphism.ext
    change (Spec.map (CommRingCat.ofHom (faceRingRename ψ q R).toRingHom) ≫ vertexFaceι R W q) ≫
        (vertexProjectionOver R W (ψ v)).left =
      (vertexFaceι R V (fun v => q (ψ v)) ≫ vertexSchemePerm R ψ.symm) ≫
        (vertexProjectionOver R W (ψ v)).left
    rw [Category.assoc, vertexFaceι_projection, Category.assoc,
      vertexSchemePerm_symm_projection_apply, vertexFaceι_projection]
    dsimp only [vertexFaceProjection]
    rw [evaluationChart_natural]
    have hc : (faceRingRename ψ q R).toRingHom.comp (algebraMap R (FaceRing R q)) =
        algebraMap R (FaceRing R (fun v => q (ψ v))) := (faceRingRename ψ q R).toAlgHom.comp_algebraMap
    rw [hc]
    change evaluationChart (algebraMap R (FaceRing R (fun v => q (ψ v))))
      (faceRingRename ψ q R (faceVariable R q (ψ v))) (vertexFacePivot (q (ψ v))) = _
    rw [faceRingRename_faceVariable]
  exact congrArg Over.Hom.left he

omit [DecidableEq V] [DecidableEq W] in
/-- The coordinate map of `ψ⁻¹` pulls back the face open of `q` to the face open of `q ∘ ψ`. -/
theorem vertexSchemePerm_symm_preimage_faceOpen (q : W → Fin 3) :
    vertexSchemePerm R ψ.symm ⁻¹ᵁ binaryCoverFaceOpen (vertexCoordinateOpen R W) q =
      binaryCoverFaceOpen (vertexCoordinateOpen R V) (fun v => q (ψ v)) :=
  vertexSchemePerm_preimage_binaryCoverFaceOpen R ψ.symm q

/-- **Face coordinates of pulled back functions.** The face coordinates of the pullback of a
function on the face of `q` along the coordinate map of `ψ⁻¹` are the renamed face coordinates of
the function. -/
theorem vertexFaceSectionsEquiv_perm (q : W → Fin 3)
    (y : Γ(vertexScheme R W, binaryCoverFaceOpen (vertexCoordinateOpen R W) q)) :
    vertexFaceSectionsEquiv R V (fun v => q (ψ v))
        ((vertexScheme R V).presheaf.map
          (homOfLE (vertexSchemePerm_symm_preimage_faceOpen R ψ q).ge).op
          ((vertexSchemePerm R ψ.symm).app _ y)) =
      faceRingRename ψ q R (vertexFaceSectionsEquiv R W q y) :=
  affineOpenSectionsIsoAt_pullback (vertexSchemePerm R ψ.symm)
    (CommRingCat.ofHom (faceRingRename ψ q R).toRingHom) (vertexFaceι R V (fun v => q (ψ v)))
    (vertexFaceι R W q) (vertexFaceι_perm R ψ q) _ _ (vertexFaceι_opensRange R V _)
    (vertexFaceι_opensRange R W q) _ y

variable (a : V → ℤ) (b : W → ℤ) (hb : ∀ v, b (ψ v) = a v)

/-- **Face coordinates of the twist transport.** For a section of `O(a)` over the preimage of the
face open of `q`, the renamed face coordinates of its transport in `O(b)` are the face coordinates
of its restriction to the face open of `q ∘ ψ`. -/
theorem vertexTwistPermIso_faceSections (q : W → Fin 3)
    (x : Γ(vertexTwistSheaf R V a,
      vertexSchemePerm R ψ.symm ⁻¹ᵁ binaryCoverFaceOpen (vertexCoordinateOpen R W) q)) :
    faceRingRename ψ q R (vertexTwistSheafFaceSectionsEquiv R W b q
        ((vertexTwistPermIso R ψ a b hb).hom.app _ x)) =
      vertexTwistSheafFaceSectionsEquiv R V a (fun v => q (ψ v))
        ((vertexTwistSheaf R V a).presheaf.map
          (homOfLE (vertexSchemePerm_symm_preimage_faceOpen R ψ q).ge).op x) := by
  rw [vertexTwistSheafFaceSectionsEquiv_apply, vertexTwistSheafFaceSectionsEquiv_apply,
    vertexTwistPermIso_chartCoefficient, ← vertexFaceSectionsEquiv_perm, app_inv_app]
  congr 1
  exact (vertexTwistSheafChartCoefficient_restrict R V a _
    (vertexSchemePerm_symm_preimage_faceOpen R ψ q).ge _ x).symm

end Faces

end BPFixedPoints.Multigraph
