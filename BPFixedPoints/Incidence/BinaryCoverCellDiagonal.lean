import BPFixedPoints.Incidence.CechCubicalCellDiagonalComplex
import BPFixedPoints.Incidence.BinaryCoverCellEndpoint

/-! # The specified cubical diagonal on the actual open cell presheaves

The target has the original available face pairs in their original total
degree. Its differential is the original signed tensor cell differential.
Restrictions retain the original cell pairs with their original coefficients.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type*) [CommRing R]

@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module

/-- Original pairs available on the actual open, in their original summed overlap degree. -/
noncomputable def pairedChains (W : Opens T) (n : ℕ) : Submodule R (CellPairs R V) :=
  supported R R {z | W ≤ binaryCoverFaceOpen U z.1 ∧ W ≤ binaryCoverFaceOpen U z.2 ∧
    faceDegree z.1+faceDegree z.2 = n}

@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

private theorem leftEndpoint_mem {W : Opens T} {n : ℕ} {p q : V → Fin 3}
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q = n+1) (v : V) (hv : p v = 2) (k : Fin 2) (r : R) :
    single (Function.update p v k.castSucc,q) r ∈ pairedChains U R W n := by
  apply single_mem_supported R r
  refine ⟨hp.trans (faceOpen_refinement_le U (endpoint_refines (faceRefines_refl p) v hv k.castSucc)),hq,?_⟩
  have h := faceDegree_endpoint p v hv k
  change faceDegree (Function.update p v k.castSucc)+faceDegree q = n
  omega

private theorem rightEndpoint_mem {W : Opens T} {n : ℕ} {p q : V → Fin 3}
    (hp : W ≤ binaryCoverFaceOpen U p) (hq : W ≤ binaryCoverFaceOpen U q)
    (hd : faceDegree p+faceDegree q = n+1) (v : V) (hv : q v = 2) (k : Fin 2) (r : R) :
    single (p,Function.update q v k.castSucc) r ∈ pairedChains U R W n := by
  apply single_mem_supported R r
  refine ⟨hp,hq.trans (faceOpen_refinement_le U (endpoint_refines (faceRefines_refl q) v hv k.castSucc)),?_⟩
  have h := faceDegree_endpoint q v hv k
  change faceDegree p+faceDegree (Function.update q v k.castSucc) = n
  omega

/-- The original signed pair boundary stays on the same actual open and lowers the original total degree once. -/
theorem pairBoundary_mem (W : Opens T) (n : ℕ) (x : CellPairs R V) (hx : x ∈ pairedChains U R W (n+1)) :
    pairBoundary R V x ∈ pairedChains U R W n := by
  rw [← x.sum_single,map_finsuppSum]
  apply Submodule.sum_mem
  intro z hz
  rcases z with ⟨p,q⟩
  have h := hx hz
  change pairBoundary R V (single (p,q) (x (p,q))) ∈ pairedChains U R W n
  rw [pairBoundary_single]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro v _
    by_cases hv : p v = 2
    · exact Submodule.sub_mem _ (leftEndpoint_mem U R h.1 h.2.1 h.2.2 v hv 0 _)
        (leftEndpoint_mem U R h.1 h.2.1 h.2.2 v hv 1 _)
    · simp only [hv,ite_false,zero_mul,mul_zero,Finsupp.single_zero,sub_self]
      exact Submodule.zero_mem _
  · apply Submodule.sum_mem
    intro v _
    by_cases hv : q v = 2
    · exact Submodule.sub_mem _ (rightEndpoint_mem U R h.1 h.2.1 h.2.2 v hv 0 _)
        (rightEndpoint_mem U R h.1 h.2.1 h.2.2 v hv 1 _)
    · simp only [hv,ite_false,zero_mul,mul_zero,Finsupp.single_zero,sub_self]
      exact Submodule.zero_mem _

/-- The actual original pair differential, restricted without changing its original coefficients. -/
noncomputable def pairedDifferential (W : Opens T) (n : ℕ) :
    pairedChains U R W (n+1) →ₗ[R] pairedChains U R W n :=
  ((pairBoundary R V).comp (pairedChains U R W (n+1)).subtype).codRestrict _
    (fun x => pairBoundary_mem U R W n x.val x.property)

/-- The original pair differential still squares to zero after the actual support restriction. -/
theorem pairedDifferential_square (W : Opens T) (n : ℕ) :
    (pairedDifferential U R W n).comp (pairedDifferential U R W (n+1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (pairBoundary_square R V) x.val

/-- The actual native diagonal uses only originally available pairs and preserves their summed degree. -/
theorem diagonal_mem (W : Opens T) (n : ℕ) (x : chains U R W n) :
    flatDiagonal R V x.val ∈ pairedChains U R W n := by
  change pairCoordinates R V ((CechCubicalCell.diagonal R V).map x.val) ∈ _
  rw [← x.val.sum_single,map_finsuppSum,map_finsuppSum]
  apply Submodule.sum_mem
  intro p hp
  have hs := diagonal_single_support R p (x.val p)
  have hW := x.property.1 hp
  have hd : faceDegree p = n := by
    have h := x.property.2 hp
    change -(faceDegree p : ℤ) = -(n : ℤ) at h
    omega
  intro z hz
  have h := hs hz
  exact ⟨hW.trans (faceOpen_refinement_le U h.1),
    hW.trans (faceOpen_refinement_le U h.2.1),h.2.2.trans hd⟩

/-- The specified actual open diagonal on the original supported cell modules. -/
noncomputable def openDiagonal (W : Opens T) (n : ℕ) : chains U R W n →ₗ[R] pairedChains U R W n :=
  ((flatDiagonal R V).comp (chains U R W n).subtype).codRestrict _ (diagonal_mem U R W n)

/-- The original supported diagonal commutes with the original supported boundaries. -/
theorem openDiagonal_boundary (W : Opens T) (n : ℕ) :
    (pairedDifferential U R W n).comp (openDiagonal U R W (n+1)) =
      (openDiagonal U R W n).comp (differential U R W n) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact flatDiagonal_boundary R V x.val

/-- Original paired cells remain available under the original open restriction. -/
theorem pairedChains_mono {W Z : Opens T} (h : Z ≤ W) (n : ℕ) :
    pairedChains U R W n ≤ pairedChains U R Z n := by
  intro x hx z hz
  have h' := hx hz
  exact ⟨h.trans h'.1,h.trans h'.2.1,h'.2.2⟩

/-- The actual pair presheaf keeps the same original cells and coefficients on restriction. -/
noncomputable def pairedPresheaf (n : ℕ) : (Opens T)ᵒᵖ ⥤ ModuleCat R where
  obj W := ModuleCat.of R (pairedChains U R W.unop n)
  map f := ModuleCat.ofHom (Submodule.inclusion (pairedChains_mono U R (leOfHom f.unop) n))
  map_id W := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The original pair boundary commutes with the original pair restrictions. -/
noncomputable def pairedPresheafDifferential (n : ℕ) : pairedPresheaf U R (n+1) ⟶ pairedPresheaf U R n where
  app W := ModuleCat.ofHom (pairedDifferential U R W.unop n)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The original native pair presheaf boundary squares to zero. -/
theorem pairedPresheafDifferential_square (n : ℕ) :
    pairedPresheafDifferential U R (n+1) ≫ pairedPresheafDifferential U R n = 0 := by
  apply NatTrans.ext
  funext W
  exact ModuleCat.hom_ext (pairedDifferential_square U R W.unop n)

/-- The actual native original total pair complex. -/
noncomputable def pairedPresheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat R) ℕ :=
  ChainComplex.of (pairedPresheaf U R) (pairedPresheafDifferential U R) (pairedPresheafDifferential_square U R)

/-- The actual original diagonal is natural for every original open restriction. -/
noncomputable def presheafDiagonal (n : ℕ) : presheaf U R n ⟶ pairedPresheaf U R n where
  app W := ModuleCat.ofHom (openDiagonal U R W.unop n)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The specified diagonal is a chain map of the actual original open cell presheaves. -/
noncomputable def presheafDiagonalMap : presheafComplex U R ⟶ pairedPresheafComplex U R :=
  ChainComplex.ofHom (presheafDiagonal U R) (fun n => by
    simp only [pairedPresheafComplex,presheafComplex,ChainComplex.of_d]
    apply NatTrans.ext
    funext W
    change ModuleCat.ofHom ((pairedDifferential U R W.unop n).comp (openDiagonal U R W.unop (n+1))) =
      ModuleCat.ofHom ((openDiagonal U R W.unop n).comp (differential U R W.unop n))
    exact ModuleCat.hom_ext (openDiagonal_boundary U R W.unop n))

end BPFixedPoints.SheafTools.BinaryCells
