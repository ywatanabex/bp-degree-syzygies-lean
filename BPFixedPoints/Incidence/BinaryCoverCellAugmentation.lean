import BPFixedPoints.Incidence.BinaryCoverCellComplex

/-! # The original cubical augmentation is exact before sheafification

The augmentation is the original tensor component projection. Its kernel
is the original degree-one boundary image on every actual open, whether
or not any chart contains that whole open. No presheaf epimorphism is asserted.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance augmentationChainsAddCommGroup (W : Opens T) (n : ℕ) :
    AddCommGroup (chains U R W n) := (chains U R W n).addCommGroup
@[reducible] noncomputable local instance augmentationChainsModule (W : Opens T) (n : ℕ) :
    Module R (chains U R W n) := (chains U R W n).module

/-- The original degree-zero augmentation on an actual open is the original tensor component projection. -/
noncomputable def componentAugmentation (W : Opens T) : chains U R W 0 →ₗ[R] Components R V :=
  (CechCubicalCell.contraction R (fun _ : V => 0)).p.comp (chains U R W 0).subtype

/-- The original augmentation kills the original degree-one differential. -/
theorem componentAugmentation_boundary (W : Opens T) :
    (componentAugmentation U R W).comp (differential U R W 0) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (CechCubicalCell.contraction R (fun _ : V => 0)).p_d x.val

/-- Every original degree-zero augmentation kernel has a primitive on the same actual open. -/
theorem componentAugmentation_range_eq_ker (W : Opens T) :
    LinearMap.range (differential U R W 0) = LinearMap.ker (componentAugmentation U R W) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (componentAugmentation_boundary U R W) y
  · intro hx
    by_cases hv : HasVertex U W
    · let b := baseVertex U W
      have hs : x.val ∈ subfaces R (maximalFace U W) := by
        rw [← available_eq_subfaces U W R hv]
        exact x.property.1
      have hd : (CechCubicalCell.contraction R b).d x.val = 0 :=
        contraction_d_zero_degree R b x.val x.property.2
      have hp : (CechCubicalCell.contraction R b).p x.val = 0 := by
        rw [contraction_p_eq R b (fun _ => 0)]
        exact hx
      have hg := (contraction_degrees R b).h 0 x.val x.property.2
      have hz : (CechCubicalCell.contraction R b).h x.val ∈ chains U R W 1 := by
        constructor
        · rw [available_eq_subfaces U W R hv]
          exact contraction_h_subfaces R b (maximalFace U W) (baseVertex_refines U W hv) x.val hs
        · change (CechCubicalCell.contraction R b).h x.val ∈
            supported R R {q | cellDegree q = -((1 : ℕ) : ℤ)}
          simpa only [zero_add,Nat.cast_one,neg_zero] using hg
      refine ⟨⟨(CechCubicalCell.contraction R b).h x.val,hz⟩,?_⟩
      apply Subtype.ext
      change (CechCubicalCell.contraction R (fun _ : V => 0)).d
        ((CechCubicalCell.contraction R b).h x.val) = x.val
      rw [contraction_d_eq R (fun _ : V => 0) b]
      have he := LinearMap.congr_fun (CechCubicalCell.contraction R b).homotopy x.val
      simpa only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.comp_apply,
        Module.End.one_apply,hd,hp,map_zero,add_zero] using he
    · have hx0 : x.val = 0 := by
        have h := x.property.1
        change x.val ∈ available U W R at h
        rw [available_eq_bot U W R hv] at h
        exact h
      have he : x = 0 := Subtype.ext hx0
      exact ⟨0,by rw [map_zero,he]⟩

/-- The original component augmentation commutes with the original restriction inclusions. -/
noncomputable def componentPresheafAugmentation : presheaf U R 0 ⟶
    (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of R (Components R V)) where
  app W := ModuleCat.ofHom (componentAugmentation U R W.unop)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The original presheaf augmentation kills the original presheaf differential. -/
theorem componentPresheafAugmentation_zero :
    presheafDifferential U R 0 ≫ componentPresheafAugmentation U R = 0 := by
  apply NatTrans.ext
  funext W
  exact ModuleCat.hom_ext (componentAugmentation_boundary U R W.unop)

/-- Native degree-zero augmented exactness of the original cell presheaf, without a cover assumption. -/
theorem componentPresheafAugmentation_exact :
    (ShortComplex.mk (presheafDifferential U R 0) (componentPresheafAugmentation U R)
      (componentPresheafAugmentation_zero U R)).Exact := by
  let S := ShortComplex.mk (presheafDifferential U R 0) (componentPresheafAugmentation U R)
    (componentPresheafAugmentation_zero U R)
  change S.Exact
  rw [ShortComplex.exact_iff_isZero_homology,IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext W
  let E := (evaluation (Opens T)ᵒᵖ (ModuleCat R)).obj W
  have hW : (S.map E).Exact := by
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact componentAugmentation_range_eq_ker U R W.unop
  exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp hW)
    (S.mapHomologyIso E).symm).eq_of_src _ _

end BPFixedPoints.SheafTools.BinaryCells
