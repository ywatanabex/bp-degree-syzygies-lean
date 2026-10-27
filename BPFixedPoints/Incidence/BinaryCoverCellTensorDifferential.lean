import BPFixedPoints.Incidence.BinaryCoverCellTensorTermIso

/-! # Original tensor cells and Mathlib's standard total differential

The native totalization has the original unsigned left differential and the
original left-degree sign on the right differential. No differential is
redefined by the term isomorphism.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite Finsupp
open CechCubicalCell CechProduct GradedContraction
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type) [CommRing R]

@[reducible] noncomputable local instance tensorDifferentialChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (chains U R W n) :=
  (chains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorDifferentialChainsModule (W : Opens T) (n : ℕ) : Module R (chains U R W n) :=
  (chains U R W n).module
@[reducible] noncomputable local instance tensorDifferentialPairedAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] noncomputable local instance tensorDifferentialPairedModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- Original homogeneous cells have precisely their original overlap parity. -/
theorem chain_parity (W : Opens T) (i : ℕ) (x : chains U R W i) :
    (CechCubicalCell.contraction R (fun _ : V => 0)).sign x.val = (-1 : R)^i • x.val := by
  have h : (CechCubicalCell.contraction R (fun _ : V => 0)).sign.comp (chains U R W i).subtype =
      (-1 : R)^i • (chains U R W i).subtype := by
    apply cellLinear_ext_one U R W i
    intro p hp hd
    change (CechCubicalCell.contraction R (fun _ : V => 0)).sign (single p 1) = (-1 : R)^i • single p 1
    rw [CechCubicalCell.contraction_sign_single,hd]
  exact LinearMap.congr_fun h x

/-- The original degree-zero cell differential is actually zero. -/
theorem chain_d_zero (W : Opens T) (x : chains U R W 0) :
    (CechCubicalCell.contraction R (fun _ : V => 0)).d x.val = 0 :=
  contraction_d_zero_degree R (fun _ => 0) x.val x.property.2

/-- Native integer-unit signs act by the same original geometric coefficient sign. -/
theorem tensorSign_smul {M : Type*} [AddCommGroup M] [Module R M] (i : ℕ) (x : M) :
    ((-1 : ℤˣ)^i) • x = (-1 : R)^i • x := by
  rw [Units.smul_def,Units.val_pow_eq_pow_val]
  change ((-1 : ℤ)^i) • x = _
  rw [← Int.cast_smul_eq_zsmul (R := R),Int.cast_pow,Int.cast_neg,Int.cast_one]

/-- The original source term inside the native chain complex. -/
theorem cellPresheafComplex_X (i : ℕ) :
    (presheafComplex U R).X i = presheaf U R i := rfl

/-- The original source differential inside the native chain complex. -/
theorem cellPresheafComplex_d (i : ℕ) :
    (presheafComplex U R).d (i+1) i = presheafDifferential U R i := ChainComplex.of_d _ _ i

/-- The actual original tensor differential evaluated on arbitrary pure original supported cells. -/
theorem tensorPair_boundary_val (W : Opens T) (i j n : ℕ) (h : i+j=n)
    (x : chains U R W i) (y : chains U R W j) :
    pairBoundary R V (tensorPairLinear U R W i j n h (x ⊗ₜ[R] y)).val =
      pairCoordinates R V ((CechCubicalCell.contraction R (fun _ : V => 0)).d x.val ⊗ₜ[R] y.val +
        (CechCubicalCell.contraction R (fun _ : V => 0)).sign x.val ⊗ₜ[R] (CechCubicalCell.contraction R (fun _ : V => 0)).d y.val) := by
  rw [tensorPairLinear_tmul,pairBoundary_apply,LinearEquiv.symm_apply_apply]
  rfl

/-- The native first total differential, before applying the original comparison. -/
noncomputable abbrev tensorLeftDifferential (i j n : ℕ) :
    presheaf U R i ⊗ presheaf U R j ⟶ (tensorPresheafComplex R U).X n :=
  HomologicalComplex.mapBifunctor.d₁ (presheafComplex U R) (presheafComplex U R)
    (curriedTensor ((Opens T)ᵒᵖ ⥤ ModuleCat R)) (ComplexShape.down ℕ) i j n

/-- The native second total differential, with its native integer-unit sign. -/
noncomputable abbrev tensorRightDifferential (i j n : ℕ) :
    presheaf U R i ⊗ presheaf U R j ⟶ (tensorPresheafComplex R U).X n :=
  HomologicalComplex.mapBifunctor.d₂ (presheafComplex U R) (presheafComplex U R)
    (curriedTensor ((Opens T)ᵒᵖ ⥤ ModuleCat R)) (ComplexShape.down ℕ) i j n

/-- A degree-zero first factor has no native first differential. -/
theorem tensorLeftDifferential_zero (j n : ℕ) : tensorLeftDifferential U R 0 j n = 0 :=
  HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by decide)

/-- A degree-zero second factor has no native second differential. -/
theorem tensorRightDifferential_zero (i n : ℕ) : tensorRightDifferential U R i 0 n = 0 :=
  HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by decide)

/-- Native first total differential on its original positive bidegree summand. -/
theorem tensorLeftDifferential_succ (i j n : ℕ) (h : i+j=n) :
    tensorLeftDifferential U R (i+1) j n =
      (presheafDifferential U R i ▷ presheaf U R j) ≫ tensorPresheafInclusion R U i j n h := by
  have e := HomologicalComplex.mapBifunctor.d₁_eq (presheafComplex U R) (presheafComplex U R)
    (curriedTensor ((Opens T)ᵒᵖ ⥤ ModuleCat R)) (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n h
  have hs : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i+1,j) = 1 := rfl
  simpa only [cellPresheafComplex_d,cellPresheafComplex_X,hs,one_smul,curriedTensor_map_app] using e

/-- Native second total differential has exactly the original left-degree Koszul sign. -/
theorem tensorRightDifferential_succ (i j n : ℕ) (h : i+j=n) :
    tensorRightDifferential U R i (j+1) n =
      ((-1 : ℤˣ)^i) • ((presheaf U R i ◁ presheafDifferential U R j) ≫ tensorPresheafInclusion R U i j n h) := by
  have e := HomologicalComplex.mapBifunctor.d₂_eq (presheafComplex U R) (presheafComplex U R)
    (curriedTensor ((Opens T)ᵒᵖ ⥤ ModuleCat R)) (ComplexShape.down ℕ) i
    (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n h
  have hs : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i,j+1) =
      (-1 : ℤˣ)^i := rfl
  simpa only [cellPresheafComplex_d,cellPresheafComplex_X,hs,curriedTensor_obj_map] using e

/-- Every native bidegree differential agrees with the originally specified pair boundary. -/
theorem tensorPairTerm_boundary (i j n : ℕ) (h : i+j=n+1) :
    tensorPairTerm U R i j (n+1) h ≫ pairedPresheafDifferential U R n =
      (tensorLeftDifferential U R i j n+tensorRightDifferential U R i j n) ≫ tensorToPairTerm U R n := by
  cases i with
  | zero =>
    cases j with
    | zero => omega
    | succ j =>
      have hj : 0+j=n := by omega
      rw [tensorLeftDifferential_zero,tensorRightDifferential_succ U R 0 j n hj,
        zero_add,pow_zero,one_smul,Category.assoc,tensorInclusion_toPair]
      apply NatTrans.ext
      funext W
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      apply Subtype.ext
      change pairBoundary R V (tensorPairLinear U R W.unop 0 (j+1) (n+1) h (x ⊗ₜ[R] y)).val =
        pairCoordinates R V (x.val ⊗ₜ[R] (CechCubicalCell.contraction R (fun _ : V => 0)).d y.val)
      rw [tensorPair_boundary_val,chain_d_zero,chain_parity]
      simp
  | succ i =>
    cases j with
    | zero =>
      have hi : i+0=n := by omega
      rw [tensorRightDifferential_zero,tensorLeftDifferential_succ U R i 0 n hi,
        add_zero,Category.assoc,tensorInclusion_toPair]
      apply NatTrans.ext
      funext W
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      apply Subtype.ext
      change pairBoundary R V (tensorPairLinear U R W.unop (i+1) 0 (n+1) h (x ⊗ₜ[R] y)).val =
        pairCoordinates R V ((CechCubicalCell.contraction R (fun _ : V => 0)).d x.val ⊗ₜ[R] y.val)
      rw [tensorPair_boundary_val,chain_d_zero]
      simp
    | succ j =>
      have hL : i+(j+1)=n := by omega
      have hR : (i+1)+j=n := by omega
      rw [tensorLeftDifferential_succ U R i (j+1) n hL,tensorRightDifferential_succ U R (i+1) j n hR,
        Preadditive.add_comp,Linear.units_smul_comp,Category.assoc,Category.assoc,
        tensorInclusion_toPair,tensorInclusion_toPair]
      apply NatTrans.ext
      funext W
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      apply Subtype.ext
      change pairBoundary R V (tensorPairLinear U R W.unop (i+1) (j+1) (n+1) h (x ⊗ₜ[R] y)).val =
        pairCoordinates R V ((CechCubicalCell.contraction R (fun _ : V => 0)).d x.val ⊗ₜ[R] y.val) +
          ((-1 : ℤˣ)^(i+1)) • pairCoordinates R V (x.val ⊗ₜ[R] (CechCubicalCell.contraction R (fun _ : V => 0)).d y.val)
      rw [tensorPair_boundary_val,chain_parity,tensorSign_smul R]
      simp only [map_add,← TensorProduct.smul_tmul',map_smul]

end BPFixedPoints.SheafTools.BinaryCells
