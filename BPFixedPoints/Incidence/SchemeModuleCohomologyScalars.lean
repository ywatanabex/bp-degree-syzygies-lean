import BPFixedPoints.Incidence.SchemeModuleBaseScalars
import BPFixedPoints.Incidence.SheafGlobalCechComparison
import BPFixedPoints.Incidence.SheafInjectiveFlasque

/-! # Original geometric base scalars on actual Ext-defined cohomology

Coefficients act on the original module sheaf through the given structural
morphism. The induced Ext action is postcomposition by these actual sheaf
endomorphisms, independently of every later state comparison.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)

/-- Original geometric coefficients on an actual open, restricted from the original global coefficients. -/
noncomputable def schemeBaseCoefficientAt (U : X.Opens) : R →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp (schemeBaseCoefficientHom f)

/-- Original geometric coefficients commute with every original restriction. -/
theorem schemeBaseCoefficientAt_map {U V : X.Opens} (i : U ⟶ V) (r : R) :
    X.presheaf.map i.op (schemeBaseCoefficientAt f V r) = schemeBaseCoefficientAt f U r := by
  dsimp only [schemeBaseCoefficientAt, RingHom.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- On the whole space the open coefficient map is the original global coefficient map. -/
theorem schemeBaseCoefficientAt_top : schemeBaseCoefficientAt f ⊤ = schemeBaseCoefficientHom f := by
  ext r
  change X.presheaf.map (𝟙 (op ⊤)) (schemeBaseCoefficientHom f r) = schemeBaseCoefficientHom f r
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (op ⊤)) (schemeBaseCoefficientHom f r)

/-- Original module sections on an actual open have the independently induced geometric base action. -/
@[instance_reducible] noncomputable def schemeBaseOpenModuleSections (U : X.Opens) :
    Module R Γ(M, U) := Module.compHom _ (schemeBaseCoefficientAt f U)

/-- The original scalar endomorphism of the actual underlying abelian sheaf. -/
noncomputable def schemeBaseAbelianScalar (r : R) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj M where
  hom :=
    { app U := (M.smul (schemeBaseCoefficientAt f U.unop r)).asHom
      naturality {U V} i := by
        change M.presheaf.map i ≫ (M.smul (schemeBaseCoefficientAt f V.unop r)).asHom =
          (M.smul (schemeBaseCoefficientAt f U.unop r)).asHom ≫ M.presheaf.map i
        rw [← schemeBaseCoefficientAt_map f i.unop r]
        exact (M.map_comp_smul i.unop (schemeBaseCoefficientAt f U.unop r)).symm }

/-- The actual scalar endomorphism acts by the original coefficient on every original section. -/
theorem schemeBaseAbelianScalar_app (r : R) (U : X.Opens) (s : Γ(M, U)) :
    (schemeBaseAbelianScalar f M r).hom.app (op U) s =
      schemeBaseCoefficientAt f U r • s := rfl

/-- The original unit coefficient acts as the identity sheaf morphism. -/
theorem schemeBaseAbelianScalar_one : schemeBaseAbelianScalar f M 1 = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U s
  let sM : Γ(M, U.unop) := s
  change schemeBaseCoefficientAt f U.unop 1 • sM = sM
  rw [map_one, one_smul]

/-- The original zero coefficient acts as the zero sheaf morphism. -/
theorem schemeBaseAbelianScalar_zero : schemeBaseAbelianScalar f M 0 = 0 := by
  apply Sheaf.hom_ext
  ext U s
  let sM : Γ(M, U.unop) := s
  change schemeBaseCoefficientAt f U.unop 0 • sM = 0
  rw [map_zero, zero_smul]

/-- Addition of original coefficients is addition of the actual sheaf endomorphisms. -/
theorem schemeBaseAbelianScalar_add (r s : R) :
    schemeBaseAbelianScalar f M (r+s) = schemeBaseAbelianScalar f M r + schemeBaseAbelianScalar f M s := by
  apply Sheaf.hom_ext
  ext U x
  let xM : Γ(M, U.unop) := x
  change schemeBaseCoefficientAt f U.unop (r+s) • xM =
    schemeBaseCoefficientAt f U.unop r • xM + schemeBaseCoefficientAt f U.unop s • xM
  rw [map_add, add_smul]

/-- Multiplication of original coefficients is the original composition in action order. -/
theorem schemeBaseAbelianScalar_mul (r s : R) :
    schemeBaseAbelianScalar f M (r*s) = schemeBaseAbelianScalar f M s ≫ schemeBaseAbelianScalar f M r := by
  apply Sheaf.hom_ext
  ext U x
  let xM : Γ(M, U.unop) := x
  change schemeBaseCoefficientAt f U.unop (r*s) • xM =
    schemeBaseCoefficientAt f U.unop r • (schemeBaseCoefficientAt f U.unop s • xM)
  rw [map_mul, mul_smul]

noncomputable local instance schemeBaseCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Coefficients act on actual Ext by postcomposition with the original geometric scalar endomorphism. -/
@[instance_reducible] noncomputable def schemeBaseExtModule
    (K : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (n : ℕ) :
    Module R (Ext.{1} K ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) where
  smul r x := x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n)
  one_smul x := by
    change x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M 1)) (add_zero n) = x
    rw [schemeBaseAbelianScalar_one]
    simp
  mul_smul r s x := by
    change x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M (r*s))) (add_zero n) =
      (x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M s)) (add_zero n)).comp
        (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n)
    rw [schemeBaseAbelianScalar_mul, ← Ext.mk₀_comp_mk₀]
    simp only [Ext.comp_assoc_of_second_deg_zero]
  smul_add r x y := by
    change (x+y).comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n) =
      x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n) +
        y.comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n)
    exact Ext.add_comp _ _ _ _
  smul_zero r := by
    change (0 : Ext.{1} K ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n).comp
      (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n) = 0
    simp only [Ext.zero_comp]
  add_smul r s x := by
    change x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M (r+s))) (add_zero n) =
      x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero n) +
        x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M s)) (add_zero n)
    rw [schemeBaseAbelianScalar_add, Ext.mk₀_add, Ext.comp_add]
  zero_smul x := by
    change x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M 0)) (add_zero n) = 0
    rw [schemeBaseAbelianScalar_zero, Ext.mk₀_zero, Ext.comp_zero]

/-- Actual global cohomology has the base action induced by the original structural morphism. -/
@[instance_reducible] noncomputable def schemeBaseCohomologyModule (n : ℕ) :
    Module R (Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :=
  schemeBaseExtModule f M _ n

/-- Actual ambient local cohomology has the same independently induced geometric base action. -/
@[instance_reducible] noncomputable def schemeBaseLocalCohomologyModule (U : X.Opens) (n : ℕ) :
    Module R (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n U) :=
  schemeBaseExtModule f M _ n

/-- The original global action is the native induced sheaf-cohomology map. -/
theorem schemeBaseCohomology_smul (n : ℕ) (r : R)
    (x : Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :
    letI := schemeBaseCohomologyModule f M n
    r • x = Sheaf.H.map (schemeBaseAbelianScalar f M r) n x := rfl

end BPFixedPoints.SchemeTools
