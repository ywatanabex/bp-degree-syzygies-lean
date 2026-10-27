import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Sections of finite biproducts and kernels of sheaves of modules

General facts about sheaves of modules `SheafOfModules R` over a sheaf of rings `R` on any site,
used for the kernel bundle of the incidence evaluation map:

* sections of a finite sum of morphisms are the sums of the sections
  (`sheafOfModules_sum_app_apply`);
* the sections of a finite biproduct `⨁ f` over an object are the product of the sections of
  the summands, by the projections and inclusions of the biproduct
  (`biproductSectionsEquiv`, `biproduct_section_ext`, `biproduct_ι_π_app_self`,
  `biproduct_ι_π_app_ne`), and morphisms into and out of `⨁ f` act on sections through their
  components (`biproduct_lift_app_π`, `biproduct_desc_app`);
* the sections of Mathlib's kernel `kernel g` over an object are the kernel of `g` on those
  sections: `kernel.ι g` is injective on sections and its image is the kernel
  (`kernel_ι_app_injective`, `kernel_ι_app_exists`);
* restriction to an object `U` of the site (`SheafOfModules.overFunctor R U`) is additive and
  preserves limits indexed by small categories (`overFunctor_isLimit`), so it preserves kernels: the restriction of
  `kernel.ι g` is a kernel of the restriction of `g` (`isLimit_kernelFork_over`), and the
  restriction of the kernel is Mathlib's kernel of the restricted morphism
  (`kernelOverIso`, `kernelOverIso_hom_ι`).

Nothing about the incidence evaluation map is proved here.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

universe v₁ u₁ u

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-! ### Sums of morphisms on sections -/

/-- Evaluation of sheaves of modules on an object is an additive functor. -/
instance sheafOfModules_evaluation_additive (X : Cᵒᵖ) :
    (SheafOfModules.evaluation R X).Additive :=
  inferInstanceAs ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation _ X).Additive)

/-- Sections of a finite sum of morphisms of sheaves of modules are the sums of the sections. -/
theorem sheafOfModules_sum_app_apply {M N : SheafOfModules.{u} R} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (X : Cᵒᵖ) (x : M.val.obj X) :
    ((∑ i ∈ s, f i).val.app X).hom x = ∑ i ∈ s, ((f i).val.app X).hom x := by
  have h := congrArg (fun g => g.hom x) (Functor.map_sum (SheafOfModules.evaluation R X) f s)
  rw [ModuleCat.hom_sum, LinearMap.sum_apply] at h
  exact h

/-! ### Sections of finite biproducts -/

section Biproduct

variable {ι : Type*} [Fintype ι] (f : ι → SheafOfModules.{u} R) [HasBiproduct f]

/-- A section of a finite biproduct is the sum of the inclusions of its projections. -/
theorem biproduct_section_eq_sum (X : Cᵒᵖ) (x : (⨁ f).val.obj X) :
    x = ∑ i, ((biproduct.ι f i).val.app X).hom (((biproduct.π f i).val.app X).hom x) := by
  have h := congrArg (fun g : ⨁ f ⟶ ⨁ f => (g.val.app X).hom x) (biproduct.total (f := f))
  rw [sheafOfModules_sum_app_apply] at h
  exact h.symm

/-- Sections of a finite biproduct are determined by their projections. -/
theorem biproduct_section_ext (X : Cᵒᵖ) {x y : (⨁ f).val.obj X}
    (h : ∀ i, ((biproduct.π f i).val.app X).hom x = ((biproduct.π f i).val.app X).hom y) :
    x = y := by
  rw [biproduct_section_eq_sum f X x, biproduct_section_eq_sum f X y]
  simp only [h]

/-- The projection of the inclusion of a section into its own summand is the section. -/
theorem biproduct_ι_π_app_self (i : ι) (X : Cᵒᵖ) (x : (f i).val.obj X) :
    ((biproduct.π f i).val.app X).hom (((biproduct.ι f i).val.app X).hom x) = x :=
  congrArg (fun g : f i ⟶ f i => (g.val.app X).hom x) (biproduct.ι_π_self f i)

/-- The projection of the inclusion of a section into another summand is zero. -/
theorem biproduct_ι_π_app_ne {i j : ι} (h : i ≠ j) (X : Cᵒᵖ) (x : (f i).val.obj X) :
    ((biproduct.π f j).val.app X).hom (((biproduct.ι f i).val.app X).hom x) = 0 :=
  congrArg (fun g : f i ⟶ f j => (g.val.app X).hom x) (biproduct.ι_π_ne f h)

/-- A morphism into a finite biproduct has the given components on sections. -/
theorem biproduct_lift_app_π {M : SheafOfModules.{u} R} (g : ∀ i, M ⟶ f i) (i : ι) (X : Cᵒᵖ)
    (x : M.val.obj X) :
    ((biproduct.π f i).val.app X).hom (((biproduct.lift g).val.app X).hom x) =
      ((g i).val.app X).hom x :=
  congrArg (fun φ : M ⟶ f i => (φ.val.app X).hom x) (biproduct.lift_π g i)

/-- A morphism out of a finite biproduct is, on sections, the sum of its components applied to
the projections. -/
theorem biproduct_desc_app {N : SheafOfModules.{u} R} (g : ∀ i, f i ⟶ N) (X : Cᵒᵖ)
    (x : (⨁ f).val.obj X) :
    ((biproduct.desc g).val.app X).hom x =
      ∑ i, ((g i).val.app X).hom (((biproduct.π f i).val.app X).hom x) := by
  conv_lhs => rw [biproduct_section_eq_sum f X x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun φ : f i ⟶ N => (φ.val.app X).hom (((biproduct.π f i).val.app X).hom x))
    (biproduct.ι_desc g i)

/-- **Sections of a finite biproduct.** The sections of `⨁ f` over `X` are the families of
sections of the summands, by the projections, with inverse the sum of the inclusions. -/
noncomputable def biproductSectionsEquiv (X : Cᵒᵖ) :
    (⨁ f).val.obj X ≃ₗ[R.obj.obj X] (∀ i, (f i).val.obj X) where
  toFun x i := ((biproduct.π f i).val.app X).hom x
  map_add' x y := by
    funext i
    simp
  map_smul' a x := by
    funext i
    simp
  invFun y := ∑ i, ((biproduct.ι f i).val.app X).hom (y i)
  left_inv x := (biproduct_section_eq_sum f X x).symm
  right_inv y := by
    funext j
    simp only [map_sum]
    rw [Finset.sum_eq_single j (fun i _ hij => biproduct_ι_π_app_ne f hij X (y i))
      (fun hj => (hj (Finset.mem_univ j)).elim)]
    exact biproduct_ι_π_app_self f j X (y j)

/-- The components of a section of a biproduct are its projections. -/
@[simp] theorem biproductSectionsEquiv_apply (X : Cᵒᵖ) (x : (⨁ f).val.obj X) (i : ι) :
    biproductSectionsEquiv f X x i = ((biproduct.π f i).val.app X).hom x :=
  rfl

/-- The projections of the section with prescribed components are those components. -/
@[simp] theorem biproduct_π_app_biproductSectionsEquiv_symm (X : Cᵒᵖ) (y : ∀ i, (f i).val.obj X)
    (i : ι) :
    ((biproduct.π f i).val.app X).hom ((biproductSectionsEquiv f X).symm y) = y i :=
  congrFun ((biproductSectionsEquiv f X).apply_symm_apply y) i

end Biproduct

/-! ### Sections of kernels -/

section Kernel

variable {A B : SheafOfModules.{u} R} (g : A ⟶ B)

/-- On the sections over `X`, the inclusion of Mathlib's kernel of `g` is the inclusion of the
kernel of `g` on sections, up to a linear isomorphism. -/
theorem kernel_ι_app_eq (X : Cᵒᵖ) :
    ∃ e : (kernel g).val.obj X ≃ₗ[R.obj.obj X] LinearMap.ker (g.val.app X).hom,
      ∀ k, ((kernel.ι g).val.app X).hom k = (e k : A.val.obj X) := by
  let G := SheafOfModules.evaluation R X
  let i := PreservesKernel.iso G g ≪≫ ModuleCat.kernelIsoKer (G.map g)
  refine ⟨i.toLinearEquiv, fun k => ?_⟩
  have h : G.map (kernel.ι g) = i.hom ≫ ModuleCat.ofHom (LinearMap.ker (G.map g).hom).subtype := by
    simp only [i, Iso.trans_hom, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact congrArg (fun φ => φ.hom k) h

/-- The inclusion of the kernel is injective on sections. -/
theorem kernel_ι_app_injective (X : Cᵒᵖ) : Function.Injective ((kernel.ι g).val.app X).hom := by
  obtain ⟨e, he⟩ := kernel_ι_app_eq g X
  intro k k' h
  rw [he, he] at h
  exact e.injective (Subtype.ext h)

/-- Every section killed by `g` is a section of the kernel. -/
theorem kernel_ι_app_exists (X : Cᵒᵖ) (x : A.val.obj X) (hx : (g.val.app X).hom x = 0) :
    ∃ k, ((kernel.ι g).val.app X).hom k = x := by
  obtain ⟨e, he⟩ := kernel_ι_app_eq g X
  exact ⟨e.symm ⟨x, hx⟩, by rw [he, LinearEquiv.apply_symm_apply]⟩

/-- Sections of the kernel are killed by `g`. -/
theorem kernel_ι_app_comp (X : Cᵒᵖ) (k : (kernel g).val.obj X) :
    (g.val.app X).hom (((kernel.ι g).val.app X).hom k) = 0 :=
  congrArg (fun φ : kernel g ⟶ B => (φ.val.app X).hom k) (kernel.condition g)

end Kernel

/-! ### Restriction to an object of the site -/

section Over

variable (U : C)

/-- Restriction of sheaves of modules to `U` is additive. -/
instance overFunctor_additive : (SheafOfModules.overFunctor.{u} R U).Additive where
  map_add := rfl

/-- **Restriction preserves limits.** The restriction to `U` of a limit cone of sheaves of
modules is a limit cone: limits are computed on sections, and the sections of a restriction over
`S ⟶ U` are the sections over `S`. -/
noncomputable def overFunctor_isLimit {D : Type} [SmallCategory D] {F : D ⥤ SheafOfModules.{u} R}
    {c : Cone F} (hc : IsLimit c) :
    IsLimit ((SheafOfModules.overFunctor R U).mapCone c) := by
  apply isLimitOfReflects (SheafOfModules.forget _)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro S
  have h := isLimitOfPreserves (SheafOfModules.evaluation R (op S.unop.left)) hc
  exact isLimitOfPreserves (ModuleCat.restrictScalars _) h

variable {A B : SheafOfModules.{u} R} (g : A ⟶ B)

/-- **Restriction preserves kernels.** The restriction to `U` of the inclusion of Mathlib's
kernel of `g` is a kernel of the restriction of `g`. -/
noncomputable def isLimit_kernelFork_over :
    IsLimit (KernelFork.ofι ((SheafOfModules.overFunctor R U).map (kernel.ι g))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero]) :
        KernelFork ((SheafOfModules.overFunctor R U).map g)) :=
  (KernelFork.isLimitMapConeEquiv (KernelFork.ofι (kernel.ι g) (kernel.condition g))
    (SheafOfModules.overFunctor R U)).toFun (overFunctor_isLimit U (kernelIsKernel g))

/-- The restriction of Mathlib's kernel of `g` to `U` is Mathlib's kernel of the restriction
of `g`. -/
noncomputable def kernelOverIso :
    (SheafOfModules.overFunctor R U).obj (kernel g) ≅
      kernel ((SheafOfModules.overFunctor R U).map g) :=
  IsLimit.conePointUniqueUpToIso (isLimit_kernelFork_over U g) (limit.isLimit _)

/-- The comparison of kernels commutes with the inclusions into the restriction of `A`. -/
@[reassoc (attr := simp)] theorem kernelOverIso_hom_ι :
    (kernelOverIso U g).hom ≫ kernel.ι ((SheafOfModules.overFunctor R U).map g) =
      (SheafOfModules.overFunctor R U).map (kernel.ι g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimit_kernelFork_over U g) (limit.isLimit _)
    WalkingParallelPair.zero

end Over

end BPFixedPoints.Multigraph
