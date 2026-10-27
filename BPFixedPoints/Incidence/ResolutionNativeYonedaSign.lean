import BPFixedPoints.Incidence.ResolutionNativeSyzygyStep
import BPFixedPoints.Incidence.AcyclicResolutionYonedaRightRecursion

/-! # The native original resolution roof and the original iterated Yoneda sign

The sign is obtained from the actual successive cone projections. Neither
the native roof nor the original iterated Yoneda comparison is redefined.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
universe w w' v u

/-- The accumulated signs of the original native successor cone projections. -/
def nativeYonedaSign : ℕ → ℤˣ
  | 0 => 1
  | n+1 => ((n : ℤ)+1).negOnePow * nativeYonedaSign n

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]

/-- The actual native Ext identification preserves integer-unit multiplication. -/
theorem nativeExt_units_hom {A B : C} {n : ℕ} (a : ℤˣ) (x : Ext.{w'} A B n) :
    (a • x).hom = a • x.hom := by
  simpa only [Units.smul_def,Ext.homAddEquiv_apply] using map_zsmul Ext.homAddEquiv (a : ℤ) x

omit [HasDerivedCategory C] in
/-- Integer units commute with the original Ext composition on the left. -/
theorem nativeExt_units_comp {A B D : C} {p q r : ℕ} (a : ℤˣ)
    (x : Ext.{w'} A B p) (y : Ext.{w'} B D q) (h : p+q=r) :
    (a • x).comp y h = a • (x.comp y h) := by
  change (y.postcomp A h) ((a : ℤ) • x) = (a : ℤ) • (y.postcomp A h) x
  exact map_zsmul (y.postcomp A h) (a : ℤ) x

omit [HasDerivedCategory C] in
/-- Integer units commute with the original Ext composition on the right. -/
theorem nativeExt_comp_units {A B D : C} {p q r : ℕ} (a : ℤˣ)
    (x : Ext.{w'} A B p) (y : Ext.{w'} B D q) (h : p+q=r) :
    x.comp (a • y) h = a • (x.comp y h) := by
  change (x.precomp D h) ((a : ℤ) • y) = (a : ℤ) • (x.precomp D h) y
  exact map_zsmul (x.precomp D h) (a : ℤ) y

variable (P : ChainComplex C ℕ) (hP : ∀ n, P.ExactAt (n+1))

/-- The existing native cocycle Ext roof of the original degree-n syzygy projection. -/
abbrev nativeProjectionExt (n : ℕ) : Ext.{w'} (complexSyzygy P 0) (complexSyzygy P n) n :=
  nativeCocycleExt P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
      n (cokernel.π (P.d (n+1) n)) (cokernel.condition _)

/-- The native original projection roofs retain the actual right SES connecting recursion and its forced successor sign. -/
theorem nativeProjectionExt_step (n : ℕ) :
    (nativeProjectionExt P hP n).comp (complexSyzygy_shortExact P n (hP n)).extClass rfl =
      ((n : ℤ)+1).negOnePow • nativeProjectionExt P hP (n+1) := by
  apply Ext.ext
  rw [Ext.comp_hom,nativeExt_units_hom,ShortComplex.ShortExact.extClass_hom]
  apply (cancel_epi (nativeAugmentationIso P (cokernel.π (P.d 1 0)) (cokernel.condition _)
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP).hom).mp
  simp only [nativeProjectionExt,nativeCocycleExt_hom,nativeCocycleRoof,ShiftedHom.comp,
    Linear.comp_units_smul,← Category.assoc,Iso.hom_inv_id,Category.id_comp]
  simp only [Category.assoc]
  convert nativeSyzygyProjection_step P hP n using 1
  simp only [ShiftedHom.comp,Category.assoc]
  rfl

/-- The original native degree-zero projection is the original identity Ext morphism. -/
theorem nativeProjectionExt_zero : nativeProjectionExt P hP 0=Ext.mk₀ (𝟙 (complexSyzygy P 0)) := by
  have h := nativeCocycleExt_zero_factor P (cokernel.π (P.d 1 0))
    (cokernel.condition _) (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)) hP
      (𝟙 (cokernel (P.d 1 0))) (by rw [Category.comp_id]; exact cokernel.condition _)
  simpa only [Category.comp_id,complexSyzygy,nativeProjectionExt] using h

/-- In every degree, the original native projection roof is the original iterated Yoneda projection class with its accumulated cone sign. -/
theorem nativeProjectionExt_yoneda (n : ℕ) :
    nativeProjectionExt P hP n = nativeYonedaSign n •
      ((complexTower P hP).connecting (complexSyzygy P n) n (Ext.mk₀ (𝟙 (complexSyzygy P n)))) := by
  induction n with
  | zero => simpa [nativeYonedaSign,ExactTower.connecting] using nativeProjectionExt_zero P hP
  | succ n ih =>
    have h := nativeProjectionExt_step P hP n
    rw [ih] at h
    rw [nativeExt_units_comp] at h
    have h' := congrArg (fun x => ((n : ℤ)+1).negOnePow • x) h
    simp only [smul_smul,Int.units_mul_self,one_smul] at h'
    calc
      _ = (nativeYonedaSign (n+1)) •
          (((complexTower P hP).connecting (complexSyzygy P n) n (Ext.mk₀ (𝟙 (complexSyzygy P n)))).comp
            (complexSyzygy_shortExact P n (hP n)).extClass rfl) := h'.symm
      _ = _ := congrArg (fun x => nativeYonedaSign (n+1) • x)
        (ExactTower.connecting_projection_succ n (complexTower P hP)).symm

end
end BPFixedPoints.ExtResolutionTools
