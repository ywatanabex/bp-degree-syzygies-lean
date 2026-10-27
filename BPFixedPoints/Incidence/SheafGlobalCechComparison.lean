import BPFixedPoints.Incidence.SheafTerminalCohomology
import BPFixedPoints.Incidence.SheafTwoOpenCechComparison

/-! # Mayer-Vietoris quotients compare with actual global sheaf cohomology

For a two-open cover, the preceding local Ext comparison now has genuine global
cohomology as its target. Local vanishing remains an explicit hypothesis; the
comparison is induced by the original Mayer-Vietoris connecting morphism.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]
noncomputable local instance globalCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Local Ext on a covering open equals independently defined global cohomology. -/
noncomputable def localSheafCoverEquiv (n : ℕ) (U : Opens T) (hU : U = ⊤) :
    F.H' n U ≃+ F.H n := by
  subst U
  exact localSheafTopEquiv F n

variable (U V : Opens T) (hcover : U ⊔ V = ⊤) (n : ℕ)

/-- The genuine global connecting homomorphism on a two-open cover. -/
noncomputable def mayerVietorisGlobalConnecting :
    F.H' n (U ⊓ V) →+ F.H (n+1) :=
  (localSheafCoverEquiv F (n+1) (U ⊔ V) hcover).toAddMonoidHom.comp
    ((Opens.mayerVietorisSquare U V).δ F n (n+1) rfl).hom

/-- The previously constructed quotient comparison is induced by the actual
Mayer-Vietoris connecting map on representatives. -/
theorem mayerVietorisCokernelEquiv_mk
    [Subsingleton (F.H' (n+1) U)] [Subsingleton (F.H' (n+1) V)]
    (x : F.H' n (U ⊓ V)) :
    mayerVietorisCokernelEquiv F U V n (QuotientAddGroup.mk x) =
      (Opens.mayerVietorisSquare U V).δ F n (n+1) rfl x := by
  rfl

/-- In every degree, the actual restriction cokernel computes global
cohomology when the next local cohomology vanishes on both cover members. -/
noncomputable def mayerVietorisGlobalCokernelEquiv
    [Subsingleton (F.H' (n+1) U)] [Subsingleton (F.H' (n+1) V)] :
    mayerVietorisCokernel F U V n ≃+ F.H (n+1) :=
  (mayerVietorisCokernelEquiv F U V n).trans
    (localSheafCoverEquiv F (n+1) (U ⊔ V) hcover)

/-- The global comparison is induced by the genuine global connecting map. -/
theorem mayerVietorisGlobalCokernelEquiv_mk
    [Subsingleton (F.H' (n+1) U)] [Subsingleton (F.H' (n+1) V)]
    (x : F.H' n (U ⊓ V)) :
    mayerVietorisGlobalCokernelEquiv F U V hcover n (QuotientAddGroup.mk x) =
      mayerVietorisGlobalConnecting F U V hcover n x := by
  rfl

/-- The ordinary two-open Cech section quotient computes actual global H1
under the explicit two local degree-one vanishing hypotheses. -/
noncomputable def twoOpenSectionGlobalH1Equiv
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] :
    twoOpenSectionH1 F U V ≃+ F.H 1 :=
  (twoOpenSectionH1Equiv F U V).trans (localSheafCoverEquiv F 1 (U ⊔ V) hcover)

/-- Existence form retaining the cover and local vanishing hypotheses. -/
theorem twoOpenSectionGlobalH1_comparison (hcover : U ⊔ V = ⊤)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] :
    Nonempty (twoOpenSectionH1 F U V ≃+ F.H 1) :=
  ⟨twoOpenSectionGlobalH1Equiv F U V hcover⟩

end BPFixedPoints.SheafTools
