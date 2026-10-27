import BPFixedPoints.Incidence.SheafGlobalCechComparison

/-! # Naturality of the original global Mayer-Vietoris connecting map

All maps are the native Ext maps of the actual sheaves. Naturality is Ext
associativity followed by the existing whole-space cohomology comparison.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : Type} [TopologicalSpace T]
noncomputable local instance connectingNaturalityHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (a : F ⟶ G)

/-- The genuine comparison on an open equal to the whole space is natural in the actual sheaf. -/
theorem localSheafCoverEquiv_naturality (n : ℕ) (W : Opens T) (hW : W = ⊤)
    (x : F.H' n W) :
    localSheafCoverEquiv G n W hW (x.comp (Ext.mk₀ a) (add_zero n)) =
      Sheaf.H.map a n (localSheafCoverEquiv F n W hW x) := by
  subst W
  exact localSheafTopEquiv_naturality a n x

/-- The original global connecting map commutes with the actual induced sheaf maps in every degree. -/
theorem mayerVietorisGlobalConnecting_naturality (U V : Opens T) (hcover : U ⊔ V = ⊤)
    (n : ℕ) (x : F.H' n (U ⊓ V)) :
    mayerVietorisGlobalConnecting G U V hcover n (x.comp (Ext.mk₀ a) (add_zero n)) =
      Sheaf.H.map a (n+1) (mayerVietorisGlobalConnecting F U V hcover n x) := by
  have hc : (Opens.mayerVietorisSquare U V).δ G n (n+1) rfl
        (x.comp (Ext.mk₀ a) (add_zero n)) =
      ((Opens.mayerVietorisSquare U V).δ F n (n+1) rfl x).comp
        (Ext.mk₀ a) (add_zero (n+1)) := by
    exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (show 1+n = n+1 by omega)).symm
  exact (congrArg (localSheafCoverEquiv G (n+1) (U ⊔ V) hcover) hc).trans
    (localSheafCoverEquiv_naturality a (n+1) (U ⊔ V) hcover _)

/-- The genuine global connecting map is surjective under the original two local vanishing hypotheses. -/
theorem mayerVietorisGlobalConnecting_surjective
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (U V : Opens T) (hcover : U ⊔ V = ⊤) (n : ℕ)
    [Subsingleton (F.H' (n+1) U)] [Subsingleton (F.H' (n+1) V)] :
    Function.Surjective (mayerVietorisGlobalConnecting F U V hcover n) :=
  (localSheafCoverEquiv F (n+1) (U ⊔ V) hcover).surjective.comp
    (mayerVietoris_delta_surjective F U V n)

end BPFixedPoints.SheafTools
