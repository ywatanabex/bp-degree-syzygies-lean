import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars
import BPFixedPoints.Incidence.SheafConnectingNaturality
import BPFixedPoints.Incidence.SheafFlasqueCohomology

/-! # Geometric base linearity of actual Ext evaluations and connecting maps

The base actions are the original structural scalar endomorphisms, acting by
postcomposition on Ext. Naturality of the original evaluation and connecting
maps therefore gives linearity without transporting any action from states.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance schemeCohomologyLinearityHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Actual local degree-zero evaluation is linear for the original geometric base actions. -/
noncomputable def schemeBaseLocalH0LinearEquiv (U : X.Opens) :
    letI := schemeBaseLocalCohomologyModule f M U 0
    letI := schemeBaseOpenModuleSections f M U
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 0 U ≃ₗ[R] Γ(M, U) := by
  letI := schemeBaseLocalCohomologyModule f M U 0
  letI := schemeBaseOpenModuleSections f M U
  refine { SheafTools.localSheafH0Equiv ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U with
    map_smul' := ?_ }
  intro r x
  let sx : Γ(M, U) := SheafTools.localSheafH0Equiv ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U x
  change SheafTools.localSheafH0Equiv _ U
      (x.comp (Ext.mk₀ (schemeBaseAbelianScalar f M r)) (add_zero 0)) =
    schemeBaseCoefficientAt f U r • sx
  rw [SheafTools.localSheafH0Equiv_postcomp]
  rfl

/-- Genuine global degree-zero evaluation retains the original global geometric base action. -/
noncomputable def schemeBaseH0LinearEquiv :
    letI := schemeBaseCohomologyModule f M 0
    letI := schemeBaseModuleSections f M
    Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 0 ≃ₗ[R] Γ(M, ⊤) := by
  letI := schemeBaseCohomologyModule f M 0
  letI := schemeBaseModuleSections f M
  refine { Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop with
    map_smul' := ?_ }
  intro r x
  let sx : Γ(M, ⊤) := Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop x
  change Sheaf.H.equiv₀ _ isTerminalTop (Sheaf.H.map (schemeBaseAbelianScalar f M r) 0 x) =
    schemeBaseCoefficientHom f r • sx
  refine (Sheaf.H.equiv₀_naturality isTerminalTop (schemeBaseAbelianScalar f M r) x).symm.trans ?_
  change schemeBaseCoefficientAt f ⊤ r • sx = schemeBaseCoefficientHom f r • sx
  rw [schemeBaseCoefficientAt_top]

/-- In every degree the genuine whole-space Ext comparison preserves the original base action. -/
noncomputable def schemeBaseLocalTopLinearEquiv (n : ℕ) :
    letI := schemeBaseLocalCohomologyModule f M ⊤ n
    letI := schemeBaseCohomologyModule f M n
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n ⊤ ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n := by
  letI := schemeBaseLocalCohomologyModule f M ⊤ n
  letI := schemeBaseCohomologyModule f M n
  refine { SheafTools.localSheafTopEquiv ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n with
    map_smul' := ?_ }
  intro r x
  exact SheafTools.localSheafTopEquiv_naturality (schemeBaseAbelianScalar f M r) n x

/-- The genuine global Mayer-Vietoris connecting map preserves the original base scalars. -/
theorem schemeBaseGlobalConnecting_smul (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (n : ℕ) (r : R) (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V)) :
    letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
    letI := schemeBaseCohomologyModule f M (n+1)
    SheafTools.mayerVietorisGlobalConnecting ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      U V hcover n (r • x) =
        r • SheafTools.mayerVietorisGlobalConnecting ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
          U V hcover n x := by
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  letI := schemeBaseCohomologyModule f M (n+1)
  exact SheafTools.mayerVietorisGlobalConnecting_naturality (schemeBaseAbelianScalar f M r)
    U V hcover n x

end BPFixedPoints.SchemeTools
