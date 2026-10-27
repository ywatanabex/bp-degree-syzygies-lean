import BPFixedPoints.Incidence.IncidenceGluedGlobalSections
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Topology.Sheaves.MayerVietoris

/-! # Genuine Ext-defined cohomology of the incidence structure sheaf

The underlying abelian sheaf is obtained by forgetting multiplication in the
actual scheme structure sheaf. Cohomology uses Mathlib's Ext definition, not
state spaces or a proposed Cech complex. Degree zero is compared with the
existing global-function theorem. Higher local cohomology is retained as actual
Ext groups, with its genuine Mayer-Vietoris sequence.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

/-- Forget multiplication in the actual structure sheaf while retaining its sections and restrictions. -/
noncomputable def structureAbelianSheaf (X : Scheme.{0}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj X.sheaf

noncomputable local instance structureAbelianSheafHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Actual sheaf cohomology, defined by Ext from the constant integer sheaf. -/
noncomputable def structureSheafCohomology (X : Scheme.{0}) (n : ℕ) : Type 1 :=
  Sheaf.H (structureAbelianSheaf X) n

noncomputable instance structureSheafCohomology_addCommGroup (X : Scheme.{0}) (n : ℕ) :
    AddCommGroup (structureSheafCohomology X n) := by
  unfold structureSheafCohomology
  infer_instance

/-- The actual degree-zero Ext group is the additive group of genuine global functions. -/
noncomputable def structureSheafH0Equiv (X : Scheme.{0}) :
    structureSheafCohomology X 0 ≃+ Γ(X, ⊤) :=
  Sheaf.H.equiv₀ (structureAbelianSheaf X) (isTerminalTop (α := X.Opens))

/-- Actual local cohomology of an open, in the Ext-based presheaf of cohomology. -/
noncomputable def structureSheafLocalCohomology (X : Scheme.{0}) (n : ℕ) (U : X.Opens) :
    AddCommGrpCat.{1} :=
  (structureAbelianSheaf X).H' n U

/-- The genuine Mayer-Vietoris long exact sequence for two opens of the actual scheme. -/
theorem structureSheaf_mayerVietoris_exact (X : Scheme.{0}) (U V : X.Opens) (n : ℕ) :
    ((Opens.mayerVietorisSquare U V).sequence (structureAbelianSheaf X) n (n+1) rfl).Exact :=
  (Opens.mayerVietorisSquare U V).sequence_exact (structureAbelianSheaf X) n (n+1) rfl

end BPFixedPoints.SheafTools

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry SheafTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Actual degree-zero sheaf cohomology of the constructed incidence scheme is
its original incidence ring, as an additive group. No higher comparison is assumed. -/
noncomputable def incidenceStructureSheafH0Equiv :
    structureSheafCohomology G.incidenceGluedScheme 0 ≃+ G.IncidenceRing :=
  (structureSheafH0Equiv G.incidenceGluedScheme).trans G.incidenceGluedGlobalSectionsEquiv.toAddEquiv

/-- Existence form of the actual degree-zero Ext comparison. -/
theorem incidenceStructureSheafH0 :
    Nonempty (structureSheafCohomology G.incidenceGluedScheme 0 ≃+ G.IncidenceRing) :=
  ⟨G.incidenceStructureSheafH0Equiv⟩

end BPFixedPoints.Multigraph
