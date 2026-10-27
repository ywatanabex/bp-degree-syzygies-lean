import BPFixedPoints.Incidence.StructureSheafCohomology
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # A genuine higher-cohomology quotient from Mayer-Vietoris

If the next cohomology vanishes on the two opens, their union's next cohomology
is the cokernel of the actual restriction difference on the intersection. The
vanishing assumptions are explicit and are not inferred from affineness here.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]

noncomputable local instance mayerVietorisQuotientHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
  (U V : Opens T) (n : ℕ)

/-- The actual restriction cokernel appearing in the Ext-defined Mayer-Vietoris sequence. -/
noncomputable def mayerVietorisCokernel : Type 1 :=
  (F.H' n (U ⊓ V)) ⧸ ((Opens.mayerVietorisSquare U V).fromBiprod F n).hom.range

noncomputable instance mayerVietorisCokernel_addCommGroup :
    AddCommGroup (mayerVietorisCokernel F U V n) := by
  unfold mayerVietorisCokernel
  infer_instance

variable [Subsingleton (F.H' (n+1) U)] [Subsingleton (F.H' (n+1) V)]

/-- The actual connecting homomorphism is surjective when the next groups on
both opens vanish. -/
theorem mayerVietoris_delta_surjective :
    Function.Surjective ((Opens.mayerVietorisSquare U V).δ F n (n+1) rfl) := by
  let S := Opens.mayerVietorisSquare U V
  haveI : Subsingleton ((F.H' (n+1) S.X₂ ⊞ F.H' (n+1) S.X₃ : AddCommGrpCat.{1}) : Type 1) := by
    constructor
    intro x y
    apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    apply Prod.ext
    · exact @Subsingleton.elim (F.H' (n+1) U) inferInstance _ _
    · exact @Subsingleton.elim (F.H' (n+1) V) inferInstance _ _
  have he := ((S.sequence_exact F n (n+1) rfl).exact 2).ab_range_eq_ker
  change (S.δ F n (n+1) rfl).hom.range = (S.toBiprod F (n+1)).hom.ker at he
  intro x
  have hx : x ∈ (S.δ F n (n+1) rfl).hom.range := by
    rw [he]
    exact Subsingleton.elim _ _
  exact hx

/-- A real higher sheaf-cohomology comparison induced by the connecting map,
with every local vanishing hypothesis explicit. -/
noncomputable def mayerVietorisCokernelEquiv :
    mayerVietorisCokernel F U V n ≃+ F.H' (n+1) (U ⊔ V) := by
  let S := Opens.mayerVietorisSquare U V
  have he := ((S.sequence_exact F n (n+1) rfl).exact 1).ab_range_eq_ker
  change (S.fromBiprod F n).hom.range = (S.δ F n (n+1) rfl).hom.ker at he
  exact (QuotientAddGroup.quotientAddEquivOfEq he).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (S.δ F n (n+1) rfl).hom
      (mayerVietoris_delta_surjective F U V n))

end BPFixedPoints.SheafTools
