import BPFixedPoints.Incidence.SheafMayerVietorisQuotient
import Mathlib.Order.Fin.Basic

/-! # Actual cohomology above the number of binary cover directions

The proof iterates the native Mayer--Vietoris connecting map. It uses the
actual local Ext groups on every rectangular face, including overlaps.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {T : Type} [TopologicalSpace T]

/-- The original left, right and overlap open for one cover direction. -/
def binaryCoverFaceFactor (U : Fin 2 → Opens T) (q : Fin 3) : Opens T :=
  if q = 0 then U 0 else if q = 1 then U 1 else U 0 ⊓ U 1

/-- The actual rectangular open for a family of original binary cover directions. -/
def binaryCoverFaceOpen {ι : Sort*} (U : ι → Fin 2 → Opens T) (q : ι → Fin 3) : Opens T :=
  ⨅ i, binaryCoverFaceFactor (U i) (q i)

/-- Reindex the original rectangular open along an equivalence. -/
theorem binaryCoverFaceOpen_reindex {ι κ : Type*} (e : ι ≃ κ)
    (U : ι → Fin 2 → Opens T) (q : κ → Fin 3) :
    binaryCoverFaceOpen (fun j => U (e.symm j)) q =
      binaryCoverFaceOpen U (fun i => q (e i)) := by
  unfold binaryCoverFaceOpen
  apply le_antisymm
  · apply le_iInf
    intro i
    simpa only [e.symm_apply_apply] using
      (iInf_le (fun j => binaryCoverFaceFactor (U (e.symm j)) (q j)) (e i))
  · apply le_iInf
    intro j
    simpa only [e.apply_symm_apply] using
      (iInf_le (fun i => binaryCoverFaceFactor (U i) (q (e i))) (e.symm j))

/-- Split off the first original cover direction. -/
theorem binaryCoverFaceOpen_cons {n : ℕ} (U : Fin (n+1) → Fin 2 → Opens T)
    (q₀ : Fin 3) (q : Fin n → Fin 3) :
    binaryCoverFaceOpen U (Fin.cons q₀ q) =
      binaryCoverFaceFactor (U 0) q₀ ⊓ binaryCoverFaceOpen (fun i => U i.succ) q := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)
  · apply le_iInf
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact inf_le_left
    · exact inf_le_right.trans (iInf_le _ j)

noncomputable local instance binaryCoverHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- Vanishing of the actual native local Ext group, with its original degree and open. -/
def localSheafCohomologyVanishes
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) (U : Opens T) : Prop :=
  ∀ x : F.H' n U, x = 0

/-- Actual local Ext vanishes above the number of binary directions when all rectangular faces are acyclic. -/
theorem sheaf_cohomology_binaryCover_bound
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :
    ∀ (U : Fin n → Fin 2 → Opens T), (∀ i, U i 0 ⊔ U i 1 = ⊤) →
    ∀ (W : Opens T),
    (∀ q k, localSheafCohomologyVanishes F (k+1) (W ⊓ binaryCoverFaceOpen U q)) →
    ∀ k, localSheafCohomologyVanishes F (n+k+1) W := by
  induction n with
  | zero =>
      intro U hU W hF k
      simpa only [binaryCoverFaceOpen, iInf_of_empty, inf_top_eq, Nat.zero_add]
        using hF (fun i => Fin.elim0 i) k
  | succ n ih =>
      intro U hU W hF k
      rw [show n+1+k+1 = n+k+1+1 by omega]
      intro x
      let A := W ⊓ U 0 0
      let B := W ⊓ U 0 1
      let D : Fin n → Fin 2 → Opens T := fun i => U i.succ
      have hD i : D i 0 ⊔ D i 1 = ⊤ := hU i.succ
      have hA q j : localSheafCohomologyVanishes F (j+1) (A ⊓ binaryCoverFaceOpen D q) := by
        simpa [binaryCoverFaceOpen_cons, binaryCoverFaceFactor, A, D, inf_assoc]
          using hF (Fin.cons 0 q) j
      have hB q j : localSheafCohomologyVanishes F (j+1) (B ⊓ binaryCoverFaceOpen D q) := by
        simpa [binaryCoverFaceOpen_cons, binaryCoverFaceFactor, B, D, inf_assoc]
          using hF (Fin.cons 1 q) j
      have hAB q j : localSheafCohomologyVanishes F (j+1) ((A ⊓ B) ⊓ binaryCoverFaceOpen D q) := by
        simpa [binaryCoverFaceOpen_cons, binaryCoverFaceFactor, A, B, D,
          inf_assoc, inf_left_comm, inf_comm] using hF (Fin.cons 2 q) j
      have hAu := ih D hD A hA (k+1)
      have hBu := ih D hD B hB (k+1)
      have : Subsingleton (F.H' (n+k+1+1) A) :=
        subsingleton_of_forall_eq 0 (show localSheafCohomologyVanishes F (n+k+1+1) A from
          by simpa only [Nat.add_assoc] using hAu)
      have : Subsingleton (F.H' (n+k+1+1) B) :=
        subsingleton_of_forall_eq 0 (show localSheafCohomologyVanishes F (n+k+1+1) B from
          by simpa only [Nat.add_assoc] using hBu)
      have hc : A ⊔ B = W := by
        dsimp only [A, B]
        rw [← inf_sup_left, hU 0, inf_top_eq]
      let hx := (F.cohomologyPresheaf (n+k+1+1)).map (eqToHom hc).op x
      obtain ⟨z, hz⟩ := mayerVietoris_delta_surjective F A B (n+k+1) hx
      have hz0 : z = 0 := ih D hD (A ⊓ B) hAB k z
      rw [hz0, map_zero] at hz
      apply (ConcreteCategory.bijective_of_isIso
        ((F.cohomologyPresheaf (n+k+1+1)).map (eqToHom hc).op)).injective
      simpa only [hx, map_zero] using hz.symm

/-- The binary-cover bound retains the original finite labels, including the empty index set. -/
theorem sheaf_cohomology_finiteBinaryCover_bound
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    {V : Type} [Fintype V] (U : V → Fin 2 → Opens T)
    (hU : ∀ v, U v 0 ⊔ U v 1 = ⊤) (W : Opens T)
    (hF : ∀ q k, localSheafCohomologyVanishes F (k+1) (W ⊓ binaryCoverFaceOpen U q))
    (k : ℕ) : localSheafCohomologyVanishes F (Fintype.card V+k+1) W := by
  let e := Fintype.equivFin V
  apply sheaf_cohomology_binaryCover_bound F (Fintype.card V)
    (fun i => U (e.symm i)) (fun i => hU (e.symm i)) W
  intro q j
  rw [binaryCoverFaceOpen_reindex e]
  exact hF _ j

end BPFixedPoints.SheafTools
