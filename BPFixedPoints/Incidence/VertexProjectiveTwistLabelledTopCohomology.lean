import BPFixedPoints.Incidence.VertexProjectiveTwistTopLinear

/-! # The original top-cohomology quotient in arbitrary finite vertex labels

The chosen pivot vertex is removed only from the cover index. The original
projective product, sheaf, structural morphism and cohomology groups are retained.
-/

namespace BPFixedPoints.SheafTools
open TopologicalSpace

/-- Fixing one original cover direction identifies its remaining rectangular faces. -/
theorem binaryCoverFaceOpen_pivot {T V : Type} [TopologicalSpace T] [DecidableEq V]
    (U : V → Fin 2 → Opens T) (v : V) (b : Fin 2) (q : {w : V // w ≠ v} → Fin 3) :
    binaryCoverFaceOpen U (fun w => if h : w = v then b.castSucc else q ⟨w,h⟩) =
      U v b ⊓ binaryCoverFaceOpen (fun w : {w : V // w ≠ v} => U w.1) q := by
  let p : V → Fin 3 := fun w => if h : w = v then b.castSucc else q ⟨w,h⟩
  have hpv : p v = b.castSucc := dif_pos rfl
  have hpw (w : {w : V // w ≠ v}) : p w.1 = q w := dif_neg w.property
  have hb : binaryCoverFaceFactor (U v) b.castSucc = U v b := by
    fin_cases b <;> simp [binaryCoverFaceFactor]
  change (⨅ w, binaryCoverFaceFactor (U w) (p w)) =
    U v b ⊓ ⨅ w : {w : V // w ≠ v}, binaryCoverFaceFactor (U w.1) (q w)
  apply le_antisymm
  · apply le_inf
    · simpa only [hpv, hb] using iInf_le (fun w => binaryCoverFaceFactor (U w) (p w)) v
    · apply le_iInf
      intro w
      simpa only [hpw] using iInf_le (fun w => binaryCoverFaceFactor (U w) (p w)) w.1
  · apply le_iInf
    intro w
    by_cases hw : w = v
    · subst w
      simpa only [hpv, hb] using
        (inf_le_left : U v b ⊓ (⨅ w : {w : V // w ≠ v}, binaryCoverFaceFactor (U w.1) (q w)) ≤ U v b)
    · have hh : binaryCoverFaceFactor (U w) (q ⟨w,hw⟩) = binaryCoverFaceFactor (U w) (p w) :=
        congrArg (binaryCoverFaceFactor (U w)) (hpw ⟨w,hw⟩).symm
      exact inf_le_right.trans ((iInf_le _ ⟨w,hw⟩).trans_eq hh)

end BPFixedPoints.SheafTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] [IsNoetherianRing R] (V : Type) [Fintype V]
noncomputable local instance vertexLabelledTopHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Fixing a chosen original vertex pivot leaves the remaining directions in the actual Ext bound. -/
theorem vertexTwistSheaf_pivotOpen_higher_eq_zero (a : V → ℤ) (v : V) (b : Fin 2)
    (n : ℕ) (hV : Fintype.card V = n+1) (k : ℕ)
    (x : (vertexTwistAbelianSheaf R V a).H' (n+k+1) (vertexCoordinateOpen R V v b)) : x = 0 := by
  classical
  have hc : Fintype.card {w : V // w ≠ v} = n := by
    rw [Fintype.card_subtype_compl (fun w : V => w = v), Fintype.card_subtype_eq, hV]
    omega
  have hfaces q j : SheafTools.localSheafCohomologyVanishes (vertexTwistAbelianSheaf R V a) (j+1)
      (vertexCoordinateOpen R V v b ⊓
        SheafTools.binaryCoverFaceOpen (fun w : {w : V // w ≠ v} => vertexCoordinateOpen R V w.1) q) := by
    rw [← SheafTools.binaryCoverFaceOpen_pivot]
    exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero _ _
      (vertexBinaryFaceOpen_isAffine R V _) (vertexTwistSheaf R V a) j
  have h := SheafTools.sheaf_cohomology_finiteBinaryCover_bound (vertexTwistAbelianSheaf R V a)
    (fun w : {w : V // w ≠ v} => vertexCoordinateOpen R V w.1)
    (fun w => vertexCoordinateOpen_cover R V w.1) (vertexCoordinateOpen R V v b) hfaces k
  rw [hc] at h
  exact h x

/-- The original top global cohomology is the original restriction cokernel in the original vertex labels. -/
noncomputable def vertexTwistSheafTopCokernelEquivAtVertex (a : V → ℤ) (v : V)
    (n : ℕ) (hV : Fintype.card V = n+1) :
    SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R V a)
      (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n ≃+
        (vertexTwistAbelianSheaf R V a).H (n+1) := by
  let F := vertexTwistAbelianSheaf R V a
  let A := vertexCoordinateOpen R V v 0
  let B := vertexCoordinateOpen R V v 1
  let : Subsingleton (F.H' (n+1) A) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_pivotOpen_higher_eq_zero R V a v 0 n hV 0)
  let : Subsingleton (F.H' (n+1) B) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_pivotOpen_higher_eq_zero R V a v 1 n hV 0)
  exact SheafTools.mayerVietorisGlobalCokernelEquiv F A B (vertexCoordinateOpen_cover R V v) n

/-- The original top quotient comparison preserves the original geometric base action in arbitrary labels. -/
noncomputable def vertexTwistSheafTopCokernelLinearEquivAtVertex (a : V → ℤ) (v : V)
    (n : ℕ) (hV : Fintype.card V = n+1) :
    letI : Module R (SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R V a)
      (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n) :=
      SchemeTools.schemeBaseMayerVietorisCokernelModule (vertexToBase R V) (vertexTwistSheaf R V a)
        (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n
    letI : Module R ((vertexTwistAbelianSheaf R V a).H (n+1)) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (n+1)
    SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R V a)
      (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n ≃ₗ[R]
        (vertexTwistAbelianSheaf R V a).H (n+1) := by
  letI : Module R (SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R V a)
    (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n) :=
    SchemeTools.schemeBaseMayerVietorisCokernelModule (vertexToBase R V) (vertexTwistSheaf R V a)
      (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) n
  letI : Module R ((vertexTwistAbelianSheaf R V a).H (n+1)) :=
    SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (n+1)
  refine { vertexTwistSheafTopCokernelEquivAtVertex R V a v n hV with map_smul' := ?_ }
  intro r x
  refine Quotient.inductionOn' x (fun y => ?_)
  let A := vertexCoordinateOpen R V v 0
  let B := vertexCoordinateOpen R V v 1
  letI : Module R ((vertexTwistAbelianSheaf R V a).H' n (A ⊓ B)) :=
    SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (A ⊓ B) n
  let z : (vertexTwistAbelianSheaf R V a).H' n (A ⊓ B) := y
  change vertexTwistSheafTopCokernelEquivAtVertex R V a v n hV (QuotientAddGroup.mk (r • z)) =
    r • vertexTwistSheafTopCokernelEquivAtVertex R V a v n hV (QuotientAddGroup.mk z)
  change SheafTools.mayerVietorisGlobalConnecting _ A B (vertexCoordinateOpen_cover R V v) n (r • z) =
    r • SheafTools.mayerVietorisGlobalConnecting _ A B (vertexCoordinateOpen_cover R V v) n z
  exact SchemeTools.schemeBaseGlobalConnecting_smul (vertexToBase R V) (vertexTwistSheaf R V a)
    A B (vertexCoordinateOpen_cover R V v) n r z

/-- Every original quotient representative maps to the native global connecting class, in the original labels. -/
theorem vertexTwistSheafTopCokernelLinearEquivAtVertex_mk (a : V → ℤ) (v : V)
    (n : ℕ) (hV : Fintype.card V = n+1)
    (x : (vertexTwistAbelianSheaf R V a).H' n (vertexCoordinateOpen R V v 0 ⊓ vertexCoordinateOpen R V v 1)) :
    vertexTwistSheafTopCokernelLinearEquivAtVertex R V a v n hV (QuotientAddGroup.mk x) =
      SheafTools.mayerVietorisGlobalConnecting (vertexTwistAbelianSheaf R V a)
        (vertexCoordinateOpen R V v 0) (vertexCoordinateOpen R V v 1) (vertexCoordinateOpen_cover R V v) n x := rfl

/-- On the original Fin labels and first pivot, the extended comparison is the previous specified map. -/
theorem vertexTwistSheafTopCokernelLinearEquivAtVertex_fin (n : ℕ) (a : Fin (n+1) → ℤ)
    (h : Fintype.card (Fin (n+1)) = n+1)
    (x : SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
      (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n) :
    vertexTwistSheafTopCokernelLinearEquivAtVertex R (Fin (n+1)) a 0 n h x =
      vertexTwistSheafTopCokernelLinearEquiv R n a x := by
  refine Quotient.inductionOn' x (fun y => ?_)
  rw [vertexTwistSheafTopCokernelLinearEquivAtVertex_mk, vertexTwistSheafTopCokernelLinearEquiv_mk]

end BPFixedPoints.ProjectiveLine
