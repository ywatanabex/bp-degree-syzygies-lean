import BPFixedPoints.Incidence.IncidenceZeroBaseChangeTor

/-! # The base-changed Čech model computes the cohomology of the exterior bundles

For `j + p = q`, the cohomology `ZbcCohomology p q` of `ℂ ⊗_{S_G} K` in homological degree `p`
and internal degree `q` is identified with the actual (Ext-defined) sheaf cohomology
`H^j(X_G, ∧^q F_G^∨)` of the `q`-th exterior bundle on `X_G = (ℙ¹)^V` over `ℂ`
(`zbcSheafEquiv`). The isomorphism is a composite of three canonical steps; no state basis is
used to define it or to prove that it is bijective.

* **Decomposition into summands** (`zbcDecompositionEquiv`). After base change the Koszul part
  of the differential is zero, so the model is the direct sum over edge subsets `S` of the Čech
  complexes of `O(-d_S)`. In internal degree `q` only the `q`-element subsets occur, and the
  cohomology splits as the product over `S` of the Čech cohomology `ZbcTwistCohomology V (d_S) j`
  (cycles of Čech degree `j` modulo the image of Čech degree `j - 1`).
* **Čech cohomology of a summand is its sheaf cohomology** (`zbcTwistSheafEquiv`). In degree
  zero, the Čech cycles are the global sections through the existing chart restrictions
  (`vertexTwistGlobalZeroCycleEquiv`) and global sections are `H⁰`. In degree `m + 1`, the
  existing signed cell coefficients identify the cell cocycles and cell boundaries of the actual
  twist sheaf with the Čech cycles and boundaries (`zbcCellCyclesEquiv`, `zbcTwistCellEquiv`),
  and the existing comparison `vertexTwistCellActualLinearEquiv` identifies cell cohomology
  with actual cohomology. Both steps are linear for the geometric action.
* **Reassembly** through the biproduct decomposition of the exterior bundle
  (`exteriorBundleCohomologyLinearEquiv`).

`zbcTwistSheafEquiv_inclusion` records the value on the Čech class of the contraction inclusion
of a state: it is the class assigned to that state by the existing state comparison
`vertexTwistStateLinearEquiv`. This is the per-summand input of the normalization audit in
`IncidenceZeroBaseChangeNormalization`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CechProduct ProjectiveLine IncidencePerturbation Finsupp SheafTools.BinaryCells

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

section Twist

variable (V : Type) [Fintype V] [DecidableEq V]

/-- The Čech cycles of `O(-d)` over `ℂ` in Čech degree `j`. -/
def zbcTwistCycles (d : V → ℕ) (j : ℕ) : Submodule ℂ (CechProduct.C ℂ V) :=
  zbcCechPiece V (j : ℤ) ⊓ LinearMap.ker (CechProduct.contraction ℂ d).d

@[reducible] local instance zbcTwistCyclesAddCommGroup (d : V → ℕ) (j : ℕ) :
    AddCommGroup (zbcTwistCycles V d j) := (zbcTwistCycles V d j).addCommGroup

@[reducible] local instance zbcTwistCyclesModule (d : V → ℕ) (j : ℕ) :
    Module ℂ (zbcTwistCycles V d j) := (zbcTwistCycles V d j).module

@[reducible] local instance zbcCechPieceAddCommGroup (n : ℤ) :
    AddCommGroup (zbcCechPiece V n) := (zbcCechPiece V n).addCommGroup

@[reducible] local instance zbcCechPieceModule (n : ℤ) :
    Module ℂ (zbcCechPiece V n) := (zbcCechPiece V n).module

/-- The Čech differential of `O(-d)` from Čech degree `j - 1` into the cycles of degree `j`. -/
def zbcTwistBoundary (d : V → ℕ) (j : ℕ) : zbcCechPiece V ((j : ℤ) - 1) →ₗ[ℂ] zbcTwistCycles V d j :=
  ((CechProduct.contraction ℂ d).d.comp (zbcCechPiece V ((j : ℤ) - 1)).subtype).codRestrict _
    fun y => ⟨by
      have h := contraction_d_degree ℂ d _ y.val y.property
      rwa [sub_add_cancel] at h,
      LinearMap.congr_fun (CechProduct.contraction ℂ d).d_sq y.val⟩

@[simp] theorem zbcTwistBoundary_val (d : V → ℕ) (j : ℕ) (y : zbcCechPiece V ((j : ℤ) - 1)) :
    (zbcTwistBoundary V d j y).val = (CechProduct.contraction ℂ d).d y.val := rfl

/-- The Čech cohomology of `O(-d)` over `ℂ` in degree `j`, for the product of the standard
two-chart covers. -/
abbrev ZbcTwistCohomology (d : V → ℕ) (j : ℕ) :=
  zbcTwistCycles V d j ⧸ LinearMap.range (zbcTwistBoundary V d j)

/-- The class of a Čech cycle. -/
def zbcTwistClass (d : V → ℕ) (j : ℕ) : zbcTwistCycles V d j →ₗ[ℂ] ZbcTwistCohomology V d j :=
  (LinearMap.range (zbcTwistBoundary V d j)).mkQ

theorem zbcTwistClass_surjective (d : V → ℕ) (j : ℕ) :
    Function.Surjective (zbcTwistClass V d j) :=
  Submodule.mkQ_surjective _

theorem zbcTwistClass_eq_zero_iff (d : V → ℕ) (j : ℕ) (z : zbcTwistCycles V d j) :
    zbcTwistClass V d j z = 0 ↔
      ∃ y ∈ zbcCechPiece V ((j : ℤ) - 1), (CechProduct.contraction ℂ d).d y = z.val := by
  rw [zbcTwistClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy, hdy⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩

end Twist

section TwistSheaf

variable (V : Type) [Fintype V] [DecidableEq V]

local instance zbcTwistSheafHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

@[reducible] local instance zbcTwistSheafCyclesAddCommGroup (d : V → ℕ) (j : ℕ) :
    AddCommGroup (zbcTwistCycles V d j) := (zbcTwistCycles V d j).addCommGroup

@[reducible] local instance zbcTwistSheafCyclesModule (d : V → ℕ) (j : ℕ) :
    Module ℂ (zbcTwistCycles V d j) := (zbcTwistCycles V d j).module

@[reducible] local instance zbcTwistSheafPieceAddCommGroup (n : ℤ) :
    AddCommGroup (zbcCechPiece V n) := (zbcCechPiece V n).addCommGroup

@[reducible] local instance zbcTwistSheafPieceModule (n : ℤ) :
    Module ℂ (zbcCechPiece V n) := (zbcCechPiece V n).module

/-- The cell cocycles of the actual twist sheaf `O(-d)` are the Čech cycles over `ℂ`, through the
existing signed cell coefficients. -/
def zbcCellCyclesEquiv (d : V → ℕ) (m : ℕ) :
    vertexTwistCellCycles ℂ V d (m + 1) ≃+ zbcTwistCycles V d (m + 1) where
  toFun f := ⟨(vertexTwistCellCoefficientEquiv ℂ V d (m + 1) f.val).val,
    (vertexTwistCellCoefficientEquiv ℂ V d (m + 1) f.val).property,
    vertexTwistCellCycleCoefficient_closed ℂ V d (m + 1) f⟩
  invFun z := ⟨(vertexTwistCellCoefficientEquiv ℂ V d (m + 1)).symm ⟨z.val, z.property.1⟩, by
    apply (vertexTwistCellCoefficientEquiv ℂ V d (m + 1 + 1)).injective
    apply Subtype.ext
    rw [vertexTwistCellCoefficientEquiv_tower_d, map_zero, AddEquiv.apply_symm_apply]
    exact z.property.2⟩
  left_inv f := by
    apply Subtype.ext
    change (vertexTwistCellCoefficientEquiv ℂ V d (m + 1)).symm
      ⟨(vertexTwistCellCoefficientEquiv ℂ V d (m + 1) f.val).val, _⟩ = f.val
    rw [Subtype.coe_eta, AddEquiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    change ((vertexTwistCellCoefficientEquiv ℂ V d (m + 1))
      ((vertexTwistCellCoefficientEquiv ℂ V d (m + 1)).symm ⟨z.val, z.property.1⟩)).val = z.val
    rw [AddEquiv.apply_symm_apply]
  map_add' f g := by
    apply Subtype.ext
    change (vertexTwistCellCoefficientEquiv ℂ V d (m + 1) (f.val + g.val)).val = _
    rw [map_add]
    rfl

@[simp] theorem zbcCellCyclesEquiv_val (d : V → ℕ) (m : ℕ) (f : vertexTwistCellCycles ℂ V d (m + 1)) :
    (zbcCellCyclesEquiv V d m f).val = (vertexTwistCellCoefficientEquiv ℂ V d (m + 1) f.val).val :=
  rfl

/-- The geometric scalar action on cell cocycles is the scalar action on Čech cycles. -/
theorem zbcCellCyclesEquiv_scalar (d : V → ℕ) (m : ℕ) (c : ℂ)
    (f : vertexTwistCellCycles ℂ V d (m + 1)) :
    zbcCellCyclesEquiv V d m ((cubicalTower (vertexCoordinateOpen ℂ V)).mapCycles
      (SchemeTools.schemeBaseAbelianScalar (vertexToBase ℂ V)
        (vertexTwistSheaf ℂ V (fun v => -(d v : ℤ))) c) (m + 1) f) =
      c • zbcCellCyclesEquiv V d m f := by
  apply Subtype.ext
  change (vertexTwistCellCoefficientEquiv ℂ V d (m + 1) (f.val ≫ _)).val = c • _
  rw [vertexTwistCellCoefficientEquiv_postcomp_scalar]
  rfl

/-- The cell boundaries correspond to the Čech boundaries. -/
theorem zbcCellCyclesEquiv_boundary (d : V → ℕ) (m : ℕ)
    (g : sheafTerm (vertexCoordinateOpen ℂ V) m ⟶ vertexTwistAbelianSheaf ℂ V (fun v => -(d v : ℤ))) :
    (zbcCellCyclesEquiv V d m ((cubicalTower (vertexCoordinateOpen ℂ V)).boundary _ m g)).val =
      (CechProduct.contraction ℂ d).d (vertexTwistCellCoefficientEquiv ℂ V d m g).val :=
  vertexTwistCellCoefficientEquiv_tower_d ℂ V d m g

theorem zbcCechPiece_succ_sub_one (m : ℕ) :
    zbcCechPiece V (((m + 1 : ℕ) : ℤ) - 1) = zbcCechPiece V (m : ℤ) := by
  congr 1
  push_cast
  ring

/-- The Čech cohomology of `O(-d)` over `ℂ` in positive degree is the existing cubical cell
cohomology of the actual twist sheaf, linearly for the geometric action. -/
def zbcTwistCellEquiv (d : V → ℕ) (m : ℕ) :
    letI := vertexTwistCellModule ℂ V (fun v => -(d v : ℤ)) m
    ZbcTwistCohomology V d (m + 1) ≃ₗ[ℂ] vertexTwistCellCohomology ℂ V (fun v => -(d v : ℤ)) m := by
  letI := vertexTwistCellModule ℂ V (fun v => -(d v : ℤ)) m
  let e := zbcCellCyclesEquiv V d m
  let g : zbcTwistCycles V d (m + 1) →ₗ[ℂ] vertexTwistCellCohomology ℂ V (fun v => -(d v : ℤ)) m :=
    { toFun := fun z => QuotientAddGroup.mk (e.symm z)
      map_add' := fun z w => by rw [map_add]; rfl
      map_smul' := fun c z => by
        change QuotientAddGroup.mk (e.symm (c • z)) =
          QuotientAddGroup.mk ((cubicalTower (vertexCoordinateOpen ℂ V)).mapCycles
            (SchemeTools.schemeBaseAbelianScalar (vertexToBase ℂ V)
              (vertexTwistSheaf ℂ V (fun v => -(d v : ℤ))) c) (m + 1) (e.symm z))
        congr 1
        apply e.injective
        rw [AddEquiv.apply_symm_apply, zbcCellCyclesEquiv_scalar, AddEquiv.apply_symm_apply] }
  have hg : LinearMap.range (zbcTwistBoundary V d (m + 1)) ≤ LinearMap.ker g := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have hy : y.val ∈ supported ℂ ℂ {b : V → CechProduct.Basis | (cechDegree b : ℤ) = (m : ℤ)} := by
      rw [← zbcCechPiece, ← zbcCechPiece_succ_sub_one]
      exact y.property
    let g' := (vertexTwistCellCoefficientEquiv ℂ V d m).symm ⟨y.val, hy⟩
    have he : e.symm (zbcTwistBoundary V d (m + 1) y) =
        (cubicalTower (vertexCoordinateOpen ℂ V)).boundary _ m g' := by
      apply e.injective
      rw [AddEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [zbcCellCyclesEquiv_boundary, zbcTwistBoundary_val]
      simp only [g', AddEquiv.apply_symm_apply]
    change QuotientAddGroup.mk (e.symm (zbcTwistBoundary V d (m + 1) y)) = 0
    rw [he]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨g', rfl⟩
  let F := (LinearMap.range (zbcTwistBoundary V d (m + 1))).liftQ g hg
  let Ginv : vertexTwistCellCohomology ℂ V (fun v => -(d v : ℤ)) m →+ ZbcTwistCohomology V d (m + 1) :=
    QuotientAddGroup.lift _ ((zbcTwistClass V d (m + 1)).toAddMonoidHom.comp e.toAddMonoidHom) (by
      rintro _ ⟨g', rfl⟩
      change zbcTwistClass V d (m + 1) (e ((cubicalTower (vertexCoordinateOpen ℂ V)).boundary _ m g')) = 0
      rw [zbcTwistClass_eq_zero_iff]
      refine ⟨(vertexTwistCellCoefficientEquiv ℂ V d m g').val, ?_, ?_⟩
      · rw [zbcCechPiece_succ_sub_one]
        exact (vertexTwistCellCoefficientEquiv ℂ V d m g').property
      · rw [zbcCellCyclesEquiv_boundary])
  exact
    { F with
      invFun := Ginv
      left_inv := fun c => by
        obtain ⟨z, rfl⟩ := zbcTwistClass_surjective V d (m + 1) c
        change Ginv (F (Submodule.Quotient.mk z)) = zbcTwistClass V d (m + 1) z
        rw [Submodule.liftQ_apply]
        change zbcTwistClass V d (m + 1) (e (e.symm z)) = _
        rw [AddEquiv.apply_symm_apply]
      right_inv := fun c => by
        induction c using QuotientAddGroup.induction_on with
        | _ f =>
          change F (zbcTwistClass V d (m + 1) (e f)) = QuotientAddGroup.mk f
          change g (e f) = _
          change QuotientAddGroup.mk (e.symm (e f)) = _
          rw [AddEquiv.symm_apply_apply] }

theorem zbcTwistBoundary_zero_range (d : V → ℕ) :
    LinearMap.range (zbcTwistBoundary V d 0) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  apply LinearMap.ext
  intro y
  have hy : y = 0 := by
    apply Subtype.ext
    ext b
    apply (mem_supported' ℂ y.val).mp y.property b
    change ¬ ((cechDegree b : ℤ) = ((0 : ℕ) : ℤ) - 1)
    omega
  rw [hy, map_zero, LinearMap.zero_apply]

theorem zbcTwistCycles_zero (d : V → ℕ) : zbcTwistCycles V d 0 = zeroCycleModule ℂ d := rfl

/-- The Čech cohomology of `O(-d)` over `ℂ` in degree zero is the actual `H⁰`, through the
existing chart restrictions of global sections. -/
def zbcTwistSheafEquivZero (d : V → ℕ) :
    letI := vertexTwistH0BaseModule ℂ V d
    ZbcTwistCohomology V d 0 ≃ₗ[ℂ] (vertexTwistAbelianSheaf ℂ V (fun v => -(d v : ℤ))).H 0 :=
  letI := vertexTwistH0BaseModule ℂ V d
  ((Submodule.quotEquivOfEqBot _ (zbcTwistBoundary_zero_range V d)).trans
    (LinearEquiv.ofEq _ _ (zbcTwistCycles_zero V d))).trans
    ((vertexTwistGlobalZeroCycleEquiv ℂ V d).symm.trans (vertexTwistH0SectionsLinearEquiv ℂ V d).symm)

/-- **Čech cohomology of a summand is its actual sheaf cohomology.** For every twist `d` and
degree `j`, the Čech cohomology over `ℂ` of `O(-d)` on the product of the standard two-chart
covers is the actual (Ext-defined) sheaf cohomology `H^j(O(-d))`, linearly for the geometric
action: in degree zero through global sections, in positive degree through the existing cubical
cell comparison. -/
def zbcTwistSheafEquiv (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule ℂ V d j
    ZbcTwistCohomology V d j ≃ₗ[ℂ] (vertexTwistAbelianSheaf ℂ V (fun v => -(d v : ℤ))).H j := by
  cases j with
  | zero => exact zbcTwistSheafEquivZero V d
  | succ m =>
    letI := vertexTwistCellModule ℂ V (fun v => -(d v : ℤ)) m
    exact (zbcTwistCellEquiv V d m).trans (vertexTwistCellActualLinearEquiv ℂ V _ m)

/-- The Čech inclusion of a state of degree `j` is a Čech cycle of degree `j`. -/
def zbcTwistInclusion (d : V → ℕ) (j : ℕ) : stateDegreePiece ℂ d j →ₗ[ℂ] zbcTwistCycles V d j :=
  ((CechProduct.contraction ℂ d).i.comp (stateDegreePiece ℂ d j).subtype).codRestrict _ fun s => by
    refine ⟨?_, LinearMap.congr_fun (CechProduct.contraction ℂ d).d_i s.val⟩
    have h := contraction_i_degree ℂ d (j : ℤ) s.val s.property
    rw [add_zero] at h
    exact h

@[simp] theorem zbcTwistInclusion_val (d : V → ℕ) (j : ℕ) (s : stateDegreePiece ℂ d j) :
    (zbcTwistInclusion V d j s).val = (CechProduct.contraction ℂ d).i s.val := rfl

/-- **The per-summand normalization.** The Čech-to-sheaf comparison sends the Čech class of the
contraction inclusion of a state to the actual cohomology class that the existing state comparison
assigns to that state, in every degree. -/
theorem zbcTwistSheafEquiv_inclusion (d : V → ℕ) (j : ℕ) (s : stateDegreePiece ℂ d j) :
    letI := vertexTwistStateCohomologyModule ℂ V d j
    zbcTwistSheafEquiv V d j (zbcTwistClass V d j (zbcTwistInclusion V d j s)) =
      (vertexTwistStateLinearEquiv ℂ V d j).symm s := by
  cases j with
  | zero => rfl
  | succ m =>
    let _ := vertexTwistStateCohomologyModule ℂ V d (m + 1)
    let _ := vertexTwistCellModule ℂ V (fun v => -(d v : ℤ)) m
    change vertexTwistCellActualLinearEquiv ℂ V _ m
        (QuotientAddGroup.mk ((zbcCellCyclesEquiv V d m).symm (zbcTwistInclusion V d (m + 1) s))) =
      (vertexTwistPositiveStateLinearEquiv ℂ V d m).symm s
    rw [vertexTwistPositiveStateLinearEquiv_inverse]
    congr 2

end TwistSheaf

section Decomposition

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

@[reducible] local instance zbcSheafCyclesAddCommGroup (p q : ℕ) : AddCommGroup (G.zbcCycles p q) :=
  (G.zbcCycles p q).addCommGroup

@[reducible] local instance zbcSheafCyclesModule (p q : ℕ) : Module ℂ (G.zbcCycles p q) :=
  (G.zbcCycles p q).module

@[reducible] local instance zbcSheafPieceAddCommGroup (p q : ℕ) : AddCommGroup (zbcPiece V E p q) :=
  (zbcPiece V E p q).addCommGroup

@[reducible] local instance zbcSheafPieceModule (p q : ℕ) : Module ℂ (zbcPiece V E p q) :=
  (zbcPiece V E p q).module

@[reducible] local instance zbcSheafTwistCyclesAddCommGroup (d : V → ℕ) (j : ℕ) :
    AddCommGroup (zbcTwistCycles V d j) := (zbcTwistCycles V d j).addCommGroup

@[reducible] local instance zbcSheafTwistCyclesModule (d : V → ℕ) (j : ℕ) :
    Module ℂ (zbcTwistCycles V d j) := (zbcTwistCycles V d j).module

theorem zbcSlot_of_card {p q j : ℕ} (hj : j + p = q) {S : Finset E} (hS : S.card = q) :
    zbcSlot V p q S = zbcCechPiece V (j : ℤ) := by
  rw [zbcSlot, ite_eq_left hS]
  congr 1
  omega

theorem zbcSlot_succ_of_card {p q j : ℕ} (hj : j + p = q) {S : Finset E} (hS : S.card = q) :
    zbcSlot V (p + 1) q S = zbcCechPiece V ((j : ℤ) - 1) := by
  rw [zbcSlot, ite_eq_left hS]
  congr 1
  omega

/-- The component at a `q`-element edge subset of a sum of single components. -/
theorem zbc_sum_single_apply {M : Type*} [AddCommMonoid M] {q : ℕ} (w : Set.powersetCard E q → M)
    (T : Finset E) :
    (∑ S : Set.powersetCard E q, Finsupp.single (S : Finset E) (w S)) T =
      if h : T.card = q then w ⟨T, h⟩ else 0 := by
  rw [Finset.sum_apply']
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨T, h⟩ : Set.powersetCard E q)]
    · exact Finsupp.single_eq_same
    · intro S _ hS
      apply Finsupp.single_eq_of_ne
      intro hST
      exact hS (Subtype.ext hST.symm)
    · intro hT
      exact absurd (Finset.mem_univ _) hT
  · apply Finset.sum_eq_zero
    intro S _
    apply Finsupp.single_eq_of_ne
    intro hST
    exact h (hST ▸ Set.powersetCard.card_eq S)

/-- The component at a `q`-element edge subset of a cycle of bidegree `(p, q)`, with `j + p = q`. -/
def zbcComponent {p q j : ℕ} (hj : j + p = q) (S : Set.powersetCard E q) :
    G.zbcCycles p q →ₗ[ℂ] zbcTwistCycles V (G.deg (S : Finset E)) j :=
  ((Finsupp.lapply (S : Finset E)).comp (G.zbcCycles p q).subtype).codRestrict _ fun z => by
    refine ⟨?_, ?_⟩
    · have h := ((mem_zbcSlot_iff p q (S : Finset E) (z.val (S : Finset E))).mp
        (z.property.1 (S : Finset E))).1 (Set.powersetCard.card_eq S)
      have he : (q : ℤ) - p = j := by omega
      rw [he] at h
      exact h
    · have h := congrArg (fun w : ZbcModule V E => w (S : Finset E)) z.property.2
      simp only [zbcContraction_d_apply, Finsupp.zero_apply] at h
      exact h

@[simp] theorem zbcComponent_val {p q j : ℕ} (hj : j + p = q) (S : Set.powersetCard E q)
    (z : G.zbcCycles p q) : (G.zbcComponent hj S z).val = z.val (S : Finset E) := rfl

/-- The componentwise classes of a cycle. -/
def zbcComponentClasses {p q j : ℕ} (hj : j + p = q) :
    G.zbcCycles p q →ₗ[ℂ] ((S : Set.powersetCard E q) →
      ZbcTwistCohomology V (G.deg (S : Finset E)) j) :=
  LinearMap.pi fun S => (zbcTwistClass V (G.deg (S : Finset E)) j).comp (G.zbcComponent hj S)

/-- The decomposition of the cohomology of the base-changed model in bidegree `(p, q)` into the
Čech cohomology of the summands `O(-d_S)`, `|S| = q`, in degree `j = q - p`. -/
def zbcDecomposition {p q j : ℕ} (hj : j + p = q) :
    G.ZbcCohomology p q →ₗ[ℂ] ((S : Set.powersetCard E q) →
      ZbcTwistCohomology V (G.deg (S : Finset E)) j) :=
  G.zbcLift p q (G.zbcComponentClasses hj) fun y => by
    funext S
    change zbcTwistClass V _ j (G.zbcComponent hj S (G.zbcBoundary p q y)) = 0
    rw [zbcTwistClass_eq_zero_iff]
    refine ⟨y.val (S : Finset E), ?_, ?_⟩
    · have h := ((mem_zbcSlot_iff (p + 1) q (S : Finset E) (y.val (S : Finset E))).mp
        (y.property (S : Finset E))).1 (Set.powersetCard.card_eq S)
      have he : (q : ℤ) - ((p + 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by push_cast; omega
      rw [he] at h
      exact h
    · rfl

theorem zbcDecomposition_class {p q j : ℕ} (hj : j + p = q) (z : G.zbcCycles p q)
    (S : Set.powersetCard E q) :
    G.zbcDecomposition hj (G.zbcClass p q z) S =
      zbcTwistClass V (G.deg (S : Finset E)) j (G.zbcComponent hj S z) := rfl

theorem zbcDecomposition_injective {p q j : ℕ} (hj : j + p = q) :
    Function.Injective (G.zbcDecomposition hj) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  obtain ⟨z, rfl⟩ := G.zbcClass_surjective p q c
  have hS : ∀ S : Set.powersetCard E q, ∃ y ∈ zbcCechPiece V ((j : ℤ) - 1),
      (CechProduct.contraction ℂ (G.deg (S : Finset E))).d y = z.val (S : Finset E) := fun S =>
    (zbcTwistClass_eq_zero_iff V _ j _).mp (congrFun hc S)
  choose y hy hdy using hS
  rw [zbcClass_eq_zero_iff]
  refine ⟨∑ S : Set.powersetCard E q, Finsupp.single (S : Finset E) (y S), ?_, ?_⟩
  · intro T
    rw [zbc_sum_single_apply, mem_zbcSlot_iff]
    split_ifs with hT
    · refine ⟨fun _ => ?_, fun h => absurd hT h⟩
      have he : (q : ℤ) - ((p + 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by push_cast; omega
      rw [he]
      exact hy ⟨T, hT⟩
    · exact ⟨fun h => absurd h hT, fun _ => rfl⟩
  · ext T : 1
    rw [zbcContraction_d_apply, zbc_sum_single_apply]
    split_ifs with hT
    · exact hdy ⟨T, hT⟩
    · rw [map_zero]
      exact (((mem_zbcSlot_iff p q T (z.val T)).mp (z.property.1 T)).2 hT).symm

theorem zbcDecomposition_surjective {p q j : ℕ} (hj : j + p = q) :
    Function.Surjective (G.zbcDecomposition hj) := by
  intro c
  have hS : ∀ S : Set.powersetCard E q, ∃ w : zbcTwistCycles V (G.deg (S : Finset E)) j,
      zbcTwistClass V _ j w = c S := fun S => zbcTwistClass_surjective V _ j (c S)
  choose w hw using hS
  have hz : (∑ S : Set.powersetCard E q, Finsupp.single (S : Finset E) (w S).val) ∈
      G.zbcCycles p q := by
    refine ⟨fun T => ?_, ?_⟩
    · rw [zbc_sum_single_apply, mem_zbcSlot_iff]
      split_ifs with hT
      · refine ⟨fun _ => ?_, fun h => absurd hT h⟩
        have h := (w ⟨T, hT⟩).property.1
        have he : (j : ℤ) = (q : ℤ) - p := by omega
        rw [he] at h
        exact h
      · exact ⟨fun h => absurd h hT, fun _ => rfl⟩
    · change G.zbcContraction.d
        (∑ S : Set.powersetCard E q, Finsupp.single (S : Finset E) (w S).val) = 0
      ext T : 1
      rw [zbcContraction_d_apply, zbc_sum_single_apply, Finsupp.zero_apply]
      split_ifs with hT
      · exact (w ⟨T, hT⟩).property.2
      · exact map_zero _
  refine ⟨G.zbcClass p q ⟨_, hz⟩, ?_⟩
  funext S
  rw [zbcDecomposition_class, ← hw S]
  congr 1
  apply Subtype.ext
  rw [zbcComponent_val]
  change (∑ S : Set.powersetCard E q, Finsupp.single (S : Finset E) (w S).val) (S : Finset E) = _
  rw [zbc_sum_single_apply, dite_eq_left (Set.powersetCard.card_eq S)]

/-- The decomposition is an isomorphism. -/
def zbcDecompositionEquiv {p q j : ℕ} (hj : j + p = q) :
    G.ZbcCohomology p q ≃ₗ[ℂ] ((S : Set.powersetCard E q) →
      ZbcTwistCohomology V (G.deg (S : Finset E)) j) :=
  LinearEquiv.ofBijective (G.zbcDecomposition hj)
    ⟨G.zbcDecomposition_injective hj, G.zbcDecomposition_surjective hj⟩

local instance zbcSheafExteriorHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **The cohomology of the base-changed model is the actual sheaf cohomology of the exterior
bundle.** For `j + p = q`, the cohomology of `ℂ ⊗_{S_G} K` in homological degree `p` and internal
degree `q` is `H^j(X_G, ∧^q F_G^∨)`: decompose into the summands `O(-d_S)`, `|S| = q`, compare
their Čech cohomology with their actual cohomology, and reassemble through the biproduct. -/
def zbcSheafEquiv {p q j : ℕ} (hj : j + p = q) :
    letI := G.exteriorBundleCohomologyModule ℂ q j
    G.ZbcCohomology p q ≃ₗ[ℂ] Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j :=
  letI := G.exteriorBundleCohomologyModule ℂ q j
  letI := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule ℂ V (G.deg S) j
  (G.zbcDecompositionEquiv hj).trans
    ((LinearEquiv.piCongrRight fun S : Set.powersetCard E q =>
      zbcTwistSheafEquiv V (G.deg (S : Finset E)) j).trans
      (G.exteriorBundleCohomologyLinearEquiv ℂ q j).symm)

theorem zbcSheafEquiv_class {p q j : ℕ} (hj : j + p = q) (z : G.zbcCycles p q) :
    letI := G.exteriorBundleCohomologyModule ℂ q j
    letI := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule ℂ V (G.deg S) j
    G.zbcSheafEquiv hj (G.zbcClass p q z) =
      (G.exteriorBundleCohomologyLinearEquiv ℂ q j).symm fun S : Set.powersetCard E q =>
        zbcTwistSheafEquiv V (G.deg (S : Finset E)) j
          (zbcTwistClass V (G.deg (S : Finset E)) j (G.zbcComponent hj S z)) := rfl

end Decomposition

end

end BPFixedPoints.Multigraph
