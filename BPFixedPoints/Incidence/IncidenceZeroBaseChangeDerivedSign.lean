import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedHypercohomology
import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedComplex

/-! # The sign-corrected chain isomorphism from the Hom complex to the Čech–Koszul complex

`IncidenceUniversalKoszulDerivedCech` compares the Hom complex from the negative cubical cell
resolution `P` of `ℤ` to `K_G` with the Čech–Koszul total complex by `Φ_m = cechOfCochain m`
(which already contains the totalization sign `koszulTotSign`), and proves
`Φ_{m+1}(δ z) = (-1)^{m+1} D(Φ_m z)` (`cechOfCochain_δ`). That is not a chain map. This file
corrects it by a second, independent sign depending only on the cohomological degree.

* **The sign** `zbdTotSign m = t_m = (-1)^{m(m+1)/2}` for `m ∈ ℤ`, defined with
  `Int.negOnePow`. `zbdTotSign_zero : t_0 = 1` and the integer recursion
  `zbdTotSign_succ : t_{m+1} = (-1)^{m+1} t_m` (no natural-number subtraction).
* **The chain isomorphism.** `zbdUnivGraded` grades the Čech–Koszul module of `K_G` by
  cohomological degree (`univCechKoszulPiece (-m)`), and `zbdCechAbComplex` is the resulting
  cochain complex of abelian groups. `Ψ_m = t_m Φ_m` (`zbdCechHom`) is bijective onto the piece
  (`cechOfCochain_injective`, `cechOfCochain_cochainOfCech`) and satisfies
  `Ψ_{m+1} δ = D Ψ_m` (`zbdCechHom_δ`, from `cechOfCochain_δ` and
  `t_{m+1} (-1)^{m+1} = t_m`). `zbdHomCechIso : HomComplex P K_G ≅ zbdCechAbComplex` is the
  isomorphism of cochain complexes built with `HomologicalComplex.Hom.isoOfComponents`.
  `koszulTotSign` is not applied again: it is only inside `Φ`.
* **Link with the derived base change.** `zbdUnivTotalIso` identifies the graded Čech–Koszul
  complex of `K_G` with the complex `C` of `IncidenceZeroBaseChangeDerivedComplex` through
  `univCechKoszulEquiv`; `zbdHomTotalIso` composes both.
* **Cohomology.** Through Mathlib's identification `homologyAddEquiv` of the homology of
  `HomComplex` with `CohomologyClass` (the domain of `incUniversalKoszulHypercohomologyEquiv`), the
  induced map sends the class of a cocycle `z` to the class of any cycle with underlying element
  `t_n Φ_n z` (`zbdHomCechIso_homology_class`). In degree zero `Ψ_0` is the existing cycle
  comparison `cocycleZeroToCycles` (`zbdCechHom_zero_cocycle`), and the augmentation
  `cohomologyClassZeroAugmentation` of a class is `univCechKoszulAugmentation` of any cycle in
  the image class (`zbdHomCechIso_augmentation`, using the existing boundary criterion
  `univCechKoszulAugmentation_eq_zero_iff`).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CechProduct ProjectiveLine SheafTools SheafTools.BinaryCells ExtResolutionTools ResolutionTools
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

/-! ### The sign `t_m = (-1)^{m(m+1)/2}` -/

/-- The sign `t_m = (-1)^{m(m+1)/2}` for `m ∈ ℤ`. -/
def zbdTotSign (m : ℤ) : ℤˣ := (m * (m + 1) / 2).negOnePow

theorem zbdTotSign_zero : zbdTotSign 0 = 1 := by
  simp [zbdTotSign]

/-- The recursion `t_{m+1} = (-1)^{m+1} t_m`, over the integers. -/
theorem zbdTotSign_succ (m : ℤ) : zbdTotSign (m + 1) = (m + 1).negOnePow * zbdTotSign m := by
  rw [zbdTotSign, zbdTotSign, ← Int.negOnePow_add]
  congr 1
  have h : (m + 1) * (m + 1 + 1) = m * (m + 1) + (m + 1) * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0)]
  ring

theorem zbdTotSign_mul_self (m : ℤ) : zbdTotSign m * zbdTotSign m = 1 := Int.units_mul_self _

/-- `t_{m+1} (-1)^{m+1} = t_m`. -/
theorem zbdTotSign_succ_mul (m : ℤ) : zbdTotSign (m + 1) * (m + 1).negOnePow = zbdTotSign m := by
  rw [zbdTotSign_succ, mul_comm, ← mul_assoc, Int.units_mul_self, one_mul]

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-! ### The Čech–Koszul total complex of `K_G` as a cochain complex -/

/-- The Čech–Koszul total module of `K_G` on the face cover, graded by cohomological degree. -/
abbrev zbdUnivGraded : ZbdGradedComplex (IncCoeffRing E) G.UnivCechKoszulModule where
  piece m := G.univCechKoszulPiece (-m)
  d := G.univCechKoszulDifferential
  d_mem m x hx := by
    apply (G.univCechKoszulEquiv_mem_piece _ _).mp
    rw [univCechKoszulEquiv_differential]
    have h := (G.incCechContraction_d_shifts.add G.incKoszulPerturbation_shifts) (-m) _
      ((G.univCechKoszulEquiv_mem_piece _ _).mpr hx)
    rwa [show -m + -1 = -(m + 1) by ring] at h
  d_d x := G.univCechKoszulDifferential_sq x

/-- The Čech–Koszul total complex of `K_G` as a cochain complex of abelian groups. -/
abbrev zbdCechAbComplex : CochainComplex AddCommGrpCat.{0} ℤ :=
  ((forget₂ (ModuleCat.{0} (IncCoeffRing E)) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
    G.zbdUnivGraded.complex

/-- The negative cubical cell resolution of `ℤ` on the face cover. -/
abbrev zbdCellComplex :=
  negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V))

/-! ### The sign-corrected comparison -/

/-- `Ψ_m = t_m Φ_m` as an additive map to the piece of total degree `-m`. -/
def zbdCechHom (m : ℤ) :
    Cochain (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex m →+
      G.univCechKoszulPiece (-m) :=
  AddMonoidHom.mk' (fun z => ⟨(zbdTotSign m : ℤ) • G.cechOfCochain m z,
      Submodule.smul_of_tower_mem _ _ (G.cechOfCochain_mem_piece z)⟩)
    (fun z z' => by
      apply Subtype.ext
      change (zbdTotSign m : ℤ) • G.cechOfCochain m (z + z') =
        (zbdTotSign m : ℤ) • G.cechOfCochain m z + (zbdTotSign m : ℤ) • G.cechOfCochain m z'
      rw [map_add, smul_add])

theorem zbdCechHom_val (m : ℤ)
    (z : Cochain (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex m) :
    (G.zbdCechHom m z : G.UnivCechKoszulModule) = (zbdTotSign m : ℤ) • G.cechOfCochain m z := rfl

theorem zbdCechHom_bijective (m : ℤ) : Function.Bijective (G.zbdCechHom m) := by
  constructor
  · intro z z' h
    have h1 := congrArg Subtype.val h
    rw [zbdCechHom_val, zbdCechHom_val] at h1
    have h2 := congrArg ((zbdTotSign m : ℤ) • ·) h1
    simp only [smul_smul, ← Units.val_mul, zbdTotSign_mul_self, Units.val_one, one_smul] at h2
    exact G.cechOfCochain_injective m h2
  · intro y
    refine ⟨(zbdTotSign m : ℤ) • G.cochainOfCech m y.val, Subtype.ext ?_⟩
    rw [zbdCechHom_val, map_zsmul, smul_smul, ← Units.val_mul, zbdTotSign_mul_self, Units.val_one,
      one_smul, G.cechOfCochain_cochainOfCech y.val y.2]

/-- `Ψ_m` as an additive equivalence. -/
def zbdCechAddEquiv (m : ℤ) :
    Cochain (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex m ≃+
      G.univCechKoszulPiece (-m) :=
  AddEquiv.ofBijective (G.zbdCechHom m) (G.zbdCechHom_bijective m)

/-- **The sign-corrected comparison commutes with the differentials**: `Ψ_{m+1} δ = D Ψ_m`. -/
theorem zbdCechHom_δ (m : ℤ)
    (z : Cochain (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex m) :
    (G.zbdCechHom (m + 1) (δ m (m + 1) z) : G.UnivCechKoszulModule) =
      G.univCechKoszulDifferential (G.zbdCechHom m z) := by
  rw [zbdCechHom_val, zbdCechHom_val, G.cechOfCochain_δ rfl, smul_smul, ← Units.val_mul,
    zbdTotSign_succ_mul, map_zsmul]

/-- **The Hom complex from the cell resolution to `K_G` is isomorphic to the Čech–Koszul total
complex**, as cochain complexes of abelian groups, through `Ψ_m = t_m Φ_m`. -/
def zbdHomCechIso :
    CochainComplex.HomComplex (zbdCellComplex (V := V) (E := E))
        G.incUniversalKoszulCochainComplex ≅
      G.zbdCechAbComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (G.zbdCechAddEquiv m).toAddCommGrpIso) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    ext z
    apply Subtype.ext
    change (G.zbdUnivGraded.dPiece i (i + 1) (G.zbdCechHom i z) : G.UnivCechKoszulModule) =
      (G.zbdCechHom (i + 1) (δ i (i + 1) z) : G.UnivCechKoszulModule)
    rw [ZbdGradedComplex.dPiece_val _ rfl, zbdCechHom_δ])

theorem zbdHomCechIso_hom_f (m : ℤ)
    (z : Cochain (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex m) :
    G.zbdHomCechIso.hom.f m z = G.zbdCechHom m z := rfl

/-! ### Comparison with the complex `C` of the derived base change -/

/-- The Čech–Koszul complex of `K_G` on the face cover is the complex `C` of
`IncidenceZeroBaseChangeDerivedComplex`, through the existing comparison `univCechKoszulEquiv`. -/
def zbdUnivTotalIso : G.zbdUnivGraded.complex ≅ G.zbdTotalComplex where
  hom := G.zbdUnivGraded.hom G.zbdTotalGraded G.univCechKoszulEquiv.toLinearMap
    (fun _ x hx => (G.univCechKoszulEquiv_mem_piece _ x).mpr hx)
    (fun x => (G.univCechKoszulEquiv_differential x).symm)
  inv := G.zbdTotalGraded.hom G.zbdUnivGraded G.univCechKoszulEquiv.symm.toLinearMap
    (fun _ x hx => (G.univCechKoszulEquiv_mem_piece _ _).mp (by
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hx))
    (fun x => by
      apply G.univCechKoszulEquiv.injective
      change G.univCechKoszulEquiv (G.univCechKoszulDifferential (G.univCechKoszulEquiv.symm x)) =
        G.univCechKoszulEquiv (G.univCechKoszulEquiv.symm (G.incTotalDifferential x))
      rw [univCechKoszulEquiv_differential, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply])
  hom_inv_id := by
    rw [ZbdGradedComplex.hom_comp, ← ZbdGradedComplex.hom_id]
    exact ZbdGradedComplex.hom_ext' _ _ _ _ _ _ _ _ fun _ x _ =>
      G.univCechKoszulEquiv.symm_apply_apply x
  inv_hom_id := by
    rw [ZbdGradedComplex.hom_comp, ← ZbdGradedComplex.hom_id]
    exact ZbdGradedComplex.hom_ext' _ _ _ _ _ _ _ _ fun _ x _ =>
      G.univCechKoszulEquiv.apply_symm_apply x

/-- **The Hom complex from the cell resolution to `K_G` is the underlying complex of abelian
groups of `C`.** -/
def zbdHomTotalIso :
    CochainComplex.HomComplex (zbdCellComplex (V := V) (E := E))
        G.incUniversalKoszulCochainComplex ≅
      ((forget₂ (ModuleCat.{0} (IncCoeffRing E)) AddCommGrpCat.{0}).mapHomologicalComplex _).obj
        G.zbdTotalComplex :=
  G.zbdHomCechIso ≪≫
    ((forget₂ (ModuleCat.{0} (IncCoeffRing E)) AddCommGrpCat.{0}).mapHomologicalComplex _).mapIso
      G.zbdUnivTotalIso

/-! ### The induced map on cohomology -/

/-- The differential of the Čech–Koszul complex of abelian groups on underlying elements. -/
theorem zbdCechAbComplex_d_val {i j : ℤ} (h : i + 1 = j) (y : G.zbdCechAbComplex.X i) :
    Subtype.val (p := (· ∈ G.univCechKoszulPiece (-j))) (G.zbdCechAbComplex.d i j y) =
      G.univCechKoszulDifferential (Subtype.val (p := (· ∈ G.univCechKoszulPiece (-i))) y) :=
  G.zbdUnivGraded.dPiece_val h y

/-- **The induced map on cohomology is the existing cycle comparison.** The cohomology class of a
cocycle `z` of the Hom complex (Mathlib's `CohomologyClass`, identified with the homology of
`HomComplex` by `homologyAddEquiv`) goes to the class of any cycle of the Čech–Koszul complex whose
underlying element is `t_n Φ_n z`. -/
theorem zbdHomCechIso_homology_class (n : ℤ)
    (z : Cocycle (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex n)
    (c : G.zbdCechAbComplex.cycles n)
    (hc : G.zbdCechAbComplex.iCycles n c = G.zbdCechHom n z.1) :
    HomologicalComplex.homologyMap G.zbdHomCechIso.hom n
        ((CochainComplex.HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z)) =
      G.zbdCechAbComplex.homologyπ n c := by
  let h := CochainComplex.HomComplex.leftHomologyData (zbdCellComplex (V := V) (E := E))
    G.incUniversalKoszulCochainComplex n
  have e1 : (CochainComplex.HomComplex.homologyAddEquiv _ _ n).symm (CohomologyClass.mk z) =
      (CochainComplex.HomComplex (zbdCellComplex (V := V) (E := E))
        G.incUniversalKoszulCochainComplex).homologyπ n (h.cyclesIso.inv z) := by
    change h.homologyIso.inv (h.π z) = _
    rw [← ConcreteCategory.comp_apply, h.π_comp_homologyIso_inv]
    rfl
  have e2 : (CochainComplex.HomComplex (zbdCellComplex (V := V) (E := E))
      G.incUniversalKoszulCochainComplex).iCycles n (h.cyclesIso.inv z) = z.1 :=
    congrArg (fun φ => φ z) h.cyclesIso_inv_comp_iCycles
  rw [e1, ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (G.zbdCechAbComplex.iCycles n)).mp inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    e2, hc]
  rfl

/-- In degree zero `t_0 = 1`, so `Ψ_0` is the existing cycle comparison `cocycleZeroToCycles`. -/
theorem zbdCechHom_zero_cocycle
    (z : Cocycle (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex 0) :
    (G.zbdCechHom 0 z.1 : G.UnivCechKoszulModule) = (G.cocycleZeroToCycles z).val := by
  rw [zbdCechHom_val, zbdTotSign_zero, Units.val_one, one_smul, cocycleZeroToCycles_val]

/-- In a short complex of abelian groups, a cycle whose homology class vanishes is a boundary. -/
theorem zbd_ab_exists_of_homologyπ_eq_zero (S : ShortComplex AddCommGrpCat.{0}) (c : S.cycles)
    (hc : S.homologyπ c = 0) : ∃ y : S.X₁, S.f y = S.iCycles c := by
  have h1 : S.abLeftHomologyData.homologyIso.hom (S.homologyπ c) = 0 := by
    rw [hc]
    exact map_zero _
  rw [← ConcreteCategory.comp_apply,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ConcreteCategory.comp_apply] at h1
  let k : AddMonoidHom.ker S.g.hom := S.abLeftHomologyData.cyclesIso.hom c
  have h2 : (QuotientAddGroup.mk k : AddMonoidHom.ker S.g.hom ⧸
      AddMonoidHom.range S.abToCycles) = 0 := h1
  rw [QuotientAddGroup.eq_zero_iff] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨y, ?_⟩
  have h3 : S.f y = (k : S.X₂) := congrArg Subtype.val hy
  rw [h3]
  exact congrArg (fun φ => φ c) S.abLeftHomologyData.cyclesIso_hom_comp_i

/-- The degree-zero cycle of `Ψ`-target underlying a cycle of the Čech–Koszul complex. -/
def zbdCyclesZero (c : G.zbdCechAbComplex.cycles 0) : G.univCechKoszulCycles0 :=
  ⟨Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0))) (G.zbdCechAbComplex.iCycles 0 c), by
    have h1 : Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0)))
        (G.zbdCechAbComplex.iCycles 0 c) ∈ G.univCechKoszulPiece 0 := by
      have h0 := Subtype.property (p := (· ∈ G.univCechKoszulPiece (-0)))
        (G.zbdCechAbComplex.iCycles 0 c)
      generalize Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0)))
        (G.zbdCechAbComplex.iCycles 0 c) = w at h0 ⊢
      rwa [neg_zero] at h0
    refine ⟨h1, ?_⟩
    have h2 := congrArg (Subtype.val (p := (· ∈ G.univCechKoszulPiece (-(0 + 1)))))
      (congrArg (fun φ => φ c) (G.zbdCechAbComplex.iCycles_d 0 (0 + 1)))
    rw [ConcreteCategory.comp_apply, zbdCechAbComplex_d_val G rfl] at h2
    exact h2⟩

/-- **Compatibility with the augmentation used by `incUniversalKoszulHypercohomologyZeroEquiv`.**
If a degree-zero cycle `c` of the Čech–Koszul complex has the same class as the image of a
Hom-complex class `x`, then the augmentation of `x` (`cohomologyClassZeroAugmentation`) is the
augmentation of `c` (`univCechKoszulAugmentation`). -/
theorem zbdHomCechIso_augmentation
    (x : CohomologyClass (zbdCellComplex (V := V) (E := E)) G.incUniversalKoszulCochainComplex 0)
    (c : G.zbdCechAbComplex.cycles 0)
    (hc : G.zbdCechAbComplex.homologyπ 0 c = HomologicalComplex.homologyMap G.zbdHomCechIso.hom 0
      ((CochainComplex.HomComplex.homologyAddEquiv _ _ 0).symm x)) :
    G.cohomologyClassZeroAugmentation x = G.univCechKoszulAugmentation (G.zbdCyclesZero c) := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let h := CochainComplex.HomComplex.leftHomologyData (zbdCellComplex (V := V) (E := E))
    G.incUniversalKoszulCochainComplex 0
  let c' : G.zbdCechAbComplex.cycles 0 :=
    HomologicalComplex.cyclesMap G.zbdHomCechIso.hom 0 (h.cyclesIso.inv z)
  have hc' : G.zbdCechAbComplex.iCycles 0 c' = G.zbdCechHom 0 z.1 := by
    change (HomologicalComplex.cyclesMap G.zbdHomCechIso.hom 0 ≫ G.zbdCechAbComplex.iCycles 0)
      (h.cyclesIso.inv z) = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
    have e2 : (CochainComplex.HomComplex (zbdCellComplex (V := V) (E := E))
        G.incUniversalKoszulCochainComplex).iCycles 0 (h.cyclesIso.inv z) = z.1 :=
      congrArg (fun φ => φ z) h.cyclesIso_inv_comp_iCycles
    rw [e2]
    rfl
  rw [G.zbdHomCechIso_homology_class 0 z c' hc'] at hc
  have h0 : G.zbdCechAbComplex.homologyπ 0 (c - c') = 0 := by
    rw [map_sub, hc, sub_self]
  obtain ⟨y, hy⟩ := zbd_ab_exists_of_homologyπ_eq_zero (G.zbdCechAbComplex.sc 0) _ h0
  have hprev : (ComplexShape.up ℤ).prev 0 + 1 = 0 := by
    rw [CochainComplex.prev]
    ring
  have hy' := congrArg (Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0)))) hy
  change Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0)))
    (G.zbdCechAbComplex.d ((ComplexShape.up ℤ).prev 0) 0 y) = _ at hy'
  rw [zbdCechAbComplex_d_val G hprev, map_sub] at hy'
  rw [cohomologyClassZeroAugmentation_mk, eq_comm, ← sub_eq_zero, ← map_sub,
    univCechKoszulAugmentation_eq_zero_iff]
  refine ⟨Subtype.val (p := (· ∈ G.univCechKoszulPiece (-((ComplexShape.up ℤ).prev 0)))) y, ?_, ?_⟩
  · have h1 := Subtype.property (p := (· ∈ G.univCechKoszulPiece (-((ComplexShape.up ℤ).prev 0)))) y
    generalize Subtype.val (p := (· ∈ G.univCechKoszulPiece (-((ComplexShape.up ℤ).prev 0)))) y = w
      at h1 ⊢
    rwa [show -((ComplexShape.up ℤ).prev 0) = 1 by omega] at h1
  · rw [hy']
    have e3 : Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0)))
        (G.zbdCechAbComplex.iCycles 0 c') = (G.cocycleZeroToCycles z).val := by
      rw [← G.zbdCechHom_zero_cocycle z]
      exact congrArg Subtype.val hc'
    change Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0))) (G.zbdCechAbComplex.iCycles 0 c) -
        Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0))) (G.zbdCechAbComplex.iCycles 0 c') =
      Subtype.val (p := (· ∈ G.univCechKoszulPiece (-0))) (G.zbdCechAbComplex.iCycles 0 c) -
        (G.cocycleZeroToCycles z).val
    rw [e3]

end

end BPFixedPoints.Multigraph
