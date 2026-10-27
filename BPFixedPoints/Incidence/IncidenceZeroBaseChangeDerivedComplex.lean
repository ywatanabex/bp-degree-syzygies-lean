import BPFixedPoints.Incidence.IncidenceZeroBaseChangeNormalization
import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedGraded
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # The base change to the coefficient origin as an isomorphism in `D(ModuleCat ℂ)`

The paper computes `𝒰_G ⊗^L_{S_G} ℂ` from the bounded Čech–Koszul model (end of the proof of
Theorem 3.4). `IncidenceZeroBaseChangeTor` did this on cohomology, one bidegree at a time. This
file lifts it to an actual isomorphism in the derived category of `ℂ`-vector spaces.

* **Complexes over `S_G`** (`ZbdGradedComplex`, `IncidenceZeroBaseChangeDerivedGraded`).
  `zbdResolutionComplex` is the free resolution `F⁻` (`incResolutionDifferential`), with
  homological degree `p` in cohomological degree `-p`; `zbdTotalComplex` is the Čech–Koszul model
  `C` (`incTotalDifferential`), with exterior degree `q` and Čech degree `j` in cohomological
  degree `j - q`. Both are `CochainComplex (ModuleCat S_G) ℤ`; their terms are the existing
  integer-indexed pieces `incResolutionPiece (-i)` and `incTotalPiece (-i)`.
* **Homotopy equivalence over `S_G`** (`zbdHomotopyEquiv`). It is assembled from the existing
  perturbation data: `ι = incResolutionInclusion` and `P = incResolutionProjection` are chain
  maps, `P ι = 1`, and `D H + H D + ι P = 1` says that `-H` (`zbdHomotopy`) is a homotopy from
  `ι P` to `1` in Mathlib's convention `f = dNext + prevD + g`. The degree conventions are the
  existing `Shifts` lemmas.
* **Base change** (`zbdBaseChangeHomotopyEquiv`). Extension of scalars along `constantCoeff` is
  additive, so `Functor.mapHomotopyEquiv` gives a homotopy equivalence
  `ℂ ⊗ F⁻ ≃ C₀ = ℂ ⊗ C`. **No flatness is used**: `ℂ` is not flat over `S_G`, and the argument
  never claims that `ℂ ⊗ -` preserves quasi-isomorphisms; only the explicit homotopies are
  transported.
* **The derived isomorphism** (`zbdDerivedIso`): `Q(ℂ ⊗ F⁻) ≅ Q(C₀)` in `DerivedCategory
  (ModuleCat ℂ)`, for any chosen model of the derived category, through
  `HomotopyCategory.isoOfHomotopyEquiv`, `DerivedCategory.Qh` and `quotientCompQhIso`. Its
  morphism is `Q` of the base change of `ι` (`zbdDerivedIso_hom`), its inverse `Q` of the base
  change of `P` (`zbdDerivedIso_inv`).
* **`C₀` is the existing model over `ℂ`** (`zbdModelIso`): an isomorphism of cochain complexes
  from `C₀` to `zbdModelComplex`, the module `ZbcModule` graded by total degree
  (`zbdModelPiece`) with the Čech differential `zbcContraction.d`. In each degree it is
  `zbcBaseChangeEquiv` restricted to the pieces (`zbdPieceEquiv`; the inverse uses the
  projection `zbdTotalRetraction` onto a piece, which commutes with specialization). It is a
  chain map because the Koszul part vanishes at the origin (`zbcSpecialize_total`).
  `zbdDerivedModelIso` composes both.

The identification of the cohomology of `ℂ ⊗ F⁻` with Mathlib's left derived functor, the
comparison with `zbcTorEquiv` and with sheaf cohomology are in
`IncidenceZeroBaseChangeDerivedTor`.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CechProduct IncidencePerturbation Finsupp ResolutionTools
open scoped TensorProduct ChangeOfRings

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-! ### The free resolution and the Čech–Koszul model as cochain complexes over `S_G` -/

/-- The free resolution `F⁻`: homological degree `p` in cohomological degree `-p`. -/
abbrev zbdResolutionGraded :
    ZbdGradedComplex (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E) where
  piece i := G.incResolutionPiece (-i)
  d := G.incResolutionDifferential
  d_mem i x hx := by
    have h := G.incResolutionDifferential_hasDegree (-i) x hx
    rwa [show -i + -1 = -(i + 1) by ring] at h
  d_d x := LinearMap.congr_fun G.incResolutionDifferential_sq x

/-- The Čech–Koszul model `C`: exterior degree `q` and Čech degree `j` in cohomological degree
`j - q`. -/
abbrev zbdTotalGraded : ZbdGradedComplex (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) where
  piece i := incTotalPiece (-i)
  d := G.incTotalDifferential
  d_mem i x hx := by
    have h := (G.incCechContraction_d_shifts.add G.incKoszulPerturbation_shifts) (-i) x hx
    rwa [show -i + -1 = -(i + 1) by ring] at h
  d_d x := LinearMap.congr_fun G.incTotalDifferential_sq x

/-- The free resolution `F⁻` as a cochain complex over `S_G`. -/
abbrev zbdResolutionComplex : CochainComplex (ModuleCat.{0} (IncCoeffRing E)) ℤ :=
  G.zbdResolutionGraded.complex

/-- The Čech–Koszul model as a cochain complex over `S_G`. -/
abbrev zbdTotalComplex : CochainComplex (ModuleCat.{0} (IncCoeffRing E)) ℤ :=
  G.zbdTotalGraded.complex

/-- The homotopy `-H` from `ι P` to the identity, in Mathlib's convention. -/
def zbdHomotopy :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] IncTotalModule (V := V) (E := E) where
  toFun x := -G.incResolutionHomotopy x
  map_add' x y := by
    change -G.incResolutionHomotopy (x + y) =
      -G.incResolutionHomotopy x + -G.incResolutionHomotopy y
    rw [map_add]
    exact neg_add (G.incResolutionHomotopy x) (G.incResolutionHomotopy y)
  map_smul' r x := by
    change -G.incResolutionHomotopy (r • x) = r • -G.incResolutionHomotopy x
    rw [map_smul]
    exact (smul_neg r (G.incResolutionHomotopy x)).symm

theorem zbdHomotopy_apply (x : IncTotalModule (V := V) (E := E)) :
    G.zbdHomotopy x = -G.incResolutionHomotopy x := rfl

theorem zbd_homotopy_identity (x : IncTotalModule (V := V) (E := E)) :
    G.incResolutionInclusion (G.incResolutionProjection x) =
      G.zbdHomotopy (G.incTotalDifferential x) +
        G.incTotalDifferential (G.zbdHomotopy x) + x := by
  have h := LinearMap.congr_fun G.incResolutionHomotopy_identity x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h
  have hn : G.incTotalDifferential (-G.incResolutionHomotopy x) =
      -G.incTotalDifferential (G.incResolutionHomotopy x) :=
    map_neg G.incTotalDifferential (G.incResolutionHomotopy x)
  rw [zbdHomotopy_apply, zbdHomotopy_apply, hn]
  calc G.incResolutionInclusion (G.incResolutionProjection x) =
      (G.incTotalDifferential (G.incResolutionHomotopy x) +
        G.incResolutionHomotopy (G.incTotalDifferential x) +
        G.incResolutionInclusion (G.incResolutionProjection x)) -
        G.incTotalDifferential (G.incResolutionHomotopy x) -
        G.incResolutionHomotopy (G.incTotalDifferential x) := by abel
    _ = _ := by rw [h]; abel

/-- **The homotopy equivalence `F⁻ ≃ C` over `S_G`** from the perturbation data: `ι` and `P`
are chain maps, `P ι = 1`, and `-H` is a homotopy from `ι P` to `1` in Mathlib's convention
(the identity `D H + H D + ι P = 1` reads `ι P = (-H) D + D (-H) + 1`). -/
def zbdHomotopyEquiv : HomotopyEquiv G.zbdResolutionComplex G.zbdTotalComplex :=
  ZbdGradedComplex.homotopyEquiv _ _ G.incResolutionInclusion G.incResolutionProjection
    (fun i x hx => by
      have h := G.incResolutionInclusion_shifts (-i) x hx
      rw [add_zero] at h
      exact h)
    (fun x => LinearMap.congr_fun G.incResolutionInclusion_chain x)
    (fun i x hx => by
      have h := G.incResolutionProjection_shifts (-i) x hx
      rw [add_zero] at h
      exact h)
    (fun x => (LinearMap.congr_fun G.incResolutionProjection_chain x).symm)
    (fun x => LinearMap.congr_fun G.incResolutionProjection_inclusion x)
    G.zbdHomotopy
    (fun i x hx => by
      have h := G.incResolutionHomotopy_shifts (-i) x hx
      rw [show -i + 1 = -(i - 1) by ring] at h
      rw [zbdHomotopy_apply, ← neg_one_smul (IncCoeffRing E) (G.incResolutionHomotopy x)]
      exact Submodule.smul_mem _ _ h)
    G.zbd_homotopy_identity

/-! ### Base change along the coefficient origin -/

/-- Extension of scalars along the coefficient origin `constantCoeff : S_G → ℂ`. -/
abbrev zbdBaseChange (E : Type) : ModuleCat.{0} (IncCoeffRing E) ⥤ ModuleCat.{0} ℂ :=
  ModuleCat.extendScalars (zbcOrigin E)

/-- `ℂ ⊗_{S_G} F⁻`. -/
abbrev zbdResolutionComplexC : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  ((zbdBaseChange E).mapHomologicalComplex _).obj G.zbdResolutionComplex

/-- `C₀ = ℂ ⊗_{S_G} C`. -/
abbrev zbdTotalComplexC : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  ((zbdBaseChange E).mapHomologicalComplex _).obj G.zbdTotalComplex

/-- **The base change of the homotopy equivalence.** Extension of scalars is an additive functor,
so it carries the homotopy equivalence `F⁻ ≃ C` to a homotopy equivalence
`ℂ ⊗ F⁻ ≃ ℂ ⊗ C`. No flatness is used. -/
def zbdBaseChangeHomotopyEquiv : HomotopyEquiv G.zbdResolutionComplexC G.zbdTotalComplexC :=
  (zbdBaseChange E).mapHomotopyEquiv G.zbdHomotopyEquiv

theorem zbdBaseChangeHomotopyEquiv_hom_f (i : ℤ) :
    G.zbdBaseChangeHomotopyEquiv.hom.f i = (zbdBaseChange E).map (G.zbdHomotopyEquiv.hom.f i) :=
  rfl

/-! ### The base-changed model over `ℂ` -/

/-- The Čech monomials of Čech degree `|S| - n` (total degree `n`, homological convention). -/
abbrev zbdSlot (V : Type) [Fintype V] (S : Finset E) (n : ℤ) : Set (V → CechProduct.Basis) :=
  {b | (cechDegree b : ℤ) = (S.card : ℤ) - n}

/-- The piece of the base-changed model of total degree `n` (homological convention, as
`incTotalPiece`). -/
def zbdModelPiece (V E : Type) [Fintype V] [DecidableEq E] (n : ℤ) :
    Submodule ℂ (ZbcModule V E) where
  carrier := {x | ∀ S, x S ∈ supported ℂ ℂ (zbdSlot V S n)}
  zero_mem' := fun _ => Submodule.zero_mem _
  add_mem' hx hy := fun S => Submodule.add_mem _ (hx S) (hy S)
  smul_mem' c _ hx := fun S => Submodule.smul_mem _ c (hx S)

theorem mem_zbdModelPiece_iff (n : ℤ) (x : ZbcModule V E) :
    x ∈ zbdModelPiece V E n ↔ ∀ S, x S ∈ supported ℂ ℂ (zbdSlot V S n) := Iff.rfl

/-- The base-changed model `ZbcModule` with the Čech differential over `ℂ`, graded by
cohomological degree. -/
abbrev zbdModelGraded : ZbdGradedComplex ℂ (ZbcModule V E) where
  piece i := zbdModelPiece V E (-i)
  d := G.zbcContraction.d
  d_mem i x hx S := by
    rw [zbcContraction_d_apply]
    have h := contraction_d_degree ℂ (G.deg S) ((S.card : ℤ) - -i) (x S) (hx S)
    rwa [show (S.card : ℤ) - -i + 1 = (S.card : ℤ) - -(i + 1) by ring] at h
  d_d x := LinearMap.congr_fun G.zbcContraction.d_sq x

/-- The base-changed model as a cochain complex over `ℂ`. -/
abbrev zbdModelComplex : CochainComplex (ModuleCat.{0} ℂ) ℤ := G.zbdModelGraded.complex

/-- A componentwise map on exterior-state sums acts componentwise. -/
theorem zbd_diagonal_apply {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (f : Finset E → Module.End R W) (x : Koszul.Space E W) (T : Finset E) :
    Koszul.diagonal f x T = f T (x T) := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply]; exact (map_zero (f T)).symm
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, map_add]
  | single S w =>
    rw [Koszul.diagonal_single]
    by_cases h : S = T
    · subst h
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne' h, Finsupp.single_eq_of_ne' h, map_zero]

/-- The projection of the base-changed model onto total degree `n`. -/
def zbdModelFilter (n : ℤ) : Module.End ℂ (ZbcModule V E) :=
  Koszul.diagonal fun S =>
    (supported ℂ ℂ (zbdSlot V S n)).subtype ∘ₗ restrictDom ℂ ℂ (zbdSlot V S n)

theorem zbdModelFilter_apply (n : ℤ) (x : ZbcModule V E) (S : Finset E) :
    zbdModelFilter n x S = Finsupp.filter (· ∈ zbdSlot V S n) (x S) := by
  rw [zbdModelFilter, zbd_diagonal_apply]
  rfl

theorem zbdModelFilter_of_mem {n : ℤ} {x : ZbcModule V E} (hx : x ∈ zbdModelPiece V E n) :
    zbdModelFilter n x = x := by
  ext S b
  rw [zbdModelFilter_apply, Finsupp.filter_apply]
  split_ifs with hb
  · rfl
  · exact ((mem_supported' ℂ _).mp (hx S) b hb).symm

/-- The projection of the Čech–Koszul model over `S_G` onto total degree `n`, as a retraction
onto `incTotalPiece n`. -/
def zbdTotalRetraction (n : ℤ) :
    IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] incTotalPiece (V := V) (E := E) n :=
  LinearMap.codRestrict _
    (Koszul.diagonal fun S =>
      (supported (IncCoeffRing E) (IncCoeffRing E) (zbdSlot V S n)).subtype ∘ₗ
        restrictDom (IncCoeffRing E) (IncCoeffRing E) (zbdSlot V S n))
    (fun x S => by
      rw [zbd_diagonal_apply]
      exact (restrictDom (IncCoeffRing E) (IncCoeffRing E) (zbdSlot V S n) (x S)).2)

theorem zbdTotalRetraction_apply (n : ℤ) (x : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    (zbdTotalRetraction n x : IncTotalModule (V := V) (E := E)) S =
      Finsupp.filter (· ∈ zbdSlot V S n) (x S) := by
  change Koszul.diagonal _ x S = _
  rw [zbd_diagonal_apply]
  rfl

theorem zbdTotalRetraction_val {n : ℤ} (x : incTotalPiece (V := V) (E := E) n) :
    zbdTotalRetraction n x.val = x := by
  apply Subtype.ext
  refine Finsupp.ext fun S => Finsupp.ext fun b => ?_
  rw [zbdTotalRetraction_apply, Finsupp.filter_apply]
  split_ifs with hb
  · rfl
  · exact ((mem_supported' (IncCoeffRing E) _).mp (x.2 S) b hb).symm

/-- Specialization commutes with the projection onto total degree `n`. -/
theorem zbdSpecialize_totalRetraction (n : ℤ) (x : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (zbdTotalRetraction n x : IncTotalModule (V := V) (E := E)) =
      zbdModelFilter n (zbcSpecialize x) := by
  ext S b
  rw [zbcSpecialize_apply, zbdModelFilter_apply, zbcSpecialize_apply, mapRange_apply,
    zbdTotalRetraction_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs with hb
  · rw [mapRange_apply]
  · exact map_zero _

/-- Specialization preserves the total degree. -/
theorem zbdSpecialize_mem_model {n : ℤ} {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalPiece n) : zbcSpecialize x ∈ zbdModelPiece V E n := by
  intro S
  rw [zbcSpecialize_apply, mem_supported']
  intro b hb
  rw [mapRange_apply, (mem_supported' (IncCoeffRing E) _).mp (hx S) b hb, map_zero]

section Pieces

local instance zbdOriginAlgebra : Algebra (IncCoeffRing E) ℂ := (zbcOrigin E).toAlgebra

theorem zbdBaseChangeEquiv_subtype_mem (n : ℤ)
    (t : ℂ ⊗[IncCoeffRing E] incTotalPiece (V := V) (E := E) n) :
    zbcBaseChangeEquiv ((incTotalPiece (V := V) (E := E) n).subtype.baseChange ℂ t) ∈
      zbdModelPiece V E n := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul]
    exact Submodule.smul_mem _ c (zbdSpecialize_mem_model x.2)
  | add s t hs ht => rw [map_add, map_add]; exact Submodule.add_mem _ hs ht

/-- The base change of a piece maps to the piece of the model. -/
def zbdPieceToModel (n : ℤ) :
    ℂ ⊗[IncCoeffRing E] incTotalPiece (V := V) (E := E) n →ₗ[ℂ] zbdModelPiece V E n :=
  LinearMap.codRestrict _
    (zbcBaseChangeEquiv.toLinearMap ∘ₗ (incTotalPiece (V := V) (E := E) n).subtype.baseChange ℂ)
    (zbdBaseChangeEquiv_subtype_mem n)

theorem zbdPieceToModel_tmul (n : ℤ) (c : ℂ) (x : incTotalPiece (V := V) (E := E) n) :
    (zbdPieceToModel n (c ⊗ₜ[IncCoeffRing E] x) : ZbcModule V E) = c • zbcSpecialize x.val := by
  change zbcBaseChangeEquiv ((incTotalPiece (V := V) (E := E) n).subtype.baseChange ℂ (c ⊗ₜ x)) = _
  rw [LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul]
  rfl

/-- The model piece back to the base change of the piece, through the retraction. -/
def zbdModelToPiece (n : ℤ) :
    zbdModelPiece V E n →ₗ[ℂ] ℂ ⊗[IncCoeffRing E] incTotalPiece (V := V) (E := E) n :=
  (zbdTotalRetraction n).baseChange ℂ ∘ₗ zbcBaseChangeEquiv.symm.toLinearMap ∘ₗ
    (zbdModelPiece V E n).subtype

theorem zbdBaseChangeEquiv_retraction (n : ℤ)
    (t : ℂ ⊗[IncCoeffRing E] IncTotalModule (V := V) (E := E)) :
    zbcBaseChangeEquiv ((incTotalPiece (V := V) (E := E) n).subtype.baseChange ℂ
      ((zbdTotalRetraction n).baseChange ℂ t)) = zbdModelFilter n (zbcBaseChangeEquiv t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul,
      zbcBaseChangeEquiv_tmul, map_smul]
    congr 1
    exact zbdSpecialize_totalRetraction n x
  | add s t hs ht => simp only [map_add, hs, ht]

/-- **The base change of a piece of `C` is the piece of the model**, through
`zbcBaseChangeEquiv`. -/
def zbdPieceEquiv (n : ℤ) :
    ℂ ⊗[IncCoeffRing E] incTotalPiece (V := V) (E := E) n ≃ₗ[ℂ] zbdModelPiece V E n :=
  LinearEquiv.ofLinearMap (zbdPieceToModel n) (zbdModelToPiece n)
    (by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change zbcBaseChangeEquiv ((incTotalPiece (V := V) (E := E) n).subtype.baseChange ℂ
        ((zbdTotalRetraction n).baseChange ℂ (zbcBaseChangeEquiv.symm z.val))) = z.val
      rw [zbdBaseChangeEquiv_retraction, LinearEquiv.apply_symm_apply,
        zbdModelFilter_of_mem z.2])
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c x
      change (zbdTotalRetraction n).baseChange ℂ (zbcBaseChangeEquiv.symm
        (zbdPieceToModel n (c ⊗ₜ x) : ZbcModule V E)) = c ⊗ₜ x
      rw [zbdPieceToModel_tmul, ← zbcBaseChangeEquiv_tmul, LinearEquiv.symm_apply_apply,
        LinearMap.baseChange_tmul, zbdTotalRetraction_val])

theorem zbdPieceEquiv_tmul (n : ℤ) (c : ℂ) (x : incTotalPiece (V := V) (E := E) n) :
    (zbdPieceEquiv n (c ⊗ₜ[IncCoeffRing E] x) : ZbcModule V E) = c • zbcSpecialize x.val :=
  zbdPieceToModel_tmul n c x

/-- The components of the identification of `C₀` with the model. -/
def zbdModelIsoApp (i : ℤ) : G.zbdTotalComplexC.X i ≅ G.zbdModelComplex.X i :=
  (zbdPieceEquiv (V := V) (E := E) (-i)).toModuleIso

theorem zbdModelIsoApp_hom_tmul (i : ℤ) (m : G.zbdTotalComplex.X i) :
    Subtype.val (p := (· ∈ zbdModelPiece V E (-i)))
      ((G.zbdModelIsoApp i).hom ((1 : ℂ) ⊗ₜ[IncCoeffRing E, zbcOrigin E] m)) =
      zbcSpecialize (Subtype.val (p := (· ∈ incTotalPiece (V := V) (E := E) (-i))) m) := by
  have h := zbdPieceEquiv_tmul (V := V) (E := E) (-i) 1 m
  rw [one_smul] at h
  exact h

/-- **`C₀` is the base-changed model**: the isomorphism of cochain complexes over `ℂ` given in
each degree by `zbcBaseChangeEquiv`; it carries `D ⊗ ℂ` to the Čech differential over `ℂ`
because the Koszul part vanishes at the origin (`zbcSpecialize_total`). -/
def zbdModelIso : G.zbdTotalComplexC ≅ G.zbdModelComplex :=
  HomologicalComplex.Hom.isoOfComponents G.zbdModelIsoApp (by
    intro i j hij
    apply ModuleCat.hom_ext
    have key : G.zbdModelGraded.dPiece i j ∘ₗ (zbdPieceEquiv (V := V) (E := E) (-i)).toLinearMap =
        (zbdPieceEquiv (V := V) (E := E) (-j)).toLinearMap ∘ₗ
          (G.zbdTotalGraded.dPiece i j).baseChange ℂ := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c m
      apply Subtype.ext
      change Subtype.val (G.zbdModelGraded.dPiece i j (zbdPieceEquiv (-i) (c ⊗ₜ m))) =
        Subtype.val (zbdPieceEquiv (-j) (c ⊗ₜ (G.zbdTotalGraded.dPiece i j m)))
      rw [ZbdGradedComplex.dPiece_val _ hij, zbdPieceEquiv_tmul, zbdPieceEquiv_tmul,
        ZbdGradedComplex.dPiece_val _ hij, map_smul]
      exact congrArg (c • ·) (zbcSpecialize_total G m.val).symm
    exact key)

end Pieces

section Derived

universe w

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℂ)]

/-- **The base change as an isomorphism in `D(ModuleCat ℂ)`**: the image of the base-changed
homotopy equivalence in the homotopy category, sent to the derived category by `Qh` and
transported to `Q` by the canonical isomorphism `quotient ⋙ Qh ≅ Q`. -/
def zbdDerivedIso :
    DerivedCategory.Q.obj G.zbdResolutionComplexC ≅ DerivedCategory.Q.obj G.zbdTotalComplexC :=
  ((DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℂ)).app _).symm ≪≫
    DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv G.zbdBaseChangeHomotopyEquiv) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℂ)).app _

/-- The derived isomorphism is the image under `Q` of the base change of `ι`. -/
theorem zbdDerivedIso_hom :
    G.zbdDerivedIso.hom = DerivedCategory.Q.map G.zbdBaseChangeHomotopyEquiv.hom := by
  simp [zbdDerivedIso]

/-- The inverse of the derived isomorphism is the image under `Q` of the base change of `P`. -/
theorem zbdDerivedIso_inv :
    G.zbdDerivedIso.inv = DerivedCategory.Q.map G.zbdBaseChangeHomotopyEquiv.inv := by
  simp [zbdDerivedIso]

/-- The derived isomorphism followed by the identification of `C₀` with the model over `ℂ`. -/
def zbdDerivedModelIso :
    DerivedCategory.Q.obj G.zbdResolutionComplexC ≅ DerivedCategory.Q.obj G.zbdModelComplex :=
  G.zbdDerivedIso ≪≫ DerivedCategory.Q.mapIso G.zbdModelIso

theorem zbdDerivedModelIso_hom :
    G.zbdDerivedModelIso.hom =
      DerivedCategory.Q.map (G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom) := by
  rw [zbdDerivedModelIso, Iso.trans_hom, zbdDerivedIso_hom, Functor.mapIso_hom, Functor.map_comp]

end Derived

end

end BPFixedPoints.Multigraph
