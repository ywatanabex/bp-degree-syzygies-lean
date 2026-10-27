import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedDecomposition

/-! # Products through the derived base change

The target is a commutative diagram in `DerivedCategory (ModuleCat ℂ)`, not a strict map of dg
algebras. Both products are compared through a common zero-differential state model over `ℂ`.

* **Zero differentials** (`zbdHomotopyOfRange`, `zbdHomotopyOfZeroDifferentials`,
  `zbd_Q_map_eq_of_zeroDifferentials`). If `K` has zero differentials and projective terms (for
  instance any complex of `ℂ`-vector spaces with zero differential), two chain maps `K ⟶ L` that
  agree on cohomology are homotopic, hence equal in the derived category: their difference lands
  in the boundaries (`zbd_mem_range_d_of_homologyMap_eq_zero`) and projectivity lifts it through
  the differential. "Same map on cohomology implies same morphism in `D`" is false in general;
  only this special case is used.
* **Cohomology level** (`zbdDerivedIso_product`, `zbdDerivedIso_one`). Read through
  `zbdTorDerivedIso` and `zbdSheafToDerived`, the cohomology of the derived isomorphism sends the
  standard Tor product and unit to the exterior cohomology product and unit (from
  `incidenceTorExteriorEquiv_product`, `incidenceTorExteriorEquiv_one`).
* **The product comparison in `D(ℂ)`** (`zbdProductSquare`, `zbdDerivedProduct`). The state model
  `zbdStateGraded` is the free `ℂ`-module on the states with zero differential, and it is
  `ℂ ⊗ F⁻` (`zbdStateIso`); the pair model `zbdPairGraded` is the free `ℂ`-module on pairs of
  states with zero differential. `μ₀ = zbdStateProductHom` is the specialization of the
  multiplication lift `incResolutionCup` (which computes `incidenceTorProduct`,
  `incidenceTorProduct_eq_transferred`), `ι₀ = zbdStateInclusionHom` is `zbcContraction.i`, which
  is the base change of `ι` under `zbdStateIso` (`zbdStateIso_inclusion`), and
  `zbdPairCupHom` is the specialized Čech–Koszul product `incTotalCup` of the inclusions,
  `∪₀ ∘ (ι₀ ⊗ ι₀)` at the chain level. Then
  `Q(μ₀) ≫ Q(zbdStateIso.inv) ≫ zbdDerivedModelIso.hom = Q(∪₀ ∘ (ι₀ ⊗ ι₀))`. The proof is an
  explicit homotopy: `ι₀ μ₀ - ∪₀(ι₀ ⊗ ι₀) = d(-h₀ ∪₀(ι₀ ⊗ ι₀))` (`zbdStateProduct_inclusion`),
  from `μ₀ = p₀ ∪₀ (ι₀ ⊗ ι₀)` at the origin (`zbcFreeSpecialize_projection`), the Leibniz rule
  (`incTotalCup_leibniz`, the differential of the minimal resolution vanishing at the origin) and
  the contraction identity `d h + h d + i p = 1` over `ℂ`.

`IncidenceZeroBaseChangeDerivedTensor` identifies the pair model with Mathlib's monoidal tensor
product of the state model with itself, makes the Čech product a chain map `C₀ ⊗ C₀ ⟶ C₀` out of
the tensor product, and turns the square above into a square out of the tensor product
(`zbdDerivedTensorProduct`). The unit is compared on cohomology (`zbdDerivedIso_one`), and the
relation of the Čech product `incTotalCup` with the sheaf-theoretic exterior product is the
cohomology-level one.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory

universe w

section ZeroDifferential

variable {R : Type} [CommRing R]

/-- A chain map out of a complex with zero differentials that is zero on cohomology lands in the
boundaries. -/
theorem zbd_mem_range_d_of_homologyMap_eq_zero {K L : CochainComplex (ModuleCat.{0} R) ℤ}
    (hK : ∀ i j, K.d i j = 0) (φ : K ⟶ L) (hφ : ∀ n, HomologicalComplex.homologyMap φ n = 0)
    {i j : ℤ} (hji : j + 1 = i) (x : K.X i) : φ.f i x ∈ LinearMap.range (L.d j i).hom := by
  have hk : φ.f i ≫ L.d i ((ComplexShape.up ℤ).next i) = 0 := by
    rw [φ.comm, hK, Limits.zero_comp]
  have hπ : L.homologyπ i (L.liftCycles (φ.f i) _ rfl hk x) = 0 := by
    have hlift : L.liftCycles (φ.f i) _ rfl hk =
        K.liftCycles (𝟙 _) _ rfl (by rw [hK, Limits.comp_zero]) ≫
          HomologicalComplex.cyclesMap φ i := by
      rw [HomologicalComplex.liftCycles_comp_cyclesMap]
      simp only [Category.id_comp]
    have hmor : L.liftCycles (φ.f i) _ rfl hk ≫ L.homologyπ i = 0 := by
      rw [hlift, Category.assoc, ← HomologicalComplex.homologyπ_naturality, hφ i]
      simp only [Limits.comp_zero]
    exact ConcreteCategory.congr_hom hmor x
  obtain ⟨j', y, hy⟩ := zbd_exists_boundary_of_homologyπ_eq_zero L _ hπ
  have hval : L.iCycles i (L.liftCycles (φ.f i) _ rfl hk x) = φ.f i x :=
    ConcreteCategory.congr_hom (HomologicalComplex.liftCycles_i L (φ.f i) _ rfl hk) x
  rw [hval] at hy
  by_cases h : j' + 1 = i
  · obtain rfl : j' = j := by omega
    exact ⟨y, hy⟩
  · rw [L.shape j' i h] at hy
    rw [← hy]
    exact ⟨0, map_zero _⟩

/-- **A homotopy out of a complex with zero differentials and projective terms.** If `f - g`
lands in the boundaries in every degree, projectivity lifts it through the differential, and the
lifts form a homotopy from `f` to `g`. -/
noncomputable def zbdHomotopyOfRange {K L : CochainComplex (ModuleCat.{0} R) ℤ}
    (hK : ∀ i j, K.d i j = 0) [∀ n, Module.Projective R (K.X n)] (f g : K ⟶ L)
    (hrange : ∀ i j, j + 1 = i → ∀ x : K.X i,
      (f - g).f i x ∈ LinearMap.range (L.d j i).hom) :
    Homotopy f g := by
  have hlift : ∀ i j, j + 1 = i → ∃ h : K.X i ⟶ L.X j, h ≫ L.d j i = (f - g).f i := by
    intro i j hji
    obtain ⟨h, hh⟩ := Module.projective_lifting_property (L.d j i).hom.rangeRestrict
      (((f - g).f i).hom.codRestrict (LinearMap.range (L.d j i).hom) (hrange i j hji))
      (LinearMap.surjective_rangeRestrict _)
    refine ⟨ModuleCat.ofHom h, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (LinearMap.congr_fun hh x)
  choose hom hhom using hlift
  exact
    { hom := fun i j => if hji : j + 1 = i then hom i j hji else 0
      zero := fun i j hji => dite_eq_right hji
      comm := fun i => by
        rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i from sub_add_cancel i 1), hK,
          Limits.zero_comp, zero_add, dite_eq_left (sub_add_cancel i 1), hhom,
          HomologicalComplex.sub_f_apply, sub_add_cancel] }

/-- **Over a complex with zero differentials and projective terms, cohomology determines chain
maps up to homotopy.** If `f` and `g` induce the same maps on cohomology, then `f - g` lands in
the boundaries (`zbd_mem_range_d_of_homologyMap_eq_zero`). -/
noncomputable def zbdHomotopyOfZeroDifferentials {K L : CochainComplex (ModuleCat.{0} R) ℤ}
    (hK : ∀ i j, K.d i j = 0) [∀ n, Module.Projective R (K.X n)] (f g : K ⟶ L)
    (hfg : ∀ n, HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n) :
    Homotopy f g :=
  zbdHomotopyOfRange hK f g fun _ _ hji x =>
    zbd_mem_range_d_of_homologyMap_eq_zero hK (f - g)
      (fun n => by rw [HomologicalComplex.homologyMap_sub, hfg, sub_self]) hji x

/-- Over a complex with zero differentials and projective terms, two chain maps with the same
cohomology maps are equal in the derived category. -/
theorem zbd_Q_map_eq_of_zeroDifferentials [HasDerivedCategory.{w} (ModuleCat.{0} R)]
    {K L : CochainComplex (ModuleCat.{0} R) ℤ} (hK : ∀ i j, K.d i j = 0)
    [∀ n, Module.Projective R (K.X n)] (f g : K ⟶ L)
    (hfg : ∀ n, HomologicalComplex.homologyMap f n = HomologicalComplex.homologyMap g n) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat.{0} R)
    (zbdHomotopyOfZeroDifferentials hK f g hfg)

/-- A graded module with zero differential gives a complex with zero differentials. -/
theorem zbd_complex_d_eq_zero {M : Type} [AddCommGroup M] [Module R M]
    (A : ZbdGradedComplex R M) (hA : A.d = 0) (i j : ℤ) : A.complex.d i j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : A.piece i)
  apply Subtype.ext
  by_cases h : i + 1 = j
  · change (A.dPiece i j x : M) = 0
    rw [A.dPiece_val h, hA, LinearMap.zero_apply]
  · rw [A.complex.shape i j h]

/-- A linear map out of a free module sends the span of a set of basis vectors into a submodule
if it sends those basis vectors into it. -/
theorem zbd_map_mem_of_supported {α M : Type} [AddCommGroup M] [Module R M]
    (f : (α →₀ R) →ₗ[R] M) (s : Set α) (P : Submodule R M)
    (h : ∀ a ∈ s, f (Finsupp.single a 1) ∈ P) {x : α →₀ R}
    (hx : x ∈ Finsupp.supported R R s) : f x ∈ P := by
  rw [Finsupp.supported_eq_span_single] at hx
  refine (Submodule.span_le.mpr ?_ : _ ≤ P.comap f) hx
  rintro _ ⟨a, ha, rfl⟩
  exact h a ha

end ZeroDifferential

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct ProjectiveLine
open ResolutionTools
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

universe w'

variable [HasDerivedCategory.{w'} (ModuleCat.{0} ℂ)]

local instance zbdProductHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **On cohomology, the derived isomorphism is multiplicative**: read through `zbdTorDerivedIso`
and `zbdSheafToDerived`, it sends the standard Tor product to the exterior cohomology product.
This is a statement about the cohomology maps of one morphism of `D(ℂ)`; it is not a
commutative square of products in `D(ℂ)`. -/
theorem zbdDerivedIso_product {p q p' q' : ℕ} (h : p ≤ q) (h' : p' ≤ q')
    (x : G.incidenceTorInternalPiece p q) (y : G.incidenceTorInternalPiece p' q') :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-((p + p' : ℕ) : ℤ))).map
        G.zbdDerivedIso.hom
        ((G.zbdTorDerivedIso (p + p')).hom (G.incidenceTorProduct p p' x.val y.val)) =
      G.zbdSheafToDerived (Nat.sub_add_cancel (Nat.add_le_add h h'))
        (G.exteriorHCast ℂ rfl (by omega : (q - p) + (q' - p') = (q + q') - (p + p'))
          (G.exteriorCohomologyProduct ℂ q q' (q - p) (q' - p')
            (G.incidenceTorExteriorEquiv h x) (G.incidenceTorExteriorEquiv h' y))) := by
  have hx := G.zbdDerivedIso_exterior (Nat.add_le_add h h')
    ⟨G.incidenceTorProduct p p' x.val y.val,
      G.incidenceTorProduct_internal_degree p p' q q' x.property y.property⟩
  rw [G.incidenceTorExteriorEquiv_product h h' x y] at hx
  exact hx

/-- **On cohomology, the derived isomorphism is unital**: the Tor unit goes to the exterior
cohomology unit. -/
theorem zbdDerivedIso_one :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℂ) (-((0 : ℕ) : ℤ))).map G.zbdDerivedIso.hom
        ((G.zbdTorDerivedIso 0).hom G.incidenceTorOne) =
      G.zbdSheafToDerived (Nat.sub_add_cancel (le_refl 0)) (G.exteriorCohomologyUnit ℂ) := by
  have hx := G.zbdDerivedIso_exterior (le_refl 0)
    ⟨G.incidenceTorOne, G.incidenceTorOne_internal_degree⟩
  rw [G.incidenceTorExteriorEquiv_one] at hx
  exact hx

/-! ### The products through the zero-differential state model -/

section StateModel

open Finsupp

/-- The states of homological degree `-i`. -/
abbrev zbdStateSet (i : ℤ) : Set G.IncResolutionBasis := {b | (G.incResolutionDegree b : ℤ) = -i}

/-- The pairs of states of total homological degree `-i`. -/
abbrev zbdPairSet (i : ℤ) : Set (G.IncResolutionBasis × G.IncResolutionBasis) :=
  {e | ((G.incResolutionDegree e.1 + G.incResolutionDegree e.2 : ℕ) : ℤ) = -i}

/-- **The state model** of `ℂ ⊗ F⁻`: the states, graded by `-` homological degree, with zero
differential. -/
abbrev zbdStateGraded : ZbdGradedComplex ℂ (G.IncResolutionBasis →₀ ℂ) where
  piece i := supported ℂ ℂ (G.zbdStateSet i)
  d := 0
  d_mem _ _ _ := Submodule.zero_mem _
  d_d _ := rfl

/-- **The pair model** of `(ℂ ⊗ F⁻) ⊗ (ℂ ⊗ F⁻)`: pairs of states, with zero differential. -/
abbrev zbdPairGraded :
    ZbdGradedComplex ℂ ((G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) where
  piece i := supported ℂ ℂ (G.zbdPairSet i)
  d := 0
  d_mem _ _ _ := Submodule.zero_mem _
  d_d _ := rfl

/-- The specialized standard Tor product on pairs of states: `e_b ⊗ e_b'` goes to the
specialization of the product `incResolutionCup e_b e_b'` of the free resolution. -/
def zbdStateProduct :
    ((G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) →ₗ[ℂ] (G.IncResolutionBasis →₀ ℂ) :=
  linearCombination ℂ fun e =>
    G.zbcFreeSpecialize (G.incResolutionCup (single e.1 1) (single e.2 1))

/-- The specialized Čech–Koszul product of the specialized inclusions:
`e_b ⊗ e_b' ↦ (ι e_b ∪ ι e_b')(0)`, i.e. `∪₀ ∘ (ι₀ ⊗ ι₀)` at the chain level. -/
def zbdPairCup : ((G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) →ₗ[ℂ] ZbcModule V E :=
  linearCombination ℂ fun e => zbcSpecialize
    (G.incTotalCup (G.incResolutionInclusion (single e.1 1))
      (G.incResolutionInclusion (single e.2 1)))

theorem zbdFreeSpecialize_single_one (b : G.IncResolutionBasis) :
    G.zbcFreeSpecialize (single b (1 : IncCoeffRing E)) = single b 1 := by
  rw [zbcFreeSpecialize_apply, mapRange_single, map_one]

theorem zbdStateProduct_mem {i : ℤ} {x : (G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ}
    (hx : x ∈ supported ℂ ℂ (G.zbdPairSet i)) :
    G.zbdStateProduct x ∈ supported ℂ ℂ (G.zbdStateSet i) := by
  refine zbd_map_mem_of_supported _ _ _ (fun e he => ?_) hx
  rw [zbdStateProduct, linearCombination_single, one_smul]
  have h := G.incResolutionCup_degree (G.incResolutionDegree e.1) (G.incResolutionDegree e.2)
    (single_mem_supported _ (1 : IncCoeffRing E) rfl)
    (single_mem_supported _ (1 : IncCoeffRing E) rfl)
  rw [mem_supported']
  intro b hb
  rw [zbcFreeSpecialize_apply, mapRange_apply]
  rw [(mem_supported' _ _).mp h b (fun hb' => hb (by
    change (G.incResolutionDegree b : ℤ) = -i
    rw [← he]
    exact congrArg Nat.cast hb')), map_zero]

theorem zbdStateInclusion_mem {i : ℤ} {x : G.IncResolutionBasis →₀ ℂ}
    (hx : x ∈ supported ℂ ℂ (G.zbdStateSet i)) :
    G.zbcContraction.i x ∈ zbdModelPiece V E (-i) := by
  refine zbd_map_mem_of_supported _ _ _ (fun b hb => ?_) hx
  rw [← G.zbdFreeSpecialize_single_one, ← zbcSpecialize_i]
  have h := G.incCechContraction_i_shifts (G.incResolutionDegree b : ℤ) (single b 1)
    (single_mem_supported _ _ rfl)
  rw [add_zero] at h
  have h' := zbdSpecialize_mem_model h
  rwa [show (G.incResolutionDegree b : ℤ) = -i from hb] at h'

theorem zbdPairCup_mem {i : ℤ} {x : (G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ}
    (hx : x ∈ supported ℂ ℂ (G.zbdPairSet i)) :
    G.zbdPairCup x ∈ zbdModelPiece V E (-i) := by
  refine zbd_map_mem_of_supported _ _ _ (fun e he => ?_) hx
  rw [zbdPairCup, linearCombination_single, one_smul]
  have h := G.incTotalCup_degree _ _
    (G.incResolutionInclusion_degree (G.incResolutionDegree e.1) (single e.1 1)
      (single_mem_supported _ _ rfl))
    (G.incResolutionInclusion_degree (G.incResolutionDegree e.2) (single e.2 1)
      (single_mem_supported _ _ rfl))
  have h' := zbdSpecialize_mem_model h
  have he' : ((G.incResolutionDegree e.1 : ℕ) : ℤ) + (G.incResolutionDegree e.2 : ℕ) = -i := by
    rw [← he]
    push_cast
    ring
  rwa [he'] at h'

/-- The Čech differential kills the specialized products: the Leibniz rule over `S_G`, and the
differential of the minimal resolution vanishes at the origin. -/
theorem zbdPairCup_d (x : (G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) :
    G.zbcContraction.d (G.zbdPairCup x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single e r =>
    rw [zbdPairCup, linearCombination_single, map_smul, ← zbcSpecialize_total,
      G.incTotalCup_leibniz]
    have hI : ∀ z, G.incTotalDifferential (G.incResolutionInclusion z) =
        G.incResolutionInclusion (G.incResolutionDifferential z) :=
      fun z => LinearMap.congr_fun G.incResolutionInclusion_chain z
    rw [hI, hI]
    have h1 := map_mem_ideal_smul_top _
      (G.incTotalCup.flip (G.incResolutionInclusion (single e.2 1)))
      (map_mem_ideal_smul_top _ G.incResolutionInclusion
        (G.incResolutionDifferential_minimal (single e.1 1)))
    have h2 := map_mem_ideal_smul_top _ (G.incTotalCup (incTotalSign (G.incResolutionInclusion
      (single e.1 1))))
      (map_mem_ideal_smul_top _ G.incResolutionInclusion
        (G.incResolutionDifferential_minimal (single e.2 1)))
    rw [LinearMap.flip_apply] at h1
    rw [zbc_map_eq_zero_of_mem zbcSpecialize (Submodule.add_mem _ h1 h2), smul_zero]

/-- The Čech homotopy over `ℂ` raises the total degree by one. -/
theorem zbdContraction_h_mem_model {n : ℤ} {x : ZbcModule V E} (hx : x ∈ zbdModelPiece V E n) :
    G.zbcContraction.h x ∈ zbdModelPiece V E (n + 1) := by
  intro S
  rw [zbcContraction_h_apply]
  have h := contraction_h_degree ℂ (G.deg S) ((S.card : ℤ) - n) (x S) (hx S)
  rwa [show (S.card : ℤ) - n + -1 = (S.card : ℤ) - (n + 1) by ring] at h

/-- The specialized Tor product as a chain map from the pair model to the state model. -/
def zbdStateProductHom : G.zbdPairGraded.complex ⟶ G.zbdStateGraded.complex :=
  G.zbdPairGraded.hom G.zbdStateGraded G.zbdStateProduct (fun _ _ hx => G.zbdStateProduct_mem hx)
    (fun x => by
      change (0 : (G.IncResolutionBasis →₀ ℂ) →ₗ[ℂ] (G.IncResolutionBasis →₀ ℂ)) _ =
        G.zbdStateProduct ((0 : ((G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) →ₗ[ℂ]
          ((G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ)) x)
      rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero])

/-- The specialized inclusion `ι₀ = zbcContraction.i` as a chain map from the state model to the
model of `C₀`. -/
def zbdStateInclusionHom : G.zbdStateGraded.complex ⟶ G.zbdModelComplex :=
  G.zbdStateGraded.hom G.zbdModelGraded G.zbcContraction.i
    (fun _ _ hx => G.zbdStateInclusion_mem hx)
    (fun x => by
      change G.zbcContraction.d (G.zbcContraction.i x) =
        G.zbcContraction.i ((0 : (G.IncResolutionBasis →₀ ℂ) →ₗ[ℂ] _) x)
      rw [LinearMap.zero_apply, map_zero]
      exact LinearMap.congr_fun G.zbcContraction.d_i x)

/-- The specialized Čech–Koszul product `∪₀ ∘ (ι₀ ⊗ ι₀)` as a chain map from the pair model to
the model of `C₀`. -/
def zbdPairCupHom : G.zbdPairGraded.complex ⟶ G.zbdModelComplex :=
  G.zbdPairGraded.hom G.zbdModelGraded G.zbdPairCup (fun _ _ hx => G.zbdPairCup_mem hx)
    (fun x => by
      change G.zbcContraction.d (G.zbdPairCup x) =
        G.zbdPairCup ((0 : _ →ₗ[ℂ] (G.IncResolutionBasis × G.IncResolutionBasis →₀ ℂ)) x)
      rw [LinearMap.zero_apply, map_zero]
      exact G.zbdPairCup_d x)

/-- On a pair of states, the specialized Tor product included by `ι₀` differs from the Čech
product of the inclusions by a boundary: the Tor product is `p₀ ∘ ∪₀ ∘ (ι₀ ⊗ ι₀)` at the origin
(`zbcFreeSpecialize_projection`), and `ι₀ p₀ = 1 - d h - h d` (the Čech contraction). -/
theorem zbdStateProduct_inclusion (x : (G.IncResolutionBasis × G.IncResolutionBasis) →₀ ℂ) :
    G.zbcContraction.i (G.zbdStateProduct x) - G.zbdPairCup x =
      G.zbcContraction.d (-G.zbcContraction.h (G.zbdPairCup x)) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, sub_zero, neg_zero]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, add_sub_add_comm, hx, hy, map_add, neg_add, map_add]
  | single e r =>
    rw [zbdStateProduct, zbdPairCup, linearCombination_single, linearCombination_single, map_smul,
      map_smul, ← smul_neg, map_smul, ← smul_sub]
    congr 1
    set c := zbcSpecialize (G.incTotalCup (G.incResolutionInclusion (single e.1 1))
      (G.incResolutionInclusion (single e.2 1))) with hc
    have hdc : G.zbcContraction.d c = 0 := by
      have h := G.zbdPairCup_d (single e 1)
      rwa [zbdPairCup, linearCombination_single, one_smul] at h
    have hp : G.zbcFreeSpecialize (G.incResolutionCup (single e.1 1) (single e.2 1)) =
        G.zbcContraction.p c := by
      rw [incResolutionCup_apply, zbcFreeSpecialize_projection]
    have hh := LinearMap.congr_fun G.zbcContraction.homotopy c
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.comp_apply,
      Module.End.one_apply, hdc, map_zero, add_zero] at hh
    rw [hp, map_neg]
    calc G.zbcContraction.i (G.zbcContraction.p c) - c
        = (G.zbcContraction.d (G.zbcContraction.h c) + G.zbcContraction.i (G.zbcContraction.p c))
          - G.zbcContraction.d (G.zbcContraction.h c) - c := by abel
      _ = -G.zbcContraction.d (G.zbcContraction.h c) := by rw [hh]; abel

/-- **The two products agree in `D(ℂ)`, through the common zero-differential state model.** In
`DerivedCategory (ModuleCat ℂ)`, the specialized standard Tor product `μ₀` (pairs of states to
states) followed by the specialized inclusion `ι₀` equals the specialized Čech–Koszul product
of the inclusions, `∪₀ ∘ (ι₀ ⊗ ι₀)`. The proof is an explicit homotopy: the difference is the
boundary of `-h₀ ∘ ∪₀ ∘ (ι₀ ⊗ ι₀)` (`zbdStateProduct_inclusion`), and the source has zero
differential and free terms (`zbdHomotopyOfRange`). -/
theorem zbdProductSquare :
    DerivedCategory.Q.map G.zbdStateProductHom ≫ DerivedCategory.Q.map G.zbdStateInclusionHom =
      DerivedCategory.Q.map G.zbdPairCupHom := by
  rw [← Functor.map_comp]
  apply DerivedCategory.Q_map_eq_of_homotopy (C := ModuleCat.{0} ℂ)
  refine zbdHomotopyOfRange (zbd_complex_d_eq_zero _ rfl) _ _ ?_
  intro i j hji x
  have hx := Subtype.property (p := (· ∈ supported ℂ ℂ (G.zbdPairSet i))) x
  refine ⟨⟨-G.zbcContraction.h (G.zbdPairCup
    (Subtype.val (p := (· ∈ supported ℂ ℂ (G.zbdPairSet i))) x)), ?_⟩, ?_⟩
  · have h := G.zbdContraction_h_mem_model (G.zbdPairCup_mem hx)
    rw [show -i + 1 = -j by omega] at h
    exact neg_mem h
  · apply Subtype.ext
    refine (ZbdGradedComplex.complex_d_val G.zbdModelGraded hji _).trans ?_
    exact (G.zbdStateProduct_inclusion _).symm

section StateIso

local instance zbdStateOriginAlgebra : Algebra (IncCoeffRing E) ℂ := (zbcOrigin E).toAlgebra

/-- The base change of the free module on the states is the free `ℂ`-module on the states. -/
def zbdFreeBaseChangeEquiv :
    ℂ ⊗[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E) ≃ₗ[ℂ]
      (G.IncResolutionBasis →₀ ℂ) :=
  TensorProduct.finsuppScalarRight (IncCoeffRing E) ℂ ℂ G.IncResolutionBasis

theorem zbdFreeBaseChangeEquiv_tmul (c : ℂ) (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.zbdFreeBaseChangeEquiv (c ⊗ₜ y) = c • G.zbcFreeSpecialize y := by
  ext b
  rw [zbdFreeBaseChangeEquiv, TensorProduct.finsuppScalarRight_apply_tmul_apply,
    Finsupp.smul_apply, zbcFreeSpecialize_apply, mapRange_apply, Algebra.smul_def, smul_eq_mul,
    mul_comm]
  rfl

/-- The projection of the free module onto the states of degree `n`. -/
def zbdStateRetraction (n : ℤ) :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E] G.incResolutionPiece n :=
  restrictDom (IncCoeffRing E) (IncCoeffRing E) {b | (G.incResolutionDegree b : ℤ) = n}

theorem zbdStateRetraction_apply (n : ℤ) (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    (G.zbdStateRetraction n y : G.IncResolutionBasis →₀ IncCoeffRing E) =
      Finsupp.filter (· ∈ {b | (G.incResolutionDegree b : ℤ) = n}) y := rfl

theorem zbdFreeSpecialize_stateRetraction (n : ℤ) (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.zbcFreeSpecialize (G.zbdStateRetraction n y : G.IncResolutionBasis →₀ IncCoeffRing E) =
      Finsupp.filter (· ∈ {b | (G.incResolutionDegree b : ℤ) = n}) (G.zbcFreeSpecialize y) := by
  ext b
  rw [zbcFreeSpecialize_apply, mapRange_apply, zbdStateRetraction_apply,
    Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem zbdFreeSpecialize_mem {n : ℤ} {y : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hy : y ∈ G.incResolutionPiece n) :
    G.zbcFreeSpecialize y ∈ supported ℂ ℂ {b | (G.incResolutionDegree b : ℤ) = n} := by
  rw [mem_supported']
  intro b hb
  rw [zbcFreeSpecialize_apply, mapRange_apply, (mem_supported' _ _).mp hy b hb, map_zero]

theorem zbdFreeBaseChangeEquiv_subtype_mem (n : ℤ)
    (t : ℂ ⊗[IncCoeffRing E] G.incResolutionPiece n) :
    G.zbdFreeBaseChangeEquiv ((G.incResolutionPiece n).subtype.baseChange ℂ t) ∈
      supported ℂ ℂ {b | (G.incResolutionDegree b : ℤ) = n} := by
  induction t using TensorProduct.inductionOn with
  | tmul c y =>
    rw [LinearMap.baseChange_tmul, zbdFreeBaseChangeEquiv_tmul]
    exact Submodule.smul_mem _ c (G.zbdFreeSpecialize_mem y.2)
  | add s t hs ht => rw [map_add, map_add]; exact Submodule.add_mem _ hs ht

/-- The base change of a piece of `F⁻` is the piece of the state model. -/
def zbdStatePieceEquiv (n : ℤ) :
    ℂ ⊗[IncCoeffRing E] G.incResolutionPiece n ≃ₗ[ℂ]
      supported ℂ ℂ {b : G.IncResolutionBasis | (G.incResolutionDegree b : ℤ) = n} :=
  LinearEquiv.ofLinearMap
    (LinearMap.codRestrict _ (G.zbdFreeBaseChangeEquiv.toLinearMap ∘ₗ
      (G.incResolutionPiece n).subtype.baseChange ℂ) (G.zbdFreeBaseChangeEquiv_subtype_mem n))
    ((G.zbdStateRetraction n).baseChange ℂ ∘ₗ G.zbdFreeBaseChangeEquiv.symm.toLinearMap ∘ₗ
      (supported ℂ ℂ {b : G.IncResolutionBasis | (G.incResolutionDegree b : ℤ) = n}).subtype)
    (by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change G.zbdFreeBaseChangeEquiv ((G.incResolutionPiece n).subtype.baseChange ℂ
        ((G.zbdStateRetraction n).baseChange ℂ (G.zbdFreeBaseChangeEquiv.symm z.val))) = z.val
      have key : ∀ t : ℂ ⊗[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E),
          G.zbdFreeBaseChangeEquiv ((G.incResolutionPiece n).subtype.baseChange ℂ
            ((G.zbdStateRetraction n).baseChange ℂ t)) =
          Finsupp.filter (· ∈ {b | (G.incResolutionDegree b : ℤ) = n})
            (G.zbdFreeBaseChangeEquiv t) := by
        intro t
        induction t using TensorProduct.inductionOn with
        | tmul c y =>
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, zbdFreeBaseChangeEquiv_tmul,
            zbdFreeBaseChangeEquiv_tmul, Finsupp.filter_smul]
          congr 1
          exact G.zbdFreeSpecialize_stateRetraction n y
        | add s t hs ht => rw [map_add, map_add, map_add, hs, ht, map_add, Finsupp.filter_add]
      rw [key, LinearEquiv.apply_symm_apply]
      exact (Finsupp.filter_eq_self_iff _ _).mpr fun b hb => by
        by_contra h
        exact hb ((mem_supported' ℂ _).mp z.2 b h))
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro c y
      change (G.zbdStateRetraction n).baseChange ℂ (G.zbdFreeBaseChangeEquiv.symm
        (G.zbdFreeBaseChangeEquiv ((G.incResolutionPiece n).subtype.baseChange ℂ (c ⊗ₜ y)))) =
          c ⊗ₜ y
      rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      exact LinearMap.congr_fun (restrictDom_comp_subtype (M := IncCoeffRing E)
        (R := IncCoeffRing E) {b | (G.incResolutionDegree b : ℤ) = n}) y)

theorem zbdStatePieceEquiv_tmul (n : ℤ) (c : ℂ) (y : G.incResolutionPiece n) :
    (G.zbdStatePieceEquiv n (c ⊗ₜ y) : G.IncResolutionBasis →₀ ℂ) =
      c • G.zbcFreeSpecialize y.val := by
  change G.zbdFreeBaseChangeEquiv ((G.incResolutionPiece n).subtype.baseChange ℂ (c ⊗ₜ y)) = _
  rw [LinearMap.baseChange_tmul, zbdFreeBaseChangeEquiv_tmul]
  rfl

/-- The components of the identification of `ℂ ⊗ F⁻` with the state model. -/
def zbdStateIsoApp (i : ℤ) : G.zbdResolutionComplexC.X i ≅ G.zbdStateGraded.complex.X i :=
  (G.zbdStatePieceEquiv (-i)).toModuleIso

/-- **`ℂ ⊗ F⁻` is the state model**: both have zero differentials, and in each degree the base
change of the free module on the states is the free `ℂ`-module on the states. -/
def zbdStateIso : G.zbdResolutionComplexC ≅ G.zbdStateGraded.complex :=
  HomologicalComplex.Hom.isoOfComponents G.zbdStateIsoApp (by
    intro i j _
    rw [G.zbdResolutionComplexC_d, zbd_complex_d_eq_zero _ rfl, Limits.comp_zero,
      Limits.zero_comp])

/-- Under the identification with the state model, the base change of `ι` followed by the model
isomorphism is the specialized inclusion `ι₀ = zbcContraction.i` (`zbcSpecialize_inclusion`). -/
theorem zbdStateIso_inclusion :
    G.zbdStateIso.hom ≫ G.zbdStateInclusionHom =
      G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom := by
  ext i : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  have key : G.zbdStateGraded.homPiece G.zbdModelGraded G.zbcContraction.i
        (fun _ _ hx => G.zbdStateInclusion_mem hx) i ∘ₗ
        (G.zbdStatePieceEquiv (-i)).toLinearMap =
      (zbdPieceEquiv (V := V) (E := E) (-i)).toLinearMap ∘ₗ
        (G.zbdResolutionGraded.homPiece G.zbdTotalGraded G.incResolutionInclusion
          (fun j x hx => by
            have h := G.incResolutionInclusion_shifts (-j) x hx
            rw [add_zero] at h
            exact h) i).baseChange ℂ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c y
    apply Subtype.ext
    change G.zbcContraction.i (G.zbdStatePieceEquiv (-i) (c ⊗ₜ y) : G.IncResolutionBasis →₀ ℂ) =
      (zbdPieceEquiv (V := V) (E := E) (-i) (c ⊗ₜ (G.zbdResolutionGraded.homPiece
        G.zbdTotalGraded G.incResolutionInclusion _ i y)) : ZbcModule V E)
    rw [zbdStatePieceEquiv_tmul, zbdPieceEquiv_tmul, map_smul]
    exact congrArg (c • ·) (G.zbcSpecialize_inclusion y.val).symm
  exact key

end StateIso

section Derived

/-- **The product comparison in `D(ℂ)`.** The specialized standard Tor product on the state model
(the specialization of the multiplication lift `incResolutionCup`, which computes
`incidenceTorProduct` by `incidenceTorProduct_eq_transferred`), followed by the identification of
the state model with `ℂ ⊗ F⁻` and the derived base-change isomorphism, equals the specialized
Čech–Koszul product of the specialized inclusions `∪₀ ∘ (ι₀ ⊗ ι₀)`, as morphisms
`Q(pair model) ⟶ Q(model of C₀)` in `DerivedCategory (ModuleCat ℂ)`. -/
theorem zbdDerivedProduct :
    DerivedCategory.Q.map G.zbdStateProductHom ≫ DerivedCategory.Q.map G.zbdStateIso.inv ≫
        G.zbdDerivedModelIso.hom =
      DerivedCategory.Q.map G.zbdPairCupHom := by
  have h : DerivedCategory.Q.map G.zbdStateIso.inv ≫ G.zbdDerivedModelIso.hom =
      DerivedCategory.Q.map G.zbdStateInclusionHom := by
    rw [zbdDerivedModelIso_hom, ← Functor.map_comp, ← zbdStateIso_inclusion, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [h, zbdProductSquare]

end Derived

end StateModel

end

end BPFixedPoints.Multigraph
