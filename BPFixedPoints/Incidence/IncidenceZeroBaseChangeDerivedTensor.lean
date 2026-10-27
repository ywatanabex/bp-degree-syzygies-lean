import BPFixedPoints.Incidence.IncidenceZeroBaseChangeDerivedProduct

/-! # The derived product through Mathlib's tensor product of complexes

`IncidenceZeroBaseChangeDerivedProduct` compares the two products in `D(ℂ)` out of a hand-made pair
model (the free `ℂ`-module on pairs of states with zero differential). This file identifies that
pair model with Mathlib's monoidal tensor product `tensorObj` of the state model with itself
(`zbdPairTensorIso`), defines the specialized Čech–Koszul product `∪₀` as a chain map out of
Mathlib's tensor product `C₀ ⊗ C₀` of the base-changed model (`zbdModelCupHom`, with the Leibniz
rule for the signs of `ComplexShape.up ℤ`), and proves that the derived base-change isomorphism
is multiplicative for these products, as a commutative square in `D(ℂ)` whose source is the
monoidal tensor product (`zbdDerivedTensorProduct`).

* **The product over `ℂ`.** `zbcTotalCup` is `incTotalCup` with coefficients in `ℂ`, and
  specialization at the coefficient origin is multiplicative (`zbcSpecialize_totalCup`). Its
  Leibniz rule over `ℂ` (`zbcTotalCup_leibniz`) is deduced from the one over `S_G` through the
  surjective specialization, and the sign operator `zbcSign` is `(-1)^i` on cohomological
  degree `i` (`zbcSign_degree`), the sign `ε` of `ComplexShape.up ℤ`.
* **The pair model is the tensor product.** `zbdPairTensorHom : S ⊗ S ⟶ pair` sends a summand
  `S.X i₁ ⊗ S.X i₂` to pairs of states by `finsuppTensorFinsupp'`, with inverse
  `zbdPairTensorInv` on the pair basis; both complexes have zero differentials.
* **The product on `C₀ ⊗ C₀`.** `zbdModelCupHom : C₀ ⊗ C₀ ⟶ C₀` is `∪₀` on every summand; the
  chain-map property is the Leibniz rule with the signs `ε₁ = 1`, `ε₂ = (-1)^{i₁}` of
  `mapBifunctor`.
* **The comparison.** `zbdPairCupHom = zbdPairTensorHom ≫ (ι₀ ⊗ ι₀) ≫ ∪₀` at the chain level
  (`zbdPairTensorHom_cup`), so the square of `zbdProductSquare` becomes a square out of
  `S ⊗ S`: `Q(μ) ≫ Q(ι₀) = Q(ι₀ ⊗ ι₀) ≫ Q(∪₀)` with `μ = zbdPairTensorIso.hom ≫ μ₀`
  (`zbdTensorProductSquare`). Transported along `zbdStateIso` this is the statement for
  `ℂ ⊗ F⁻` itself: the product `zbdResolutionProductC` on `ℂ ⊗ F⁻` and the derived base-change
  isomorphism `zbdDerivedModelIso` satisfy `Q(μ) ≫ iso = Q(β ⊗ β) ≫ Q(∪₀)` where `β` is the
  base change of `ι` followed by the model isomorphism (`zbdDerivedTensorProduct`).

The right side `RΓ(X_G, ⊕_q ∧^q F_G^∨[q])` is represented by its Čech model `C₀`, as everywhere in
the derived base change.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

section TensorZero

variable {R : Type} [CommRing R]

/-- The tensor product of two complexes with zero differentials has zero differentials. -/
theorem zbd_tensorObj_d_eq_zero {K L : CochainComplex (ModuleCat.{0} R) ℤ}
    (hK : ∀ i j, K.d i j = 0) (hL : ∀ i j, L.d i j = 0) (i j : ℤ) :
    (HomologicalComplex.tensorObj K L).d i j = 0 := by
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, comp_zero,
    mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel i₁ (i₁ + 1) from rfl),
    mapBifunctor.d₂_eq' _ _ _ _ i₁ (show (ComplexShape.up ℤ).Rel i₂ (i₂ + 1) from rfl), hK, hL]
  simp

/-- Linear maps out of a supported submodule are determined by the basis vectors. -/
theorem zbd_supported_ext {α N : Type} [AddCommGroup N] [Module R N] (s : Set α)
    (f g : Finsupp.supported R R s →ₗ[R] N)
    (h : ∀ a (ha : a ∈ s), f ⟨Finsupp.single a 1, Finsupp.single_mem_supported R 1 ha⟩ =
      g ⟨Finsupp.single a 1, Finsupp.single_mem_supported R 1 ha⟩) : f = g := by
  classical
  have key : f ∘ₗ (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm.toLinearMap =
      g ∘ₗ (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm.toLinearMap := by
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    have e : (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm (Finsupp.single a 1) =
        ⟨Finsupp.single (a : α) 1, Finsupp.single_mem_supported R 1 a.2⟩ :=
      Subtype.ext (Finsupp.supportedEquivFinsupp_symm_single s a 1)
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearEquiv.coe_coe, e]
    exact h a a.2
  apply LinearMap.ext
  intro x
  have := LinearMap.congr_fun key (Finsupp.supportedEquivFinsupp s x)
  simpa using this

/-- A ring homomorphism applied coefficientwise is semilinear for scalars. -/
theorem zbd_mapRange_smul {α R' : Type} [CommRing R'] (f : R →+* R') (r : R) (v : α →₀ R) :
    Finsupp.mapRange f (map_zero f) (r • v) = f r • Finsupp.mapRange f (map_zero f) v := by
  ext a
  simp [Finsupp.mapRange_apply, Finsupp.smul_apply]

end TensorZero

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CechProduct ResolutionTools Finsupp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

universe w'

variable [HasDerivedCategory.{w'} (ModuleCat.{0} ℂ)]

/-! ### The Čech–Koszul product over `ℂ` -/

/-- The coefficient of the product over `ℂ`: the Čech chain cup with the parity sign of the left
exterior degree (`incCupCoefficient` at the coefficient origin). -/
def zbcCupCoefficient (S T : Finset E) :
    CechProduct.C ℂ V →ₗ[ℂ] CechProduct.C ℂ V →ₗ[ℂ] CechProduct.C ℂ V :=
  (chainCup ℂ (G.deg S) (G.deg T)).compl₂ (parity ℂ ^ S.card)

/-- The Čech–Koszul product on the base-changed model over `ℂ` (`incTotalCup` at the origin). -/
def zbcTotalCup : ZbcModule V E →ₗ[ℂ] ZbcModule V E →ₗ[ℂ] ZbcModule V E :=
  Finsupp.lsum ℂ fun S => (Finsupp.lsum ℂ).comp
    (LinearMap.pi fun T => (G.zbcCupCoefficient S T).compr₂ (Koszul.wedgeSingle (R := ℂ) S T))

theorem zbcTotalCup_single (S T : Finset E) (x y : CechProduct.C ℂ V) :
    G.zbcTotalCup (single S x) (single T y) =
      Koszul.wedgeSingle (R := ℂ) S T (G.zbcCupCoefficient S T x y) := by
  simp [zbcTotalCup]

theorem zbcSpecialize_single (S : Finset E) (c : IncCechModule (V := V) (E := E)) :
    zbcSpecialize (single S c) = single S (mapRange (zbcOrigin E) (map_zero _) c) := by
  apply Finsupp.ext
  intro T
  rw [zbcSpecialize_apply]
  by_cases h : S = T
  · subst h
    rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne' h, single_eq_of_ne' h, mapRange_zero]

/-- Specialization at the coefficient origin is surjective: lift the coefficients as constants. -/
theorem zbcSpecialize_surjective : Function.Surjective (zbcSpecialize (V := V) (E := E)) := by
  intro y
  refine ⟨mapRange (fun c : CechProduct.C ℂ V =>
    (mapRange MvPolynomial.C (map_zero _) c : IncCechModule (V := V) (E := E))) (by simp) y, ?_⟩
  ext S b
  simp [zbcSpecialize_apply, mapRange_apply, zbcOrigin]

theorem zbc_parity_pow_mapRange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ)
    (x : CechProduct.C R V) :
    (parity R' ^ n) (mapRange f (map_zero f) x) = mapRange f (map_zero f) ((parity R ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Module.End.mul_apply]
    have hp : parity R' (mapRange f (map_zero f) x) = mapRange f (map_zero f) (parity R x) :=
      contraction_sign_mapRange f 0 x
    rw [hp, ih]

theorem zbcSpecialize_cupCoefficient (S T : Finset E) (x y : IncCechModule (V := V) (E := E)) :
    mapRange (zbcOrigin E) (map_zero _) (G.incCupCoefficient S T x y) =
      G.zbcCupCoefficient S T (mapRange (zbcOrigin E) (map_zero _) x)
        (mapRange (zbcOrigin E) (map_zero _) y) := by
  simp only [incCupCoefficient, zbcCupCoefficient, LinearMap.compl₂_apply]
  rw [zbc_parity_pow_mapRange, chainCup_mapRange]

theorem zbcSpecialize_wedgeSingle (S T : Finset E) (w : IncCechModule (V := V) (E := E)) :
    zbcSpecialize (Koszul.wedgeSingle (R := IncCoeffRing E) S T w) =
      Koszul.wedgeSingle (R := ℂ) S T (mapRange (zbcOrigin E) (map_zero _) w) := by
  rw [Koszul.wedgeSingle_apply, Koszul.wedgeSingle_apply]
  split_ifs
  · rw [← smul_single, ← smul_single, map_smulₛₗ, zbcSpecialize_single]
    congr 1
    simp [Koszul.shuffleSign]
  · exact map_zero _

/-- **Specialization is multiplicative**: `incTotalCup` at the coefficient origin is `zbcTotalCup`. -/
theorem zbcSpecialize_totalCup (x y : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (G.incTotalCup x y) = G.zbcTotalCup (zbcSpecialize x) (zbcSpecialize y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single S c =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single T c' =>
      rw [G.incTotalCup_single, zbcSpecialize_wedgeSingle, zbcSpecialize_single,
        zbcSpecialize_single, G.zbcTotalCup_single, zbcSpecialize_cupCoefficient]

theorem zbd_single_mem_model {n : ℤ} (S : Finset E) {w : CechProduct.C ℂ V}
    (hw : w ∈ supported ℂ ℂ (zbdSlot V S n)) : single S w ∈ zbdModelPiece V E n := by
  intro T
  by_cases h : S = T
  · subst h
    rw [single_eq_same]
    exact hw
  · rw [single_eq_of_ne' h]
    exact Submodule.zero_mem _

theorem zbcCupCoefficient_degree (S T : Finset E) (p q : ℤ) {x y : CechProduct.C ℂ V}
    (hx : x ∈ supported ℂ ℂ {b | (cechDegree b : ℤ) = p})
    (hy : y ∈ supported ℂ ℂ {b | (cechDegree b : ℤ) = q}) :
    G.zbcCupCoefficient S T x y ∈ supported ℂ ℂ {b | (cechDegree b : ℤ) = p + q} := by
  apply chainCup_degree _ _ _ p q hx
  have h : HasDegree (fun b => (cechDegree b : ℤ)) (fun b => (cechDegree b : ℤ)) 0
      (parity ℂ (V := V)) := by
    apply HasDegree.of_single
    intro b r
    rw [parity, contraction_sign_single]
    exact Submodule.smul_mem _ _ (single_mem_supported _ _ (by simp))
  simpa only [add_zero] using h.pow_zero S.card q y hy

/-- The product over `ℂ` adds total degrees. -/
theorem zbcTotalCup_degree (p q : ℤ) {x y : ZbcModule V E}
    (hx : x ∈ zbdModelPiece V E p) (hy : y ∈ zbdModelPiece V E q) :
    G.zbcTotalCup x y ∈ zbdModelPiece V E (p + q) := by
  rw [← x.sum_single, map_finsuppSum, Finsupp.sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro S _
  rw [← y.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro T _
  dsimp only
  rw [G.zbcTotalCup_single, Koszul.wedgeSingle_apply]
  by_cases h : Disjoint S T
  · rw [ite_eq_left h]
    apply zbd_single_mem_model
    apply Submodule.smul_mem
    have hdeg := G.zbcCupCoefficient_degree S T ((S.card : ℤ) - p) ((T.card : ℤ) - q)
      (hx S) (hy T)
    have he : ((S ∪ T).card : ℤ) - (p + q) = ((S.card : ℤ) - p) + ((T.card : ℤ) - q) := by
      rw [Finset.card_union_of_disjoint h, Nat.cast_add]; ring
    simpa only [zbdSlot, he] using hdeg
  · rw [ite_eq_right h]
    exact Submodule.zero_mem _

/-- The sign operator of the product over `ℂ`: `(-1)^{|S|}` times the Čech parity on the
`S`-component (`incTotalSign` at the origin). -/
def zbcSign : Module.End ℂ (ZbcModule V E) :=
  Koszul.diagonal fun S => (-1 : ℂ) ^ S.card • parity ℂ

@[simp] theorem zbcSign_single (S : Finset E) (x : CechProduct.C ℂ V) :
    zbcSign (single S x) = single S ((-1 : ℂ) ^ S.card • parity ℂ x) := by
  simp [zbcSign]

theorem zbcSpecialize_sign (x : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (incTotalSign x) = zbcSign (zbcSpecialize x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single S c =>
    rw [incTotalSign_single, zbcSpecialize_single, zbcSpecialize_single, zbcSign_single,
      zbd_mapRange_smul]
    have hp : mapRange (zbcOrigin E) (map_zero _) (parity (IncCoeffRing E) c) =
        parity ℂ (mapRange (zbcOrigin E) (map_zero _) c) :=
      (contraction_sign_mapRange (zbcOrigin E) 0 c).symm
    rw [hp]
    simp

theorem zbd_neg_one_pow_mul (a b : ℕ) (i : ℤ) (h : (b : ℤ) = a + i) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b = ((i.negOnePow : ℤ) : ℂ) := by
  have h1 : ((a + b : ℕ) : ℤ).negOnePow = i.negOnePow := by
    rw [Int.negOnePow_eq_iff]
    exact ⟨a, by push_cast; omega⟩
  rw [← pow_add, ← h1, Int.coe_negOnePow_natCast]
  push_cast
  rfl

/-- On cohomological degree `i` the sign operator is `(-1)^i`, the sign of `ComplexShape.up ℤ`. -/
theorem zbcSign_degree {i : ℤ} {x : ZbcModule V E} (hx : x ∈ zbdModelPiece V E (-i)) :
    zbcSign x = ((i.negOnePow : ℤ) : ℂ) • x := by
  rw [← x.sum_single, map_finsuppSum]
  simp only [Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [zbcSign_single, smul_single]
  congr 1
  have hS := hx S
  rw [← (x S).sum_single, map_finsuppSum]
  simp only [Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := (mem_supported ℂ (x S)).mp hS hb
  rw [parity, contraction_sign_single, smul_smul]
  congr 1
  exact zbd_neg_one_pow_mul S.card (cechDegree b) i
    (by simp only [zbdSlot, Set.mem_ofPred_eq] at hb'; omega)

/-- **The Leibniz rule over `ℂ`**, deduced from the one over `S_G` through the surjective
specialization. -/
theorem zbcTotalCup_leibniz (x y : ZbcModule V E) :
    G.zbcContraction.d (G.zbcTotalCup x y) =
      G.zbcTotalCup (G.zbcContraction.d x) y +
        G.zbcTotalCup (zbcSign x) (G.zbcContraction.d y) := by
  obtain ⟨x, rfl⟩ := zbcSpecialize_surjective x
  obtain ⟨y, rfl⟩ := zbcSpecialize_surjective y
  rw [← G.zbcSpecialize_totalCup, ← zbcSpecialize_total G, G.incTotalCup_leibniz, map_add,
    G.zbcSpecialize_totalCup, G.zbcSpecialize_totalCup, zbcSpecialize_total G,
    zbcSpecialize_total G, zbcSpecialize_sign]

/-! ### The product `∪₀` as a chain map out of Mathlib's tensor product `C₀ ⊗ C₀` -/

/-- The bilinear product on the terms of the model, landing in the term of the sum of the
degrees. -/
def zbdModelCupBilinear (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    G.zbdModelComplex.X i₁ →ₗ[ℂ] G.zbdModelComplex.X i₂ →ₗ[ℂ] G.zbdModelComplex.X j :=
  LinearMap.mk₂ ℂ
    (fun x y => (⟨G.zbcTotalCup (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x)
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y), by
          have := G.zbcTotalCup_degree (-i₁) (-i₂)
            (Subtype.property (p := (· ∈ zbdModelPiece V E (-i₁))) x)
            (Subtype.property (p := (· ∈ zbdModelPiece V E (-i₂))) y)
          rwa [show -i₁ + -i₂ = -j by omega] at this⟩ : zbdModelPiece V E (-j)))
    (fun x x' y => Subtype.ext (by
      change G.zbcTotalCup (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x +
        Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x') _ =
        G.zbcTotalCup _ _ + G.zbcTotalCup _ _
      rw [map_add, LinearMap.add_apply]))
    (fun c x y => Subtype.ext (by
      change G.zbcTotalCup (c • Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x) _ =
        c • G.zbcTotalCup _ _
      rw [map_smul, LinearMap.smul_apply]))
    (fun x y y' => Subtype.ext (by
      change G.zbcTotalCup _ (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y +
        Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y') =
        G.zbcTotalCup _ _ + G.zbcTotalCup _ _
      rw [map_add]))
    (fun c x y => Subtype.ext (by
      change G.zbcTotalCup _ (c • Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y) =
        c • G.zbcTotalCup _ _
      rw [map_smul]))

theorem zbdModelCupBilinear_val (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) (x : G.zbdModelComplex.X i₁)
    (y : G.zbdModelComplex.X i₂) :
    Subtype.val (p := (· ∈ zbdModelPiece V E (-j))) (G.zbdModelCupBilinear i₁ i₂ j h x y) =
      G.zbcTotalCup (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x)
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y) := rfl

/-- The product on the summand `C₀.X i₁ ⊗ C₀.X i₂` of `(C₀ ⊗ C₀).X j`. -/
def zbdModelCupPiece (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    G.zbdModelComplex.X i₁ ⊗ G.zbdModelComplex.X i₂ ⟶ G.zbdModelComplex.X j :=
  ModuleCat.ofHom (TensorProduct.lift (G.zbdModelCupBilinear i₁ i₂ j h))

theorem zbdModelCupPiece_tmul (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) (x : G.zbdModelComplex.X i₁)
    (y : G.zbdModelComplex.X i₂) :
    (G.zbdModelCupPiece i₁ i₂ j h).hom (x ⊗ₜ y) = G.zbdModelCupBilinear i₁ i₂ j h x y := rfl

/-- The component of `∪₀` on `(C₀ ⊗ C₀).X j`. -/
def zbdModelCupF (j : ℤ) :
    (HomologicalComplex.tensorObj G.zbdModelComplex G.zbdModelComplex).X j ⟶
      G.zbdModelComplex.X j :=
  mapBifunctorDesc fun i₁ i₂ h => G.zbdModelCupPiece i₁ i₂ j h

/-- The Leibniz rule with the signs `ε₁ = 1`, `ε₂ = (-1)^{i₁}` of `mapBifunctor`: `∪₀` commutes
with the differentials. -/
theorem zbdModelCupF_comm (i j : ℤ) (hij : i + 1 = j) :
    G.zbdModelCupF i ≫ G.zbdModelComplex.d i j =
      (HomologicalComplex.tensorObj G.zbdModelComplex G.zbdModelComplex).d i j ≫
        G.zbdModelCupF j := by
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  change i₁ + i₂ = i at h
  rw [← Category.assoc, ← Category.assoc, zbdModelCupF, ι_mapBifunctorDesc, mapBifunctor.d_eq,
    Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel i₁ (i₁ + 1) from rfl) i₂ j
      (show i₁ + 1 + i₂ = j by omega),
    mapBifunctor.d₂_eq _ _ _ _ i₁ (show (ComplexShape.up ℤ).Rel i₂ (i₂ + 1) from rfl) j
      (show i₁ + (i₂ + 1) = j by omega),
    Preadditive.add_comp, Units.smul_def, Units.smul_def, Preadditive.zsmul_comp,
    Preadditive.zsmul_comp, Category.assoc, Category.assoc, zbdModelCupF, ι_mapBifunctorDesc,
    ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  apply Subtype.ext
  change Subtype.val (p := (· ∈ zbdModelPiece V E (-j)))
      (G.zbdModelComplex.d i j (G.zbdModelCupBilinear i₁ i₂ i h x y)) =
    ((1 : ℤˣ) : ℤ) • G.zbcTotalCup
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-(i₁ + 1))))
          (G.zbdModelComplex.d i₁ (i₁ + 1) x))
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₂))) y) +
      ((i₁.negOnePow : ℤˣ) : ℤ) • G.zbcTotalCup
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-i₁))) x)
        (Subtype.val (p := (· ∈ zbdModelPiece V E (-(i₂ + 1))))
          (G.zbdModelComplex.d i₂ (i₂ + 1) y))
  rw [ZbdGradedComplex.complex_d_val G.zbdModelGraded hij,
    ZbdGradedComplex.complex_d_val G.zbdModelGraded rfl,
    ZbdGradedComplex.complex_d_val G.zbdModelGraded rfl, zbdModelCupBilinear_val, Units.val_one,
    one_smul, G.zbcTotalCup_leibniz,
    zbcSign_degree (Subtype.property (p := (· ∈ zbdModelPiece V E (-i₁))) x), map_smul,
    LinearMap.smul_apply, Int.cast_smul_eq_zsmul]

/-- **The product `∪₀` as a chain map `C₀ ⊗ C₀ ⟶ C₀`** for Mathlib's tensor product of
complexes. -/
def zbdModelCupHom :
    HomologicalComplex.tensorObj G.zbdModelComplex G.zbdModelComplex ⟶ G.zbdModelComplex where
  f j := G.zbdModelCupF j
  comm' i j hij := G.zbdModelCupF_comm i j hij

/-! ### The pair model is the tensor product of the state model with itself -/

theorem zbdPairTensor_mem {i₁ i₂ j : ℤ} (h : i₁ + i₂ = j)
    (t : supported ℂ ℂ (G.zbdStateSet i₁) ⊗[ℂ] supported ℂ ℂ (G.zbdStateSet i₂)) :
    finsuppTensorFinsupp' ℂ G.IncResolutionBasis G.IncResolutionBasis
        (TensorProduct.map (supported ℂ ℂ (G.zbdStateSet i₁)).subtype
          (supported ℂ ℂ (G.zbdStateSet i₂)).subtype t) ∈
      supported ℂ ℂ (G.zbdPairSet j) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, mem_supported']
    intro e he
    rw [Submodule.subtype_apply, Submodule.subtype_apply, finsuppTensorFinsupp'_apply_apply]
    by_contra hne
    rcases mul_ne_zero_iff.mp hne with ⟨hx, hy⟩
    have h1 : e.1 ∈ G.zbdStateSet i₁ := by
      by_contra h1
      exact hx ((mem_supported' ℂ _).mp x.2 e.1 h1)
    have h2 : e.2 ∈ G.zbdStateSet i₂ := by
      by_contra h2
      exact hy ((mem_supported' ℂ _).mp y.2 e.2 h2)
    apply he
    change ((G.incResolutionDegree e.1 + G.incResolutionDegree e.2 : ℕ) : ℤ) = -j
    change (G.incResolutionDegree e.1 : ℤ) = -i₁ at h1
    change (G.incResolutionDegree e.2 : ℤ) = -i₂ at h2
    push_cast
    omega
  | add s t hs ht =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hs ht

/-- The summand `S.X i₁ ⊗ S.X i₂` goes to the pairs of states of total degree `j`. -/
def zbdPairTensorLinear (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    supported ℂ ℂ (G.zbdStateSet i₁) ⊗[ℂ] supported ℂ ℂ (G.zbdStateSet i₂) →ₗ[ℂ]
      supported ℂ ℂ (G.zbdPairSet j) :=
  LinearMap.codRestrict (supported ℂ ℂ (G.zbdPairSet j))
    ((finsuppTensorFinsupp' ℂ G.IncResolutionBasis G.IncResolutionBasis).toLinearMap ∘ₗ
      TensorProduct.map (supported ℂ ℂ (G.zbdStateSet i₁)).subtype
        (supported ℂ ℂ (G.zbdStateSet i₂)).subtype)
    (fun t => G.zbdPairTensor_mem h t)

theorem zbdPairTensorLinear_tmul (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j)
    (x : supported ℂ ℂ (G.zbdStateSet i₁)) (y : supported ℂ ℂ (G.zbdStateSet i₂)) :
    (G.zbdPairTensorLinear i₁ i₂ j h (x ⊗ₜ y) : G.IncResolutionBasis × G.IncResolutionBasis →₀ ℂ) =
      finsuppTensorFinsupp' ℂ G.IncResolutionBasis G.IncResolutionBasis (x.1 ⊗ₜ y.1) := rfl

/-- The components of the map from the tensor product to the pair model on a summand. -/
def zbdPairTensorPiece (i₁ i₂ j : ℤ) (h : i₁ + i₂ = j) :
    G.zbdStateGraded.complex.X i₁ ⊗ G.zbdStateGraded.complex.X i₂ ⟶ G.zbdPairGraded.complex.X j :=
  ModuleCat.ofHom (G.zbdPairTensorLinear i₁ i₂ j h)

/-- The component in degree `j` of the map from the tensor product to the pair model. -/
def zbdPairTensorF (j : ℤ) :
    (HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex).X j ⟶
      G.zbdPairGraded.complex.X j :=
  mapBifunctorDesc fun i₁ i₂ h => G.zbdPairTensorPiece i₁ i₂ j h

/-- **From the tensor product of the state model to the pair model**; both complexes have zero
differentials. -/
def zbdPairTensorHom :
    HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex ⟶
      G.zbdPairGraded.complex where
  f j := G.zbdPairTensorF j
  comm' i j _ := by
    rw [zbd_complex_d_eq_zero _ rfl,
      zbd_tensorObj_d_eq_zero (zbd_complex_d_eq_zero _ rfl) (zbd_complex_d_eq_zero _ rfl),
      comp_zero, zero_comp]

/-- The basis vector of a pair of states in the tensor product, or zero when the degrees do not
add up to `j`. -/
def zbdPairTensorVector (j : ℤ) (e : G.IncResolutionBasis × G.IncResolutionBasis) :
    (HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex).X j :=
  (ιMapBifunctorOrZero G.zbdStateGraded.complex G.zbdStateGraded.complex
    (curriedTensor (ModuleCat.{0} ℂ)) (ComplexShape.up ℤ)
    (-(G.incResolutionDegree e.1 : ℤ)) (-(G.incResolutionDegree e.2 : ℤ)) j).hom
    ((⟨single e.1 1, single_mem_supported ℂ 1 (by simp [zbdStateSet])⟩ :
        supported ℂ ℂ (G.zbdStateSet (-(G.incResolutionDegree e.1 : ℤ)))) ⊗ₜ
      (⟨single e.2 1, single_mem_supported ℂ 1 (by simp [zbdStateSet])⟩ :
        supported ℂ ℂ (G.zbdStateSet (-(G.incResolutionDegree e.2 : ℤ)))))

theorem zbdPairTensorVector_eq {j : ℤ} {e : G.IncResolutionBasis × G.IncResolutionBasis}
    (he : e ∈ G.zbdPairSet j) :
    G.zbdPairTensorVector j e =
      (ιTensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex
        (-(G.incResolutionDegree e.1 : ℤ)) (-(G.incResolutionDegree e.2 : ℤ)) j
        (by change ((G.incResolutionDegree e.1 + G.incResolutionDegree e.2 : ℕ) : ℤ) = -j at he
            push_cast at he; omega)).hom
      ((⟨single e.1 1, single_mem_supported ℂ 1 (by simp [zbdStateSet])⟩ :
          supported ℂ ℂ (G.zbdStateSet (-(G.incResolutionDegree e.1 : ℤ)))) ⊗ₜ
        (⟨single e.2 1, single_mem_supported ℂ 1 (by simp [zbdStateSet])⟩ :
          supported ℂ ℂ (G.zbdStateSet (-(G.incResolutionDegree e.2 : ℤ))))) := by
  rw [zbdPairTensorVector, ιMapBifunctorOrZero_eq]

/-- The inverse on the pair basis. -/
def zbdPairTensorInvLinear (j : ℤ) :
    supported ℂ ℂ (G.zbdPairSet j) →ₗ[ℂ]
      (HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex).X j :=
  Finsupp.linearCombination ℂ (G.zbdPairTensorVector j) ∘ₗ (supported ℂ ℂ (G.zbdPairSet j)).subtype

/-- The component in degree `j` of the inverse. -/
def zbdPairTensorInvF (j : ℤ) :
    G.zbdPairGraded.complex.X j ⟶
      (HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex).X j :=
  ModuleCat.ofHom (G.zbdPairTensorInvLinear j)

/-- **From the pair model to the tensor product of the state model.** -/
def zbdPairTensorInv :
    G.zbdPairGraded.complex ⟶
      HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex where
  f j := G.zbdPairTensorInvF j
  comm' i j _ := by
    rw [zbd_complex_d_eq_zero _ rfl,
      zbd_tensorObj_d_eq_zero (zbd_complex_d_eq_zero _ rfl) (zbd_complex_d_eq_zero _ rfl),
      comp_zero, zero_comp]

theorem zbd_desc_apply {K L : CochainComplex (ModuleCat.{0} ℂ) ℤ} {A : ModuleCat.{0} ℂ} {j : ℤ}
    (f : ∀ (i₁ i₂ : ℤ) (_ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = j),
      ((curriedTensor (ModuleCat.{0} ℂ)).obj (K.X i₁)).obj (L.X i₂) ⟶ A)
    (i₁ i₂ : ℤ) (h : i₁ + i₂ = j) (t : (K.X i₁ ⊗ L.X i₂ : ModuleCat.{0} ℂ)) :
    (mapBifunctorDesc (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat.{0} ℂ))
      (c := ComplexShape.up ℤ) f).hom ((ιTensorObj K L i₁ i₂ j h).hom t) = (f i₁ i₂ h).hom t := by
  have := congrArg ModuleCat.Hom.hom (ι_mapBifunctorDesc f i₁ i₂ h)
  rw [ModuleCat.hom_comp] at this
  exact LinearMap.congr_fun this t

theorem zbdPairTensorF_vector {j : ℤ} {e : G.IncResolutionBasis × G.IncResolutionBasis}
    (he : e ∈ G.zbdPairSet j) :
    (G.zbdPairTensorF j).hom (G.zbdPairTensorVector j e) =
      ⟨single e 1, single_mem_supported ℂ 1 he⟩ := by
  rw [G.zbdPairTensorVector_eq he, zbdPairTensorF, zbd_desc_apply]
  apply Subtype.ext
  change finsuppTensorFinsupp' ℂ G.IncResolutionBasis G.IncResolutionBasis
    (single e.1 1 ⊗ₜ single e.2 1) = single e 1
  rw [finsuppTensorFinsupp'_single_tmul_single, one_mul]

theorem zbdPairTensorInv_hom (j : ℤ) :
    (G.zbdPairTensorF j).hom ∘ₗ G.zbdPairTensorInvLinear j = LinearMap.id := by
  apply zbd_supported_ext
  intro e he
  change (G.zbdPairTensorF j).hom
      (G.zbdPairTensorInvLinear j ⟨single e 1, single_mem_supported ℂ 1 he⟩) =
    (⟨single e 1, single_mem_supported ℂ 1 he⟩ : supported ℂ ℂ (G.zbdPairSet j))
  rw [zbdPairTensorInvLinear, LinearMap.comp_apply, Submodule.subtype_apply,
    linearCombination_single, one_smul]
  exact G.zbdPairTensorF_vector he

theorem zbdPairTensorHom_inv (j : ℤ) :
    G.zbdPairTensorF j ≫ G.zbdPairTensorInvF j = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  change i₁ + i₂ = j at h
  rw [← Category.assoc, zbdPairTensorF, ι_mapBifunctorDesc, Category.comp_id]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp]
  apply TensorProduct.ext
  apply zbd_supported_ext
  intro a ha
  apply zbd_supported_ext
  intro b hb
  change (G.incResolutionDegree a : ℤ) = -i₁ at ha
  change (G.incResolutionDegree b : ℤ) = -i₂ at hb
  obtain rfl : i₁ = -(G.incResolutionDegree a : ℤ) := by omega
  obtain rfl : i₂ = -(G.incResolutionDegree b : ℤ) := by omega
  change G.zbdPairTensorInvLinear j (G.zbdPairTensorLinear _ _ j h
      (⟨single a 1, single_mem_supported ℂ 1 ha⟩ ⊗ₜ ⟨single b 1, single_mem_supported ℂ 1 hb⟩)) =
    (ιTensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex _ _ j h).hom
      (⟨single a 1, single_mem_supported ℂ 1 ha⟩ ⊗ₜ ⟨single b 1, single_mem_supported ℂ 1 hb⟩)
  rw [zbdPairTensorInvLinear, LinearMap.comp_apply, Submodule.subtype_apply]
  have hval : (G.zbdPairTensorLinear _ _ j h
      (⟨single a 1, single_mem_supported ℂ 1 ha⟩ ⊗ₜ ⟨single b 1, single_mem_supported ℂ 1 hb⟩) :
        G.IncResolutionBasis × G.IncResolutionBasis →₀ ℂ) = single (a, b) 1 := by
    rw [zbdPairTensorLinear_tmul, finsuppTensorFinsupp'_single_tmul_single, one_mul]
  rw [hval, linearCombination_single, one_smul]
  exact G.zbdPairTensorVector_eq (j := j) (e := (a, b))
    (by change ((G.incResolutionDegree a + G.incResolutionDegree b : ℕ) : ℤ) = -j; push_cast; omega)

/-- **The pair model is Mathlib's tensor product of the state model with itself.** -/
def zbdPairTensorIso :
    HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex ≅
      G.zbdPairGraded.complex where
  hom := G.zbdPairTensorHom
  inv := G.zbdPairTensorInv
  hom_inv_id := by
    ext j : 1
    exact G.zbdPairTensorHom_inv j
  inv_hom_id := by
    ext j : 1
    apply ModuleCat.hom_ext
    exact G.zbdPairTensorInv_hom j

/-! ### The factorization of `∪₀ ∘ (ι₀ ⊗ ι₀)` and the square in `D(ℂ)` -/

/-- **`∪₀ ∘ (ι₀ ⊗ ι₀)` on the pair model is the composite through the tensor product**: the chain
map `zbdPairCupHom` of `IncidenceZeroBaseChangeDerivedProduct` is `ι₀ ⊗ ι₀` followed by `∪₀`, read
through the identification of the tensor product with the pair model. -/
theorem zbdPairTensorHom_cup :
    HomologicalComplex.tensorHom G.zbdStateInclusionHom G.zbdStateInclusionHom ≫
        G.zbdModelCupHom =
      G.zbdPairTensorHom ≫ G.zbdPairCupHom := by
  ext j : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [← Category.assoc, ← Category.assoc, ι_mapBifunctorMap]
  change (_ ≫ _ ≫ _) ≫ G.zbdModelCupF j = (_ ≫ G.zbdPairTensorF j) ≫ _
  rw [zbdPairTensorF, ι_mapBifunctorDesc, Category.assoc, Category.assoc, zbdModelCupF,
    ι_mapBifunctorDesc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply zbd_supported_ext
  intro a ha
  apply zbd_supported_ext
  intro b hb
  apply Subtype.ext
  change G.zbcTotalCup (G.zbcContraction.i (single a 1)) (G.zbcContraction.i (single b 1)) =
    G.zbdPairCup (finsuppTensorFinsupp' ℂ G.IncResolutionBasis G.IncResolutionBasis
      (single a 1 ⊗ₜ single b 1))
  rw [finsuppTensorFinsupp'_single_tmul_single, one_mul, zbdPairCup, linearCombination_single,
    one_smul, G.zbcSpecialize_totalCup,
    zbcSpecialize_inclusion, zbcSpecialize_inclusion, G.zbdFreeSpecialize_single_one,
    G.zbdFreeSpecialize_single_one]

section Derived

/-- The specialized standard Tor product on Mathlib's tensor product of the state model with
itself: the identification with the pair model followed by `μ₀`. -/
def zbdStateTensorProductHom :
    HomologicalComplex.tensorObj G.zbdStateGraded.complex G.zbdStateGraded.complex ⟶
      G.zbdStateGraded.complex :=
  G.zbdPairTensorHom ≫ G.zbdStateProductHom

/-- **The square of products in `D(ℂ)` out of the tensor product**: `Q(μ) ≫ Q(ι₀) =
Q(ι₀ ⊗ ι₀) ≫ Q(∪₀)` for the product `μ` on `S ⊗ S` and the Čech–Koszul product `∪₀` on
`C₀ ⊗ C₀`. -/
theorem zbdTensorProductSquare :
    DerivedCategory.Q.map G.zbdStateTensorProductHom ≫
        DerivedCategory.Q.map G.zbdStateInclusionHom =
      DerivedCategory.Q.map
          (HomologicalComplex.tensorHom G.zbdStateInclusionHom G.zbdStateInclusionHom) ≫
        DerivedCategory.Q.map G.zbdModelCupHom := by
  rw [zbdStateTensorProductHom, Functor.map_comp, Category.assoc, zbdProductSquare,
    ← Functor.map_comp, ← zbdPairTensorHom_cup, Functor.map_comp]

/-- The product on `ℂ ⊗ F⁻`, transported from the state model along `zbdStateIso`. -/
def zbdResolutionProductC :
    HomologicalComplex.tensorObj G.zbdResolutionComplexC G.zbdResolutionComplexC ⟶
      G.zbdResolutionComplexC :=
  HomologicalComplex.tensorHom G.zbdStateIso.hom G.zbdStateIso.hom ≫
    G.zbdStateTensorProductHom ≫ G.zbdStateIso.inv

/-- The base change of `ι` followed by the model isomorphism, `ℂ ⊗ F⁻ ⟶ C₀`; its image in
`D(ℂ)` is `zbdDerivedModelIso.hom`. -/
def zbdBaseChangeModelHom : G.zbdResolutionComplexC ⟶ G.zbdModelComplex :=
  G.zbdBaseChangeHomotopyEquiv.hom ≫ G.zbdModelIso.hom

theorem zbdBaseChangeModelHom_eq :
    G.zbdBaseChangeModelHom = G.zbdStateIso.hom ≫ G.zbdStateInclusionHom :=
  G.zbdStateIso_inclusion.symm

theorem zbdDerivedModelIso_hom_eq :
    G.zbdDerivedModelIso.hom = DerivedCategory.Q.map G.zbdBaseChangeModelHom :=
  G.zbdDerivedModelIso_hom

/-- **The derived base change respects the products, for Mathlib's tensor product of complexes.**
In `D(ℂ)`, the product `μ` on `ℂ ⊗ F⁻` followed by the derived base-change isomorphism equals
`β ⊗ β` followed by the Čech–Koszul product `∪₀` on `C₀ ⊗ C₀`, where `β : ℂ ⊗ F⁻ ⟶ C₀` is the
base change of `ι` followed by the model isomorphism. -/
theorem zbdDerivedTensorProduct :
    DerivedCategory.Q.map G.zbdResolutionProductC ≫ G.zbdDerivedModelIso.hom =
      DerivedCategory.Q.map
          (HomologicalComplex.tensorHom G.zbdBaseChangeModelHom G.zbdBaseChangeModelHom) ≫
        DerivedCategory.Q.map G.zbdModelCupHom := by
  rw [zbdDerivedModelIso_hom_eq, ← Functor.map_comp, zbdBaseChangeModelHom_eq,
    zbdResolutionProductC, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  have ht : HomologicalComplex.tensorHom (G.zbdStateIso.hom ≫ G.zbdStateInclusionHom)
      (G.zbdStateIso.hom ≫ G.zbdStateInclusionHom) =
      HomologicalComplex.tensorHom G.zbdStateIso.hom G.zbdStateIso.hom ≫
        HomologicalComplex.tensorHom G.zbdStateInclusionHom G.zbdStateInclusionHom :=
    (MonoidalCategory.tensorHom_comp_tensorHom (C := CochainComplex (ModuleCat.{0} ℂ) ℤ)
      G.zbdStateIso.hom G.zbdStateIso.hom G.zbdStateInclusionHom G.zbdStateInclusionHom).symm
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  exact G.zbdTensorProductSquare

/-- The same statement in the notation of the monoidal category of cochain complexes. -/
theorem zbdDerivedTensorProduct' :
    DerivedCategory.Q.map G.zbdResolutionProductC ≫ G.zbdDerivedModelIso.hom =
      DerivedCategory.Q.map (G.zbdBaseChangeModelHom ⊗ₘ G.zbdBaseChangeModelHom) ≫
        DerivedCategory.Q.map G.zbdModelCupHom :=
  G.zbdDerivedTensorProduct

end Derived

end

end BPFixedPoints.Multigraph
