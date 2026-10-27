import BPFixedPoints.Incidence.KoszulCechCup
import BPFixedPoints.Incidence.CechProductCupLaws
import BPFixedPoints.Incidence.CechProductRingChange

/-!
# Ring-generic exterior state product

The standard Tor product of the incidence resolution is computed at the origin by
projecting the exterior Čech product of included states (`incidenceTorProduct_cech_formula`).
Replace the coefficient ring `IncCoeffRing E` by an arbitrary commutative ring and
define the resulting state product `incStateCup R`. At `IncCoeffRing E` it is the
existing composite by definition. On state basis vectors it vanishes when the edge
states share an edge; for disjoint edge states it is the shuffle sign times the
Koszul sign (−1)^(|S|·j_T) times the multi-vertex Čech cup product, transported
along deg(S∪T) = deg S + deg T. The empty edge state with the twist-zero unit is a
two-sided unit and the product is associative. Coefficientwise ring change
(`Finsupp.mapRange`) is multiplicative for these products.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.CechProduct

open Finsupp

variable (R : Type*) [CommRing R] {V : Type*} [Fintype V]

/-- Parity acts on a cocycle in the image of the chosen state inclusion by the sign of the
cohomological degree of the twist. -/
theorem contraction_sign_i (d : V → ℕ) (x : H R d) :
    (contraction R d).sign ((contraction R d).i x) =
      (-1 : R) ^ cohomologyDegree d • (contraction R d).i x := by
  classical
  have hx := contraction_i_degree R d (cohomologyDegree d) x
    ((mem_supported R x).mpr (by intro b _; rfl))
  have hs : ∀ (z : C R V),
      z ∈ supported R R {b | (cechDegree b : ℤ) = cohomologyDegree d + 0} →
        (contraction R d).sign z = (-1 : R) ^ cohomologyDegree d • z := by
    intro z hz
    rw [← z.sum_single, map_finsuppSum]
    change (∑ b ∈ z.support, _) = (-1 : R) ^ cohomologyDegree d • ∑ b ∈ z.support, single b (z b)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hdeg : (cechDegree b : ℤ) = cohomologyDegree d + 0 := (mem_supported R z).mp hz hb
    rw [add_zero, Nat.cast_inj] at hdeg
    dsimp only
    rw [contraction_sign_single, hdeg]
  exact hs _ hx

/-- Powers of the Čech parity act on an included state by the corresponding power of its
degree sign. -/
theorem parity_pow_i (d : V → ℕ) (n : ℕ) (x : H R d) :
    (parity R ^ n) ((contraction R d).i x) =
      (-1 : R) ^ (n * cohomologyDegree d) • (contraction R d).i x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [parity_pow_succ_apply, ih, map_smul, parity_eq R d, contraction_sign_i, smul_smul,
      ← pow_add, Nat.succ_mul]

/-- Transport of twist vectors on both factors of the cup product, as a heterogeneous equality. -/
theorem cohomologyCup_heq {d d' e e' : V → ℕ} (hd : d = d') (he : e = e')
    {x : H R d} {x' : H R d'} {y : H R e} {y' : H R e'} (hx : HEq x x') (hy : HEq y y') :
    HEq (cohomologyCup R d e x y) (cohomologyCup R d' e' x' y') := by
  subst hd he
  rw [eq_of_heq hx, eq_of_heq hy]

/-- Cohomological degrees add when no vertex has both twists positive. -/
theorem cohomologyDegree_add_of_forall_not_pos (d e : V → ℕ)
    (h : ∀ v, ¬ (0 < d v ∧ 0 < e v)) :
    cohomologyDegree (d + e) = cohomologyDegree d + cohomologyDegree e := by
  unfold cohomologyDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv := h v
  simp only [Pi.add_apply, lineCohomologyDegree]
  split_ifs <;> omega

/-- The zero twist has cohomological degree zero. -/
theorem cohomologyDegree_zero : cohomologyDegree (0 : V → ℕ) = 0 := by
  simp [cohomologyDegree, lineCohomologyDegree]

/-- Coefficientwise ring change commutes with transport of twist vectors. -/
theorem castH_mapRange {R' : Type*} [CommRing R'] (f : R →+* R') {d d' : V → ℕ} (h : d = d')
    (x : H R d) :
    castH R' h (mapRange f (map_zero f) x) = mapRange f (map_zero f) (castH R h x) := by
  subst h
  rfl

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Koszul

/-- A ring homomorphism sends the shuffle sign to the shuffle sign. -/
theorem map_shuffleSign {E R R' : Type*} [LinearOrder E] [CommRing R] [CommRing R']
    (f : R →+* R') (S T : Finset E) :
    f (shuffleSign (R := R) S T) = shuffleSign (R := R') S T := by
  simp [shuffleSign]

end BPFixedPoints.Koszul

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct IncidencePerturbation

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (R : Type) [CommRing R]

/-- Statewise product Čech contraction with coefficients in an arbitrary commutative ring. -/
noncomputable def incCechContractionOver :
    Contraction R (Koszul.Space E (CechProduct.C R V)) (G.IncResolutionBasis →₀ R) :=
  Contraction.finsupp fun S => (CechProduct.contraction R (G.deg S)).toContraction

/-- Edge-state coefficient of the exterior Čech product over an arbitrary commutative ring. -/
noncomputable def incCupCoefficientOver (S T : Finset E) :
    CechProduct.C R V →ₗ[R] CechProduct.C R V →ₗ[R] CechProduct.C R V :=
  (chainCup R (G.deg S) (G.deg T)).compl₂ (parity R ^ S.card)

/-- Exterior Čech product on the total module over an arbitrary commutative ring. -/
noncomputable def incTotalCupOver :
    Koszul.Space E (CechProduct.C R V) →ₗ[R] Koszul.Space E (CechProduct.C R V) →ₗ[R]
      Koszul.Space E (CechProduct.C R V) :=
  Finsupp.lsum R fun S => (Finsupp.lsum R).comp
    (LinearMap.pi fun T => (G.incCupCoefficientOver R S T).compr₂
      (Koszul.wedgeSingle (R := R) S T))

/-- Ring-generic state product: project the exterior Čech product of included states. -/
noncomputable def incStateCup :
    (G.IncResolutionBasis →₀ R) →ₗ[R] (G.IncResolutionBasis →₀ R) →ₗ[R]
      (G.IncResolutionBasis →₀ R) :=
  ((G.incTotalCupOver R).compl₁₂ (G.incCechContractionOver R).i
    (G.incCechContractionOver R).i).compr₂ (G.incCechContractionOver R).p

/-- At the incidence coefficient ring the generic contraction is the existing one. -/
theorem incCechContractionOver_incCoeffRing :
    G.incCechContractionOver (IncCoeffRing E) = G.incCechContraction := rfl

/-- At the incidence coefficient ring the generic edge-state coefficient is the existing one. -/
theorem incCupCoefficientOver_incCoeffRing (S T : Finset E) :
    G.incCupCoefficientOver (IncCoeffRing E) S T = G.incCupCoefficient S T := rfl

/-- At the incidence coefficient ring the generic exterior Čech product is the existing one. -/
theorem incTotalCupOver_incCoeffRing :
    G.incTotalCupOver (IncCoeffRing E) = G.incTotalCup := rfl

/-- At the incidence coefficient ring the state product is the projected exterior Čech
product of included states appearing in `incidenceTorProduct_cech_formula`. -/
theorem incStateCup_incCoeffRing (x y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incStateCup (IncCoeffRing E) x y =
      G.incCechContraction.p
        (G.incTotalCup (G.incCechContraction.i x) (G.incCechContraction.i y)) := rfl

/-- Additivity of vertex degrees over a disjoint union of edge sets, as functions. -/
theorem deg_union_eq_add {S T : Finset E} (h : Disjoint S T) :
    G.deg (S ∪ T) = G.deg S + G.deg T := by
  funext v
  exact Finset.sum_union h

/-- The empty edge state has twist zero, as a function. -/
theorem deg_empty_eq_zero : G.deg (∅ : Finset E) = 0 :=
  funext G.deg_empty

/-- Index of a state of one edge set in the full state basis. -/
def incStateIndex (S : Finset E) (κ : HBasis (G.deg S)) : G.IncResolutionBasis := ⟨S, κ⟩

/-- Distinct states of one edge set have distinct indices. -/
theorem incStateIndex_injective (S : Finset E) : Function.Injective (G.incStateIndex S) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

/-- Insert the states of one edge set into the full state module. -/
noncomputable def incStateEmbed (S : Finset E) :
    CechProduct.H R (G.deg S) →ₗ[R] (G.IncResolutionBasis →₀ R) :=
  Finsupp.lmapDomain R R (G.incStateIndex S)

/-- The embedding of a state basis vector. -/
@[simp] theorem incStateEmbed_single (S : Finset E) (κ : HBasis (G.deg S)) (r : R) :
    G.incStateEmbed R S (single κ r) = single ⟨S, κ⟩ r := by
  simp [incStateEmbed, incStateIndex]

/-- Coefficients of an embedded state in its own edge set. -/
theorem incStateEmbed_apply_same (S : Finset E) (x : CechProduct.H R (G.deg S))
    (κ : HBasis (G.deg S)) : G.incStateEmbed R S x ⟨S, κ⟩ = x κ :=
  mapDomain_apply_of_injective (G.incStateIndex_injective S) x κ

/-- Coefficients of an embedded state in another edge set vanish. -/
theorem incStateEmbed_apply_of_ne {S T : Finset E} (h : S ≠ T) (x : CechProduct.H R (G.deg S))
    (κ : HBasis (G.deg T)) : G.incStateEmbed R S x ⟨T, κ⟩ = 0 := by
  apply mapDomain_of_notMem_range
  rintro ⟨κ', hκ'⟩
  exact h (congrArg Sigma.fst hκ')

/-- Embeddings of heterogeneously equal states of equal edge sets agree. -/
theorem incStateEmbed_heq {S S' : Finset E} (h : S = S')
    {x : CechProduct.H R (G.deg S)} {x' : CechProduct.H R (G.deg S')} (hx : HEq x x') :
    G.incStateEmbed R S x = G.incStateEmbed R S' x' := by
  subst h
  rw [eq_of_heq hx]

/-- The generic inclusion of an embedded state is the included cocycle in its edge state. -/
theorem incCechContractionOver_i_embed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    (G.incCechContractionOver R).i (G.incStateEmbed R S x) =
      single S ((CechProduct.contraction R (G.deg S)).i x) := by
  apply Finsupp.ext
  intro T
  change (CechProduct.contraction R (G.deg T)).i
    ((Finsupp.sigmaFinsuppLEquivPiFinsupp R) (G.incStateEmbed R S x) T) = _
  by_cases hST : S = T
  · subst hST
    rw [single_eq_same]
    congr 1
    ext κ
    rw [sigmaFinsuppLEquivPiFinsupp_apply]
    exact G.incStateEmbed_apply_same R S x κ
  · rw [single_eq_of_ne (Ne.symm hST)]
    have hz : (Finsupp.sigmaFinsuppLEquivPiFinsupp R) (G.incStateEmbed R S x) T = 0 := by
      ext κ
      rw [sigmaFinsuppLEquivPiFinsupp_apply]
      exact G.incStateEmbed_apply_of_ne R hST x κ
    rw [hz, map_zero]

/-- The generic projection of a single edge state is the embedding of its projected state. -/
theorem incCechContractionOver_p_single (S : Finset E) (c : CechProduct.C R V) :
    (G.incCechContractionOver R).p (single S c) =
      G.incStateEmbed R S ((CechProduct.contraction R (G.deg S)).p c) := by
  ext ⟨T, κ⟩
  change (CechProduct.contraction R (G.deg T)).p ((single S c) T) κ = _
  by_cases hST : S = T
  · subst hST
    rw [single_eq_same]
    exact (G.incStateEmbed_apply_same R S _ κ).symm
  · rw [single_eq_of_ne (Ne.symm hST), map_zero]
    exact (G.incStateEmbed_apply_of_ne R hST _ κ).symm

/-- The generic exterior Čech product on single edge states. -/
theorem incTotalCupOver_single (S T : Finset E) (x y : CechProduct.C R V) :
    G.incTotalCupOver R (single S x) (single T y) =
      Koszul.wedgeSingle (R := R) S T (G.incCupCoefficientOver R S T x y) := by
  simp [incTotalCupOver]

/-- State product of embedded states: zero when the edge states share an edge, and otherwise
the shuffle sign times the Koszul sign (−1)^(|S|·j_T) times the transported cup product. -/
theorem incStateCup_embed (S T : Finset E) (x : CechProduct.H R (G.deg S))
    (y : CechProduct.H R (G.deg T)) :
    G.incStateCup R (G.incStateEmbed R S x) (G.incStateEmbed R T y) =
      if h : Disjoint S T then
        (Koszul.shuffleSign (R := R) S T * (-1 : R) ^ (S.card * cohomologyDegree (G.deg T))) •
          G.incStateEmbed R (S ∪ T)
            (castH R (G.deg_union_eq_add h).symm (cohomologyCup R (G.deg S) (G.deg T) x y))
      else 0 := by
  change (G.incCechContractionOver R).p (G.incTotalCupOver R
    ((G.incCechContractionOver R).i (G.incStateEmbed R S x))
    ((G.incCechContractionOver R).i (G.incStateEmbed R T y))) = _
  rw [incCechContractionOver_i_embed, incCechContractionOver_i_embed, incTotalCupOver_single,
    Koszul.wedgeSingle_apply]
  by_cases h : Disjoint S T
  · rw [dite_eq_left h, ite_eq_left h, incCechContractionOver_p_single]
    change G.incStateEmbed R (S ∪ T) ((CechProduct.contraction R (G.deg (S ∪ T))).p
      (Koszul.shuffleSign (R := R) S T • chainCup R (G.deg S) (G.deg T)
        ((CechProduct.contraction R (G.deg S)).i x)
        ((parity R ^ S.card) ((CechProduct.contraction R (G.deg T)).i y)))) = _
    rw [parity_pow_i]
    simp only [map_smul]
    rw [← castH_contraction_p R (G.deg_union_eq_add h).symm,
      ← cohomologyCup_chain_projection R (G.deg S) (G.deg T) (contraction_d_i R _ x)
        (contraction_d_i R _ y), contraction_p_i, contraction_p_i, smul_smul]
  · rw [dite_eq_right h, ite_eq_right h, map_zero]

/-- State product of basis vectors: zero when the edge states share an edge; for disjoint
edge states the shuffle sign times (−1)^(|S|·j_T) times the embedded, transported
multi-vertex cup product of the two state basis vectors, with j_T the cohomological degree
of the twist of `T`. -/
theorem incStateCup_single (S T : Finset E) (κ : HBasis (G.deg S)) (κ' : HBasis (G.deg T))
    (r s : R) :
    G.incStateCup R (single ⟨S, κ⟩ r) (single ⟨T, κ'⟩ s) =
      if h : Disjoint S T then
        (Koszul.shuffleSign (R := R) S T * (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) *
            (r * s)) •
          G.incStateEmbed R (S ∪ T)
            (castH R (G.deg_union_eq_add h).symm
              (cohomologyCup R (G.deg S) (G.deg T) (single κ 1) (single κ' 1)))
      else 0 := by
  rw [← G.incStateEmbed_single R S κ r, ← G.incStateEmbed_single R T κ' s,
    incStateCup_embed]
  by_cases h : Disjoint S T
  · rw [dite_eq_left h, dite_eq_left h]
    have hr : (single κ r : CechProduct.H R (G.deg S)) = r • single κ 1 := by
      rw [smul_single, smul_eq_mul, mul_one]
    have hs : (single κ' s : CechProduct.H R (G.deg T)) = s • single κ' 1 := by
      rw [smul_single, smul_eq_mul, mul_one]
    rw [hr, hs]
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    congr 1
    ring
  · rw [dite_eq_right h, dite_eq_right h]

/-- State product of basis vectors of edge-disjoint states. -/
theorem incStateCup_single_of_disjoint {S T : Finset E} (h : Disjoint S T)
    (κ : HBasis (G.deg S)) (κ' : HBasis (G.deg T)) (r s : R) :
    G.incStateCup R (single ⟨S, κ⟩ r) (single ⟨T, κ'⟩ s) =
      (Koszul.shuffleSign (R := R) S T * (-1 : R) ^ (S.card * cohomologyDegree (G.deg T)) *
          (r * s)) •
        G.incStateEmbed R (S ∪ T)
          (castH R (G.deg_union_eq_add h).symm
            (cohomologyCup R (G.deg S) (G.deg T) (single κ 1) (single κ' 1))) := by
  rw [incStateCup_single, dite_eq_left h]

/-- The state product of basis vectors whose edge states share an edge is zero. -/
theorem incStateCup_single_of_not_disjoint {S T : Finset E} (h : ¬ Disjoint S T)
    (κ : HBasis (G.deg S)) (κ' : HBasis (G.deg T)) (r s : R) :
    G.incStateCup R (single ⟨S, κ⟩ r) (single ⟨T, κ'⟩ s) = 0 := by
  rw [incStateCup_single, dite_eq_right h]

/-- Unit state: the empty edge state carrying the twist-zero cohomology unit. -/
noncomputable def incStateUnit : G.IncResolutionBasis →₀ R :=
  G.incStateEmbed R ∅ (castH R G.deg_empty_eq_zero.symm (cohomologyUnit (V := V) R))

/-- The unit state is a left unit on embedded states. -/
theorem incStateCup_unit_left_embed (T : Finset E) (y : CechProduct.H R (G.deg T)) :
    G.incStateCup R (G.incStateUnit R) (G.incStateEmbed R T y) = G.incStateEmbed R T y := by
  rw [incStateUnit, incStateCup_embed, dite_eq_left (Finset.disjoint_empty_left T),
    Koszul.shuffleSign_empty_left, Finset.card_empty, zero_mul, pow_zero, mul_one, one_smul]
  apply G.incStateEmbed_heq R (Finset.empty_union T)
  refine (castH_heq R _ _).trans ?_
  refine (cohomologyCup_heq R G.deg_empty_eq_zero rfl (castH_heq R _ _) HEq.rfl).trans ?_
  exact cohomologyCup_unit_left_heq R (G.deg T) y

/-- The unit state is a right unit on embedded states. -/
theorem incStateCup_unit_right_embed (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    G.incStateCup R (G.incStateEmbed R S x) (G.incStateUnit R) = G.incStateEmbed R S x := by
  have h0 : cohomologyDegree (G.deg (∅ : Finset E)) = 0 := by
    rw [G.deg_empty_eq_zero]
    exact cohomologyDegree_zero
  rw [incStateUnit, incStateCup_embed, dite_eq_left (Finset.disjoint_empty_right S),
    Koszul.shuffleSign_empty_right, h0, mul_zero, pow_zero, mul_one, one_smul]
  apply G.incStateEmbed_heq R (Finset.union_empty S)
  refine (castH_heq R _ _).trans ?_
  refine (cohomologyCup_heq R rfl G.deg_empty_eq_zero HEq.rfl (castH_heq R _ _)).trans ?_
  exact heq_of_eq (cohomologyCup_unit_right R (G.deg S) x)

/-- The unit state is a left unit for the state product. -/
theorem incStateCup_unit_left (z : G.IncResolutionBasis →₀ R) :
    G.incStateCup R (G.incStateUnit R) z = z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add z z' hz hz' => rw [map_add, hz, hz']
  | single p r =>
    obtain ⟨T, κ⟩ := p
    rw [← G.incStateEmbed_single R T κ r]
    exact G.incStateCup_unit_left_embed R T _

/-- The unit state is a right unit for the state product. -/
theorem incStateCup_unit_right (z : G.IncResolutionBasis →₀ R) :
    G.incStateCup R z (G.incStateUnit R) = z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add z z' hz hz' => rw [map_add, LinearMap.add_apply, hz, hz']
  | single p r =>
    obtain ⟨S, κ⟩ := p
    rw [← G.incStateEmbed_single R S κ r]
    exact G.incStateCup_unit_right_embed R S _

/-- Associativity of the state product on embedded states. -/
theorem incStateCup_assoc_embed (S T U : Finset E) (a : CechProduct.H R (G.deg S))
    (b : CechProduct.H R (G.deg T)) (c : CechProduct.H R (G.deg U)) :
    G.incStateCup R (G.incStateCup R (G.incStateEmbed R S a) (G.incStateEmbed R T b))
        (G.incStateEmbed R U c) =
      G.incStateCup R (G.incStateEmbed R S a)
        (G.incStateCup R (G.incStateEmbed R T b) (G.incStateEmbed R U c)) := by
  rw [G.incStateCup_embed R S T, G.incStateCup_embed R T U]
  by_cases hST : Disjoint S T
  swap
  · rw [dite_eq_right hST, map_zero, LinearMap.zero_apply]
    by_cases hTU : Disjoint T U
    · rw [dite_eq_left hTU, map_smul, incStateCup_embed,
        dite_eq_right (fun h => hST (Finset.disjoint_union_right.mp h).1), smul_zero]
    · rw [dite_eq_right hTU, map_zero]
  by_cases hTU : Disjoint T U
  swap
  · rw [dite_eq_right hTU, map_zero, dite_eq_left hST, map_smul, LinearMap.smul_apply,
      incStateCup_embed, dite_eq_right (fun h => hTU (Finset.disjoint_union_left.mp h).2),
      smul_zero]
  by_cases hSU : Disjoint S U
  swap
  · rw [dite_eq_left hST, dite_eq_left hTU, map_smul, LinearMap.smul_apply, map_smul,
      incStateCup_embed, incStateCup_embed,
      dite_eq_right (fun h => hSU (Finset.disjoint_union_left.mp h).1),
      dite_eq_right (fun h => hSU (Finset.disjoint_union_right.mp h).2), smul_zero, smul_zero]
  have hSTU : Disjoint (S ∪ T) U := Finset.disjoint_union_left.mpr ⟨hSU, hTU⟩
  have hSTU' : Disjoint S (T ∪ U) := Finset.disjoint_union_right.mpr ⟨hST, hSU⟩
  rw [dite_eq_left hST, dite_eq_left hTU, map_smul, LinearMap.smul_apply, map_smul,
    incStateCup_embed, incStateCup_embed, dite_eq_left hSTU, dite_eq_left hSTU', smul_smul,
    smul_smul]
  by_cases hov : ∃ v, 0 < G.deg T v ∧ 0 < G.deg U v
  · obtain ⟨v, hTv, hUv⟩ := hov
    have hSTv : 0 < G.deg (S ∪ T) v := by
      rw [G.deg_union_eq_add hST, Pi.add_apply]
      omega
    rw [cohomologyCup_eq_zero_of_overlap R (G.deg (S ∪ T)) (G.deg U) v hSTv hUv,
      cohomologyCup_eq_zero_of_overlap R (G.deg T) (G.deg U) v hTv hUv]
    simp only [LinearMap.zero_apply, map_zero, smul_zero]
  have hno : ∀ v, ¬ (0 < G.deg T v ∧ 0 < G.deg U v) := fun v hv => hov ⟨v, hv⟩
  have hcd : cohomologyDegree (G.deg (T ∪ U)) =
      cohomologyDegree (G.deg T) + cohomologyDegree (G.deg U) := by
    rw [G.deg_union_eq_add hTU]
    exact cohomologyDegree_add_of_forall_not_pos _ _ hno
  congr 1
  · rw [hcd, Finset.card_union_of_disjoint hST, Koszul.shuffleSign_union_left hST,
      Koszul.shuffleSign_union_right S hTU]
    simp only [add_mul, mul_add, pow_add]
    ring
  · apply G.incStateEmbed_heq R (Finset.union_assoc S T U)
    refine (castH_heq R _ _).trans ?_
    refine (cohomologyCup_heq R (G.deg_union_eq_add hST) rfl (castH_heq R _ _) HEq.rfl).trans ?_
    refine (cohomologyCup_assoc_heq R (G.deg S) (G.deg T) (G.deg U) a b c).trans ?_
    refine ((castH_heq R _ _).trans ?_).symm
    exact cohomologyCup_heq R rfl (G.deg_union_eq_add hTU) HEq.rfl (castH_heq R _ _)

/-- Associativity of the state product. -/
theorem incStateCup_assoc (x y z : G.IncResolutionBasis →₀ R) :
    G.incStateCup R (G.incStateCup R x y) z = G.incStateCup R x (G.incStateCup R y z) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single p r =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | single q s =>
      induction z using Finsupp.induction_linear with
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | single t u =>
        obtain ⟨S, κ⟩ := p
        obtain ⟨T, κ'⟩ := q
        obtain ⟨U, κ''⟩ := t
        rw [← G.incStateEmbed_single R S κ r, ← G.incStateEmbed_single R T κ' s,
          ← G.incStateEmbed_single R U κ'' u]
        exact G.incStateCup_assoc_embed R S T U _ _ _

section RingChange

variable {R} {R' : Type} [CommRing R'] (f : R →+* R')

/-- Coefficientwise ring change commutes with embedding the states of one edge set. -/
theorem incStateEmbed_mapRange (S : Finset E) (x : CechProduct.H R (G.deg S)) :
    G.incStateEmbed R' S (mapRange f (map_zero f) x) =
      mapRange f (map_zero f) (G.incStateEmbed R S x) :=
  mapDomain_mapRange _ x f (map_zero f) (map_add f)

/-- Coefficientwise ring change is a ring-change morphism of state products. -/
theorem incStateCup_mapRange (x y : G.IncResolutionBasis →₀ R) :
    G.incStateCup R' (mapRange f (map_zero f) x) (mapRange f (map_zero f) y) =
      mapRange f (map_zero f) (G.incStateCup R x y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [mapRange_zero, map_zero, LinearMap.zero_apply]
  | add x x' hx hx' =>
    rw [mapRange_add (map_add f), map_add, LinearMap.add_apply, hx, hx', map_add,
      LinearMap.add_apply, mapRange_add (map_add f)]
  | single p r =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [mapRange_zero, map_zero]
    | add y y' hy hy' =>
      rw [mapRange_add (map_add f), map_add, hy, hy', map_add, mapRange_add (map_add f)]
    | single q s =>
      obtain ⟨S, κ⟩ := p
      obtain ⟨T, κ'⟩ := q
      rw [mapRange_single, mapRange_single, incStateCup_single, incStateCup_single]
      by_cases h : Disjoint S T
      · rw [dite_eq_left h, dite_eq_left h,
          mapRange_smul' _ (f _) _ (fun z => by rw [smul_eq_mul, smul_eq_mul, map_mul]),
          ← incStateEmbed_mapRange, ← castH_mapRange, ← cohomologyCup_mapRange, mapRange_single,
          mapRange_single, map_one, map_mul, map_mul, map_mul, Koszul.map_shuffleSign, map_pow,
          map_neg, map_one]
      · rw [dite_eq_right h, dite_eq_right h, mapRange_zero]

end RingChange

end BPFixedPoints.Multigraph
