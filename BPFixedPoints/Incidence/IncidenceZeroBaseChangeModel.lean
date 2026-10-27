import BPFixedPoints.Incidence.IncidenceTorNormalization
import BPFixedPoints.Incidence.IncidenceRelabelResolution
import BPFixedPoints.Incidence.CechProductRingChange

/-! # Base change of the Čech–Koszul model to the coefficient origin

The paper (end of the proof of Theorem 3.4) computes `𝒰_G ⊗^L_{S_G} ℂ` from the bounded Čech
model `K = IncTotalModule` with total differential `D = d_Čech + δ_Koszul`
(`incTotalDifferential`). This file carries out the base change of that model and of the
perturbation data along the coefficient origin `constantCoeff : S_G → ℂ`.

* **The base-changed model.** `ZbcModule V E` is the same free module of exterior states and
  Čech monomials over `ℂ`; `zbcContraction` is the direct sum over edge subsets `S` of the
  product Čech contractions of `O(-d_S)` over `ℂ`; its differential is the Čech differential of
  `⊕_S O(-d_S)` on the product of the standard two-chart covers.
* **Specialization.** `zbcSpecialize : K → ZbcModule` and `zbcFreeSpecialize` (on the free
  resolution module) apply `constantCoeff` to every coefficient; they are semilinear over the
  origin and kill the augmentation ideal multiples (`zbc_map_eq_zero_of_mem`).
* **The Koszul part vanishes at the origin** (`zbcSpecialize_koszul`, `zbc_baseChange_koszul`),
  so the specialization intertwines `D` with the Čech differential over `ℂ`
  (`zbcSpecialize_total`).
* **Base change of the perturbation data.** The perturbed inclusion `ι = incResolutionInclusion`
  and projection `P = incResolutionProjection` of the finite homological perturbation specialize
  to the *unperturbed* Čech inclusion and projection over `ℂ` (`zbcSpecialize_inclusion`,
  `zbcFreeSpecialize_projection`): their corrections lie in the augmentation ideal multiples. The
  transferred differential of the free resolution specializes to zero
  (`zbcFreeSpecialize_differential`).
* **Freeness.** `K` is a free `S_G`-module (`incTotalModule_free`), so `ℂ ⊗_{S_G} K` computes
  the derived tensor product. `zbcBaseChangeEquiv : ℂ ⊗_{S_G} K ≃ ZbcModule` is the canonical
  isomorphism (Mathlib's `finsuppRight` and `finsuppScalarRight`); it sends `c ⊗ x` to
  `c • zbcSpecialize x` and carries `D ⊗ ℂ` to the Čech differential over `ℂ`
  (`zbcBaseChangeEquiv_differential`).
* **The base-changed comparison on Tor.** `zbcTorCycle p` is the composite of the derived-functor
  identification `Tor_p ≅ ℂ ⊗ F_p` (`incidenceTorToFull`), the base change of the chain map
  `ι : F → K`, and `zbcBaseChangeEquiv`. It is defined without state coordinates.
-/

namespace BPFixedPoints.Multigraph

open CechProduct IncidencePerturbation Finsupp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable section

/-- The base-changed Čech model over `ℂ`. -/
abbrev ZbcModule (V E : Type) [DecidableEq E] := Koszul.Space E (CechProduct.C ℂ V)

/-- The coefficient origin. -/
abbrev zbcOrigin (E : Type) : IncCoeffRing E →+* ℂ := MvPolynomial.constantCoeff

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- The bounded Čech–Koszul model is a free module over the coefficient ring. -/
theorem incTotalModule_free : Module.Free (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) :=
  inferInstance

/-- Statewise Čech contraction over ℂ. -/
def zbcContraction : Contraction ℂ (ZbcModule V E) (G.IncResolutionBasis →₀ ℂ) :=
  Contraction.finsupp fun S => (CechProduct.contraction ℂ (G.deg S)).toContraction

@[simp] theorem zbcContraction_d_apply (x : ZbcModule V E) (S : Finset E) :
    G.zbcContraction.d x S = (CechProduct.contraction ℂ (G.deg S)).d (x S) := rfl

@[simp] theorem zbcContraction_h_apply (x : ZbcModule V E) (S : Finset E) :
    G.zbcContraction.h x S = (CechProduct.contraction ℂ (G.deg S)).h (x S) := rfl

@[simp] theorem zbcContraction_i_apply (s : G.IncResolutionBasis →₀ ℂ) (S : Finset E) :
    G.zbcContraction.i s S =
      (CechProduct.contraction ℂ (G.deg S)).i ((Finsupp.sigmaFinsuppLEquivPiFinsupp ℂ) s S) := rfl

@[simp] theorem zbcContraction_p_apply (x : ZbcModule V E) (S : Finset E)
    (k : CechProduct.HBasis (G.deg S)) :
    G.zbcContraction.p x ⟨S, k⟩ = (CechProduct.contraction ℂ (G.deg S)).p (x S) k := rfl

/-- Specialization of the total module at the coefficient origin, coefficient by coefficient. -/
def zbcSpecialize : IncTotalModule (V := V) (E := E) →ₛₗ[zbcOrigin E] ZbcModule V E where
  toFun x := mapRange (fun c => mapRange (zbcOrigin E) (map_zero _) c) (by simp) x
  map_add' x y := by
    ext S b
    simp
  map_smul' r x := by
    ext S b
    simp

/-- Specialization of the free resolution module at the coefficient origin. -/
def zbcFreeSpecialize :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₛₗ[zbcOrigin E] (G.IncResolutionBasis →₀ ℂ) where
  toFun y := mapRange (zbcOrigin E) (map_zero _) y
  map_add' x y := by
    ext b
    simp
  map_smul' r x := by
    ext b
    simp

theorem zbcSpecialize_apply (x : IncTotalModule (V := V) (E := E)) (S : Finset E) :
    zbcSpecialize x S = mapRange (zbcOrigin E) (map_zero _) (x S) := by
  simp [zbcSpecialize]

theorem zbcFreeSpecialize_apply (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.zbcFreeSpecialize y = mapRange (zbcOrigin E) (map_zero _) y := rfl

/-- A semilinear map over the coefficient origin kills the augmentation ideal multiples. -/
theorem zbc_map_eq_zero_of_mem {M N : Type*} [AddCommMonoid M] [Module (IncCoeffRing E) M]
    [AddCommMonoid N] [Module ℂ N] (f : M →ₛₗ[zbcOrigin E] N) {x : M}
    (hx : x ∈ incCoeffAugmentationIdeal E • (⊤ : Submodule (IncCoeffRing E) M)) : f x = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smulₛₗ]
    have h0 : zbcOrigin E r = 0 := hr
    rw [h0, zero_smul]
  · rw [map_add, hx, hy, add_zero]

/-- The Koszul part of the total differential vanishes at the coefficient origin. -/
theorem zbcSpecialize_koszul (x : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (G.incKoszulPerturbation x) = 0 :=
  zbc_map_eq_zero_of_mem zbcSpecialize (G.incKoszulPerturbation_mem_augmentation x)

/-- Specialization intertwines the Čech differentials over `S_G` and over `ℂ`. -/
theorem zbcSpecialize_cech (x : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (G.incCechContraction.d x) = G.zbcContraction.d (zbcSpecialize x) := by
  ext S : 1
  rw [zbcContraction_d_apply, zbcSpecialize_apply, zbcSpecialize_apply, incCechContraction_d_apply,
    contraction_d_mapRange]

/-- Specialization intertwines the total differential with the Čech differential over `ℂ`. -/
theorem zbcSpecialize_total (x : IncTotalModule (V := V) (E := E)) :
    zbcSpecialize (G.incTotalDifferential x) = G.zbcContraction.d (zbcSpecialize x) := by
  rw [incTotalDifferential, LinearMap.add_apply, map_add, zbcSpecialize_koszul, add_zero,
    zbcSpecialize_cech]

/-- Specialization intertwines the Čech inclusions over `S_G` and over `ℂ`. -/
theorem zbcSpecialize_i (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    zbcSpecialize (G.incCechContraction.i y) = G.zbcContraction.i (G.zbcFreeSpecialize y) := by
  ext S : 1
  rw [zbcContraction_i_apply, zbcSpecialize_apply, incCechContraction_i_apply,
    ← contraction_i_mapRange]
  congr 1
  ext κ
  simp [zbcFreeSpecialize_apply, sigmaFinsuppLEquivPiFinsupp_apply]

/-- Specialization intertwines the Čech projections over `S_G` and over `ℂ`. -/
theorem zbcFreeSpecialize_p (x : IncTotalModule (V := V) (E := E)) :
    G.zbcFreeSpecialize (G.incCechContraction.p x) = G.zbcContraction.p (zbcSpecialize x) := by
  ext ⟨S, κ⟩
  rw [zbcContraction_p_apply, zbcFreeSpecialize_apply, mapRange_apply, incCechContraction_p_apply,
    zbcSpecialize_apply, contraction_p_mapRange, mapRange_apply]

/-- **Base change of the perturbed inclusion.** At the coefficient origin the perturbed inclusion
`ι` of the homological perturbation is the unperturbed Čech inclusion over `ℂ`. -/
theorem zbcSpecialize_inclusion (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    zbcSpecialize (G.incResolutionInclusion y) = G.zbcContraction.i (G.zbcFreeSpecialize y) := by
  have h := G.incCechContraction.inclusion_sub_mem_ideal (incCoeffAugmentationIdeal E)
    G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation y
  have h0 := zbc_map_eq_zero_of_mem zbcSpecialize h
  rw [map_sub, sub_eq_zero] at h0
  rw [incResolutionInclusion, h0, zbcSpecialize_i]

/-- **Base change of the perturbed projection.** At the coefficient origin the perturbed projection
`P` is the unperturbed Čech projection over `ℂ`. -/
theorem zbcFreeSpecialize_projection (x : IncTotalModule (V := V) (E := E)) :
    G.zbcFreeSpecialize (G.incResolutionProjection x) = G.zbcContraction.p (zbcSpecialize x) := by
  have h := G.incCechContraction.projection_sub_mem_ideal (incCoeffAugmentationIdeal E)
    G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x
  have h0 := zbc_map_eq_zero_of_mem G.zbcFreeSpecialize h
  rw [map_sub, sub_eq_zero] at h0
  rw [incResolutionProjection, h0, zbcFreeSpecialize_p]

/-- The transferred differential of the free resolution vanishes at the coefficient origin. -/
theorem zbcFreeSpecialize_differential (y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.zbcFreeSpecialize (G.incResolutionDifferential y) = 0 :=
  zbc_map_eq_zero_of_mem G.zbcFreeSpecialize (G.incResolutionDifferential_minimal y)

section BaseChange

local instance zeroBaseChangeOriginAlgebra : Algebra (IncCoeffRing E) ℂ := (zbcOrigin E).toAlgebra

/-- The base change of the Čech–Koszul total module along the coefficient origin is the
base-changed Čech model. -/
def zbcBaseChangeEquiv :
    ℂ ⊗[IncCoeffRing E] IncTotalModule (V := V) (E := E) ≃ₗ[ℂ] ZbcModule V E :=
  (TensorProduct.finsuppRight (IncCoeffRing E) ℂ ℂ (IncCechModule (V := V) (E := E)) (Finset E)).trans
    (Finsupp.mapRange.linearEquiv
      (TensorProduct.finsuppScalarRight (IncCoeffRing E) ℂ ℂ (V → CechProduct.Basis)))

/-- The base-change isomorphism on pure tensors. -/
theorem zbcBaseChangeEquiv_tmul (c : ℂ) (x : IncTotalModule (V := V) (E := E)) :
    zbcBaseChangeEquiv (c ⊗ₜ x) = c • zbcSpecialize x := by
  ext S b
  simp only [zbcBaseChangeEquiv, LinearEquiv.trans_apply, mapRange.linearEquiv_apply,
    mapRange_apply, TensorProduct.finsuppRight_apply_tmul_apply,
    TensorProduct.finsuppScalarRight_apply_tmul_apply, Finsupp.smul_apply, zbcSpecialize_apply,
    Algebra.smul_def, mul_comm]
  rfl

/-- The base change of the total differential is the Čech differential over `ℂ`. -/
theorem zbcBaseChangeEquiv_differential (t : ℂ ⊗[IncCoeffRing E] IncTotalModule (V := V) (E := E)) :
    zbcBaseChangeEquiv (G.incTotalDifferential.baseChange ℂ t) =
      G.zbcContraction.d (zbcBaseChangeEquiv t) := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul, zbcBaseChangeEquiv_tmul,
      zbcSpecialize_total, map_smul]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- The base change of the Koszul part of the differential is zero. -/
theorem zbc_baseChange_koszul :
    G.incKoszulPerturbation.baseChange ℂ = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c x
  apply zbcBaseChangeEquiv.injective
  rw [LinearMap.baseChange_tmul, zbcBaseChangeEquiv_tmul, zbcSpecialize_koszul, smul_zero,
    LinearMap.zero_apply, map_zero]

/-- The base change of the comparison chain map, on Tor. -/
def zbcTorCycle (p : ℕ) : G.incidenceTor p →ₗ[ℂ] ZbcModule V E :=
  zbcBaseChangeEquiv.toLinearMap ∘ₗ (G.incResolutionInclusion.baseChange ℂ) ∘ₗ G.incidenceTorToFull p

/-- On the specialization of a free-resolution element, the base-changed comparison is the
specialization of its image under `ι`. -/
theorem zbcTorCycle_class (p : ℕ) (x : G.IncFreeTerm p) :
    G.zbcTorCycle p (G.incFreeTermToTor p x) = zbcSpecialize (G.incResolutionInclusion x.val) := by
  rw [zbcTorCycle, LinearMap.comp_apply, LinearMap.comp_apply, incidenceTorToFull_class,
    LinearMap.baseChange_tmul, LinearEquiv.coe_coe, zbcBaseChangeEquiv_tmul, one_smul]

end BaseChange

end

end BPFixedPoints.Multigraph
