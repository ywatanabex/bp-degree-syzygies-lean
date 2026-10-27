import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization

/-! # Finite-type field extensions and finiteness of relative integral closures -/

namespace BPFixedPoints.IntegralTools

open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin

/-- Adjoining algebraically independent elements preserves linear independence of coefficients. -/
theorem linearIndependent_adjoin
    {K L F ι σ : Type*} [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F]
    {b : ι → L} (hb : LinearIndependent K b) {t : σ → F}
    (ht : AlgebraicIndependent L t) :
    LinearIndependent (IntermediateField.adjoin K (Set.range t))
      (fun i => algebraMap L F (b i)) := by
  classical
  have htK : AlgebraicIndependent K t :=
    ht.restrictScalars (FaithfulSMul.algebraMap_injective K L)
  apply (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range t))
    (IntermediateField.adjoin K (Set.range t))).mp
  rw [linearIndependent_iff']
  intro s g hsum i hi
  change ∑ j ∈ s, (g j : F) * algebraMap L F (b j) = 0 at hsum
  let p : ι → MvPolynomial σ K := fun j => htK.aevalEquiv.symm (g j)
  have hp (j : ι) : aeval t (p j) = (g j : F) :=
    congrArg Subtype.val (htK.aevalEquiv.apply_symm_apply (g j))
  have heval (q : MvPolynomial σ K) :
      aeval (R := L) t (map (algebraMap K L) q) = aeval (R := K) t q := by
    simp only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq]
  have hq : ∑ j ∈ s, map (algebraMap K L) (p j) * C (b j) = 0 := by
    apply (algebraicIndependent_iff_injective_aeval.mp ht)
    simpa only [map_sum, map_mul, aeval_C, heval, hp, map_zero] using hsum
  have hpi : p i = 0 := by
    ext d
    have hc := congrArg (fun q : MvPolynomial σ L => q.coeff d) hq
    simp [coeff_C_mul, mul_comm, coeff_map] at hc
    exact (linearIndependent_iff'.mp hb) s (fun j => (p j).coeff d)
      (by simpa only [Algebra.smul_def, mul_comm] using hc) i hi
  apply htK.aevalEquiv.symm.injective
  simpa only [map_zero] using hpi

/-- The relative algebraic closure in a finitely generated field extension is finite. -/
theorem finite_algebraicClosure (K F : Type*) [Field K] [Field F]
    [Algebra K F] [Algebra.EssFiniteType K F] :
    Module.Finite K (algebraicClosure K F) := by
  obtain ⟨σ, t, ht⟩ := exists_isTranscendenceBasis' K F
  let T := IntermediateField.adjoin K (Set.range t)
  let L := algebraicClosure K F
  have : Algebra.IsAlgebraic T F := ht.isAlgebraic_field
  have : Algebra.EssFiniteType T F := Algebra.EssFiniteType.of_comp K T F
  have : Module.Finite T F := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let b := Module.Basis.ofVectorSpace K L
  have hlin := linearIndependent_adjoin b.linearIndependent (ht.1.extendScalars L)
  have : Finite (Module.Basis.ofVectorSpaceIndex K L) := hlin.finite
  exact Module.Finite.of_basis b

/-- For a normal Noetherian ring of characteristic zero, its integral closure in a finitely generated field extension is finite. -/
theorem finite_integralClosure_of_essFiniteType (R F : Type*)
    [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [FaithfulSMul R F] [Algebra.EssFiniteType R F] :
    Module.Finite R (integralClosure R F) := by
  let K := FractionRing R
  let : Algebra K F := FractionRing.liftAlgebra R F
  have : IsScalarTower R K F := FractionRing.isScalarTower_liftAlgebra R F
  have : Algebra.EssFiniteType K F := Algebra.EssFiniteType.of_comp R K F
  let L := algebraicClosure K F
  have : Module.Finite K L := finite_algebraicClosure K F
  have : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R K L (integralClosure R L)
  let f : integralClosure R F →ₗ[R] integralClosure R L :=
    { toFun := fun x =>
        ⟨⟨x.val, mem_algebraicClosure_iff'.mpr x.property.tower_top⟩,
          IntermediateField.coe_isIntegral_iff.mp x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro x y h
  exact Subtype.ext (congrArg (fun z : integralClosure R L => (z.val : F)) h)

/-- An integral extension of a finite-type algebra embedded in a finitely generated field is finite. -/
theorem finite_of_integral_of_field_embedding
    {k R A F : Type*} [Field k] [CharZero k] [CommRing R] [Nontrivial R]
    [CommRing A] [Field F] [Algebra k R] [Algebra k A] [Algebra k F]
    [Algebra.FiniteType k R] [Algebra.EssFiniteType k F]
    (f : R →ₐ[k] A) (g : A →ₐ[k] F)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hint : f.toRingHom.IsIntegral) : f.toRingHom.Finite := by
  obtain ⟨n, φ, hφ, hφfin⟩ := exists_finite_inj_algHom_of_fg k R
  let N := MvPolynomial (Fin n) k
  let h : N →ₐ[k] A := f.comp φ
  let j : N →ₐ[k] F := g.comp h
  let : Algebra N A := h.toRingHom.toAlgebra
  let : Algebra N F := j.toRingHom.toAlgebra
  have : IsScalarTower k N F := IsScalarTower.of_algHom j
  have : FaithfulSMul N F :=
    (faithfulSMul_iff_algebraMap_injective N F).mpr (hg.comp (hf.comp hφ))
  have : Algebra.EssFiniteType N F := Algebra.EssFiniteType.of_comp k N F
  have : Module.Finite N (integralClosure N F) :=
    finite_integralClosure_of_essFiniteType N F
  have hh : h.toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans φ.toRingHom f.toRingHom hφfin.to_isIntegral hint
  let ι : A →ₐ[N] F :=
    { toRingHom := g.toRingHom
      commutes' := fun _ => rfl }
  let ι' : A →ₐ[N] integralClosure N F :=
    ι.codRestrict (integralClosure N F) (fun x => (show IsIntegral N x from hh x).map ι)
  have hhfin : h.toRingHom.Finite := by
    apply Module.Finite.of_injective ι'.toLinearMap
    intro x y heq
    exact hg (congrArg Subtype.val heq)
  exact RingHom.Finite.of_comp_finite hhfin

end BPFixedPoints.IntegralTools
