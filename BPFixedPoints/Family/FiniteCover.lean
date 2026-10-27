import BPFixedPoints.Family.BeliefRing

/-!
# Finite map to free belief coordinates

Over the open set of free coordinates (u_v,q_e), couplings satisfy
a_e²=q_e d_e/(r_e s_e). This presentation makes the belief ring integral
over the free-coordinate ring.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial BP
open scoped Ring
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

abbrev BeliefBasePoly (V E : Type) := MvPolynomial (V ⊕ E) ℂ

noncomputable def beliefBaseU (i : V) : BeliefBasePoly V E := X (Sum.inl i)
noncomputable def beliefBaseQ (e : E) : BeliefBasePoly V E := X (Sum.inr e)
noncomputable def beliefBaseR (e : E) : BeliefBasePoly V E :=
  beliefBaseU (G.fst e) - beliefBaseQ e
noncomputable def beliefBaseS (e : E) : BeliefBasePoly V E :=
  beliefBaseU (G.snd e) - beliefBaseQ e
noncomputable def beliefBaseD (e : E) : BeliefBasePoly V E :=
  1 - beliefBaseU (G.fst e) - beliefBaseU (G.snd e) + beliefBaseQ e
noncomputable def beliefBaseDen : BeliefBasePoly V E :=
  (∏ i, beliefBaseU i) * (∏ i, (1 - beliefBaseU i)) * (∏ e, beliefBaseQ e) *
    (∏ e, G.beliefBaseR e) * (∏ e, G.beliefBaseS e) * ∏ e, G.beliefBaseD e

abbrev BeliefBaseRing := Localization.Away G.beliefBaseDen

theorem beliefBaseDen_ne_zero : G.beliefBaseDen ≠ 0 := by
  let v : V ⊕ E → ℂ := Sum.elim (fun _ => 2) (fun _ => 1)
  have hu i : aeval v (beliefBaseU (E := E) i) = 2 := by simp [beliefBaseU, v]
  have hq e : aeval v (beliefBaseQ (V := V) e) = 1 := by simp [beliefBaseQ, v]
  have hr e : aeval v (G.beliefBaseR e) = 1 := by norm_num [beliefBaseR, beliefBaseU, beliefBaseQ, v]
  have hs e : aeval v (G.beliefBaseS e) = 1 := by norm_num [beliefBaseS, beliefBaseU, beliefBaseQ, v]
  have hd e : aeval v (G.beliefBaseD e) = -2 := by norm_num [beliefBaseD, beliefBaseU, beliefBaseQ, v]
  have hn : aeval v G.beliefBaseDen ≠ 0 := by
    simp only [beliefBaseDen, map_mul, map_prod, map_sub, map_one, hu, hq, hr, hs, hd]
    norm_num [Finset.prod_const, mul_ne_zero_iff, pow_ne_zero]
  intro h
  exact hn (by rw [h, map_zero])

instance beliefBaseRing_isDomain : IsDomain G.BeliefBaseRing :=
  Localization.Away.isDomain G.beliefBaseDen_ne_zero

namespace BeliefPoint

variable {G} {R : Type*} [CommRing R] [Algebra ℂ R] (p : BeliefPoint G R)

def baseVal : V ⊕ E → R := Sum.elim p.u p.q

@[simp] theorem base_eval_u (i : V) : aeval p.baseVal (beliefBaseU (E := E) i) = p.u i := by
  simp [beliefBaseU, baseVal]
@[simp] theorem base_eval_q (e : E) : aeval p.baseVal (beliefBaseQ (V := V) e) = p.q e := by
  simp [beliefBaseQ, baseVal]
@[simp] theorem base_eval_r (e : E) :
    aeval p.baseVal (G.beliefBaseR e) = p.u (G.fst e) - p.q e := by simp [beliefBaseR]
@[simp] theorem base_eval_s (e : E) :
    aeval p.baseVal (G.beliefBaseS e) = p.u (G.snd e) - p.q e := by simp [beliefBaseS]
@[simp] theorem base_eval_d (e : E) :
    aeval p.baseVal (G.beliefBaseD e) = p.d e := by simp [beliefBaseD, d]

theorem base_eval_den_unit : IsUnit (aeval p.baseVal G.beliefBaseDen) := by
  simp only [beliefBaseDen, map_mul, map_prod, map_sub, map_one,
    base_eval_u, base_eval_q, base_eval_r, base_eval_s, base_eval_d]
  exact (((((IsUnit.prod_iff.mpr fun i _ => p.u_unit i).mul
    (IsUnit.prod_iff.mpr fun i _ => p.uc_unit i)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.q_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.r_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.s_unit e)).mul
    (IsUnit.prod_iff.mpr fun e _ => p.d_unit e)

noncomputable def baseHom : G.BeliefBaseRing →ₐ[ℂ] R :=
  IsLocalization.Away.liftAlgHom _ p.base_eval_den_unit

@[simp] theorem baseHom_map (f : BeliefBasePoly V E) :
    p.baseHom (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing f) = aeval p.baseVal f :=
  IsLocalization.Away.lift_eq _ p.base_eval_den_unit _

theorem map_baseHom {S : Type*} [CommRing S] [Algebra ℂ S] (φ : R →ₐ[ℂ] S) :
    (p.map φ.toRingHom).baseHom = φ.comp p.baseHom := by
  apply IsLocalization.algHom_ext (Submonoid.powers G.beliefBaseDen)
  apply MvPolynomial.algHom_ext
  intro i
  change (p.map φ.toRingHom).baseHom
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X i)) =
    φ (p.baseHom (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X i)))
  simp only [baseHom_map, MvPolynomial.aeval_X]
  rcases i with i | e <;> rfl

end BeliefPoint

noncomputable def beliefRingPoint : BeliefPoint G G.BeliefRing :=
  G.beliefPointOfHom (AlgHom.id ℂ G.BeliefRing)

noncomputable def beliefBaseHom : G.BeliefBaseRing →ₐ[ℂ] G.BeliefRing :=
  G.beliefRingPoint.baseHom

noncomputable instance beliefBaseAlgebra : Algebra G.BeliefBaseRing G.BeliefRing :=
  G.beliefBaseHom.toAlgebra

instance beliefBaseScalarTower : IsScalarTower ℂ G.BeliefBaseRing G.BeliefRing :=
  IsScalarTower.of_algebraMap_eq' G.beliefBaseHom.comp_algebraMap.symm

@[simp] theorem beliefBaseHom_map (f : BeliefBasePoly V E) :
    algebraMap G.BeliefBaseRing G.BeliefRing (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing f) =
      aeval G.beliefRingPoint.baseVal f :=
  G.beliefRingPoint.baseHom_map f

theorem beliefBase_unit_factors :
    (∀ i, IsUnit (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseU i))) ∧
    (∀ i, IsUnit (1 - algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseU i))) ∧
    (∀ e, IsUnit (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e))) ∧
    (∀ e, IsUnit (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e))) ∧
    (∀ e, IsUnit (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e))) ∧
    (∀ e, IsUnit (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseD e))) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := G.BeliefBaseRing) G.beliefBaseDen
  simp only [beliefBaseDen, map_mul, map_prod, map_sub, map_one, IsUnit.mul_iff,
    IsUnit.prod_univ_iff] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

noncomputable def beliefBaseSquare (e : E) : G.BeliefBaseRing :=
  algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e) *
    algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseD e) *
    (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e))⁻¹ʳ *
    (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e))⁻¹ʳ

theorem beliefBaseSquare_unit (e : E) : IsUnit (G.beliefBaseSquare e) := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.beliefBase_unit_factors
  exact (((hq e).mul (hd e)).mul (unit_ringInverse (hr e))).mul (unit_ringInverse (hs e))

theorem beliefBaseSquare_mul (e : E) :
    G.beliefBaseSquare e * algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e) *
      algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e) =
    algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e) *
      algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseD e) := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.beliefBase_unit_factors
  dsimp only [beliefBaseSquare]
  calc
    _ = (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e) *
        algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseD e)) *
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e) *
        (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e))⁻¹ʳ) *
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e) *
        (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e))⁻¹ʳ) := by ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ (hr e), Ring.mul_inverse_cancel _ (hs e)]; ring

theorem beliefRingPoint_a_sq (e : E) :
    G.beliefRingPoint.a e ^ 2 = algebraMap G.BeliefBaseRing G.BeliefRing (G.beliefBaseSquare e) := by
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.beliefBase_unit_factors
  simp only [beliefBaseSquare, map_mul,
    (hr e).map_ringInverse (algebraMap G.BeliefBaseRing G.BeliefRing),
    (hs e).map_ringInverse (algebraMap G.BeliefBaseRing G.BeliefRing),
    beliefBaseHom_map, BeliefPoint.base_eval_q, BeliefPoint.base_eval_d,
    BeliefPoint.base_eval_r, BeliefPoint.base_eval_s]
  have h := G.beliefRingPoint.equation e
  have hri := Ring.mul_inverse_cancel _ (G.beliefRingPoint.r_unit e)
  have hsi := Ring.mul_inverse_cancel _ (G.beliefRingPoint.s_unit e)
  change _ = G.beliefRingPoint.q e * G.beliefRingPoint.d e at h
  linear_combination ((G.beliefRingPoint.u (G.fst e) - G.beliefRingPoint.q e)⁻¹ʳ *
      (G.beliefRingPoint.u (G.snd e) - G.beliefRingPoint.q e)⁻¹ʳ) * h +
    -(G.beliefRingPoint.a e ^ 2) * hri +
    -(G.beliefRingPoint.a e ^ 2) *
      ((G.beliefRingPoint.u (G.fst e) - G.beliefRingPoint.q e) *
        (G.beliefRingPoint.u (G.fst e) - G.beliefRingPoint.q e)⁻¹ʳ) * hsi

theorem beliefRingPoint_a_integral (e : E) :
    IsIntegral G.BeliefBaseRing (G.beliefRingPoint.a e) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [G.beliefRingPoint_a_sq]
  exact isIntegral_algebraMap

theorem beliefRing_integral : Algebra.IsIntegral G.BeliefBaseRing G.BeliefRing := by
  let T := integralClosure G.BeliefBaseRing G.BeliefRing
  let p := G.beliefRingPoint
  let u : V → T := fun i => algebraMap G.BeliefBaseRing T
    (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseU i))
  let q : E → T := fun e => algebraMap G.BeliefBaseRing T
    (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e))
  let a : E → T := fun e => ⟨p.a e, G.beliefRingPoint_a_integral e⟩
  have hu (i : V) : (u i : G.BeliefRing) = p.u i := by
    change algebraMap G.BeliefBaseRing G.BeliefRing
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseU i)) = p.u i
    simp [p]
  have hq (e : E) : (q e : G.BeliefRing) = p.q e := by
    change algebraMap G.BeliefBaseRing G.BeliefRing
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e)) = p.q e
    simp [p]
  have hr (e : E) : u (G.fst e) - q e = algebraMap G.BeliefBaseRing T
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseR e)) := by simp only [u, q, beliefBaseR, RingHom.map_sub]
  have hs (e : E) : u (G.snd e) - q e = algebraMap G.BeliefBaseRing T
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseS e)) := by simp only [u, q, beliefBaseS, RingHom.map_sub]
  have hd (e : E) : 1 - u (G.fst e) - u (G.snd e) + q e = algebraMap G.BeliefBaseRing T
      (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (G.beliefBaseD e)) := by simp only [u, q, beliefBaseD, RingHom.map_sub, RingHom.map_add, RingHom.map_one]
  obtain ⟨huu, huc, hqu, hru, hsu, hdu⟩ := G.beliefBase_unit_factors
  have hau (e : E) : IsUnit (a e) := by
    apply (isUnit_pow_iff (n := 2) (by decide)).mp
    have he : a e ^ 2 = algebraMap G.BeliefBaseRing T (G.beliefBaseSquare e) := by
      apply Subtype.ext
      exact G.beliefRingPoint_a_sq e
    rw [he]
    exact (G.beliefBaseSquare_unit e).map (algebraMap G.BeliefBaseRing T)
  let p' : BeliefPoint G T :=
    { a := a
      u := u
      q := q
      a_unit := hau
      u_unit i := (huu i).map (algebraMap G.BeliefBaseRing T)
      uc_unit i := by simpa only [RingHom.map_sub, RingHom.map_one, u] using (huc i).map (algebraMap G.BeliefBaseRing T)
      q_unit e := (hqu e).map (algebraMap G.BeliefBaseRing T)
      r_unit e := by rw [hr]; exact (hru e).map (algebraMap G.BeliefBaseRing T)
      s_unit e := by rw [hs]; exact (hsu e).map (algebraMap G.BeliefBaseRing T)
      d_unit e := by rw [hd]; exact (hdu e).map (algebraMap G.BeliefBaseRing T)
      equation e := by
        apply Subtype.ext
        simpa only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_sub,
          Subalgebra.coe_add, Subalgebra.coe_one, hu, hq] using p.equation e }
  let φ : T →ₐ[ℂ] G.BeliefRing := (integralClosure G.BeliefBaseRing G.BeliefRing).val.restrictScalars ℂ
  have hp : p'.map φ.toRingHom = p := by
    ext i
    · rfl
    · exact hu i
    · exact hq i
  have hf : φ.comp p'.toHom = AlgHom.id ℂ G.BeliefRing := by
    rw [← BeliefPoint.map_toHom, hp]
    exact G.toHom_beliefPointOfHom _
  refine Algebra.isIntegral_def.mpr fun x => ?_
  have hx := (p'.toHom x).2
  have he : (p'.toHom x : G.BeliefRing) = x := congrArg (fun f : G.BeliefRing →ₐ[ℂ] G.BeliefRing => f x) hf
  exact he ▸ hx

instance beliefRing_finiteType : Algebra.FiniteType ℂ G.BeliefRing := inferInstance

theorem beliefRing_finite : Module.Finite G.BeliefBaseRing G.BeliefRing := by
  letI := G.beliefRing_integral
  letI : Algebra.FiniteType G.BeliefBaseRing G.BeliefRing :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ G.BeliefBaseRing G.BeliefRing
  exact Algebra.IsIntegral.finite

theorem beliefBaseHom_injective : Function.Injective G.beliefBaseHom := by
  let K := FractionRing G.BeliefBaseRing
  let L := AlgebraicClosure K
  let ι : G.BeliefBaseRing →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ G.BeliefBaseRing L
  have hι : Function.Injective ι := by
    change Function.Injective (algebraMap G.BeliefBaseRing L)
    rw [IsScalarTower.algebraMap_eq G.BeliefBaseRing K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective G.BeliefBaseRing K)
  let u : V → L := fun i => ι (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseU i))
  let q : E → L := fun e => ι (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (beliefBaseQ e))
  have he (e : E) : ∃ a : L, a ^ 2 = ι (G.beliefBaseSquare e) :=
    IsAlgClosed.exists_pow_nat_eq _ (by decide)
  choose a ha using he
  obtain ⟨hu, huc, hq, hr, hs, hd⟩ := G.beliefBase_unit_factors
  let p : BeliefPoint G L :=
    { a := a
      u := u
      q := q
      a_unit e := by
        apply (isUnit_pow_iff (n := 2) (by decide)).mp
        rw [ha]
        exact (G.beliefBaseSquare_unit e).map ι
      u_unit i := (hu i).map ι
      uc_unit i := by simpa [u] using (huc i).map ι
      q_unit e := (hq e).map ι
      r_unit e := by simpa [u, q, beliefBaseR] using (hr e).map ι
      s_unit e := by simpa [u, q, beliefBaseS] using (hs e).map ι
      d_unit e := by simpa [u, q, beliefBaseD] using (hd e).map ι
      equation e := by
        have h := congrArg ι (G.beliefBaseSquare_mul e)
        simpa [map_mul, ← ha e, beliefBaseR, beliefBaseS, beliefBaseD, u, q] using h }
  have hp : G.beliefRingPoint.map p.toHom.toRingHom = p := by
    change (G.beliefPointOfHom (AlgHom.id ℂ G.BeliefRing)).map p.toHom.toRingHom = p
    rw [G.beliefPointOfHom_map, AlgHom.comp_id, G.beliefPointOfHom_toHom]
  have hf : p.toHom.comp G.beliefBaseHom = ι := by
    change p.toHom.comp G.beliefRingPoint.baseHom = ι
    rw [← BeliefPoint.map_baseHom, hp]
    apply IsLocalization.algHom_ext (Submonoid.powers G.beliefBaseDen)
    apply MvPolynomial.algHom_ext
    intro j
    change p.baseHom (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X j)) =
      ι (algebraMap (BeliefBasePoly V E) G.BeliefBaseRing (X j))
    rw [BeliefPoint.baseHom_map, MvPolynomial.aeval_X]
    rcases j with i | e <;> rfl
  have hinj : Function.Injective (p.toHom.comp G.beliefBaseHom) := hf ▸ hι
  intro x y hxy
  apply hinj
  exact congrArg p.toHom hxy

end BPFixedPoints.Multigraph
