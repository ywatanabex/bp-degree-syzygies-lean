import BPFixedPoints.Incidence.Torus

/-!
# Integral closedness of the universal incidence ring

Every chart is a polynomial ring and the torus its localization. A torus
element integral over 𝒰_G extends to each chart, hence to their intersection
𝒰_G. Together with integral closedness of the torus, this makes 𝒰_G a normal domain.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

instance incLocal_isIntegrallyClosed : IsIntegrallyClosed (IncLocalRing V E) :=
  isIntegrallyClosed_of_isLocalization (IncLocalRing V E)
    (Submonoid.powers (incFreeDen (V := V) (E := E)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors incFreeDen_ne_zero)

/-- The free polynomial ring is integrally closed in its vertex-coordinate localization. -/
instance incLocal_isIntegrallyClosedIn : IsIntegrallyClosedIn (IncFreeRing V E) (IncLocalRing V E) := by
  let A := IncFreeRing V E
  let L := IncLocalRing V E
  let K := FractionRing A
  let M := Submonoid.powers (incFreeDen (V := V) (E := E))
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors (incFreeDen_ne_zero (V := V) (E := E))
  let f : L →ₐ[A] K := Localization.mapToFractionRing K M L hM
  have hf : Function.Injective f := by
    apply (IsLocalization.lift_injective_iff (Localization.map_isUnit_of_le K M hM)).mpr
    intro x y
    exact ⟨fun h => congrArg _ (IsLocalization.injective L hM h),
      fun h => congrArg _ (IsFractionRing.injective A K h)⟩
  exact f.isIntegrallyClosedIn hf inferInstance

variable (G : Multigraph V E)

instance incTorus_isIntegrallyClosed : IsIntegrallyClosed G.IncTorusRing :=
  IsIntegrallyClosed.of_equiv (G.incTorusEquiv (fun _ => false)).symm.toRingEquiv

/-- A torus element integral over 𝒰_G extends to every chart. -/
theorem integral_mem_incChartRange {x : G.IncTorusRing} (hx : IsIntegral G.IncidenceRing x)
    (σ : V → Bool) : x ∈ (G.incChartMap σ).range := by
  let e := AlgEquiv.ofInjective (G.incChartMap σ) (G.incChartMap_injective σ)
  have hle : G.IncidenceRing ≤ (G.incChartMap σ).range := iInf_le _ σ
  let φ : G.IncidenceRing →+* IncFreeRing V E :=
    (G.incChartEquiv σ).toRingHom.comp
      (e.symm.toRingHom.comp (Subalgebra.inclusion hle).toRingHom)
  have hcomm : (algebraMap (IncFreeRing V E) (IncLocalRing V E)).comp φ =
      (G.incTorusToLocal σ).toRingHom.comp (algebraMap G.IncidenceRing G.IncTorusRing) := by
    apply RingHom.ext
    intro u
    have he : G.incChartMap σ (e.symm ((Subalgebra.inclusion hle) u)) = (u : G.IncTorusRing) :=
      congrArg Subtype.val (e.apply_symm_apply _)
    change algebraMap _ _ (G.incChartEquiv σ (e.symm ((Subalgebra.inclusion hle) u))) = _
    rw [← incTorusToLocal_chart_apply, he]
    rfl
  have hx' := hx.map_of_comp_eq φ (G.incTorusToLocal σ).toRingHom hcomm
  obtain ⟨p, hp⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hx'
  refine ⟨(G.incChartEquiv σ).symm p, ?_⟩
  apply (G.incTorusEquiv σ).injective
  change G.incTorusToLocal σ (G.incChartMap σ ((G.incChartEquiv σ).symm p)) = _
  rw [incTorusToLocal_chart_apply, AlgEquiv.apply_symm_apply]
  exact hp

instance incidenceRing_isIntegrallyClosedIn : IsIntegrallyClosedIn G.IncidenceRing G.IncTorusRing := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨Subtype.val_injective, fun {x} hx => ?_⟩
  have hxmem : x ∈ G.IncidenceRing := by
    rw [IncidenceRing, Algebra.mem_iInf]
    exact G.integral_mem_incChartRange hx
  exact ⟨⟨x, hxmem⟩, rfl⟩

/-- **Normality in `alg:normal-cm`.** 𝒰_G is integrally closed in its fraction field. -/
theorem incidenceRing_isIntegrallyClosed : IsIntegrallyClosed G.IncidenceRing :=
  IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
    (R := G.IncidenceRing) (S := G.IncTorusRing)

end BPFixedPoints.Multigraph
