import BPFixedPoints.Incidence.IncidenceCutTorProduct

/-! # Actual scalar-extended multiplication chain maps after parameter cuts

The source is the scalar extension of the original tensor complex and the target
is the actual changed projective resolution. All differentials and chain-map
components are the original linear maps extended along the coefficient algebra.
-/

namespace BPFixedPoints.ResolutionTools
open CategoryTheory
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

universe u
variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]

/-- Coefficient extension of a concrete complex using the ambient algebra structure. -/
noncomputable def baseChangeChainComplex (K : ChainComplex (ModuleCat S) ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => R ⊗[S] K.X n)
    (fun n => (K.d (n+1) n).hom.baseChange R) (fun n => by
      rw [← LinearMap.baseChange_comp]
      have h : (K.d (n+1) n).hom.comp (K.d (n+2) (n+1)).hom = 0 := by
        exact congrArg ModuleCat.Hom.hom (K.d_comp_d (n+2) (n+1) n)
      rw [h, LinearMap.baseChange_zero])

@[simp] theorem baseChangeChainComplex_d (K : ChainComplex (ModuleCat S) ℕ) (n : ℕ) :
    (baseChangeChainComplex (R := R) K).d (n+1) n =
      ModuleCat.ofHom ((K.d (n+1) n).hom.baseChange R) :=
  linearChainComplex_d _ _ _ n

/-- A scalar-extended complex of free modules still has projective terms. -/
noncomputable instance baseChangeChainComplex_projective
    (K : ChainComplex (ModuleCat S) ℕ) [∀ n, Module.Free S (K.X n)] (n : ℕ) :
    Projective ((baseChangeChainComplex (R := R) K).X n) :=
  ModuleCat.projective_of_free ((Module.Free.chooseBasis S (K.X n)).baseChange R)

/-- Minimality is preserved for the entire scalar-extended tensor source. -/
theorem baseChangeChainComplex_minimal {k : Type u} [CommRing k]
    (e : S →+* k) (e' : R →+* k) (he : e'.comp (algebraMap S R) = e)
    (K : ChainComplex (ModuleCat S) ℕ)
    (hK : ∀ i j, LinearMap.range (K.d i j).hom ≤
      RingHom.ker e • (⊤ : Submodule S (K.X j))) (i j : ℕ) :
    LinearMap.range ((baseChangeChainComplex (R := R) K).d i j).hom ≤
      RingHom.ker e' • (⊤ : Submodule R ((baseChangeChainComplex (R := R) K).X j)) := by
  by_cases h : j+1=i
  · subst i
    rw [baseChangeChainComplex_d]
    exact baseChange_minimal e e' he (K.d (j+1) j).hom (hK (j+1) j)
  · rw [(baseChangeChainComplex (R := R) K).shape i j h]
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact bot_le

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph
open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)
  (I : Ideal (MvPolynomial (Fin G.dG) ℂ))

noncomputable local instance cutLiftRingAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

/-- Scalar extension of the actual projective tensor source. -/
noncomputable def incidenceCutTensorSource :
    letI := G.incidenceCoefficientParameterAlgebra a
    ChainComplex (ModuleCat
      (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I))) ℕ := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact baseChangeChainComplex (R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ]
    (MvPolynomial (Fin G.dG) ℂ ⧸ I)) G.incTensorResolutionComplex

variable (ha : a ∈ G.incidenceFiniteParameterLocus)

/-- Extend an original multiplication lift as an actual chain map into the changed resolution. -/
noncomputable def incidenceCutMultiplicationChainMap (μ : G.IncResolutionMultiplication) :
    letI := G.incidenceCoefficientParameterAlgebra a
    G.incidenceCutTensorSource a I ⟶
      (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).complex := by
  letI := G.incidenceCoefficientParameterAlgebra a
  let R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)
  refine ChainComplex.ofHom (fun n => ModuleCat.ofHom ((μ.chainMap.f n).hom.baseChange R))
    (fun n => ?_)
  rw [G.incidenceParameterBaseChangeResolution_d]
  dsimp only [incidenceCutTensorSource]
  rw [baseChangeChainComplex_d]
  apply ModuleCat.hom_ext
  have h := congrArg ModuleCat.Hom.hom (μ.chainMap.comm (n+1) n)
  rw [G.incFreeResolution_d] at h
  have hb := congrArg (fun f => f.baseChange R) h
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.baseChange_comp] using hb

/-- On every pure tensor representative, the actual extended chain map has
exactly the multiplication formula used by the cut Tor product. -/
theorem incidenceCutMultiplicationChainMap_tmul (μ : G.IncResolutionMultiplication)
    (p q : ℕ) (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ r : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I),
      (G.incidenceCutMultiplicationChainMap a I ha μ).f (p+q)
        (r ⊗ₜ[IncCoeffRing E] (⟨freePair x.val y.val,
          freePair_degree G.incResolutionDegree p q x.property y.property⟩ :
            G.incTensorResolutionComplex.X (p+q))) =
      r ⊗ₜ[IncCoeffRing E] (⟨μ.mul x.val y.val,
        μ.homogeneous p q x.property y.property⟩ : G.IncFreeTerm (p+q)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro r
  change r ⊗ₜ[IncCoeffRing E]
    (μ.toGradedFreePairing.component (p+q) ⟨freePair x.val y.val,
      freePair_degree G.incResolutionDegree p q x.property y.property⟩) = _
  congr 1
  apply Subtype.ext
  exact μ.toGradedFreePairing.linearize_tmul x.val y.val

/-- The actual extended chain map computes the cut product on all residue
representatives; these representatives surject onto actual Tor. -/
theorem incidenceCutLiftProduct_chain_formula (hI : I ≤ RingHom.ker constantCoeff)
    (μ : G.IncResolutionMultiplication) (p q : ℕ) (x : G.IncFreeTerm p) (y : G.IncFreeTerm q) :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
    G.incidenceCutLiftProduct a I hI ha μ p q
      (G.incidenceCutResolutionClass a I hI ha p x)
      (G.incidenceCutResolutionClass a I hI ha q y) =
      G.incidenceCutFreeToTor a I hI ha (p+q)
        ((G.incidenceCutMultiplicationChainMap a I ha μ).f (p+q)
          ((1 : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)) ⊗ₜ[IncCoeffRing E]
            (⟨freePair x.val y.val, freePair_degree G.incResolutionDegree p q x.property y.property⟩ :
              G.incTensorResolutionComplex.X (p+q)))) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := tensorQuotientScalarTower (k := ℂ) (S := IncCoeffRing E) I
  rw [G.incidenceCutLiftProduct_on_classes, G.incidenceCutMultiplicationChainMap_tmul]
  rfl

/-- Scalar extension preserves equality of the actual augmented multiplication lifts. -/
theorem incidenceCutMultiplicationChainMap_augmentation_eq
    (μ ν : G.IncResolutionMultiplication) :
    letI := G.incidenceCoefficientParameterAlgebra a
    G.incidenceCutMultiplicationChainMap a I ha μ ≫
        (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π =
      G.incidenceCutMultiplicationChainMap a I ha ν ≫
        (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π := by
  letI := G.incidenceCoefficientParameterAlgebra a
  let R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  have hp : (G.incFreeResolution.π.f 0).hom = G.incResolutionAugmentation := by
    dsimp only [incFreeResolution, projectiveResolutionOfLinearExact, projectiveResolutionOfExact]
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have hq : ((G.incidenceParameterBaseChangeResolution a ha
      (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π.f 0).hom =
      G.incResolutionAugmentation.baseChange R := by
    dsimp only [incidenceParameterBaseChangeResolution, coefficientBaseChangeResolution,
      projectiveResolutionOfLinearExact, projectiveResolutionOfExact]
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have h := congrArg (fun f => (f.f 0).hom) (μ.chainMap_augmentation_eq ν)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, hp] at h
  have hb := congrArg (fun f => f.baseChange R) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hb
  change ((G.incidenceParameterBaseChangeResolution a ha
      (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π.f 0).hom.comp
        ((μ.chainMap.f 0).hom.baseChange R) =
    ((G.incidenceParameterBaseChangeResolution a ha
      (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π.f 0).hom.comp
        ((ν.chainMap.f 0).hom.baseChange R)
  rw [hq]
  exact hb

/-- All lifts on the changed tensor source with the same actual augmentation
agree after residue specialization, including lifts not extended from an original choice. -/
theorem incidenceCut_specialized_lifts_eq (hI : I ≤ RingHom.ker constantCoeff) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ (f g : G.incidenceCutTensorSource a I ⟶
      (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).complex),
    f ≫ (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π =
      g ≫ (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)).π →
    ∀ n, (ModuleCat.extendScalars (G.incidenceParameterCutOrigin a I hI)).map (f.f n) =
      (ModuleCat.extendScalars (G.incidenceParameterCutOrigin a I hI)).map (g.f n) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  let R := IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] (MvPolynomial (Fin G.dG) ℂ ⧸ I)
  let e := G.incidenceParameterCutOrigin a I hI
  let he := G.incidenceParameterCoefficientOrigin_compatible a (MvPolynomial (Fin G.dG) ℂ ⧸ I)
    (G.incidenceParameterQuotientOrigin I hI) (G.incidenceParameterQuotientOrigin_compatible I hI)
  haveI : ∀ n, Module.Free (IncCoeffRing E) (G.incTensorResolutionComplex.X n) := fun n => by
    change Module.Free (IncCoeffRing E)
      (gradedPiece (IncCoeffRing E) (fun b : G.IncResolutionBasis × G.IncResolutionBasis =>
        G.incResolutionDegree b.1 + G.incResolutionDegree b.2) n)
    infer_instance
  haveI : ∀ n, Projective ((G.incidenceCutTensorSource a I).X n) := fun n =>
    baseChangeChainComplex_projective G.incTensorResolutionComplex n
  intro f g h n
  apply specialized_lifts_eq e
    (G.incidenceParameterBaseChangeResolution a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)) f g h
  · intro i j
    have hmin := gradedTensorComplex_minimal G.incResolutionDegree G.incResolutionDifferential
      G.incResolutionDifferential_hasDegree G.incResolutionDifferential_sq
      (incCoeffAugmentationIdeal E) G.incResolutionDifferential_minimal
    have hc := baseChangeChainComplex_minimal (S := IncCoeffRing E) (R := R) (k := ℂ)
      (constantCoeff : IncCoeffRing E →+* ℂ) e he G.incTensorResolutionComplex hmin i j
    exact hc
  · exact G.incidenceParameterBaseChangeResolution_minimal a (MvPolynomial (Fin G.dG) ℂ ⧸ I) ha e he

end BPFixedPoints.Multigraph
