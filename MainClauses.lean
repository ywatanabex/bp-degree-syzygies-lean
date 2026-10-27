import BPFixedPoints

/-!
# Main clauses of Theorems 1.1 and 1.2: audit entry point

For every clause of the two main theorems of the paper (`thm:structure`, `thm:real`) this file
prints the complete type of the Lean declarations that formalize it (`#check @name`, with all
implicit and instance arguments) and their axiom dependencies (`#print axioms name`). The last
sections print the identification of the model of 𝒰_G and the definitions of the Lean objects
that occur in the types.

Run from the package root, after `lake build`:

    lake env lean MainClauses.lean

`MAIN_CLAUSES.md` reproduces this output clause by clause (inserted by a script, not by hand)
with the manuscript statement, the hypotheses in words, the differences from the paper and a
status. This file declares nothing.

Reading the printed types:
* Names are written in full and no namespace is opened, so the types use full names.
* `⋯` stands for a proof term (Lean's default `pp.proofs false`).
* Instance arguments inside a type are not printed. These statements use three structures that
  are supplied locally rather than by global instances: the Zariski topology on tuples of linear
  forms, made visible by the scoped notation `IsOpen[t]` opened below; the S_G-module structure
  of 𝒰_G given by `coeffHom`; and the ℂ-module structure of the cohomology of the exterior
  bundle given by the base (`exteriorBundleCohomologyModule`). The `example`s below restate the
  statements that use the last two with the structure written out; Lean checks each restatement
  against the declaration.
-/

-- Only notation: prints `IsOpen[t] s` when the topology `t` is not an instance.
open scoped Topology

/-! ## Theorem 1.1 (`thm:structure`) -/

/-! ### S1. N(G) = Q(G) for every finite loopless multigraph (`thm:structure`, `thm:degree`)
The generic admissible complex BP degree N(G) equals the state sum Q(G). In Lean, N(G) = n is the
counting statement `HasGenericDegree G n`; the algebraic finite étale form is
`prop_bp_family_finite_etale`. -/
#check @BPFixedPoints.Paper.thm_structure_N_eq_Q
#check @BPFixedPoints.Paper.thm_degree
#check @BPFixedPoints.Paper.prop_bp_family_finite_etale
#print axioms BPFixedPoints.Paper.thm_structure_N_eq_Q
#print axioms BPFixedPoints.Paper.thm_degree
#print axioms BPFixedPoints.Paper.prop_bp_family_finite_etale

/-! ### S2. 𝒰_G is a normal domain (`thm:structure`, `alg:normal-cm`) -/
#check @BPFixedPoints.Paper.alg_normal_domain
#print axioms BPFixedPoints.Paper.alg_normal_domain

/-! ### S3. 𝒰_G is Cohen–Macaulay (`thm:structure`, `alg:normal-cm`, `supp:cm-localization`)
Noetherian, and depth equals Krull dimension at every maximal ideal and at every prime. -/
#check @BPFixedPoints.Paper.alg_cohenMacaulay
#check @BPFixedPoints.Paper.alg_cohenMacaulay_all_primes
#print axioms BPFixedPoints.Paper.alg_cohenMacaulay
#print axioms BPFixedPoints.Paper.alg_cohenMacaulay_all_primes

/-! ### S4. 𝒰_G is finite over S_G (`thm:structure`, `alg:incidence-vector-bundle`) -/
#check @BPFixedPoints.Multigraph.incidenceRing_finite
#print axioms BPFixedPoints.Multigraph.incidenceRing_finite

/-! ### S5. dim 𝒰_G = d_G = 3m + n − τ (`thm:structure`, `alg:normal-cm`) -/
#check @BPFixedPoints.Multigraph.ringKrullDim_incidenceRing
#check @BPFixedPoints.Paper.thm_structure_dim
#print axioms BPFixedPoints.Multigraph.ringKrullDim_incidenceRing
#print axioms BPFixedPoints.Paper.thm_structure_dim

/-! ### S6. Minimal graded free resolution, β_{p,q} = Σ_{|S|=q, |S|−v(S)=p} wt(S), N(G) = Σ β_{p,q}
(`thm:structure`, `intro:betti`, `alg:resolution`, `alg:total-betti`)
The state-sum table, the free resolution on the state basis (square zero, exact, augmentation
onto 𝒰_G, minimal, length ρ, exact in every internal degree), the dimensions of the internal
Tor pieces, and the free terms F_p ≅ ⊕_q H^{q−p}(X_G, ∧^q F_G^∨) ⊗ S_G(−q) (`alg:free-terms`). -/
#check @BPFixedPoints.Paper.thm_structure_betti
#check @BPFixedPoints.Paper.alg_total_betti
#check @BPFixedPoints.Multigraph.incResolutionDifferential
#check @BPFixedPoints.Multigraph.incResolutionDifferential_sq
#check @BPFixedPoints.Multigraph.incResolutionDifferential_exact
#check @BPFixedPoints.Multigraph.incResolutionAugmentation_surjective
#check @BPFixedPoints.Multigraph.incResolutionAugmentation_exact
#check @BPFixedPoints.Multigraph.incResolutionDifferential_minimal
#check @BPFixedPoints.Multigraph.projectiveDimension_incidenceRing
#check @BPFixedPoints.Multigraph.incFreeTermDifferential_graded_exact
#check @BPFixedPoints.Multigraph.finrank_incidenceTorInternalPiece
#check @BPFixedPoints.Paper.alg_free_terms
#check @BPFixedPoints.Paper.alg_free_terms_internal
#check @BPFixedPoints.Paper.alg_free_terms_residue
#print axioms BPFixedPoints.Paper.thm_structure_betti
#print axioms BPFixedPoints.Paper.alg_total_betti
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential_sq
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential_exact
#print axioms BPFixedPoints.Multigraph.incResolutionAugmentation_surjective
#print axioms BPFixedPoints.Multigraph.incResolutionAugmentation_exact
#print axioms BPFixedPoints.Multigraph.incResolutionDifferential_minimal
#print axioms BPFixedPoints.Multigraph.projectiveDimension_incidenceRing
#print axioms BPFixedPoints.Multigraph.incFreeTermDifferential_graded_exact
#print axioms BPFixedPoints.Multigraph.finrank_incidenceTorInternalPiece
#print axioms BPFixedPoints.Paper.alg_free_terms
#print axioms BPFixedPoints.Paper.alg_free_terms_internal
#print axioms BPFixedPoints.Paper.alg_free_terms_residue

-- restate: projectiveDimension
example {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
    (G : BPFixedPoints.Multigraph V E) :
    letI := G.coeffHom.toRingHom.toAlgebra
    CategoryTheory.projectiveDimension
        (ModuleCat.of (BPFixedPoints.Multigraph.IncCoeffRing E) G.IncidenceRing) =
      (G.rho : WithBot ℕ∞) :=
  BPFixedPoints.Multigraph.projectiveDimension_incidenceRing G

/-! ### S7. Tor_p^{S_G}(𝒰_G, ℂ)_q ≅ E_1^{−q,q−p}(G) = H^{q−p}(X_G, ∧^q F_G^∨) as bigraded algebras
(`thm:structure`, `intro:tor`, `alg:tor-isomorphism`)
The linear isomorphism, products, unit, vanishing for q < p, and the chart-wise identification
of the biproduct model of ∧^q F_G^∨ with the exterior power. -/
#check @BPFixedPoints.Paper.alg_tor_isomorphism
#check @BPFixedPoints.Paper.alg_tor_isomorphism_mul
#check @BPFixedPoints.Paper.alg_tor_isomorphism_one
#check @BPFixedPoints.Paper.alg_tor_piece_eq_bot_of_lt
#check @BPFixedPoints.Paper.alg_exterior_chart_wedge_bijective_all
#check @BPFixedPoints.Paper.alg_exterior_pairing_wedge
#print axioms BPFixedPoints.Paper.alg_tor_isomorphism
#print axioms BPFixedPoints.Paper.alg_tor_isomorphism_mul
#print axioms BPFixedPoints.Paper.alg_tor_isomorphism_one
#print axioms BPFixedPoints.Paper.alg_tor_piece_eq_bot_of_lt
#print axioms BPFixedPoints.Paper.alg_exterior_chart_wedge_bijective_all
#print axioms BPFixedPoints.Paper.alg_exterior_pairing_wedge

-- restate: torIsomorphism
noncomputable example {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
    (G : BPFixedPoints.Multigraph V E) {p q : ℕ} (h : p ≤ q) :
    letI : CategoryTheory.HasExt.{1} (CategoryTheory.Sheaf
        (Opens.grothendieckTopology
          (BPFixedPoints.ProjectiveLine.vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
      CategoryTheory.HasExt.standard _
    letI := G.exteriorBundleCohomologyModule ℂ q (q - p)
    G.incidenceTorInternalPiece p q ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) (q - p) :=
  BPFixedPoints.Paper.alg_tor_isomorphism G h

/-! ### S8. Naturality for endpoint-preserving graph maps that do not contract edges
(`thm:structure`, `alg:functoriality`)
General graph maps: the edge relation a_φ^* b_e = ε_φ(e) b_{φ(e)}, the incidence ring map over
the coefficient map, identity and composition laws, independence of the factorization, the
naturality square of the Tor isomorphism, and the graded incidence ring map. -/
#check @BPFixedPoints.Paper.alg_graph_map_relation
#check @BPFixedPoints.Paper.alg_graph_map_incidence
#check @BPFixedPoints.Multigraph.GraphMap.incidenceHom_refl
#check @BPFixedPoints.Paper.alg_graph_map_incidence_trans
#check @BPFixedPoints.Multigraph.GraphMap.incidenceTorHom_refl
#check @BPFixedPoints.Paper.alg_graph_map_tor_trans
#check @BPFixedPoints.Paper.alg_graph_map_tor_factorization
#check @BPFixedPoints.Paper.alg_tor_isomorphism_graph_map_natural
#check @BPFixedPoints.Paper.alg_graph_map_graded
#check @BPFixedPoints.Multigraph.GraphMap.incidenceGradedHom_apply
#print axioms BPFixedPoints.Paper.alg_graph_map_relation
#print axioms BPFixedPoints.Paper.alg_graph_map_incidence
#print axioms BPFixedPoints.Multigraph.GraphMap.incidenceHom_refl
#print axioms BPFixedPoints.Paper.alg_graph_map_incidence_trans
#print axioms BPFixedPoints.Multigraph.GraphMap.incidenceTorHom_refl
#print axioms BPFixedPoints.Paper.alg_graph_map_tor_trans
#print axioms BPFixedPoints.Paper.alg_graph_map_tor_factorization
#print axioms BPFixedPoints.Paper.alg_tor_isomorphism_graph_map_natural
#print axioms BPFixedPoints.Paper.alg_graph_map_graded
#print axioms BPFixedPoints.Multigraph.GraphMap.incidenceGradedHom_apply

/-! ### S9. Hilb_{𝒰_G}(t) = θ_G(t,2i)/(1−t)^{4m} = ω_G(t)/(1−t)^{3m+n}
(`thm:structure`, `intro:hilbert`, `alg:hilbert`) -/
#check @BPFixedPoints.Paper.thm_structure_theta
#check @BPFixedPoints.Paper.alg_hilbert_theta
#check @BPFixedPoints.Paper.alg_universal_hilbert
#check @BPFixedPoints.Paper.alg_hilbert_reduced
#print axioms BPFixedPoints.Paper.thm_structure_theta
#print axioms BPFixedPoints.Paper.alg_hilbert_theta
#print axioms BPFixedPoints.Paper.alg_universal_hilbert
#print axioms BPFixedPoints.Paper.alg_hilbert_reduced

/-! ### S10. Artin reduction: d_G general linear forms are a regular sequence,
Hilb_{A_G} = ω̃_G = ∏_C ω_C (`thm:structure`, `alg:hilbert`, `alg:artin-hilbert`) -/
#check @BPFixedPoints.Paper.alg_artin_parameter_open
#check @BPFixedPoints.Paper.alg_artin_parameters_regular
#check @BPFixedPoints.Paper.alg_linear_artin_exists
#check @BPFixedPoints.Paper.thm_structure_omega
#print axioms BPFixedPoints.Paper.alg_artin_parameter_open
#print axioms BPFixedPoints.Paper.alg_artin_parameters_regular
#print axioms BPFixedPoints.Paper.alg_linear_artin_exists
#print axioms BPFixedPoints.Paper.thm_structure_omega

/-! ## Theorem 1.2 (`thm:real`) -/

/-! ### R1. (i) For a_e ≠ 0, a_e² ≠ 1 and all small nonzero p_i = b_i⁻¹, exactly Q(G) simple roots
(`thm:real` (i), `sf:exhaustion`) -/
#check @BPFixedPoints.Paper.thm_real_i
#print axioms BPFixedPoints.Paper.thm_real_i

/-! ### R2. (i) Smooth local analytic extension across p = 0 with p_i = (−1)^{d_S(i)} w_i^{r_i}
(`thm:real` (i), `intro:power-map`, `sf:normal-form`) -/
#check @BPFixedPoints.Paper.sf_normal_form
#print axioms BPFixedPoints.Paper.sf_normal_form

/-! ### R3. (i) Boundary local algebra ⊗_i ℂ[w_i]/(w_i^{r_i}) of length wt(S)
(`thm:real` (i), `sf:boundary-algebra`) -/
#check @BPFixedPoints.Paper.sf_state_fiber_equiv
#check @BPFixedPoints.Paper.sf_vertex_fiber_equiv
#check @BPFixedPoints.Paper.sf_state_fiber_length
#check @BPFixedPoints.Paper.sf_state_fiber_regular
#print axioms BPFixedPoints.Paper.sf_state_fiber_equiv
#print axioms BPFixedPoints.Paper.sf_vertex_fiber_equiv
#print axioms BPFixedPoints.Paper.sf_state_fiber_length
#print axioms BPFixedPoints.Paper.sf_state_fiber_regular

/-! ### R4. (ii) At every field, every Eulerian edge set is the negative-message support of an
admissible real root (`thm:real` (ii), `real:sector-degree`) -/
#check @BPFixedPoints.Paper.thm_real_ii_sector
#print axioms BPFixedPoints.Paper.thm_real_ii_sector

/-! ### R5. (ii) R_G(J, h) ≥ 2^{ν(G)} at every field (`thm:real` (ii), `real:lower-bound`) -/
#check @BPFixedPoints.Paper.thm_real_ii_lower
#print axioms BPFixedPoints.Paper.thm_real_ii_lower

/-! ### R6. (ii) Strong fields in every orthant: (N_ℂ, R_G, N_+) = (Q(G), 2^{ν(G)}, 1), all
complex roots simple (`thm:real` (ii), `intro:three-counts`, `real:strong-field-count`) -/
#check @BPFixedPoints.Paper.thm_real_ii_strong
#print axioms BPFixedPoints.Paper.thm_real_ii_strong

/-! ### R7. (ii) min_h R_G(J, h) = 2^{ν(G)} (`thm:real` (ii), `intro:minimum`, `real:minimum`) -/
#check @BPFixedPoints.Paper.thm_real_ii_min
#print axioms BPFixedPoints.Paper.thm_real_ii_min

/-! ### R8. Maximum degree ≤ 3: Σ_q β_{0,q} = 2^{ν(G)} = min_h R_G(J, h)
(`intro:generator-real-bridge`, `alg:generator-real-bridge`) -/
#check @BPFixedPoints.Paper.intro_generator_real_bridge
#check @BPFixedPoints.Paper.alg_generator_real_bridge
#check @BPFixedPoints.Paper.alg_module_generator_number
#check @BPFixedPoints.Paper.alg_module_generators_minimal
#check @BPFixedPoints.Paper.alg_module_generator_min_real_count
#print axioms BPFixedPoints.Paper.intro_generator_real_bridge
#print axioms BPFixedPoints.Paper.alg_generator_real_bridge
#print axioms BPFixedPoints.Paper.alg_module_generator_number
#print axioms BPFixedPoints.Paper.alg_module_generators_minimal
#print axioms BPFixedPoints.Paper.alg_module_generator_min_real_count

-- restate: generatorsSpan
example {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
    (G : BPFixedPoints.Multigraph V E) :
    letI := G.coeffHom.toRingHom.toAlgebra
    Submodule.span (BPFixedPoints.Multigraph.IncCoeffRing E)
        (Set.range G.incidenceResolutionGenerators) = ⊤ ∧
      ∀ {J : Type} [Fintype J] (g : J → G.IncidenceRing),
        Submodule.span (BPFixedPoints.Multigraph.IncCoeffRing E) (Set.range g) = ⊤ →
          Fintype.card {b // G.incResolutionDegree b = 0} ≤ Fintype.card J :=
  BPFixedPoints.Paper.alg_module_generators_minimal G

-- restate: generatorNumber
example {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
    (G : BPFixedPoints.Multigraph V E) :
    G.incidenceModuleGeneratorNumber =
      letI := G.coeffHom.toRingHom.toAlgebra
      (⊤ : Submodule (BPFixedPoints.Multigraph.IncCoeffRing E) G.IncidenceRing).spanFinrank :=
  rfl

/-! ## Statements on the manuscript's routes (§3–§5 and the supplement)
The intermediate statements through which the manuscript proves the main clauses; their
types are printed so that their hypotheses can be checked as for the main clauses. -/

/-! ### M1. Z_G is the total space of a rank-3m vector bundle on X_G (`alg:incidence-vector-bundle`, `supp:vector-bundle`) -/
#check @BPFixedPoints.Paper.alg_vector_bundle_total_space
#check @BPFixedPoints.Paper.alg_vector_bundle_total_space_projection
#check @BPFixedPoints.Paper.alg_vector_bundle_sym_sections
#print axioms BPFixedPoints.Paper.alg_vector_bundle_total_space
#print axioms BPFixedPoints.Paper.alg_vector_bundle_total_space_projection
#print axioms BPFixedPoints.Paper.alg_vector_bundle_sym_sections

/-! ### M2. The universal Koszul complex resolves 𝒪_{Z_G} (`alg:universal-koszul`) -/
#check @BPFixedPoints.Paper.alg_universal_koszul_complex
#check @BPFixedPoints.Paper.alg_universal_koszul_exact
#check @BPFixedPoints.Paper.alg_universal_koszul_resolves
#print axioms BPFixedPoints.Paper.alg_universal_koszul_complex
#print axioms BPFixedPoints.Paper.alg_universal_koszul_exact
#print axioms BPFixedPoints.Paper.alg_universal_koszul_resolves

/-! ### M3. The derived global sections of K_G are concentrated in degree zero and equal 𝒰_G (`alg:resolution`) -/
#check @BPFixedPoints.Paper.sheaf_hypercohomology_single
#check @BPFixedPoints.Paper.alg_resolution_derived_vanishing
#check @BPFixedPoints.Paper.alg_resolution_derived_h0
#check @BPFixedPoints.Paper.alg_resolution_derived_h0_augmentation
#print axioms BPFixedPoints.Paper.sheaf_hypercohomology_single
#print axioms BPFixedPoints.Paper.alg_resolution_derived_vanishing
#print axioms BPFixedPoints.Paper.alg_resolution_derived_h0
#print axioms BPFixedPoints.Paper.alg_resolution_derived_h0_augmentation

/-! ### M4. Base change to the coefficient origin in D(ℂ) (`alg:zero-base-change`) -/
#check @BPFixedPoints.Paper.alg_zero_base_change_derived
#check @BPFixedPoints.Paper.alg_zero_base_change_derived_exterior
#check @BPFixedPoints.Paper.alg_zero_base_change_pair_tensor
#check @BPFixedPoints.Paper.alg_zero_base_change_cech_product
#check @BPFixedPoints.Paper.alg_zero_base_change_derived_product
#print axioms BPFixedPoints.Paper.alg_zero_base_change_derived
#print axioms BPFixedPoints.Paper.alg_zero_base_change_derived_exterior
#print axioms BPFixedPoints.Paper.alg_zero_base_change_pair_tensor
#print axioms BPFixedPoints.Paper.alg_zero_base_change_cech_product
#print axioms BPFixedPoints.Paper.alg_zero_base_change_derived_product

/-! ### M5. deg 𝔥_S = (−1)^{v(S)} (`real:sector-degree`, `real:degree`) -/
#check @BPFixedPoints.Paper.real_sector_degree
#check @BPFixedPoints.Paper.real_sector_degree_integral
#check @BPFixedPoints.Paper.proper_degree_integral
#print axioms BPFixedPoints.Paper.real_sector_degree
#print axioms BPFixedPoints.Paper.real_sector_degree_integral
#print axioms BPFixedPoints.Paper.proper_degree_integral
#print BPFixedPoints.brouwerDegree
#print BPFixedPoints.signedFiberCount

/-! ### M6. Supplementary statements (`sf:serre-comparison`, `supp:nonnormalizable-dim`, `supp:cm-localization`) -/
#check @BPFixedPoints.Paper.sf_serre_duality
#check @BPFixedPoints.Paper.sf_serre_cup_eq_residue
#check @BPFixedPoints.Paper.supp_nonnormalizable_dim_tree
#check @BPFixedPoints.Paper.supp_nonnormalizable_dim_cyclic
#check @BPFixedPoints.Paper.supp_cm_localization_cohenMacaulay
#print axioms BPFixedPoints.Paper.sf_serre_duality
#print axioms BPFixedPoints.Paper.sf_serre_cup_eq_residue
#print axioms BPFixedPoints.Paper.supp_nonnormalizable_dim_tree
#print axioms BPFixedPoints.Paper.supp_nonnormalizable_dim_cyclic
#print axioms BPFixedPoints.Paper.supp_cm_localization_cohenMacaulay
/-! ## The model of 𝒰_G
`IncidenceRing` (the chart-intersection model) is isomorphic to the global sections of the
projective zero scheme, compatibly with the coefficient action; that scheme is proper over the
coefficient space. -/
#check @BPFixedPoints.Paper.alg_projective_zero_global_sections
#check @BPFixedPoints.Paper.alg_projective_zero_coefficient
#check @BPFixedPoints.Paper.alg_incidence_projective_proper
#print axioms BPFixedPoints.Paper.alg_projective_zero_global_sections
#print axioms BPFixedPoints.Paper.alg_projective_zero_coefficient
#print axioms BPFixedPoints.Paper.alg_incidence_projective_proper

/-! ## Definitions of the objects in the statements -/
#print BPFixedPoints.Multigraph.Loopless
#print BPFixedPoints.Multigraph.HasGenericDegree
#print BPFixedPoints.Multigraph.IsAdmissibleSolution
#print BPFixedPoints.Multigraph.IsFixedPoint
#print BPFixedPoints.Multigraph.Admissible
#print BPFixedPoints.Multigraph.IsSimpleSolution
#print BPFixedPoints.phi
#print BPFixedPoints.Multigraph.wt
#print BPFixedPoints.Multigraph.Q
#print BPFixedPoints.Multigraph.betti
#print BPFixedPoints.Multigraph.IsEvenSet
#print BPFixedPoints.BP.negSupport
#print BPFixedPoints.Multigraph.nu
#print BPFixedPoints.Multigraph.tau
#print BPFixedPoints.Multigraph.rho
#print BPFixedPoints.Multigraph.dG
#print BPFixedPoints.Multigraph.IncCoeffIdx
#print BPFixedPoints.Multigraph.IncCoeffRing
#print BPFixedPoints.Multigraph.IncidenceRing
#print BPFixedPoints.Multigraph.coeffHom
#print BPFixedPoints.Multigraph.incCoeffAugmentationIdeal
#print BPFixedPoints.Multigraph.incidenceCoefficientPiece
#print BPFixedPoints.Multigraph.incidenceHilbertSeries
#print BPFixedPoints.Multigraph.incidenceTor
#print BPFixedPoints.Multigraph.incidenceTorInternalPiece
#print BPFixedPoints.Multigraph.exteriorBundle
#print BPFixedPoints.Multigraph.exteriorSummand
#print BPFixedPoints.Multigraph.GraphMap
#print BPFixedPoints.Multigraph.GraphMap.exteriorCohomologyMap
#print BPFixedPoints.Multigraph.IncidenceLinearParameters
#print BPFixedPoints.Multigraph.incidenceFiniteParameterLocus
#print BPFixedPoints.ResolutionTools.parameterZariskiTopology
#print BPFixedPoints.ResolutionTools.parameterPrime
#print BPFixedPoints.Multigraph.IsState
#print BPFixedPoints.Multigraph.rS
#print BPFixedPoints.Multigraph.powerMap
#print BPFixedPoints.Multigraph.IsPowerMapChart
#print BPFixedPoints.BoundaryAlgebra.analyticGerms
#print BPFixedPoints.Multigraph.stateFiberIdeal
#print BPFixedPoints.Multigraph.powerMapGerm
#print BPFixedPoints.Multigraph.boundaryAlgebra
#print BPFixedPoints.BoundaryAlgebra.truncIdeal
#print BPFixedPoints.Multigraph.incidenceModuleGeneratorNumber

-- restate: incidenceTor
example {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
    (G : BPFixedPoints.Multigraph V E) (p : ℕ) :
    G.incidenceTor p =
      letI := G.coeffHom.toRingHom.toAlgebra
      ((ModuleCat.extendScalars
          (MvPolynomial.constantCoeff : BPFixedPoints.Multigraph.IncCoeffRing E →+* ℂ)).leftDerived
          p).obj (ModuleCat.of (BPFixedPoints.Multigraph.IncCoeffRing E) G.IncidenceRing) :=
  rfl
