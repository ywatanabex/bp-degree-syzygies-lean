# BP degree and syzygies: Lean formalization

Lean 4 formalization of the main results of

> Yusuke Watanabe, *Counting the Fixed Points of Binary Belief Propagation:
> Generic Degree, Syzygies, and Real Solutions*. Draft, October 2026.

The paper determines the generic number of fixed points of belief
propagation (BP) on a finite loopless multigraph with binary pairwise
interactions, realizes this number as the total Betti number of a
universal edge-incidence ring, and describes the real fixed points through
Eulerian sign sectors. This repository contains a self-contained Lean 4 /
Mathlib development, `BPFixedPoints`, whose index module
[`BPFixedPoints/Paper.lean`](BPFixedPoints/Paper.lean) restates the
results of the paper in the order of the paper and attaches the Lean
declarations.

All Lean declarations in this package are **VERIFIED (Lean kernel checked)**.
Every clause of Theorems 1.1 and 1.2 is formalized, under formal hypotheses
recorded with each statement: [MAIN_CLAUSES.md](MAIN_CLAUSES.md) gives, clause
by clause, the complete Lean types, the hypotheses, the axioms and whether the
proof follows the paper's argument. The
[correspondence table](#correspondence-with-the-paper) summarizes the scope, and
[FORMALIZATION.md](FORMALIZATION.md) records the differences between the Lean
definitions and the paper's, the correspondence of every label of the paper and
its supplement with Lean declarations, and the completion status. What remains
of the paper's independent intermediate statements is the functoriality route
through Koszul algebras of sheaves and the saturation lemma (Lemma 4.2) for
smooth varieties (their conclusions are proved by other routes), and the
external Gröbner basis check for K₄.

## Reproduce the proof

Install [elan](https://github.com/leanprover/elan) and Git, then run the
following commands from this repository's root:

```sh
lake exe cache get
lake build
```

The first command obtains the pinned Mathlib dependency cache. The second
checks the whole library and the axiom audit `PaperAudit` (both are default
targets). Dependency acquisition requires network access; all project proof
sources are in this repository.

- Lean: `leanprover/lean4:v4.35.0`, fixed by [lean-toolchain](lean-toolchain).
- Mathlib: tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Every transitive dependency revision is fixed by [lake-manifest.json](lake-manifest.json).

[`PaperAudit.lean`](PaperAudit.lean) walks every declaration of the
`BPFixedPoints` namespace in the environment, including private and
auxiliary declarations, definitions and instances, and fails the build if
any of them depends on an axiom other than `propext`, `Classical.choice`
and `Quot.sound`. It rejects `sorryAx`, user axioms and native-evaluation
axioms. `native_decide` is not used anywhere; concrete values are checked
by kernel `decide`.

For a clean rebuild with a fresh audit and a validation receipt, install
Python 3.9 or later and run:

```sh
python3 checks/validate_paper.py --clean
```

The script needs only the Python standard library. It checks the source
inventory (no external paths, no local path dependency, every dependency
pinned to a commit, no `sorry`, `axiom` or `native_decide` outside
comments), rebuilds the package, re-runs the audit and writes
`validation/receipt.json` with the toolchain, the dependency revisions and
the SHA-256 digests of the sources. The
[GitHub Actions workflow](.github/workflows/lean.yml) is manual only
(`workflow_dispatch`); pushes and pull requests do not start it. Local incremental
validation is sufficient for normal changes. A clean run is an explicit
reproducibility check, not an automatic action on each update.

## Where to start

- [`BPFixedPoints/Paper.lean`](BPFixedPoints/Paper.lean): the index module.
  Every statement of the paper and its supplement has a docstring with its
  label and status, followed by an `alias` of the proving declaration.
- [`MAIN_CLAUSES.md`](MAIN_CLAUSES.md): Theorems 1.1 and 1.2 clause by clause,
  with the complete Lean types, the formal hypotheses, the axioms and whether
  the proof follows the paper's argument; generated from
  [`MainClauses.lean`](MainClauses.lean).
- [`FORMALIZATION.md`](FORMALIZATION.md): the differences between the Lean
  definitions and the paper's, how the main results are proved, the
  correspondence of every label with Lean declarations, and the completion
  status, including the two intermediate statements of the paper that are
  proved by other routes and the generalizations that are not formalized.
- [`MANUSCRIPT.json`](MANUSCRIPT.json): the paper version the correspondence
  refers to and the code release.

## Correspondence with the paper

Theorem numbers follow the article version of the draft (one counter per
section). All declarations below live in the namespace `BPFixedPoints`;
`Paper.` abbreviates `BPFixedPoints.Paper`, and the remaining names are in
`BPFixedPoints.Multigraph` or `BPFixedPoints.BP`. The formal hypotheses
remain explicit in the Lean statements; the main one is that the graph is
loopless (`Multigraph.Loopless`).

| Paper statement | Lean declaration and scope |
|---|---|
| Theorem 1.1: N(G) = Q(G) | `Paper.thm_structure_N_eq_Q`, `Paper.thm_degree`; counting form of the generic degree (`HasGenericDegree`): on the nonvanishing locus of a nonzero integer polynomial in the parameters, exactly Q(G) admissible complex fixed points, all simple |
| Theorem 1.1: 𝒰_G is a normal domain, finite over S_G, of dimension d_G = 3m + n − τ | `Paper.alg_normal_domain`, `Multigraph.incidenceRing_finite`, `Multigraph.ringKrullDim_incidenceRing`; proved for the intersection of the affine chart images in the torus ring. Its identification with the actual Γ of the independent projective zero scheme is proved |
| Theorem 1.1: minimal free resolution, Betti table (`intro:betti`), projective dimension ρ | `Multigraph.projectiveDimension_incidenceRing`, `Paper.thm_structure_betti`; a finite free resolution with state bases, minimal at the coefficient origin, of length ρ; its differential preserves the internal coefficient degree (`incResolutionDifferential_internal_degree`). Actual derived specialization has a state basis (`incidenceTorEquivState`) and dimensions Σ_q β_{p,q} with total Q(G) (`finrank_incidenceTor`, `sum_finrank_incidenceTor`). The images of homogeneous free terms define internal Tor pieces with dimensions β_{p,q} and unique finite decomposition (`finrank_incidenceTorInternalPiece`, `sum_incidenceTorComponent`, `incidenceTorInternalPiece_sum_unique`). The natural chart grading is a graded algebra (`incidenceCoefficientGradedAlgebra`), the original coefficient map and augmentation preserve degree, and the resolution is exact in every internal degree (`NaturalGradedResolution.lean`). The standard Tor product agrees with the exterior-edge and Čech cup formula (`Paper.alg_tor_product`); the sheaf-cohomology algebra comparison is the next row |
| Theorem 1.1: alternating numerator θ_G(t, 2i), ω_G, ω̃_G = ∏_C ω_C | `Paper.thm_structure_theta`, `Paper.thm_structure_omega`, `Paper.alg_hilbert`; polynomial identities. `Paper.alg_hilbert_theta`, `Paper.alg_universal_hilbert` and `Paper.alg_hilbert_reduced` prove the actual Hilbert series of 𝒰_G. Linear regular Artin quotients exist with Hilbert series ω̃_G; the finite-quotient parameter locus is nonempty Zariski open; regularity and the common Hilbert series throughout it are proved (`Paper.alg_artin_parameters_regular`) |
| Theorem 1.1: Cohen–Macaulay | `Paper.alg_cohenMacaulay`, `Paper.alg_cohenMacaulay_all_primes`; Noetherian and depth equals Krull dimension at every maximal ideal and every prime. `Paper.alg_origin_depth` gives coefficient-origin depth d_G; the supplement's localized statement depth = ht 𝔭 − ρ = dim is `Paper.supp_cm_localization_cohenMacaulay` |
| Theorem 1.1: regular Artin quotients | `Paper.alg_regular_artin_exists`; in each maximal ideal a length-d_G regular sequence gives a nonzero finite-dimensional Artin quotient. `Paper.alg_linear_artin_exists`, `Paper.alg_artin_hilbert` and `Paper.alg_artin_length` prove existence of homogeneous linear regular cuts, their Hilbert series ω̃_G, and dimension ω̃_G(1). `Paper.alg_artin_parameter_open` proves that the finite-quotient locus is nonempty Zariski open; regularity and the common Hilbert series throughout it are proved (`Paper.alg_artin_parameters_regular`) |
| Theorem 1.1: Tor isomorphism with sheaf cohomology, naturality | `Paper.alg_tor_isomorphism`, `Paper.alg_tor_isomorphism_mul`, `Paper.alg_tor_isomorphism_one`: bigraded ℂ-linear isomorphism preserving products and units, with the exterior bundle as the actual biproduct of twist sheaves, identified chart-wise with the exterior power in every degree and with product pairing equal to exterior multiplication; for q < p the Tor piece is zero (`Paper.alg_tor_piece_eq_bot_of_lt`); the same isomorphism is constructed by the paper's base change of the Čech–Koszul model to the coefficient origin, and the two constructions are equal (`Paper.alg_zero_base_change_eq`); naturality is the row Proposition 3.7 |
| Theorem 3.4: universal Koszul complex and its derived global sections | `Paper.alg_universal_koszul_complex`, `Paper.alg_universal_koszul_exact`, `Paper.alg_resolution_derived_vanishing`, `Paper.alg_resolution_derived_h0`; a complex of sheaves of modules, exact in negative degrees, whose hypercohomology in the derived category of abelian sheaves is 𝒰_G in degree zero and vanishes elsewhere |
| Theorem 1.2 (i): exhaustion of the complex fiber at strong field | `Paper.thm_real_i`; for fixed a_e ≠ 0, a_e² ≠ 1 and all sufficiently small nonzero p = b⁻¹, exactly Q(G) admissible complex roots, all simple. The analytic power-map normal form is `Paper.sf_normal_form` (exactly wt(S) distinct simple admissible solutions per state); the boundary algebras are the local algebra of the analytic special fiber p = 0 of the state chart is ℂ[w]/(w_i^{r_i}), of length wt(S), with the vanishing order r_i (`Paper.sf_state_fiber_equiv`, `Paper.sf_state_fiber_length`, `Paper.sf_ramification_index`) |
| Theorem 1.2 (ii): every Eulerian sector is nonempty at every field, R ≥ 2^ν | `Paper.thm_real_ii_sector`, `Paper.thm_real_ii_lower` |
| Theorem 1.2 (ii): strong field (N_ℂ, R, N_+) = (Q, 2^ν, 1), all roots simple | `Paper.thm_real_ii_strong`, `Paper.real_strong_field_count` |
| Theorem 1.2 (ii): min_h R_G(J, h) = 2^ν | `Paper.thm_real_ii_min` |
| Generator–real bridge (`intro:generator-real-bridge`, Corollary 3.9) | `Paper.alg_module_generator_number`, `Paper.alg_module_generators_minimal`, `Paper.alg_module_generator_cycles`, `Paper.alg_module_generator_sharp`, `Paper.alg_module_generator_min_real_count`; the intrinsic coefficient-module minimum is Σ_q β_{0,q}, with the cycle count, sharpness criterion and equality with the minimum real BP count for the chart model |
| Proposition 2.2 (admissible BP family) | `Paper.prop_bp_family`, `Paper.prop_bp_family_smooth`, `Multigraph.familyRing_isDomain`, `Multigraph.ringKrullDim_familyRing`; generic fiber, smoothness, domain, dimension m + n |
| Lemmas 2.3–2.4, Theorem 2.5, Corollary 2.6 | `Paper.lem_weak_boundary`, `Paper.lem_unique_weak_lift*`, `Paper.thm_degree`, `Paper.cor_elementary_degree_*` |
| Definition 3.2 and Lemma 3.3: actual projective zero scheme and global functions | `Paper.alg_incidence_projective_closed`, `Paper.alg_incidence_projective_zero_scheme`, `Paper.alg_incidence_projective_zero_charts`, `Paper.alg_projective_zero_global_sections`, `Paper.alg_projective_zero_coefficient`; the independent homogeneous zero scheme has the prescribed full affine quotient charts and actual global functions equal to the original incidence ring, preserving the geometric coefficient action; properness including every scheme base change is proved by `Paper.alg_incidence_projective_proper` and `Paper.alg_incidence_proper_basechange`; the vector-bundle description is proved on charts and on their overlaps, with linear transition functions satisfying the cocycle condition (`Paper.alg_vector_bundle_trivialization`, `Paper.alg_vector_bundle_linear_transition`), the kernel sheaf is constructed (`Paper.alg_kernel_sheaf_chart`), and Z_G is isomorphic over X_G to the total space of the rank-3m kernel bundle (`Paper.alg_vector_bundle_total_space`) |
| Lemma 3.1, Corollary 3.5, Proposition 3.8, tables and K₄ (numerical/combinatorial parts) | `Paper.alg_state_cohomology`, `Paper.alg_total_betti`, `Paper.alg_cycle_product`, `Paper.alg_generator_table`, `Paper.alg_k4`, `Paper.fig_k4_states`; the graded Tor dimensions are proved, the sheaf-cohomology comparison is `Paper.alg_tor_isomorphism`, the E_1 dimension formula is `Paper.alg_state_dimensions`, and the K₄ graded shape and generator products are `Paper.alg_k4_graded_betti` and `Paper.alg_k4_generator_products`; `Paper.alg_module_generator_table` gives the intrinsic module-generator counts; `Paper.alg_k4_artin_exists` constructs an actual Artin quotient of dimension 30 |
| Proposition 3.7: functoriality | `Paper.alg_graph_map_relation`, `Paper.alg_derived_ring_map_eq`, `Paper.alg_graph_map_tor_trans`, `Paper.alg_graph_map_tor_factorization`, `Paper.alg_tor_isomorphism_graph_map_natural`, `Paper.alg_graph_map_graded`, `Paper.alg_disjoint_union_tensor`; for every endpoint-preserving graph map that does not contract edges (vertex maps, edge maps, reversals and signs), incidence ring maps compatible with the coefficient ring maps, Tor maps derived along the non-flat coefficient ring maps, identity and composition laws, and the naturality square of the Tor isomorphism; the ring maps are graded and 𝒰_{G⊔H} ≅ 𝒰_G ⊗ 𝒰_H with its coherence |
| Proposition 3.8: the cycle-compatibility algebra | `Paper.alg_cycle_algebra`: graded ℂ-algebra isomorphism U_G/(S_G)_+U_G ≅ ℂ[z_C]/(z_C z_D : V(C)∩V(D)≠∅), deg z_C = \|C\|; `Paper.alg_cycle_algebra_tor`: the same algebra is Tor_0 with its standard product |
| Lemma 4.2, Corollary 4.3 | `Paper.sf_degree_saturation`, `Paper.sf_exhaustion` |
| Propositions 5.1, 5.3, 5.4, 5.6, Lemma 5.2, Corollaries 5.5 and 5.8 | `Paper.real_sign_sectors`, `Paper.real_vertex_map`, `Paper.real_sector_degree_bounded`, `Paper.real_strong_field_count`, `Paper.real_edge_branches*`, `Multigraph.sector_count_odd`, `Paper.real_positive_bound`; Lemma 5.2 and Proposition 5.3 with real analyticity (`Paper.real_edge_branches_analytic`, `Paper.real_vertex_map_analytic`); Proposition 5.4 with the degree value (−1)^{v(S)} for the C¹ degree of signed counts and determinant integrals (`Paper.real_sector_degree`, `Paper.real_sector_degree_integral`) |
| Supplement: degree bounds, K₄ states | `Paper.alg_degree_bounds`, `Paper.sf_k4_states`; total counts (48, 8, 1), one real root per Eulerian sector, and the statewise complex and real chart counts (`Paper.sf_k4_statewise_chart_counts`, `Paper.sf_k4_statewise_real_counts`) |
| Supplement: duality on ℙ¹, non-normalizable locus, Cohen–Macaulay localization | `Paper.sf_serre_duality`, `Paper.sf_serre_cup_eq_residue`; `Paper.supp_nonnormalizable_dim_tree`, `Paper.supp_nonnormalizable_dim_cyclic`; `Paper.supp_cm_localization_cohenMacaulay` |

The paper-facing docstrings in `Paper.lean` give the corresponding labels
and formalization statuses. Labels of the paper that have no Lean counterpart are
listed with the reason in [FORMALIZATION.md](FORMALIZATION.md).

## Paper version

The paper is posted as [arXiv:2610.36964](https://arxiv.org/abs/2610.36964)
(v1, 27 October 2026). [MANUSCRIPT.json](MANUSCRIPT.json) records the version
the correspondence refers to, and the tag `arxiv-v1` marks the snapshot cited
by that version. The paper source is not required to build these proofs.

## Contents

- `BPFixedPoints/`: all proof modules, arranged by the sections of the paper
  (`Graph/`, `StateSum/`, `Degree/`, `Family/`, `Incidence/`, `StrongField/`,
  `Real/`, `Examples/`, `StatementOnly/`), and the index `Paper.lean`.
- `BPFixedPoints.lean`: aggregate proof library, importing every module.
- `PaperAudit.lean`: default-build axiom audit; `FormalizationAdditions.lean`:
  the same audit restricted to the additions made for the paper.
- `MainClauses.lean` and `MAIN_CLAUSES.md`: the main clauses with their
  complete types; `checks/gen_main_clauses.py` regenerates the latter.
- `FORMALIZATION.md`: scope, differences in hypotheses, full label
  correspondence and the completion status.
- `checks/validate_paper.py`: standalone clean build, audit and receipt.
- `.github/workflows/lean.yml`: manually dispatched clean build and validation.
- `third_party/` and `THIRD_PARTY_NOTICES.md`: adapted sources and their
  attributions.

The proof modules were developed in the author's research repository and
are included here with the namespace `BPFixedPoints`; this repository is a
snapshot of that development without its history. The proof comments, the
index `Paper.lean`, the audit and the package documentation are in English.

## License

The project sources and documentation are licensed under the
[MIT license](LICENSE), except for material adapted from Mathlib and the
public Anthropic and OpenAI sources under the
[Apache 2.0 license](LICENSE-APACHE-2.0). Source commits, adapted files and
attributions are recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md);
`ProjectiveLiftComparison.lean` retains its original Mathlib header.
Downloaded dependencies retain their own licenses.
