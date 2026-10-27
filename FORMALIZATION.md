# Formalization scope

This document records what the Lean development proves about the paper

> Yusuke Watanabe, *Counting the Fixed Points of Binary Belief Propagation:
> Generic Degree, Syzygies, and Real Solutions* (draft, October 2026),

what it does not prove, and where the Lean definitions differ from the
paper's. Theorem numbers follow the article version of the draft (one
counter per section). Status words:

- **Proved**: the statement is proved without `sorry`, checked by
  `lake build`, and covered by the axiom audit `PaperAudit`.
- **Partial**: only the part named in parentheses is proved. This also
  applies when a proved state-sum identity lacks its identification
  with the geometric invariant in the labelled paper statement.
- **Not formalized**: no Lean statement exists.
- **Definition**: a definition or notation of the paper with a Lean
  counterpart, with no claim attached.
- **Section**: a section label without formal content.

Names starting with `Paper.` are in the namespace `BPFixedPoints.Paper`
([`BPFixedPoints/Paper.lean`](BPFixedPoints/Paper.lean)); the remaining
names are in `BPFixedPoints.Multigraph`, `BPFixedPoints.BP` or
`BPFixedPoints.Examples`.

In the ring-theoretic rows below, 𝒰_G denotes the chart-intersection model
`IncidenceRing`. `incidenceGluedGlobalSectionsEquiv` identifies it with the
global regular functions of the scheme glued from its affine quotient charts
and all their higher overlaps. `incidenceProjectiveZeroIso` identifies this
scheme with the independently constructed closed zero scheme of the
homogeneous edge equations in the product of projective lines over the
coefficient space; the identification of global sections preserves the
geometric coefficient action. The bigraded Tor algebra is compared with sheaf
cohomology of the exterior bundle (row `intro:tor` below), both through state
bases and through the paper's base change to the coefficient origin; the two
comparisons are equal. The universal Koszul complex is a complex of sheaves,
resolving 𝒪_{Z_G}, Z_G is the total space of the rank-3m kernel bundle, and
the derived global sections are concentrated in degree zero and equal 𝒰_G.
What remains of the paper is listed under "Completion status".

## Main theorems, clause by clause

[MAIN_CLAUSES.md](MAIN_CLAUSES.md) gives, for each clause below, the complete Lean types, the
hypotheses, the axiom lines and the status, generated from [MainClauses.lean](MainClauses.lean).

### Theorem 1.1 (`thm:structure`)

| Clause | Status | Lean |
|---|---|---|
| N(G) = Q(G) for every finite loopless multigraph | Proved | `Paper.thm_structure_N_eq_Q` (= `exists_generic_degree_eq_Q`), `Paper.thm_degree`; the generic degree is taken in the counting form `HasGenericDegree` described below |
| 𝒰_G is a normal domain | Proved | `Paper.alg_normal_domain` (`incidenceRing_isDomain`, `incidenceRing_isIntegrallyClosed`) |
| 𝒰_G is Cohen–Macaulay | Proved | `Paper.alg_cohenMacaulay`: the actual ring is Noetherian and depth equals Krull dimension at every maximal localization; both equal d_G (`incidence_local_depth`, `incidence_local_krullDim`). At every prime P, depth equals Krull dimension (`Paper.alg_cohenMacaulay_all_primes`). Depth is Mathlib’s Ext depth |
| 𝒰_G is finite over S_G | Proved | `incidenceRing_finite` (`StatementOnly/IncidenceRing.lean`) |
| dim 𝒰_G = d_G = 3m + n − τ | Proved | `ringKrullDim_incidenceRing`; the arithmetic d_G + ρ = 4m is `Paper.thm_structure_dim` |
| minimal graded free resolution with Betti numbers β_{p,q} = Σ_{\|S\|=q, \|S\|−v(S)=p} wt(S) (`intro:betti`) | Proved | the numerical table `betti p q` with Σ_{p,q} β_{p,q} = N(G), rows 0 ≤ p ≤ ρ and row ρ nonzero (`Paper.thm_structure_betti`, `Paper.alg_total_betti`); a finite free resolution of 𝒰_G over the coefficient ring whose free terms have bases indexed by contributing states with their local Čech-cohomology basis indices (`IncResolutionBasis`, `incResolutionDifferential`), exact, minimal (the differential vanishes at the coefficient origin, `incResolutionDifferential_minimal`) and of length exactly ρ (`projectiveDimension_incidenceRing`). It is graded for the natural coefficient grading of 𝒰_G, with exactness in every internal degree (`NaturalGradedResolution.lean`); the differential preserves internal degree and its entries have degree card(S)−card(T) (`incResolutionDifferential_internal_degree`, `incResolutionDifferential_entry_degree`). Derived specialization has the state basis (`incidenceTorEquivState`, `finrank_incidenceTor`), and its internal pieces have dimension β_{p,q} (`incFreeTermToTor_eq_tmul`, `finrank_incidenceTorInternalPiece`), with a finite and unique decomposition |
| Tor_p(𝒰_G, ℂ)_q ≅ E_1^{−q,q−p}(G) = H^{q−p}(X_G, ∧^q F_G^∨) as bigraded algebras (`intro:tor`, `alg:tor-isomorphism`) | Proved | `Paper.alg_tor_isomorphism` (ℂ-linear isomorphism for p ≤ q from the internal-degree-q piece of `incidenceTor p`, Mathlib’s left derived extension of scalars along `constantCoeff`, to actual Ext-defined H^{q−p} of the q-th exterior bundle), `Paper.alg_tor_isomorphism_mul` (the standard Tor product goes to the cup product followed by exterior multiplication, with sign (−1)^{q·j}), `Paper.alg_tor_isomorphism_one` (unit). ∧^q F_G^∨ is the finite biproduct of the twist sheaves L(−d_S), \|S\| = q, identified on chart subopens with Mathlib’s exterior power of the sections of the dual edge bundle (`Paper.alg_exterior_chart_wedge_bijective_all`, `Paper.alg_exterior_pairing_wedge`), and the cup product is the standard product computed from the cubical cell resolution of the standard chart cover (both are described in "Differences in hypotheses"). For q < p the internal piece is zero (`Paper.alg_tor_piece_eq_bot_of_lt`), so no negative cohomological degree occurs. The normalization is fixed explicitly: in every bidegree a Tor class with a single state basis vector goes to the exterior class with the same state and coefficient +1 (`Paper.alg_tor_isomorphism_normalization`, which holds by construction of the state-basis isomorphism), since naturality, products and units alone would allow rescaling by λ^p; the K₄ test in bidegree (1, 5) is `Paper.alg_k4_tor_normalization`. The same isomorphism is also constructed without state bases, by the paper's base change of the Čech–Koszul model to the coefficient origin, and the two constructions are equal (`Paper.alg_zero_base_change_eq`). Also proved: state bases and dimensions β_{p,q} of the internal pieces (`incidenceTorInternalEquivState`, `finrank_incidenceTorInternalPiece`) and the Čech formula of the Tor product (`incidenceTorProduct_cech_formula`) |
| naturality for endpoint-preserving, non-contracting graph maps | Proved | for graph maps fixing the vertices the square with the Tor isomorphism commutes, the Tor map being induced by the ring maps and independent of the resolution and lift: edge relabelings (`EdgeRelabel`: edge bijections with per-edge orientation reversal and independent edge orders; `Paper.alg_tor_isomorphism_natural`, `Paper.alg_relabel_tor_product`, `Paper.alg_relabel_tor_one`, `Paper.alg_relabel_tor_trans`); the orientation signs ε_φ(e), as per-edge sign changes and signed edge relabelings that copy the chart equation of e to ε_φ(e) times that of φ(e) (`Paper.alg_signed_relabel_chart`, `Paper.alg_tor_isomorphism_sign`, `Paper.alg_tor_isomorphism_signed_natural`); edge maps that need not be injective, with the Tor map derived along the non-flat coefficient ring map, sending the state of S to the wedge sign times the state of φ(S) when φ is injective on S and to zero otherwise (`Paper.alg_derived_ring_map_eq`, `Paper.alg_edge_map_tor_state`, `Paper.alg_tor_isomorphism_edge_map_natural`); signed edge maps combining both, the state of S going to the wedge sign times ∏_{e∈S} ε_φ(e) times the state of φ(S) (`Paper.alg_signed_edge_map_chart`, `Paper.alg_signed_edge_map_tor_state`, `Paper.alg_tor_isomorphism_signed_edge_map_natural`). Vertex bijections: incidence and Tor isomorphisms, the Tor map permuting states with the Koszul sign of the vertex permutation, preserving products and composition (`Paper.alg_vertex_relabel_tor_state`, `Paper.alg_vertex_relabel_tor_product`, `Paper.alg_vertex_relabel_tor_trans`); on the geometric side the scheme isomorphism of (ℙ¹)^V, the transport of sheaf cohomology, of the twist sheaves (glued from the transported chart frames) and of the exterior bundles and their cohomology (`Paper.alg_vertex_scheme_perm`, `Paper.alg_vertex_sheaf_h_perm`, `Paper.alg_vertex_twist_perm`, `Paper.alg_vertex_exterior_cohomology`); the multi-twist state formula (the transport acts on state coordinates by the Koszul-signed relabeling, with the constant 1 going to 1 and the swap giving −1 on H^2 of O(−2,−2)) and hence the naturality square (`Paper.alg_vertex_twist_state_formula`, `Paper.alg_tor_isomorphism_vertex_natural`, `Paper.alg_vertex_exterior_product`). Vertex maps that identify vertices (edges unchanged): incidence ring maps by pullback along a_φ, Tor maps preserving products, units and composition (`Paper.alg_vertex_map_incidence`, `Paper.alg_vertex_map_tor_product`, `Paper.alg_vertex_map_tor_trans`); in every Tor degree the Tor map commutes with the edge sign action, preserves the edge-set components and the internal degree, and kills the component of an edge set whose active vertices φ identifies (`Paper.alg_vertex_map_tor_sign`, `Paper.alg_vertex_map_edge_set`, `Paper.alg_vertex_map_internal_degree`, `Paper.alg_vertex_map_collision_zero`); in degree zero z_C goes to a nonzero multiple of z_{φ(C)} if φ is injective on the vertices of C and to zero otherwise (`Paper.alg_vertex_map_cycle_class`, `Paper.alg_vertex_map_cycle_zero`, `Paper.alg_vertex_map_cycle_product_zero`). The disjoint-union isomorphism 𝒰_{G⊔H} ≅ 𝒰_G ⊗ 𝒰_H with its coefficient, symmetry, associativity and unit compatibilities (`Paper.alg_disjoint_union_tensor`, `Paper.alg_disjoint_union_coeff`, `Paper.alg_disjoint_union_comm`, `Paper.alg_disjoint_union_assoc`, `Paper.alg_disjoint_union_unit`). For maps identifying vertices also the explicit Tor state formula on non-colliding states with its sign, z_C ↦ ±z_{φ(C)} with that sign (`Paper.alg_vertex_map_tor_state_formula`, `Paper.alg_vertex_map_cycle_sign`), the scheme map a_φ, the pullback of the twist sheaves and of exterior cohomology (`Paper.alg_vertex_twist_pullback`, `Paper.alg_vertex_map_exterior_pullback`), and the naturality square on colliding states (`Paper.alg_tor_isomorphism_vertex_map_collision`). The naturality square for maps identifying vertices holds unconditionally (`Paper.alg_tor_isomorphism_vertex_map_natural`, through the multi-twist state formula for the pullback `Paper.alg_vertex_map_twist_state_formula`). General graph maps (`GraphMap`: vertex map, edge map, reversals and signs): intrinsic coefficient and incidence ring maps with a_φ^* b_e = ε_φ(e) b_{φ(e)}, Tor maps derived along them, identity and composition laws, independence of the factorization into a vertex map and a signed edge map, and the naturality square (`Paper.alg_graph_map_relation`, `Paper.alg_graph_map_tor_trans`, `Paper.alg_graph_map_tor_factorization`, `Paper.alg_tor_isomorphism_graph_map_natural`). The incidence ring maps are graded algebra maps for the natural coefficient grading, and the disjoint-union isomorphism identifies the degree-n piece with ⊕_{i+j=n} (piece_i ⊗ piece_j) (`Paper.alg_graph_map_graded`, `Paper.alg_disjoint_union_graded`) |
| Hilb_{𝒰_G}(t) = θ_G(t,2i)/(1−t)^{4m} = ω_G(t)/(1−t)^{3m+n} (`intro:hilbert`) | Proved | `Paper.alg_hilbert_theta`, `Paper.alg_universal_hilbert`, `Paper.alg_hilbert_reduced`; `incidenceHilbertSeries` is defined from the actual finite dimensions of the natural ring components. The proof uses the degreewise exact free resolution, with the zero-edge case included |
| Artin reduction A_G by a regular sequence of d_G general linear forms, Hilb_{A_G} = ω̃_G = ∏_C ω_C | Proved | the length-d_G coefficient tuples whose quotient is finite-dimensional (then nonzero and Artinian) form a nonempty Zariski-open set (`Paper.alg_artin_parameter_open`, with a principal open certificate `Paper.alg_artin_parameter_certificate`); every tuple in this set is a regular sequence, and its quotient has Hilbert series ω̃_G and dimension ω̃_G(1) (`Paper.alg_artin_parameters_regular`; also `Paper.alg_linear_artin_exists`, `Paper.alg_artin_hilbert`, `Paper.alg_artin_length`, and regular Artin quotients in every maximal ideal, `Paper.alg_regular_artin_exists`). ω̃_G = ∏_C ω_C over the components containing a cycle, with θ_C = (1−t)^{ν(C)−1} ω_C, is the polynomial identity `Paper.thm_structure_omega`; for K₄ a linear regular Artin quotient of dimension 30 exists (`Paper.alg_k4_artin_exists`) |

### Theorem 1.2 (`thm:real`)

| Clause | Status | Lean |
|---|---|---|
| (i) for fixed a_e ≠ 0, a_e² ≠ 1 and all sufficiently small nonzero p_i = b_i⁻¹, the complex admissible fiber consists of exactly Q(G) simple roots | Proved | `Paper.thm_real_i` (= `strong_field_exactly_Q_simple`) |
| (i) smooth local analytic extension across p = 0 and the power-map normal form p_i = (−1)^{d_S(i)} w_i^{r_i} (`intro:power-map`) | Proved | `Paper.sf_normal_form` (= `exists_powerMap_normal_form`): analytic chart with analytic coordinate change and analytic inverse, exactly wt(S) distinct simple admissible solutions per state for small nonzero p |
| (i) boundary local algebra ⊗_i ℂ[w_i]/(w_i^{r_i}) of length wt(S) | Proved | the local algebra of the special fiber p = 0 of the state chart, the analytic germs at 0 modulo the parameter germs, is ℂ[w]/(w_i^{r_i}), in the chart coordinate and in the vertex coordinate of the power-map chart (`Paper.sf_state_fiber_equiv`, `Paper.sf_vertex_fiber_equiv`); it is local of length wt(S) and the parameter germs form a regular sequence (`Paper.sf_state_fiber_length`, `Paper.sf_state_fiber_regular`); the polynomial algebra itself: `Paper.sf_boundary_algebra_length`, `Paper.sf_boundary_algebra_regular` |
| (ii) at every field h, every Eulerian edge subset is the negative-message support of an admissible real root | Proved | `Paper.thm_real_ii_sector` |
| (ii) R_G(J, h) ≥ 2^{ν(G)} at every field | Proved | `Paper.thm_real_ii_lower` (with `ENat.card`, so finiteness is not assumed) |
| (ii) in every field orthant, sufficiently large fields give (N_ℂ, R_G, N_+) = (Q(G), 2^ν, 1) with all complex roots simple (`intro:three-counts`) | Proved | `Paper.thm_real_ii_strong`; the threshold H on \|log b_i\| is uniform over all sign patterns |
| (ii) min_h R_G(J, h) = 2^{ν(G)} (`intro:minimum`) | Proved | `Paper.thm_real_ii_min` |
| (`intro:generator-real-bridge`): maximum degree ≤ 3 implies Σ_q β_{0,q} = 2^ν = min_h R_G | Proved for the chart-intersection model | `Paper.intro_generator_real_bridge` proves the state-sum equality Σ_q β_{0,q} = 2^ν (with `betti` the state sum) and the minimum real count; the general inequality Σ_q β_{0,q} ≤ 2^ν with its equality criterion is `Paper.alg_generator_real_bridge`. The identification of the left side with graded Tor dimensions follows from `finrank_incidenceTorInternalPiece` and `NaturalGradedResolution.lean`; the intrinsic module minimum, homogeneous generating family and real-minimum comparison are proved by `Paper.alg_module_generator_number`, `Paper.alg_module_generators_minimal` and `Paper.alg_module_generator_min_real_count` |

## Differences in hypotheses (Lean definitions versus the paper)

- **Graphs.** A multigraph is a vertex type `V`, an edge type `E` and
  endpoint maps `fst snd : E → V` (the orientation is only used for
  display). Parallel edges are distinguished by their edge identifiers and
  degrees count multiplicity. The BP layer assumes `Loopless`; the
  combinatorial quantities admit loops, counted as degree 2.
- **Components, ν, τ, ρ.** Components are the quotient `Comp` by
  reachability along all edges; c(G) = `numComponents`; ν = m + c − n
  (`nu`, equal to dim H₁(G; 𝔽₂) for every graph); a tree component is one
  with m_K + 1 = n_K (isolated vertices included); τ = `tau`;
  ρ = m + τ − n; d_G = 3m + n − τ. All are natural numbers, and the
  nonnegativity needed for the subtractions is proved. For connected
  graphs ν = `cycleRank` = m + 1 − n.
- **2-core.** The union `core` of the generalized loops (edge sets without
  vertices of degree one). Agreement with the iterated removal of vertices
  of degree at most one is `isPruned_iff`.
- **ω.** ω_G is defined as the integer polynomial with
  (1−t)^n θ_G(t,2i) = (1−t)^m ω_G, that is ω_G = (1−t)^{n−m} θ_G(t,2i)
  as in the paper; ω_G = (1−t)^τ ω̃_G and ω̃_G = ∏_C ω_C over the
  components C that contain a cycle.
- **Generic degree N(G).** `HasGenericDegree G n` means: there is a
  nonzero polynomial P ∈ ℤ[a, b] such that for every nonzero complex
  parameter (a, b) with P(a, b) ≠ 0 there are exactly n admissible BP
  solutions, all simple (nonzero determinant of the Jacobian of the BP
  polynomial system with respect to the messages). Such an n is unique
  (`HasGenericDegree.unique`). This is the counting form of the paper's
  "degree of the finite étale cover over a nonempty Zariski open set". The
  algebraic form is also proved (`Paper.prop_bp_family_finite_etale`): over
  ℂ[a, b][1/s] for a nonzero s the localized family ring is finite, free of
  rank Q(G) and étale (Mathlib's `Algebra.Etale`), stated for the affine ring
  map rather than in the language of schemes; s comes from a shape-lemma
  certificate and is not claimed to cut out the largest étale locus.
- **Admissibility.** `IsAdmissibleSolution a b y` is the polynomial fixed
  point equation together with the open condition (`eq:admissibility`):
  every message y_α ≠ 0, every update denominator X_α + a_e ≠ 0 and every
  vertex factor 1 + F_i ≠ 0 (`Admissible`). The rational form of the update
  is equivalent on this set (`isFixedPoint_iff_isRationalFixedPoint`).
- **Boundary exclusion (Lemma 2.3).** Stated for an arbitrary field with a
  valuation `v : Valuation K Γ₀` (`boundary_exclusion`) instead of the
  t-adic valuation of 𝒦 = \overline{K((t))}. The extension of the
  valuation takes, in an algebraic closure of K((t)), a valuation ring
  dominating K⟦t⟧ (`BP.newtonPuiseux_exists`); the Newton–Puiseux theorem
  itself is not used.
- **Constancy of the generic fiber.** The paper's use of "generically
  finite étale" is replaced by the abstract statement
  `BP.generic_fiber_constancy` (ℤ[s, β] → algebraically closed fields),
  proved through shape-lemma certificates.
- **Saturation lemma (Lemma 4.2).** Instead of "the generically étale
  locus is analytically dense in the smooth irreducible total space", the
  development uses density through the rational parametrization of the
  auxiliary coordinates and the identity theorem on complex lines
  (`exists_aux_near_generic`), together with the abstract topological lemma
  `card_eq_of_saturation`. Lemma 4.2 as stated for smooth irreducible varieties
  is therefore not formalized; Corollary 4.3 is.
- **Internal grading of Tor.** The internal degree-q piece
  `incidenceTorInternalPiece p q` of Tor_p^{S_G}(𝒰_G, ℂ) is defined as the image
  of the internal-degree-q part of the p-th term of the natural graded free
  resolution. Its independence from the choice of graded resolution is not
  formalized; the dimensions are β_{p,q} and the isomorphism with
  H^{q−p}(X_G, ∧^q F_G^∨) is proved for these pieces.
- **Real counts.** R is `Nat.card {y : Dart E → ℝ // IsAdmissibleSolution a b y}`
  (the lower bound at every field uses `ENat.card` and does not assume
  finiteness), and the positive count is the number of admissible real
  solutions with every message positive. Couplings are a_e = e^{2J_e} > 0
  with a_e ≠ 1 (J_e ≠ 0); fields are b_i = e^{2h_i} > 0. Strong field
  means \|log b_i\| ≥ H at every vertex, all sign patterns at once. The
  roots counted are the same as in the paper: admissible real solutions in
  the localization (`eq:admissibility`), with finite nonzero messages. The
  paper's phrase "allowing the value ∞" for R_G(J, h) allows the number of
  roots to be infinite, which is why the bound at every field is stated
  with `ENat.card`; the strong-field and minimum statements use `Nat.card`
  together with explicit finiteness.
- **Simple cycles and generators.** A simple cycle is a nonempty Eulerian
  edge set without a nonempty Eulerian proper subset (`IsSimpleCycle`, the
  minimal elements of the binary cycle space; all its degrees are 0 or 2).
  `incidenceModuleGeneratorNumber` is Mathlib's `Submodule.spanFinrank` of
  𝒰_G as a module over the coefficient ring.
  `Paper.alg_module_generator_number` identifies this intrinsic minimum with
  Σ_q β_{0,q}; the augmentation gives a homogeneous minimal family with
  β_{0,q} elements of degree q. The cycle criterion and real
  minimum comparison are proved for this count, without a sheaf comparison.
- **Nondegeneracy (Corollary 5.5).** Nonzero determinant of the Jacobian of
  the BP system over ℝ (`IsSimpleSolution`).
- **The universal ring.** `IncidenceRing` is the subalgebra of the common
  torus ring given by the intersection of the images of the affine chart
  rings (`incChartMap`). It is identified with the global sections of
  `incidenceGluedScheme`, glued from these chart quotient rings and all their
  higher overlaps, and with the global functions of the independently
  constructed projective zero scheme. The natural coefficient grading is
  defined on every chart, with vertex coordinates in degree zero and free
  coefficients in degree one, and proved to be a graded algebra.
- **Exterior bundle.** Mathlib has no exterior powers or duals of sheaves of
  modules. ∧^q F_G^∨ is the finite biproduct of the twist sheaves L(−d_S)
  over the edge sets S with |S| = q; in degree one it is the dual edge bundle
  (`Paper.alg_exterior_bundle_one`). On every open inside a standard chart and
  in every degree, Mathlib's exterior power of the sections of the dual edge
  bundle maps bijectively onto its sections, and its product pairing is
  exterior multiplication (`Paper.alg_exterior_chart_wedge_bijective_all`,
  `Paper.alg_exterior_pairing_wedge`).
- **Cohomology and cup product.** Sheaf cohomology is Mathlib's Ext-defined
  cohomology of the underlying abelian sheaf. The cup product is the standard
  product on these groups defined through the cubical cell resolution of the
  standard chart cover of (ℙ¹)^V, from the unit identification, the inverse
  left unitor, the inverse tensor of the two input augmentations and
  Mathlib's shifted tensor pairing. It does not depend on representatives,
  and it is natural in the coefficient pairing and along supplied
  augmentation-preserving chain maps between the cell complexes of binary
  covers; every binary cover family of (ℙ¹)^V with affine cell opens computes
  the same product. Its independence from arbitrary resolutions is not
  formalized.
- **Vertex enumeration.** State products, and the state coordinates of
  cohomology, order the vertices by `Fintype.equivFin V`. The absolute signs
  of state products depend on this enumeration; the reverse-order sign,
  associativity and unit laws do not.
- **Brouwer degree.** Mathlib has no degree theory. For C¹ maps f of a
  finite-dimensional real space to itself, `brouwerDegree f` is the signed
  count Σ_{f(x)=y} sign det Df(x) at a regular value y (`signedFiberCount`;
  regular values exist in every ball by Mathlib's Sard theorem). For maps at
  bounded distance from an invertible linear map A, which are proper, the
  signed count is the same at every regular value and equals sign det A
  (`Paper.proper_degree_regular_value`, `Paper.proper_degree_linear`), and the
  degree is also given by the determinant integral
  ∫ ψ(f x) det Df(x) dx = deg f · ∫ ψ for every continuous compactly supported
  ψ, which needs no regular value (`Paper.proper_degree_integral`). The paper
  defines the degree through the induced map of spheres (Milnor); the
  coincidence of the two definitions, well-definedness for general proper
  maps, and degree theory for continuous maps are not formalized. Homotopy
  invariance along D_S − tΨ_S is obtained by computing the degree of each map.
- **Base rings.** The paper works over ℂ. The sheaf-theoretic statements are
  proved over arbitrary small commutative base rings; those about positive
  cohomology degrees assume the base Noetherian, through affine vanishing.
  The Tor isomorphism is stated over ℂ.

## Completion status

Every clause of Theorems 1.1 and 1.2 is proved (the tables above, and
[MAIN_CLAUSES.md](MAIN_CLAUSES.md) with the complete types). The remaining
items fall into three kinds.

**1. Proved, possibly by another argument.** All rows marked Proved in the
correspondence table. Some conclusions are reached by a route different from
the paper's; these are described in "How the main results are proved" and,
for the main clauses, in MAIN_CLAUSES.md (status (b)).

**2. Independent intermediate statements of the paper that remain.** Their
conclusions, as used for the main theorems, are proved by the routes above.

- **Saturation lemma** (`sf:degree-saturation`, Lemma 4.2) for smooth
  irreducible varieties: replaced by an abstract topological lemma with an
  explicit density hypothesis; Corollary 4.3 is proved.
- **Functoriality route** (`supp:functoriality`): a map of Koszul algebras of
  sheaves and derived global sections giving 𝒰_G ⊗^L S_H → 𝒰_H, and the tensor
  formula through Künneth. The statements of `alg:functoriality` are proved by
  another route (factorization, state formulas and the chart model).
- **K₄** (`alg:k4-section`): the Gröbner-basis check over 𝔽_32003 is an
  external computation (the graded shape of the resolution and the vanishing
  of products of nonunit generator classes are proved).

**3. Generalizations and internal comparisons that no paper statement
needs.** They are not part of the paper's claims and are not counted as
missing.

- The cup product on sheaf cohomology is defined through the cubical cell
  resolution of the standard chart cover; on (ℙ¹)^V over a Noetherian base,
  every binary cover family with covering charts and affine cell opens computes
  the same product (`Paper.alg_vertex_cup_cover_independent`,
  `Paper.alg_cover_refinement_augmentation`,
  `Paper.alg_standard_class_cup_concat`). Covers that are not binary families,
  independence from arbitrary resolutions, and a cover-free cup product on
  derived sheaf cohomology (Mathlib has none) are not formalized.
- The geometric functor laws over a general base ring (they are proved over
  ℂ, where the paper works).
- Relative Spec of a general quasi-coherent algebra and its universal property
  (Mathlib has none). Z_G is identified with the total space of the kernel
  bundle glued from Spec Sym of the kernel frames, and K^∨, Sym(K^∨) are used
  face by face in these frames rather than as quasi-coherent sheaves of
  algebras.
- The internal grading S_G(−q) on the universal Koszul complex of sheaves; it is
  carried by the Čech–Koszul model, where all graded statements are proved.
- RΓ(X_G, −) as an object of a derived category independent of covers: the
  derived base change represents it by the Čech model, and the derived
  products are compared for Mathlib's tensor product of complexes over the
  field ℂ, not through a monoidal structure on D(ℂ) (Mathlib has none).
- In `real:vertex-map`, the solution spaces are identified through mutually
  inverse real-analytic maps on open sets; an isomorphism of analytic germs
  with nonreduced structure is not formalized.
- Comparisons of two internal Lean constructions with each other, for example
  the cubical cell route against the two-open Mayer–Vietoris representatives
  or the tuple Čech complex, comparisons between bracketings or vertex
  enumerations of finite tensor products, and the removal of the Noetherian
  hypothesis from positive-degree vanishing (the paper works over ℂ).

## How the main results are proved

- **N = Q (§2).** The admissible BP system is rewritten in auxiliary
  coordinates (`Degree/AuxSystem.lean`, `Degree/Inverse.lean`). The
  boundary exclusion is proved in valuation form for any valued field
  (`Degree/Boundary/`). On the weak-coupling line s_e = 1 + t c_e the limit
  system at t = 0 has exactly Q(G) solutions (`Degree/Limit/`), each lifts
  uniquely by a multivariate Hensel lemma to K⟦t⟧ and to a Puiseux-type
  valued field (`Degree/Lift/`), so that the fiber over a generic point of
  the line has exactly Q(G) simple solutions. The constancy of the generic
  fiber over ℤ[s, β] (`Degree/Generic/FiberConstancy.lean`, proved with
  shape-lemma certificates rather than étaleness) transfers the count and
  the simplicity to a nonempty Zariski open set of parameters over every
  algebraically closed field (`Degree/Generic/Count.lean`,
  `Degree/Main.lean`).
- **The admissible family (Proposition 2.2).** The coordinate ring of the
  admissible total space is identified with the normalized belief ring
  (`Family/Beliefs.lean`), embedded into a localization of a domain built
  from the quadratic edge covers (`Family/Domain.lean`), and shown to be
  smooth over ℂ and of Krull dimension m + n through an injective integral
  extension of free belief coordinates (`Family/Smooth.lean`,
  `Family/Dimension.lean`).
- **The universal ring (§3).** `Incidence/Chart.lean` presents each chart
  as a polynomial ring in n + 3m variables, `Incidence/Torus.lean`
  identifies the common torus with a localization, and
  `Incidence/Normal.lean` proves integral closedness of the intersection.
  Finiteness over the coefficient ring uses integrality with respect to
  every valuation ring containing the coefficients and the finiteness of
  the integral closure (`Incidence/Integral.lean`, `Incidence/Finite.lean`).
  The Krull dimension d_G combines an upper bound by d_G generators with a
  lower bound from a Hall matching and algebraic independence
  (`Incidence/Matching.lean`, `Incidence/Dimension.lean`). The free
  resolution comes from the Koszul–Čech total complex, two finite
  homological perturbations, the gluing of the degree-zero cycles to the
  unchanged `IncidenceRing`, minimality at the coefficient origin and a
  nonzero top Ext class (`Incidence/KoszulCech.lean`,
  `Incidence/Resolution*.lean`, `Incidence/QuotientCechSections.lean`).
- **Tor and sheaf cohomology (§3).** The isomorphism is built in two ways
  that are proved equal (`Paper.alg_zero_base_change_eq`). The paper's base
  change: ℂ ⊗_{S_G} of the Čech–Koszul total complex (free over S_G) is the
  Čech complex of ⊕_q ∧^q F_G^∨ on X_G over ℂ, the Koszul part vanishes, the
  base change of the perturbation data computes Tor from it, and its cohomology
  is the actual sheaf cohomology (`Paper.alg_zero_base_change_model`,
  `Paper.alg_zero_base_change_tor`, `Paper.alg_zero_base_change_sheaf`); this
  route uses no state bases. It is also an isomorphism in D(ℂ): the
  perturbation data give a homotopy equivalence over S_G between the free
  resolution and the Čech–Koszul total complex, whose base change to ℂ is an
  isomorphism in D(ℂ) inducing the Tor isomorphism on cohomology and
  multiplicative for the products on Mathlib's tensor product of complexes:
  the zero-differential pair model of states is the tensor product of the
  state model ℂ ⊗ F⁻ with itself, the Čech–Koszul product over ℂ is a chain
  map C₀ ⊗ C₀ → C₀, and the square of products commutes in D(ℂ)
  (`Paper.alg_zero_base_change_derived`,
  `Paper.alg_zero_base_change_derived_exterior`,
  `Paper.alg_zero_base_change_pair_tensor`,
  `Paper.alg_zero_base_change_cech_product`,
  `Paper.alg_zero_base_change_derived_product`). The comparison in state bases: derived specialization of the free
  resolution is computed by the zero-differential state complex
  (`incidenceTorEquivState`). The positive-degree cohomology of every integral
  multi-twist on (ℙ¹)^V is computed by the cubical cell resolution of the
  standard chart cover; for the nonpositive twists that make up the exterior
  bundle, the state contraction of the Čech coefficient complex identifies it
  with the state pieces (`Paper.alg_vertex_twist_cohomology_states`). The Tor
  product and the cup product are defined independently and compared through
  injective state vectors (`Paper.alg_tor_isomorphism_mul`). The next
  section gives the details.
- **Universal Koszul complex and derived global sections (§3).** The
  universal Koszul complex `alg:universal-koszul` is a complex of sheaves of
  modules on (ℙ¹)^V × Spec S_G with terms ∧^k F_G^∨ and differential the
  contraction with the universal section (`Paper.alg_universal_koszul_complex`,
  `Paper.alg_universal_koszul_d_comp`). It is exact in every negative degree as
  a complex of sheaves (`Paper.alg_universal_koszul_exact`); on a chart its
  differential is the Koszul differential of the chart incidence equations, a
  regular sequence (`Paper.alg_universal_koszul_chart`,
  `Paper.alg_koszul_exact_of_regular`). Its Čech–Koszul total complex for the
  product of the standard two-chart covers is S_G-linearly isomorphic to the
  total complex of the resolution (`Paper.alg_universal_koszul_cech_equiv`,
  `Paper.alg_universal_koszul_cech_internal`). The derived global sections are
  the hypercohomology H^n(K_G) = Hom_{D(Ab)}(ℤ, K_G[n]) in the derived category
  of abelian sheaves (any model of it), which for a sheaf in degree zero is
  Mathlib's `Sheaf.H` (`Paper.sheaf_hypercohomology_single`). The Čech–Koszul
  model computes it (`Paper.alg_resolution_derived_cech`, by induction over the
  stupid truncations with the five lemma), so H^n(K_G) = 0 for n ≠ 0 and
  H^0(K_G) ≅ 𝒰_G over S_G (`Paper.alg_resolution_derived_vanishing`,
  `Paper.alg_resolution_derived_h0`). Lean deduces this concentration from the
  exactness of the resolution, the converse of the paper's order. The sheaf
  route agrees with this identification: postcomposing with the augmentation
  K_G → i_*𝒪_{Z_G}[0] and reading H^0 as global sections, followed by
  Γ(Z_G, 𝒪) ≅ 𝒰_G, gives the same map H^0(K_G) → 𝒰_G
  (`Paper.alg_resolution_derived_h0_augmentation`).
- **Strong field (§4).** Statewise chart systems with branches given by the
  implicit function theorem (`StrongField/Chart.lean`,
  `StrongField/ChartSolution.lean`), the saturation lemma
  (`StrongField/Saturation.lean`) and the simplicity of the roots
  (`StrongField/Simple.lean`) give the exhaustion of the complex fiber by
  Q(G) simple roots (`StrongField/Exhaustion.lean`). The analytic germ
  algebra at 0 (`StrongField/AnalyticGerm.lean`) admits monomial division by
  (w_i^{r_i}): an analytic function is a polynomial in the box plus
  Σ_i w_i^{r_i} g_i with analytic g_i, by an explicit power series for the
  quotient by one coordinate (`StrongField/AnalyticDivision.lean`); coefficient
  functionals give uniqueness. Hence the special fiber of the power-map chart
  is the boundary algebra (`StrongField/AnalyticBoundary.lean`).
- **Real sectors (§5).** Sign sectors and the maximum principle
  (`Real/SignSectors.lean`), the two edge branches (`Real/EdgeBranches.lean`),
  the vertex map as a bounded perturbation of an invertible diagonal map
  (`Real/VertexMap.lean`, `Real/BoundedPerturbation.lean`), the counting
  (`Real/Count.lean`), the parity of nondegenerate sectors through a
  determinant integral (`Real/SectorOddness.lean`,
  `Real/SectorRegularity.lean`), the strong-field count for every sign
  pattern through a spin gauge (`Real/StrongFieldCount.lean`) and the
  positive-root budget (`Real/PositiveBound.lean`).

## Natural coefficient grading, Tor pieces and Čech products

Throughout this section, comparisons are between independently defined
objects: no grading, module structure, action or product is transported from
the desired target by definition.

### Natural grading and internal Tor pieces

`incidenceCoefficientPiece n` is defined independently of the free resolution:
its elements restrict to homogeneous degree-n free-coefficient polynomials
on every affine chart. `ChartCoefficientGrading.lean` proves that exchanging
face and coefficient variables and eliminating each edge's pivot coefficient
preserve this degree. `coeffHom` and the augmentation preserve it.
`incidenceCoefficientGradedAlgebra` proves directness, spanning, unit and
multiplication. `incResolutionAugmentation_graded_surjective`,
`incResolutionAugmentation_graded_exact` and
`incFreeTermDifferential_graded_exact` prove exactness of the augmented free
resolution in every internal degree. Thus the internal Tor pieces below come
from the natural graded resolution of the chart-intersection ring.

`incidenceTorInternalPiece p q` is the image of the internal degree-q part of
the p-th free term under `incFreeTermToTor p`. `incFreeTermToTor_eq_tmul`
identifies this map with `x ↦ 1 ⊗ x`, followed by the isomorphism with
derived specialization. The definition does not prescribe a dimension.
Evaluation at the coefficient origin and an explicit constant-coefficient
lift prove `incidenceTorInternalEquivState` and
`finrank_incidenceTorInternalPiece`. `sum_incidenceTorComponent` and
`incidenceTorInternalPiece_sum_unique` give existence and uniqueness of the
finite decomposition; pieces above the number of edges vanish.

`IncidenceHilbertSeries.lean` defines the Hilbert series from the finite
dimensions of the natural ring components and proves its θ, ω and ω̃ formulas
from exactness in each natural degree, including the zero-edge case. The
degree-zero component consists of the constants (`Paper.alg_degree_zero`).

### Čech products and the Tor product

In the namespace `BPFixedPoints.CechLine` (`CechCup.lean`,
`CechCupCohomology.lean`), `cup` is the Alexander–Whitney product on the
two-chart complexes for O(−d). Its mixed terms use the left and right
restrictions, including the right-hand twist. `cup_leibniz` and `cup_assoc`
concern these complexes. `cohomologyCup_projection` proves independence of
cocycle representatives; `cohomologyCup_assoc`, `cohomologyCup_unit_left` and
`cohomologyCup_unit_right` give the induced algebra laws.
`cohomologyCup_eq_zero_of_pos` proves local vanishing when both twists are
positive.

`CechProduct.cohomologyCup` (`CechProductCup.lean`) uses signed tensor
products of the selected cycle representatives on arbitrary finite vertex
sets. `cyclePairing_closed`, `finCyclePairing_cup_cons` and
`cohomologyCup_eq_zero_of_overlap` prove closure, the signed pure-tensor
projection formula and vanishing for overlapping positive twists.
`CechProduct.chainCup` (`CechProductChainCup.lean`) extends the construction
to the full Čech complex. It tensors the local Alexander–Whitney products
with the Koszul sign obtained by exchanging the right head with the left
tail. `chainCup_leibniz` proves the Leibniz rule for the Čech differential,
and `chainCup_sign` proves compatibility with parity.
`cohomologyCup_chain_projection` (`CechChainCupComparison.lean`) identifies the
projection of the product of any two cocycles with the explicit cohomology
product. Thus `chainCup_projection_eq_of_same_class` proves independence of
arbitrary representatives, and overlapping positive twists give a boundary
for any representatives.

The full incidence product `incTotalCup` (`KoszulCechCupDifferential.lean`)
combines the Čech product with the edge exterior product. On edge supports
S, T it is zero when they intersect; otherwise it has the edge shuffle sign,
the union S ∪ T, and the extra sign obtained by moving the right Čech factor
past the |S| left edge generators. `erase_wedgeSingle` proves the exterior
contraction rule, while `chainCup_multiply_left` and `chainCup_multiply_right`
establish compatibility with the edge coefficient actions. These give
`incTotalCup_leibniz` for the total differential and `incTotalCup_degree` for
homological degree addition. `incResolutionCup` is its finite-perturbation
transfer p′ μ(i′x,i′y), with its chain rule and degree statement.

`incResolutionAugmentation_cup` (`ResolutionCupAugmentation.lean`) compares
this product with multiplication in `IncidenceRing`. The proof uses the
all-left chart projection, its multiplicativity, the fact that augmentation
kills the total differential, and the contraction homotopy.

`incTensorResolutionComplex` is the nonnegative tensor complex of the free
resolution P with itself, expressed using free pair bases and the signed
tensor differential. Its terms are projective. The generalized comparison
theorem `projectiveLiftHomotopy` constructs a homotopy between any two maps
from a complex with projective terms to P that have the same augmentation;
exactness of the source is not assumed. Thus any two multiplication lifts
P ⊗ P → P agree after specialization at the coefficient origin, where both
differentials vanish (`specialized_chainMap_eq`).

`incidenceTorProduct` (`ResolutionTorProduct.lean`) is defined on Mathlib's
left derived extension of scalars using this specialized tensor product and
any lift of the ring multiplication. `incidenceTorProduct_eq_of_lift` proves
independence of that lift; `incidenceTorProduct_eq_transferred` identifies it
with the concrete transferred product. Finally
`incTransferredPairing_atOrigin` removes the perturbation corrections. In the
injective full free-module coordinates `incidenceTorToFull`,
`incidenceTorProduct_cech_formula` (`Paper.alg_tor_product`) states that the
standard Tor product is exactly 1 ⊗ p μ(ix,iy). These are proofs about
Mathlib's derived Tor, not a definition of Tor as a state module.

The Tor product satisfies the left and right unit laws, associativity and
graded commutativity with sign (−1)^(pq) (`incidenceTorOne_mul`,
`incidenceTor_mul_one`, `incidenceTorProduct_assoc`,
`incidenceTorProduct_graded_comm`). The unit comes from a lift of 1 in the
incidence ring. Associativity compares maps from the threefold tensor
complex, using only projectivity of its terms and the augmentation. The
signed opposite product is another multiplication lift, which proves graded
commutativity. All these statements concern arbitrary Tor classes:
`incFreeTermToTor_surjective` provides representatives.

`ResolutionTorAlgebra.lean` bundles the homological pieces into a
`DirectSum.GRing` and `DirectSum.GAlgebra` over ℂ. `IncidenceTorAlgebra` is
their direct sum; `incidenceTorAlgebra_of_mul` identifies its homogeneous
multiplication, and `incidenceTorAlgebra_graded_comm` gives the signed
commutativity formula. It is not declared to be an ordinary commutative ring.

`ResolutionTorProductGrading.lean` proves compatibility with the internal
pieces induced by the natural ring grading:
`incidenceTorProduct_internal_degree` maps Tor(p,a) times Tor(q,b) into
Tor(p+q,a+b), and `incidenceTorOne_internal_degree` gives the unit bidegree
(0,0). The proof uses the Čech basis formula, additivity of disjoint edge
counts, and degree preservation of the perturbed inclusion and projection. A
homogeneous lift of the unit represents the same Tor class as any lift
because their difference is a boundary.

### Cohen–Macaulayness, Artin quotients and parameter cuts

Cohen–Macaulayness is proved by the Noetherian and
all-maximal-localizations depth–dimension criterion in
`IncidenceMaximalDepth.lean` (`Paper.alg_cohenMacaulay`,
`Paper.alg_origin_depth`). `IncidenceArtin.lean` constructs regular Artin
quotients in every maximal ideal (`Paper.alg_regular_artin_exists`).
`LinearParameterSequence.lean` constructs homogeneous linear regular
coefficient forms of length d_G, and `LinearArtinHilbert.lean` proves that
their quotient has Hilbert series ω̃_G, computed from the homogeneous
quotient components, and dimension ω̃_G(1) (`Paper.alg_linear_artin_exists`,
`Paper.alg_artin_hilbert`, `Paper.alg_artin_length`).

`IncidenceParameterOpen.lean` proves that the set of length-d_G coefficient
tuples whose quotient is finite-dimensional is a nonempty Zariski-open subset
of affine coefficient space, with the topology induced from `PrimeSpectrum` by
the kernels of polynomial evaluation (`Paper.alg_artin_parameter_open`,
`Paper.alg_artin_parameter_certificate`). At each finite quotient, bounded
homogeneous support supplies a positive vanishing component; the linear
multiplication map in that degree is surjective, and a polynomial determinant
preserves surjectivity on a principal open neighborhood. All these quotients
are nonzero and Artinian. `IncidenceParameterDepth.lean` proves that each
parameter ideal has the positive-degree maximal ideal as radical and has
depth d_G. `GradedDepthCriterion.lean` uses prime avoidance, induction in a
homogeneous quotient and graded permutation to prove that homogeneous linear
generators are regular whenever their number is at most the ideal depth.
`IncidenceParameterRegular.lean` applies it to every point of the open locus:
each tuple is regular, with quotient Hilbert series ω̃_G and dimension
ω̃_G(1) (`Paper.alg_artin_parameters_regular`).

`IncidenceParameterNormalization.lean` proves that each such tuple defines a
finite injective polynomial-ring map with algebraically independent images.
`GradedParameterBasis.lean` lifts a homogeneous basis of the Artin quotient
and uses the Hilbert-series identity to obtain injectivity in each component,
so `IncidenceParameterFree.lean` proves finite freeness, faithful flatness and
rank ω̃_G(1) (`Paper.alg_parameter_normalization`,
`Paper.alg_parameter_finite_free`). `IncidenceParameterBaseChange.lean` proves
that nonzero base change preserves these properties and identifies the
quotient by any proper parameter ideal with the tensor base change
(`Paper.alg_parameter_baseChange`, `Paper.alg_parameter_cut`). No algebraic
isomorphism between different fibers, and no variation of the chosen basis
with the tuple, is claimed.

`IncidenceParameterSections.lean` proves that every initial segment of a tuple
is regular, with quotient Hilbert series ω̃_G/(1−t)^(d_G−r); when d_G > 0 the
first d_G − 1 cuts give ω̃_G/(1−t) (`Paper.alg_parameter_section_hilbert`,
`Paper.alg_pencil_hilbert`). `LinearPolynomialCoordinates.lean` extends the
coefficient forms to polynomial coordinates, making the coefficient ring free
over the parameter ring; `ProjectiveTargetBaseChange.lean`,
`TensorBaseChangeSquare.lean` and `IncidenceParameterResolution.lean` show that
the augmented resolution stays exact after the cut, and
`BaseChangeMinimality.lean` that it stays minimal at every compatible residue
origin (`Paper.alg_parameter_resolution_exact`,
`Paper.alg_parameter_resolution_minimal`). `IncidenceParameterCutTor.lean` and
`IncidenceSectionTor.lean` compute Tor after the cut and prove invariance of
each homological Tor dimension and of the total Betti number Q(G) for all
initial cuts, including the pencil and Artin cuts
(`Paper.alg_parameter_cut_tor`, `Paper.alg_parameter_section_tor`,
`Paper.alg_parameter_section_total_betti`). `IncidenceCutGradedResolution.lean`
and `IncidenceCutTorGrading.lean` prove graded exactness and the internal
dimensions β_{p,q} after every successive coordinate cut
(`Paper.alg_parameter_resolution_graded_exact`,
`Paper.alg_parameter_augmentation_graded_exact`,
`Paper.alg_parameter_section_bigraded`); the grading interpretation requires a
homogeneous cut ideal. `IncidenceCutTorProduct.lean`,
`IncidenceCutTorNaturality.lean`, `IncidenceSectionTorProduct.lean` and
`IncidenceCutMultiplicationLift.lean` define the product after a cut by scalar
extension of a multiplication lift and prove that the comparisons between
uncut and cut Tor, and among all successive sections, preserve products
and internal degrees, independently of the lift
(`Paper.alg_parameter_cut_tor_product`,
`Paper.alg_parameter_cut_tor_naturality`,
`Paper.alg_parameter_section_tor_product`,
`Paper.alg_parameter_cut_product_internal`,
`Paper.alg_parameter_cut_chain_product`,
`Paper.alg_parameter_cut_lift_independent`).

### The incidence scheme

`IncidenceFaceRefinement.lean` descends all polynomial/Laurent face
restrictions to the quotient chart rings; they are injective and satisfy
identity and composition laws by their common-torus evaluation.
`IncidenceRefinementLocalization.lean` proves that they are localizations at
the product of the newly inverted coordinates, and
`IncidenceFaceIntersection.lean` that face joins realize intersections of the
localization opens.

`IncidenceFaceGluing.lean` constructs `incidenceGluedScheme` by Mathlib's
gluing of this locally directed open-immersion diagram and proves that it is
integral. `IncidenceGluedAtlas.lean` proves that the chart spectra cover it,
`incidenceFaceι_join_range` identifies all intersections with the prescribed
higher faces, and `IncidenceLaurentFace.lean` and `IncidenceGluedTorus.lean`
identify the torus with the all-Laurent face, compatibly with every chart
map. `AffineOpenSections.lean` identifies the sections on each affine open
through `ΓSpecIso`, and `IncidenceFaceSheafSections.lean` realizes every
higher face as an affine open with its quotient section ring and restriction
maps; `incidenceGluedGlobalSectionsEquiv` then applies sheaf gluing to
identify Γ(`incidenceGluedScheme`, 𝒪) with `IncidenceRing`. All atlas
assumptions of `incidenceGlobalSectionsEquivOfAtlas` are discharged for
this scheme. `IncidenceCoefficientMorphism.lean` glues the coefficient
variables to the projection onto coefficient space, and
`incidenceGluedGlobalSectionsAlgEquiv` respects the coefficient action.
`IncidenceGlobalResolutionTor.lean` and `IncidenceGlobalTorProduct.lean`
augment the free complex to global functions, prove exactness and minimality,
and show that derived Tor of the global functions is that of `IncidenceRing`,
with products preserved (`incidenceGlobalTorIso_mul`) and total dimension
Q(G).

`CoxNormalizedCharts.lean` and `CoxIncidenceZeroCharts.lean` normalize one of
the two homogeneous variables per vertex and prove that the normalized zero
scheme of the homogeneous edge equations has the incidence chart ring
(`incidenceHomogeneousZeroCharts`). `IncidenceEquationTransitions.lean` proves
that refinement multiplies each edge equation by an explicit endpoint unit,
`IncidenceZeroIdealDescent.lean` identifies extension and contraction of the
zero ideals, and `incidenceZeroFace_isPullback` gives the pullback squares of
the closed affine zero loci on each higher overlap.
`CechLineBundleTransitions.lean` proves the cocycle conditions for every
integral multi-twist, including tensor products and duals.

`ProjectiveLineEvaluation.lean` and `IncidenceProjectiveMorphism.lean` glue the
vertex coordinates to a morphism into the product of projective lines over
the coefficient scheme, compatible with the coefficient projection.
`ProjectiveLineChartPreimages.lean`, `ProjectiveProductChartImages.lean`,
`IncidenceProjectiveChartPreimages.lean` and
`IncidenceProjectiveChartFactorization.lean` identify the chart preimages and
chart maps with the surjective polynomial quotient maps; Mathlib's
target-locality theorem gives the closed immersion
(`IncidenceProjectiveClosedImmersion.lean`). `IncidenceProjectiveZeroCharts.lean`
and `IncidenceProjectiveZeroScheme.lean` define the closed zero scheme of the
homogeneous equations independently, by the scheme-theoretic kernels of the
zero charts, and prove that the glued scheme is isomorphic to it
(`incidenceProjectiveZeroIso`), compatibly with the embedding and the
coefficient map. `IncidenceProjectiveZeroAtlas.lean` proves that the full zero
quotients are open charts with pullback squares, so the scheme has exactly
the prescribed local zero schemes, including nilpotents and multiplicities.
`IncidenceProjectiveZeroSections.lean` identifies its global regular functions
with `IncidenceRing`, preserving the coefficient action.
`ProjectiveLineProper.lean` and `IncidenceProjectiveProper.lean` prove
properness, for every base change of the coefficient projection; the empty
vertex set is included. The vector-bundle presentation is formalized on
charts and on their overlaps. On every chart the evaluation map is surjective
with kernel free of rank 3m (`IncidenceVectorBundleCharts.lean`). On the
overlap face of two charts the evaluation maps differ by the diagonal action of
the edge-bundle transition units, so their kernels agree; the kernel
coordinates give linear transitions with the cocycle condition, proved by
cancelling inverse isomorphisms (`IncidenceKernelBundleTransitions.lean`); the
chart trivializations of Z_G differ by the induced linear substitutions
Sym(g^∨) (`IncidenceKernelBundleTrivialization.lean`). The units are the
transition coefficients of the edge line sheaves
(`IncidenceKernelBundleEdgeSheaf.lean`).

### Twist sheaves on products of projective lines

The statements of this subsection hold over every small commutative base
ring, include the empty vertex set, and need no Noetherian, domain or
nontriviality hypothesis.

- **The projective line.** `ProjectiveLineCharts.lean`,
  `ProjectiveLineGeometry.lean`, `ProjectiveLineOverlap.lean` and
  `ProjectiveLineSheafSections.lean` use Mathlib's Proj of the two-variable
  polynomial ring: the two standard opens are affine lines, their
  intersection is the Laurent affine scheme, and the structure-sheaf
  restrictions are the polynomial inclusion and the substitution of the
  inverse parameter. `ProjectiveLineGeometricSections.lean` and
  `AffineSchemeGlobalSections.lean` give the same formulas for global sections
  of the open subschemes.
- **Twists on ℙ¹.** `TwoOpenTwistSheaf.lean` constructs a sheaf of modules as
  the kernel of the difference of the two chart restrictions, the second one
  twisted by an overlap unit; `ProjectiveLineTwistSheaf.lean` uses the Laurent
  unit T^n, with addition and inverse laws. `TwoOpenTwistSections.lean`
  identifies sections on every open with the matching kernel.
  `TwoOpenTwistLocal.lean`, `TwoOpenTwistLocallyFree.lean`,
  `TwoOpenTwistTransitions.lean` and `ProjectiveLineTwistLocallyFree.lean` prove
  Mathlib's `IsLocallyFree` with one generator on each chart (through
  `LocalGeneratorsData`), quasicoherence, and the frame transition T^n
  (`Paper.alg_twist_sheaf_rank_one`, `Paper.alg_twist_sheaf_locally_free`,
  `Paper.alg_twist_sheaf_quasicoherent`, `Paper.alg_twist_frame_transition`,
  `Paper.alg_twist_frame_coordinate`).
- **Products over the coefficient base.** `ProjectiveLineOverBase.lean`,
  `ProjectiveLinePowers.lean`, `AffinePolynomialProducts.lean`,
  `ProjectivePowerAffineCharts.lean`, `ProjectivePowerChartCover.lean`,
  `VertexProjectiveProducts.lean`, `ProjectivePowerCoordinates.lean` and
  `ProjectiveLineTransitionMorphisms.lean` construct the finite product
  (ℙ¹)^V over the coefficient scheme, its vertex polynomial charts covering
  every point, the vertex projections, and the Laurent coordinate inversion
  as morphisms into Proj.
- **Tensor sheaves.** `SchemeModuleTensor.lean`,
  `SchemeModuleTensorSections.lean`, `SchemeModuleTensorUnits.lean`,
  `SchemeModuleTensorBaseLinearity.lean` and `SchemeModuleFiniteTensor.lean`
  construct tensor sheaves by Mathlib's pointwise tensor and module
  sheafification, with pure sections, unit isomorphisms, base scalars and
  ordered finite tensors. `PublicPresheafInternalHom.lean`,
  `PublicPresheafInternalHomSheaf.lean` and `PublicModuleTensorLocalization.lean`
  port the minimal internal-Hom and local-equivalence arguments from the
  pinned public Anthropic FLT sources listed in
  [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). `SchemeModuleMonoidal.lean`
  applies Mathlib's `LocalizedMonoidal` construction to module
  sheafification, which gives coherent associators, unitors and a symmetric
  braiding without a package dependency; `moduleTensorIsoMonoidal`
  (`SchemeModuleMonoidalComparison.lean`, `SchemeModuleMonoidalSections.lean`,
  `SchemeModuleTensorAssociator.lean`) compares the tensor sheaves with it,
  including pure sections and reassociation.
- **Multi-twists.** `VertexProjectiveTwistSheaf.lean` defines external tensor
  sheaves on (ℙ¹)^V from the pullbacks along the vertex projections, and the
  integral multi-twist as the external tensor of the one-factor twists
  (`Paper.alg_vertex_external_tensor`, `Paper.alg_vertex_twist_sheaf`,
  `Paper.alg_vertex_twist_empty`). Pullback and tensor frames
  (`SchemeModulePullbackFrames.lean`, `SchemeModuleSheafificationOver.lean`,
  `SchemeModuleTensorLocalFrames.lean`, `VertexProjectiveTwistLocalFrames.lean`,
  `SchemeModuleFrameScalars.lean`) give rank-one chart frames, local freeness
  and quasicoherence (`Paper.alg_vertex_twist_rank_one`,
  `Paper.alg_vertex_twist_locally_free`, `Paper.alg_vertex_twist_quasicoherent`).
  On each pairwise chart overlap the frames differ by the vertex-labelled
  product of the pulled-back Laurent units
  (`SchemeModuleTensorFrameTransitions.lean`,
  `SchemeModulePullbackTransitions.lean`, `ProjectiveLineTwistPairFrames.lean`,
  `VertexProjectiveTwistPairFrames.lean`;
  `Paper.alg_vertex_twist_pair_transition`), and the restrictions of the chart
  frames are exactly the pair frames (`SchemeModulePullbackCoherence.lean`,
  `SchemeModuleRestrictionPullbackCoherence.lean`,
  `SchemeModuleLocalFramePullbackCoherence.lean`,
  `SchemeModulePullbackRestrictionFrames.lean`,
  `VertexProjectiveTwistPairChartComparison.lean`,
  `VertexProjectiveTwistPairCoefficients.lean`). The tensor of two multi-twists
  is the sum twist (`Paper.alg_vertex_twist_tensor_add`, see "Products on
  cohomology" below).
- **Chart and face sections.** `VertexProjectiveChartSections.lean` and
  `VertexProjectiveTwistPolynomialSections.lean` identify the twist sections on
  a chart with the polynomial module. `VertexProjectiveFaceMorphisms.lean`,
  `VertexProjectiveFaceOpens.lean`, `AffineOpenSectionCoordinates.lean` and
  `VertexProjectiveFaceSections.lean` prove that each mixed face ring is an
  open immersion onto the rectangular intersection, with structure sections
  the face ring, restrictions the face refinements, and twist sections and
  degree-zero local Ext the face module.
  `SchemeModuleGeometricCoefficients.lean`,
  `ProjectiveLineLaurentEvaluation.lean`, `VertexProjectiveFaceTwistUnits.lean`,
  `VertexProjectiveTwistFaceRestrictions.lean`,
  `VertexProjectiveTwistFaceDiagram.lean` and
  `VertexProjectiveTwistFaceDifferences.lean` prove that the geometric
  transition unit on every face is `multiTwistTransition` and that the twist
  restriction on all faces, including changes of chart, is the face
  refinement times the inverse unit, with identity and composition laws and
  the native degree-zero Mayer–Vietoris differences.

### Cohomology of twist sheaves

Cohomology is Mathlib's Ext-defined cohomology of the underlying abelian
sheaf (`StructureSheafCohomology.lean`). Local Ext on the whole space is
global cohomology (`SheafTerminalCohomology.lean`), and local degree zero is
sections, naturally in the open (`SheafLocalCohomologyZero.lean`). The base
ring acts on Ext by postcomposition with geometric coefficients, independently
of any state comparison; restriction, evaluation and Mayer–Vietoris connecting
maps preserve this action (`SchemeModuleCohomologyScalars.lean`,
`SheafConnectingNaturality.lean`, `SchemeModuleCohomologyLinearity.lean`,
`SchemeModuleMayerVietorisLinear.lean`, `OpenUnitBaseLinearity.lean`).
Degree-zero statements hold over every small commutative ring; positive-degree
statements assume a Noetherian base, through affine vanishing.

- **Affine vanishing.** Injective abelian sheaves are flasque, and flasque
  sheaves are acyclic on every small space (`SheafInjectiveFlasque.lean`,
  `SheafFlasqueCohomology.lean`). On a Noetherian affine scheme, injective
  tilde sheaves are flasque (`InjectiveLocalizationSections.lean`,
  `AffineInjectiveBasicSections.lean`, `PrimaryTorsionInjective.lean`,
  `AffineTildeSupportedKernel.lean`, `SupportedLocalizationExtension.lean`,
  `AffineInjectiveSectionClearing.lean`, `AffineInjectiveFlasque.lean`), and
  every positive cohomology group of a quasicoherent module on Spec of a small
  Noetherian ring vanishes (`AffineTildeStalkComparison.lean`,
  `AffineTildeExact.lean`, `AffineTildeCohomology.lean`;
  `Paper.alg_affine_quasicoherent_global_vanishing`). The vanishing transfers
  to local Ext on affine opens (`OpenSheafCohomology.lean`,
  `AffineOpenCohomology.lean`, `NoetherianAffineOpenCohomology.lean`;
  `Paper.alg_affine_open_local_vanishing`). General modules are not asserted
  to be flasque, and no vanishing on non-affine opens is claimed.
- **Comparison tools.** Two-open and rectangle Mayer–Vietoris tools compare
  Čech quotients, section kernels and connecting maps with Ext
  (`SheafTwoOpenCechComparison.lean`,
  `SheafMayerVietorisQuotient.lean`, `SheafGlobalCechComparison.lean`,
  `SchemeModuleSectionH1.lean`, `SchemeModuleSectionKernel.lean`,
  `SchemeModuleMayerVietorisKernel.lean`,
  `SheafMayerVietorisOpenNaturality.lean`,
  `SheafMayerVietorisSectionConnecting.lean`, `SheafRectangleConnecting.lean`,
  `SheafRectangleTopQuotient.lean`, `SchemeModuleRectangleLinear.lean`). Where
  local vanishing is needed it is an explicit hypothesis; for twist sheaves
  over a Noetherian base, affine vanishing discharges it. For an augmented
  resolution with relatively acyclic terms, the cohomology of the Hom complex
  is Ext in every positive degree, through iterated Yoneda classes, naturally
  in the target sheaf and linearly for the geometric scalars; no projectivity
  or splitting is assumed (`AcyclicResolutionExtTower.lean`,
  `AcyclicResolutionExtCocycles.lean`, `AcyclicResolutionExtNaturality.lean`,
  `AcyclicResolutionScalars.lean`, `AcyclicResolutionComplex.lean`,
  `SchemeModuleResolutionCohomology.lean`).
- **One factor.** On ℙ¹ (`TwoOpenTwistGlobalMatching.lean`,
  `TwoOpenTwistGlobalSections.lean`, `ProjectiveLineTwistCechCoordinates.lean`,
  `ProjectiveLineTwistGlobalSections.lean`, `PolynomialCechLineComparison.lean`,
  `ProjectiveLineTwistH0.lean`, `SchemeModuleBaseScalars.lean`,
  `ProjectiveLineBaseSections.lean`, `ProjectiveLineTwistBaseLinearity.lean`,
  `ProjectiveLineMatchingBaseLinearity.lean`, `OpenUnitChartSections.lean`,
  `TwoOpenTwistCechFrames.lean`, `ProjectiveLineCanonicalCech.lean`,
  `ProjectiveLineCanonicalH1.lean`, `ProjectiveLineTwistCohomology.lean`,
  `ProjectiveLineCechBaseLinearity.lean`,
  `ProjectiveLineTwistH1BaseLinearity.lean`): global sections of O(n) are the
  polynomial matching kernel, linearly for the base action
  (`Paper.alg_twist_polynomial_global_sections_linear`). For n = −d the
  matching differential is the negative of the right-minus-left differential
  of the coefficient complex (through Mathlib's
  `AddMonoidAlgebra.coeffLinearEquiv`), and the canonical Čech quotient is the
  H1 state module (`Paper.alg_twist_matching_base_differential`,
  `Paper.alg_twist_canonical_cech_differential`,
  `Paper.alg_twist_canonical_cech_H1`). H0 is the H0 state module, finite free
  of rank one for d = 0 and zero otherwise over a nontrivial base, over every
  small commutative ring (`Paper.alg_twist_H0_linear`,
  `Paper.alg_twist_H0_free`, `Paper.alg_twist_H0_finite`,
  `Paper.alg_twist_H0_finrank`, `Paper.alg_twist_H0_cohomology_linear`,
  `Paper.alg_twist_H0_cohomology_finrank`). Over a small Noetherian base all
  positive local Ext groups of each twist vanish on both charts and their
  overlap (`Paper.alg_twist_standard_local_vanishing`); H1 of O(−d) is the H1
  state module, connecting classes map to the Laurent coefficient
  projection, and H1 is finite free of rank d − 1 over a nontrivial base
  (`Paper.alg_twist_H1_noetherian`, `Paper.alg_twist_H1_connecting_projection`,
  `Paper.alg_twist_H1_linear`, `Paper.alg_twist_H1_finrank`); cohomology above
  degree one vanishes (`Paper.alg_twist_higher_vanishing`). Over an arbitrary
  base, the H1 comparison keeps local H1 vanishing on both charts as a
  hypothesis.
- **Degree zero on every finite vertex set.** `CechTwistZeroCocycles.lean`,
  `CechTwistChartMatching.lean`, `CechZeroStatePiece.lean`,
  `VertexProjectiveTwistZeroCycles.lean` and `VertexProjectiveTwistH0States.lean`
  identify the global sections of every nonpositive multi-twist with the
  degree-zero cocycles of the coefficient complex, through chart restrictions
  and frame coefficients, with Mathlib's sheaf gluing as the inverse. Hence H0
  is the degree-zero state piece: finite free, of rank one exactly at the zero
  twist over a nontrivial base, equal to R at the zero twist, and zero with
  any strictly negative factor (`Paper.alg_vertex_twist_H0_states`,
  `Paper.alg_vertex_twist_H0_states_representative`,
  `Paper.alg_vertex_twist_H0_states_inverse`,
  `Paper.alg_vertex_twist_H0_finrank`, `Paper.alg_vertex_twist_H0_zero`,
  `Paper.alg_vertex_twist_H0_negative_vanishing`). No Noetherian hypothesis is
  used. For the empty vertex set, H0 is R over every commutative base
  (`VertexProjectiveTwistEmptyCohomology.lean`).
- **The cubical complex of sections.** `CechCubicalBoundary.lean`,
  `CechTwistRestrictionMonomials.lean`, `CechCubicalFaceDifferential.lean`,
  `SchemeModuleOpenRestrictions.lean`, `VertexProjectiveTwistCubicalSections.lean`
  and `VertexProjectiveTwistCubicalComparison.lean` define the cubical cochains
  of sections with the left-minus-right restriction differential. For
  nonpositive multi-twists, multiplying degree q by (−1)^q gives a chain
  equivalence with the coefficient tensor complex (a right-chart exponent k
  becomes −d(v)−k on the overlap); it preserves overlap degree, and a cocycle
  is a boundary exactly when its state projection vanishes
  (`Paper.alg_vertex_twist_cubical_chain_differential`,
  `Paper.alg_vertex_twist_cubical_chain_degree`,
  `Paper.alg_vertex_twist_cubical_boundary_criterion`).
- **Bounds and top degree.** Over a Noetherian base, positive local Ext
  groups of every multi-twist vanish on every finite chart intersection
  (`VertexProjectiveTwistCechAcyclic.lean`), global H^j vanishes for j > |V|
  (`SheafCohomologyBinaryCover.lean`, `VertexProjectiveTwistHigherCohomology.lean`),
  and top cohomology H^{|V|} is the restriction cokernel for any finite vertex
  type and any pivot vertex (`VertexProjectiveTwistLabelledTopCohomology.lean`,
  `VertexProjectiveTwistTopLinear.lean`).
- **Two vertices.** For every integral two-vertex twist over a Noetherian
  base, H2 is the signed quotient of rectangular sections by the four face
  restrictions (`VertexProjectiveTwistTwoRectangleCohomology.lean`,
  `VertexProjectiveTwistTwoRectangleCoordinates.lean`;
  `Paper.alg_vertex_two_twist_H2_rectangle`,
  `Paper.alg_vertex_two_twist_H2_rectangle_representative`). Each row H1 is its
  coefficient cokernel, and for nonpositive twists the one-factor Laurent
  state module over the first face ring; the first-direction restrictions act
  at every gap by m ↦ m on the left and m ↦ −d(0)−m on the right
  (`VertexProjectiveTwistRowH1.lean`, `VertexProjectiveTwistRowRestriction.lean`,
  `CechTwoRowCoordinates.lean`, `CechTwoRowStates.lean`,
  `VertexProjectiveTwistRowStates.lean`,
  `VertexProjectiveTwistRowStateFormula.lean`;
  `Paper.alg_vertex_two_row_H1_coefficients`,
  `Paper.alg_vertex_two_row_H1_states`,
  `Paper.alg_vertex_two_row_H1_representative`,
  `Paper.alg_vertex_two_row_H1_gap`,
  `Paper.alg_vertex_two_row_H1_restrict_pointwise`). Row sections and row H0
  are the one-factor H0 states over the first face ring, without Noetherian
  hypothesis (`VertexProjectiveTwistRowH0.lean`;
  `Paper.alg_vertex_two_row_H0_sections`, `Paper.alg_vertex_two_row_H0_states`).
  For nonpositive twists, H2 is the degree-two state piece, finite free of
  rank (d(0)−1)(d(1)−1) with natural subtraction, and H2(−2,−2) = R with its
  (−1,−1) Laurent representative
  (`VertexProjectiveTwistFaceCoordinatesAt.lean`,
  `CechTwoRectangleBoundary.lean`, `CechTwoRectangleSigns.lean`,
  `CechTwoTopState.lean`,
  `CechTwoTopStatePiece.lean`, `CechMinusTwoBasis.lean`,
  `VertexProjectiveTwistTwoH2States.lean`, `VertexProjectiveTwistTwoH2Piece.lean`,
  `VertexProjectiveTwistTwoH2Generator.lean`;
  `Paper.alg_vertex_two_twist_H2_piece`,
  `Paper.alg_vertex_two_twist_H2_piece_inverse`,
  `Paper.alg_vertex_two_twist_H2_piece_positive`,
  `Paper.alg_vertex_two_twist_H2_finrank_nonpositive`,
  `Paper.alg_vertex_two_twist_H2_minus_two_representative`). H1 is the
  degree-one state piece, through the row restriction kernel when d(1) > 0
  and through the outer connecting map when d(1) = 0; it is finite free of
  rank (if d(0)=0 then d(1)−1 else 0) + (if d(1)=0 then d(0)−1 else 0)
  (`VertexProjectiveTwistTwoH1Kernel.lean`, `CechTwoRowH1Kernel.lean`,
  `CechTwoRowKernelStates.lean`, `CechTwoMiddleStatePiece.lean`,
  `VertexProjectiveTwistTwoH1States.lean`,
  `VertexProjectiveTwistRowH0Restriction.lean`, `CechTwoBaseH1.lean`,
  `VertexProjectiveTwistTwoH1ZeroSecond.lean`, `VertexProjectiveTwistTwoH1All.lean`;
  `Paper.alg_vertex_two_twist_H1_state_kernel`,
  `Paper.alg_vertex_two_twist_H1_states`,
  `Paper.alg_vertex_two_twist_H1_projection`,
  `Paper.alg_vertex_two_twist_H1_zero_second_connecting`,
  `Paper.alg_vertex_two_twist_H1_zero_second_inverse`,
  `Paper.alg_vertex_two_twist_H1_finrank`,
  `Paper.alg_vertex_two_twist_H1_minus_two_zero_representative`). Strictly
  negative twists have cohomology only in degree two, and a factor −1 kills
  all cohomology, for example for (−1,−2)
  (`VertexProjectiveTwistTwoNegativeCohomology.lean`;
  `Paper.alg_vertex_two_twist_H1_negative_vanishing`,
  `Paper.alg_vertex_two_twist_negative_concentrated`,
  `Paper.alg_vertex_two_twist_minus_one_minus_two_acyclic`,
  `Paper.alg_vertex_two_twist_one_acyclic_nonpositive`). The nonpositive cases
  are also covered by the next item.
- **All degrees on every finite vertex set.** `FreeAbelianCechResolution.lean`
  and `FreeAbelianCechSections.lean` adapt only the tuple extra-degeneracy,
  positive exactness and section-differential arguments from the pinned
  OpenAI Math sources in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md); with
  `FreeAbelianCechAugmentation.lean`, `FreeAbelianCechAcyclic.lean`,
  `FiniteCechActualCohomology.lean` and `VertexProjectiveTwistTupleCech.lean`,
  the tuple Čech Hom complex of the chart cover computes H^{n+1} for n ≥ 0,
  for every finite V, integral multi-twist and small Noetherian base
  (`Paper.alg_vertex_twist_tuple_cech_actual`,
  `Paper.alg_free_cech_section_differential`,
  `Paper.alg_free_cech_augmentation_exact`). The bounded cubical cell complex
  of a binary cover is an exact augmented complex of finite biproducts of
  free sheaves (for twist sheaves its relative acyclicity follows from affine
  vanishing on the face intersections through Mathlib's
  `Ext.biproductAddEquiv`); its Hom complex consists of face sections with
  the signed endpoint-restriction differential, and it computes H^{n+1} in the
  same range
  (`CechCubicalCellInterval.lean`, `CechCubicalCellProduct.lean`,
  `CechCubicalCellBoundary.lean`, `CechCubicalCellMaps.lean`,
  `CechCubicalCellDegree.lean`, `CechCubicalCellSubface.lean`,
  `CechCubicalCellComplex.lean`, `BinaryCoverCellAvailability.lean`,
  `BinaryCoverCellComplex.lean`, `BinaryCoverCellSheaf.lean`,
  `BinaryCoverCellFree.lean`, `BinaryCoverCellSections.lean`,
  `BinaryCoverCellEndpoint.lean`, `BinaryCoverCellBoundary.lean`,
  `BinaryCoverCellSectionDifferential.lean`, `SchemeModuleCellSections.lean`,
  `BinaryCoverCellAcyclic.lean`, `BinaryCoverCellAugmentation.lean`,
  `BinaryCoverCellAugmentedSheaf.lean`, `BinaryCoverCellCoverAugmentation.lean`,
  `FiniteCubicalActualCohomology.lean`, `VertexProjectiveTwistCellAcyclic.lean`,
  `VertexProjectiveTwistCellCohomology.lean`;
  `Paper.alg_vertex_twist_cell_actual`,
  `Paper.alg_cubical_cell_section_differential`). Combined with the cubical
  chain equivalence and the state contraction
  (`VertexProjectiveTwistCubicalComponent.lean`,
  `VertexProjectiveTwistCellNative.lean`,
  `VertexProjectiveTwistCellCoefficients.lean`,
  `VertexProjectiveTwistCellStates.lean`,
  `VertexProjectiveTwistCellStateCohomology.lean`,
  `VertexProjectiveTwistStateCohomology.lean`,
  `VertexProjectiveTwistCohomologyRanks.lean`): for every finite V,
  nonpositive twist −d and small Noetherian base, H^j is the degree-j state
  piece for every j ≥ 0; it is finite free, concentrated in j equal to the
  number of nonzero entries of d, of rank ∏_v φ(d(v)) over a nontrivial base,
  and zero in every degree if some d(v) = 1
  (`Paper.alg_vertex_twist_cohomology_states`,
  `Paper.alg_vertex_twist_cohomology_states_representative`,
  `Paper.alg_vertex_twist_cohomology_states_inverse`,
  `Paper.alg_vertex_twist_cohomology_finrank`). In degree zero this agrees
  with the comparison above, which needs no Noetherian hypothesis
  (`Paper.alg_vertex_state_equiv_cell`). The cubical complex is not the
  tuple-indexed Čech complex.

### Products on cohomology and the Tor isomorphism

- **Twist pairing.** The tensor sheaf of two integral multi-twists is the sum
  twist, by gluing the chart frames (`Paper.alg_vertex_twist_tensor_add`). The
  section pairing preserves restrictions, the chart and mixed-face
  coefficient products and the geometric base action, over every small
  commutative ring; through the integer tensor and sheafification it extends
  uniquely to a map of abelian sheaves.
- **Cell diagonal and cup cochains.** For every finite vertex set the
  cubical cell complex has a diagonal, a chain map from the cell sheaf
  complex to its pair complex with the Koszul crossing signs of the fixed
  vertex enumeration, preserving face availability, degree and augmentation
  (`Paper.alg_cubical_cell_sheaf_diagonal`). The pair complex is Mathlib's
  standard tensor totalization of the cell complex, both for module
  presheaves and for the cell sheaf complexes in the abelian category used by
  Ext (`Paper.alg_cubical_cell_tensor_pair_complex`,
  `Paper.alg_cubical_cell_actual_tensor_pair`). With the twist pairing the
  diagonal gives biadditive cup cochains with the signed Leibniz rule, which
  descend to the Hom quotients in every degree. The cup has an explicit
  mixed-face formula for all integral twists
  (`Paper.alg_vertex_twist_cell_cup_face`); for nonpositive twists it is the
  signed tensor coefficient product `chainCup` on every representative
  (`Paper.alg_vertex_twist_cell_cup_coefficient`) and induces the state
  product on classes (`Paper.alg_vertex_twist_cell_quotient_cup_states`). None
  of these statements needs a Noetherian hypothesis.
- **From cochains to Ext.** The comparison of Hom quotients with Ext is
  natural in the resolution along every supplied augmentation-preserving
  chain map (`Paper.alg_augmented_resolution_source_ext`; in degree zero
  without acyclicity, `Paper.alg_cubical_geometric_actual_zero_source`). The
  tensor square of the cell resolution is exact and, over a Noetherian base,
  also computes cohomology; the geometric cup and the tensor cocycle give the
  same class (`Paper.alg_vertex_tensor_actual`,
  `Paper.alg_vertex_tensor_cup_actual`). In the derived category every cup class is the roof of the tensor product of
  its two input maps (`Paper.alg_vertex_native_cup_roof`,
  `Paper.alg_native_cubical_cup_actual_roof`, with the factor (−1)^(ij)). The
  derived roof of an n-cocycle is its iterated Yoneda representative times
  (−1)^(n(n+1)/2) (`Paper.alg_native_ext_all_yoneda`,
  `Paper.alg_native_yoneda_sign`), and over a Noetherian base it is a linear
  equivalence for the geometric action
  (`Paper.alg_vertex_native_all_linear_apply`). The denominator of these
  roofs is the tensor of the two input augmentations
  (`Paper.alg_negative_augmentation_tensor`,
  `Paper.alg_input_tensor_denominator`,
  `Paper.alg_native_cup_roof_input_tensor`); identifying the terminal sheaf
  with the tensor unit, the terminal diagonal is the inverse left unitor
  (`Paper.alg_terminal_diagonal_unit`, `Paper.alg_native_cup_roof_unit_tensor`).
- **The standard product.** The standard external roof of two cocycles is
  built from the unit identification, the inverse left unitor, the inverse
  tensor of the two input augmentations and Mathlib's shifted tensor pairing;
  it is the derived cup roof times (−1)^(ij)
  (`Paper.alg_standard_tensor_roof_native`). The resulting product on
  Ext-defined cohomology is computed by every choice of representatives
  (`Paper.alg_standard_class_product_representative`). With the iterated
  Yoneda normalization of inputs and output, the geometric cup is exactly
  this standard product: the triangular normalization signs and the Koszul
  sign cancel, and no sign is inserted by hand
  (`Paper.alg_yoneda_cup_standard`; for vertex twists
  `Paper.alg_vertex_standard_cup_yoneda`, bilinear for the geometric action
  over a Noetherian base). The product is natural for compatible pairings
  (`Paper.alg_standard_class_cup_natural`) and, along a supplied
  augmentation-preserving chain map between the cell complexes of two binary
  covers, the products computed through the two covers agree
  (`Paper.alg_standard_class_cup_source`). Such comparison maps exist for any
  two binary cover families through their concatenation, by forgetting
  directions (l, r ↦ 1, e ↦ 0, with explicit relabelling signs;
  `Paper.alg_cover_refinement_augmentation`), so on (ℙ¹)^V every binary cover
  family with affine cell opens computes the same product
  (`Paper.alg_vertex_cup_cover_independent`, `Paper.alg_vertex_cup_reindex`).
  Independence from arbitrary resolutions is not formalized.
- **Product laws.** For nonpositive twists the state coordinates of
  cohomology are injective in every degree, and the state coordinate of the
  standard product is the state product
  (`Paper.alg_vertex_actual_state_standard_cup`). The Čech chain product of
  the state complex is strictly associative, and the state product is
  associative and graded commutative with sign (−1)^(ij), with explicit
  transport of twists (`Paper.alg_state_cup_assoc`, `Paper.alg_state_cup_comm`).
  Hence the product on cohomology of nonpositive twists is associative,
  graded commutative and unital (`Paper.alg_vertex_product_assoc`,
  `Paper.alg_vertex_product_comm`, `Paper.alg_vertex_product_unit_left`); the
  unit is the global section equal to the constant one on every chart
  (`Paper.alg_vertex_product_unit_section`). The product is defined
  geometrically; only its laws are read off through the injective state
  coordinates. The Alexander–Whitney chain cup is not claimed to be
  commutative. The state product orders the vertices by `Fintype.equivFin V`:
  its absolute signs depend on this enumeration, while the reverse-order
  sign, associativity and unit laws do not, and the state coordinates of
  cohomology use the same enumeration. Examples: for twists (−2,0) and (0,−2)
  the two orders of the degree-one generators differ by −1, detected over ℤ
  (`Paper.alg_state_cup_example_reverse_sign`,
  `Paper.alg_state_cup_example_sign_detected`); for three vertices the two
  bracketings of the degree-one generators agree and give the Laurent gap
  state of twist (−2,−2,−2) (`Paper.alg_state_cup_example_three_assoc`,
  `Paper.alg_state_cup_example_three_generator`).
- **Exterior side.** A ring-generic state product of edge states reproduces
  the Čech formula of the Tor product at the incidence coefficient ring,
  vanishes on edge sets sharing an edge, carries the edge shuffle sign and
  (−1)^(|S| deg T) otherwise, is associative and unital, and commutes with
  change of coefficient ring (`Paper.alg_state_exterior_cup_tor`,
  `Paper.alg_state_exterior_cup_single`, `Paper.alg_state_exterior_cup_assoc`,
  `Paper.alg_state_exterior_cup_unit_left`,
  `Paper.alg_state_exterior_cup_ring_change`). The edge shuffle sign is the
  sign of Mathlib's disjoint-union permutation, and the edge exterior space is
  Mathlib's exterior algebra on the free module of edges
  (`Paper.alg_shuffle_sign_perm`, `Paper.alg_exterior_algebra_wedge`). The
  orientation line of an edge is the second exterior power of the functions
  on its endpoints, free of rank one for distinct endpoints, and state
  orientation generators multiply by the shuffle sign
  (`Paper.alg_orientation_line_rank`, `Paper.alg_state_orientation_mul`). The
  cohomology of the exterior bundle (the biproduct model of "Differences in
  hypotheses"; `Paper.alg_exterior_bundle_one` in degree one) splits as the
  product of the cohomology of its summands, is the product of state pieces
  over a Noetherian base, and vanishes above degree q
  (`Paper.alg_exterior_bundle_cohomology`, `Paper.alg_exterior_bundle_states`,
  `Paper.alg_exterior_bundle_vanishing`). Its product is (−1)^(q·j) times the
  standard cup with the exterior pairing (summand twist products with the edge
  shuffle sign, zero on shared edges); its state vector is the state product,
  and it is associative and unital (`Paper.alg_exterior_product_states`,
  `Paper.alg_exterior_product_assoc`, `Paper.alg_exterior_product_unit_left`).
  On every open inside a standard chart, the wedge map from Mathlib's exterior
  power of the sections of the dual edge bundle is bijective, and the sheaf
  pairing is exterior multiplication, in every degree including zero
  (`Paper.alg_exterior_chart_wedge_bijective`,
  `Paper.alg_exterior_chart_wedge_mul`, `Paper.alg_exterior_pairing_bridge`,
  `Paper.alg_exterior_pairing_wedge`,
  `Paper.alg_exterior_chart_wedge_bijective_all`).
- **The Tor isomorphism.** The full state vector of the standard Tor product
  is the state product, and the Tor unit has the unit state
  (`Paper.alg_tor_product_states`, `Paper.alg_tor_unit_state`). Consequently
  (`Paper.alg_tor_isomorphism`, `Paper.alg_tor_isomorphism_mul`,
  `Paper.alg_tor_isomorphism_one`, `Paper.alg_tor_isomorphism_state`), for
  p ≤ q the internal degree-q piece of Tor_p over the coefficient origin is
  ℂ-linearly isomorphic to H^{q−p} of the q-th exterior bundle, sending the
  standard Tor product to the exterior product and the unit to the unit. The
  two products are defined independently and compared through injective
  state vectors. For graph maps fixing the vertices the isomorphism is
  natural: for edge relabelings the exterior side is the signed biproduct
  reindexing (`Paper.alg_tor_isomorphism_natural`,
  `Paper.alg_relabel_exterior_product`); per-edge sign changes scale the
  summand of S by ∏_{e∈S} ε_e (`Paper.alg_tor_isomorphism_sign`); for edge
  maps the summand of S goes to that of φ(S) with the wedge sign when φ is
  injective on S and to zero otherwise
  (`Paper.alg_tor_isomorphism_edge_map_natural`); signed edge maps compose
  the two (`Paper.alg_tor_isomorphism_signed_edge_map_natural`). The Tor map of an edge map
  is `derivedRingMap` along the coefficient ring map: a lift from a projective
  resolution to the restricted (exact, not projective) resolution, followed by
  the one-way map k ⊗_R f^*Q → k ⊗_{R'} Q (`Paper.alg_derived_ring_map_eq`).

## Correspondence table

Every label of the paper and of its supplementary material, in the order
of the article version.

### §1 Introduction

| Label | Kind | Lean | Status |
|---|---|---|---|
| `sec:introduction` | section | — | Section |
| `intro:state-sum` | equation | `phi`, `Multigraph.wt`, `Multigraph.Q` | Definition |
| `thm:structure` | Theorem 1.1 | `Paper.thm_structure_N_eq_Q`, `Paper.thm_structure_betti`, `Paper.thm_structure_theta`, `Paper.thm_structure_omega`, `Paper.thm_structure_dim`, `Paper.alg_normal_domain`, `projectiveDimension_incidenceRing` | Proved (every clause, see the table of Theorem 1.1 above; naturality covers general non-contracting graph maps, `Paper.alg_tor_isomorphism_graph_map_natural`. The derived global sections of the universal Koszul complex in Theorem 3.4 are a separate statement, see `alg:resolution`) |
| `intro:betti` | equation | `betti`, `Paper.thm_structure_betti`, `card_incBigradedBasis`, `finrank_incidenceTorInternalPiece` | Proved for the chart-intersection model (the natural coefficient grading, homogeneous minimal free resolution, exactness in every internal degree and actual graded Tor dimensions β_{p,q}) |
| `intro:tor` | equation | `Paper.alg_tor_isomorphism`, `Paper.alg_tor_isomorphism_mul`, `Paper.alg_tor_isomorphism_one`, `incidenceTorInternalEquivState`, `finrank_incidenceTorInternalPiece`, `Paper.alg_tor_product` | Proved (bigraded algebra isomorphism with actual cohomology of the exterior bundle, modelled as the biproduct of twist sheaves identified chart-wise with the exterior power; see the row of Theorem 1.1 above) |
| `intro:hilbert` | equation | `Paper.alg_hilbert_theta`, `Paper.alg_universal_hilbert` | Proved (actual Hilbert series of the natural chart-graded ring) |
| `thm:real` | Theorem 1.2 | `Paper.thm_real_i`, `Paper.thm_real_ii_sector`, `Paper.thm_real_ii_lower`, `Paper.thm_real_ii_strong`, `Paper.thm_real_ii_min` | Proved (the exhaustion of (i) by Q simple roots, the analytic power-map charts, the boundary local algebra as the analytic special fiber of the state chart, and all of (ii); see the table of Theorem 1.2 above) |
| `intro:power-map` | equation | `Paper.sf_normal_form` | Proved |
| `intro:three-counts` | equation | `Paper.thm_real_ii_strong` | Proved |
| `intro:minimum` | equation | `Paper.thm_real_ii_min` | Proved |
| `intro:generator-real-bridge` | equation | `Paper.intro_generator_real_bridge`, `Paper.alg_module_generator_number`, `Paper.alg_module_generator_min_real_count` | Proved for the chart-intersection model (intrinsic module minimum, homogeneous generators, sharp cycle criterion, and equality with the real minimum) |
| `intro:related` | section | — | Section (no formal content) |

### §2 The admissible BP family and the generic degree

| Label | Kind | Lean | Status |
|---|---|---|---|
| `sec:degree` | section | `Degree/` | Section |
| `eq:bp-ratios` | equation | `cavity`, `totalField` | Definition |
| `eq:bp-update` | equation | `bpPoly`, `IsRationalFixedPoint`, `isFixedPoint_iff_isRationalFixedPoint` | Proved (equivalence where the denominators are nonzero) |
| `eq:admissibility` | equation | `Admissible`, `IsAdmissibleSolution` | Definition |
| `ex:triangle-admissible` | Example 2.1 | `Paper.ex_triangle_admissible`, `Paper.ex_triangle_T_cube`, `Examples/TriangleAdmissible.lean` | Proved (4 rational solutions, 2 admissible = N(C₃), F = −1 at the mixed solutions, x± ≠ −1, the formula for T³; the generic dimension ν − 1 belongs to `supp:nonnormalizable-dim`) |
| `prop:bp-family` | Proposition 2.2 | `Paper.prop_bp_family` (counting form), `Paper.prop_bp_family_finite_etale`, `Paper.prop_bp_family_dominant`, `Paper.prop_bp_family_smooth`; `familyRing_isDomain`, `ringKrullDim_familyRing` | Proved (over ℂ[a, b][1/s] with s ≠ 0 the family ring is finite, free of rank N(G) = Q(G) and étale, with exactly Q(G) simple admissible solutions over every point of D(s); smoothness, domain and dimension m + n of the total space) |
| `eq:belief-cover` | equation | `normalization_identity`, `edge_marginal_eq`, `familyRingEquivBeliefRing`, `beliefRing_finite`, `Paper.eq_belief_cover_finite_etale` | Proved (ring isomorphism with the belief coordinates; the belief ring is finite, free of rank 2^m and étale over the belief base ring, as m adjoined square roots of units; the transfer of this algebra structure to the family ring through the ℂ-algebra isomorphism is not stated) |
| `eq:aux-coordinates` | equation | `auxA`, `auxBeta` | Definition |
| `eq:aux-edge` | equation | `field_eq_auxA` | Proved |
| `eq:aux-vertex` | equation | `auxBeta_eq` | Proved |
| `eq:aux-recovery` | equation | `reconY`, `isAdmissibleSolution_reconY`, `reconY_auxA` | Proved |
| `eq:edge-quadratic` | equation | `BP.edge_quadratic` | Proved |
| `lem:weak-boundary` | Lemma 2.3 | `Paper.lem_weak_boundary` (= `boundary_exclusion`), `boundary_exclusion_puiseux` | Proved (valuation form over any valued field) |
| `eq:spin-gauge` | equation | `isAuxSolution_flip` | Proved |
| `eq:generic-weak-line` | equation | `weakSystem`, `sP` | Definition |
| `eq:weak-limit-vertex` | equation | `VertexLimitEq`, `BP.card_vertexLimitEq` | Proved (φ(k) roots) |
| `eq:state-sum-degree` | equation | `card_limitSolutions` | Proved (Q(G) limit points) |
| `lem:unique-weak-lift` | Lemma 2.4 | `Paper.lem_unique_weak_lift` (= `exists_unique_lift`), `Paper.lem_unique_weak_lift_uniqueness` (= `BP.unique_of_cong`), `Paper.lem_unique_weak_lift_count`, `card_puiseuxSolutions` | Proved |
| `thm:degree` | Theorem 2.5 | `Paper.thm_degree`, `exists_generic_degree_eq_Q` | Proved |
| `cor:elementary-degree` | Corollary 2.6 | `Paper.cor_elementary_degree_disjUnion`, `_addLeaf`, `_subdivide`, `_forest`, `_unicyclic` | Proved |

### §3 The universal edge-incidence ring

| Label | Kind | Lean | Status |
|---|---|---|---|
| `sec:incidence` | section | `Incidence/` | Section |
| `alg:edge-bundles` | section | `nu`, `numComponents`, `tau`, `rho`, `dG`, `dG_add_rho`, `rho_eq_sum` | Definition (definitions and relations of ν, c, τ, ρ, d_G; X_G = (ℙ¹)^V and its integral twists and multi-twists as rank-one locally free quasicoherent sheaves with their frame transitions (`Paper.alg_twist_sheaf_rank_one`, `Paper.alg_twist_sheaf_locally_free`, `Paper.alg_twist_sheaf_quasicoherent`, `Paper.alg_twist_frame_transition`, `Paper.alg_twist_frame_coordinate`, `Paper.alg_vertex_twist_rank_one`, `Paper.alg_vertex_twist_locally_free`, `Paper.alg_vertex_twist_quasicoherent`, `Paper.alg_vertex_twist_pair_transition`); F_G^∨ and its exterior powers in the biproduct model, and the orientation lines (`Paper.alg_exterior_bundle_one`, `Paper.alg_orientation_line_rank`); the universal section is `Paper.alg_universal_koszul_complex`'s differential, and Z_G as a vector bundle belongs to `alg:incidence-vector-bundle`; the section's remark that changing the edge orientations or the edge order gives an isomorphic construction is the naturality under edge relabelings, `Paper.alg_tor_isomorphism_natural`) |
| `alg:first-page` | equation | `stateDim`, `IncResolutionBasis`, `CechProduct.contraction` | Definition (Ext-defined cohomology of the biproduct model of ∧^q F_G^∨, with the product (−1)^(q·j) times the standard cup with the exterior pairing; its state description is `Paper.alg_exterior_bundle_states`, and its identification with the Tor algebra is `Paper.alg_tor_isomorphism`) |
| `alg:state-cohomology` | Lemma 3.1 | `Paper.alg_state_cohomology`, `Paper.alg_vertex_twist_cohomology_states`, `Paper.alg_vertex_twist_cohomology_finrank`, `card_le_card_support_add_rho`, `exists_isContributing_card_eq`, `CechProduct.line`, `CechProduct.contraction` | Proved (the counts Σ wt(S) = Q, the bound 0 ≤ q − j ≤ ρ with its attainment, and the monomial contraction of the Čech complex (`Paper.alg_state_cohomology`); for every finite vertex set and nonpositive multi-twist −d over a Noetherian base, sheaf cohomology is the state piece in every degree, finite free, concentrated in the degree equal to the number of nonzero entries of d, of rank ∏_v φ(d(v)), and zero in every degree when some d(v) = 1 (`Paper.alg_vertex_twist_cohomology_states`, `Paper.alg_vertex_twist_cohomology_finrank`); with d = d_S this is the summand statement of the lemma. The dimension formula for E_1 is `Paper.alg_state_dimensions`. The supporting statements are listed in "Cohomology of twist sheaves" above) |
| `alg:state-dimensions` | equation | `Paper.alg_state_dimensions`, `Paper.alg_exterior_bundle_finrank`, `stateDim`, `sum_stateDim_eq_Q`, `stateDim_eq_zero_of` | Proved (dim H^j of the q-th exterior bundle is Σ_{|S|=q, v(S)=j} wt(S), with total Q(G); over every nontrivial Noetherian base the cohomology is free of that rank) |
| `alg:universal-incidence` | section | — | Section |
| `alg:coefficient-ring` | equation | `IncCoeffRing` | Definition (`Incidence/Ring.lean`) |
| `alg:incidence-scheme` | equation | `incidenceProjectiveZeroScheme`, `IncidenceProjectiveZeroChartRing`, `incidenceProjectiveZeroAffineCover` | Definition (independent closed zero scheme of the homogeneous edge equations in the actual projective product, with the prescribed full affine quotient charts) |
| `alg:universal-definition` | Definition 3.2 | `IncidenceRing`, `Paper.alg_universal_definition`, `Paper.alg_projective_zero_global_sections`, `Paper.alg_projective_zero_coefficient` | Definition (the chart-intersection ring and natural coefficient grading; its identification with actual global functions of the independent projective zero scheme preserves the geometric coefficient action) |
| `alg:incidence-vector-bundle` | Lemma 3.3 | `incidenceRing_finite`, `Paper.alg_incidence_projective_closed`, `Paper.alg_incidence_projective_zero_scheme`, `Paper.alg_incidence_projective_zero_charts`, `Paper.alg_projective_zero_global_sections` | Proved (finiteness over S_G; the closed embedding into the product of projective lines, the comparison with the independent homogeneous zero scheme, its quotient charts and its global functions; properness, including every base change (`Paper.alg_incidence_projective_proper`, `Paper.alg_incidence_proper_basechange`); the degree-zero part consists of the constants (`Paper.alg_degree_zero`); at chart level, the regular sequence, the rank-3m local trivialization and the surjective evaluation (`Paper.alg_vector_bundle_trivialization`); on chart overlaps, linear transition functions with the cocycle condition relating the chart trivializations of Z_G (`Paper.alg_vector_bundle_linear_transition`, `Paper.alg_vector_bundle_cocycle`). the glued evaluation map of sheaves of modules and its kernel sheaf K, free of rank 3m on every chart with these transitions (`Paper.alg_vector_bundle_evaluation_sheaf`, `Paper.alg_kernel_sheaf_chart`, `Paper.alg_kernel_sheaf_transition`). the sequence 0 → K → O^{4m} → F_G → 0 is short exact and splits on charts (`Paper.alg_kernel_sheaf_short_exact`).; Z_G is isomorphic over X_G to the total space of a rank-3m vector bundle, glued from Spec Sym of the kernel frames on the face cover with the transposed kernel transitions, compatibly with the zero sections and the maps to the coefficient space; the projection Z_G → X_G is defined through the glued incidence scheme, on charts by forgetting the coefficients (`Paper.alg_vector_bundle_total_space`, `Paper.alg_vector_bundle_total_space_projection`, `Paper.alg_vector_bundle_zero_section`, `Paper.alg_vector_bundle_coefficient`); Sym(K^∨) is used face by face in the kernel frames, not as a quasi-coherent sheaf of algebras) |
| `alg:resolution-section` | section | — | Section |
| `alg:universal-koszul` | equation | `Paper.alg_universal_koszul_complex`, `Paper.alg_universal_koszul_exact`, `Paper.alg_universal_koszul_chart_augmentation`, `Paper.alg_universal_koszul_cech_equiv` , `Paper.alg_universal_koszul_augmentation`, `Paper.alg_universal_koszul_cokernel`, `Paper.alg_universal_koszul_resolves`| Proved (the complex of sheaves with terms ∧^k F_G^∨ and the contraction with the universal section, d² = 0, exactness in negative degrees, and the augmentation ∧^0 ≅ 𝒪_Y → i_*𝒪_{Z_G} as a morphism of sheaves whose cokernel is i_*𝒪_{Z_G}, so that the complex resolves 𝒪_{Z_G} (a quasi-isomorphism, `Paper.alg_universal_koszul_resolves`); its Čech–Koszul model is the total complex of the resolution. The internal grading S_G(−q) is carried by the Čech model, not by the complex of sheaves) |
| `alg:resolution` | Theorem 3.4 | `incResolutionDifferential`, `incidenceRing_projectiveDimension`, `projectiveDimension_incidenceRing`, `Paper.alg_resolution_derived_vanishing`, `Paper.alg_resolution_derived_h0`, `Paper.alg_free_terms`, `Paper.alg_resolution_derived_h0_augmentation` | Proved (the free resolution, exactness, gluing in degree zero, minimality at the coefficient origin, projective dimension ρ, compatibility with the natural grading with exactness in every internal degree, the internal Tor pieces of dimension β_{p,q} and the Tor algebra isomorphism `alg:tor-isomorphism` are proved; the free terms are H^{q−p}(X_G, ∧^q F_G^∨) ⊗ S_G(−q) as graded S_G-modules (`alg:free-terms`, `Paper.alg_free_terms`); the derived global sections of the universal Koszul complex, defined as hypercohomology in the derived category of abelian sheaves, vanish outside degree zero and are 𝒰_G in degree zero, S_G-linearly (`Paper.alg_resolution_derived_vanishing`, `Paper.alg_resolution_derived_h0`), deduced from the exactness of the resolution through the Čech–Koszul model; this identification of H^0 agrees with the sheaf route through the augmentation K_G → i_*𝒪_{Z_G}[0] and Γ(Z_G, 𝒪) ≅ 𝒰_G (`Paper.alg_resolution_derived_h0_augmentation`)) |
| `alg:free-terms` | equation | `IncResolutionBasis`, `incResolutionDegree`, `incResolutionInternalPiece`, `card_incBigradedBasis` , `Paper.alg_free_terms`, `Paper.alg_free_terms_internal`, `Paper.alg_free_terms_residue`| Proved (free terms in both degrees, with homogeneous coefficient pieces shifted by the edge count, and an internally homogeneous differential; the p-th free term is S_G-linearly isomorphic to ⊕_{p ≤ q ≤ m} S_G ⊗_ℂ H^{q−p}(X_G, ∧^q F_G^∨), with the actual Ext-defined sheaf cohomology, compatibly with the internal grading S_G(−q) (`Paper.alg_free_terms`, `Paper.alg_free_terms_internal`); the generator of a state goes to 1 ⊗ the exterior class of the same state, so the isomorphism depends on the free basis, and its reduction modulo (S_G)_+ is the base-change isomorphism, built without state bases, applied to the Tor class (`Paper.alg_free_terms_residue`)) |
| `alg:betti-state-sum` | equation | `betti` | Definition (the state sum on the right side) |
| `alg:tor-isomorphism` | equation | `Paper.alg_tor_isomorphism`, `Paper.alg_tor_isomorphism_mul`, `Paper.alg_tor_isomorphism_one`, `incidenceTorInternalEquivState`, `Paper.alg_tor_product` | Proved (bigraded ℂ-linear isomorphism of the Tor pieces with cohomology of the exterior bundle, preserving products and units; the exterior bundle is the finite biproduct of the twist sheaves L(−d_S), identified chart-wise with the exterior power of the dual edge bundle in every degree, its product pairing being exterior multiplication; the cup product is the standard product of the cubical cell resolution; for q < p the Tor piece is zero (`Paper.alg_tor_piece_eq_bot_of_lt`); it is built through state bases and, independently, by the base change of the Čech model at the coefficient origin, and the two constructions are proved equal (`Paper.alg_zero_base_change_eq`); naturality is the row `alg:functoriality`) |
| `alg:transferred-differential` | equation | `IncidencePerturbation.Contraction.transfer`, `incResolutionDifferential` | Proved (the actual differential by finite perturbation, square zero, homological degree) |
| `alg:zero-base-change` | equation | `Paper.alg_zero_base_change_model`, `Paper.alg_zero_base_change_koszul`, `Paper.alg_zero_base_change_tor`, `Paper.alg_zero_base_change_sheaf`, `Paper.alg_zero_base_change_iso`, `Paper.alg_zero_base_change_eq`, `Paper.alg_zero_base_change_derived`, `Paper.alg_zero_base_change_derived_exterior`, `Paper.alg_zero_base_change_pair_tensor`, `Paper.alg_zero_base_change_cech_product`, `Paper.alg_zero_base_change_derived_product` | Proved (the free resolution F⁻ and the Čech–Koszul total complex are homotopy equivalent over S_G through the perturbation data, and base change to ℂ gives an isomorphism in D(ℂ) between ℂ ⊗ F⁻, whose cohomology is Mathlib's Tor, and the Čech complex C₀ of ⊕_q ∧^q F_G^∨ on X_G over ℂ, whose cohomology is the actual sheaf cohomology; no flatness is used. On cohomology it induces `Paper.alg_tor_isomorphism`, every state class going to the same state with coefficient +1. The derived products: the Čech–Koszul product ∪₀ is a chain map C₀ ⊗ C₀ → C₀ out of Mathlib's monoidal tensor product of complexes (the Leibniz rule with the signs of `ComplexShape.up ℤ`), the specialized standard Tor product is a chain map (ℂ ⊗ F⁻) ⊗ (ℂ ⊗ F⁻) → ℂ ⊗ F⁻ through the identification of the zero-differential pair model of states with the tensor product of the state model with itself, and the derived isomorphism is multiplicative for them, as a commutative square in D(ℂ) out of the tensor product; on cohomology this square is `Paper.alg_zero_base_change_derived_product_cohomology`. The right side RΓ(X_G, ⊕_q ∧^q F_G^∨[q]) is represented by its Čech model C₀, and the products on the derived tensor products by the tensor product of complexes over the field ℂ, where every complex is flat) |
| `alg:total-betti` | Corollary 3.5 | `Paper.alg_total_betti`, `sum_finrank_incidenceTor` | Proved (the state-sum total and the total dimension of actual derived specialization both equal Q) |
| `alg:bp-total-betti` | equation | `Paper.alg_total_betti` | Proved (same) |
| `alg:cm-section` | section | — | Section |
| `alg:normal-cm` | Proposition 3.6 | `Paper.alg_normal_domain`, `ringKrullDim_incidenceRing`, `Paper.alg_cohenMacaulay` | Proved for the chart-intersection ring (normal Noetherian domain of dimension d_G; every maximal localization has depth and dimension d_G) |
| `alg:functoriality-section` | section | — | Section |
| `alg:functoriality` | Proposition 3.7 | `Paper.alg_relabel_incidence`, `Paper.alg_tor_isomorphism_natural`, `Paper.alg_signed_relabel_chart`, `Paper.alg_tor_isomorphism_signed_natural`, `Paper.alg_edge_map_incidence`, `Paper.alg_tor_isomorphism_edge_map_natural`, `Paper.alg_vertex_relabel_incidence`, `Paper.alg_vertex_relabel_tor_state`, `Paper.alg_disjoint_union_tensor`, `Q_disjUnion` | Proved (graph maps fixing the vertices: edge relabelings, orientation signs ε_φ on them, and non-injective edge maps induce incidence ring maps compatible with the coefficient ring maps, Tor maps derived from the ring maps that preserve products, units, identities and composition, and natural Tor isomorphisms; signed edge maps combine the signs with non-injective edge maps; vertex bijections: incidence and Tor isomorphisms with the Koszul sign of the vertex permutation; vertex maps identifying vertices: incidence ring maps and Tor maps preserving products, units, edge-set components and internal degree, zero on colliding states in every degree, with the degree-zero behaviour on the cycle-compatibility algebra; 𝒰_{G⊔H} ≅ 𝒰_G ⊗ 𝒰_H with coefficient, symmetry, associativity and unit compatibilities. vertex bijections also satisfy the naturality square, through the transport of the twist sheaves and the multi-twist state formula. For maps identifying vertices the Tor state formula on non-colliding states, the geometric pullback and the naturality square on colliding states are proved. The naturality square for maps identifying vertices is proved through the multi-twist state formula for the pullback (`Paper.alg_tor_isomorphism_vertex_map_natural`). General graph maps combine these with identity and composition laws, independence of the factorization and the naturality square (`Paper.alg_tor_isomorphism_graph_map_natural`). The incidence ring maps are graded and the disjoint-union isomorphism respects the grading (`Paper.alg_graph_map_graded`, `Paper.alg_disjoint_union_graded`); the numerical fact that Q of a disjoint union is the product is `Q_disjUnion`) |
| `alg:cycle-product` | Proposition 3.8 | `Paper.alg_cycle_algebra` (= `incidenceQuotientEquivCycleAlgebra`), `Paper.alg_cycle_algebra_tor` (= `cycleAlgebraEquivTor`), `Paper.alg_cycle_algebra_grading`, `Paper.alg_cycle_algebra_square`, `Paper.alg_cycle_product`, `betti_zero_eq_card`, `card_cycleCollections` | Proved (graded ℂ-algebra isomorphism U_G/(S_G)_+U_G ≅ ℂ[z_C]/(z_C z_D : V(C)∩V(D)≠∅), deg z_C = \|C\|, also with Tor_0 and its standard product; simple cycles are the minimal nonempty Eulerian edge sets, so 2-cycles on parallel edges are included; z_C² = 0; the product of vertex-disjoint cycle classes is ± the class of the union, the sign depending on the vertex enumeration of the state product) |
| `alg:cycle-algebra` | equation | `Paper.alg_cycle_algebra` | Proved |
| `alg:generator-real-bridge` | Corollary 3.9 | `Paper.alg_module_generator_number`, `Paper.alg_module_generators_minimal`, `Paper.alg_module_generators_homogeneous`, `Paper.alg_module_generator_degrees`, `Paper.alg_module_generator_cycles`, `Paper.alg_module_generator_bound`, `Paper.alg_module_generator_sharp`, `Paper.alg_module_generator_min_real_count` | Proved for the chart-intersection model (Mathlib's intrinsic minimum among generating sets, the homogeneous minimal family, its degree counts, cycle formula, bound, exact sharpness criterion and real minimum comparison) |
| (table: triangle, K₄, bowtie) | table | `Paper.alg_generator_table`, `Paper.alg_module_generator_table`, `Examples.bowtie_union` | Proved for the chart-intersection model (intrinsic module generator counts 2, 8 and 3) |
| `alg:polynomials-section` | section | — | Section |
| `alg:omega-definition` | equation | `fGen`, `thetaGen`, `thetaTwoI`, `thetaGen_two_I`, `omega`, `one_sub_pow_mul_thetaTwoI` | Proved |
| `alg:omega-reduced` | equation | `omegaTilde`, `compOmega`, `thetaTwoI_eq_omegaTilde`, `thetaTwoI_compGraph_of_isTreeComp` | Proved |
| `alg:hilbert` | Proposition 3.10 | `Paper.alg_hilbert`, `Paper.alg_hilbert_theta`, `Paper.alg_universal_hilbert`, `Paper.alg_hilbert_reduced`, `Paper.alg_linear_artin_exists`, `Paper.alg_artin_hilbert`, `Paper.alg_artin_length`, `Paper.alg_artin_parameter_open`, `Paper.alg_artin_parameters_regular` | Proved (the Hilbert series and its θ, ω and ω̃ formulas; on the nonempty Zariski-open set of length-d_G coefficient tuples with finite-dimensional quotient, every tuple is a regular sequence with quotient Hilbert series ω̃_G and dimension ω̃_G(1)) |
| `alg:theta-numerator` | equation | `thetaTwoI_eq_betti`, `incidenceHilbertSeries_numerator` | Proved (actual graded Betti numbers and actual Hilbert numerator) |
| `alg:universal-hilbert` | equation | `Paper.alg_universal_hilbert` | Proved (the Hilbert series is defined from the dimensions of the natural ring components) |
| `alg:artin-hilbert` | equation | `Paper.alg_artin_hilbert`, `Paper.alg_artin_length` | Proved for every homogeneous linear regular sequence of length d_G in the actual chart-intersection ring; such coefficient sequences exist (`Paper.alg_linear_artin_exists`) |
| `alg:k4-section` | section | `Paper.alg_k4`, `Paper.alg_k4_artin_exists`, `Paper.alg_k4_generator_products` | Proved (for the chart-intersection model: the numerical identities, the naturally graded resolution, the Hilbert series, and linear regular Artin quotients of dimension 30 on the whole open parameter locus; the 8 minimal generators (unit, four triangles, three squares) and the vanishing of all products of two nonunit generator classes in 𝒰_{K₄}/S_+𝒰_{K₄} (`Paper.alg_k4_module_generators`, `Paper.alg_k4_generator_products`); the Gröbner-basis check over 𝔽_32003 is an external computation) |
| `alg:k4-resolution` | equation | `Paper.alg_k4`, `Paper.alg_k4_graded_betti`, `Examples.K4_betti_rows`, `K4_betti_entries` | Proved (the graded Betti numbers β_{0,0}, β_{0,3}, β_{0,4}, β_{1,5}, β_{2,6} = 1, 4, 3, 24, 16 as dimensions of the internal Tor pieces, all others zero; θ, ω̃, 30, 48, d_G = 22 and ρ = 2) |
| `fig:k4-states` | figure | `Paper.fig_k4_states` (= `K4_state_counts`), `Examples.K4_sector_strong_field` | Proved (number, weight, q and p per state type, the complex count per state chart (16, 4 or 1, total 48) and the real count per chart (1 for the 8 Eulerian states), `Paper.sf_k4_statewise_chart_counts`, `Paper.sf_k4_statewise_real_counts`) |

### §4 The strong-field boundary

| Label | Kind | Lean | Status |
|---|---|---|---|
| `sec:strong-field` | section | `StrongField/` | Section |
| `sf:parameters` | equation | hypotheses a_e ≠ 0, a_e² ≠ 1, p_i = b_i⁻¹ | Definition |
| `sf:state-weights` | equation | `phi`, `Multigraph.wt` | Definition |
| `sf:normal-form` | Theorem 4.1 | `Paper.sf_normal_form` (= `exists_powerMap_normal_form`), `Paper.sf_power_map_chart`, `Paper.sf_normal_form_branch` | Proved (analytic chart with analytic coordinate change Φ, analytic inverse and invertible diagonal derivative; exactly wt(S) distinct simple admissible solutions for small nonzero p; different states give different solutions. The chart coordinate is the paper's w, so Φ is w ↦ f; simplicity uses the determinant argument `isSimple_of_det_normC`) |
| `sf:power-map` | equation | `Paper.sf_power_map_chart` (`powerMap`, `chartB_eq_inv_powerMap`) | Proved |
| `sf:vertex-chart` | equation | `chartSys` | Definition (coordinates of the chart system) |
| `sf:edge-equations` | equation | `chartSys` | Definition |
| `sf:base-branch` | equation | `chartMap_base` | Proved |
| `sf:other-branch` | equation | `isAdmissibleSolution_chartBP` | Proved (the branch −F/q on S) |
| `sf:edge-involution` | equation | `Paper.sf_edge_involution` (= `edgeRes_involution`) | Proved (algebraic identity) |
| `sf:consistency` | equation | `chartSys` | Definition |
| `sf:units` | equation | `unitC`, `unitC_q0`, `Paper.sf_unit_equations` | Proved |
| `sf:unit-equations` | equation | `chartSys` | Definition |
| `sf:coordinate-change` | equation | `Paper.sf_power_map_chart`, `Paper.sf_unit_equations` | Proved (in the direction w ↦ f; W_i^{r_i} = C_{S,i}) |
| `sf:degree-saturation` | Lemma 4.2 | `Paper.sf_degree_saturation` (= `card_eq_of_saturation`), `exists_aux_near_generic` | Partial (replaced: an abstract topological lemma with an explicit density hypothesis, supplied in the application by the rational parametrization of the auxiliary coordinates; the lemma for smooth irreducible varieties is not formalized. Corollary 4.3, which uses it, is proved) |
| `sf:exhaustion` | Corollary 4.3 | `Paper.sf_exhaustion` (= `strong_field_exactly_Q_simple`) | Proved |
| `sf:boundary-algebra` | Proposition 4.4 | `Paper.sf_state_fiber_equiv`, `Paper.sf_vertex_fiber_equiv`, `Paper.sf_state_fiber_length`, `Paper.sf_state_fiber_regular`, `Paper.sf_ramification_index`, `Paper.sf_boundary_algebra_finrank`, `Paper.sf_boundary_algebra_local` | Proved (the local algebra of the special fiber p = 0 of the state chart, analytic germs modulo the parameter germs, is ℂ[w]/(w_i^{r_i}) in the chart coordinate and in the vertex coordinate; it is local, a complete intersection, of length wt(S); the ramification index is read as the analytic vanishing order r_i of p_i along the i-th coordinate axis) |
| `sf:local-algebra` | equation | `Paper.sf_state_fiber_equiv`, `Paper.sf_analytic_trunc_equiv`, `BoundaryAlgebra.truncBasis`, `truncIdeal_rS_eq_span_neg_one_pow` | Proved (as for `sf:boundary-algebra`) |

### §5 Real sign sectors and the minimum real count

| Label | Kind | Lean | Status |
|---|---|---|---|
| `sec:real` | section | `Real/` | Section |
| `real:sign-sectors` | Proposition 5.1 | `Paper.real_sign_sectors` (= `real_sign_sectors`) | Proved |
| `real:maximum-principle` | equation | `totalField_pos` | Proved (the consequence F_i > 0 of the maximum principle) |
| `real:edge-branches` | Lemma 5.2 | `Paper.real_edge_branches`, `Paper.real_edge_branches_unique_pos`, `_neg`, `Paper.real_edge_branches_analytic` | Proved (the two branches, signs and uniqueness; real analyticity on the positive quadrant; the Jacobian of the cleared edge equations has positive determinant on the positive branch and negative on the negative branch) |
| `real:edge-product` | equation | `Paper.real_edge_branches` | Proved |
| `real:log-branches` | equation | `sectorMsg_eq_exp` | Proved |
| `real:edge-bound` | equation | `Paper.real_edge_bound` (= `BP.abs_zPlus_lt`), `BP.abs_zPlus_le` | Proved (strict form for a_e ≠ 1; the non-strict form holds for every a_e > 0) |
| `real:field-map` | equation | `sectorField` | Definition |
| `real:vertex-map` | Proposition 5.3 | `Paper.real_vertex_map` (= `eq_sectorMsg`), `Paper.real_vertex_map_analytic`, `Paper.real_vertex_map_nondegeneracy` | Proved (bijection of points, box estimate, real-analytic maps on open sets restricting to mutually inverse correspondences, and equivalence of nondegeneracy in both directions; the solution spaces are identified as sets, not as analytic germs with nonreduced structure) |
| `real:vertex-equation` | equation | `sectorField … = log b / 2` | Definition |
| `real:global-box` | equation | `Paper.real_global_box` (= `abs_sub_le_of_sectorField_eq`) | Proved |
| `real:sector-degree` | Proposition 5.4 | `Paper.real_sector_degree`, `Paper.real_sector_proper`, `Paper.real_sector_degree_homotopy`, `Paper.real_sector_surjective_of_degree`, `Paper.thm_real_ii_sector`, `Paper.thm_real_ii_lower`, `Paper.real_sector_degree_bounded` | Proved (𝔥_S is proper and has degree (−1)^{v(S)} for a_e > 0 and no vertex of S-degree one, in particular for Eulerian S; every map of the homotopy D_S − tΨ_S has the same degree; surjectivity follows from the nonzero degree, and also from `surjective_sub_of_bounded`. The degree is the C¹ degree described in "Differences in hypotheses") |
| `real:degree` | equation | `Paper.real_sector_degree`, `Paper.real_sector_degree_integral`, `Paper.real_sector_signed_count` | Proved (deg 𝔥_S = (−1)^{v(S)}, in the integral form at every value and as the signed count at every regular value) |
| `real:lower-bound` | equation | `Paper.thm_real_ii_lower` | Proved |
| `real:sector-parity` | Corollary 5.5 | `sector_count_odd`, `positive_count_odd` | Proved |
| `real:strong-field-count` | Proposition 5.6 | `Paper.thm_real_ii_strong`, `Paper.real_strong_field_count` (= `card_sector_strong_field`) | Proved |
| `real:spin-gauge` | equation | `gaugeA`, `gaugeB`, `gaugeY`, `isAdmissibleSolution_gauge`, `isSimpleSolution_gauge` | Proved |
| `real:all-real-states` | Remark 5.7 | `Paper.real_all_real_states`, `card_sector_strong_field` | Proved (the combinatorics of weights and degrees; per chart state one real root if S is Eulerian and none otherwise, all roots real exactly for cycle unions, sign pattern negative exactly on S, in every field orthant through the gauge, `Paper.real_all_real_states_chart_counts`, `Paper.real_all_real_states_orthant`) |
| `real:minimum` | equation | `Paper.thm_real_ii_min` | Proved |
| `real:positive-bound` | Corollary 5.8 | `Paper.real_positive_bound` | Proved |
| `real:positive-budget` | equation | `Paper.real_positive_bound` | Proved |
| `real:parity` | equation | `Paper.real_positive_bound`, `Q_modEq_two_pow_nu`, `card_real_admissible_modEq_Q` | Proved |

### Supplementary material

| Label | Kind | Lean | Status |
|---|---|---|---|
| `supp:notation` | section (notation) | header of `Paper.lean` | Definition |
| `supp:degree-section` | section | — | Section |
| `supp:elementary-degree` | section (proof of Corollary 2.6) | `Paper.cor_elementary_degree_*` | Proved |
| `supp:nonnormalizable` | section | — | Section |
| `supp:nonnormalizable-dim` | proposition | `Paper.supp_nonnormalizable_dim_tree`, `Paper.supp_nonnormalizable_dim_cyclic`, `Paper.supp_nonnormalizable_chart`, `Paper.supp_nonnormalizable_regular`, `Paper.supp_nonnormalizable_propagation` | Proved (for connected G: if G is a tree, the locus F ≡ −1 is empty outside the zero set of a nonzero P ∈ ℤ[a,b], over every field; if ν ≥ 1, outside the zero set of a nonzero P ∈ ℂ[a,b] the locus is nonempty and smooth of dimension ν − 1. The locus is the set of solutions with nonzero messages and nonzero update denominators, identified with a fiber of the chart equations in (a, x); smooth means that the Jacobian of these |V| equations in |E| unknowns is surjective at every point, and the dimension is that of its kernel, with a local chart from the implicit function theorem over ℂ. Smoothness holds generically over every field; nonemptiness and the chart are proved over ℂ. Generic smoothness in characteristic zero is replaced by a dimension count on the ring of critical points, and the paper's base point by a choice of signs of x, since the edge orientation is fixed. Irreducibility of the locus is not claimed) |
| `supp:ring` | section | — | Section |
| `supp:vector-bundle` | section (proof of Lemma 3.3) | `Paper.alg_vector_bundle_regular`, `Paper.alg_vector_bundle_trivialization`, `Paper.alg_vector_bundle_evaluation_surjective`, `Paper.alg_vector_bundle_kernel_rank` | Proved (chart level: on every standard chart the evaluation map is surjective with kernel free of rank 3m, the edge equations become independent linear coordinates after an explicit coordinate change and form a regular sequence, and the chart ring of the incidence zero scheme is a polynomial ring in 3m variables over the chart coordinate ring, its points being a chart point with a kernel vector; on chart overlaps the evaluation maps differ by the diagonal edge-bundle transition units, the kernel transitions are linear with the cocycle condition, and the chart trivializations of Z_G differ by the induced linear substitutions (`Paper.alg_vector_bundle_overlap_evaluation`, `Paper.alg_vector_bundle_cocycle`, `Paper.alg_vector_bundle_linear_transition`); the kernel sheaf K of the glued evaluation map is free of rank 3m on every chart with these transitions (`Paper.alg_kernel_sheaf_chart`, `Paper.alg_kernel_sheaf_zero_scheme`); the sequence 0 → K → O^{4m} → F_G → 0 is short exact (`Paper.alg_kernel_sheaf_short_exact`); the total space of the kernel bundle is glued from Spec of polynomial rings in 3m variables over the face rings, with affine projection and restriction maps the transposed kernel transitions, and is isomorphic to Z_G over X_G (`Paper.alg_vector_bundle_total_space`, `Paper.alg_vector_bundle_affine`, `Paper.alg_vector_bundle_sym_sections`, `Paper.alg_vector_bundle_sym_restrict`, `Paper.alg_vector_bundle_sym_transpose`)) |
| `supp:cm-localization` | section | `Paper.supp_cm_localization_cohenMacaulay`, `Paper.supp_cm_localization_dimension`, `Paper.supp_cm_localization_height`, `Paper.supp_cm_localization_depth`, `Paper.supp_cm_localization_bounds`, `Paper.supp_depth_finite_free_resolution`, `Paper.alg_cohenMacaulay_all_primes` | Proved (for every prime 𝔭 of S_G containing I = ker(S_G → 𝒰_G): depth_{(S_G)_𝔭}(𝒰_G)_𝔭 = ht 𝔭 − ρ = dim (𝒰_G)_𝔭, the dimension being the support dimension over (S_G)_𝔭; the depth bound comes from the localized resolution and the depth lemma. The dimension formula is replaced by ht I = ρ, proved from a transcendence basis of 𝒰_G among the coefficients and the growth of heights along polynomial extensions, and by contracting chains of the support. The equivalence with the ring statement is not formalized; Cohen–Macaulayness of the ring 𝒰_G at every prime is proved by another route, `Paper.alg_cohenMacaulay_all_primes`) |
| `supp:functoriality` | section | `Paper.alg_graph_map_relation`, `Paper.alg_derived_ring_map_eq`, `Paper.alg_tor_isomorphism_graph_map_natural`, `Paper.alg_disjoint_union_tensor` | Partial (the conclusions of `alg:functoriality` are proved, including the copied sections with signs ε_φ and a Tor map along a non-flat coefficient ring map; the proof route through a map of Koszul algebras of sheaves, derived global sections and Künneth is not formalized) |
| `supp:cycle-product` | section | `Paper.alg_cycle_algebra`, `Paper.alg_cycle_algebra_tor`, `Paper.alg_cycle_product` | Proved |
| `supp:generator-bridge` | section | `Paper.alg_module_generator_number`, `Paper.alg_module_generator_sharp`, `Paper.alg_module_generator_min_real_count` | Proved for the chart-intersection model (intrinsic module minimum, exact cycle criterion and real-minimum comparison) |
| `supp:three-invariants` | section | `fGen_two_I`, `thetaTwoI_eq_betti`, `Paper.alg_universal_hilbert`, `Paper.alg_artin_parameters_regular`, `Paper.alg_artin_hilbert` | Proved (f_d(2i) = i^d(1 − d), the alternating numerator, the Hilbert series from the resolution, and regularity of general linear forms with the Artin Hilbert series; the regularity proof uses a graded depth criterion instead of the system-of-parameters argument) |
| `supp:pencil` | section | — | Section |
| `alg:pencil-sections` | remark | `Paper.alg_pencil_cohenMacaulay`, `Paper.alg_pencil_coefficient_ring`, `Paper.alg_parameter_section_hilbert`, `Paper.alg_pencil_hilbert`, `Paper.alg_parameter_cut`, `Paper.alg_parameter_resolution_exact`, `Paper.alg_parameter_resolution_minimal`, `Paper.alg_parameter_section_tor`, `Paper.alg_parameter_section_total_betti`, `Paper.alg_parameter_section_bigraded`, `Paper.alg_parameter_resolution_graded_exact`, `Paper.alg_parameter_augmentation_graded_exact`, `Paper.alg_parameter_section_tor_product` | Proved (the section Hilbert series, finite freeness, the natural graded resolution and augmentation, minimality, each bigraded Tor dimension, the total Betti number and the products under all successive cuts; the pencil section is a one-dimensional Cohen–Macaulay ring, finite free over ℂ[X] of rank ω̃_G(1) and finite over its coefficient ring, a polynomial ring in ρ + 1 variables, `Paper.alg_pencil_cohenMacaulay_over_coefficients`; the coefficient isomorphism is stated as a ring isomorphism) |
| `supp:degree-bounds` | section | — | Section |
| `alg:degree-bounds` | proposition | `Paper.alg_degree_bounds`, `Paper.U_eq_zpow`, `Q_triFlower`, `Q_ladder`, `isPruned_iff` | Proved |
| `alg:theta-special-value` | equation | `Paper.alg_theta_special_value_sum`, `Paper.alg_theta_special_value`, `Paper.alg_theta_f_closed_form`, `Paper.alg_theta_special_value_two`, `theta_eq_U_of_connected` | Proved (for connected graphs and every γ: the bouquet sum and, with γ = ξ − ξ⁻¹, the closed form; the second equality is proved through the recurrence of the binomial transform rather than the binomial theorem; the citation of Watanabe's Lemma 4.2 is replaced by this proof) |
| `supp:scope` | section | — | Section |
| `alg:scope` | remark | `Paper.alg_scope`, `Paper.alg_k4_artin_exists`, `sum_finrank_incidenceTor` | Proved for the chart-intersection model: an actual linear regular Artin quotient has dimension 30, and the total Tor dimension is 48 |
| `supp:strong-field` | section | — | Section |
| `supp:boundary-algebra` | section | `Paper.supp_boundary_family_basis`, `Paper.supp_boundary_state_family_rank`, `Paper.supp_boundary_family_special_fiber`, `Paper.sf_state_fiber_regular`, `Paper.sf_ramification_index` | Proved (ℂ{w} is a free ℂ{p}-module with the monomial basis w^α, α_i < r_i, of rank wt(S), specializing at p = 0 to the basis of the special fiber; the proof regroups the power series by exponent residues; the chart as the analytic space ℂ{w,p}/((−1)^{k_i} w_i^{r_i} − p_i) is not formed, the family being described through the pullback ℂ{p} → ℂ{w}) |
| `supp:duality` | section | — | Section |
| `sf:serre-comparison` | remark | `Paper.sf_serre_duality`, `Paper.sf_serre_cup_perfect`, `Paper.sf_serre_cup_eq_residue`, `Paper.sf_serre_residue_pairing_perfect`, `Paper.sf_serre_residue_orthogonal`, `Paper.sf_serre_cup_orthogonal` | Proved (over any field K, for one vertex: the cup product H^1(ℙ¹, O(−k)) × H^0(ℙ¹, O(k − 2)) → H^1(ℙ¹, O(−2)) followed by the trace H^1(ℙ¹, O(−2)) ≅ K is a perfect pairing, giving H^1(ℙ¹, O(−k)) ≅ H^0(ℙ¹, O(k − 2))^*; through the affine coordinate it is the residue pairing (f, g) ↦ (coefficient of w^{r−1} in fg) on B = K[w]/(w^r), r = k − 1, which is perfect with (w^aB)^⊥ = w^{r−a}B. The isomorphism is proved directly from the cup product, with O(−2) in place of ω_{ℙ¹}; general Serre duality and the dualizing sheaf are not formalized. As the remark says, the trace and the identifications with B depend on the chosen coordinate; no algebra identification with a Tor summand is claimed) |
| `supp:k4-states` | section | — | Section |
| `sf:k4-states` | example | `Paper.sf_k4_states` (= `K4_strong_field`), `Examples.K4_isEvenSet_iff`, `Examples.K4_sector_strong_field` | Proved (the total counts (48, 8, 1), one real root per Eulerian sector, the intrinsic module-generator count, and the statewise complex and real chart counts, `Paper.sf_k4_statewise_chart_counts`, `Paper.sf_k4_statewise_real_counts`) |
| `supp:real` | section | — | Section |
| `supp:edge-branches` | section (proof of Lemma 5.2) | `BP.quadPosRoot_spec`, `BP.posMsg_edge`, `Paper.real_edge_branches_analytic` | Proved (as for `real:edge-branches`) |
| `real:edge-cavities` | equation | `field_eq_auxA` | Proved |
| `real:edge-quadratic` | equation | `BP.edge_quadratic`, `BP.edge_quadratic'` | Proved |
| `supp:vertex-map` | section | `Paper.real_vertex_map`, `Paper.real_vertex_map_analytic` | Proved (as Proposition 5.3) |
| `supp:positive-bound` | section | `Paper.real_positive_bound` | Proved |
| `supp:zero-couplings` | section | `Paper.real_zero_couplings_msg`, `Paper.real_zero_couplings_equiv`, `Paper.real_zero_couplings_lower`, `Paper.real_zero_couplings_min`, `Paper.real_zero_couplings_essential`, `zeroCoupling_strong` | Proved (messages on zero-coupling edges are 1; bijection with admissible solutions of the support graph over every field, with F_i + 1 > 0 in the real case; lower bound, minimum 2^ν of the coupling support graph, strong-field counts; the bound with ν(G) fails when all couplings vanish) |
| `supp:related` | section | — | Section (no formal content) |

## Axioms

`PaperAudit.lean` collects, with `Lean.collectAxioms`, the axioms of every
constant of the environment whose name lies in the `BPFixedPoints`
namespace, including private declarations, auxiliary declarations,
definitions and instances. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed; `sorryAx`, user axioms and native-evaluation
axioms fail the build. `native_decide` is not used; every concrete value
(the tables for the triangle, K₄ and the bowtie, the Betti numbers of K₄)
is checked by kernel `decide`. `checks/validate_paper.py` records the
source digests, the dependency revisions, the last successful audit line and
whether the build was clean in `validation/receipt.json`.

Here VERIFIED means Lean kernel checking together with this axiom audit.
It does not claim peer review, nor a formal proof of every statement in the
paper.
