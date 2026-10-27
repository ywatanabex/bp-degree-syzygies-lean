# Third-party Lean material

The project's original code remains under the MIT license in [LICENSE](LICENSE).
The files listed below contain material adapted from
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2),
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.

> Fermat's Last Theorem in Lean 4
>
> Copyright 2026 Anthropic, PBC

Those portions are licensed under the Apache License, Version 2.0, reproduced
in [LICENSE-APACHE-2.0](LICENSE-APACHE-2.0). The upstream [NOTICE](third_party/anthropic-flt/NOTICE)
and [ATTRIBUTION.md](third_party/anthropic-flt/ATTRIBUTION.md) are preserved.
The selected files have no additional file-specific attribution entries in that
upstream table. Mathlib is a separately pinned Apache-2.0 dependency; its source
headers remain in the dependency checkout.

| Adapted module in `BPFixedPoints/Incidence/` | Upstream source |
| --- | --- |
| `PublicPresheafInternalHom.lean` | `Definitions/Def_PresheafOfModules_InternalHom.lean` |
| `PublicPresheafInternalHomSheaf.lean` | `P2M/Sol/S_PresheafOfModules_isSheaf_ihomObj.lean` |
| `PublicModuleTensorLocalization.lean` | `P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean` |
| `SchemeModuleMonoidal.lean` | `Definitions/Def_SheafOfModules_Monoidal.lean` |

Changes: move declarations into `BPFixedPoints`, replace the upstream wrapper
macros by their ordinary Lean declarations, use Mathlib's current
`PresheafOfModulesOfCommRing` API and one-based `List.TFAE` indices, narrow the
imports, and adapt the scheme construction to the project's original chosen
sheafification and counit. No external package or toolchain dependency is added.
The comparison, section and original-associator modules are project-specific
adapters and retain the original sheaves and section maps.

## OpenAI Math

`BPFixedPoints/Incidence/FreeAbelianCechResolution.lean` adapts the tuple
extra degeneracy and positive exactness proofs, and
`BPFixedPoints/Incidence/FreeAbelianCechSections.lean` adapts the tuple sections
and boundary comparisons, from
[openai/math](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/FreeCechResolution.lean),
commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
The second source is the adjacent `FreeCechSections.lean` in that directory.
These portions are under the Apache License, Version 2.0, reproduced in
[LICENSE-APACHE-2.0](LICENSE-APACHE-2.0). The upstream file has no individual
copyright or attribution header.

Changes: replace free module presheaves and module sheaves by free abelian
presheaves and underlying abelian sheaves, use native functor-category evaluation
and exact sheafification, and narrow the imports to pinned Mathlib. No external
package is added. Positive exactness is kept separate from augmented
degree-zero exactness, which requires a cover.
