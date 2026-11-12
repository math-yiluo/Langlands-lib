# Renard II.2.5: complex vector sheaves, compact-section test modules and comparison targets

Worker 184 and Worker 188, Task 5338, 11 November 2026. This note maps
Renard II.2.5 onto the Lean declarations built for the III.3 consumer
(Task 5297). It records the constructed functors and comparison maps, the
closed statements of the II.2.5 Theorem and Remark, their hypotheses and
sizes, and the proof tasks that carry the remaining obligations. None of
the statements below is proved yet.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The units below were checked against the II.2.5 Proposition, Remark and
Theorem with its proof, printed pp.38–40 / PDF pp.44–46. They were also
checked against the original-module stalk description `M_x = M/M(x)`,
printed p.41 / PDF p.47, and the Remark
`F_x = F_c(X)/⟨f·φ, φ ∈ F_c(X), f ∈ D(X), f(x) = 0⟩`, printed p.42 /
PDF p.48.

## Conventions and sizes

- A complex vector sheaf is
  `Langlands.Sheaf.Renard.VectorSheafScalars.VectorSheaf X`, an abbreviation
  for Mathlib's `TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of X)` on all opens
  of `X : Type u`. The source works with sheaves of `C^∞_X`-modules. The II.2.5
  Proposition identifies them with sheaves of complex vector spaces, and
  `VectorSheafScalars` constructs that module structure.
- Renard's t.d. hypothesis is `Langlands.Topology.IsLocallyProfinite X`
  (Hausdorff with a compact open neighborhood basis). Compact opens are
  therefore clopen. The scalar action in `VectorSheafScalars` needs no
  hypothesis on the topology.
- The published `Langlands.Sheaf.CompactSupport` puts the space, the
  coefficient ring and the section carriers in one universe. With `ℂ : Type`,
  everything involving compact sections is at `X : Type`, `ModuleCat.{0} ℂ`
  and `NondegenerateModuleCat.{0, 0}`. All statements below quantify over
  `X : Type`. The scalar action is universe-polymorphic in `u`.
  `ProjectorVectorSheaf.functor` is polymorphic too, from
  `NondegenerateModuleCat.{u, max u v}` to
  `TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of X)`, and the statements use
  `functor.{0, 0}`.
- Renard asserts that `ℂ` injects into every `C^∞(U)`. This fails for
  `U = ∅`, and no construction here uses it.
- The test algebra is the published
  `Langlands.HarmonicAnalysis.PointwiseTestAlgebra.Carrier X`. It acts on a
  compactly supported global section through `testScalar`, which reads a test
  function as a locally constant function on `⊤`.

## Source-to-declaration map

All names are in namespace `Langlands.Sheaf.Renard`.

| Source | Declarations | Status |
| --- | --- | --- |
| Proposition, p.38: a vector sheaf is a `C^∞_X`-module, `(f·s)(x) = f(x)s(x)` on germs | `VectorSheafScalars.module`, `germ_lc_smul`, `constants_smul`, `restrictSemilinear`, `appLinear` ([pair](../../Langlands/Sheaf/Renard/VectorSheafScalars.md)) | constructed |
| Theorem, p.39: `F_c(X)` is a nondegenerate `D(X)`-module, and `F ↦ F_c(X)` is a functor | `CompactSectionTestModule.testModule`, `Γgerm_testSmul`, `isNondegenerate`, `complexModule_eq`, `compactSectionFunctor` ([pair](../../Langlands/Sheaf/Renard/CompactSectionTestModule.md)) | constructed |
| Proof, p.39: the inverse `M ↦ (U ↦ χ_U·M)` with its complex structure | `ProjectorVectorSheaf.functor`, `sheaf`, `sectionLinearEquiv`, `functor_comp_forget₂` ([pair](../../Langlands/Sheaf/Renard/ProjectorVectorSheaf.md)); sections `ProjectorVectorSheaf.sectionMk`, `ProjectorVectorSheaf.section_ext`, `ProjectorVectorSheaf.originalSection`, `ProjectorVectorSheaf.compactOriginal`, declared in module `ProjectorVectorSheafSections` ([pair](../../Langlands/Sheaf/Renard/ProjectorVectorSheafSections.md)) | constructed (Worker 188) |
| Proof, p.40: the sheaf rebuilt from `F_c(X)` is `F`, `χ_U·F_c(X) = F(U)` | `SheafProjectorComparison.sheafComparison`, `sheafComparison_app_val`, `sheafComparisonNat` ([pair](../../Langlands/Sheaf/Renard/SheafProjectorComparison.md)) | map constructed |
| Proof, p.40: `M_c(X) = ⋃_U χ_U·M = M` | `ModuleProjectorComparison.moduleComparison`, `moduleComparisonHom_component`, `moduleComparisonNat` ([pair](../../Langlands/Sheaf/Renard/ModuleProjectorComparison.md)) | map constructed |
| Proof, p.40: both comparisons are isomorphisms | `CompactSectionEquivalence.SheafComparisonIsIso` ([pair](../../Langlands/Sheaf/Renard/CompactSectionEquivalenceStatement.md)), `ModuleProjectorComparison.ModuleComparisonIsIso` ([pair](../../Langlands/Sheaf/Renard/ModuleProjectorComparisonStatement.md)) | statements only |
| Theorem, p.39: the two functors are equivalences | `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence`, `ProjectorFunctorIsEquivalence` (same pair) | statements only |
| Remark, p.42: `F_x = F_c(X)/⟨f·φ, f(x) = 0⟩` | `CompactSectionStalks.vanishingSpan`, `stalkQuotientMap`, `stalkQuotientMap_surjective`, `stalkQuotientMap_naturality` ([pair](../../Langlands/Sheaf/Renard/CompactSectionStalks.md)); statement `CompactSectionStalks.StalkQuotientComparison` ([pair](../../Langlands/Sheaf/Renard/CompactSectionStalksStatement.md)) | map and surjectivity constructed; bijectivity is a statement only |

The comparison maps follow the source's formulas on compact opens.
`sheafComparison F hX` sends a section `s` over `V` to the family whose value
on a compact open `U ⊆ V` is the zero extension of `s|_U`. The value of
`moduleComparison hX M` at `m` is the compactly supported global section of
`P M` whose component on a compact open `U` is `χ_U · m`. Both are natural
transformations from the identity, `𝟭 ⟶ Γc ⋙ P` and `𝟭 ⟶ P ⋙ Γc`. No
inverse, inverse law or comparison certificate is assumed or constructed.

`StalkQuotientComparison` asserts that the map
`F_c(X) ⧸ vanishingSpan F x → F_x` induced by the compact germ map is
bijective, for every `X : Type` with `IsLocallyProfinite X`, every `F` and
every `x`. `vanishingSpan F x` is the complex span of the `f · φ` with
`f(x) = 0`. The source's middle description, by sections vanishing near
`x`, is not stated separately.

## Proof tasks

Each closed statement has its own `lean.proof@1` task. All five use
environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`.

| Statement | Task |
| --- | --- |
| `CompactSectionStalks.StalkQuotientComparison` | Task 5507, `35a1f2b6-846f-4884-a350-72fdbd67adb6` |
| `CompactSectionEquivalence.SheafComparisonIsIso` | Task 5508, `9acfe5aa-c8c3-44cc-a6bd-8bb23c6c924d` |
| `ModuleProjectorComparison.ModuleComparisonIsIso` | Task 5533, `e83a660d-f5e6-435d-ba2f-bfc6011d74f8` |
| `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence` | Task 5534, `9cac26a3-f3e3-41f6-a168-828b5691f273` |
| `CompactSectionEquivalence.ProjectorFunctorIsEquivalence` | Task 5535, `d681dc7e-6e4e-49c9-af10-de5d24cc9f35` |

The two equivalence proofs are expected to import the two isomorphism
proofs. With both isomorphisms, `sheafComparisonNat` and
`moduleComparisonNat` become natural isomorphisms and give the unit and
counit of an equivalence. For the stalk statement only injectivity is open:
a compact section with zero germ at `x` vanishes on a compact open
neighborhood `W` of `x`. Hence it equals `χ_U · s` for a compact open
`U ⊇ supp s` with `x ∉ U`.

## Remaining obligations

- The five proofs listed above.
- The original-module stalk description `M_x = M/M(x)` of p.41 has no Lean
  statement. Once the module comparison is proved, it should follow from
  `StalkQuotientComparison` by transport along that comparison.
- The rest of pp.41–42 is not covered: the `q_!`/`q^{-1}` examples,
  restriction to locally closed subsets, distributions and the exact
  sequences.

## Publication evidence

All units are in Library commit `0a5678a23daa0818e88076247923cd745542293f`.
Each was accepted after machine validation and an independent review.

| Candidate | Kind | Module |
| --- | --- | --- |
| `0c52ec3a-5411-45f9-8314-93d3e76c00de` | definition | `VectorSheafScalars`, `CompactSectionTestModule` |
| `c5f9bd40-f8c4-482a-a410-3ba83525f776` | definition | `CompactSectionStalks` |
| `01233f16-6a3a-41df-8e95-7e5f8020539e` | definition (Worker 188) | `ProjectorVectorSheaf` |
| `337ea224-0f71-4c23-9eca-78fb9bab37b6` | definition (Worker 188) | `ProjectorVectorSheafSections` |
| `155bed4d-bcdb-4106-a2d2-7262e69b0215` | definition | `SheafProjectorComparison` |
| `1158c902-1cd4-4fcb-89b1-8a2047ae801f` | definition | `ModuleProjectorComparison` |
| `832879c8-3957-4497-acf5-b3425a6f943b` | statement | `CompactSectionStalksStatement` |
| `4d47ced9-db27-465f-bbb5-1b34dd8b5b0e` | statement | `CompactSectionEquivalenceStatement` |
| `29706658-8d30-47c0-b225-46d2ebf77cc7` | statement | `ModuleProjectorComparisonStatement` |
