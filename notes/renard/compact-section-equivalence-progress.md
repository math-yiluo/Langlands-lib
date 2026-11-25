# Renard II.2.5: complex vector sheaves, compact-section test modules and comparison targets

This note, dated 11 November 2026, maps Renard II.2.5 onto the Lean
declarations of `Langlands/Sheaf/Renard/` built for III.3 (see
[iii3-sheaf-sections](iii3-sheaf-sections.md)). It records the constructed
functors and comparison maps, the closed statements of the II.2.5 Theorem and
Remark, their hypotheses and sizes, and their proofs. The Library proves all
five statements (see [Proofs](#proofs)).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The modules below were checked against the II.2.5 Proposition, Remark and
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
| Proof, p.39: the inverse `M ↦ (U ↦ χ_U·M)` with its complex structure | `ProjectorVectorSheaf.functor`, `sheaf`, `sectionLinearEquiv`, `functor_comp_forget₂` ([pair](../../Langlands/Sheaf/Renard/ProjectorVectorSheaf.md)); sections `ProjectorVectorSheaf.sectionMk`, `ProjectorVectorSheaf.section_ext`, `ProjectorVectorSheaf.originalSection`, `ProjectorVectorSheaf.compactOriginal`, declared in module `ProjectorVectorSheafSections` ([pair](../../Langlands/Sheaf/Renard/ProjectorVectorSheafSections.md)) | constructed |
| Proof, p.40: the sheaf rebuilt from `F_c(X)` is `F`, `χ_U·F_c(X) = F(U)` | `SheafProjectorComparison.sheafComparison`, `sheafComparison_app_val`, `sheafComparisonNat` ([pair](../../Langlands/Sheaf/Renard/SheafProjectorComparison.md)) | map constructed |
| Proof, p.40: `M_c(X) = ⋃_U χ_U·M = M` | `ModuleProjectorComparison.moduleComparison`, `moduleComparisonHom_component`, `moduleComparisonNat` ([pair](../../Langlands/Sheaf/Renard/ModuleProjectorComparison.md)) | map constructed |
| Proof, p.40: both comparisons are isomorphisms | `CompactSectionEquivalence.SheafComparisonIsIso` ([pair](../../Langlands/Sheaf/Renard/CompactSectionEquivalenceStatement.md)), `ModuleProjectorComparison.ModuleComparisonIsIso` ([pair](../../Langlands/Sheaf/Renard/ModuleProjectorComparisonStatement.md)) | proved (`sheafComparisonIsIso`, `moduleComparisonIsIso`) |
| Theorem, p.39: the two functors are equivalences | `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence`, `ProjectorFunctorIsEquivalence` (same pair) | proved (`compactSectionFunctorIsEquivalence`, `projectorFunctorIsEquivalence`) |
| Remark, p.42: `F_x = F_c(X)/⟨f·φ, f(x) = 0⟩` | `CompactSectionStalks.vanishingSpan`, `stalkQuotientMap`, `stalkQuotientMap_surjective`, `stalkQuotientMap_naturality` ([pair](../../Langlands/Sheaf/Renard/CompactSectionStalks.md)); statement `CompactSectionStalks.StalkQuotientComparison` ([pair](../../Langlands/Sheaf/Renard/CompactSectionStalksStatement.md)) | map and surjectivity constructed; bijectivity proved (`stalkQuotientComparison`) |

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

## Proofs

The Library proves each closed statement, in `Langlands/Sheaf/Renard/`:

| Statement | Proof |
| --- | --- |
| `CompactSectionStalks.StalkQuotientComparison` | `stalkQuotientComparison` (`CompactSectionStalksProof.lean`) |
| `CompactSectionEquivalence.SheafComparisonIsIso` | `sheafComparisonIsIso` (`SheafComparisonIsIsoProof.lean`) |
| `ModuleProjectorComparison.ModuleComparisonIsIso` | `moduleComparisonIsIso` (`ModuleProjectorComparisonProof.lean`) |
| `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence` | `compactSectionFunctorIsEquivalence` (`CompactSectionEquivalenceProof.lean`) |
| `CompactSectionEquivalence.ProjectorFunctorIsEquivalence` | `projectorFunctorIsEquivalence` (`ProjectorFunctorEquivalenceProof.lean`) |

The two equivalence proofs use the two isomorphism proofs
(`compactSectionFunctorIsEquivalence_of_comparisons`,
`projectorFunctorIsEquivalence_of_comparisons`). With both isomorphisms, `sheafComparisonNat` and
`moduleComparisonNat` become natural isomorphisms and give the unit and
counit of an equivalence. For the stalk statement only injectivity needs proof:
a compact section with zero germ at `x` vanishes on a compact open
neighborhood `W` of `x`. Hence it equals `χ_U · s` for a compact open
`U ⊇ supp s` with `x ∉ U`.

## Remaining obligations

- The original-module stalk description `M_x = M/M(x)` of p.41 has no Lean
  statement in these modules. With the module comparison proved, it should follow from
  `StalkQuotientComparison` by transport along that comparison.
- The rest of pp.41–42 is not covered: the `q_!`/`q^{-1}` examples,
  restriction to locally closed subsets, distributions and the exact
  sequences.

## Modules

All modules below are in Library commit `0a5678a23daa0818e88076247923cd745542293f`.

| Kind | Module |
| --- | --- |
| definition | `VectorSheafScalars`, `CompactSectionTestModule` |
| definition | `CompactSectionStalks` |
| definition | `ProjectorVectorSheaf` |
| definition | `ProjectorVectorSheafSections` |
| definition | `SheafProjectorComparison` |
| definition | `ModuleProjectorComparison` |
| statement | `CompactSectionStalksStatement` |
| statement | `CompactSectionEquivalenceStatement` |
| statement | `ModuleProjectorComparisonStatement` |
