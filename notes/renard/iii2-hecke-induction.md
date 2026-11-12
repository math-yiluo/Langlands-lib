# Renard III.2: Hecke induction and the complete assertion map

Worker 150, Task 5296 (`29275a21-bb5b-46f1-8412-ed69ddc931a1`).

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, III.2, printed pp.70–83 /
PDF pp.76–89. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The entire section was read. PDF page numbers are printed page numbers plus six.
This map lists the definitions, named assertions, examples, remarks and numbered
proof displays; a published proposition definition is distinguished from a proof.

## Models, conventions and status

Groups are Hausdorff, locally compact and nonarchimedean, the source's t.d.
convention from II.1.1. Group and representation-carrier universe parameters
remain independent. No topology or finite-dimensionality is imposed on a
representation space. The actual published `Langlands.Hecke.HeckeAlgebra`,
`Langlands.SmoothRep`, Chapter I module categories, tensor quotient and Hom
constructions are reused throughout.

Write `HH` below for the namespace `Langlands.Hecke.Homomorphism`, `I` for
`Langlands.Induction`, `J` for `Langlands.Jacquet`, and `JL` for
`Langlands.Jacquet.Localization`. These abbreviations in this note are only
namespace abbreviations, not new Lean declarations.

Mathlib's modular character `Δ` scales the right-pushforward Haar measure.
Renard's character is `δ = Δ⁻¹` (II.3.7, printed p.47 / PDF p.53). Thus the
relative twist in III.2.6 is `δG|H/δH = ΔH/ΔG|H`. Weighted distribution inversion
on Haar densities is `f(x) ↦ Δ(x)f(x⁻¹)`. It is complex-linear and reverses
convolution. It differs from unweighted function inversion and from the
conjugate-linear Hecke adjoint.

The eight initial Hecke definition/statement units through III.2.6 are
published. Their declarations are in the modules linked below. The four units
`NormalQuotientModels`, `NormalQuotientStatements`, `MackeyModels` and
`MackeyStatements` have been compiled and staged in the same task. Their entries
below describe submitted targets, pending independent review/integration as
applicable at this snapshot. They are not represented here as proved results.

## III.2.1: continuous homomorphisms and four Hecke functors

Source: printed pp.70–71 / PDF pp.76–77.

| Assertion | Exact Lean counterpart and scope |
| --- | --- |
| Definition (III.2.1.1): pullback along continuous `φ : H → G`, with action `π(φ(h))` and unchanged maps; smoothness | `HH.restriction` in [HomomorphismSmooth](../../Langlands/Representation/Hecke/HomomorphismSmooth.lean) is the published `Langlands.MixedProductTensor.pullbackFunctor`. `Langlands.isSmooth_comp` proves smoothness. No injectivity or closed image is assumed. |
| Left/right regular representations on `H(G)` used in the construction are smooth | `HH.isSmooth_leftTests`, `HH.isSmooth_rightTests`, and `HH.leftRepresentation_isSmooth` in [HomomorphismLeft](../../Langlands/Representation/Hecke/HomomorphismLeft.lean). The distribution right representation is `HH.rightRepresentation` and `HH.rightRepresentation_isSmooth` in [HomomorphismRight](../../Langlands/Representation/Hecke/HomomorphismRight.lean). |
| The nondegenerate `H(H)` bimodule on the actual `H(G)`, using inversion for the right action | `HH.leftModule`, `HH.rightModule`, `HH.bimodule`, `HH.left_commutes_right`, and `HH.bimodule_isNondegenerate`. `Langlands.Hecke.haarInversion` and `haarInversion_mul` in [HaarInversion](../../Langlands/Representation/Hecke/HaarInversion.lean) implement the required distribution anti-involution. `HH.rightModule_eq_integrated` identifies the actual inversion-defined action with its distribution integration. |
| Left `H(H)` action commutes with right multiplication by `H(G)`, and right `H(H)` action with left multiplication by `H(G)`; two-sided nondegeneracy | `HH.left_commutes_regular`, `HH.regular_commutes_right`, `HH.left_regular_nondegenerate`, `HH.regular_right_nondegenerate`. These are proved laws of the specified actions. |
| Definitions of `F`, pseudo-`F`, `I`, `P` through Chapter I and III.1.4 | `HH.F`, `HH.I`, `HH.P`, `HH.pseudoF` directly specialize `NondegenerateTensorFunctor.F/P` and `RenardHomFunctors.I/pseudoF`. `HH.smoothF`, `smoothPseudoF`, `smoothI`, `smoothP` transport them through the exact `heckeNondegenerateModuleFunctor`, consuming explicit equivalence proofs. The independent published theorem `Langlands.Hecke.heckeNondegenerateModuleEquivalence` proves III.1.4. |
| `Fφ ≅ F`, `F ⊣ I`, `P ⊣` pseudo-`F` | `HH.ContinuousHomomorphismStatements` in [HomomorphismStatements](../../Langlands/Representation/Hecke/HomomorphismStatements.lean), the conjunction of `HeckeInductionAdjunctionStatement` and `SmoothInductionAdjunctionStatement`. The exact generic adjunction evaluation formulas and naturality are retained. Hecke equivalences are conclusions, not extra hypotheses. This is a published statement; its exact proof is Task 5401. |
| Example: transport by an isomorphism; conjugation formula (III.2.1.2) | `HH.restriction` already applies to a continuous group isomorphism. The generic inner-conjugation adapter `I.conjugateSmoothInducedEquiv` below consumes the explicit equality `τ(e(p)) = σ(p)`. A source-named declaration of the conjugated coefficient representation and the equation `πᵍ(ghg⁻¹)=π(h)` is not separately packaged here. |

## III.2.2–III.2.5: function induction and Frobenius reciprocity

| Locator and assertion | Exact Lean counterpart, limitation or gap |
| --- | --- |
| III.2.2 Definition, printed p.71 / PDF p.77: covariant smooth functions, right translation and compact induction | `I.SmoothFunctions`, `I.smoothInduced`, `I.CompactFunctions`, `I.compactInduced`, and their smoothness proofs and functors in [Definitions](../../Langlands/Representation/Induction/Definitions.lean). The model uses a uniform open right stabilizer and compact projected support; the compact-open basis supplies the source's compact open stabilizer. |
| III.2.2 Lemma and (III.2.2.1), printed pp.71–72 / PDF pp.77–78: fixed vectors as products over all double cosets, or finite-support functions for compact induction | `I.fixedEvaluationEquiv` and its explicit inverse in [FixedVectorModel](../../Langlands/Representation/Induction/FixedVectorModel.lean) prove the smooth-induction model **for a finite double-coset transversal**. `I.fixedDoubleCosetSection` constructs individual compact sections. The unrestricted product and finite-support direct-sum equivalences for an arbitrary transversal are not supplied by that finite theorem; those full source models remain a gap. |
| III.2.2 Proposition, printed p.72 / PDF p.78: functoriality by postcomposition and exactness of both inductions | The actual functors and their postcomposition laws are in `I.smoothInductionFunctor` and `I.compactInductionFunctor`. `I.InductionExactnessClause` in [StructuralStatement](../../Langlands/Representation/Induction/StructuralStatement.lean) states full exactness. Published `I.smoothInductionSurjectivity` and `I.compactInductionSurjectivity` prove the surjectivity portions under compact-open cofinality. This note does not claim a proof of the entire seven-clause `I.StructuralStatement`. |
| III.2.3 Lemma, printed p.72 / PDF p.78: compact `H\G` gives `Ind=ind` and preserves admissibility | `I.CompactQuotientClause`; its proof is `I.compactQuotientClause_holds` in [CompactQuotientProof](../../Langlands/Representation/Induction/CompactQuotientProof.lean), using `compactInclusion_bijective_of_compactSpace` and `smoothInduced_isAdmissible_of_compactSpace`. |
| III.2.4 Lemma, printed p.73 / PDF p.79: normalizer conjugation does not change either induction, with `f(x) ↦ f(g⁻¹x)` | Generic published `I.conjugateSmoothInducedEquiv`, evaluation and naturality in [ConjugateParabolic](../../Langlands/Representation/Induction/ConjugateParabolic.lean) give the smooth-function assertion for an actual inner-conjugation subgroup equivalence and matching coefficient actions. The corresponding compact-induction equivalence is not provided by this declaration; a full compact counterpart remains a gap. |
| III.2.5 Theorem, printed pp.73–74 / PDF pp.79–80: smooth induction is right adjoint to restriction | `I.SmoothFrobeniusClause` in `I.StructuralStatement` specifies the linear Hom equivalence by evaluation at `1`. `HH.SmoothInductionAdjunctionStatement` is the separate Hecke-transport adjunction target; neither statement alone identifies the two induction functors. |
| III.2.5 Remark, (III.2.5.1)–(III.2.5.5), printed pp.74–75 / PDF pp.80–81: explicit smooth induction/Hecke Hom natural isomorphism | Published `HH.ClosedInductionHomStatement` in [ClosedInductionStatements](../../Langlands/Representation/Hecke/ClosedInductionStatements.lean). It prescribes `f ↦ (T ↦ (T·f)(1))`, existence of a compact-open right local unit for each Hom vector, and the inverse `q ↦ (g ↦ q(l(g)eK))` for every such local unit. The original induced carrier supplies covariance (III.2.5.3); the restricted-action identity of (III.2.5.4) is included explicitly. Its exact proof is Task 5402. |

## III.2.6–III.2.8: compact induction, duality and stages

| Locator and assertion | Exact Lean counterpart, limitation or gap |
| --- | --- |
| III.2.6 right module formula (III.2.6.1), printed p.75 / PDF p.81 | `HH.CompactInductionHeckeStatement` in [CompactInductionStatements](../../Langlands/Representation/Hecke/CompactInductionStatements.lean) includes the equality `(f·a)(x)=∫H ΔG(h)a(h)f(xh⁻¹) dμH`. The action is the original `HH.rightModule`; no unimodularity premise removes the factor. |
| III.2.6 tensor model, map (III.2.6.2) and Theorem, printed pp.75–76 / PDF pp.81–82 | `HH.relativeModularCharacter`, `tensorInductionHeckeFunctor`, `compactModularHeckeFunctor`, and `tensorInductionTmul` in [CompactInductionModels](../../Langlands/Representation/Hecke/CompactInductionModels.lean). Published `HH.CompactInductionHeckeStatement` asserts the natural isomorphism and specifies `p(f⊗w)(g)=∫H f((hg)⁻¹)ΔG(h)ρ(h⁻¹)w dμH` after every algebraic complex-linear functional. This specifies the vector formula without adding a topology to `W`. Its exact proof is Task 5403. |
| Proof models (III.2.6.3)–(III.2.6.4), printed pp.76–77 / PDF pp.82–83: fixed-vector direct sums and orbitwise tensor identifications | The existing finite `I.fixedEvaluationEquiv` supports only the finite-transversal situation. The unrestricted direct-sum models and orbitwise tensor identifications in this proof are not separately stated or proved by the new theorem statement. They remain construction/proof obligations for a proof following this source route. |
| III.2.6 final Remark, printed p.77 / PDF p.83: for open `H`, extension of Hecke distributions by zero identifies its bimodule with the inclusion bimodule; pseudo-`F ≅ F`; relative modular character is trivial | The generic actions exist above. This exact extension/inclusion bimodule comparison and the resulting Hecke pseudo-forgetful comparison for all open subgroups are not separately packaged here. A direct general-open-subgroup triviality theorem for `HH.relativeModularCharacter` is also not supplied by the compact-induction statement. These are retained gaps. |
| Same Remark, (III.2.6.5): open-subgroup compact induction is left adjoint to restriction | `I.OpenSubgroupAdjunctionClause` in `I.StructuralStatement`; the actual smooth categorical adjunction is published as `I.compactInductionAdjunction` in [OpenAdjunction](../../Langlands/Representation/Induction/OpenAdjunction.lean), with unit/counit formulas. This proves the function-category assertion, without claiming the preceding Hecke inclusion comparison. |
| III.2.7 Theorem and integral pairing, printed p.78 / PDF p.84: full closed-subgroup induction/compact-induction smooth duality | A restricted published result is `I.exists_integralDualEquiv_of_section` in [CompactQuotientSmoothDuality](../../Langlands/Representation/Induction/CompactQuotientSmoothDuality.lean). It requires compact quotient, a supplied continuous homomorphic section of the coefficient projection, a twist-square relation, and positivity/invariance conditions on the compact-model integral. It imposes no admissibility but does **not** cover the unrestricted closed-subgroup theorem or its general quotient-measure pairing. Those remain a gap. |
| III.2.8 Proposition, printed p.78 / PDF p.84: natural induction by stages | `I.InductionTransitivityClause` in `I.StructuralStatement` states both smooth and compact assertions. Published `I.smoothStagesEquiv` and `smoothStagesEquiv_natural` in [SmoothTransitivity](../../Langlands/Representation/Induction/SmoothTransitivity.lean) give the smooth assertion. The compact analogue is `I.compactStagesEquiv`, `compactStagesEquiv_natural`, and `compactInductionTransitivity` in [CompactTransitivityProof](../../Langlands/Representation/Induction/CompactTransitivityProof.lean). |

## III.2.9: coinvariants

Source: printed pp.78–80 / PDF pp.84–86.

| Assertion | Exact Lean counterpart, limitation or gap |
| --- | --- |
| Definition of the relation span and quotient | `J.relations`, `J.Coinvariants`, `J.mk`, `J.relations_eq_span` in [Coinvariants](../../Langlands/Representation/Jacquet/Coinvariants.lean) use Mathlib's actual quotient by the span of `ρ(h)v−v`. |
| Full algebraic dual of coinvariants equals subgroup-invariant functionals | Published `J.subgroupInvariantDual`, `J.coinvariantsDualEquiv`, and `coinvariantsDualEquiv_apply` in [DualJacquet](../../Langlands/Representation/Exponents/DualJacquet.lean). This is the full algebraic dual, as in this paragraph, not only smooth dual vectors. |
| Haar Example: the left-regular test-function coinvariants have dimension one | Haar existence and uniqueness are available, but an exact dimension-one declaration for this coinvariant carrier was not located in the inspected Library. The example remains an explicit adapter gap. |
| Remarks 1–2: action of a normalizing subgroup, smoothness and functoriality | `J.relations_stable`, `J.action`, `J.action_mk`, `J.map` and its laws; `J.isSmooth_action` in [SmoothTwist](../../Langlands/Representation/Jacquet/SmoothTwist.lean). `JL.smoothFunctor` in [Localization](../../Langlands/Representation/Jacquet/Localization.lean), at character `1`, is the smooth functor; `JL.trivialEquiv` and its naturality identify its carrier/action with the untwisted quotient. |
| Lemma (i): for `H=H1 H2`, with `H1` normalizing `H2`, iterated coinvariants equal full coinvariants | General published `JL.TowerDatum.equiv` in [LocalizationTower](../../Langlands/Representation/Jacquet/LocalizationTower.lean), specialized to trivial characters, first subgroup `H2`, second subgroup `H1`, compares the actual iterated quotient with the quotient by `H2 ⊔ H1`. With the source's product hypothesis this join is `H`; `JL.trivialEquiv` transports to the untwisted quotient. The narrower `J.coinvariantTower` in `CoinvariantTowerProof` assumes nested ambient-normal subgroups and alone does not cover the source's general product lemma. A source-named product adapter is not separately packaged. |
| Lemma (ii): natural functor version with final normalizing subgroup `N` and intermediate `J=⟨H1,N2⟩` | Published `JL.TowerDatum.smoothIso` and its representative formulas/naturality are the general counterpart. Use first subgroup `H2`, intermediate acting group `H1 ⊔ N2`, second subgroup `H1`, final acting group `N`, and trivial characters. The datum explicitly retains the two normalizer conditions and subgroup inclusions. Source-specific join/equality and trivial-character adapters are not bundled into a separate III.2.9 declaration. |
| Definition of filtered increasing union and following compact-containment Remark | `JL.IsLimitOfCompactSubgroups` in [LocalizationExactnessStatement](../../Langlands/Representation/Jacquet/LocalizationExactnessStatement.lean) uses the resulting condition that every compact subset lies in a compact subgroup. The exact source filtered-union definition and its compact-containment implication are not separately packaged here. |
| Proposition: relations are precisely vectors killed by some compact-subgroup average `eK` | `JL.CompactCharacterRelationDetectionClause` and proved `JL.mem_relations_iff_compact` detect a relation inside a single compact subgroup. They do **not** state the literal averaging-kernel criterion. The exact `eK` criterion, including the source's compact subgroup averaging, remains an adapter gap. |
| Corollary: `E'(H)=E(H)∩E'` and exactness of coinvariants, hence of `j_H` under compact exhaustion | `JL.CharacterLocalizationExactnessStatement` and its proof `JL.characterLocalizationExactness` in [LocalizationExactnessProof](../../Langlands/Representation/Jacquet/LocalizationExactnessProof.lean), at character `1`, cover injectivity, middle exactness and surjectivity of the actual quotient maps, with the full normalizing action. The intersection identity follows through the kernels of these quotient maps; its literal subrepresentation equality and the bridge from the source's filtered-union wording are not separately packaged. This proof is not evidence of the preceding literal `eK` criterion. |

## III.2.10–III.2.11: submitted remaining Hecke targets

| Locator and assertion | Submitted Lean counterpart and scope |
| --- | --- |
| III.2.10, printed pp.80–81 / PDF pp.86–87: closed normal quotient, compact-open image basis and smooth quotient coinvariants | `HH.quotientOpenSubgroup`, `isCompact_quotientOpenSubgroup`, `quotientNonarchimedean`, `normalQuotientAction`, its representative formula and smoothness, and `normalCoinvariantFunctor` in [NormalQuotientModels](../../Langlands/Representation/Hecke/NormalQuotientModels.lean). The action and morphisms reuse `Representation.quotientToCoinvariants` and `Rep.quotientToCoinvariantsFunctor` on exactly `J.Coinvariants`. |
| Distribution pushforward description and (III.2.10.1), printed p.80 / PDF p.86 | `HH.NormalQuotientHeckeStatement` in [NormalQuotientStatements](../../Langlands/Representation/Hecke/NormalQuotientStatements.lean) includes `T·a_{p,K}=T*a_{q(p),q(K)}`, using `a=eK*l(p)eK` as an actual Hecke density. A general pushforward `E'(P) → D'(P/N)` and its pairing identity are not separately constructed; they are an intermediate source proof device, not an extra input to this statement. |
| Pseudo-forgetful equals forgetful for the quotient, printed p.81 / PDF p.87 | First conjunct of `HH.NormalQuotientHeckeStatement`, a natural isomorphism of the actual Chapter I Hecke functors `pseudoF` and `F`. The local-unit identity `T·eK=T*eKM` is the `p=1` specialization of its preceding right-action formula. |
| Proposition, (III.2.10.2) and inverse, printed pp.81–82 / PDF pp.87–88 | `HH.NormalQuotientHeckeStatement` asserts a single natural isomorphism from actual `j_N` to actual Hecke tensor induction, with `[v] ↦ eKM⊗v` for every compact open `K` fixing `v`, and inverse `T⊗v ↦ T·[v]`. Choice independence, balancing, invertibility and naturality are conclusions, not supplied certificates. |
| Proposition's adjunction | `HH.NormalQuotientAdjunctionStatement` asserts actual `j_N ⊣` continuous pullback along `P → P/N`. It uses arbitrary carrier universe. |
| Corollary, printed p.82 / PDF p.88 | `HH.NormalQuotientInductionAdjunctionStatement`: for `P` closed in `G`, restriction to `P` followed by `j_N` is left adjoint to quotient pullback followed by actual smooth function induction `Ind_P^G`. Restriction implicit in the source's `V ↦ V_N` is explicit. `HH.NormalQuotientStatements` groups all three targets. |
| III.2.11 Theorem, printed pp.82–83 / PDF pp.88–89: Hom Mackey isomorphism | Actual bifunctors and composites in [MackeyModels](../../Langlands/Representation/Hecke/MackeyModels.lean). `HH.MackeyIsomorphismStatements` in [MackeyStatements](../../Langlands/Representation/Hecke/MackeyStatements.lean) asserts `mackeyHomLeft ≅ mackeyHomRight`, naturally on `SmoothRep(G)ᵒᵖ × SmoothRep(H)`. |
| Same Theorem: tensor Mackey isomorphism under pseudo-`F ≅ F` | Second Mackey assertion, `mackeyTensorLeft ≅ mackeyTensorRight` naturally on `SmoothRep(H) × SmoothRep(G)`, is explicitly conditional on `Nonempty (smoothPseudoF ≅ smoothF)`. The exact Hecke equivalences and `Fφ ≅ F` are conclusions. |
| Proof displays (III.2.11.1)–(III.2.11.10) | The theorem target states the resulting two natural isomorphisms. The intermediate Hom-set equivalences are not separately asserted here. Their ingredients are the published tensor–Hom adjunction (`Langlands.Renard.Smooth.TensorHom.smoothIntertwinerCurry`), the III.2.1 induction adjunction targets, and the pseudo-forgetful/forgetful condition specifically needed at (III.2.11.8). |

## Proof successors and retained work

The exact published statement targets have focused `lean.proof@1` successors:

- Task 5401 (`1ed372bc-4451-4d12-8a7f-070d0b3afd80`):
  `HH.ContinuousHomomorphismStatements`.
- Task 5402 (`1cedfe50-9565-4867-b786-9da87b49b6cd`):
  `HH.ClosedInductionHomStatement`.
- Task 5403 (`d95a6f63-4a55-407f-a899-cf5f2b98540f`):
  `HH.CompactInductionHeckeStatement`.

The exact III.2.10 and III.2.11 proof successors will be published once their
statement units enter the Library. Task 5296 supplies definitions, statements
and this source map; it does not claim their theorem proofs. The gaps recorded
in the tables remain gaps even when a related restricted result is published.
