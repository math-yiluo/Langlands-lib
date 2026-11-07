# Renard VI.1, VI.9.4, VI.9.6–VI.9.7, VII.1.3 and VII.2.2–VII.2.6: parabolic functors and tempered representations

Worker 6, 6 November 2026, updated 7 November 2026. This focused map
supplements the [whole-book ledger](coverage.md) and continues the
[actual-root and exponent source map](root-exponent-tempered-progress.md),
whose represented-parabolic induction, Levi-point transport, temperedness
predicate and VII.1.1, Casselman and VII.2.1 Remark 2 statements are used
below. It records twenty-two verified publications by Worker 6, one
definition and twenty-one statements, and the proof tasks for them. None of these
publications proves a proposition. It also lists the published proofs of
five of the statements, by other workers, and published conditional
reductions. The map is not a complete inventory of VI.1, VI.9, VII.1 or
VII.2, and supplies no new Lean proof. The
[supercuspidal induction and finite-length map](supercuspidal-finite-length-progress.md)
continues it for VI.3.6 and VI.5.2–VI.7.5, and the
[supercuspidal block map](supercuspidal-block-center-progress.md) for VI.4.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all forty primary files equal their frozen
accepted files, Worker 6's workspace files and the files at Library
`eec7519b852f9097606377425625fd5794c87f71`. A fresh Lean check at that
Library of fifty modules, including these twenty (check
`6459f600-a711-4494-a5dc-27d2639384bc`), had zero diagnostics. The two
VI.9.4 statements, added 7 November 2026, were published later: their four
primary files equal their frozen accepted files, Worker 6's workspace files
and the files at Libraries `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` and
`8b14de0b5103d5fc1e615f094904129bf8cfe3a3`, and a fresh Lean check of both
modules at the latter (check `6561d516-6349-465f-a892-72360be91883`) had
zero diagnostics.

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an accepted
`lean.statement@1` or `lean.definition@1` machine validation, an
independent semantic approval with no qualification and a published
integration. A definition receipt covers its construction and intrinsic
laws; a statement receipt does not prove its proposition.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [LeviFrobeniusReciprocityStatement](../../Langlands/Representation/Exponents/LeviFrobeniusReciprocityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviFrobeniusReciprocityStatement` | Statement `734b9786-356d-4a67-b62f-8e04f3b04351`; Reviewer 15183, review `ef723e0c-0965-4070-9179-9963a2e5fd08`; machine `65533b5c-1aaa-4fcc-99c4-956ca20e3318`; integration `f2b4c05a373a4528978a26cccf7d61be`, commit `819ea8d4de6f7dde4b0d7f879f58af405e135acf`. |
| [LeviParabolicFunctorsExactStatement](../../Langlands/Representation/Exponents/LeviParabolicFunctorsExactStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsExactStatement` | Statement `d4e93676-1c19-4bfd-9865-9cd763a7222d`; Reviewer 15196, review `b8e3b989-de4e-4fc4-b682-1182a37e786b`; machine `984c60d1-7209-4c5f-a2f3-0cd8b0a8c7c2`; integration `eb0cbd7c62c84dce95b49df0b8665e2a`, commit `819ea8d4de6f7dde4b0d7f879f58af405e135acf`. |
| [LeviParabolicFunctorsPreserveLimitsStatement](../../Langlands/Representation/Exponents/LeviParabolicFunctorsPreserveLimitsStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicFunctorsPreserveLimitsStatement` | Statement `de71af43-bc90-46e3-8838-16dd041f94ec`; Reviewer 15299, review `6ecae22c-a730-4d03-b74b-3e2fd3f40bf6`; machine `96963143-c6b1-4643-b3aa-1ec09c602477`; integration `a17d31e061d24da8bfc721424767e46f`, commit `73016647c403b942bebe18fad4e569a83c342b52`. |
| [LeviJacquetFiniteTypeStatement](../../Langlands/Representation/Exponents/LeviJacquetFiniteTypeStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetFiniteTypeStatement` | Statement `7516217f-e291-4532-86e2-d77f618ea9e0`; Reviewer 15265, review `a4c5a747-a391-4aa4-acab-94097dac89b9`; machine `0c3c2cdc-828a-41d1-8f26-d2f318ed8efb`; integration `4c6eb03bd10442aeb8f1aebd73d7d4a4`, commit `73016647c403b942bebe18fad4e569a83c342b52`. |
| [LeviSecondAdjointnessStatement](../../Langlands/Representation/Exponents/LeviSecondAdjointnessStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviSecondAdjointnessStatement` | Statement `f6896c6d-05c9-453e-8597-075e16cf05c5`; Reviewer 15353, review `9895a73b-17e5-4bb4-8f93-d05eae94310a`; machine `1a61a021-772a-4e0d-93d8-f99eca5c485f`; integration `2da1d747a80a45ff9f579797519aa982`, commit `08e8de28d111b66b088500c8ad1b0bd0f947991d`. |
| [LeviJacquetContragredientStatement](../../Langlands/Representation/Exponents/LeviJacquetContragredientStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement` | Statement `dbb3d501-a3c0-41fd-b9d8-dc80a270fb62`; Reviewer 15379, review `8e3e2bc4-3504-43b1-8609-156ba090e174`; machine `05988f50-dc7a-4287-bea1-de626066a651`; integration `1f3249f8cbe6472786c7e363480a20a5`, commit `08e8de28d111b66b088500c8ad1b0bd0f947991d`. |
| [MaximalLeviSupercuspidalReducibilityStatement](../../Langlands/Representation/Exponents/MaximalLeviSupercuspidalReducibilityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalReducibilityStatement` | Statement `350df272-e3a8-4a27-bc40-b04df9c26d13`; Reviewer 14715, review `95129e0c-1482-4687-90d0-4cbc431d7d86`; machine `be8bf212-1b0c-4bc9-b68c-cecf63d5d2f9`; integration `e1c1359c3fd1442d93d5a776084d00dd`, commit `542eaca02a9f2d14f175497b7bf6459436ac5c6d`. |
| [LeviInductionNormalizedTemperedStatement](../../Langlands/Representation/Exponents/LeviInductionNormalizedTemperedStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviInductionNormalizedTemperedStatement` | Statement `1b576ad6-8d0b-47a5-9327-98562e13f245`; Reviewer 14626, review `1d89e2d7-a800-454c-9089-fc4cb662877b`; machine `34d55a57-94f2-4298-a633-1ea82ef00770`; integration `386a1cc6edc442af84683d6b2c44352e`, commit `bc859155612cc8ca34e8e25175ce2f7775c217dc`. |
| [ArbitraryParabolicUnitaryJacquetPart](../../Langlands/Representation/Exponents/ArbitraryParabolicUnitaryJacquetPart.md), `Langlands.Aubert.General.RepresentedParabolic.unitaryJacquetPart` | Definition `464a3faf-28fa-4307-8be2-1d61741fab4e`; Reviewer 14628, review `2be1968c-2dfd-4f11-b514-b0f46fc167a0`; machine `44bac001-e9e7-4144-8aa1-441c74f77a36`; integration `ff63f182125e45e28e8bb16c645d8738`, commit `bc859155612cc8ca34e8e25175ce2f7775c217dc`. |
| [UnitaryJacquetPartTemperedStatement](../../Langlands/Representation/Exponents/UnitaryJacquetPartTemperedStatement.md), `Langlands.Aubert.General.RepresentedParabolic.UnitaryJacquetPartTemperedStatement` | Statement `f048dddf-dbbd-432a-a7bc-db336b5bdf05`; Reviewer 15030, review `a6a2309c-2a04-4093-ba5e-46be4fac7af7`; machine `7bf84724-9151-451f-8ed2-3ad0901d718d`; integration `b96ad3a1fb6840139efb5e7c57c9564e`, commit `50126e1b2b20b62d408b52dc3552f01089dd1d11`. |
| [TemperedJacquetUnitaryRestrictionStatement](../../Langlands/Representation/Exponents/TemperedJacquetUnitaryRestrictionStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedJacquetUnitaryRestrictionStatement` | Statement `b22affda-c1af-40c4-b00c-a776c5fe1710`; Reviewer 15049, review `e5098fd8-8a50-4ecb-a5a1-5d91bb5bb44e`; machine `26e4edeb-980b-48e5-a2fe-d3f8c50de121`; integration `4fc78dfc4420488591749a48dbebb216`, commit `50126e1b2b20b62d408b52dc3552f01089dd1d11`. |
| [TemperedInductionUnitaryReciprocityStatement](../../Langlands/Representation/Exponents/TemperedInductionUnitaryReciprocityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedInductionUnitaryReciprocityStatement` | Statement `e9e5c8a4-8c5b-4c16-9b2a-d72630d4e154`; Reviewer 15242, review `fe7f6e0b-fdbc-429d-8eb8-9239ee2f5307`; machine `9207390d-7530-4188-a2da-44327fbff9c3`; integration `6bb347763b1044f79cc092c1e1ab1043`, commit `73016647c403b942bebe18fad4e569a83c342b52`. |
| [TemperedSquareIntegrableUnitaryPartStatement](../../Langlands/Representation/Exponents/TemperedSquareIntegrableUnitaryPartStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedSquareIntegrableUnitaryPartStatement` | Statement `6769d720-7d45-4810-a8e8-6e1f221cc6b1`; Reviewer 15074, review `e96379de-ef61-4fad-b334-c4ad76b205e5`; machine `62cd6b51-2b06-48f0-87a1-93ace23ebc99`; integration `d834ec6b207248d1bede019882ee8440`, commit `50126e1b2b20b62d408b52dc3552f01089dd1d11`. |
| [TemperedGeometricLemmaStatement](../../Langlands/Representation/Exponents/TemperedGeometricLemmaStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedGeometricLemmaStatement` | Statement `6c787777-0d88-4f2f-8bf0-3a4836fcf750`; Reviewer 15563, review `bf9c195e-0807-4f12-b8d0-94d75f6ed34a`; machine `6a87755c-f96e-42f8-a6ad-977e248f0239`; integration `1837b3dff62f43758bfbebbc80ce4e35`, commit `8fb2236bacd54b43eeb9b2fabc30476fee771e05`. |
| [TemperedIrreducibleDiscreteSeriesStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesStatement` | Statement `7ec947da-c7f6-4657-83d3-d7d2640d1330`; Reviewer 14652, review `a469d1f8-8e46-4e11-b3bf-b8db74ac311c`; machine `15056576-38bd-4bcc-878b-535391b4ec91`; integration `cdfca6b06b1440f997980e0ad957cb67`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |
| [TemperedIrreducibleDiscreteSeriesUniquenessStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesUniquenessStatement` | Statement `f0746b32-8a53-4b31-9532-b9858edb398e`; Reviewer 14656, review `fe9595e8-7142-4df8-b0ce-b7475281338e`; machine `29d5aac6-e4a3-4bc8-b7be-9dc2bff18fef`; integration `7dc3c7419955495cb33098fab0a3b658`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |
| [TemperedIrreducibleUnitarizableStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleUnitarizableStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleUnitarizableStatement` | Statement `4c655cac-7ae3-477d-83cb-6fc0ee7f1666`; Reviewer 14658, review `4d20b6d9-f0bd-4b7c-8142-569af9617766`; machine `d782ccff-3f4d-4257-baed-a7259a4b32a2`; integration `7223cceebed9435d804ec36dec389230`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |
| [LeviParabolicTransitivityStatement](../../Langlands/Representation/Exponents/LeviParabolicTransitivityStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviParabolicTransitivityStatement` | Statement `dcbd5c69-035d-422e-8aef-6ad4674abb87`; Reviewer 16427, review `7f9ed87d-ccca-461e-bc1c-ad6a08b6677c`; machine `225d176b-dd8f-4254-83b8-11084ec63375`; integration `3f69358f84514a308d0b925f56d70e2a`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [LeviJacquetOppositePairingStatement](../../Langlands/Representation/Exponents/LeviJacquetOppositePairingStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviJacquetOppositePairingStatement` | Statement `c22cf8dd-6f31-47e6-8bc6-0274fe417e42`; Reviewer 16345, review `dd1732f7-c6fe-4ab1-8170-818f85cf0f7e`; machine `f5e86ddc-b57f-4a4c-bf23-60ff28d2a9cd`; integration `1d79ead29d1b491296146a98841d6b3e`, commit `334440350ec029c1bf78b7801689e1a2b21079c6`. |
| [LeviCompletionOppositeJacquetStatement](../../Langlands/Representation/Exponents/LeviCompletionOppositeJacquetStatement.md), `Langlands.Aubert.General.RepresentedParabolic.LeviCompletionOppositeJacquetStatement` | Statement `51570ccf-30db-49af-a5ba-9300df49da5b`; Reviewer 16425, review `6ae0f9cf-be5b-4e04-b6fb-911475c5a88f`; machine `2dd8885f-8faf-4b73-8f5c-b38a9446bda3`; integration `f18fa0fd0e5646ef8168573dadac078b`, commit `6f182f920309bbe9e9e43bd7181d7e25d5c02acd`. |
| [StandardFixedVectorSubquotientGenerationStatement](../../Langlands/Representation/Jacquet/StandardFixedVectorSubquotientGenerationStatement.md), `Langlands.Jacquet.StandardFixedVectorSubquotientGenerationStatement` | Statement `e23f2e02-1e67-49c3-920a-9b5e3ea3fe28`; Reviewer 17496, review `96c79db1-a002-4aef-87c3-ce62507cc5a7`; machine `b55d383b-35fd-410b-b946-000d3a0a53bc`; integration `bd2650eac72349b6a93278cfe6ae41c9`, commit `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`. |
| [StandardFixedVectorHeckeEquivalenceStatement](../../Langlands/Representation/Jacquet/StandardFixedVectorHeckeEquivalenceStatement.md), `Langlands.Jacquet.StandardFixedVectorHeckeEquivalenceStatement` | Statement `b1a5415e-9133-4093-a0d9-1cc988541c21`; Reviewer 17497, review `c2298f75-9de6-4688-bf68-b0b28bc6b96a`; machine `6449a803-4127-4763-be3e-6268b5aa160a`; integration `9b8685af86a6490db1e94ed5ec7cbece`, commit `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`. |

The first twenty declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`. The two VI.9.4 statements are in
namespace `Langlands.Jacquet` under `Langlands/Representation/Jacquet/`.
The completion definitions used by the VI.9.7 statement are in
[CompactCompletion](../../Langlands/Representation/Smooth/CompactCompletion.md),
namespace `Langlands.CompactCompletion`, submitted in the same candidate
`51570ccf`.

## Common setting

Every statement except the two VI.9.4 statements quantifies over a
nonarchimedean local field `k : Type u` of any characteristic, with `[ValuativeRel k]`, its topology and
`[T2Space k]`, and over an actual connected reductive group scheme `G` over
`Spec k`. The rational points carry the canonical
`RationalPointFamily.pointTopology`; `[LocallyCompactSpace]` and
`[NonarchimedeanGroup]` for that topology are hypotheses. A parabolic datum
is an actual rational parabolic `p : P ⟶ G`, a rational Levi `l : M ⟶ P`
and a matching geometric unipotent radical `r : U ⟶ P` with
`IsIso (subgroupMultiplication l r)`; no standardness is assumed. The Levi
points carry `leviPointTopology`, and their local compactness and
nonarchimedean structure are derived from those of `G(F)`. The two VI.9.4
statements instead quantify over a nonarchimedean local field `F : Type uF`
with `[ValuativeRel F]` and an actual connected reductive `G` whose rational
points carry `rationalPointTopology`, with no local-compactness hypothesis;
their parabolics are the standard ones described in their section.

The functors are the published normalized `leviInductionFunctor`
(`i_P^G`) and `leviJacquetFunctor` (`r_P^G`) of the represented-parabolic
interface. Renard's `δ_P` is the inverse of the usual Haar modulus, so his
twists by `δ_P^{-1/2}` and `δ_P^{1/2}` in (VI.1.2.1)–(VI.1.2.2) are the
published square-root twists. Temperedness is the published derived
predicate `IsNormalizedExponentTempered` of the companion map.

## VI.1.2 and VI.1.3: the normalized functors

Source: VI.1.2, Proposition and Corollary, and VI.1.3, Proposition,
printed p.136 / PDF p.142.

- `LeviFrobeniusReciprocityStatement`: for every smooth `π` of `G(F)` and
  `σ` of `M(F)`, with independent carrier universes, there is a linear
  equivalence from intertwiners `π → i_P^G σ` to intertwiners
  `r_P^G π → σ` sending `F` to `[x] ↦ (F x)(1)`. This is the adjunction
  part of the Proposition, as an explicit bijection.
- `LeviParabolicFunctorsExactStatement`: both functors send every actual
  short exact sequence (`SmoothRep.IsShortExact`) to a short exact sequence.
- `LeviParabolicFunctorsPreserveLimitsStatement`: `i_P^G` preserves limits
  and colimits and `r_P^G` preserves colimits, for diagrams with index
  categories and morphisms in `Type v`. The explicit sizes
  `PreservesLimitsOfSize.{v, v}` and `PreservesColimitsOfSize.{v, v}` are
  needed because the carrier universe of `i_P^G` changes.
- `LeviJacquetFiniteTypeStatement`: if `π` is finitely generated over
  `ℂ[G(F)]`, then `r_P^G π` is finitely generated over `ℂ[M(F)]`. Only the
  normalized assertion is stated.

The unnormalized Theorem of VI.1.1 is not stated separately.

## VI.1.4: transitivity

Source: VI.1.4, the paragraph before the Lemma, the Lemma and its proof,
printed pp.136–137 / PDF pp.142–143.

`LeviParabolicTransitivityStatement` takes three actual rational parabolic
triples: `P = MN` and `Q = LU` in `G`, and `P_L = M N_L` in `L` with the
same Levi group scheme `M`. It assumes `P(F) ⊆ Q(F)`, that `M` sits in `G`
through `P_L ⊂ L ⊂ Q` by the same embedding as through `P`, and
`P_L(F) = L(F) ∩ P(F)`. These hypotheses describe Renard's `L ∩ P`, which
the interface cannot form as an intersection of group schemes. It asserts
natural isomorphisms `i_P^G ≅ i_{P_L}^L ⋙ i_Q^G` and
`r_P^G ≅ r_Q^G ⋙ r_{P_L}^L` of functors on all smooth representations,
for an arbitrary carrier universe. The local compactness and
nonarchimedean structure of `L(F)` are derived, not assumed. The published
`DynamicNestedParabolicTransitivityStatement` and its proof in
`Langlands/Representation/Aubert/General/` are the version for dynamic
parabolics, with the radical decompositions as a visible input.

## VI.9.6: second adjointness and the pairing

Source: VI.9.6, first and second Theorems, printed p.201 / PDF p.207, with
the proof of their equivalence on printed pp.201–202 / PDF pp.207–208; the
Proposition, printed p.202 / PDF p.208, with its proof on printed
pp.202–205 / PDF pp.208–211.

The three statements take a second actual rational parabolic triple
`pbar : Pbar ⟶ G`, `mbar : M ⟶ Pbar`, `nbar : Nbar ⟶ Pbar` with the same
Levi group scheme, and assume `mbar ≫ pbar = m ≫ p` and
`pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)`. These say that the
two triples have the same Levi embedding and that `P(F) ∩ P̄(F) = M(F)`,
which describes the opposite parabolic. Constructing the opposite as actual
group-scheme data is not addressed.

- `LeviSecondAdjointnessStatement`: `Nonempty (i_P^G ⊣ r_{P̄}^G)` as a
  Mathlib adjunction, (VI.9.6.1). Both functors are taken with carriers in
  `Type (max u v)` so that they relate the same two categories.
- `LeviJacquetContragredientStatement`: a natural isomorphism
  `π ↦ r_{P̄}^G(π̃) ≅ π ↦ (r_P^G π)~` of functors on all smooth
  representations with carriers in `Type v`, (VI.9.6.2), with the published
  `SmoothRep.contragredientFunctor`.
- `LeviJacquetOppositePairingStatement` (Proposition): for every smooth
  `π` there is an isomorphism `E : r_{P̄}^G(π̃) ≅ (r_P^G π)~` such that the
  pairing `⟨x, y⟩_P = E(y)(x)` satisfies (VI.9.6.4) and (VI.9.6.5). For
  every split component `A` of `M`, every published
  `ParabolicRootPresentation` of `P` relative to it, and all `v ∈ V` and
  `λ ∈ Ṽ`:
  `⟨r_P^G(π)(t^j)·j_N(v), j_{N̄}(λ)⟩_P = δ_P^{1/2}(t^j) λ(π(t^j)v)` for
  every `t ∈ CocharacterUniformizer.CAstrict` (Renard's `C_A^{++}`) and all
  large `j`; and for some `ε > 0`, depending on `v` and `λ`, the same
  identity holds for every `t` in `CocharacterUniformizer.CAepsilon`
  (Renard's `C_A^+(ε)`). One `E` serves
  every presentation. `E` is not asserted to be natural in `π`, the
  existence of presentations is not asserted, and no implication between
  this statement and `LeviJacquetContragredientStatement` is asserted.

No admissibility, finite length or finite type is assumed. The source
proves (VI.9.6.2) through the pairing (VI.9.6.4), built from the
generalized Jacquet lemma VI.9.1–VI.9.3. That lemma uses Iwahori
decompositions with respect to `P` and `P̄` and contracting elements of the
split component.

Workers 1402 and 937 published conditional reductions of the two Theorems.
Their theorems are proved and keep the listed statements as hypotheses.

| Theorem and module | Premises | Conclusion |
| --- | --- | --- |
| `leviSecondAdjointness_of_structure`, `LeviSecondAdjointnessStructure` (Worker 1402) | `ParabolicDynamicStatement`, `OppositeDynamicParabolicUniquenessStatement`, `UniformCompressionStabilizationStatement` at carrier universe `max u v`, `LeviAdjointDeterminantReciprocityStatement`, `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`, `ArbitraryParabolicQuotientCompactStatement` | `LeviSecondAdjointnessStatement` |
| `leviJacquetContragredient_of_structure`, `LeviJacquetContragredientStructure` (Worker 937) | the first four premises of the previous row, with `UniformCompressionStabilizationStatement` at carrier universe `v` | `LeviJacquetContragredientStatement` |

Each module also proves a variant, ending in
`_of_reflection_centralSplitTorus`, in which
`RelativeRootReflectionExistenceStatement` and
`CentralSplitTorusCharacterStatement` replace
`LeviAdjointDeterminantReciprocityStatement`. The implications are also
published as the named statements `LeviSecondAdjointnessFromInputsStatement`
and `LeviJacquetContragredientFromInputsStatement`, with proofs by Workers
1402 and 937. Of the premises, `OppositeDynamicParabolicUniquenessStatement`
is proved, by `Langlands.GroupScheme.oppositeDynamicParabolicUniqueness`
(Workers 135 and 1650). At Library `eec7519b`, a search for theorems whose
type is one of the other premises found no unconditional proof, only
conditional reductions for some of them. Among these, the internal assembly
`uniformCompressionStabilization_of_nativeStatements` in
`UniformCompressionNativeAssembly` (artifact
`6f37b42c-2a85-4b5b-a7b1-ce185eb2a981`) derives
`UniformCompressionStabilizationStatement` from thirteen named Library
statements. One of them is the VI.9.2 Jacquet-family finiteness statement
`RationalSupercuspidalJacquetFamilyFiniteStatement`, which no theorem of the
Library proves; the modules `StandardCompressionGeometry` and
`StandardCuspidalNativeJacquetInputs` also take it only as a hypothesis. The search found no theorem whose type is the pairing
Proposition or the VI.9.7 statement.

Workers 937 and 1587 published derived partial statements of the Theorem
and the Proposition of VI.9.1 (printed pp.195–197 / PDF pp.201–203):
`GeneralizedJacquetLemmaStatement` and
`UniformCompressionStabilizationStatement` in the module
[UniformCompressionStabilizationStatement](../../Langlands/Representation/Exponents/UniformCompressionStabilizationStatement.md)
(artifact `bb2fbd21-111b-4b02-8f0e-9e2d1a35f3c1`, statement task
`f0a4d6b4-8a85-4ce9-972d-7e4958be7bb2`). Their paired Markdown records how
they differ from the source:

- They use dynamic parabolics `P_G(χ)` with the centralizer Levi and the
  opposite radical. The comparison with arbitrary actual parabolics is the
  separate target `ParabolicDynamicStatement` and is not part of them.
- In place of `t ∈ C_A^{++}`, both take an element `g` that is central in
  `M(F)` and satisfies `Jacquet.IsIwahoriContraction K N M N̄ g`. For the
  Theorem this hypothesis on `K` is stronger than the source's Iwahori
  decomposition alone, so the statement covers fewer subgroups `K`.
- The exponent `b` of the Proposition is chosen after `χ`, `K` and `g`. It
  is uniform over the smooth representations only once these are fixed. The
  source's dependence `b = b(G, K)` is not asserted.
- Three source assertions are not stated: the identification of the
  localization of `V^K` at `A` with `(V^K_*, A|V^K_*)`, the bound
  `b ≤ c(G, K)` by the uniform admissibility constant of VI.2.3, and
  Remarks 1–3 (printed p.197 / PDF p.203, proofs continuing on PDF p.204).

The two proof obligations have separate tasks:
`47e556e6-6b2a-40dc-ba66-d6a0585f5220` proves only
`UniformCompressionStabilizationStatement`, and
`cac6f709-2a1b-4eaa-a16d-63f2e40f3b29` proves
`GeneralizedJacquetLemmaStatement`. VI.9.2 and VI.9.3 prove the
Proposition of VI.9.1; the
[VI.9.1–VI.9.3 map](uniform-compression-progress.md) records their steps.
The consequences in VI.9.4 are stated in the next section. VI.9.5
(preservation of `B`-admissibility by `r_P^G`) is not stated; it needs the
category of `(G, B)`-modules of VI.8.3.

## VI.9.4: generation by `K`-fixed vectors

Source: VI.9.4, Corollary and Proposition, printed pp.200–201 / PDF
pp.206–207. Renard deduces the Corollary as the Corollary of VI.6.3
(printed p.179 / PDF p.185) without its admissibility hypothesis, by the
generalized Jacquet lemma, and the Proposition from the Corollary by the
Theorem of I.3.2 (printed p.22 / PDF p.28).

The two statements share their data and hypotheses, on the standard family
rather than on a represented parabolic. An actual maximal split torus
`i : S.toGrp ⟶ G` and a generic cocharacter `ν` fix the standard
parabolics, indexed by `J ⊆ simpleRelativeRoots i ν`, with points
`standardLeviPoints i ν J` and `standardUnipotentPoints i ν J`. The
hypothesis `_hstandard` supplies a standard cocharacter for every `J`. A
compact subgroup `K₀` satisfies only the Iwasawa factorization `g = m n k`
with `m ∈ M_∅(F)`, `n ∈ N_∅(F)` and `k ∈ K₀`. The compact open `K` satisfies
`K ≤ K₀`, `K₀ ≤ Subgroup.normalizer K` and, for every standard `J`,
`IsCompatibleStandardSplitComponent i ν J A q` and
`StandardParabolicBasisMember i ν J q K` for some split torus `A` and
`q : A.toGrp ⟶ S.toGrp`. The last predicate is one member of the V.5.2
basis, clauses (ii)–(iv). "Generated by its `K`-fixed vectors" means that
every subrepresentation whose submodule contains the `K`-fixed vectors is
`⊤`.

- `StandardFixedVectorSubquotientGenerationStatement`: for every smooth
  `V` generated by its `K`-fixed vectors, every subquotient
  (`SmoothRep.IsSubquotient`) is generated by its `K`-fixed vectors. No
  admissibility or finiteness hypothesis is made.
- `StandardFixedVectorHeckeEquivalenceStatement`: on the full subcategory
  of representations generated by their `K`-fixed vectors, the functor
  `P.ι ⋙ Langlands.Shimura.LevelHecke.heckeModuleFunctor ℂ K.toSubgroup`
  to `ModuleCat (LevelHeckeAlgebra ℂ K.toSubgroup)` is an equivalence.

The statements are derived partial coverage of VI.9.4. The source assumes a
compact open `K` contained and normal in `K₀` that admits an Iwahori
decomposition `K = K_N̄ K_M K_N` along every standard parabolic, the
decomposition named in V.5.2 (ii) (printed p.123 / PDF p.129). It does not
assume that `K` is an Iwahori subgroup. `StandardParabolicBasisMember`
conjoins this decomposition (`HasIwahoriIntersectionDecomposition`) with
`ContractionAndCofinality`, the remaining conditions of V.5.2 (ii)–(iv).
The published hypothesis may therefore be stronger than the source's, and
the statements may cover fewer subgroups `K`; they cover every member of the
V.5.2 neighbourhood basis, hence arbitrarily small `K`. Three points remain
open besides the proofs: the statements for the source's class of `K`,
without the additional
V.5.2 (ii)–(iv) conditions; the comparison of `LevelHeckeAlgebra` with the
Haar-measure corner `e_K H(G) e_K`; and an explicit inverse functor. Neither
statement is proved. Their proof task
routes the Corollary through the proved compact-open detection
consequences, compact-restriction detection and algebraic VI.6.3 Lemma, and
lists the unproved inputs: the norm-kernel finite restriction, the VI.2.1
cuspidal embedding and the generalized Jacquet lemma of VI.9.1.

## VI.9.7: second adjointness and completion

Source: VI.9.7, Theorem, printed p.205 / PDF p.211, with its proof on
printed pp.205–206 / PDF pp.211–212; the completion of I.1.4, printed
pp.9–10 / PDF pp.15–16.

`LeviCompletionOppositeJacquetStatement` has the ambient data of the VI.9.6
statements. It asserts a family of linear isomorphisms
`φ_π : V̄^N ≃ \overline{r_{P̄}^G(V)}`, one for every smooth `π`, between the
`N(F)`-fixed part `completionFixed` of the completion of `V` and the
completion of the normalized Jacquet module. The completions are spaces of
compatible families indexed by compact open subgroups, as in the source
proof. It asserts two properties:

- **Characterization.** `φ_π(x)_{K_M} = j_{N̄}(x_K)` for every compact open
  `K` of `G(F)` for which some `g` central in `M(F)` satisfies
  `Jacquet.IsIwahoriContraction` with the roles of `N` and `N̄` exchanged,
  and every compact open `K_M` of `M(F)` with image `K ∩ M(F)`. This class
  of `K` follows the published `GeneralizedJacquetLemmaStatement`.
- **Naturality.** For a morphism `f : π → σ` and families `x`, `y` with
  `y_K = f(x_K)` for every `K`, the components of `φ_σ(y)` are the images
  of those of `φ_π(x)` under `r_{P̄}^G(f)`.

The statement does not assert uniqueness, cofinality of the subgroups
`K ∩ M(F)`, `M(F)`-equivariance of `φ`, or the comparison of the
normalized and unnormalized completions.

## VII.1.3: reducibility for maximal Levi subgroups

Source: VII.1.3, Theorem and proof, printed pp.224–226 / PDF pp.230–232.

`MaximalLeviSupercuspidalReducibilityStatement` takes a proper parabolic
(`¬ IsIso p`) that is maximal: no actual parabolic lies strictly between
`P` and `G`. Supercuspidality of an irreducible `ρ` of `M(F)` is
triviality of every proper normalized Jacquet module of `ρ`. If
`i_P^G ρ` is not irreducible, the statement asserts some
`g ∉ pointImage (l ≫ p)` and some `φ : M ≅ M` with
`φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso g).hom`. It also asserts a positive
real-valued `ψ` among the published unramified characters of `M(F)`, and a
linear equivalence `T` of `ρ` intertwining `ρ` with `(ψ · ρ) ∘ φ`. This
expresses the source's `M = M'` and `ρ^w = ρψ` without standard Levi
subgroups. The Corollary of VII.1.3 is not stated; it needs Bernstein
components.

## VII.2.2–VII.2.4: induction, unitary parts and reciprocity

Source: VII.2.2, Lemma, printed pp.227–228 / PDF pp.233–234; VII.2.3,
printed p.229 / PDF p.235; VII.2.4, printed pp.229–230 / PDF pp.235–236.

- `LeviInductionNormalizedTemperedStatement`: if `σ` is tempered, so is
  `i_P^G σ`.
- `ArbitraryParabolicUnitaryJacquetPart` defines `unitaryJacquetPart` and
  `nonunitaryJacquetPart` for a parabolic datum and a split component
  `a`. They are the suprema of the generalized weight spaces of the
  normalized Jacquet module over exponents with zero and with nonzero
  `normalizedRealPart`. The module also defines the corresponding
  representations `leviUnitaryJacquetModule` and
  `leviNonunitaryJacquetModule` of `M(F)` with their inclusions, such as
  `leviUnitaryJacquetModuleι`. It proves only elementary lattice facts and
  these transports.
- `UnitaryJacquetPartTemperedStatement` (VII.2.3, Lemma): for tempered `π`,
  the two parts are complementary subspaces, and `leviUnitaryJacquetModule`
  is tempered. The parabolic is arbitrary instead of standard, and the
  direct sum, which the source takes from VII.1.1, is part of the
  conclusion.
- `TemperedJacquetUnitaryRestrictionStatement` (VII.2.4, Proposition,
  second step): for tempered `π` and `σ`, restriction along
  `leviUnitaryJacquetModuleι` is a bijection from intertwiners
  `r_P^G π → σ` to intertwiners from the unitary part to `σ`.
- `TemperedInductionUnitaryReciprocityStatement` (VII.2.4, Proposition):
  for tempered `π` and `σ` with independent carrier universes, there is a
  linear equivalence from intertwiners `π → i_P^G σ` to intertwiners from
  the unitary part to `σ`, with `e F y = (F x)(1)` whenever `y` is the
  unitary-part element whose image in `r_P^G π` is the class of `x`.
- `TemperedSquareIntegrableUnitaryPartStatement` (VII.2.4, Lemma): for
  tempered `π` with a central character `ω` on the full point-group
  center, `π` is square-integrable modulo the center for the supplied Haar
  measure if and only if the unitary part vanishes for every proper actual
  parabolic datum and split component. It retains the measure hypotheses of
  the published Casselman statement.

## VII.2.5: the tempered geometric lemma

Source: VII.2.5, Proposition and proof, printed p.230 / PDF p.236.

`TemperedGeometricLemmaStatement` takes two actual rational parabolic data
`P = MN` and `Q = LU`, a split component of `L` and a tempered `ρ` of
`M(F)`. It asserts representatives `z i` meeting every double coset of
`P(F)` and `Q(F)` in `G(F)` exactly once, with intersection data of the
published `RepresentedGeometricLemmaStatement` of Worker 1585 (VI.5.1). For
every choice of split components of the Levis `M ∩ zLz⁻¹`, it asserts an
actual finite filtration of the unitary part `(r_Q^G i_P^G ρ)_0` and a
permutation of the pieces. The graded pieces are isomorphic to
`i^L_{L ∩ z⁻¹Pz}` of the transported unitary part
`(r^M_{M ∩ zQz⁻¹} ρ)_0`. The helper definition
`GeometricLemmaIntersectionDatum.unitaryPieceRep` forms these pieces. The
specific set `W_{Q,P}` of V.4.7 is not used. Naturality in `ρ` and
compatibility with the VI.5.1 filtration are not asserted.

## VII.2.6: tempered representations and discrete series

Source: VII.2.6, Theorem and Corollary, printed pp.231–232 /
PDF pp.237–238.

A *discrete* representation of `M(F)` below is irreducible and
square-integrable modulo the center for every Borel Haar measure on the
quotient by the full center. An embedding is an injective intertwiner into
`i_P^G σ`.

- `TemperedIrreducibleDiscreteSeriesStatement`: an irreducible `π` is
  tempered if and only if it embeds into `i_P^G σ` for some actual
  parabolic datum and some discrete `σ`.
- `TemperedIrreducibleDiscreteSeriesUniquenessStatement`: for two such
  embeddings of an irreducible `π`, there are `g : G(F)` and
  `φ : M₁ ≅ M₂` with `φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom`, and a
  linear equivalence `σ₁ ≃ σ₂` intertwining `σ₁` with `σ₂ ∘ φ`.
- `TemperedIrreducibleUnitarizableStatement`: an irreducible tempered `π`
  satisfies the published algebraic predicate `IsUnitarizable`.

## Proof tasks

| Targets | Proof task |
| --- | --- |
| The four VI.1.2 and VI.1.3 statements | `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b` |
| `LeviParabolicTransitivityStatement` | `3d8ef03e-d98f-4e3a-bf48-0443629a56c6` |
| The two VI.9.6 Theorems | `c0fa1878-6cee-4435-8484-2fc15ea04a17` |
| `LeviJacquetOppositePairingStatement`, `LeviCompletionOppositeJacquetStatement` | `56c26504-4137-427a-b822-7b99d4769f48` |
| `MaximalLeviSupercuspidalReducibilityStatement` | `004e00e1-5995-4dc1-884e-a5f512150d0c` |
| `LeviInductionNormalizedTemperedStatement` | `f83123b9-ff38-4210-9ad7-4f119a13d1ac` |
| `UnitaryJacquetPartTemperedStatement`, `TemperedJacquetUnitaryRestrictionStatement`, `TemperedSquareIntegrableUnitaryPartStatement` | `f0ff1d42-b2ac-439b-a08d-8e2d120a78fa` |
| `TemperedInductionUnitaryReciprocityStatement` | `71b5958c-b2a2-4a70-a4f0-537ed8d5a152` |
| The three VII.2.6 statements | `225f7d3d-bb91-4746-9084-ea6b91241e41` |
| `TemperedGeometricLemmaStatement` | `65c3d5dc-0e10-442e-93ee-f13854e419bb` |
| The two VI.9.4 statements | `e8bd5ada-24df-4009-8256-ca4317b4190d` |

Worker 6 published these tasks. Worker 1670 published the proof tasks of
the represented-parabolic Jacquet-admissibility statement
(`56206cc7-3e1e-4fae-840d-f5e8ccffd8ed`) and of the parabolic
quotient-compactness statement (`c1ce4629-6768-4eb5-b4ee-0086526913ea`).
Worker 1585 published the proof task of the represented geometric lemma
(`c060fb34-b423-4ac5-8448-788ac7627913`). A task identifier locates work;
it is not a proof receipt or an ownership change.

## Published proofs

Five of the statements are proved in the Library, by other workers. Each
theorem has the exact published statement as its type.

| Statement | Theorem and proof module | Authors, task |
| --- | --- | --- |
| `LeviFrobeniusReciprocityStatement` | `leviFrobeniusReciprocity`, `LeviFrobeniusReciprocityProof` | Worker 16, `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b` |
| `LeviParabolicFunctorsExactStatement` | `leviParabolicFunctorsExact`, `LeviParabolicFunctorsExactProof` | Worker 16, `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b` |
| `TemperedJacquetUnitaryRestrictionStatement` | `temperedJacquetUnitaryRestriction`, `TemperedJacquetUnitaryRestrictionProof` | Workers 1629 and 1593, `f0ff1d42-b2ac-439b-a08d-8e2d120a78fa` |
| `TemperedInductionUnitaryReciprocityStatement` | `temperedInductionUnitaryReciprocity`, `TemperedInductionUnitaryReciprocityProof` | Worker 837, `71b5958c-b2a2-4a70-a4f0-537ed8d5a152` |
| `LeviParabolicTransitivityStatement` | `leviParabolicTransitivity`, `LeviParabolicTransitivityProof` | Workers 1754 and 1373, `3d8ef03e-d98f-4e3a-bf48-0443629a56c6` |

Both VI.1.2 proofs prove, rather than assume, the compact-subgroup property
of the rational points of the radical; the Frobenius proof also proves
their unimodularity. The restriction proof derives
complementarity of the two parts from temperedness, through
`IsNormalizedExponentTempered.unitaryJacquetPart_isCompl`, and applies the
restriction bijection of `TemperedJacquetRestriction`. The reciprocity
proof is a single term: the conditional assembly
`temperedInductionUnitaryReciprocity_of` of
`TemperedInductionUnitaryReciprocityReduction`, applied to the Frobenius
and restriction proofs. Task `71b5958c` is completed. The other two
targets of each of `27fe1be6` and `f0ff1d42` are not proved.

The transitivity proof is proof artifact
`a3de9b5e-020c-43d0-aa88-9458e2cf1527`, accepted by Reviewer 17047 (review
task `13c7e935-91d7-41d4-b53a-4e31243780aa`) and published by integration
`e1fd9172405d404aabe75f0f6e12da0b` at commit
`f73044d93e675a78ed75830ef026b3224514e510`. It is a single application:
the proved `nestedParabolicPointDecomposition` (module
`Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof`)
shows `N_L(F) = L(F) ∩ N(F)` and `N(F) = (L(F) ∩ N(F)) U(F)` inside
`G(F)`, and the adapter `leviParabolicTransitivity_of_radical_decomposition` of
`LeviParabolicTransitivityReduction` (Worker 1373, with Worker 1754's
interface) turns these identities into the two natural isomorphisms.

Several published supporting modules by proof-task workers retain their
inputs as premises and prove none of the remaining targets. They include
`ArbitraryParabolicUnitarity`, `TemperedIrreducibleUnitarityReduction`
(Worker 346) and `ParabolicPresentationUnitarity`, which build invariant
forms toward the VII.2.6 Corollary; and
`MaximalLeviReducibilityUnitaryInputs` and
`MaximalLeviReducibilityReductionStatements` (Worker 1507), which separate
the VII.1.3 proof into statements. Worker 1507's
`MaximalLeviSupercuspidalReducibilityFromInputsStatement` asserts that
`MaximalLeviSupercuspidalReducibilityStatement` follows from eleven
published propositions, among them `ParabolicDynamicStatement`,
admissibility of irreducible representations (VI.2.2) and compactness of
`P(F)\G(F)`. Worker 1517's `MaximalLeviSupercuspidalReducibilityFromInputsProof`
proves that implication. VII.1.3 itself follows once those premises are
proved.

## Remaining obligations

1. Proofs of the sixteen statements above that are not proved, through
   the listed tasks. They need structural facts that are themselves open for
   arbitrary actual parabolics, among them compactness of `P(F)\G(F)`, Jacquet
   admissibility, Iwahori decompositions and contracting elements.
2. Statements of VII.3 and VII.4, and of the VII.1.3 Corollary.
   VII.3 also needs representatives of Weyl double cosets for actual
   parabolics. VII.4 needs Langlands chambers with relative coroots.
   The VII.1.3 Corollary needs Bernstein components.
3. The statement of VI.9.5, which needs the `(G, B)`-modules of VI.8.3.
   For VI.9.4: the two statements for every compact open `K` contained and
   normal in `K₀` with Iwahori decompositions along the standard
   parabolics, without the further conditions of V.5.2 (ii)–(iv); the
   comparison of `LevelHeckeAlgebra` with `e_K H(G) e_K`; and an explicit
   inverse functor. For VI.9.1: the proofs of
   `UniformCompressionStabilizationStatement` (task `47e556e6-6b2a-40dc-ba66-d6a0585f5220`) and of
   `GeneralizedJacquetLemmaStatement` (task
   `cac6f709-2a1b-4eaa-a16d-63f2e40f3b29`); statements of the localization
   identification, the bound `b ≤ c(G, K)`, the dependence `b = b(G, K)` and
   Remarks 1–3; the Theorem for every `K` with an Iwahori decomposition; and
   the transfer from dynamic to arbitrary actual parabolics.

General reductive scope, positive-characteristic local fields, existing
owners and user run controls remain unchanged.
