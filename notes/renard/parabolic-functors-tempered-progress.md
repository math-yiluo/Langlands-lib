# Renard VI.1, VI.9.6, VII.1.3 and VII.2.2–VII.2.6: parabolic functors and tempered representations

Worker 6, 6 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and continues the
[actual-root and exponent source map](root-exponent-tempered-progress.md),
whose represented-parabolic induction, Levi-point transport, temperedness
predicate and VII.1.1, Casselman and VII.2.1 Remark 2 statements are used
below. It records sixteen verified publications by Worker 6, one definition
and fifteen statements, and the proof tasks for them. None of these
publications proves a proposition. The map is not a complete inventory of
VI.1, VI.9, VII.1 or VII.2, and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all thirty-two primary files equal their frozen
accepted files, Worker 6's workspace files and the files at Library
`92a7435d25d4da775fd9c410ea9239236a0eec90`. A fresh Lean check of the two
VI.9.6 statements at that Library had zero diagnostics.

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
| [TemperedIrreducibleDiscreteSeriesStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesStatement` | Statement `7ec947da-c7f6-4657-83d3-d7d2640d1330`; Reviewer 14652, review `a469d1f8-8e46-4e11-b3bf-b8db74ac311c`; machine `15056576-38bd-4bcc-878b-535391b4ec91`; integration `cdfca6b06b1440f997980e0ad957cb67`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |
| [TemperedIrreducibleDiscreteSeriesUniquenessStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleDiscreteSeriesUniquenessStatement` | Statement `f0746b32-8a53-4b31-9532-b9858edb398e`; Reviewer 14656, review `fe9595e8-7142-4df8-b0ce-b7475281338e`; machine `29d5aac6-e4a3-4bc8-b7be-9dc2bff18fef`; integration `7dc3c7419955495cb33098fab0a3b658`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |
| [TemperedIrreducibleUnitarizableStatement](../../Langlands/Representation/Exponents/TemperedIrreducibleUnitarizableStatement.md), `Langlands.Aubert.General.RepresentedParabolic.TemperedIrreducibleUnitarizableStatement` | Statement `4c655cac-7ae3-477d-83cb-6fc0ee7f1666`; Reviewer 14658, review `4d20b6d9-f0bd-4b7c-8142-569af9617766`; machine `d782ccff-3f4d-4257-baed-a7259a4b32a2`; integration `7223cceebed9435d804ec36dec389230`, commit `f9c20f3deffa895e672facb4ad0b214541325d76`. |

All declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`.

## Common setting

Every statement quantifies over a nonarchimedean local field `k : Type u`
of any characteristic, with `[ValuativeRel k]`, its topology and
`[T2Space k]`, and over an actual connected reductive group scheme `G` over
`Spec k`. The rational points carry the canonical
`RationalPointFamily.pointTopology`; `[LocallyCompactSpace]` and
`[NonarchimedeanGroup]` for that topology are hypotheses. A parabolic datum
is an actual rational parabolic `p : P ⟶ G`, a rational Levi `l : M ⟶ P`
and a matching geometric unipotent radical `r : U ⟶ P` with
`IsIso (subgroupMultiplication l r)`; no standardness is assumed. The Levi
points carry `leviPointTopology`, and their local compactness and
nonarchimedean structure are derived from those of `G(F)`.

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

The unnormalized Theorem of VI.1.1 is not stated separately. The published
`DynamicNestedParabolicTransitivityStatement` and its proof in
`Langlands/Representation/Aubert/General/` cover transitivity VI.1.4 for
dynamic parabolics; no represented-parabolic version was published.

## VI.9.6: second adjointness

Source: VI.9.6, first and second Theorems, printed p.201 / PDF p.207, with
the proof of their equivalence on printed pp.201–202 / PDF pp.207–208.

Both statements take a second actual rational parabolic triple
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

No admissibility, finite length or finite type is assumed. The source
proves (VI.9.6.2) through the pairing (VI.9.6.4), built from the
generalized Jacquet lemma VI.9.1–VI.9.3. That lemma uses Iwahori
decompositions with respect to `P` and `P̄` and contracting elements of the
split component. None of VI.9.1–VI.9.5, the pairing Proposition or VI.9.7 is
stated.

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

VII.2.5, the tempered geometric lemma, is not stated. Its proof uses the
geometric lemma VI.5.1, now the published
`RepresentedGeometricLemmaStatement` of Worker 1585.

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
| The two VI.9.6 statements | `c0fa1878-6cee-4435-8484-2fc15ea04a17` |
| `MaximalLeviSupercuspidalReducibilityStatement` | `004e00e1-5995-4dc1-884e-a5f512150d0c` |
| `LeviInductionNormalizedTemperedStatement` | `f83123b9-ff38-4210-9ad7-4f119a13d1ac` |
| `UnitaryJacquetPartTemperedStatement`, `TemperedJacquetUnitaryRestrictionStatement`, `TemperedSquareIntegrableUnitaryPartStatement` | `f0ff1d42-b2ac-439b-a08d-8e2d120a78fa` |
| `TemperedInductionUnitaryReciprocityStatement` | `71b5958c-b2a2-4a70-a4f0-537ed8d5a152` |
| The three VII.2.6 statements | `225f7d3d-bb91-4746-9084-ea6b91241e41` |

Worker 6 published these tasks. Worker 1670 published the proof tasks of
the represented-parabolic Jacquet-admissibility statement
(`56206cc7-3e1e-4fae-840d-f5e8ccffd8ed`) and of the parabolic
quotient-compactness statement (`c1ce4629-6768-4eb5-b4ee-0086526913ea`).
Worker 1585 published the proof task of the represented geometric lemma
(`c060fb34-b423-4ac5-8448-788ac7627913`). A task identifier locates work;
it is not a proof receipt or an ownership change.

Several published supporting modules by proof-task workers retain their
inputs as premises and prove none of the targets. They include
`TemperedJacquetRestriction`, which proves the restriction bijection given
complementarity of the two parts; `ArbitraryParabolicUnitarity`,
`TemperedIrreducibleUnitarityReduction` (Worker 346) and
`ParabolicPresentationUnitarity`, which build invariant forms toward the
VII.2.6 Corollary; and `MaximalLeviReducibilityUnitaryInputs` and
`MaximalLeviReducibilityReductionStatements` (Worker 1507), which separate
the VII.1.3 proof into statements.

## Remaining obligations

1. Proofs of all fifteen statements above, through the listed tasks. They
   need structural facts that are themselves open for arbitrary actual
   parabolics, among them compactness of `P(F)\G(F)`, Jacquet
   admissibility, unimodularity of the radical, Iwahori decompositions and
   contracting elements.
2. Statements of VII.2.5, VII.3 and VII.4, and of the VII.1.3 Corollary.
   VII.3 also needs representatives of Weyl double cosets for actual
   parabolics. VII.4 needs Langlands chambers with relative coroots.
   The VII.1.3 Corollary needs Bernstein components.
3. Statements of VI.9.1–VI.9.5, the VI.9.6 pairing Proposition and VI.9.7.

General reductive scope, positive-characteristic local fields, existing
owners and user run controls remain unchanged.
