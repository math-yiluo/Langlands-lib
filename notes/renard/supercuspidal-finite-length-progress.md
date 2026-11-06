# Renard VI.5.2–VI.5.4, VI.6.2, VI.6.4 and VI.7.1: supercuspidal induction, finite length and cuspidal support

Worker 6, 6 November 2026. This focused map supplements the
[whole-book ledger](coverage.md) and continues the
[parabolic-functor and tempered map](parabolic-functors-tempered-progress.md),
whose common setting, normalized functors `leviInductionFunctor` (`i_P^G`)
and `leviJacquetFunctor` (`r_P^G`) and Frobenius-reciprocity and exactness
statements are used below. It records nine verified statement publications
by Worker 6 and the proof tasks for them. None of these publications proves
a proposition. The map is not a complete inventory of VI.5, VI.6 or VI.7,
and supplies no new Lean proof.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are one-based and equal printed page numbers plus six.
The source passages and the paired Lean and Markdown files were read for the
claims below. By SHA256, all eighteen primary files equal their frozen
accepted files, Worker 6's workspace files and the files at Library
`1eb9a9ee0815224a368f8dc58b7d95f024cfff05`. A fresh Lean check of the nine
modules at that Library (check `9809af85-16b6-4ac4-a333-3cc9ade5dc05`) had
zero diagnostics.

## Verified publications

Each receipt below has `accepted = true`, `public = true`, an accepted
`lean.statement@1` machine validation, an independent semantic approval with
no qualification and a published integration. A statement receipt does not
prove its proposition. All declarations are in namespace
`Langlands.Aubert.General.RepresentedParabolic` under
`Langlands/Representation/Exponents/`.

| Pair and exact declaration | Candidate, independent review and publication |
| --- | --- |
| [LeviInductionNoSupercuspidalSubquotientStatement](../../Langlands/Representation/Exponents/LeviInductionNoSupercuspidalSubquotientStatement.md) | Statement `e93e95d2-ca7f-4d7d-a1d6-cb04598cc1ea`; Reviewer 15619, review `85521bfd-40db-4034-b9ef-71e1cc1dabb4`; machine `5f5540f4-3676-42df-921b-3dfa833356ba`; integration `6d61a772205845d4868220fa325e25ba`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviJacquetInductionVanishingStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionVanishingStatement.md) | Statement `95ba2853-4379-4d40-b6c8-a576ecec21f6`; Reviewer 15648, review `5bc0a3b6-326f-4ef3-8d2a-88368a3e9688`; machine `fc6c600e-5177-4a54-98f7-99b2f2b42638`; integration `fba3254333a44de98175faf47a30b024`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviJacquetInductionNoSupercuspidalStatement](../../Langlands/Representation/Exponents/LeviJacquetInductionNoSupercuspidalStatement.md) | Statement `48f590b0-7eea-4dd8-9f2d-a99006a6bd6b`; Reviewer 15670, review `c604f71e-35b7-4696-b0a9-ecced65645e6`; machine `1b83d17b-8ce4-4335-876c-5bce8d5c0b8e`; integration `c7296e7ae6004643a55ebead47f4320e`, commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`. |
| [LeviSupercuspidalInductionAssociationStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionAssociationStatement.md) | Statement `35407138-5d7e-4281-b589-fb65f5cc6ad5`; Reviewer 15692, review `386ea4d7-a2cb-49b7-be08-2335a614dde7`; machine `3e6774cb-2345-4eea-8454-b8482b246c83`; integration `b6b19aa2a8124aaca8acb47d9a49f061`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviSupercuspidalInductionSameLeviStatement](../../Langlands/Representation/Exponents/LeviSupercuspidalInductionSameLeviStatement.md) | Statement `0e5e5741-ab65-4ce3-a341-a709a9d078b9`; Reviewer 15733, review `e2ccd97b-1c2a-4480-bcae-80dae050427c`; machine `f270e74f-62a1-4cc7-ab78-1d437c660f31`; integration `bbdf6d0cd87949f393da245302225740`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviInductionFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviInductionFiniteLengthStatement.md) | Statement `bdd93bab-5980-4e35-b6b3-f2ca2cc68219`; Reviewer 15785, review `3a5fb44c-9665-419c-9d8c-9883a678739c`; machine `b89db3a8-c977-4019-9dfc-132d1b3bfc3e`; integration `b97e590988a042ca92be0ce4b529fc47`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviJacquetFiniteLengthStatement](../../Langlands/Representation/Exponents/LeviJacquetFiniteLengthStatement.md) | Statement `d55652fe-b897-4785-9287-b2761f02037a`; Reviewer 15803, review `7c2bbc4e-203a-4130-b980-406f2a33be8a`; machine `0b4720ea-6c33-4226-bcff-d02e1ca3bf7d`; integration `dd4fa1b59e8740719fb2e3893ed66e08`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviCuspidalSupportAssociationStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportAssociationStatement.md) | Statement `30e51bc2-d06b-499d-ab92-53034d6142be`; Reviewer 15825, review `ed5f187c-5759-4760-9485-d5d6c06bda16`; machine `59a2b597-9a3c-407b-af80-849d47f210d9`; integration `50ecd894860c4f72aa894dd657a62b45`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |
| [LeviCuspidalSupportSurjectiveStatement](../../Langlands/Representation/Exponents/LeviCuspidalSupportSurjectiveStatement.md) | Statement `c243504f-8e15-415a-b429-badb33721f17`; Reviewer 15848, review `e76bcd06-2b10-4de1-a9f0-6d2e6a30f9b5`; machine `47236c4e-633f-4aeb-88c8-b56474422a68`; integration `d5df3182f0d6464fb0cf782f0d16c43d`, commit `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. |

## Common conventions

The setting is that of the parabolic-functor map: every nonarchimedean local
field of any characteristic, an actual connected reductive group scheme, and
actual rational parabolics with rational Levis and matching radicals,
without standardness.

- **Supercuspidality.** Renard's definition (VI.2.1, printed p.137 /
  PDF p.143) is the vanishing of `r_P` for every proper parabolic. Each
  statement writes it out as `Subsingleton` of the normalized
  `jacquetFunctor` for every proper actual rational parabolic of the group,
  as in the published `MaximalLeviSupercuspidalReducibilityStatement`. No
  predicate is defined.
- **Conjugacy and association.** `g M g⁻¹ = M'` is an isomorphism
  `φ : M ≅ M'` with `φ.hom ≫ l' ≫ p' = l ≫ p ≫ (G.innerIso g).hom`.
  Association of cuspidal data (VI.5.2, printed p.172 / PDF p.178) adds a
  linear equivalence `ρ ≃ ρ'` intertwining `ρ` with `ρ' ∘ φ`, the encoding of
  the published `TemperedIrreducibleDiscreteSeriesUniquenessStatement`.
- **Subquotients and length.** Subquotients and irreducibility are the
  published `SmoothRep.IsSubquotient` and `SmoothRep.IsIrreducible`.
  Composition factors are read as irreducible subquotients. Finite length
  is either `SmoothRep.PreservesFiniteLength` or Worker 14's
  `HasCompositionSeriesLength` and `HaveSameJordanHolderFactors`.

## VI.5.2–VI.5.4: induction from supercuspidal representations

Source: VI.5.2, Lemma, and VI.5.3, Proposition, printed p.173 / PDF p.179;
VI.5.4, Theorem and Corollary, printed pp.173–175 / PDF pp.179–181.

- `LeviInductionNoSupercuspidalSubquotientStatement` (VI.5.2, Lemma): for a
  proper parabolic and every smooth `ρ`, no irreducible subquotient of
  `i_P^G ρ` is supercuspidal.
- `LeviJacquetInductionVanishingStatement` (VI.5.3 (i)): if `L` has no
  Levi subgroup `G(F)`-conjugate to `M`, then `r_Q^G i_P^G ρ = 0` for every
  supercuspidal `ρ`.
- `LeviJacquetInductionNoSupercuspidalStatement` (VI.5.3 (ii)): if `M` is
  not `G(F)`-conjugate to `L`, no irreducible subquotient of
  `r_Q^G i_P^G ρ` is supercuspidal. The source's "subquotient" is read as
  "irreducible subquotient", since the zero representation is
  supercuspidal.
- `LeviSupercuspidalInductionAssociationStatement` (VI.5.4, Theorem,
  partial): for irreducible supercuspidal `ρ` and `ρ'`, `i_P^G ρ` has
  finite length, and four conditions are equivalent (`List.TFAE`):
  association, a nonzero intertwiner `i_P^G ρ → i_{P'}^G ρ'`, equal
  Jordan–Hölder factors, and a common irreducible subquotient. The bound
  `l(M)` on the length and the bound on `dim Hom` are not stated; they need
  the Weyl-group sets of V.4 for actual groups.
- `LeviSupercuspidalInductionSameLeviStatement` (VI.5.4, Corollary): for
  parabolics `P` and `Q` with the same Levi embedding `M → G`, equal
  Jordan–Hölder factors and a nonzero intertwiner `i_P^G ρ → i_Q^G ρ`; and
  every irreducible subquotient of `i_P^G ρ` embeds into some `i_Q^G ρ`.

Assertion (iii) of VI.5.3, the filtration by the `w·ρ`, is not stated; it
needs the double-coset set `W(L, M)` modulo `W_L`.

## VI.6.2 and VI.6.4: finite length

Source: VI.6.2, printed p.178 / PDF p.184; VI.6.4, printed p.179 /
PDF p.185; the introduction of VI.6, printed pp.175–176 / PDF pp.181–182.

- `LeviInductionFiniteLengthStatement`:
  `SmoothRep.PreservesFiniteLength` for `i_P^G`. This is the preservation
  announced by the section; its Lemma is the irreducible case.
- `LeviJacquetFiniteLengthStatement`: `SmoothRep.PreservesFiniteLength` for
  `r_P^G`.

The published `DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement` of `Aubert/General/PrerequisiteStatements`
assert the same for the parabolics `P(χ)` of cocharacters.

## VI.7.1: the cuspidal support

Source: VI.7.1, Lemma and Proposition, printed p.180 / PDF p.186.

- `LeviCuspidalSupportAssociationStatement` (Lemma): if irreducible
  supercuspidal `ρ₁` and `ρ₂` are subquotients of `r_{P₁}^G π` and
  `r_{P₂}^G π` for one irreducible `π`, the cuspidal data are associated.
- `LeviCuspidalSupportSurjectiveStatement` (Proposition, partial): for a
  fixed parabolic and an irreducible supercuspidal `ρ`, some irreducible `π`
  has a surjective intertwiner `r_P^G π → ρ`, and finitely many `π₀ i`
  represent every irreducible `π` with `ρ` a subquotient of `r_P^G π`. The
  map `Sc` on isomorphism classes is not formed; finiteness of the whole
  fibre also needs conjugation of associated data and finiteness of `P(M)`.

VI.7.2 (the functors `I`, `R` and Bernstein components) is not stated here.

## Proof tasks

| Targets | Proof task |
| --- | --- |
| The five VI.5.2–VI.5.4 statements | `fc21c11d-1a31-468d-a90e-fdda36098677` |
| The four VI.6.2, VI.6.4 and VI.7.1 statements | `9b0a1303-9208-4f6c-96b8-996d44645bf2` |

Worker 6 published both tasks. The source proofs use inputs that are not
stated for represented parabolics: the VI.3.5 splitting into a
supercuspidal part and its complement, Lemma VI.3.6, Corollary VI.2.1 and
transitivity of induction. The represented geometric lemma VI.5.1 is the
published `RepresentedGeometricLemmaStatement` of Worker 1585, with proof
task `c060fb34-b423-4ac5-8448-788ac7627913`. Standard-family analogues of
VI.2.1 and VI.3.5 are published in `Langlands/Representation/CuspidalSupport/`.

Related tasks of other workers, kept separate: VI.5.4 finite length for
general standard-family supercuspidal induction,
`59ee1ed5-28d6-4574-bb6e-be514fd6f378`; VI.6.2 for dynamic induction,
`02257068-4b1f-4c7d-b849-c85a24606658`; actual inertial cuspidal data and
Bernstein blocks for VI.7.1–VI.7.2, `b0b200c0-5960-4909-a733-0bcbcc0f0dde`;
the VI.4.1 norm-kernel progenerator comparison,
`3e43c59a-2f05-433e-a739-54f50fcea0d3`; VI.8.1–VI.8.2 flatness and
admissibility, `e2884067-b19a-4685-91d9-e62316299fc3`; compact-level cuspidal
inertia finiteness (VI.3.4), `61b5cb94-c808-4499-9efb-ec1ae6c0cecb`; and,
for VI.9, the VI.9.1 statement task `f0a4d6b4-8a85-4ce9-972d-7e4958be7bb2`
(published module `UniformCompressionStabilizationStatement`, with derived
partial statements of the Theorem and the Proposition), the proof tasks
`47e556e6-6b2a-40dc-ba66-d6a0585f5220` for
`UniformCompressionStabilizationStatement` and
`cac6f709-2a1b-4eaa-a16d-63f2e40f3b29` for
`GeneralizedJacquetLemmaStatement`, and the opposite-parabolic
uniqueness statement task `773fb2e1-0719-4374-b8ea-8da9a3ace5c6`. Worker
1751's published `RationalCuspidalInducedEmbeddingStatement` states a
consequence of VI.7.2 for standard families. A task identifier locates work;
it is not a proof receipt or an ownership change.

## Remaining obligations

1. Proofs of all nine statements, through the two listed tasks, including
   represented forms of the VI.3.5 splitting, Lemma VI.3.6, Corollary VI.2.1
   and transitivity of induction.
2. Statements of VI.5.3 (iii), the numerical bounds of VI.5.4, the map `Sc`
   of VI.7.1 on isomorphism classes, and VI.7.2 for represented parabolics.

General reductive scope, positive-characteristic local fields, existing
owners and user run controls remain unchanged.
