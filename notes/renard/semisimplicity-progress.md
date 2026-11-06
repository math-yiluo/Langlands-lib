# Renard A.VII: semisimplicity and subobjects

Worker 709 checked this passage and the two proof publications on 1 November
2026, against Library commit `dac2bb9e83346876770fced17af26f0cba7f4c98`.
This is a bounded source and publication audit for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2. On 6 November 2026,
under revision 3 and against Library
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd`, Worker 709 added the
published canonical subobject-complement comparison, a derived internal
comparison used by both proofs, with its statement and proof receipts.

## Source and assertions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.VII starts on printed264/PDF270; its lemma and proof, followed by the
subobject corollary and its proof, are on printed265/PDF271.
On 1 November, Worker 709 read PDF270–272 in full and compared the five
Lean/Markdown pairs of the predicate, lemma and corollary rows below. On
6 November, Worker 709 reread PDF269 and PDF271 and compared the two pairs
of the comparison row. The standing hypotheses come from A.VI.3,
printed263/PDF269: the category is source Grothendieck and locally of
finite type.

All declaration names in this note are in `Langlands.Renard`.

| Source assertion | Current declaration and module | Checked scope |
| --- | --- | --- |
| Lemma condition (i): an object is isomorphic to a direct sum of simple objects | `IsCompletelyReducible` in `Langlands.CategoryTheory.RenardSemisimplicity` | An actual coproduct cofan with simple summands, at an explicit index universe; the family may be empty |
| Lemma condition (ii): the object is the sum of its simple subobjects | `IsSumOfSimpleSubobjects` in the same module | `⊤` is the least upper bound of the set of actual simple subobjects |
| Lemma condition (iii): every subobject has a direct-sum complement | `EverySubobjectHasComplement` in the same module | The canonical map `coprod.desc P.arrow Q.arrow` is an isomorphism |
| Implicit use of “semisimple” in the corollary; the source gives no separate definition | `IsSemisimpleObject` in the same module | Internal packaging of condition (i) at index universe `max u v`; the lemma below supplies the equivalence with the other conditions |
| Unnumbered lemma: equivalence of (i), (ii), (iii) | `SemisimplicityEquivalenceStatement` in `Langlands.CategoryTheory.Renard.SemisimplicityEquivalenceStatements`, proved by `semisimplicityEquivalence` in `Langlands.CategoryTheory.Renard.SemisimplicityEquivalence` | Published proof, including the comparison with condition (i) at source index size `r` |
| Unnumbered corollary: a subobject of a semisimple object is semisimple | `SemisimpleSubobjectStatement` in `Langlands.CategoryTheory.Renard.SemisimpleSubobjectStatements`, proved by `semisimpleSubobject` in `Langlands.CategoryTheory.Renard.SemisimpleSubobject` | Published proof for every monomorphism into the ambient object |
| Derived internal comparison, not separately printed: a canonical decomposition by two subobjects versus lattice complements, motivated by A.VI.2(9), printed263/PDF269, and condition (iii) | `SubobjectComplementComparisonStatement` in [SubobjectComplementComparisonStatements](../../Langlands/CategoryTheory/Renard/SubobjectComplementComparisonStatements.md), proved by `subobjectComplementComparison` in [SubobjectComplementComparison](../../Langlands/CategoryTheory/Renard/SubobjectComplementComparison.md) | Every abelian category, with no Grothendieck, AB6 or smallness premise; beyond the A.VI.2(9) direct-sum direction it formalizes no source assertion. See the comparison section below |

The three predicates are defined for arbitrary abelian categories; they do
not assume their equivalence. The two source results have independent
source-index, Hom and object universes `r`, `v`, `u`. They assume
`IsSourceGrothendieck.{r} C` and `SourceAB6 C`. Here source Grothendieck
means `r`-indexed coproducts and Renard's directed-subobject distributivity
law, without a generator; source AB6 means local finite type, rather than
Tohoku AB6.

For the lemma, `Small.{r} (Subobject X)` makes explicit the source's
set-sized subobjects of the object under consideration. The result
identifies `IsSemisimpleObject X` with `IsCompletelyReducible.{r} X`,
identifies semisimplicity with condition (ii), and identifies (ii) with
(iii). This uses only source-sized global coproducts. The alias at
`max u v` is compared to that size objectwise; no global coproduct
assumption at `max u v` or equality of universes is added.

The corollary assumes this smallness only at the ambient `X`. For an
arbitrary mono `j : Y ⟶ X`, its proof derives
`Small.{r} (Subobject Y)` from the injectivity of postcomposition with
`j`. It concludes the same public semisimplicity predicate at `Y`.
Neither theorem introduces a generator, finite-length, Noetherian or
module hypothesis. Zero objects are included.

## Implemented proofs and source correspondence

The equivalence proof uses the actual modular lattice of subobjects,
Zorn's lemma, source AB5 and source AB6. Its maximal independent family of
simple subobjects is reindexed at size `r`. The canonical coproduct map is
proved both mono and epi. In the converse complement argument, source
AB6 supplies a nonzero finite-type subobject; a simple quotient and a
complement yield a simple subobject. The implemented route proves
(i) ⇔ (ii) and (ii) ⇔ (iii), whereas the printed proof deduces (i) from
(iii). The size comparison between the alias and size `r` is an internal
construction with no separate assertion in the source. The (ii) ⇔ (iii)
theorem `isSumOfSimpleSubobjects_iff_everySubobjectHasComplement` first
rewrites condition (iii) as `ComplementedLattice (Subobject X)` by the
published `everySubobjectComplementedLattice`, described in the comparison
section below. The equivalence module imports that comparison, and both
directions are then lattice arguments.

The corollary imports that proof. Complementedness passes through the
order isomorphism between the subobjects of a subobject and the interval
below it. The modular-lattice complement is the intersection of an
ambient complement with that subobject, matching the source argument.
The arbitrary mono is handled through its underlying-object isomorphism.
Its step `everySubobjectHasComplement_of_mono` moves the canonical
complement predicate to the complemented lattice at the ambient object and
back at the subobject, by the same `everySubobjectComplementedLattice`.
The equivalence is then applied at the ambient object and at its
subobject. No new gap was found in this bounded comparison.

Worker 1069 wrote the equivalence proof, reusing Worker 6's size-comparison
probe. Worker 1073 wrote the corollary proof. This audit reuses their
published mathematics and does not supply another proof.

## Independent acceptance and publication

Direct TaskHub fetches reported `accepted=true`, `public=true` and
integration state `published` for both candidates. Each machine receipt
records a Lake build, exact-target validation, unchanged statements and
frozen inputs. Independent semantic reviews approved both without
qualifications.

| Proof | Task and candidate | Machine evidence | Independent review | Publication |
| --- | --- | --- | --- | --- |
| Equivalence | Task `dc8906fc-997e-47d1-a37d-33676b441dca`; candidate `c97ca88f-f289-4511-9036-5d89a2045085` | `2c3dc62b-67e3-4a05-b801-3b5d3e9b79b7` | Reviewer 4780, review `eaf1f10a-245d-41ba-b7a5-4d80c7c22233` | Integration `8b970460c8b048e8b6ed25c11357fded`, commit `f6b64ec108eed89ad46dff1d99192f40c4f29015` |
| Subobject corollary | Task `13b953c4-b5a9-46ec-8ab2-4307634441fe`; candidate `a27d0113-37b1-4d3f-903f-9a68e0321998` | `473f0a38-f5ee-4041-aea2-f49f01a0771c` | Reviewer 4810, review `acab5475-3908-406e-8f65-27fcf3cc6b6d` | Integration `8d5033ca1d194d6c87fb5d19ce49a6ef`, commit `f5e9b4259cccc86006fbed5ed946afb499668dda` |

All four current Library files and local files match the hashes in their
accepted frozen bundles:

| Path under `Langlands/CategoryTheory/Renard/` | SHA256 |
| --- | --- |
| `SemisimplicityEquivalence.lean` | `ac765876fd55789d9c27d6dca1408351ef72d0230d8f68f30c60624a313186bb` |
| `SemisimplicityEquivalence.md` | `0b38a21ba6312a8fa39f842f398b0c350f1c82e6aaf93d19d31fef7ac56ddc3e` |
| `SemisimpleSubobject.lean` | `232158b56448bb4d463bbb50eb011da325272a04534946f1b2e6d531dbd528dd` |
| `SemisimpleSubobject.md` | `aabbd64c89bae0631e208e307e4e2ad3b43cf3f656e60a9a1315a7d95888afbe` |

On 6 November 2026 the same four hashes held at Libraries
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd` and
`87e695f5180726de47820341b89accb81c4e1033` and in the workspace.

These two proof publications discharge the lemma and corollary recorded
here. This note makes no completion declaration for the appendix or the
whole-book task. A.VI.3, A.VIII and later sections retain their own
coverage and publication obligations.

## Canonical subobject-complement comparison

The statement module
[SubobjectComplementComparisonStatements](../../Langlands/CategoryTheory/Renard/SubobjectComplementComparisonStatements.md)
defines three propositions:

```lean
def CanonicalSubobjectComplementStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (P Q : Subobject X),
    IsIso (coprod.desc P.arrow Q.arrow) ↔
      P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤

def EverySubobjectComplementedLatticeStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ X : C,
    EverySubobjectHasComplement X ↔ ComplementedLattice (Subobject X)

def SubobjectComplementComparisonStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  CanonicalSubobjectComplementStatement C ∧
    EverySubobjectComplementedLatticeStatement C
```

The map `coprod.desc P.arrow Q.arrow : (P : C) ⨿ (Q : C) ⟶ X` is induced
by the two actual subobject inclusions. This is the same normalization as
`EverySubobjectHasComplement` in the table above, which the module imports
unchanged. The infimum, supremum, bottom and top are Mathlib's operations
on `Subobject X`; no complete-lattice instance is used.
`ComplementedLattice (Subobject X)` is the right side of an equivalence,
never a hypothesis. The object and Hom universes are independent. No
smallness, well-poweredness, arbitrary-coproduct, Grothendieck, AB6,
generator, Noetherian, module or finite-dimensionality premise is added.
Zero objects and zero subobjects are included.

A.VI.2(9), printed263/PDF269, ends: if `A ∩ B = 0` and `A + B = C`, then
`C ≃ A ⊕ B`. Condition (iii), printed265/PDF271, asks that every subobject
have a complement giving such a decomposition. The book states neither the
converse nor a comparison with lattice complements. The statement Markdown
classifies both full equivalences as derived internal specifications.
Worker 709 reread PDF269 and PDF271 and rechecked the source SHA256 on
6 November 2026, and found this reading accurate.

Curried, the right-to-left direction of the pointwise statement is the
earlier `ComplementarySubobjectsSumStatement C` of
`Langlands.CategoryTheory.RenardNoetherIsomorphismStatements`. Its proof
`complementarySubobjectsSum` is the third clause of the published
`noetherIsomorphisms`, recorded in the A.VI.2(9) row and receipts of
[abelian-categories-progress](abelian-categories-progress.md). The
statement unit does not import that module.

The module
[SubobjectComplementComparison](../../Langlands/CategoryTheory/Renard/SubobjectComplementComparison.md)
proves the aggregate as `subobjectComplementComparison`, the pair
`⟨canonicalSubobjectComplement C, everySubobjectComplementedLattice C⟩`,
at the same universe parameters and with no further hypothesis:

- `canonicalSubobjectComplement`: suppose the canonical map `f` is
  invertible. Then `p := inv f ≫ coprod.desc (𝟙 _) 0` is the projection
  onto `P` along `Q`, with `P.arrow ≫ p = 𝟙` and `Q.arrow ≫ p = 0`. These
  force the inclusion of `P ⊓ Q` into `P` to be zero, so `P ⊓ Q = ⊥`. Next,
  `f` factors through `(P ⊔ Q).arrow`, which is therefore an epimorphism.
  It is also a monomorphism, and an abelian category is balanced, so it is
  an isomorphism and `P ⊔ Q = ⊤`. The converse direction applies the
  published `complementarySubobjectsSum C X P Q` unchanged.
- `everySubobjectComplementedLattice`: `complementedLattice_iff`,
  `isCompl_iff`, `disjoint_iff` and `codisjoint_iff` rewrite the lattice
  side as `∀ P, ∃ Q, P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤`. The pointwise theorem is then
  applied under the quantifiers, with the same complement `Q` on both
  sides.

As recorded in the proof section above, both A.VII proofs use the second
clause. The comparison itself proves neither the three-way lemma nor the
corollary, and contains no arbitrary-sum, AB5 or AB6 argument.

| Unit and authors | Candidate; machine receipt | Independent review task / reviewer | Integration; published commit |
| --- | --- | --- | --- |
| `SubobjectComplementComparisonStatement` and its two clauses — Workers 849 and 6 | `f2114093-fa92-4f0d-aaae-171821f97eb1`; `c4bfdb59-96f9-4daf-94d1-2a01bbf5777c` | `8e7c0a1b-49f0-476d-8431-7efe6bb1b576` / Reviewer 3613 | `9ccddd1cbc994f6ba12cadbfd481a55a`; `06ce3701c57321e39772a06c6c0202f3644c6cb7` |
| `subobjectComplementComparison` — Workers 882 and 6 | `d9f93a1b-1f97-4403-91d5-ad5dee536eb2`; `780a5bfc-e8c4-4d1c-beba-b0514e2518ad` | `a18e6354-aaef-43dd-829b-86c0fb61c1c4` / Reviewer 4009 | `4815d9aabfa1412cbb3033a77a50f599`; `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |

The statement was produced under statement task
`b8c328aa-9fed-4b42-895b-43c43b42550f`. Its `lean.statement@1` receipt
passed the schema, immutable-content, reference-integrity,
exact-reference-policy, Lake-build and declaration-kind checks; this is
not proof acceptance. Its frozen record has two author qualifications,
both scope notes. One restates the meaning. The other says that the unit
supplies statements only and that the lattice-to-canonical-map direction
belongs to the Noether proof task `d0241956-6d80-41a2-8ca8-88db6bad7b32`.
On 6 November that task was done, with accepted proof
`c2dc09d5-e172-44a1-b1bb-98de55f92df5`. Reviewer 3613 judged both notes
accurate and approved without review qualifications.

The proof was produced under proof task
`8307c004-2fb8-4b34-8014-3c75d3ff38fb`. Its `lean.proof@1` receipt passed
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`,
with `proof_accepted: true`. Its frozen record has no author
qualifications, and Reviewer 4009 approved without qualifications.
Worker 709 authored neither unit; this note documents them and is not a
review.

On 6 November 2026 the frozen bundles, Libraries
`d2fd0b68e11e9844d5da3650e7579d62588fd3fd` and
`87e695f5180726de47820341b89accb81c4e1033`, and the workspace had
the same SHA256 for each file:

| Path under `Langlands/CategoryTheory/Renard/` | SHA256 |
| --- | --- |
| `SubobjectComplementComparisonStatements.lean` | `12b635efa6c59239fa8f6d090b208496c679fc43238ca7365c4921737867269d` |
| `SubobjectComplementComparisonStatements.md` | `da26b347ad5f3dcd4d6b513957c2298b4bb47eaf22e5d734dc5052790dbcf558` |
| `SubobjectComplementComparison.lean` | `b4eec322addb8f5b9c3abbc3f37493116177a4f37b6e01652b0155adf1158ba7` |
| `SubobjectComplementComparison.md` | `62264aaea04ee918cfe95559c3b3fd1f78113c038d5931043844733856e578ba` |

The comparison is internal and closes no further source assertion. This
addition makes no completion declaration either.
