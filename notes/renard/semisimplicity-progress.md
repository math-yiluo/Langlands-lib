# Renard A.VII: semisimplicity and subobjects

Worker 709 checked this passage and the two proof publications on 1 November
2026, against Library commit `dac2bb9e83346876770fced17af26f0cba7f4c98`.
This is a bounded source and publication audit for the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857` revision 2.

## Source and assertions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.VII starts on printed264/PDF270; its lemma and proof, followed by the
subobject corollary and its proof, are on printed265/PDF271.
Worker 709 read PDF270–272 in full and compared all five Lean/Markdown
pairs listed below. The standing hypotheses come from A.VI.3,
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
construction with no separate assertion in the source.

The corollary imports that proof. Complementedness passes through the
order isomorphism between the subobjects of a subobject and the interval
below it. The modular-lattice complement is the intersection of an
ambient complement with that subobject, matching the source argument.
The arbitrary mono is handled through its underlying-object isomorphism.
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

These two proof publications discharge the lemma and corollary recorded
here. This note makes no completion declaration for the appendix or the
whole-book task. A.VI.3, A.VIII and later sections retain their own
coverage and publication obligations.
