# Renard A.I.3: Noetherian objects, finite type and unital modules

Worker 709, 3 November 2026. This note maps the assertions on printed
pages 248–249 / PDF254–255 to the current Library definitions, four
independently published proof units and the remaining general
all-subobjects proof obligation. It supplements the
[elementary categorical map](elementary-categories-source-map.md) and
[whole-book ledger](coverage.md). It introduces no Lean declaration and
does not close A.I.3, Appendix A or the book program.

## Source and conventions

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF254–255 were read in full and visually inspected for this audit.
Printed page 6 / PDF12 was also reread and visually checked: rings and
actions need not be unital in general, but `M(A)` for a unital ring is
the full subcategory of **unital** modules. Thus the A.I.3 example in
`M(A)` is modeled by Mathlib's actual `ModuleCat R`.

The current [Appendix A corrections note](appendix-a-corrections.md)
concerns other passages. No dedicated Renard 2026 errata note was found
in the checked public or project notes. The published
[definition companion](../../Langlands/CategoryTheory/RenardFiniteType.md)
records its bounded check of the supplementary 2010 errata, PDF18–19,
registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Those pages do not supply the A.I.3 repairs. The conventions below are
internal mathematical diagnoses retained from that reviewed definition:

- the selected member of a subobject subset is maximal;
- chains in the maximality and finite-type conditions are nonempty;
- a proper subobject means its class differs from top, equivalently
  its inclusion is not invertible;
- the initial covering equation has union the ambient object `X`.

An abstract isomorphism between a subobject's domain and `X` does not
make its inclusion invertible. Arbitrary unions include the empty
union; finite subcovers may be empty, as required for zero objects.
These repairs are not attributed to an author-issued erratum.

## Source assertions and exact declarations

The six predicates in
[`Langlands.CategoryTheory.RenardFiniteType`](../../Langlands/CategoryTheory/RenardFiniteType.md)
use `CategoryTheory.Subobject X`, its existing factorization order and
`IsLUB`. All names in the following table have prefix `Langlands.Renard`.

| Original passage | Library meaning and status |
| --- | --- |
| A.I.2 context and A.I.3 standing union assumption, PDF254 | `HasSubobjectUnions X` requires a least upper bound for every subset of `Subobject X`; `HasAllSubobjectUnions C` requires this for every object. These predicates choose no union operation. |
| A.I.3 first paragraph, PDF254 | `IsNoetherianObject X` means every nonempty subset has a maximal member. [`NoetherianCriteriaStatement`](../../Langlands/CategoryTheory/Renard/NoetherianCriteriaStatements.md) and proof [`noetherianCriteria`](../../Langlands/CategoryTheory/Renard/NoetherianCriteria.md) give the nonempty-chain and monotone natural-sequence criteria, together with an internal Mathlib comparison. |
| A.I.3 last paragraph on PDF254 | `IsFiniteTypeObject X` includes `HasSubobjectUnions X` and excludes top as the least upper bound of a nonempty chain of proper subobjects. |
| A.I.3 opening paragraph on PDF255 | `HasFiniteSubcoverProperty X` includes union existence and gives a finite subset of every subobject cover whose union is top. [`FiniteTypeFiniteSubcoverStatement`](../../Langlands/CategoryTheory/Renard/FiniteTypeFiniteSubcoverStatements.md) is proved by [`finiteTypeFiniteSubcover`](../../Langlands/CategoryTheory/Renard/FiniteTypeFiniteSubcover.md). This is the printed compactness characterization. |
| A.I.3 next paragraph, PDF255 | [`NoetherianSubobjectFiniteTypeStatement`](../../Langlands/CategoryTheory/Renard/NoetherianSubobjectFiniteTypeStatements.md) states that an object is Noetherian iff every subobject's underlying object is of finite type, under `HasAllSubobjectUnions C`. The statement is published; its general proof remains open. |
| A.I.3 category definition, PDF255 | `IsNoetherianCategory C` is `HasAllSubobjectUnions C ∧ ∀ X, IsFiniteTypeObject X → IsNoetherianObject X`. Mathlib's category-wide `CategoryTheory.Noetherian` has a different convention, including essential smallness. |
| A.I.3 example, first sentence, PDF255 | [`ModuleFiniteType.ModuleFiniteTypeStatement`](../../Langlands/CategoryTheory/RenardModuleFiniteTypeStatements.md), proved by [`ModuleFiniteType.moduleFiniteType`](../../Langlands/CategoryTheory/RenardModuleFiniteTypeProof.md), compares source finite type with `Module.Finite R M`, and separately compares finite subcovers with the same algebraic predicate. |
| A.I.3 example, second sentence, PDF255 | [`ModuleNoetherian.ModuleNoetherianStatement`](../../Langlands/CategoryTheory/RenardModuleNoetherianStatements.md), proved by [`ModuleNoetherian.moduleNoetherian`](../../Langlands/CategoryTheory/RenardModuleNoetherianProof.md), includes the internal object comparison with `IsNoetherian R M` and the source category comparison with left Noetherianity `IsNoetherianRing R`. |

The general categorical declarations retain independent object and Hom
universes, `C : Type u` and `Category.{v} C`. They impose no abelian,
zero-object, well-poweredness or essential-smallness hypothesis. The
Noetherian criteria need no union-existence assumption. In the
finite-type/finite-subcover equivalence, union existence is part of each
predicate; no category-wide union hypothesis or complete-lattice
structure is added to the theorem's external parameters.

The sequence criterion gives one index `n` such that `f n = f m` for
every `m ≥ n`, for every monotone `f : ℕ → Subobject X`. The chain
criterion requires a maximal member belonging to each nonempty chain.
The internal comparison
`noetherianMathlibComparison` identifies the source maximal-subset
definition with `CategoryTheory.IsNoetherianObject X`; it is a
correspondence result, rather than an additional printed assertion.

## Implemented proof routes

`noetherianMathlibComparison` unwraps Mathlib's Noetherian-object
predicate and applies its well-founded-order maximality theorem.
Antisymmetry converts the two maximality formulations. The sequence
criterion then uses Mathlib's monotone-chain condition, passing between
order homomorphisms and monotone functions. For the reverse chain
criterion, the range of a monotone natural sequence is a nonempty
chain; a maximal member forces uniform stabilization. The aggregate
`noetherianCriteria` combines the three comparisons.

`finiteTypeFiniteSubcover` chooses a complete lattice locally from
`HasSubobjectUnions X`, retaining the actual subobject order and top.
For the forward direction, Zorn's lemma supplies a maximal element
whose join with every finite part of a supposed counterexample cover
remains proper. Maximality forces it to bound the entire cover, giving
a contradiction. Conversely, a finite subset of a nonempty chain has
an upper bound inside that chain. A finite subcover would force that
member to equal top. No distributivity or directedness assumption is
used for arbitrary covers.

For actual modules, `ModuleFiniteType.hasSubobjectUnions` transports
suprema along
`ModuleCat.subobjectModule M : Subobject M ≃o Submodule R M`.
`finiteSubcover_iff_finite` transports finite covers along this same
order isomorphism and uses Mathlib's equivalence between finite
generation and compactness of the top **submodule**. The finite-type
comparison composes this result with the general
`finiteTypeFiniteSubcover` theorem. A separate general
`IsCompactElement ⊤` bridge on categorical subobjects is not claimed
here and is not needed to cover the printed finite-subcover assertion.

`ModuleNoetherian.object_iff` transports maximal-subset conditions
through the subobject–submodule order isomorphism. The category proof
uses the published finite-type comparison. In one direction it applies
the category property to the finitely generated lifted regular module
`ModuleCat.of R (ULift.{uM} R)` and transports Noetherianity back to `R`.
In the other direction, finite modules over a left Noetherian ring are
Noetherian, and the union-existence theorem supplies the other conjunct.
The exported aggregate has no remaining finite-type-comparison premise.

Both module units permit arbitrary unital rings, including
noncommutative and zero rings. Their object comparisons preserve
independent ring and module-carrier universes `uR` and `uM`. The
category comparison uses `ModuleCat.{max uR uM} R` so that it contains
the lifted regular module; it makes no assertion at an arbitrarily
smaller carrier universe. These examples do not identify categories of
possibly nonunital actions with `ModuleCat R`.

Renard cites [25], Proposition 1.6.1 and Lemma 3.6.1, and [37], 4.10
Theorem 1. The implementations above use the described Library and
Mathlib arguments. They do not claim to reproduce those cited proofs.
The separate [finiteness-convention audit](nonunital-finiteness-sources.md)
records the selected Pareigis and supplied Douady-edition passages
actually read, including their edition and locator limits.

## Verified acceptance and publication

The following records were checked as accepted and public, with
unqualified independent semantic approval and published integration.
The complete integrated reports were read. The proof records retain
their separate build and exact-target validation; this note supplies
no additional proof receipt.

| Unit and artifact | Independent review task | Published integration and Library commit |
| --- | --- | --- |
| Six predicates, definition `b6b67e9d-51ea-4c5e-8271-e17af270ec5b` | Reviewer 3000, `86dfdcc2-bd4c-4f6a-a175-4a000ef512a9` | `ca5a3e04e6464331b5cc6b46f724be55`; `6e568b3024e33889aa9fcaae1e910b0ff99f9b59` |
| General Noetherian criteria, proof `7474f69a-8d19-4ce2-a566-66242b722e4f` | Reviewer 3968, `835dee8e-b5e6-40f5-88ab-4979d51b21e7` | `15f38fe826014be2b9beba9555612f80`; `b0ef093b63d0f0c27bb690dca12820c991756955` |
| General finite-subcover characterization, proof `f2b9c9ad-00d5-49a3-bea3-a45798a028f5` | Reviewer 3974, `4ebbe37f-d053-4693-b81c-41f1a935f5cf` | `37853f2cdd3240d291f4339a01d8d791`; `b0ef093b63d0f0c27bb690dca12820c991756955` |
| Actual unital-module finite type, proof `e0a2ce4f-81e4-44fb-af45-8bc54f853910` | Reviewer 4092, `8182e185-cb51-4a8a-be4b-0c959a8aef24` | `2f68890ca03046909dee35c88882c3fe`; `355c05239d7704a3ed5d72bad864cb1d542b647a` |
| Actual unital-module Noetherian comparisons, proof `daeef1c9-4062-4e6f-a5d8-9be2d43bed01` | Reviewer 4120, `49e71a02-69b7-4540-ba75-d6f1258945a6` | `1ed9d5ff6b53487e80c9236bca765029`; `9f141aa49982eab63f32f392c4c63dcb83837a19` |
| All-subobjects equivalence, statement `2363d84e-7cf6-4e2c-8bba-622278171cc8` | Reviewer 4045, `895e2f0e-e38b-4941-98ad-b7f512e82897` | `abf6746c200c4c699d2576378e3b0fc2`; `cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b` |

The ten cited definition, statement and proof Lean/Markdown pairs match
the admitted Library `6eec947454b4466fab00fb115b09f2dc49fe158b`.
The current module-Noetherian proof reuses
`ModuleFiniteType.hasSubobjectUnions`, as its integrated companion
explains; its frozen candidate contained a duplicate helper.
The mathematical import paths and declarations above refer to the
current Library. Mathlib is pinned at
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 6 authored the general criteria and finite-subcover proof drafts;
Workers 122 and 840 respectively prepared their published proof units.
Worker 702 and Worker 6 contributed the six-predicate definition.
Workers 709 and 820 contributed the actual-module finite-type proof;
Workers 709 and 735 contributed the actual-module Noetherian proof.
Worker 6 and Worker 951 contributed the all-subobjects statement.
This source map preserves those attributions.

## Remaining general proof

The exact published `NoetherianSubobjectFiniteTypeStatement C` is:

```lean
HasAllSubobjectUnions C →
  ∀ X : C, Langlands.Renard.IsNoetherianObject X ↔
    ∀ P : CategoryTheory.Subobject X,
      Langlands.Renard.IsFiniteTypeObject (P : C)
```

The right side concerns the underlying object of every actual
categorical subobject, including top. Proof task
`b0f9eac8-d06f-44db-8205-0baab9f101f1`, revision 1, was checked on
3 November 2026 as ready, with no executor, active attempt or candidate.
That is task status, not proof evidence.

Renard's forward argument treats a chain of subobjects of a subobject
inside the original object's subobject order. His converse takes the
union of an increasing sequence and uses its finite type to obtain a
finite subcover and stabilization. The published criteria and
finite-subcover theorem provide reusable ingredients, but neither
proves this exact categorical equivalence by itself. The general proof,
later A.VI.3 assertions, other categorical constructions and the
possibly nonunital comparison obligations remain separate.
