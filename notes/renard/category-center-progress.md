# Renard A.X: categorical centers and the unital module example

The source passage and the Lean/Markdown pairs were checked on 1 November
2026 against Library
`dad4d948ab2f6838277ce9094bcc92df1507b0cb`. This supplements the
[whole-book ledger](coverage.md), whose other initial-pass rows retain
their stated scope. It records existing published mathematics; it introduces
no new definition, statement or proof.

## Source passage and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.X, printed page 269 /
PDF page 275. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
That complete page was read. It defines the center of a category
and gives the unnumbered unital-module example below, without a proof
of the example.

The current statement and proof documentation also records the module
conventions on printed pages 5–6 / PDF11–12: modules are left modules,
and a unital module has the unit acting as the identity. Although the
book generally permits nonunital rings and actions, this A.X example
explicitly assumes both a unital ring and unital modules.

No source-specific file under `notes/errata` was found in the checked
Library. The published paired documentation records its check of the
registered 2010-edition supplement
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
including its Appendix A corrections on PDF18–19; it found no correction
to this example. The 2026 original governs this audit.

## Assertion map

| Source content | Existing Lean interface | Scope |
| --- | --- | --- |
| Center of any category: natural endomorphisms of its identity functor | Mathlib `CategoryTheory.CatCenter C`, defined as `End (𝟭 C)` | Reuses the actual functor category. No preadditivity is required for this definition. |
| Component description: an endomorphism of every object commuting with every morphism | `CatCenter.app`, `CatCenter.naturality` and `CatCenter.ext` | For `f : X ⟶ Y`, naturality is `f ≫ z.app Y = z.app X ≫ f`; this is the source equation in diagrammatic composition order. |
| Unnumbered example: the center of the category of unital left modules is canonically the ring center | `Langlands.Renard.moduleCatCenterIdentification`, proving `ModuleCatCenterIdentificationStatement` | Actual `ModuleCat.{max u v} R`, arbitrary `[Ring R]`, independent `u, v`, and the exact scalar-action map specified below. |

The general definition and component laws were checked directly in the
pinned Mathlib `CategoryTheory/Center/Basic.lean`. The source uses the
ordinary category center, so no parallel project definition is needed.

## Exact map and published proof

The [statement pair](../../Langlands/CategoryTheory/RenardModuleCatCenterStatements.md)
fixes Mathlib's ring homomorphism

```lean
Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)
```

under `open scoped ModuleCat.Algebra`. Its direction is from the ring
center to the category center. The published theorem
`Langlands.Renard.moduleCatCenterScalarComponent` proves that its component
at a module `M` sends `m` to `(c : R) • m`. This is a normalization of the
source's canonical identification.

For `R : Type u` with only `[Ring R]`, the required aggregate is

```lean
ModuleCatCenterBijectiveStatement.{u, v} R ∧
  ModuleCatCenterRingEquivStatement.{u, v} R
```

in namespace `Langlands.Renard`. The first clause is bijectivity of that
specific homomorphism. The second is

```lean
∃ e : Subring.center R ≃+* CatCenter (ModuleCat.{max u v} R),
  e.toRingHom =
    Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)
```

Thus the conclusion retains the specified map, rather than merely
asserting an abstract ring isomorphism. The separate component theorem
is not a conjunct of the aggregate.

The [published proof](../../Langlands/CategoryTheory/RenardModuleCatCenter.md)
evaluates a natural endomorphism on `ModuleCat.of R (ULift.{v} R)` at
`ULift.up 1`. Naturality along the maps `r ↦ r.down • m` reconstructs its
action on every module element. Applying this reconstruction on the
lifted regular module and using linearity proves that the evaluated
element commutes with every ring element. Evaluation gives injectivity,
and reconstruction gives surjectivity. `RingEquiv.ofBijective` then
produces the ring equivalence with the required forward map.

The proof adds no commutativity, field, finiteness or nontriviality
hypothesis. The zero ring is included. The carrier bound `max u v`
ensures that the category contains the lifted regular module. These
declarations make no assertion for module carriers in an arbitrarily
smaller universe. They also do not state compatibility with varying
ring homomorphisms.

## In the Library

| Module | First appeared at Library commit |
| --- | --- |
| Statements | `b9a5677e7d9363960d4c8b6705892ed2b9e28155` |
| Exact aggregate proof | `d8425b466384657b53f6106e0310f36fe92afff2` |

The proof was checked by a Lake build against the exact target
`Langlands.Renard.ModuleCatCenterIdentificationStatement`, with the statement
and its inputs unchanged. The statement module alone does not prove the
example.

The SHA-256 hashes of the four files, unchanged in the present Library:

| File | SHA256 |
| --- | --- |
| `Langlands/CategoryTheory/RenardModuleCatCenterStatements.lean` | `e783d0fc96cd3ab059a5091bb9a9c62ff7693e72eec42ce0df7c0c539ceb29cc` |
| `Langlands/CategoryTheory/RenardModuleCatCenterStatements.md` | `8d5f6f6797aff523c3d635b637511c05b8fa48ce4d9fba36605333763c11bbaf` |
| `Langlands/CategoryTheory/RenardModuleCatCenter.lean` | `0d224cde02e217c810c5127e315da67164250dd2e15b54ec5486f7ae0abe6801` |
| `Langlands/CategoryTheory/RenardModuleCatCenter.md` | `d8c1d49a77f3ea036422636327df28168a7c059ccc650fa33b4003b59e47fed2` |

## Remaining boundaries

This audit finds no additional target for the A.X passage at its stated
module-carrier size. It does not close the whole Appendix A or book.
The nonunital idempotented-ring center of I.1.7, A.IX decompositions,
and the later Bernstein-center assertions are separate from this passage.
