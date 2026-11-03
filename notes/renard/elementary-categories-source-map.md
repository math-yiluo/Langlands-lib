# Renard A.I–A.II: elementary categorical correspondences

Worker 709, 3 November 2026. This note maps the introductory category and
functor notation, A.I.1, the factor-map and order-bound assertions of A.I.2,
the uniqueness and zero-object assertions of A.I.4, and the full/faithful
definitions of A.II.2 to existing Mathlib declarations. It complements the
[category-construction and duality map](category-constructions-source-map.md)
and [equivalence progress map](appendix-a-equivalence-progress.md).
It introduces no new Lean declarations or mathematical artifacts.

## Original source and pinned interfaces

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Original PDF253–257, printed pp.247–251, were read; PDF254 and PDF257 were
also visually inspected. The exact passages used here are:

| Passage | Printed page / one-based PDF page | Content used |
| --- | --- | --- |
| A.I opening paragraphs | 247 / 253 | Objects, Hom, identities, composition, and the object and morphism maps of a functor. |
| A.I.1 and its concluding paragraph | 247–248 / 253–254 | Inverse equations, cancellation definitions, isomorphisms are mono and epi, failure of the general converse, and the abelian converse. |
| A.I.2 | 248 / 254 | Factorization order, monicity of the factor map, subobject classes, intersections and unions, conditional uniqueness, and arbitrary/finite family existence conventions. |
| A.I.4, opening paragraph | 249 / 255 | Initial and terminal unique-Hom conditions, zero iff both conditions, and uniqueness up to isomorphism. |
| A.II.2, paragraph beginning “Le foncteur” after the vector-space example | 251 / 257 | Full, faithful and fully faithful functors, and full subcategories through their inclusions. |

No separate source-specific errata file was found in the inspected Library
or project `notes/errata` locations. This note makes no claim to have read
the references cited by the book for category theory. Other assertions on
these pages, including A.I.3 and the equivalence criterion, are outside
this note's selected scope.

All Mathlib paths below are relative to its source tree at commit
`5ed2965256430c3649e86755f9576b54eca72435`, approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The cited ranges were read.
Use independent object and Hom universes:
`C : Type u₁`, `[Category.{v₁} C]`,
`D : Type u₂`, `[Category.{v₂} D]`.
Lean's `f ≫ g` means the conventional composite `g ∘ f`.

## Category notation, invertibility and cancellation

| Source assertion | Existing Mathlib interface | Correspondence |
| --- | --- | --- |
| Category data and laws | `CategoryTheory.CategoryStruct`, `Mathlib/CategoryTheory/Category/Basic.lean:124–139`; `Category`, same file:235–245 | `X ⟶ Y`, `𝟙 X` and `f ≫ g` supply Hom, identity and composition. The category instance supplies both identity laws and associativity. |
| Functor data and laws | `CategoryTheory.Functor`, `Mathlib/CategoryTheory/Functor/Basic.lean:33–49` | `F.obj` and `F.map` are the actual object and morphism maps; `F.map_id` and `F.map_comp` are the source's preservation conditions. |
| Isomorphism and inverse | `CategoryTheory.Iso`, `Mathlib/CategoryTheory/Iso.lean:53–62`; `IsIso`, same file:238–240; `asIso`, same file:275–277 | An isomorphism contains arrows in both directions and both inverse equations. `IsIso f` asserts the existence of such an inverse for the specified arrow; `asIso f` packages it as an actual isomorphism. |
| Mono and epi definitions | `CategoryTheory.Mono`, `Epi`, `Mathlib/CategoryTheory/Category/Basic.lean:320–331`; cancellation lemmas, same file:333–339, including the generated mono dual | These are cancellation against every test object and parallel pair of arrows, exactly as in A.I.1. |
| Isomorphisms are mono and epi | `CategoryTheory.IsIso.epi_of_iso` and its generated mono dual, `Mathlib/CategoryTheory/Iso.lean:289–293` | Both instances follow from the inverse equations; no abelian hypothesis is used. |

For `f : X ⟶ Y`, the exact propositional readings are

```text
IsIso f ↔
  ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y.

Mono f ↔
  ∀ (Z : C) (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h.

Epi f ↔
  ∀ (Z : C) (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h.
```

An internal example witnesses the source's assertion that the converse
fails in general: in the preorder category on `ℕ`, the arrow `0 ⟶ 1`
from `homOfLE` is mono and epi, since the category is thin. It is not
invertible, since an invertible arrow in a partial order forces equality
of its endpoints. The relevant sources are
`Mathlib/CategoryTheory/Category/Preorder.lean:40–53,63–66,265–272`
and the thin-category cancellation instances in
`Mathlib/CategoryTheory/Category/Basic.lean:385–387`, including the
generated mono dual. Renard does not specify this example.

For the abelian converse, reuse the existing Library theorem
`Langlands.Renard.isoIffMonoAndEpiStatement C` in
[`ImageFactorization`](../../Langlands/CategoryTheory/Renard/ImageFactorization.md).
It proves the criterion for every `[Abelian C]`, with independent object
and Hom universes. Its proof uses Mathlib's
`CategoryTheory.isIso_iff_mono_and_epi`, which requires balancedness.
The instance route is
`Abelian → IsNormalEpiCategory → IsRegularEpiCategory →
StrongEpiCategory → Balanced`; see
`Mathlib/CategoryTheory/Abelian/Basic.lean:103–115`,
`Limits/Shapes/NormalMono/Basic.lean:326–330`,
`Limits/Shapes/RegularMono.lean:699–703`,
`Limits/Shapes/StrongEpi.lean:154–158`, and
`Mathlib/CategoryTheory/Balanced.lean:30–44`, where the three `Limits/`
paths are relative to `Mathlib/CategoryTheory/`.
This reuses the existing proof; the broader comparison of the book's
abelian axioms has its separate
[progress map](abelian-categories-progress.md).

## Subobject factors, bounds and existence conventions

The [duality map](category-constructions-source-map.md) explains why
Mathlib's actual `Subobject X` is the source's quotient of monomorphisms
by mutual factorization, with the same order. Here
`Subobject X : Type (max u₁ v₁)`. Its partial order and representatives
are in `Mathlib/CategoryTheory/Subobject/Basic.lean:101–117,239–241,286–288`.

If `f : A ⟶ X` and `g : B ⟶ X` are the two monomorphisms and
`i : A ⟶ B` satisfies `i ≫ g = f`, then `i` is mono by
`CategoryTheory.mono_of_mono_fac`, the generated dual of the declaration
at `Mathlib/CategoryTheory/Category/Basic.lean:373–375`.
In particular `Subobject.ofMkLEMk` extracts the factor map from an
inequality between represented subobjects; its monicity and factorization
equation are in `Mathlib/CategoryTheory/Subobject/Basic.lean:341–352`.

For `P Q R : Subobject X`, the binary intersection and union definitions
unpack to

```text
IsGLB ({P, Q} : Set (Subobject X)) R ↔
  R ≤ P ∧ R ≤ Q ∧ ∀ S, S ≤ P → S ≤ Q → S ≤ R.

IsLUB ({P, Q} : Set (Subobject X)) R ↔
  P ≤ R ∧ Q ≤ R ∧ ∀ S, P ≤ S → Q ≤ S → R ≤ S.
```

For an independently indexed family `F : I → Subobject X`,
`I : Type w`, the corresponding definitions are

```text
IsGLB (Set.range F) R ↔
  (∀ i, R ≤ F i) ∧ ∀ S, (∀ i, S ≤ F i) → S ≤ R.

IsLUB (Set.range F) R ↔
  (∀ i, F i ≤ R) ∧ ∀ S, (∀ i, F i ≤ S) → R ≤ S.
```

These use `IsGLB`, `IsLUB` and the bound definitions in
`Mathlib/Order/Bounds/Defs.lean:32–52`, including generated order duals.
The partial order gives conditional uniqueness:
if `hP : IsGLB S P` and `hQ : IsGLB S Q`, then `hP.unique hQ : P = Q`,
and the same holds for `IsLUB`. See
`Mathlib/Order/Bounds/Basic.lean:814–826`, including the generated GLB
dual. Equality here is equality of subobject classes. It is not literal
equality of all chosen representative objects.

For each chosen family-index universe `w`, the source's category-wide
existence convention becomes existence of an `R` satisfying the
appropriate displayed condition for every `X : C`,
`I : Type w` and `F : I → Subobject X`. Finite intersections or unions
restrict to `[Finite I]`. This is an explicit universe interpretation of
the source's family convention, not a claim to quantify over every
universe in a single proposition.

The formulas impose no nonempty-family condition. For an empty `I`, the
GLB condition reduces to `∀ S, S ≤ R`, and the LUB condition to
`∀ S, R ≤ S`. Thus the empty cases ask for a greatest and a least
subobject, respectively. Finite families include these empty cases.
No bound-existence, lattice, completeness, well-poweredness, additive or
abelian assumption is needed to state the definitions or their
conditional uniqueness. The source explicitly allows bounds to fail to
exist; the displayed conditions do not assert their existence.

For their relation to actual categorical universal properties, reuse
`Langlands.Renard.SubobjectLimit.subobjectLimitStatements` in
[`SubobjectLimitProof`](../../Langlands/CategoryTheory/Renard/SubobjectLimitProof.md).
It identifies limiting cones and colimiting cocones for the actual
discrete family in `Subobject X` with these GLB and LUB conditions.
It preserves independent object, Hom and index universes and includes
empty families. Its colimits are taken in `Subobject X`; it does not
identify an arbitrary union with a colimit of underlying representatives
in `C`.

## Initial, terminal and zero objects

`CategoryTheory.Limits.IsInitial X` and `IsTerminal X` express the
source's unique-Hom conditions, including existence of the arrow.
The unique-Hom data, their constructors and the generated initial duals
are in `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean:48–87`.
Given two initial objects, `hX.uniqueUpToIso hY` constructs an
isomorphism between them; the same is true for terminal objects.
See the terminal construction and generated initial dual at
`IsTerminal.lean:140–146`.

`CategoryTheory.Limits.IsZero X` is a proposition containing nonempty
unique-Hom data both from and to `X`, in
`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:42–50`.
The precise propositional correspondence is

```text
IsZero X ↔ Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X).
```

The `Nonempty` wrappers are required because `IsInitial` and `IsTerminal`
carry morphism data. `IsZero.isInitial` and `IsZero.isTerminal` give the
forward direction; the reverse packages the two unique-Hom families.
For zero objects `hX : IsZero X` and `hY : IsZero Y`, `hX.iso hY`
gives the source's uniqueness up to isomorphism. These constructions are
in `ZeroObjects.lean:86–100`. They do not require a chosen zero object for
the entire category. Zero morphisms and the kernel/cokernel definitions
are treated in the separate duality map.

## Fullness, faithfulness and actual full subcategories

For `F : C ⥤ D`, Mathlib's `Functor.Full` and `Functor.Faithful` are
propositions in
`Mathlib/CategoryTheory/Functor/FullyFaithful.lean:43–55`.
They give precisely the conditions on every Hom map in A.II.2:

```text
F.Full ↔
  ∀ X Y : C, Function.Surjective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)).

F.Faithful ↔
  ∀ X Y : C, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)).
```

Mathlib also provides the data-valued `F.FullyFaithful`. Its inverse
Hom maps, `ofFullyFaithful`, `homEquiv`, and the induced `full` and
`faithful` properties are in
`FullyFaithful.lean:127–146,159–165,189–193`. Consequently

```text
Nonempty F.FullyFaithful ↔ F.Full ∧ F.Faithful.
```

The equivalence `homEquiv` has forward map `F.map`. Passing from the two
propositions to chosen inverse Hom maps uses the noncomputable
`Functor.FullyFaithful.ofFullyFaithful`.

For `P : ObjectProperty C`, Mathlib's actual `P.FullSubcategory` and
inclusion `P.ι : P.FullSubcategory ⥤ C` are in
`Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:34–46,55–68`.
The inclusion sends `X` to `X.obj` and a morphism `f` to `f.hom`.
The declarations `fullyFaithfulι`, `full_ι` and `faithful_ι`, at
`FullSubcategory.lean:72–97`, implement exactly the full-inclusion
condition. For any `X Y : P.FullSubcategory`,

```text
P.fullyFaithfulι.homEquiv : (X ⟶ Y) ≃ (X.obj ⟶ Y.obj).
```

The Hom type is a tagged induced-category Hom, so this is an explicit
equivalence of Hom types. Its one-field structure and equivalence are in
`Mathlib/CategoryTheory/InducedCategory.lean:59–87`. The full subcategory
keeps object universe `u₁` and Hom universe `v₁`; these need not be equal.
The general source criterion for a specified subcategory inclusion uses
the same surjectivity and injectivity conditions on its Hom maps. The
canonical object-property construction above supplies an actual full
subcategory, without identifying every fully faithful functor with a
literal inclusion.

## Verification and scope

Private Lean-service recovery check
`98e4a2b3-ed3f-4108-ac75-e88f6370b468` compiled these correspondence
probes with zero errors and warnings. It checked category and functor
laws, inverse and cancellation formulas, the monic factor map, both
binary and indexed bound formulas and conditional uniqueness,
initial/terminal/zero uniqueness and the zero iff condition,
full/faithful conditions, the `Nonempty FullyFaithful` correspondence,
the actual full-subcategory Hom equivalence, the abelian criterion, and
the internal natural-number counterexample. Object, Hom and family-index
universes remain independent. These probes are private development
evidence; they are not new independently accepted Lean artifacts.

The existing Library proof modules cited above remain their own
mathematical contributions. This source map adds documentation for
direct reuse. It does not complete A.I, A.II, Appendix A or the
[whole-book program](coverage.md). In particular A.I.3, later categorical
examples and constructions, and the remaining obligations recorded in
the equivalence and coverage maps retain their separate scope.
