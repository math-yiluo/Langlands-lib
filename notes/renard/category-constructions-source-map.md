# Renard A.I.5 and A.II.1: direct category constructions in Mathlib

Worker 709, 3 November 2026. This source map identifies the existing Mathlib
constructions for the product and opposite categories, the four duality
pairs named in A.I.5, and the definitions in A.II.1. It supplements the
[whole-book ledger](coverage.md) and the
[A.II.2 equivalence audit](appendix-a-equivalence-progress.md).
The named Mathlib objects are reused directly; no additional Renard aliases
or mathematical artifacts are introduced by this note.

## Source and environment

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.I.5 and A.II.1 are on printed p.250 / one-based PDF256 of
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The original page was reread and visually inspected, including its
naturality square and inverse-transformation equations. For the named duality
pairs, A.I.1 on printed p.247 / PDF253, A.I.2 on printed p.248 / PDF254, and
A.I.4 on printed p.249 / PDF255 were also reread; PDF255 was visually
inspected. The source hash was rechecked. No source-specific Renard errata
file was found in the supplied Library or project `notes/errata` locations.

All Mathlib paths below are relative to its source root and refer to commit
`5ed2965256430c3649e86755f9576b54eca72435`, in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. These source ranges were read.
Take independent universes
`C : Type u₁`, `[Category.{v₁} C]`,
`D : Type u₂`, `[Category.{v₂} D]`.
Lean's `f ≫ g` denotes the conventional composite `g ∘ f`.

## Assertion-level correspondence

| Original passage, printed p.250 / PDF256 | Existing declaration and source | Exact correspondence |
| --- | --- | --- |
| A.I.5, first two sentences: product category | `CategoryTheory.prod` and `CategoryTheory.prod'`, `Mathlib/CategoryTheory/Products/Basic.lean:44–48,106–110` | Objects are actual pairs in `C × D`. The Hom type is definitionally `(X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)`. Identity and composition are componentwise; the category instance includes the category laws. |
| A.I.5, opposite category | `CategoryTheory.CategoryStruct.opposite`, `CategoryTheory.Category.opposite`, `Mathlib/CategoryTheory/Opposites.lean:73–76,111–119`; `Quiver.Hom.opEquiv`, `Mathlib/Combinatorics/Quiver/Basic.lean:53–69` | Objects are the tagged copy `Cᵒᵖ`. `op` and `unop` identify its objects with those of `C`. The explicit Hom equivalence `(X ⟶ Y) ≃ (op Y ⟶ op X)` accounts for Mathlib's tagged morphisms. `CategoryTheory.op_comp`, `Opposites.lean:86–88`, proves reversal of composition. |
| A.II.1, component family and commuting square | `CategoryTheory.NatTrans`, `Mathlib/CategoryTheory/NatTrans.lean:53–57` | A transformation from `F` to `G` has `app X : F.obj X ⟶ G.obj X` and `naturality f : F.map f ≫ app Y = app X ≫ G.map f`. This is precisely the displayed source square. |
| A.II.1, functor category and its Hom sets | `CategoryTheory.Functor.category`, `Mathlib/CategoryTheory/Functor/Category.lean:53–56` | Objects are the actual functors `C ⥤ D`; the Hom type from `F` to `G` is definitionally `NatTrans F G`. The instance includes identities, composition and category laws. |
| A.II.1, identity natural transformation | `CategoryTheory.NatTrans.id`, `NatTrans.lean:82–87`; `CategoryTheory.NatTrans.id_app`, `Functor/Category.lean:72–73` | The component of `𝟙 F` at `X` is `𝟙 (F.obj X)`. The composition used in the source's inverse equations is vertical composition: `NatTrans.vcomp`, `NatTrans.lean:97–106`, and `NatTrans.comp_app`, `Functor/Category.lean:75–77`, give `(α ≫ β).app X = α.app X ≫ β.app X`. |
| A.II.1, invertible natural transformation | `CategoryTheory.Iso` applied in `C ⥤ D`, `Mathlib/CategoryTheory/Iso.lean:53–62` | An actual `F ≅ G` consists of `hom : F ⟶ G`, `inv : G ⟶ F`, `hom ≫ inv = 𝟙 F` and `inv ≫ hom = 𝟙 G`. These are the source's two inverse-transformation equations in Lean's composition order. Both morphisms include naturality. |
| A.II.1, final paragraph: identity functor | `CategoryTheory.Functor.id`, `Mathlib/CategoryTheory/Functor/Basic.lean:80–87`; `Functor.id_obj` and `Functor.id_map`, same file:94–98 | `𝟭 C` sends each object and each morphism to itself, exactly as in the source. |

The product has Hom universe `max v₁ v₂`; the opposite preserves `v₁`.
The functor category has Hom universe `max u₁ v₂`, because natural
transformations quantify over objects of `C`. No equality between the four
universe parameters, smallness, nonemptiness, additivity or finiteness is
assumed.

Mathlib's opposite-category Hom is a tagged copy of the reversed original
Hom, so the correspondence uses `Quiver.Hom.opEquiv`, rather than claiming a
literal equality of those types. Product Hom and functor-category Hom have
the definitional equalities stated in the table.

For natural isomorphisms, the existential formulation of the source data is

```text
Nonempty (F ≅ G) ↔
  ∃ (α : F ⟶ G) (β : G ⟶ F),
    α ≫ β = 𝟙 F ∧ β ≫ α = 𝟙 G.
```

This correspondence simply unpacks or constructs `Iso`; it does not require
an additional hypothesis that the components be invertible. A.II.1 defines
an invertible natural transformation by its inverse natural transformation.
The page does not separately state a theorem characterizing natural
isomorphisms by componentwise invertibility.

## The four duality pairs in A.I.5

The definitions being paired occur in A.I.1, A.I.2 and A.I.4. For this
comparison fix independent universes `C : Type u`, `[Category.{v} C]`.
All paths in the following table remain at the Mathlib pin above.

| Pair named in A.I.5, printed p.250 / PDF256 | Existing declaration and source | Exact correspondence |
| --- | --- | --- |
| Monomorphism / epimorphism; definitions A.I.1, printed p.247 / PDF253 | `CategoryTheory.Mono` and `CategoryTheory.Epi`, `Mathlib/CategoryTheory/Category/Basic.lean:320–331`; `op_epi_iff`, `op_mono_iff`, `unop_epi_iff`, `unop_mono_iff`, `Mathlib/CategoryTheory/EpiMono.lean:27–43` (including generated duals) | The two cancellation definitions are exactly the source definitions. `Mono f` is equivalent to `Epi f.op`, and `Epi f` to `Mono f.op`. The `unop` equivalences give the converses for morphisms initially in the opposite category. |
| Subobject / quotient object; definitions A.I.2, printed p.248 / PDF254 | `CategoryTheory.Subobject`, its `PartialOrder` instance and `Subobject.mk`, `Mathlib/CategoryTheory/Subobject/Basic.lean:100–117`; `mk_le_mk_of_comm`, `mk_surjective`, `ofMkLEMk`, `ofMkLEMk_comp`, same file:239–241,286–288,341–352 | `Subobject X` is the ordered collection of monomorphisms into `X` modulo mutual factorization. A quotient represented by an epi `p : X ⟶ A` is represented by `Subobject.mk p.op : Subobject (op X)`. The existing order agrees with Renard's quotient order, as detailed below. |
| Initial / final object; definitions A.I.4, printed p.249 / PDF255 | `CategoryTheory.Limits.IsInitial`, `IsTerminal`, `isTerminalEquivUnique`, `IsTerminal.ofUnique`, `IsTerminal.from`, `IsTerminal.hom_ext`, `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean:48–87,110–123`, with generated initial duals; `IsInitial.op`, `IsInitial.unop` and generated terminal duals, same file:312–322 | The data are equivalent to a unique morphism from, respectively to, the object for each other object. Opposite transport exchanges initial and terminal objects, with inverse transport by `unop`. |
| Kernel / cokernel; definitions A.I.4, printed p.249 / PDF255 | `CategoryTheory.Limits.KernelFork.ofι`, `KernelFork.IsLimit.lift'`, `KernelFork.IsLimit.ofι`, `Mathlib/CategoryTheory/Limits/Shapes/Kernels.lean:91–93,127–155`; `CokernelCofork.ofπ`, `CokernelCofork.IsColimit.desc'`, `CokernelCofork.IsColimit.ofπ`, same file:593–595,612–642; the four opposite/unop transport maps, `Mathlib/CategoryTheory/Limits/Shapes/Opposites/Kernels.lean:37–79` | The limit fork and colimit cofork encode the source's vanishing composite and unique-factorization properties. `KernelFork.IsLimit.ofιOp` and `CokernelCofork.IsColimit.ofπOp` exchange them in the opposite category; `ofιUnop` and `ofπUnop` transport back. Only `HasZeroMorphisms C` is needed for these maps; existence of every kernel or cokernel is not assumed. |

For the subobject row, `MonoOver X` is the thin category of monomorphisms
into `X`; see `Mathlib/CategoryTheory/Subobject/MonoOver.lean:56–76,109–145`.
`Subobject X` is its `ThinSkeleton`, with its existing partial order.
For monos `i : A ⟶ X` and `j : B ⟶ X`, the order correspondence is

```text
Subobject.mk i ≤ Subobject.mk j ↔ ∃ a : A ⟶ B, a ≫ j = i.
```

`Subobject.ofMkLEMk` and `ofMkLEMk_comp` extract the factorization;
`mk_le_mk_of_comm` constructs the inequality. Consequently equality of
classes is exactly factorization in both directions, by antisymmetry. This
also explains why the quotient by isomorphisms used by `ThinSkeleton` agrees
with the source's quotient by mutual factorization in this thin category.

For epis `p : X ⟶ A` and `q : X ⟶ B`, applying those same declarations in
`Cᵒᵖ` gives

```text
Subobject.mk p.op ≤ Subobject.mk q.op ↔ ∃ a : B ⟶ A, q ≫ a = p.

Subobject.mk p.op = Subobject.mk q.op ↔
  (∃ a : B ⟶ A, q ≫ a = p) ∧ (∃ b : A ⟶ B, p ≫ b = q).
```

These are precisely the preorder and equivalence relation printed in
A.I.2. No extra `OrderDual` is applied to `Subobject (op X)`.
`Subobject.mk_surjective` in the opposite category, followed by `unop`,
shows that every element is represented by an actual epi out of `X`.
The resulting collection has type `Type (max u v)`; there is no
`WellPowered`, abelian, smallness or quotient-existence hypothesis here.
This is a correspondence with the existing Mathlib object, not a claim that
this note introduces a separate quotient-object type or an order-isomorphism
declaration in the Renard namespace.

Initial and terminal universal properties in Mathlib contain morphism data.
Their propositional forms therefore use `Nonempty`; for example

```text
Nonempty (IsInitial X) ↔ Nonempty (IsTerminal (op X)).
```

`IsInitial.op` supplies the forward map and `IsTerminal.unop` the reverse.
Likewise `IsTerminal.op` and `IsInitial.unop` exchange the other pair.
The unique-Hom characterization uses `Unique (X ⟶ Y)` or
`Unique (Y ⟶ X)`, not merely uniqueness without existence.

The source defines zero morphisms by factoring through a zero object.
`HasZeroObject.zeroMorphismsOfZeroObject`, in
`Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean:228–248`, supplies
exactly that construction when installed explicitly as a local instance.
With any existing `HasZeroMorphisms C`, the composite through an `IsZero`
object equals the existing zero by `IsZero.eq_zero_of_src` (same file:163–165)
and `comp_zero`. Thus the kernel/cokernel comparison below respects the
source's zero-object hypothesis while using Mathlib's more general
zero-morphism interface. The constructor is noncomputable and is not a
global instance.

For `i : K ⟶ X`, `f : X ⟶ Y`, and `w : i ≫ f = 0`, the kernel condition is

```text
Nonempty (IsLimit (KernelFork.ofι i w)) ↔
  ∀ (L : C) (l : L ⟶ X), l ≫ f = 0 → ∃! t : L ⟶ K, t ≫ i = l.
```

For `f : X ⟶ Y`, `p : Y ⟶ Q`, and `w : f ≫ p = 0`, the cokernel condition is

```text
Nonempty (IsColimit (CokernelCofork.ofπ p w)) ↔
  ∀ (L : C) (l : Y ⟶ L), f ≫ l = 0 → ∃! t : Q ⟶ L, p ≫ t = l.
```

The `lift'`/`desc'` maps supply the factorizations; limit/colimit uniqueness
supplies their uniqueness. Conversely `KernelFork.IsLimit.ofι` and
`CokernelCofork.IsColimit.ofπ` build the universal data from these unique
factorizations. Reversing arrows sends a kernel arrow `i` to a cokernel
arrow `i.op` of `f.op`, and a cokernel arrow `p` to a kernel arrow `p.op` of
`f.op`. The four maps named in the table prove both directions of the
corresponding `Nonempty` equivalences. This does not impose global kernel
or cokernel existence or select a preferred universal arrow.

There is a local typesetting error in the two cokernel vanishing displays
in A.I.4, printed p.249 / PDF255: the composites start at `X`, but the
right-hand zero arrows are printed with source `Y`. Their types require
zero arrows from `X` to `Q` (the source calls the cokernel object `K`) and
from `X` to `L`. The equations above use these correctly typed zeros. The
surrounding unique-factorization requirement and the explicit duality
sentence determine this correction; no extra mathematical hypothesis is
introduced.

## Development verification and remaining obligations

Private Lean-service check `e623464a-8e88-42a5-92a6-35c9ea8019b1`
completed with zero errors or warnings. With all four universe parameters
independent, its examples check the three category instances, product Hom,
the opposite Hom equivalence and composition reversal, functor-category Hom,
construction from a component family and naturality square, naturality
itself, vertical composition, identity components, both directions of the
displayed inverse-data correspondence, and the identity functor's object and
morphism maps. The naturality constructor uses explicit object and morphism
binders; passing its polymorphic hypothesis directly to an anonymous
constructor had failed elaboration in the earlier private probe.
This is development evidence for the correspondence, not independent
mathematical acceptance.

Private Lean-service recovery check `628e1492-5d1b-4323-9261-3bbcca742b67`
completed the four duality-pair probes with zero errors or warnings. It
checks the cancellation equivalences; both initial/terminal transports and
unique-Hom characterizations; the two order correspondences, class-equality
criteria and epi representation of every `Subobject (op X)`; both directions
of the kernel/cokernel opposite correspondences; both displayed
unique-factorization characterizations; and zero-morphism construction and
compatibility. Object and Hom universes remain independent. An earlier
probe failed only because the zero-object constructor needed a
`noncomputable` context; the reported successful check includes that fix.
These are private development checks for the source correspondence, not
independent acceptance or a new Lean publication.

The concluding general instruction in A.I.5 to reverse arrows describes a proof
translation principle; it is not treated here as a theorem quantifying over
all possible categorical statements. The paragraph's convention of
expressing contravariant functors using opposite categories is recorded as
notation and interpretation, without claiming a separate comparison theorem
for every later contravariant construction.

This note does not cover the remaining A.I definitions, assertions and examples or
assert completion of A.I, A.II, Appendix A or the book. The A.II.2 mathematical
publications and their proof evidence remain recorded in the separate
equivalence audit.
