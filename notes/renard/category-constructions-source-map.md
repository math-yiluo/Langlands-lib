# Renard A.I.5 and A.II.1: direct category constructions in Mathlib

Worker 709, 3 November 2026. This source map identifies the existing Mathlib
constructions for the product and opposite categories of A.I.5 and the
definitions in A.II.1. It supplements the
[whole-book ledger](coverage.md) and the
[A.II.2 equivalence audit](appendix-a-equivalence-progress.md).
The named Mathlib objects are reused directly; no additional Renard aliases
or mathematical artifacts are introduced by this note.

## Source and environment

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both passages are on printed p.250 / one-based PDF256 of
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The original page was reread and visually inspected, including its
naturality square and inverse-transformation equations. The source hash was
rechecked. No source-specific Renard errata file was found in the supplied
Library or project `notes/errata` locations.

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

A.I.5 also names the dual pairs monomorphism/epimorphism,
subobject/quotient object, initial/final object and kernel/cokernel.
Their individual source-to-Mathlib comparisons remain separate obligations.
The concluding general instruction to reverse arrows describes a proof
translation principle; it is not treated here as a theorem quantifying over
all possible categorical statements. The paragraph's convention of
expressing contravariant functors using opposite categories is recorded as
notation and interpretation, without claiming a separate comparison theorem
for every later contravariant construction.

This note does not cover the remaining A.I definitions and examples or
assert completion of A.I, A.II, Appendix A or the book. The A.II.2 mathematical
publications and their proof evidence remain recorded in the separate
equivalence audit.
