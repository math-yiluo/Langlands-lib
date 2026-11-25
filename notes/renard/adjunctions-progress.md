# Renard A.V: adjunctions and scalar extension

The source and the Library declarations below were checked on 2 November 2026
against Library commit `facdf46f0abfca9e85d49d3a35285c513a96d886`. This
focused source-to-declaration map is part of the whole-book coverage
([coverage.md](coverage.md)).

## Source and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.V.1–2 occupies printed pp.258–261 / one-based PDF264–267. Those four
original pages were read in full and compared with the twelve Lean/Markdown
pairs identified below.

The supplementary source `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, was also read. Its scalar-example corrections concern
A-linearity and parentheses; both are already incorporated in the governing
2026 example. The older errata's Hom subscript does not repair the typing
issue in the displayed map for `L_G`.

Write `G : B ⥤ A` and `F : A ⥤ B` for the categorical discussion.
In A.V.1 the displayed isomorphism goes from
`Hom_B(Y, F X)` to `Hom_A(G Y, X)`. Its forward map is the inverse of
Mathlib's `adj.homEquiv Y X`. The converse construction in A.V.2 and
the scalar example use the opposite direction for the letter theta.
The implementations retain these directions explicitly.

Two printed formulas require typing corrections. The Hom labels in the
`L_G` morphism-map formula must refer to category A, since `G Y` and X
are objects of A. In the definition of the counit at X on
printed259/PDF265, the identity is that of `F(X)`; the printed `F(Y)`
has the wrong variable. These corrections agree with the actual
Hom-bifunctor and counit declarations.

## Source assertions and current declarations

Each name below is in the displayed namespace. The module links lead to
the paired explanations of the actual Lean declarations.

| Source passage | Namespace and declarations | Checked content |
| --- | --- | --- |
| A.V.1, printed258/PDF264: Hom bifunctors and adjointness | `Langlands.Renard.AdjunctionHom`: `rightHomBifunctor`, `leftHomBifunctor`, `HomAdjunction`; [module](../../Langlands/CategoryTheory/Renard/AdjunctionHom.md) | Actual Hom sets, simultaneous precomposition and postcomposition, functor laws, and existence of their natural isomorphism |
| A.V.1–2: comparison with the unit–counit formulation | `Langlands.Renard.HomAdjunctionComparison`: `NativeToHomStatement`, `HomToNativeStatement`, `HomAdjunctionIffNativeStatement`, proved together by `homAdjunctionComparisonStatements`; [statements](../../Langlands/CategoryTheory/Renard/HomAdjunctionComparisonStatements.md), [proof](../../Langlands/CategoryTheory/Renard/HomAdjunctionComparisonProofs.md) | Both directions preserve the component maps of the specified Hom isomorphism; existence is equivalent to `Nonempty (G ⊣ F)` |
| A.V.1, printed258–259/PDF264–265: representability criterion | `Langlands.Renard.AdjointRepresentability`: `RightAdjointRepresentabilityStatement`, proved by `rightAdjointRepresentability`; [statements](../../Langlands/CategoryTheory/Renard/AdjointRepresentabilityStatements.md), [proof](../../Langlands/CategoryTheory/Renard/AdjointRepresentability.md) | Existence of an actual right adjoint is equivalent to representability of every actual presheaf `G.op ⋙ yoneda.obj X` |
| Same passage: uniqueness of both adjoints | Same namespace: `RightAdjointUniquenessStatement`, `LeftAdjointUniquenessStatement`, proved by `rightAdjointUniqueness`, `leftAdjointUniqueness` | Natural isomorphisms between any two right adjoints, or any two left adjoints, of the same functor |
| A.V.2, printed259/PDF265: unit, counit, naturality and triangles | `Langlands.Renard.UnitCounit`: `UnitCounitAtIdentitiesStatement`, `UnitCounitNaturalityStatement`, `TriangleIdentitiesStatement`; [statements](../../Langlands/CategoryTheory/Renard/UnitCounitStatements.md), [proof](../../Langlands/CategoryTheory/Renard/UnitCounitProofs.md) | Identity-image formulas, actual natural-transformation component equations and both triangles, all included in theorem `unitCounitStatements` |
| Same passage: converse Hom maps and adjunction quadruple | Same namespace: `HomEquivFormulasStatement`, `HomMapNaturalityStatement`, `HomMapInverseIdentitiesStatement`, `AdjunctionFromUnitCounitStatement` | Explicit Hom formulas; simultaneous naturality for arbitrary supplied unit and counit; inverse identities from the triangles; an adjunction with exactly those supplied transformations |
| A.V.2, printed260/PDF266: preservation theorem | `Langlands.Renard.AdjunctionPreservation`: `RightAdjointPreservesLimitsStatement`, `LeftAdjointPreservesColimitsStatement`, proved together by `adjunctionPreservationStatements_proof`; [statements](../../Langlands/CategoryTheory/Renard/AdjunctionPreservationStatements.md), [proof](../../Langlands/CategoryTheory/Renard/AdjunctionPreservationProof.md) | A right adjoint maps every supplied limiting cone to a limiting cone; a left adjoint maps every supplied colimiting cocone to a colimiting cocone |
| A.V.2, printed260–261/PDF266–267: extension and restriction in the example | `Langlands.Algebra.UnitalScalarExtension`: `Tensor`, `tmul`, `functor`, `restriction`, `subalgebraFunctor`, `subalgebraRestriction`, `coefficient_balanced`; [construction](../../Langlands/Algebra/UnitalScalarExtension.md) | Actual balanced quotient, residual unital A-action, maps, functor laws, native restriction and the source's subalgebra specialization |
| Same example: theta, sigma, inverse laws, naturality, unit, counit and triangles | `Langlands.Algebra.UnitalScalarExtensionAdjunction`: `ScalarExtensionAdjunctionStatements`, proved by `scalarExtensionAdjunctionStatements`; [statements](../../Langlands/Algebra/UnitalScalarExtensionAdjunctionStatements.md), [proof](../../Langlands/Algebra/UnitalScalarExtensionAdjunctionProofs.md) | One explicitly constructed adjunction satisfies all seven property families, including the pointwise formulas and their relation to its unit and counit |

The Hom bifunctors retain independent object and Hom universes for both
categories. `ULift` puts the two Hom sets in `Type (max vA vB)` with their
canonical bijections; it imposes no equality between `vA` and `vB`.
The representability, uniqueness, comparison and unit–counit results also
have four independent universes. Preservation adds independent object and
Hom universes for the diagram category. Its target is the universal
property of `F.mapCone t` or `G.mapCocone t`; there is no premise that the
target category already has the relevant limit or colimit.

## Implemented proof routes and composition

The general Hom comparison constructs `homIsoOfAdjunction` by lifting
the native Hom equivalence and its inverse. In the converse,
`coreHomEquivOfHomIso` reads the supplied isomorphism's components and
naturality, and `adjunctionOfHomIso` applies `Adjunction.mkOfHomEquiv`.
Both component equations are proved for that same supplied isomorphism.

Consequently the source formulation composes with the other published
families. Given a source Hom isomorphism, `adjunctionOfHomIso` supplies
the native adjunction to which `unitCounitStatements` and the
preservation results apply. In the other direction,
`AdjunctionFromUnitCounitStatement` supplies an adjunction with the
specified transformations, and `homIsoOfAdjunction` gives the source Hom
isomorphism. The representability criterion and both uniqueness results
transfer through the same comparison. These are applications of the
published declarations; this note introduces no additional Lean theorem.

The representability proof uses Mathlib's
`rightAdjointObjIsDefined_of_adjunction`,
`isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`,
`G.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`. Uniqueness uses
`rightAdjointUniq` and `leftAdjointUniq`. This implements an alternate
route to the printed Yoneda/quasi-inverse construction.

The unit–counit proof reads the identity formulas, naturality and triangles
from native adjunctions. For arbitrary supplied transformations it proves
naturality by functoriality and reassociation, proves inverse laws using
their naturality and the two triangles, and constructs the adjunction
with those exact transformations. Preservation uses Mathlib's
`rightAdjoint_preservesLimits` and `leftAdjoint_preservesColimits` on the
supplied cone or cocone. This cone-level route establishes the existence
and universal property needed by the source's displayed Hom argument.

In the scalar example, A is a unital complex algebra and B is interpreted
as a unital subalgebra: restriction must land in unital B-modules.
The construction generalizes internally to every unital ring homomorphism
`φ : B →+* A`, with possibly noncommutative rings. Its tensor carrier is
the quotient of `A ⊗[ℤ] M` by the integer span of the balancing relations
`(a * φ b) ⊗ m - a ⊗ (b • m)`. The residual action is proved unital;
no tensor object or universal property is supplied as an assumption.
For `S : Subalgebra ℂ A`, specialize to `S.val.toRingHom`.
`coefficient_balanced` verifies the compatibility of the coefficient
action induced from S.

The scalar proof defines the unit by `x ↦ 1 ⊗ x` and descends the balanced
action pairing to the counit `a ⊗ y ↦ a • y`. Pure-tensor extensionality
proves its A-linearity, naturality and the left triangle; the right
triangle reduces to `1 • y = y`. These maps construct a native
adjunction. Its Hom equivalence computes theta as `f ↦ (x ↦ f (1 ⊗ x))`
and sigma by `g ↦ (a ⊗ x ↦ a • g x)`; the same adjunction supplies the
whole-map inverse laws and simultaneous naturality. Applying the general
Hom comparison gives its source Hom-bifunctor formulation as well.

The ring universes `uB`, `uA` and module parameter `uM` are independent.
The tensor carrier has level `max uA uM`, and the bundled extension
adjunction uses that carrier level in both module categories. This bound
comes from the actual integer tensor quotient. It does not require the
rings to share a universe.

## In the Library

All twelve modules are in the Library. Definition and statement modules are
distinguished from proof modules in the table.

| Module | Kind | First appeared at Library commit |
| --- | --- | --- |
| Hom foundation | definition | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Hom comparison statements | statement | `4f2e1785a3faf187359b2dcec3c8bdbe4a70e762` |
| Hom comparison proof | proof | `b1c8a5e809be36100da09da81385a7ca6789ae80` |
| Representability and uniqueness statements | statement | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Representability and uniqueness proof | proof | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Unit–counit statements | statement | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Unit–counit proof | proof | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Preservation statements | statement | `4f255c2d810d0998369347f03338826ce587c35b` |
| Preservation proof | proof | `e3944f764d2c00d53ac87227e98601bb667f348f` |
| Scalar construction | definition | `a5dff2ff93bd3637a67ee8847f67f811efc82f01` |
| Scalar statements | statement | `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10` |
| Scalar proof | proof | `b1c8a5e809be36100da09da81385a7ca6789ae80` |

Each of the five proofs (Hom comparison, representability, unit–counit,
preservation, scalar adjunction) was checked by a Lake build against its exact
target, with the statement and its inputs unchanged.

All twenty-four Lean/Markdown files in the checked Library match the versions
first published. A separate build of the scalar proof completed with
zero errors or warnings and only the standard `propext`,
`Classical.choice`, `Quot.sound` assumptions.

This note records the A.V source correspondences and the checked
composition of its published results. The A.V row of the
[whole-book ledger](coverage.md) links this map.
Other Appendix A sections, Appendices B/C and the chapters
retain their respective obligations. No appendix or book completion is
declared here.
