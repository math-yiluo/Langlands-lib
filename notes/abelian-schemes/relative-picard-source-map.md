# Relative Picard representability: source and construction boundaries

Worker 141, 29 October 2026. This is a source audit for the construction of
an abelian-scheme parameter for rigidified smooth-family Picard classes.
It records no Lean representability proof.

## Sources and reading extent

| Registered original | Passages read |
| --- | --- |
| Faltings–Chai, *Degeneration of Abelian Varieties* (1990), source `provided-0ecad2ee7ec463aef945e9d85a6d369dd775bbbbbd4e55843b9bfb4aa819da7d`, SHA-256 `f53b164d7d783ca55a5b6ae6b0885601264f13f2a2660a1d689813715899f20e` | Chapter I §1, printed pp.1–7/PDF pp.13–19; Theorem 1.9 finishes on printed p.7. PDF pp.14,18–19 were also checked visually. |
| Lan, revised thesis (14 March 2021), source `lan-2008-pel-thesis-revision-2021`, SHA-256 `a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079` | Conventions, PDF p.26; §1.3.1, PDF pp.95–97; §1.3.2, PDF pp.101–102. |
| Lan, author errata (14 March 2021), source `lan-2008-pel-thesis-errata-2021`, SHA-256 `18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d` | PDF pp.1,8–9. |
| Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft, source `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42` | (0.4), PDF p.5; (6.2) and its continuation, PDF pp.92–94; (6.9), PDF p.95; Chapter VI §3, PDF p.99; (7.19)–(7.24), PDF pp.109–111. |

The files are retained under the project `literature/` directory with their
registered titles. Faltings–Chai is the complete 328-page book. No separate
errata accompanied the supplied copy, and no source-specific note was present
in the checked project, Library or workspace `notes/errata/` locations.
This records the checked locations, without asserting that no errata exist.

Lan's errata change the scheme convention to quasi-separatedness and correct
the ordinary Picard quotient to use bundles pulled back from the test scheme
`T`. They also require openness in the stated rigidity argument; arbitrary
flat morphisms cannot be treated as open.

## The unrestricted construction in Faltings–Chai

Definition 1.4, printed p.2, identifies the relative Picard functor with
rigidified line-bundle classes and defines its zero part by algebraic
equivalence on ordinary residue-field fibres. Remark 1.5 asserts fppf
sheafness, openness of the zero subfunctor and formal smoothness. These
assertions need formal proofs before use.

The discussion on printed p.3 quotes Artin's algebraic-space representability
theorem. Its displayed scope requires properness, flatness, finite
presentation and cohomological flatness in dimension zero, with the spaces
locally of finite type over a field or an excellent Dedekind domain.
The discussion then describes the zero part as a proper smooth group
algebraic space and introduces its rigidified Poincare bundle. Passing from
the quoted scope to arbitrary bases requires justified limit arguments;
the description of component geometry is a further mathematical input.

Theorem 1.9, printed pp.5–7, states that every abelian algebraic space over
a scheme is a scheme, as is its Picard functor. Its stronger assertion about
affine neighbourhoods of finite sets over affine base opens is maintained
through the proof sketch. The route is:

1. Reduce to affine bases, then finite-type integer algebras by finite
   presentation, and then reduced bases.
2. Use the correspondence space, its unramified scheme structure, and a
   valuative extension condition. The whole correspondence space need
   not be of finite type; the text explicitly distinguishes this condition
   from properness.
3. Over an integral normal base, extend a generic-fibre polarization using
   the closure of a correspondence section. Apply the Poincare bundle,
   theorem of the cube, Riemann–Roch and semicontinuity to obtain relative
   ampleness. This gives projective families over normalizations of
   irreducible components.
4. Use noetherian induction and amalgamation of components. For an
   irreducible affine base, use its normalization and conductor square.
   The affine-neighbourhood assertion is part of making this gluing work.

This is Deligne's proof of Raynaud's theorem as presented by Faltings–Chai.
It requires formal results about algebraic spaces, correspondences,
polarization extension and scheme gluing. The ring fibre-product identity
in the conductor argument does not by itself construct the global scheme.
The locally projective case alone therefore does not establish the
unrestricted representability target.

## Comparisons with the Library target

The published
[`SmoothFamilyAbelianRepresentabilityStatement`](../../Langlands/AlgebraicGeometry/Picard/SmoothFamilyAbelianRepresentabilityStatement.md)
asks for an actual `B : AbelianScheme S` and
`L : RigidifiedFamily A B.X` over every quasi-separated base. Its unchanged
universal predicate requires both global smooth-family membership and
unique actual pullback classification on every quasi-separated test,
including nonreduced tests.

| Source input | Remaining formal comparison or construction |
| --- | --- |
| Ordinary residue-field algebraic equivalence in Lan and Faltings–Chai | Compare with the Library's explicit witnesses on every algebraically closed field-valued fibre. |
| EVM (6.9), using smooth varieties and divisors | Relate divisors and line bundles to the actual smooth separated finite-type geometrically integral parameters and endpoint restriction isomorphisms in the Library. |
| EVM (7.21)–(7.22), field Picard-zero/kernel comparison | Supply its field cohomology, ampleness and component arguments through their own proof workflows. These passages do not construct a relative representer. |
| EVM (7.24), Neron–Severi quotient | Prove the algebraic-equivalence and geometric-testing bridges for actual bundles. |
| Ordinary quotient, rigidification and Poincare family | Prove normalization, choice independence, the applicable sheaf comparison, and compatibility with actual pullbacks. |
| Source product `A ×_S T` | Use and verify the Library's product transport from its parameter-first relative family. |
| Representability as a sheaf | Retain classification on nonreduced tests; geometric-point bijections alone do not give this universal property. |

EVM (0.4) defines a variety to be separated, of finite type and geometrically
integral, explaining these conditions in the Library's witness.
The trivial-automorphism and rigidification arguments in (6.2) use a section,
the stated compactness and separation conditions, and universal pushforward
of the structure sheaf. A global-functions result alone does not implement
the bundle-endomorphism argument.

## Existing construction interfaces

[`LineBundle.normalize`](../../Langlands/AlgebraicGeometry/Picard/LineBundleNormalization.md)
already constructs an actual normalized rigidified bundle along a section,
given tensor-pullback preservation, an actual inverse base line bundle,
and an evaluation isomorphism. It does not assert inverse existence,
choice independence or the ordinary/fppf comparison.
[`LineBundleDescent`](../../Langlands/AlgebraicGeometry/Picard/LineBundleDescent.md)
is a specialized gluing theorem from compatible sections for an
ample-existence spreading argument; it does not supply Artin
representability or conductor descent.

The source audit does not change any statement or allocate a proof.
The common construction task is
`e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`. Its separately owned ordinary
Picard, comparison, field, topology and gluing workflows, and all their
operator pauses, remain in force. Any required prerequisite must be
independently accepted and published before it is used as a proved input.
