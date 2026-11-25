# Renard VI.6.1: the uniform canonical Jacquet section

This source map, dated 4 November 2026, covers VI.6.1, printed pp.176–177 /
PDF pp.182–183, in David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026. The original pages were read,
including the weak Jacquet theorem, its admissibility corollary, the subsequent
single-image construction and the independence Proposition.

The registered reference is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The structural inputs are the actual-object predicates corresponding to
V.5.2(ii)–(iv), printed p.123 / PDF p.129, with their provenance and discharge
obligations retained in the [Chapter V ledger](chapter-v-structural-inputs.md).

## Source assertions and interfaces

| Source assertion | Current Library interface | Exact scope and remaining obligation |
| --- | --- | --- |
| VI.6.1 Theorem, printed176/PDF182: the actual quotient sends `V^K` onto `(V_N)^(K ∩ M)` | `Langlands.Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction`, in [IwahoriContractionAdmissibility](../../Langlands/Representation/Jacquet/IwahoriContractionAdmissibility.md) | A generic proof for the actual coinvariant quotient, given one explicit `IsIwahoriContraction` and finite dimensionality of `V^K`. Admissibility supplies that finiteness. The contraction inputs remain visible. |
| (VI.6.1.1), printed176/PDF182: compression intertwines the quotient and the unnormalized descended action | `Langlands.Jacquet.mk_compressedAction_of_iwahoriContraction`, in the same module | The equality concerns the actual compact average after the group action, the actual quotient map and its descended action. |
| Corollary, printed176–177/PDF182–183: unnormalized and normalized Jacquet restriction preserve admissibility | `Langlands.Jacquet.isAdmissible_action_of_iwahoriContraction`; `Langlands.Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction`, in [JacquetAdmissibility](../../Langlands/Representation/Aubert/General/JacquetAdmissibility.md) | Both proofs retain `HasIwahoriContractionBasis`. The actual-standard adapter `SimultaneousStandardBasisAt.hasIwahoriContractionBasis`, in [JacquetAdapterProof](../../Langlands/BruhatTits/SpecialCompact/JacquetAdapterProof.md), derives that predicate from the simultaneous basis and an actual standard cocharacter. Global structural existence and the whole-book model comparisons retain their own obligations. |
| Uniform kernel annihilation (VI.6.1.2), printed177/PDF183 | `Langlands.Jacquet.StandardCanonicalSectionStatement`, in [StandardCanonicalSectionStatement](../../Langlands/Representation/Jacquet/StandardCanonicalSectionStatement.md) | The published target chooses one positive threshold before quantifying every contracting point in the actual chamber. Its proof is `Langlands.Jacquet.standardCanonicalSection` (below). |
| Subsequent single-image isomorphism, kernel equality and direct sum, printed177/PDF183 | The same target | It asserts bijectivity of the restricted quotient on the image of one compression and `IsCompl` of that compression's kernel and image. The image is not defined to be an all-power stable image. Equality with the published stable image and generalized-kernel comparison are explicit derived conclusions. |
| Independence Proposition and inverse section, printed177/PDF183 | The same target, using the actual maps in [CompressedImageLift](../../Langlands/Representation/Jacquet/CompressedImageLift.md) | One linear right inverse is chosen before every point in a nonempty chamber. Its range is every single compression image, and every inverse restricted quotient is that same section. This gives independence from the contracting point for the specified data and `K`. |

The weak Jacquet theorem and its stable-image proof do not by themselves give
the uniform single-image independence assertion. The published
`compressedImageLift` construction provides an inverse under supplied
bijectivity, and equality of lifts under supplied image equality; those
representation-theoretic conclusions are proved separately (below).

## Statement and proof

The exact statement `Langlands.Jacquet.StandardCanonicalSectionStatement` first
appeared in the Library at commit `c5e0296f115eacde9bd491a7ea70fec6983c1c1c`.

The target uses the shared actual connected reductive group, canonical
rational-point topology, maximal split torus, standard subgroups and
compatible split component. It permits either local-field characteristic and
independent field and representation-carrier universes. Standard-cocharacter
existence, Levi normalization and the local Chapter V basis-member conditions
remain explicit. It adds no central-character or finite-dimensionality
hypothesis on the whole representation.

The Library proves it, as `Langlands.Jacquet.standardCanonicalSection` in
[StandardCanonicalSectionProof](../../Langlands/Representation/Jacquet/StandardCanonicalSectionProof.lean).
A Lake build and declaration inspection of the proof as first written found zero
errors or warnings, independent universes and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The proof's argument differs from Renard's. Span induction on the
actual Jacquet relations gives uniform annihilation for each vector, and a
finite spanning set gives one threshold for the fixed quotient kernel.
Published Fitting and contraction results give the single-image consequences.
Positive integral cocharacter pairings give chamber nonemptiness. Compression
multiplicativity puts a product image inside both factor images; quotient
surjectivity on the smaller image and injectivity on each larger image give
equality. The published inverse laws then yield the common section. The
proof file's Markdown page explains this route; no new structural or
representation-theoretic premise is introduced.

## Retained scope

The source Proposition compares contracting points in the same component
chamber. The target does not assert independence of the auxiliary
standard presentation, compatible component, uniformizer or `K`. Those
comparisons, global structural existence, the nonadmissible version in VI.9.1,
opposite pairing and second adjointness remain separate obligations.
VI.6.2–VI.6.4 and the rest of the chapter are not closed by this map.
