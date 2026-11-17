# Flat affine-base ampleness reflection and supplied representers

The following internal constructions and their accompanying theorems are
independently accepted and published in Library commit
`d210ab55a138c1f91b826ee47c6280ce6c6b90bc`. Import them by their Lean names.
They provide the geometric reflection step for polarized representability
descent without a noetherian hypothesis.

| Module in `Langlands.AlgebraicGeometry` | Main declaration and scope |
| --- | --- |
| [`Modules.FlatSupportedSectionCoefficients`](../../Langlands/AlgebraicGeometry/Modules/FlatSupportedSectionCoefficients.md) | `Modules.FlatBaseChange.scalarKernelImage` constructs the scalar extension of a kernel inclusion. Flatness identifies its image with the extended kernel. |
| [`Picard.FlatBaseChangeAmpleReflection`](../../Langlands/AlgebraicGeometry/Picard/FlatBaseChangeAmpleReflection.md) | `Picard.LineBundle.isAmple_of_affine_flat_surjective_baseChange` reflects ampleness of a specified actual line bundle in a Cartesian square over a flat surjective map between affine schemes. |
| [`Picard.PolarizedRepresenterGeometricReflection`](../../Langlands/AlgebraicGeometry/Picard/PolarizedRepresenterGeometricReflection.md) | `Picard.geometricReflection_of_representable` reflects smoothness, properness and universal-bundle ampleness for a supplied global representer. |

The ampleness theorem takes affine schemes `S,T`, a flat surjective
`b : T ⟶ S`, morphisms `f : X ⟶ S`, `f' : Y ⟶ T` and `g : Y ⟶ X`,
and `IsPullback g f' f b`. For an actual `L : LineBundle X`, ampleness
of `(LineBundle.pullback g).obj L` implies `L.IsAmple`. There are no
field, noetherian, finite-type or separatedness assumptions.

The proof obtains compactness and quasi-separatedness downstairs from
the ample pullback. Canonical flat base change then compares sections
on the scheme and on a closed complement. A positive power of a suitably
supported upstairs section vanishes on the pulled-back complement,
including when it is nonreduced. Flat kernel coefficients yield a
downstairs section vanishing on the complement and generating at the
chosen point. Its whole generation open is affine by the existing affine
generation-locus result. This generalizes the field proof; no
noetherian fibrewise-to-global ampleness theorem is used.

The coefficient lemma
`Modules.DerivedSections.FlatBaseChange.exists_vanishing_coefficient_generating`
retains two explicit canonical sections-isomorphism hypotheses.
The algebraic coefficient step needs flatness, without faithful flatness;
the ampleness theorem also uses surjectivity to choose points upstairs.

For geometric reflection, supply both a global representation
`eN : F.RepresentableBy N` and a representation `eM` after the affine
flat surjective base change, together with the coherent actual bundle
`L : PresheafLineBundle F`. Smoothness and properness of the local
representer and ampleness of its universal bundle imply the same
properties for `N` and `L.universal eN`. The scheme and value universes
remain independent. The comparison isomorphism is constructed by
`localRepresenterComparison`. The integrated actual bundle comparison is
`PresheafLineBundle.universalBaseChangePullbackIso L eN p`.

These results retain global representability as a premise. They do not
construct an effective scheme quotient or establish the full
[`PolarizedSmoothProperEtaleDescentStatement`](../../Langlands/AlgebraicGeometry/Picard/PolarizedSmoothProperDescentStatement.md).
That task still needs the global representer obtained from coherent
polarized descent.
