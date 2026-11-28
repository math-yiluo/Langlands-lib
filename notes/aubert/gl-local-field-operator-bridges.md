# Aubert operator bridges over nonarchimedean local fields

The proofs in the table below have the indicated exact proposition types
in Library commit `19fb2c25ab3dc0b2e83bebdca35724e7a62d864a`. The two
operator comparisons concern the **unadjusted** operator on exact
Grothendieck groups of smooth finite-length complex representations, not
just the classes of split sequences. The local-field datum permits both
characteristics. The bridge to the earlier matrix operator has p-adic scope.

In the table, `GL` abbreviates
`Langlands.Aubert.General.RationalPointFamily.GL`, and `P` abbreviates
`Langlands.Parabolic`.

| Exact proposition and proof | Scope, inputs and construction |
| --- | --- |
| `P.LocalFieldGeneralLinearModulusCompatibilityStatement`, [`P.localFieldGeneralLinearModulusCompatibility`](../../Langlands/Representation/Aubert/GeneralLinearLocalFieldModulusProof.lean) | For every element of the upper-block parabolic, the Haar module of conjugation on the unipotent radical is the determinant-ratio character composed with Levi projection. Compact subgroups containing radical elements give triviality on the radical. This is the upper-matrix realization of Bernstein–Zelevinsky (1977), §§1.7–1.9 and 2.1–2.3, printed pp. 444–446. |
| `GL.LocalFieldGLRationalFunctorsStatement`, [`GL.localFieldGLRationalFunctors`](../../Langlands/Representation/Aubert/General/LocalFieldGLRationalFunctorsProof.lean) | For every rank and strictly decreasing diagonal cocharacter, compares both normalized functors by natural isomorphisms in the pullback squares. Induction uses precomposition on functions with right translation and the positive half-modulus. Jacquet restriction takes the same vector on unipotent coinvariant classes and uses the inverse half-modulus. Neither finite-length premise is needed for these natural isomorphisms. |
| `GL.LocalFieldMatrixParabolicPreservationStatement`, [`GL.localFieldMatrixParabolicPreservation`](../../Langlands/Representation/Aubert/General/LocalFieldMatrixParabolicPreservationProof.lean) | For every matrix block shape and rank, both normalized functors preserve finite length and actual short exact sequences of finite-length objects. The proof uses product-Levi admissibility from refined Jacquet descent, exactness, and the all-field matrix induction and Jacquet finite-length results. This is the matrix-model input to the exact class operations; compare Zelevinsky (1980), Proposition 1.4, printed p. 171. |
| `GL.LocalFieldGLRationalOperatorComparisonStatement`, [`GL.localFieldGLRationalOperatorComparison`](../../Langlands/Representation/Aubert/General/LocalFieldGLRationalOperatorProof.lean) | For every rank and strictly decreasing diagonal cocharacter, takes `DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement` at carrier universe `max (u + 1) v`. Finite length and exactness transport from the standard rational-point functors to the matrix functors. The natural isomorphisms give the two exact class-map squares, and their composites are summed using the block-to-root-subset bijection. |
| `GL.PadicMatrixAlternatingOperatorSpecializationStatement`, [`GL.padicMatrixAlternatingOperatorSpecialization`](../../Langlands/Representation/Aubert/General/PadicMatrixOperatorSpecialization.lean) | For every `PadicField`, compatible topological datum and rank, the all-field and earlier p-adic matrix operators are equal. Finite-length and short-exact-sequence witnesses are conclusions from `padicMatrixFunctorSpecialization`. Both signed sums use the same block shapes. |

## Sign and scope

Aubert's Definition 1.5, printed p. 2181, uses induction after
Jacquet restriction with sign \((-1)^{|J|}\). For a block shape
\(B\) of rank \(n\), `blockRootSubsetEquiv` indexes the corresponding
simple roots inside the blocks. Their number is \(n-B.\mathrm{length}\).
The sign comparison also covers \(n=0\), with one empty shape and a
single positive term. The upper triangular convention and the trivial
rank-zero group are those of Aubert's §2, printed pp. 2183–2184.

Given the two dynamic finite-length propositions, the rational-point
comparison and the p-adic specialization identify the canonical
rational-point operator with the earlier p-adic matrix operator after
exact Grothendieck pullback. Matrix preservation alone does not discharge
these two general propositions. Neither comparison identifies an
adjusted involution: the support sign of Definition 2.1 and the product
and segment-monomial arguments of Theorem 2.3 concern the whole graded
group and are distinct from the rankwise unadjusted comparison. See
[the graded source map](gl-specialization-source-map.md) for the
product-Levi correction and the role of monomial spanning.

## Classification dependencies

Here a classification-module count means constants whose defining module
has a `Classification` component. It does not mean that their statements
are classification results. The proof companions give inventories from
recursive traversals of declaration types and values, distinct from
import closures.

- The full-parabolic modulus proof and the natural functor comparison
  reach no classification-module constants in their recorded inventories.
- The conditional rational-point operator proof reaches
  `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` and
  `Langlands.FiniteLengthAssembly.length_comp_surjective` in such modules.
  Both are transport of length under a surjective group map. This does
  not audit proofs supplied later for the two dynamic premises.
- The all-field matrix preservation proof reaches 67 such constants in
  13 modules. Its companion lists them: the main representation inputs
  are actual finite length, supercuspidal embedding and the product-Levi
  admissibility argument, not a Langlands-quotient theorem.
- Starting at `GL.padicMatrixAlternatingOperatorSpecialization` at the
  pin above, recursively following constants in declaration types and
  values within `Langlands` reaches 67 such constants in 10 modules.
  In particular it reaches `Langlands.Classification.normalizedInductionFiniteLength`,
  `Langlands.Parabolic.normalizedJacquetFiniteLength`, and
  `Langlands.Classification.irreducibleProductFiniteLength`, with the
  supercuspidal-embedding, tensor, transport and subquotient helpers in
  their proofs. No Langlands-classification or multisegment-classification
  theorem occurs in the reached constants from these modules.

## Distinct general input

[`Langlands.Aubert.General.RationalPointFamily.rationalSupercuspidalInductionFiniteLength`](../../Langlands/Representation/Aubert/General/RationalSupercuspidalInductionFiniteLengthProof.lean)
proves `RationalSupercuspidalInductionFiniteLengthStatement` (Renard
2026, VI.5.4, printed pp. 173–174). It is not restricted to matrix
groups. On the actual standard rational-point families, it gives finite
length of full-parabolic Haar-normalized induction of an irreducible
inside-Levi cuspidal representation. Its stated hypotheses specify the
ambient point topology, standard cocharacter and Levi intersections,
relative roots and closed radicals and Levis.
`exists_pointInducedJacquetGeometricFiltration` obtains the actual
geometric filtration from these rational-point data and the Weyl
comparisons. Separately, the joint special-compact basis supplies the
special-vertex input to proper-standard induction exclusion inside each
Levi. Together these inputs give cuspidal extraction and finite length.
This result concerns supercuspidal input; it is not the arbitrary
finite-length dynamic induction proposition.

## Sources

| Retained literature ID | SHA-256 | Locator |
| --- | --- | --- |
| `bernstein-zelevinsky-1977-induced-i` | `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` | §§1.7–1.9 and 2.1–2.3, printed pp. 444–446. |
| `zelevinsky-1980-induced-ii` | `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | Proposition 1.4, printed p. 171. |
| `aubert-1995-duality` | `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Definition 1.5, printed p. 2181, and §2 through Theorem 2.3, printed pp. 2183–2185. |
| `renard-2026-representations-groupes-reductifs-padiques` | `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` | French edition of 9 July 2026, Théorème VI.5.4, printed pp. 173–174 (PDF pp. 179–180). |
