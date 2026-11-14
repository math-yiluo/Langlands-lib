# Diagonalizable groups and finite-Galois modules: family 2 coverage update

Worker 3483, 14 November 2026.

This updates rows D4, D5 and F8 of the historical
[family 2 ledger](ledger-family-2-tori.md), against Library commit
`24789a71aba4e7d9d5c1f25c6b52d06acda8d600`. The four proof pairs below are
present in that immutable Library and byte-match the checked workspace files.
The diagonalizable smoothness and connectedness criteria in D5 and the exact
finite-homomorphism reflection theorem in F8 now have published proofs. D4 has
published split full faithfulness and finite-Galois module realization, with
the broader categorical comparison still requiring separate work.

## Exact proof endpoints

All declaration names in this table have prefix `Langlands.GroupScheme.`.
Each theorem has exactly its listed universe-polymorphic proposition as its
type, with no additional hypotheses.

| Theorem | Proposition and proof module |
| --- | --- |
| `diagonalizableCharacter` | `DiagonalizableCharacterStatement`; [DiagonalizableCharacterProof](../../Langlands/GroupScheme/Torus/DiagonalizableCharacterProof.lean), [proof explanation](../../Langlands/GroupScheme/Torus/DiagonalizableCharacterProof.md) |
| `multiplicativeTypeGaloisModuleRealization` | `MultiplicativeTypeGaloisModuleRealizationStatement`; [GaloisModuleRealizationProof](../../Langlands/GroupScheme/Torus/GaloisModuleRealizationProof.lean), [proof explanation](../../Langlands/GroupScheme/Torus/GaloisModuleRealizationProof.md) |
| `Diagonalizable.diagonalizableSmoothConnectedCriteria` | `DiagonalizableSmoothConnectedCriteriaStatement`; [DiagonalizableSmoothConnectedCriteriaProof](../../Langlands/GroupScheme/Torus/DiagonalizableSmoothConnectedCriteriaProof.lean), [proof explanation](../../Langlands/GroupScheme/Torus/DiagonalizableSmoothConnectedCriteriaProof.md) |
| `finiteHomMaximalTorusReflection` | `FiniteHomMaximalTorusReflectionStatement`; [FiniteHomMaximalTorusReflectionProof](../../Langlands/GroupScheme/Torus/FiniteHomMaximalTorusReflectionProof.lean), [proof explanation](../../Langlands/GroupScheme/Torus/FiniteHomMaximalTorusReflectionProof.md) |

### Split characters and homomorphisms

For a field `k` and a finitely generated abelian group `M`,
[DiagonalizableCharacterStatement](../../Langlands/GroupScheme/Torus/DiagonalizableCharacterStatement.lean)
identifies every actual character of `D_k(M)` with evaluation at exactly one
`m ∈ M`. The evaluation identity holds on every test scheme over `Spec k`.
For finitely generated abelian `M, M′`, the map
`Diagonalizable.restrictMap` from additive maps `M′ →+ M` to actual
homomorphisms `D_k(M) → D_k(M′)` is bijective. Torsion is allowed.

The proof constructs evaluation characters from natural families of points.
It identifies the universal value of any such multiplicative family with a
group-like element of `k[M]`, proves that this is a unique monomial, and applies
that result coordinatewise to homomorphisms. Its auxiliary character and Hom
arguments work without finite generation; the exported proposition retains
the finite generation hypotheses of its published statement.

### Finite-Galois essential surjectivity

For a finite Galois extension `L/k`, a finitely generated abelian group `M`
and a representation `ρ : Representation ℤ (L ≃ₐ[k] L) M`,
[MultiplicativeTypeGaloisModuleRealizationStatement](../../Langlands/GroupScheme/Torus/GaloisModuleRealizationStatement.lean)
produces an actual commutative `k`-group scheme `T`, an isomorphism
`i : T_L ≅ D_L(M)`, and an additive equivalence
`e : M ≃+ characterLattice T_L`. Evaluation through `i` gives `e(m)` on all
test schemes. Moreover, `e` intertwines `ρ` with
`characterLattice.galoisRepresentation k L T`, the canonical action on the
characters of the actual base-changed group.

The construction presents `M` by equivariant permutation lattices, realizes
the presentation by a homomorphism of induced tori, and takes its full
scheme-theoretic kernel. Kernel base change and the diagonalizable-kernel
comparison identify its `L`-base change with `D_L(M)`. Unique evaluation
characters prove that the resulting character map is bijective; naturality
of restriction proves equivariance. The quotient module can have torsion,
including characteristic torsion. The conclusion therefore includes groups
of multiplicative type that need not be smooth or connected.

This proves essential surjectivity at a specified finite Galois extension.
It supplies neither an assembled absolute-Galois categorical anti-equivalence
nor its compatibility with short exact sequences.

### Smoothness and connectedness

Let `k` have characteristic exponent `p`, and let `M` be finitely generated.
[DiagonalizableSmoothConnectedCriteriaStatement](../../Langlands/GroupScheme/Torus/DiagonalizableSmoothConnectedCriteriaStatement.lean)
is the conjunction of these three equivalences:

- `D_k(M)` is connected if and only if every finite-order element of `M` is
  killed by some power of `p`.
- `D_k(M)` is smooth over `k` if and only if `p • m = 0` implies `m = 0`.
- `D_k(M)` is smooth and connected if and only if `Module.Free ℤ M`.

Here `p = 1` in characteristic zero. Finite generation is an actual hypothesis;
these are not unrestricted smoothness claims for arbitrary abelian groups.
The implemented proof relates connectedness to idempotents of the group
algebra and uses finite abelian-group decomposition and Frobenius. Smoothness
implies the torsion condition by reducedness; the converse uses lifts of units
and torsion units through square-zero quotients, together with finite
presentation. The final equivalence also uses the published free-character
criterion and the smoothness and connectedness of split tori.

### Reflection of maximal tori

[FiniteHomMaximalTorusReflectionStatement](../../Langlands/GroupScheme/Torus/FiniteHomMaximalityStatement.lean)
concerns connected reductive groups `G, H` over any field, a homomorphism
`π : G → H` whose underlying scheme morphism is finite, a closed torus
`j : T → G`, a maximal torus `i : S → H`, and a homomorphism `f : T → S`.
If `f` is surjective as a scheme morphism and `j ≫ π = groupHom f ≫ i`,
then `j` is maximal among all closed tori. The tori may be nonsplit.
Neither smoothness of `π` nor surjectivity of `π` is assumed, and the
surjectivity hypothesis on `f` is not a condition just on rational points.

The exact proof is the published composite
`finiteHomMaximalTorusReflection_of_torusImage torusImageClosedTorusStatement`.
The reduction factors the image of a larger torus through a closed torus in
`H`, uses maximality of `S`, and applies finite-map rigidity via integral
incomparability. Thus F8's historical missing wrapper is now present.

## Sources and verification

The registered original source is `milne-2017-algebraic-groups`,
J. S. Milne, *Algebraic Groups* (2017), SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Lemma 12.4 and its following evaluation formula, printed p.232 (PDF p.248),
and Theorem 12.9(a), printed pp.233–234 (PDF pp.249–250), support the split
character comparison. Remark 12.5, printed p.232, gives the three criteria.
The finite-Galois realization is the essential-surjectivity part of
Theorem 12.23, printed p.240 (PDF p.256); the implementation uses the kernel
construction above rather than the book's invariant coordinate ring.
Proposition 17.20, printed pp.357–358 (PDF pp.373–374), concerns images and
lifting of maximal tori under quotient maps of connected group varieties;
the F8 reflection formulation is a derived result with the explicit Lean
hypotheses above. The complete retained
[official errata](https://www.jmilne.org/math/Books/iag2errata.html)
snapshot of 2 November 2026 was read; it does not correct these passages.

The character proof's receipt `e60c47d2-4a71-4ef3-9fd4-20fda725fc4c`
is accepted and public, with independent approval and publication at
`cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`. The realization proof's receipt
`04f517b1-4819-4f9f-b3ea-c0d23197761d` is accepted and public, with
independent approval and publication at
`51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`. Both independent and integration
reports were read. For the smoothness and reflection proofs, the evidence
used here is the exact theorem and paired Markdown in the current immutable
Library; no restored historical receipt ID is asserted.

All four modules compiled together with zero errors or warnings on
14 November 2026. The inspected smoothness theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. These development checks supplement the
Library evidence; this coverage note publishes no mathematical proof itself.

## Remaining comparison

The finite-level full-faithfulness statement for given groups that become
arbitrary finitely generated diagonalizable groups over a common `L/k`
is candidate `c9448fc7-8310-47be-8641-c89294a4a656` of Task 3483. At this
check it has independent approval but is staged and not public, with
publication deferred for the reported full-tree Lean service argument-size
failure. It has no proof from this candidate. Its separate proof successor
remains private until statement publication is verified.

The published
`IsSplitTorus.existsUnique_hom_of_equivariant_characterMap` in
[FiniteGaloisCharacterDescent](../../Langlands/GroupScheme/Torus/FiniteGaloisCharacterDescent.lean)
already descends equivariant character maps when the target becomes a split
torus over `L`; the source can be any commutative group scheme. This does not
cover targets with torsion character groups. Together with the finite-level
realization above, it records substantial D4 coverage while leaving the full
categorical and exact-sequence comparison as a broader obligation.
