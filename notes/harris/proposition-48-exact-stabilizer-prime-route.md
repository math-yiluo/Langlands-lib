# Harris Proposition 4.8 under the exact-stabilizer condition — the prime orbit

The targets are `Langlands.Global.Harris.Proposition48ExactStabilizerPrimeBranchStatement`
and `Langlands.Global.Harris.Proposition48ExactStabilizerPrimeBranchTCStatement`
at independent universes `uF` for local fields and `uV` for carriers. Both
conclude `Q.HasParameterSolution` for the original inducing character `Q.ξ`.
The child hypotheses supply untwisted cuspidal solutions with their induced
complex-place parameters. In the totally complex (TC) route, `Q.E` is CM
and the actual intermediate fields extending it are totally complex by
`NumberField.isTotallyComplex_of_algebra`.
[Branch statements](../../Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerBranchStatement.md)

## From a child's weak induction to distinct local components

Write `E ⊆ D ⊆ L` with `D/E` prime cyclic and `L` the normal closure of
`E'/E`. The auxiliary place `v = Q.Ps.v` has a unique place above it in
`L`, and hence in `D` and throughout a tower from `D` to `L`. Write `w`
for the place of `D` and `u` for the place of `L`. For a representative
`a ∈ Gal(L/E)`, let `C_a = D · a(E')` and
`μ_a = a(ξ) ∘ N_{C_a/a(E')}`. A Mackey constituent over `D` is an actual
cuspidal class weakly inducing `μ_a`. The prime-orbit proof in Harris
uses `D = E_{t−1}` and the full orbit of such a constituent.

1. **Build the chain.** `UniquePlaceCyclicTower` obtains a prime cyclic
   tower from solvability, using the identification of the Galois group
   with the decomposition group at the unique place. For a unitary
   Mackey cusp over `D`, apply `CyclicPrimeIsobaricBaseChangeStatement`
   (or `CyclicPrimeIsobaricBaseChangeTCStatement`) at each step. This is
   the existence clause of Arthur–Clozel III.4.2(c). Each upper datum is
   a multiset of actual unitary cuspidal classes, with genuine attachments
   witnessing `IsobaricData.IsWeakBaseChangeOf`. The theorem
   `PrimeCyclicBaseChangeTower.exists_isobaricChain_of_step` assembles
   the successive lifts. Compactness of the adele quotients is supplied
   by `compactSpace_adeleQuotient`.
   [Tower construction](../../Langlands/Automorphic/Unramified/WeakInductionTowerChain.md)
2. **Identify the terminal Hecke family.** If `(ρ_i)` ranges over the
   right cosets of `Gal(L/C_a)` in `Gal(L/D)`, the terminal characters are
   `μ_a ∘ N_{L/C_a} ∘ ρ_i`. The rank of the weak induction gives the
   number of these cosets. The residue-degree power rule transports the
   attached spectra to `L`, where the weak induction Euler formula is a
   product of the factors of these characters. The result
   `PrimeCyclicBaseChangeTower.exists_isobaricChain_endsAtHeckeFamily`
   uses `cuspidalArithmeticSpectralTransport` for the endpoint equivalences
   and produces `EndsAtHeckeFamily`, the rank and cofinite Euler equality
   for the already constructed terminal datum. In the source argument
   the rank-one realizations of the characters form an actual isobaric
   sum, and Jacquet–Shalika constituent recovery identifies that sum with
   the terminal lift from the Euler equality. The Lean distinctness
   theorem passes the attached Euler endpoint directly to B6. Any
   identification with a prescribed actual sum uses recovery, while
   the existence of the intermediate classes uses III.4.2(c).
   [Hecke endpoint](../../Langlands/Automorphic/Unramified/HeckeFamilyEndpoint.md),
   [rank-one realizations](../../Langlands/Automorphic/RankOneHeckeRealization.md)
3. **Separate character multisets at `u`.** The global form of (4.12)
   is given by `exactWeilStabilizer_iff_global`. Let `Φ` be the component of
   `ξ ∘ N_{L/E'}` read on `Lˣ` at `u`. The component of the `i`-th terminal
   character on those units is `z ↦ Φ(a⁻¹ ρ_i z)`. If two families agreed
   up to a bijection of indices, matching one pair would give
   `Φ ∘ (a⁻¹ ρ_i (ρ'_j)⁻¹ a') = Φ`. By the exact stabilizer, the
   element in parentheses fixes `E'`. Thus `a` and `a'` would lie in the
   same double coset `Gal(L/D) a Gal(L/E')`. For different double cosets,
   `HeckeFamily.SameFiniteComponentsAt` therefore fails at `u`. This
   uses the local characters and retains multiplicities.
   [Distinctness calculation](../../Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessReduction.md)
4. **Pass the difference down by B6.** In the paper route, III.5.1 turns
   each adjacent weak lift into a strong lift at the unique place above
   `v`. I.6.2(a) gives uniqueness of local lifting in the tempered case,
   with the extension by Langlands classification after I.6.8. Isomorphic
   starting components would therefore give isomorphic terminal
   components. At the top these are unitary principal series induced
   from the specified local characters, with their inducing multisets
   determined by their supercuspidal support. The differing character
   multisets give the contradiction. `TowerBaseChangeHeckeComponentStatement`
   and its TC form express this inference for two supplied chains, including
   isobaric data of mixed constituent ranks. Its general compatibility
   input is `CyclicStrongBaseChangeSupportStatement`. The nonsplit clause
   transports an actual support witness using a σ-lift-certified map, so
   the map and the support comparison remain separate local inputs.
   [B6 statement](../../Langlands/Automorphic/Unramified/TowerBaseChangeHeckeComponentStatement.md),
   [strong compatibility](../../Langlands/Automorphic/Unramified/CyclicStrongBaseChangeSupportStatement.md)

`proposition48ExactStabilizerDistinctness` and
`proposition48ExactStabilizerDistinctnessTC` prove the two distinctness
implications. Their signatures retain rigidity and the full statement of
III.4.2(c). The implemented chain argument uses its existence clause and
B6 with the Euler endpoint. For matching ranks the conclusion compares
every pair of local presentations of unitary Mackey constituents
from different double cosets. The general and TC proofs take the matching
form of B6 and of the isobaric lift. The TC inputs apply to `D` and every
field above it because they extend the CM base.
[General distinctness](../../Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessProof.md),
[TC distinctness](../../Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessTCProof.md)

## From the prime orbit to the original character

Harris, p. 203, uses the transitive action of `Gal(D/E)` on the
`[D : E]` Mackey classes and identifies the upper datum with the full orbit
of one child. In the two Library branch reductions, the Mackey arguments
can start with the child at the identity and transport its class and
parameters. The following steps use the twelve interfaces.
[Branch reductions](../../Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerPrimeBranchReductionStatement.md)

| Step | Input and use |
| --- | --- |
| Identify the orbit | `Proposition48MackeyFibreStatement` identifies the double-coset fibres with restrictions to `D` and gives `D ⊆ E'` for the identity representative. `Proposition48MackeyChildTransportStatement` transports the child's original, untwisted class and its parameters to `D`. `Proposition48MackeyConstituentGaloisConjugateStatement` makes each global conjugate a Mackey constituent of the corresponding lifted automorphism of `L`. |
| Establish regularity for cyclic induction | A nonidentity element of `Gal(D/E)` lifts to a representative in a different double coset. If it fixed the chosen class, `HasDistinctMackeyComponents` would make the same local presentation differ from itself. `ConjugateSelfDualUnitaryCentralCharacterStatement` and `ArithmeticComapUnitaryCentralCharacterStatement` furnish its unitary central character. |
| Construct the parent cusp | B2, `CyclicRegularInductionStatement` or `CyclicRegularInductionTCStatement`, supplies an actual cuspidal weak induction of the regular orbit representative. `cyclicNormKernelCharacter` supplies the requisite character from the cyclic extension. Harris also applies Arthur–Clozel III.6.4, represented by B3 (`CyclicRegularOrbitLiftStatement` and its TC form), which characterizes the lower singleton by its weak base change to the full upper orbit and gives its norm self-twist. The twelve-interface route obtains the cusp using B2. |
| Check the weak induction of `Q.ξ` and self-duality | `Proposition48PrimeInductionStagesStatement` composes the attached Euler identities to get weak induction of the parent's original character. `WeakInductionConjugateInverseSelfDualStatement` or its TC form applies the corresponding rigidity to the resulting actual class and its conjugate dual. |
| Establish the auxiliary supercuspidal pair | `ArithmeticComapSupercuspidalComponentStatement` transports genuine supercuspidal witnesses for the child and each cyclic conjugate to the unique place over `v`. `HasDistinctMackeyComponents` supplies the inequalities required by B4, `CyclicWeakInductionSupercuspidalStatement` or its TC form, which gives supercuspidality of the parent at `v`. The local criterion is Henniart–Herb 5.5, with the comparison to the actual local component in B4. `ConjugateSelfDualSupercuspidalConjPlaceStatement` supplies the conjugate-place witnesses. Transport the child's conjugate-place witness to `D`, using compatibility of conjugation with restriction of places. Parent validity gives unique places of `L` above `v` and `conjPlace Q.E v` and hence uniqueness of the two transported places in `D`. `ConjugateSelfDualUnitaryCentralCharacterStatement` gives the parent's unitarity, and `SplitPlaceNeConjPlaceStatement` separates the pair using the split imaginary quadratic field. |
| Recover the parameters and regular algebraicity | With the two distinct auxiliary places and their unique places in `D`, apply clause (2) of `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7) to the two unitary cusps. It gives the sum of the transported child lists over all places of `D` above each complex place of `E`. `Proposition48PrimeInducedParameterStagesStatement` identifies this list, up to permutation, with the list induced from `Q.ξ`. `Proposition48InducedParameterRegularAlgebraicStatement` applies `CuspidalComplexParameterBridgeTCStatement` using algebraicity after the specified parity twist, relative regularity and the conjugate-inverse condition on `Q.ξ`. The bridge is proved by `cuspidalComplexParameterBridgeTC`. |

The branch reductions conclude `Q.HasParameterSolution` by combining that
parameter assertion with weak induction, regular algebraicity, conjugate
self-duality and supercuspidality at `v`. Their signatures keep the branch
premises. The identity-child route leaves Theorem 1.2, isobaric invariance
and B3 unused. The proof of isobaric invariance in the source instead uses
the invariant monomial restriction and rigidity. Theorem 1.2 belongs to
the comparison of cyclic descents in the singleton case.

## Transfer inputs and reductions

| Input | Declaration and route |
| --- | --- |
| III.4.2(c), both field scopes | Use the going-up clauses of `CyclicPrimeJointRankInductionStatement` with `IsobaricData.exists_unitary_weakBaseChange_of_singletons` and upper `CuspidalEulerConstituentRecoveryStatement`. In TC use `cyclicPrimeCuspidalBaseChangeExistenceTC_of_jointRankInduction` followed by `cyclicPrimeIsobaricBaseChangeTC_of_singletons`, with `CuspidalEulerConstituentRecoveryTCStatement` over the upper field. The two analytic rank steps are `CyclicPrimeJointRankStepStatement` and `CyclicPrimeJointRankStepTCStatement`. These express the actual occurrence and cuspidality inputs of III.4.2(a), (b), (d) and (e) at each rank for a prime-degree extension. In the TC step all infinite places of the base split, so the archimedean matching is split complex. The unrestricted step also includes nonsplit real matching. |
| B2, both field scopes | `CyclicRegularInductionReductionStatement` and `CyclicRegularInductionReductionTCStatement` use actual regular-induction existence, the exact local norm-character order and lower Euler constituent recovery. For `CyclicRegularInductionExistenceStatement` or its TC form, start from the going-down orbit case, III.4.2(e), in `CyclicPrimeRegularOrbitRealizationStatement` or its TC form. Use the norm-twist pair count, the reverse arithmetic orbit comparison, equivariance, recovery and induction by stages. The prime case supplies an actual orbit witness and the cofinite polynomial comparisons certify the successive weak inductions down a composite cyclic extension. |
| B3, both field scopes | `CyclicRegularOrbitLiftReductionStatement` and its TC form use the same actual regular-induction existence together with `WeakInductionOrbitBaseChangeStatement` and the corresponding `CyclicWeakBaseChangePairMultiplicityStatement` or TC form. Constituent-pair counts and positivity of the ranks yield uniqueness among unitary isobaric data with that orbit as weak base change. |
| Rigidity, isobaric invariance and A1 | `CuspidalSpectralRigidityStatement` and `CuspidalSpectralRigidityTCStatement` provide the Euler recovery used by the transfer reductions (Arthur–Clozel III.(2.4), citing Jacquet–Shalika). The distinctness theorems retain these premises, and the branch uses rigidity for the self-duality comparison. `proposition48IsobaricInvariance` and its TC form prove the invariance inputs suggested by Harris, p. 202. `Harris1998Theorem12CuspidalStatement` records the cuspidal form of Theorem 1.2, printed p. 185 (PDF p. 9), in the branch signature. [Theorem 1.2 statement](../../Langlands/Galois/Harris1998ExistenceStatement.md) |
| Local and complex-place inputs | B6 takes the strong local support comparison through the tower as above. B4 concerns the local component of the actual global weak induction at the unique-place step. Restricted B7 uses strong lifting at split complex places (III.5.1), with the orbit comparison for weak induction and the passage from aggregate data to literal parameters. Restricted B7 concerns the cusps with the auxiliary pair supplied by the branch argument. |

`Proposition48ExactStabilizerPrimeBranchReductionStatement` and
`Proposition48ExactStabilizerPrimeBranchReductionTCStatement` state the
two implications from the twelve interfaces. Applying proofs of these
implications to proofs of their interfaces gives the exact branch targets.
The B6 distinctness implications provide `HasDistinctMackeyComponents`
for the input to that branch in the full induction.

## Sources

- Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p*, `harris-1998-local-langlands`, printed pp. 202–203
  (PDF pp. 26–27), Proposition 4.8 induction, invariance and prime orbit,
  and p. 204, condition (4.12). Theorem 1.2 is in §1, printed p. 185
  (PDF p. 9). The retained PDF SHA-256 is
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
  In `math_9611226v1.tex`, SHA-256
  `984b1397ac75baee5d261becad137a9ae91e1593f3da0d166df5136fb52e4af7`,
  see lines 523–537, 1574–1614, 1630–1664 and 1744–1766.
- Arthur and Clozel (1989), *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
  Printed locators are III.(1.1)–(1.2) and (2.4), pp. 199–200,
  III.4.2(a)–(c) and (e), pp. 202–210, III.5.1, pp. 212–213, and
  III.6.1, III.6.2 and III.6.4, pp. 214–218. Local lifting is I.6.2 and
  the extension after I.6.8, pp. 51–53 and 59–60. PDF page numbers
  are fourteen greater than printed pages.
- Henniart and Herb (1995), *Automorphic induction for GL(n) (over local
  non-archimedean fields)*, `henniart-herb-1995-induction`, SHA-256
  `5e753525048b08007d9605baa9019c8e792512887305ec2e39ae9c3bee6a963e`,
  Proposition 5.5, printed pp. 152–153 (PDF pp. 22–23).
- *Formalizing the large external inputs of the local Langlands
  correspondence for GL_n*, `operator-external-inputs-plan-2026-11-16`,
  `external-inputs-plan.tex`, SHA-256
  `816bb31b7194dea7eb38a661bf53ae670c17a2ec0bd7d1e7e4bcfa2c94aad03a`,
  Section 2.2, lines 197–199, and Section 4.8, Remark 4.2, lines
  859–894 and 908–911. The remark gives the derived exact-stabilizer
  tower argument and the complex-place obligation.
