# Dependencies of the Harris–Berkovich cohomological statements

The paths and declarations below are pinned to Library commit
`2cda61adeed2b8811c903c00be6b0a4097683eb8`, with Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. A declaration named `Statement` in
these tables is a proposition definition. For the larger inventories and
their earlier pins, see the [analytic cohomology map](harris-cohomology-coverage.md)
and the [compatible-family map](galois-family-coverage.md).

## Analytic sheaves and cohomology

| Source | Pinned declaration and its hypotheses |
| --- | --- |
| Berkovich, *Equish*, Theorem 1.4.2, pp. 8–10 | `EtaleGSheafToposComparisonStatement` uses the inverse-image and invariant-sheaf adjunction for module sheaves. It assumes image pullbacks for the forgetful étale site functor and small quotients by open subgroups. Smoothness of the inverse image and invertibility of the restricted unit and counit are conclusions. [Étale topos comparison](../../Langlands/Sheaf/Equivariant/AnalyticEtaleToposComparison/Statement.md) |
| *Equish*, §1.5 and Proposition 1.5.1, pp. 10–11, and Harris 1999, §2, p. 304 | `etaleGodementZeroFunctor` is built from the actual point fibres, right adjoints and local discrete part. `AnalyticEtaleGodementCompactAcyclicStatement` concerns positive-degree compact-support acyclicity of the image of its zero term under restriction. `analyticEtaleRestrictedInjectiveAcyclic_of_godement` derives the two restricted-injective acyclicity assertions from this vanishing and joint faithfulness of the fibres. [Godement construction](../../Langlands/Sheaf/Equivariant/AnalyticEtaleGodement.md), [acyclicity reduction](../../Langlands/Cohomology/AnalyticEtaleRestrictedInjectiveAcyclic/GodementReduction.md) |
| *Equish*, Corollary 1.5.2(i), pp. 11–12 | `AnalyticEtaleCompactComparisonStatement` compares the actual right-derived compact sections before and after forgetting the action, on Hausdorff \(X\) with a continuous action and surjective projection from the chosen field-valued points. `compactComparison_of_openDomains_of_openMap_of_compactAcyclic` proves the comparison under the additional geometric and acyclicity hypotheses in its type. [Compact-support comparison](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/Statement.md), [conditional proof](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/Reduction.md) |
| *Equish*, §1.2, pp. 4–5, and Theorem 1.6.1, pp. 13–14 | `AnalyticEtaleGlobalSpectralSequenceStatement` uses the actual smooth equivariant sections complex. `AnalyticEtaleCompactBaseSpectralSequenceStatement` specializes to a compact Hausdorff base and uses the actual restriction action on ordinary cohomology for its second page. In the compact-support setting of Corollary 1.5.2(i), `AnalyticEtaleCompactSupportSpectralSequenceOnCompactBaseStatement` uses the compact sections complex and the action on compactly supported cohomology, with surjective field-valued point projection. The second pages use derived smooth invariants and the abutments have finite filtrations in each total degree. [Global](../../Langlands/Cohomology/AnalyticGlobalSpectralSequence/Statement.md), [ordinary compact base](../../Langlands/Cohomology/AnalyticGlobalSpectralSequence/CompactBaseStatement.md), [compact supports](../../Langlands/Cohomology/AnalyticGlobalSpectralSequence/CompactSupportStatement.md) |
| *Equish*, Theorem 1.6.1(i), p. 13 | `AnalyticEtaleParacompactComparisonStatement` concerns \(R^q(\Gamma(X,-)\circ b^*)\) and \(H^q(X,-)\circ b^*\) for paracompact Hausdorff \(X\). It uses ordinary global sections of the restriction. [Paracompact comparison](../../Langlands/Cohomology/AnalyticParacompactComparison/Statement.md) |
| Harris 1999, Lemma 2.2 and Lemma 2.2 bis, pp. 304–305 | `etaleFamilyGodementResolutionSystem` and `etaleFamilyGodementTruncatedResolutionSystem` act on an actual `EtaleDivisibleSystem`. Exactness of the zero-term functor and joint faithfulness of the point fibres give a quasi-isomorphism from the original sheaf to the truncated resolution at each coefficient level. Computing the finite-stage groups from the truncated complex uses zero-term acyclicity and a uniform upper bound on the input levels, both for the derived smooth compact cohomology \(H_c^q(X\{G\},-)\). The constant-system case retains the scalar-reduction transitions. [Analytic divisible systems](../../Langlands/Cohomology/DivisibleSystem/AnalyticEtale.md), [constant coefficients](../../Langlands/Cohomology/DivisibleSystem/AnalyticEtaleConstant.md) |

These analytic statements use actions over a fixed field \(K\).
*Equish* §1.1, pp. 1–2, also considers actions on the ground field.
The étale compact support functor uses supports in the chosen
field-valued points with topology induced from the underlying space.
Surjectivity of their projection matters for comparison with supports
in the underlying space. The compact Hausdorff base in the compact-support
spectral sequence is a specialization of Corollary 1.5.2(i).
The second page uses the action on the restriction's cohomology,
with smoothness as an assertion. The sequence in §1.2 starts with
cohomology already taken in the smooth equivariant category.
To use an ordinary compact cohomology bound in the divisible-system
computation, `AnalyticEtaleCompactComparisonStatement` transports the
bound after forgetting the action. The forgetful functor detects the
zero smooth representation. [Compact comparison](../../Langlands/Cohomology/AnalyticEtaleCompactComparison/Statement.md)

For schemes, Milne, *Étale Cohomology*, V.1, p. 164, defines adic
cohomology as the inverse limit of finite-stage cohomology groups.
`adicCohomology` implements this limit. `limitComparison` maps
cohomology of the limit sheaf to this limit. Its degree-zero
isomorphism follows from the right adjoint for sections. [Scheme
adic groups](../../Langlands/Cohomology/DivisibleSystem/EtaleAdicCohomology.md)

*Equish* 1.1.1(i), p. 2, gives the continuous action of
\(\operatorname{Gal}(k^{\mathrm{sep}}/k)\) on the base change of \(X\)
to the completion of the algebraic closure of \(k\). In the
proof of Proposition 1.5.1, step (1′) uses coinduced modules for deck
actions on finite Galois coverings.
`hasCoinducedGaloisFixedSections_smoothPointProduct` proves the
coinduced-coordinate assertion for the actual smooth point product.
The reduction to compact-support vanishing uses
`AnalyticEtaleGaloisCoinducedLocalAcyclicStatement`.
Corollary 1.5.2(ii) concerns a sheaf of coefficient rings on \(X(G)\)
and the comparison with cohomology of the underlying abelian sheaf.
[Coinduced coordinates](../../Langlands/Cohomology/AnalyticEtaleSmoothPointProductGaloisReduction.md),
[acyclicity input](../../Langlands/Cohomology/AnalyticEtaleGaloisCoinducedLocalAcyclic.md)

For the quasi-étale site, the published comparisons on
`twistedQuasiEtaleTopology` concern the generated site. The
counterexample in the ordinary generated site exhibits failure of
finite compact refinements for a compact probe. The separate
`CompactProbeQuasiEtaleHausdorffComparisonStatement` compares
`compactProbeQuasiEtaleTopology` with the finite chart-neighbourhood
covering criterion on Hausdorff objects. The manuscript comparison
needs the smooth equivariant site and its restriction, with the
comparison of covering rules on the relevant objects. [Generated
site](../../Langlands/Geometry/Analytic/QuasiEtaleSite.md), [compact-probe
comparison](../../Langlands/Geometry/Analytic/CompactProbeQuasiEtaleHausdorffComparisonStatement.md)

In Harris's §2 the dimension bound comes from Berkovich 1993,
Corollary 5.3.8, pp. 104–105. For a Hausdorff space over an algebraically
closed ground field, absolute compactly supported cohomology with
abelian torsion coefficients vanishes in degrees above twice the
analytic dimension. Berkovich 1994, Corollary 5.6, p. 556, assumes an
algebraically closed ground field and a compact space. Each point has
a neighbourhood that is a finite union of closed analytic domains
admitting quasi-étale maps to analytifications of finite-type
\(k\)-schemes. The coefficients are finite locally constant sheaves of
order prime to the residue characteristic. Harris 1999, Facts 1 and
1 bis, p. 303, applies finiteness on the compact pieces over the
geometric base, then uses localization for the noncompact test domain.
His divisible-system axiom on p. 304 has a misprint,
\(p^{m'}\)-torsion. Multiplication by \(p^{m'}\) is invertible on
the \(\ell\)-power torsion modules because \(p\ne\ell\). Equation
(2.1) gives the intended \(\ell^{m'}\)-torsion. [Analytic cohomology
source details](harris-cohomology-coverage.md#source-items-and-their-declarations)

## Unitary Shimura cohomology and its labels

| Source | Pinned declaration and its hypotheses |
| --- | --- |
| Harris–Taylor 2001, III.1–2, pp. 94–98 | `cmHarrisLambdaTowerCohomology` uses actual scheme levels, level pullbacks and the coefficient tower from an algebraic representation \(W\). `CMHarrisLambdaTowerFixedVectorComparison` asserts that the actual level maps are isomorphisms onto the tower's fixed vectors. Finiteness and continuity of the Galois action are hypotheses of subsequent propositions at this pin. [Lambda-adic tower](../../Langlands/Shimura/PEL/HarrisTaylorCMLambdaTower.md) |
| Harris 1997, Lemma 4, pp. 82–83, and Harris 1999, (5.1), p. 312 | `CMHarrisVanishingStatement` uses condition (R), the specified Jacquet–Langlands transfer and supercuspidality at the split local factor to state middle-degree concentration of the isotypic part with algebraic \(W\). [Vanishing](../../Langlands/Shimura/PEL/HarrisTaylorCMHarrisVanishingStatement.md) |
| Kottwitz 1992, Theorem 1, p. 657, and §5, p. 661 | `CMHarrisKottwitzLambdaAdicStatement` gives the cohomological power identity at good primes with the fixed-vector, continuity, finiteness and good-level hypotheses in its type. `HarrisKottwitzMiddleDegreeStatement` uses concentration, occurrence at one coefficient place and good-prime charts to extract a uniform nonzero integer exponent and polynomials of weight \(n-1+w\). The bridge retains the same Hecke multiplicity objects. [Kottwitz comparison](../../Langlands/Shimura/PEL/HarrisTaylorCMKottwitzStatement.md), [middle degree](../../Langlands/Shimura/PEL/HarrisKottwitzMiddleDegreeStatement.md) |
| Harris 1999, proof of 5.7(i), pp. 313–314 | `CMHarrisLambdaCohomologyHodgeTateStatement` asserts an underlying decomposition of the level cohomology. `HarrisCMLabelledMultiplicityStatement` also assumes concentration, the fixed-vector comparisons, continuity and finiteness. For each label \(F\to K\to K_\lambda\) it gives \(n\) distinct integers, each repeated \(m\) times in the decomposition on the actual middle-degree Hecke multiplicity representation over \(K_\lambda\). The integer \(m\) is positive when that space is nonzero. [Underlying decomposition](../../Langlands/Shimura/PEL/HarrisTaylorCMLambdaHodgeTateStatement.md), [labelled multiplicity](../../Langlands/Shimura/PEL/HarrisCMLabelledMultiplicityStatement.md) |
| Harris 1999, (4.2), p. 309, (5.6) and Theorem 5.7(i)–(ii), pp. 313–314, and Harris 1998, Erratum (E.1)–(E.2) | `CMHarrisTheorem57Statement` uses the division algebras, condition (R) and the specified transfer. The rational prime \(p\) splits in the imaginary quadratic subfield. The local component on \(\mathrm{GL}_n(F_{w_0})\) is supercuspidal and the separate \(\mathbb Q_p^\times\) factor acts trivially. The transferred class occurs at the small level \(U\), with the fixed-vector, finiteness and continuity premises in the statement. The central character is restricted to the ideles of the imaginary quadratic subfield for the twist. The cohomology and \(\bar\nu(\pi)\) coefficient places lie over the same rational \(\ell\), with continuous coefficient maps compatible with the given complex realizations. For the actual realization \(\psi\) of \(\bar\nu(\pi)\) the formula uses the characteristic polynomial of \(g\mapsto\psi(g^{-1})H_\pi(g^{-1})\). The normalized Euler polynomial comparison uses good unramified charts outside a finite set of rational primes that may include \(\ell\). [Theorem 5.7(i)–(ii)](../../Langlands/Shimura/PEL/HarrisTaylorCMHarrisTheorem57Statement.md), [twisting character](../../Langlands/Galois/HarrisTwistingCharacter.md) |

The Kottwitz statement, the middle-degree bridge and the labelled
multiplicity statement assume a division algebra \(A\) and the Harris
signature with \(n\ge 3\) or a real place besides the distinguished one.
The coefficient representation is irreducible over \(\overline K\) and
the central scalars \(t\) act by \(t^{-w}\).
The finite-adelic representation \(\pi_f\) is admissible and absolutely
irreducible over \(K\). [Kottwitz hypotheses](../../Langlands/Shimura/PEL/HarrisTaylorCMKottwitzStatement.md),
[labelled hypotheses](../../Langlands/Shimura/PEL/HarrisCMLabelledMultiplicityStatement.md)

For the geometric input to labelled multiplicity, Harris–Taylor III.2,
p. 98, writes an irreducible algebraic representation \(\xi\) over the
algebraic coefficient field as a summand of
\(\nu^{t_\xi}\otimes(V^\vee)^{\otimes m_\xi}\) with
\(2t_\xi-m_\xi=-w(\xi)\). The geometric realization uses the relative
first cohomology of the tautological abelian family, its powers,
multiplication by two in each factor and the representation-theoretic
idempotent. The resulting summand lies in
\(H^{i+m_\xi}(\mathcal A^{m_\xi}_{\bar F},\overline{\mathbb Q}_\ell(t_\xi))\).
For a sum of irreducibles the construction uses the tensor degree
and twist of each summand.
The proof of the labelled statement needs this realization for the
coefficient system on the same tower, Faltings's comparison compatible
with the projector and the Hecke operators, and the Hodge types of the
cohomological discrete series at each label. Faltings 1988,
Introduction §1(b)–(c), pp. 255–256, pairs \(H^a(\Omega^b)\) with
the twist \(-b\). The formula on p. 298 prints \(-a\). [Labelled
comparison and sources](../../Langlands/Shimura/PEL/HarrisCMLabelledMultiplicityStatement.md)

## Compatible families and normalization

| Source | Pinned declaration and its hypotheses |
| --- | --- |
| Clozel 1991, Theorem 5.7, p. 142, and Clozel 1993, Theorem 2.6, p. 772 | `Clozel1991Theorem57Statement` gives the compatible family with multiplicity on its reflex field and keeps the additional square-integrable place in the bad-parity case. `Clozel1993Theorem26Statement` uses the split supercuspidal hypothesis. [Clozel statements](../../Langlands/Galois/ClozelSelfDualStatements.md) |
| Clozel 1991, §5.2–3, and Kottwitz 1992, Theorem 1 | `HarrisKottwitzPowerNormalizationStatement` removes the scalar twist by tensoring with the inverse of the actual continuous avatar, taking weight \(n-1+w\) to \(n-1\). The Euler polynomials use geometric Frobenius and a positive power \(\lvert a\rvert\). [Power normalization](../../Langlands/Galois/HarrisKottwitzPowerNormalizationStatement.md) |
| Serre, *Abelian l-Adic Representations and Elliptic Curves*, II §§2.3–2.7, and Harris 1998, Lemma 1.6, p. 188 | `AlgebraicHeckeLambdaAdicRealizationStatement` concerns a totally complex number field and an algebraic Hecke character. It asserts existence of actual continuous avatars over all finite completions of one coefficient field. [Avatars](../../Langlands/Galois/AlgebraicHeckeLambdaAdicRealizationStatement.md) |
| Harris 1997, Theorem 2, p. 100, with the Taylor proof sketch on pp. 102–103 | `TaylorMultiplicityRemovalStatement` and `TaylorLabelledMultiplicityRemovalStatement` extract the rank-\(n\) representation with the given Euler roots and Hodge–Tate input. `RegularHodgeTateCoefficientDescentStatement` is the separate descent to the coefficient completion. [Taylor statement](../../Langlands/Galois/TaylorMultiplicityRemovalStatement.md), [labelled extraction and descent](../../Langlands/Galois/HarrisLabelledMultiplicityStatement.md) |
| Harris 1998, Theorem 1.2, p. 185 | `Harris1998Theorem12Statement` takes an isobaric spectrum all of whose cuspidal constituents are regular algebraic and conjugate self-dual. Each has a square-integrable component at some finite place whose rational residue prime splits in the specified imaginary quadratic subfield. `Harris1998Theorem12CuspidalStatement` retains these conditions on a single constituent. Both assert a sum of pure compatible families with almost-everywhere weak association. `HarrisEvenGeometricPowerStatement`, `HarrisEvenNormalizedExistenceStatement` and `HarrisOddNormalizedExistenceStatement` retain the square-integrable and splitting hypotheses on the cuspidal input. [Theorem 1.2](../../Langlands/Galois/Harris1998ExistenceStatement.md), [even-degree route](../../Langlands/Galois/HarrisEvenGeometricStatement.md), [odd-degree route](../../Langlands/Galois/HarrisOddNormalizedExistenceStatement.md) |
| Harris 1999, Theorem 5.9(i), pp. 314–315 | `Harris1999Theorem59iStatement` takes a regular algebraic, conjugate self-dual cuspidal class of rank \(n\ge 2\), supercuspidal at \(v\ne c(v)\) in a CM field containing an imaginary quadratic subfield. It gives a single pure rank-\(n\) compatible family, indexed at all finite places of one coefficient field. Weak association uses the normalized unramified local factors from (5.6). [Theorem 5.9(i)](../../Langlands/Galois/Harris1999Theorem59Statement.md) |

The arithmetic normalization steps for the Kottwitz power family use the
inverse scalar avatar on the actual action. The formulation of Theorem
5.7(i) takes the dual of \(H_\pi\otimes\bar\nu(\pi)\). In (5.6), each
nonzero reciprocal root \(\beta\) of the geometric Frobenius Euler
polynomial is replaced by \(\beta/|\beta|\) in the chosen complex
realization. Relating these formulas to the Kottwitz power family uses
the scalar identity at good places for the source representations.
Banality in Harris 1999,
§4, belongs to the torsion calculation. The characteristic-zero
statements above range over the coefficient primes in their displayed
types. Compatible-family matching at good unramified places \(w\) of
the base uses coefficient places \(\lambda\) of residue characteristic
different from that of \(w\).

Harris 1999, Theorem 5.7(iii), treats the decomposition group at the
chosen uniformization place. Theorem 5.9(ii) treats the ramified
restriction at the split supercuspidal \(v\), for coefficient places
of residue characteristic different from that of \(v\). It proves the
split-place application announced in Harris 1998, Theorem 1.7, which
cites a differently titled manuscript. Corollary 5.10 returns to the
Shimura setting and treats a place \(w\) of the totally real field
splitting in the CM field, for a representation occurring in the
cohomology and supercuspidal at \(w\).

The original Taylor letter cited by Harris remains a source gap for
the detailed multiplicity-removal argument. The square-integrable
hypothesis in the full 1998 statement also has a wider range than
Clozel's split-supercuspidal theorem of 1993. The parity and descent
propositions specify the base-change, patching and coefficient inputs
used in that range. Each proposition records an obligation on those
objects. The published source and proof routes are described in
detail in the [1998 cuspidal route](../harris/theorem-12-cuspidal-route.md)
and [registered source record](sources.md).

## Retained originals

Page numbers in the text above are printed pages. The fingerprints
below identify the PDFs used for the mathematical locators. The
*Equish* entry identifies the manuscript PDF within the registered
folder.

| Original and locator | Registered ID | PDF SHA-256 |
| --- | --- | --- |
| Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, supplied 1995–1996 manuscript. §§1.1–1.2 and 1.4–1.6, printed and PDF pp. 1–14 | `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` | `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637` |
| Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993). Corollary 5.3.8, pp. 104–105, PDF pp. 101–102 | `berkovich-1993-etale-cohomology` | `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c` |
| Berkovich, *Vanishing cycles for formal schemes* (1994). §3, pp. 543–544, PDF pp. 5–6. Corollary 5.6, p. 556, PDF p. 18 | `berkovich-1994-vanishing-cycles-formal-schemes` | `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1` |
| Milne, *Étale Cohomology* (1980). V.1, p. 164 | `milne-1980-etale-cohomology` | `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232` |
| Harris, *Galois properties of cohomological automorphic forms on GL(n)* (1999). §2, pp. 303–305, PDF pp. 5–7. (4.2), p. 309, PDF p. 11. §5, pp. 312–315, PDF pp. 14–17 | `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` | `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26` |
| Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001). III.1–2, especially pp. 94–98, PDF pp. 102–106 | `harris-taylor-2001-geometry-cohomology-simple-shimura` | `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b` |
| Faltings, *p-adic Hodge theory* (1988). §1(b)–(c), pp. 255–256, PDF pp. 2–3. III, Theorem 4.1, p. 298, PDF p. 45 | `provided-1991b7d5032d5fe94ca932ccbeccf293bafd80aa29a350ed2fda545cf46b9440` | `2eb8b02f9e3e7662e1e79229488ee7e98240e23f221f1c9aaa7bec79cf329024` |
| Kottwitz, *On the \(\lambda\)-adic representations associated to some simple Shimura varieties* (1992). Theorem 1, p. 657, and §5, p. 661 | `kottwitz-1992-lambda-adic-simple-shimura` | `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799` |
| Clozel, *Représentations galoisiennes associées aux représentations automorphes autoduales de GL(n)* (1991). §5.2–3, especially Theorem 5.7, p. 142 | `clozel-1991-selfdual-galois` | `9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac` |
| Clozel, *On the cohomology of Kottwitz's arithmetic varieties* (1993). Theorem 2.6, p. 772 | `clozel-1993-kottwitz-cohomology` | `cfc3a238c923958759ad6d5b0deedffe47b34c3749630463730b066b9402491b` |
| Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half spaces* (1997). Lemma 4, pp. 82–83, and Theorem 2 and Taylor sketch, pp. 100–103 | `harris-1997-drinfeld-cohomology` | `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9` |
| Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p* (1998). Erratum (E.1)–(E.2), pp. 181–182, Theorem 1.2, p. 185, Lemma 1.6, p. 188, and Theorem 1.7, p. 190 | `harris-1998-local-langlands` | `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b` |
| Serre, *Abelian l-Adic Representations and Elliptic Curves*, 1989 reprint. II §§2.3–2.7, especially §2.5, pp. II-18–II-19, and §2.7, p. II-24 | `serre-abelian-l-adic-1989` | `971dbfdd4414d99ea21d7d0af63dbb790d7b1188e9aec37f422181a2b543dec4` |
