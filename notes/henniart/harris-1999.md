# Harris 1999 and the deferred general-coefficient argument

Author: Worker 3. Companion to [the Henniart audit](audit.md), section 3.1.

The supplied original is M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999), 299–318. Worker 3 read all twenty pages, including the proofs and bibliography, with visual checks of pp. 299, 304–305 and 309–315. Its registered literature ID is `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, and its retained-file SHA-256 is `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`. The supplied Central-Library PDF and [the registered project copy](../../literature/Harris%20%281999%29%2C%20Galois%20properties%20of%20cohomological%20automorphic%20forms%20on%20GL%28n%29.pdf) have the same fingerprint. Below this original is called **Ha99**; **Ha98** means the separately registered 1998 paper in [the source annex](sources.md#ha98).

## What the supplied paper resolves

Ha98, p. 190 defers the complete proof of Theorem 1.7 for general cohomological coefficient systems to a manuscript listed as [H2], *Galois properties of automorphic representations of GL(n)*, on p. 210. Its Proposition 4.8 expressly needs the general-coefficient result on p. 202.

Ha99 supplies a published argument for the required application. Its introduction, p. 299 expressly identifies section 5 as the proof of Ha98's Theorem 1.7. The paragraph immediately before Theorem 5.9, p. 314 identifies part (ii) as the previously announced result. The proof of Theorem 5.9(ii) is on p. 315. This is evidence from the original's actual statement and proof, not an inference from a similar title.

There are two important scope distinctions:

- Ha99's own bibliography [H2], p. 318 refers to **Ha98**, not to the manuscript called [H2] in Ha98. This audit does not assert that the 1998 manuscript and the 1999 publication are identical versions or have identical contents.
- Ha99, Theorem 5.9 assumes a conjugate-self-dual cuspidal cohomological representation and a **split supercuspidal place**. The coefficient residue characteristic must differ from the local residue characteristic. This supplies the case actually used in Ha98, Proposition 4.8: its setup on p. 200 chooses complex-conjugate auxiliary places over a rational prime split in the imaginary quadratic field. H00, section 3.3, p. 449 makes the same splitting choice, retained in the intermediate CM fields. No argument extending Ha99's displayed statement to an arbitrary nonsplit place is claimed here.

Thus the needed general-coefficient argument for Henniart's globalization now has a read, registered original. The differently titled historical manuscript remains unidentified, but it is no longer the only proof-source lead for this application.

## Argument and exact dependencies

| Ha99 location | What is proved or used |
| --- | --- |
| Section 1, pp. 301–302 | Fixes the unitary groups, inner forms, signatures and local invariants. Lemma 1.3 records the existence/parity and Hasse-principle inputs. These hypotheses are retained when realizing cohomological representations on the relevant Shimura varieties. |
| Section 2, pp. 302–306 | Extends the torsion-coefficient construction to compatible complexes. Facts 1–2 use finiteness and a cohomological-dimension bound for the distinguished analytic domains. Facts 3–4 and Lemmas 2.2/2.2 bis use a smooth equivariant Godement resolution and exactness to preserve divisibility in the coefficient systems. Lemma 2.8, p. 306 gives the cohomology/inverse-limit comparison using the Mittag-Leffler condition. |
| Section 3, pp. 306–308 | Compares complex, rational and \(\ell\)-adic realizations of algebraic automorphic forms on the definite inner form, including invariant lattices and finite-level coefficient modules. Small-level hypothesis (3.6) is used for the function-module decompositions. |
| Proposition 4.4, pp. 309–310 | Uses the uniformization (4.3) to obtain the torsion Hochschild-Serre/Ext spectral sequence. The proof first treats banal \(\ell\), then explicitly treats general \(\ell\) by projective resolutions and compact induction. Banality is not a standing hypothesis for section 5. |
| Proposition 4.10 and proof, pp. 311–312 | Passes to the lisse \(\ell\)-adic coefficient sheaf using the complexes from section 2, finite-level decompositions, surjectivity and Mittag-Leffler. This is the general-coefficient replacement for the earlier constant-coefficient spectral sequence. The stronger integral formula is displayed as (4.10.4). |
| Section 5, equations (5.1)–(5.3), p. 312 | At a supercuspidal component the higher Ext terms vanish. Harris invokes his 1997 Theorem 1 and Lemma 2 to obtain concentration in degree \(n-1\), reducing the spectral sequence to the indicated Hom space. The alternative reference [HL] is not needed for the second argument explicitly given here. |
| Theorem 5.7, pp. 313–314 | Applies that comparison to general coefficient systems on the uniformized Shimura varieties. Part (i) uses Taylor's multiplicity argument; the proof explicitly checks geometric origin of the coefficient systems through tensor powers of the universal abelian scheme, so the required Hodge-Tate decomposition applies. Part (ii) invokes Kottwitz and Clozel. Part (iii) is the new local compatibility assertion, using the earlier argument with the new (5.3). The simplifying trivial-action hypothesis on the \(\mathbb Q_p^\times\) factor is stated in the theorem. |
| Lemma 5.8, p. 314 | Checks unramified twists of the local construction via Rapoport–Zink, Lemma 6.44, and explicitly warns that their right action and Harris's left action introduce a sign change; Lemma 5.36 is also cited. |
| Theorem 5.9 and proof, pp. 314–315 | Choose a totally real quadratic extension in which the selected place splits; apply Arthur–Clozel base change, retaining cuspidality through the supercuspidal places. Clozel's Corollary 5.4.2 realizes the restricted compatible family in the appropriate unitary Shimura cohomology. Then apply Theorem 5.7(iii) at a place above the chosen one. Corollary 5.10, p. 315 uses base change back to the unitary setting. |
| Section 6, pp. 315–317 | Additional torsion results under a banality hypothesis. These are not extra assumptions imposed on Theorem 5.9 and are not needed for the Henniart application under audit. |

The labels “1997 Theorem 1,” “Clozel Corollary 5.4.2,” and the other external theorem numbers in this table report Ha99's actual invocations. Their complete proofs are transitive formalization obligations; this table does not claim they have all been independently audited or implemented.

## Normalizations

Ha99, equations (5.4)–(5.5), p. 313 retains the corrected local parameter from Ha98's erratum: local Galois semisimplification, the character \(\bar\nu(\pi_v)\), and the outer contragredient are part of the definition. Equation (5.6) uses **geometric** Frobenius and divides the pure eigenvalues by their complex absolute values in its unitary normalization. These cohomological formulas are not a license to identify a raw cohomology representation with the parameter in the audit without the displayed twists and dual. Lemma 5.8 is the additional consistency check for unramified character twists.

Ha99 does not prove the nonsupercuspidal local-global conjectures 4.9/4.9 bis of Ha98. H00's gamma-factor argument and appendix remain the route used for those local components in this construction.

## The supplied Berkovich construction

Ha99, pp. 299–304 attributes the smooth equivariant acyclic-resolution construction to Berkovich's manuscript [B4], Proposition 1.4.1, and private communications. Its p. 304 lists the properties without repeating the construction. The requested [B96 manuscript](sources.md#b96) is now supplied, registered and read in full, all fifteen printed/PDF pages, with visual checks of pp. 7–12. The registered folder ID is `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`; its receipt digest is `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`. The actual PDF inside that folder has SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`. Both folder members, including the supplied provenance README, match the receipt's file hashes.

The [author-hosted work](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf) is dated 1995–1996 and listed as an unfinished project. The supplied PDF is the complete available fifteen-page manuscript, ending with references; it is not a journal publication or evidence that the larger project was finished. The PDF-production dates recorded in its README are not substituted for the manuscript's date.

| Required interface in Ha99, p. 304 | Checked location and argument in B96 |
| --- | --- |
| Smooth equivariant sheaves | Definition 1.4.1, pp. 7–8 requires discrete, equivalently smooth, stabilizer action on sections over compact quasi-étale domains. Theorem 1.4.2, pp. 8–10 identifies these with sheaves on the equivariant topos. Its proof uses induced spaces for open subgroups, cofinality, and the sheaf condition, followed by the corresponding stalk calculation in the étale case. |
| Functorial embedding and exactness | Section 1.5, p. 10 constructs \(C^0=\nu_*\nu^*\), with the adjunction embedding, and iterates it on cokernels. It records exactness of each \(C^m\) and the split stalk resolution, citing SGA4, XVII, 4.2.3. Pullback \(b^*\) gives the smooth sheaf on the ordinary analytic space. These are precisely the two functors named in Ha99's footnote on p. 304. |
| Compact-support acyclicity | Proposition 1.5.1 and its proof, pp. 10–11 show that \(b^*C^m\) is soft. After shrinking the acting open subgroup and an étale neighborhood, the stalk assertion reduces to products of coinduced finite-Galois modules. Extension of a section from a compact set reduces to the discreteness of the indexing set of geometric points. This supplies the soft resolution used to compute compact-support cohomology. |
| Smooth action on computed cohomology | Corollary 1.5.2, pp. 11–12 identifies the equivariant compact-support construction with ordinary compact-support cohomology, gives its discrete group action and the group-cohomology spectral sequence. |
| Compatible coefficient systems | Ha99's Facts 3–4 and Lemma 2.2, p. 304 apply the exact functor and its stalk description to the \(\ell\)-divisible systems, then iterate the cokernel construction. This coefficient-system argument is stated in Ha99; it is not a separately numbered theorem asserted to appear verbatim in B96. |

The numbering discrepancy is real: **B96, 1.4.1 is a definition**, while the softness proposition is **1.5.1**. Matching the constructed functors and their properties resolves the needed source lead; it does not identify the supplied version byte for byte with the earlier manuscript or private communications Harris saw.

B96 itself invokes earlier foundations, especially the analytic lifting Key Lemma in its [Ber3], 7.2, the definition and properties of soft analytic sheaves in [Ber3], section 3, and SGA4's Godement construction. Those labels are B96's attributions, not claims that their complete original proofs were read for this note. They remain transitive formalization obligations.

Request `590d13379ffa50a4ad2f3c02b3fb3769` has a completed source response; access, registration and the required reading have now been verified. The supplied Harris and Berkovich originals resolve the two successive acquisition leads for this application. They do not close the entire cohomological proof chain, identify every historical version, or supply a Lean proof.
