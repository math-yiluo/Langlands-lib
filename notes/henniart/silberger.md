# Silberger's quotient theorem: original-source completion

Author: Worker 3. Companion to [the Henniart audit](audit.md), section 4.1.

The requested Silberger article is now accessible and has been read in full: all ten printed pages 95–104, including the proofs in sections 5–7 and the bibliography. This closes the article-access and reading boundary recorded in the earlier audit. The separately supplied Harris paper is treated in [its own companion](harris-1999.md). Neither reading establishes a Lean theorem.

## Retained originals

| Label | Registered original and exact fingerprint | Reading |
| --- | --- | --- |
| S78 | A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math. Ann. 236 (1978), 95–104. Literature ID `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`; SHA-256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`. [Retained original](../../literature/Silberger%20%281978%29%2C%20The%20Langlands%20quotient%20theorem%20for%20p-adic%20groups.pdf). | Entire article; PDF page \(k\) is printed page \(k+94\). Pages 96–104 were also read visually to check the formulas and opposite parabolics lost in extraction. |
| S79 | A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic groups*, Princeton University Press and University of Tokyo Press, 1979. Literature ID `silberger-1979-harmonic-analysis`; SHA-256 `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`. [Retained original](<C:/Central-Library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf>). | Title/publication pages; section 0.4, pp. 7–8, and opening of 0.5, p. 9, read visually. PDF page \(k\) is printed page \(k-6\) here. This is not a reading of the entire book. |

The supplied project PDF and the newly available Central-Library copy of S78 have identical bytes. The existing registration was reused. Request `c11d84f15c5e5778aaa2ed27a2ea21b8` has a completed source response. Actual file access, the fingerprint, and the reading were verified separately.

## Statement and convention translation

S78, Theorem 4.1, p. 99 applies to the points of any connected reductive group over a nonarchimedean local field. Fix a standard parabolic \(P=MN\), an irreducible tempered representation \(\sigma\) of \(M\), and a real parameter \(\lambda\) in the positive chamber, regular for the roots of \(P\). Then:

1. \(I(P,\sigma_{-i\lambda})\) has exactly one irreducible quotient, denoted \(J(\sigma,\lambda)\).
2. Equality of two such quotient classes forces equality of their standard parabolics, tempered classes, and real parameters.
3. Every irreducible admissible representation occurs in this way.

S78, p. 96 defines \(I(P,\sigma)=\operatorname{Ind}_P^G(\delta_P^{1/2}\sigma)\) and
\[
 \chi_\mu(m)=q^{\,i\langle\mu,H_M(m)\rangle},
 \qquad \sigma_\mu=\sigma\otimes\chi_\mu.
\]
Thus its subscript \(-i\lambda\) means the positive real character \(q^{\langle\lambda,H_M(m)\rangle}\). Losing the \(i\) in text extraction obscures the distinction between real and unitary twists. S79, section 0.4, pp. 7–8 fixes
\[
 |\varpi|=q^{-1},\qquad
 \langle\chi,H_M(m)\rangle=\log_q|\chi(m)|.
\]
For an upper block parabolic of \(\mathrm{GL}_n\), writing \(\lambda=\sum_j t_j\det_j\) therefore gives
\[
 \chi_{-i\lambda}(\operatorname{diag}(m_1,\ldots,m_k))
       =\prod_j|\det m_j|^{t_j}.
\]
The positive regular chamber is \(t_1>\cdots>t_k\). This agrees with the decreasing real exponents used for the audit's Langlands quotient. It does not change the increasing-segment convention for each individual special quotient.

Equal exponents among square-integrable blocks must first be grouped into a tempered representation of a larger Levi. S78's regularity condition is then imposed between groups with distinct exponents; when the parabolic is the whole group it is vacuous. The additional facts that these products of unitary square-integrable \(\mathrm{GL}_n\) blocks are irreducible and exhaust the tempered classes belong to the special/tempered classification. They are not supplied by Theorem 4.1 alone. Use the separate Zelevinsky/Henniart interfaces already recorded in [the audit, section 4.1](audit.md#41-parameter-decomposition-and-special-quotients).

## Proof and upstream dependency map

The following is a report of the argument actually read in S78. The numbered references to its bibliography [4] are **S78's citations to the then-forthcoming book**, not a claim that all those numbered results or their proofs have been independently checked in S79.

| S78 location | Argument and results invoked |
| --- | --- |
| Section 2, pp. 97–98 | Jacquet modules are admissible, exact and transitive; normalized induction is exact and transitive. Frobenius reciprocity and the opposite-parabolic relation express quotients using the opposite Jacquet module. S78 cites [4], Corollaries 2.3.6 and 1.7.11, Theorem 3.3.1. Its cuspidal Jacquet multiplicity formula cites Theorem 5.4.1.1; detection of each constituent and finite length cite Corollary 5.4.4.6. The reduction to cuspidal induction cites Corollaries 2.4.2 and 2.8.3. |
| Section 3, pp. 98–99 | The square-integrability and temperedness criteria are inequalities on normalized Jacquet exponents, citing [4], Theorem 4.4.4 and Lemma 4.5.3. Tempered classes occur as direct summands of induction from discrete series. General reductive tempered induction can be reducible; no general irreducibility claim is made here. |
| Proposition 5.1 and Lemmas 5.2–5.6, pp. 99–101 | Reduce the inducing tempered representation through discrete series and cuspidal induction, using [4], Corollary 4.5.11, Corollary 2.4.2 and Theorem 4.4.4. For generic real parameters, a Weyl-stabilizer/multiplicity calculation gives uniqueness of the quotient. Corollary 5.4 uses Casselman's projectivity of supercuspidals in the category with fixed central exponent. Lemma 5.6 extends the calculation to every regular positive parameter, using variation of Jacquet exponents, tempered inequalities and a Weyl-invariant norm argument. |
| Propositions 5.7–5.9, pp. 101–102 | Recover the inducing tempered constituent from its quotient and compare quotient multiplicities. Proposition 5.8 is used in the subsequent uniqueness proof; these steps are stronger than merely proving that some quotient exists. |
| Proposition 6.1 and Corollary 6.2, pp. 102–103 | Cuspidal-support conjugacy, cited as [4], Corollary 5.3.2.2, supplies a Weyl element. Tempered exponent inequalities and the equality case of Schwarz's inequality identify the real parameters and standard parabolic. Propositions 5.7–5.8 then identify the tempered class. Corollary 6.2 handles nonstandard parabolics by conjugacy. |
| Lemma 7.1 and Proposition 7.2, pp. 103–104 | A root/weight cone decomposition, attributed to Langlands [3], Lemma 4.4, p. 87, is extended from simple roots to parabolic roots. Choose a Jacquet exponent with maximal positive support. The remaining exponent inequalities imply that the resulting Levi representation is essentially tempered, giving exhaustion. The separate essentially tempered and central-character reductions are stated at the start of p. 104. |

The finite-dimensional cone lemma and the fixed-central-exponent projectivity assertion are actual upstream requirements of this proof route. Recording them avoids treating the quotient theorem as an unexplained choice of a constituent. Langlands [3] and the unread parts of [4] are transitive source leads reported from S78; this note does not present them as directly audited originals.

No Haar measure used for Fourier transforms or local factors is chosen by Theorem 4.1. Its normalized induction agrees with the audit's representation-side convention, while the additive character, self-dual measure and pair-factor conventions remain those checked in the main audit. The Silberger theorem supplies classification, not the JPSS factor identities. Those remain separate downstream inputs.

The new source closes one explicitly requested reading obligation. The full classification formalization and independent acceptance and publication of this update remain separate obligations. Neither the reading record nor a checked planning DAG is a proof of the local correspondence.
