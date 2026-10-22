# Henniart's construction and the full local correspondence: source audit

Author: Worker 3. Assignment: `cb578e50-7934-4825-bc45-c4e5f7827257`, revision 1.

This is a source and dependency audit, not a proof in Lean. Henniart's 2000 paper has been read in full, including its appendix and bibliography. Other originals have been read at the locations recorded in [the source register](sources.md). The register gives the exact retained file, registered literature ID, SHA-256 fingerprint, and reading extent. An abbreviated citation such as [H00, 2.4](sources.md#h00) always refers to that exact registered copy. Printed page numbers are used unless explicitly identified as PDF or internal pages.

The audit checks the theorem interfaces and the construction's dependencies. It does not claim to have checked every proof in the transitive literature closure. In particular, the global cohomological results behind Harris's theorem, the full proof of the numerical correspondence, and the complete proofs of the classification theorems remain major formalization projects. Registration establishes source access, not mathematical acceptance. Publication and independent acceptance of this note are determined by the TaskHub receipts.

The supplied Silberger 1978 and Harris 1999 papers and Berkovich manuscript are now accessible and have been read in full. [The Silberger companion](silberger.md) records the quotient theorem's proof and conventions. [The Harris companion](harris-1999.md) identifies the published general-coefficient argument needed at Henniart's split supercuspidal places and compares its equivariant-resolution input with the supplied Berkovich construction. It does not identify Harris's differently titled 1998 manuscript [H2] with the 1999 paper or extend the latter's displayed theorem to nonsplit places. The transitive cohomological dependencies remain explicit.

## 1. Scope and current formal evidence

For every prime \(p\), finite extension \(F/\mathbb Q_p\), and integer \(n\geq1\), the theorem stated in [H00, 1.1-1.2, pp. 439-440](sources.md#h00) is a bijection

\[
  \operatorname{rec}^{\,0}_{F,n}:
  \{\text{irreducible continuous complex }n\text{-dimensional representations of }W_F\}/\simeq
  \longrightarrow
  \{\text{irreducible smooth supercuspidal representations of }\mathrm{GL}_n(F)\}/\simeq .
\]

The representation spaces on the right are not required to be finite dimensional. The convention on the left is the usual finite-inertia complex Weil representation convention; its relation to continuity for the Weil topology and the usual complex topology must be proved when constructing the interface.

The **full** correspondence has Frobenius-semisimple Weil-Deligne representations of dimension \(n\), including nonzero monodromy, on the left, and all irreducible admissible smooth complex representations of \(\mathrm{GL}_n(F)\) on the right. Its extension from the displayed theorem is described in [H02, 1.1-1.8 and 2.1-2.9, pp. 588-591, 593-596](sources.md#h02). A direct sum of irreducible Weil representations with zero monodromy is only part of that domain. An arbitrary irreducible representation on the right need not be generic.

The published Library snapshot actually inspected for this audit is commit
`10c81beaaff024987cf2945c64d0c9511f6cb686`, manifest SHA-256
`aba99af67d5ac39a4ac06530dc77c33aabe8bb06cbda5fcfb527d958a7a95003`.
It contains the mathematical pair
`Langlands/Representation/Smooth/Definitions.lean` and `.md`, with respective hashes
`435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` and
`4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.
That pair defines fixed vectors, smooth vectors, smoothness, and admissibility. Admissibility there includes smoothness and finite generation of fixed vectors for every open subgroup. The bridge to the customary compact-open test is a separate obligation. This snapshot contains no local correspondence construction or proof. This statement is about the inspected snapshot, not a claim about every result in Mathlib or later publications. No Lean files are submitted or compilation results claimed by this note.

A subsequent **inventory-only** check pins public commit `222c68bf63c67a73c49f5a4d2e1b80c84dbf0154`, manifest SHA-256 `83ad449bf9350bb08154aaf4d6d14efaa055199f8e4dca813207a916c48ff747`. Its complete mathematical inventory consists of 25 Lean/Markdown pairs, with the following paths under `Langlands/` (each stem has both extensions):

| Directory | File stems |
| --- | --- |
| `LocalField/` | `Definitions` |
| `Representation/Compact/` | `Definitions`, `FiniteMean` |
| `Representation/Dual/` | `Definitions`, `LawsStatement` |
| `Representation/Smooth/` | `Definitions` |
| `Representation/Smooth/Admissibility/` | `CofinalStatement`, `EmbeddingStatement`, `EquivalenceStatement` |
| `Representation/Smooth/FixedVectors/` | `Definitions`, `OrderStatement` |
| `Representation/Smooth/SmoothPart/` | `Definitions`, `UniversalStatement` |
| `Representation/Smooth/Transfer/` | `PullbackStatement`, `StabilizerStatement`, `SubquotientStatement` |
| `Representation/Twist/` | `Definitions`, `AlgebraStatement`, `DualStatement`, `IntertwiningStatement`, `PullbackStatement`, `SmoothStatement` |
| `Topology/CompactOpen/` | `NeighborhoodBasisStatement`, `OpenSubgroupStatement` |
| `Weil/` | `Pullback` |

The original smooth pair retains the hashes recorded above. The newer inventory contains foundational constructions, helpers and proposition targets; it does not list a local-correspondence implementation. This check reads the manifest and searches the paired Markdown to identify scope. It does not claim a semantic review or proof acceptance for the new modules, and they are not used as mathematical dependencies of this note. In particular, a file named `Statement` is not evidence that its proposition has been proved. All later publication claims must be checked against their own exact artifacts and receipts.

## 2. One consistent normalization

These conventions match Henniart's stated theorem and the factor sources. They must be recorded in definitions before theorem statements are frozen.

| Item | Convention and source |
| --- | --- |
| Reciprocity direction | Write \(\tau_F:W_F\to F^\times\), factoring through the abelianization. It sends **geometric** Frobenius \(\Phi\) to a uniformizer. Its inverse on abelianizations is the map from \(F^\times\) sending a uniformizer to geometric Frobenius. [H00, 1.1, p. 439](sources.md#h00); [T79, 1.4.1](sources.md#t79); [D73, 2.3, internal/PDF p. 23](sources.md#d73). |
| Normalized absolute value | For \(q=\#k_F\), \(v_F(\varpi)=1\), put \(\nu_F(x)=|x|_F=q^{-v_F(x)}\). On \(W_F\), use \(\nu=\nu_F\circ\tau_F\), so \(\nu(\Phi)=q^{-1}\). On \(\mathrm{GL}_d(F)\), \(\nu(g)=|\det g|_F\). [T79, 2.2, 4.1](sources.md#t79); [J81, 1.2, p. 200](sources.md#j81). Do not use the restriction of a differently normalized absolute value on an extension field without its degree conversion. |
| Multiplicative characters | In H00's footnote, “character” means unitary; “quasi-character” means a continuous homomorphism to \(\mathbb C^\times\). The twisting compatibility is for arbitrary quasi-characters. H88 uses a different vocabulary. Always state unitary hypotheses explicitly. [H00, 1.1-1.2](sources.md#h00); [H88, 1.2, footnote on p. 498](sources.md#h88). |
| Additive character | \(\psi:F\to\mathbb C^\times\) is nontrivial and continuous; here it is unitary. The theorem is valid for every such \(\psi\), with the same correspondence. For Whittaker models use \(\psi(\sum_i u_{i,i+1})\) on the upper unipotent group. The second Whittaker model in the pair integrals uses \(\overline\psi=\psi^{-1}\). [H00, 1.2-1.3](sources.md#h00); [J83, notation pp. 376-378, Theorem 2.7 pp. 390-391](sources.md#j83). |
| Fourier transform and Haar measure | Use \(\widehat f(y)=\int_F f(x)\psi(xy)\,dx_\psi\), with \(dx_\psi\) self-dual, hence \(\widehat{\widehat f}(x)=f(-x)\). On matrix spaces use the trace pairing and product self-dual measure. H93 explicitly suppresses the self-dual Haar measure in both kinds of epsilon factor. [H93, 1.1-2.1, pp. 339-341](sources.md#h93); [T79, 3.2-3.6](sources.md#t79); [J83, notation p. 378](sources.md#j83). |
| Parabolic induction | Use **normalized** induction from an upper block-triangular parabolic, with right translation and transformation rule \(f(mug)=\delta_P(m)^{1/2}\sigma(m)f(g)\). For block sizes \(n_i\), \(\delta_P(m)=\prod_{i<j}|\det m_i|^{n_j}|\det m_j|^{-n_i}\). [H02, 2.5, pp. 594-595](sources.md#h02); [J83, notation pp. 377-378](sources.md#j83). J83 Theorem 3.1 uses the lower parabolic; translating its ordering requires conjugating the parabolic, not changing the normalization. |
| Duals | A dual means the smooth contragredient on the representation side and the linear dual on the finite-dimensional parameter side. For a Weil-Deligne pair use \((r^\vee,-N^{\mathsf t})\). The inverse-transpose description on \(\mathrm{GL}_n\) and the change from \(\psi\) to \(\psi^{-1}\) in Whittaker models must not be omitted. [T79, 4.1](sources.md#t79); [J81, 1.2](sources.md#j81); [Ze80, 9.4](sources.md#ze80). |
| Twists | \(\sigma\chi=\sigma\otimes(\chi\circ\tau_F)\); \(\pi\chi=\pi\otimes(\chi\circ\det)\). Thus an unramified twist by \(\nu^t\) shifts \(s\) to \(s+t\) in a standard factor, and twisting the two members of a pair by \(\nu^t,\nu^u\) shifts \(s\) by \(t+u\). [H00, 1.2, 4.4](sources.md#h00); [H93, section 4](sources.md#h93); [H02, 2.3-2.6](sources.md#h02). |

In rank one the direction is therefore
\(\operatorname{rec}^{\,0}_{F,1}(\chi\circ\tau_F)=\chi\).
Using arithmetic Frobenius instead changes both the reciprocity identification and the Frobenius used in the Euler factor. One cannot change just one of them.

### 2.1 Weil-Deligne factors

For a finite-dimensional complex pair \(D=(r,N)\), require
\[
 r(w)Nr(w)^{-1}=\nu(w)N,\qquad N\text{ nilpotent}.
\]
Frobenius semisimplicity is semisimplicity of the Frobenius action in \(r\), equivalently semisimplicity of the underlying Weil representation here. It does **not** mean \(N=0\). Frobenius semisimplification preserves the monodromy operator. See [D73, 8.4-8.6, internal/PDF pp. 68-70](sources.md#d73) and [T79, 4.1, pp. 19-21](sources.md#t79).

Let \(V_N=\ker N\). With geometric \(\Phi\),
\[
\begin{split}
 L(s,D)&=\det(1-q^{-s}r(\Phi)\mid V_N^{I_F})^{-1},\\
 \epsilon(s,D,\psi)&=\epsilon_D(r\nu^s,\psi,dx_\psi)\,
  \det(-q^{-s}r(\Phi)\mid V^{I_F}/V_N^{I_F}),\\
 \gamma(s,D,\psi)&=\epsilon(s,D,\psi)
              \frac{L(1-s,D^\vee)}{L(s,D)} .
\end{split}
\]
Here \(\epsilon_D\) denotes Deligne's local constant for a Weil representation. The quotient determinant is essential when \(N\ne0\). Tensor products have monodromy \(N\otimes1+1\otimes N'\). The Artin-conductor correction is
\(a(D)=a(r)+\dim V^{I_F}-\dim V_N^{I_F}\).
These are [T79, 4.1, pp. 20-21](sources.md#t79), with the spectral parameter inserted by twisting; [H02, 2.1-2.4](sources.md#h02) gives the decomposition calculations used below.

Tate distinguishes the constants:
\[
 \epsilon(s,r,\psi)
 =\epsilon_D(r\nu^s,\psi,dx_\psi)
 =\epsilon_L(r\nu^{s-1/2},\psi).
\]
In particular \(\epsilon_L(r,\psi)=\epsilon_D(r\nu^{1/2},\psi,dx_\psi)\). Dropping this half shift changes the theorem. [T79, 3.6, p. 17](sources.md#t79).

The self-dual measure is the authoritative normalization. If \(\psi_a(x)=\psi(ax)\), then
\[
 dx_{\psi_a}=|a|^{1/2}dx_\psi,\qquad
 \epsilon(s,D,\psi_a)=\det r(\tau_F^{-1}(a))\,
 |a|^{\dim D(s-1/2)}\epsilon(s,D,\psi).
\]
The determinant notation means evaluation of the abelian character of \(F^\times\); it does not require choosing an inverse into \(W_F\). At a fixed Haar measure, Tate's exponent before the self-dual rescaling is \(\dim D(s-1)\); multiplying a Haar measure by a positive \(c\) multiplies the epsilon constant by \(c^{\dim D}\). [T79, 3.4, pp. 14-15](sources.md#t79). The determinant correction for \(N\) is independent of \(\psi\), so the same scaling rule holds for \(D\).

For a pair of ranks \(n,n'\), this yields the change-of-character multiplier
\[
 \omega_\pi(a)^{n'}\omega_{\pi'}(a)^n
 |a|^{nn'(s-1/2)}.
\]
It agrees with the parameter determinant once central characters match. This is why the equality for one additive character in H00 is independent of that choice. The ordinary dual functional equation uses \(\psi^{-1}\):
\[
 \epsilon(s,D,\psi)\epsilon(1-s,D^\vee,\psi^{-1})=1.
\]
Keeping the same \(\psi\) instead gives \(\det D(-1)\); the pair version has the corresponding product of central-character values. These are derived consequences of the factor normalization, not additional axioms.

### 2.2 Representation factors

[J83, Theorem 2.7, pp. 390-391](sources.md#j83) constructs the rational local zeta integrals for generic pairs, their normalized greatest-common-divisor factor
\(L(s,\pi\times\pi')=P(q^{-s})^{-1}\), \(P(0)=1\), and a nonzero monomial epsilon factor. Set
\[
 \gamma(s,\pi\times\pi',\psi)=
 \epsilon(s,\pi\times\pi',\psi)
 \frac{L(1-s,\pi^\vee\times\pi'^\vee)}
      {L(s,\pi\times\pi')}.
\]
The local integral equation has additional displayed central-character signs, for example \(\omega_{\pi'}(-1)^{n-1}\) in the unequal-rank equation. Those signs are part of the integral identity and its Weyl-element convention; they are not an extra multiplier in this definition of gamma.

[J83, Theorem 3.1, pp. 404-405](sources.md#j83) gives gamma multiplicativity for a generic constituent. It does not justify asserting arbitrary constituent-wise multiplicativity of \(L\). The special, tempered, and Langlands-quotient statements are separate: Theorem 8.2, section 8.4, and sections 9.4-9.5, respectively. Nongeneric factors are defined through the unique Langlands standard module in section 9.4, and section 9.5 states the resulting multiplicativity. Thus an abstract function satisfying “multiplicativity” is not a construction of these factors.

Shahidi's raw local coefficient is another object. [Sh84, Theorem 5.1, p. 103](sources.md#sh84) states a comparison after normalizing the defining measures, with a factor \(\omega_2(-1)^m\) and a contragredient in the second Rankin-Selberg argument. [HH95, 8.16, pp. 181-182](sources.md#hh95) explains its use in the global functional equation. A future implementation through local coefficients must explicitly translate the Weyl representative, additive character, dual, and measures. The present audit fixes the JPSS factors and does not supply that complete local-coefficient implementation dictionary.

## 3. The 2000 construction, with its actual inputs

The following is the construction in the paper, rather than an invocation of a theorem named “LLC.” None of these proof nodes is discharged by this note.

| Stage | Exact place in H00 | Required mathematical result or construction |
| --- | --- | --- |
| Define weak global association | 2.1-2.2, pp. 443-444 | Global Weil representations and automorphic cuspidal representations with matching almost-everywhere unramified local data. Global class field theory supplies the rank-one case. Chebotarev and [JS81, Theorem 4.2, pp. 806-807](sources.md#js81) supply rigidity. JS81 actually proves linear independence of distinct cuspidal classes from unramified traces, stronger than an unexplained appeal to multiplicity one. |
| Compare local gamma factors | Theorem 2.3, pp. 444-445 | [H86, Theorem 4.1 and proof 4.2-4.3, pp. 157-159](sources.md#h86): compare global functional equations and isolate the required finite place by highly ramified twists at the other bad places. Weak association alone does not directly give equality of the separate local \(L,\epsilon\) factors. |
| Control the local automorphic constituent | Theorem 2.4, p. 445; Appendix A.1-A.3, pp. 453-454 | For an irreducible unitary global Weil representation weakly associated to a unitary cuspidal automorphic representation, each finite automorphic component is induced from unitary supercuspidals. The proof uses the special shape of the gamma factor, [Ze80, 9.3, 9.7](sources.md#ze80), [Ta86, Theorem D](sources.md#ta86), and JPSS pair-factor calculations. It is not a general Ramanujan theorem. |
| Separate \(L\) and epsilon | Corollary after Theorem 2.3, p. 445 | [H86, Lemma 4.4 and Proposition 4.5, pp. 159-160](sources.md#h86): under the unitary/tempered conditions, numerator and denominator have separated pole regions, so equality of gamma implies equality of \(L\), then epsilon. |
| Construct a virtual map | 2.5-2.8, pp. 445-448 | Free abelian groups on irreducible Weil classes and on supercuspidal classes, with degree and operations. For the unitary local objects just obtained, the order at zero of the factor with a dual gives the ordinary positive definite pairing of constituent multiplicities. It proves that all linear relations descend and that the map is an isometry. |
| Globalize enough induced characters | 3.1-3.7, pp. 448-451 | Realize a prescribed finite local extension globally; build appropriate regular algebraic, conjugate-self-dual Hecke characters with an auxiliary regular local component; use Harris's weak automorphic induction; apply Brauer induction to obtain the required lattice. See the detailed dependencies below. |
| Obtain irreducible local images | 2.8 and 3.8, pp. 448, 451 | An integral vector of squared norm one is a signed basis vector. Positive degree rules out the negative sign. This is the step producing a supercuspidal representation from a virtual object. |
| Remove the finite-extension choices | 4.1-4.3, pp. 451-453 | Induct on rank. Use the finite set of supercuspidal candidates of the prescribed central character and conductor, distinguish its unequal pairs by finitely many lower-rank tests using [H93, 1.1 and corollary](sources.md#h93), and enlarge the auxiliary extension to include that finite set of witnesses. Lower-rank surjectivity is used to lift the tests. |
| Establish surjectivity | 1.3 and 4.3, pp. 440-441, 452-453 | [H88, Theorem 1.2, p. 498](sources.md#h88): an injection respecting conductors and unramified twists is surjective. This is a structured counting theorem; equality of two infinite cardinalities would not suffice. |
| Remove finite-order determinant restriction | 4.4, p. 453 | Every irreducible Weil class has an unramified twist with finite-order determinant; extend the result by twisting and prove independence of the twist. H00 refers to [H93, section 4](sources.md#h93). |

The target group in the virtual step is the free abelian group on supercuspidal classes across ranks. Its positive elements encode supercuspidal support. It is not the Grothendieck group of all irreducible \(\mathrm{GL}_n(F)\) representations, and this step does not define the full monodromic correspondence. In H00, 2.8, the reference to “Theorem 2.3” for induction from unitary supercuspidals should be read with Theorem 2.4, which states that assertion.

### 3.1 Global and arithmetic prerequisites

1. **Local and global class field theory, Chebotarev, and finite-group Brauer induction.** These are substantive inputs, not implementation conveniences. Finite-order determinant gives finite image for an irreducible complex Weil representation, and unramified twisting reduces to that case; [H88, 2.2-2.3, p. 504](sources.md#h88). Brauer induction then expresses a finite-image representation as an integral virtual sum of induced one-dimensional characters. The exact lattice arguments are H00, 2.5-2.8 and 3.7.

2. **Number-field realization.** H00, 3.3, p. 449 cites [H84, Lemma 3.6, internal pp. 34-35](sources.md#h84). Its proof uses local polynomial approximation and Krasner's lemma. H00 needs the totally real enhancement, followed by imaginary-quadratic and real-quadratic choices with the specified splitting at \(p\), and two distinguished local places. The cited lemma's displayed statement does not itself include the totally real condition. An implementation must add the simultaneous archimedean approximation argument rather than treating that strengthened statement as literally quoted.

3. **Hecke characters.** H00, 3.4-3.6, pp. 449-451 constructs a conjugate-self-dual regular algebraic character. The unramified part uses finiteness of ideal class groups and the relevant unit subgroup index; the finite-order correction prescribes the required finite local components, while retaining regularity at the auxiliary place. [Ha98, Lemma 4.7, statement p. 201, proof pp. 204-206](sources.md#ha98) provides local characters of arbitrarily high conductor in general position. Its proof uses Clifford-Mackey theory, local class field theory, the \(p\)-adic logarithm, the normal basis theorem, and avoidance of finitely many proper submodules to construct characters with the required stabilizer.

4. **Harris's weak automorphic induction.** [Ha98, Proposition 4.8, pp. 201-203](sources.md#ha98) is the required global statement for the regular algebraic conjugate-self-dual character and auxiliary general-position component. Its rank is unrestricted by the \(n<p\) in the article title. There are two distinct Galois-representation inputs. **Theorem 1.2**, p. 185, gives a weakly associated compatible family for the regular cohomological isobaric representations satisfying its CM-field, conjugate-self-duality, square-integrable-place and splitting hypotheses. **Theorem 1.7**, p. 190, identifies the restriction of that family to a decomposition group at a supercuspidal place with Harris's local parameter of the supercuspidal component, for each \(\ell\) different from the local residue characteristic, in Harris's conventions. Theorem 1.2 supplies almost-everywhere unramified association; it does not supply this ramified local-global compatibility.

   The remark inside the proof of Proposition 4.8, p. 202, explicitly invokes the full strength of Theorem 1.7 because the intermediate \(\Pi(a,i)\) may have arbitrary cohomological infinity type. Choosing the infinity type at one place does not control all the other places over the same archimedean place. Thus one cannot replace this input with the trivial-coefficient case. The induction uses local compatibility to maintain the auxiliary supercuspidal condition while constructing and descending the global automorphic representations. Its final output includes weak automorphic induction and a supercuspidal auxiliary local component. Merely requiring weak association in H00's later use does not remove the stronger prerequisite from the proof of Proposition 4.8.

   **Original deferral and subsequent proof:** immediately after Theorem 1.7 on p. 190, Harris says that its complete proof will appear in [H2]. The trivial-coefficient case is essentially proved in [H1], whereas section 4 requires more general coefficient systems; he explicitly allows section 4's results to be regarded as conditional pending [H2]. The appendix, pp. 206-209, separately treats auxiliary level restrictions from [H1]. Its uniformization and Weil-descent argument removes dependence on the other local components above \(p\); it does not purport to supply the deferred general-coefficient argument. The bibliography, p. 210, identifies [H2] as *Galois properties of automorphic representations of GL(n)*, manuscript (1998).

   The supplied [Ha99, introduction p. 299 and Theorem 5.9(ii), pp. 314-315](sources.md#ha99) explicitly identifies and proves the previously announced result for a **split supercuspidal place**, with general cohomological coefficients. That split hypothesis holds in the required application: Ha98, p. 200 chooses complex-conjugate places over a prime split in the imaginary quadratic field, as does H00, 3.3, p. 449; the intermediate CM fields retain this splitting. The general-coefficient construction uses Ha99's Propositions 4.4 and 4.10, pp. 309-312, followed by the supercuspidal Ext degeneration and Theorem 5.7(iii), pp. 312-314. Theorem 5.9 descends the conclusion after a totally real quadratic base change. [The companion](harris-1999.md) maps the proof and its actual upstream inputs. This resolves the required proof-source lead for Henniart's application; it does not prove an unqualified nonsplit version or assert that the two differently titled manuscripts are identical. Ha99's own bibliography [H2] means Ha98, so the two bibliography labels must not be conflated.

   Harris's account of Theorem 1.2, pp. 185-186, also identifies Kottwitz and Clozel, Taylor's multiplicity removal, and the parity issue resolved using quadratic base change and Blasius's observation. These are distinct transitive inputs, not substitutes for local compatibility. Ha99, pp. 299-304 additionally uses Berkovich's smooth equivariant acyclic-resolution construction, attributed to manuscript [B4] and private communications. The supplied [B96, 1.4.2-1.5.2, pp. 8-12](sources.md#b96) provides the required functors and compact-support comparison under different numbering; the complete fifteen-page manuscript has been read. [The companion](harris-1999.md#the-supplied-berkovich-construction) records the argument comparison, exact file fingerprint and historical-version qualification. The underlying cohomological proof chain is not claimed fully audited or formalized merely because these sources have been read.

5. **Actual global functional equation.** H00, 1.8 and 2.3, and [HH95, 8.16, p. 181](sources.md#hh95) distinguish an announcement from a proof. The latter uses [Sh81, Theorem 4.1 and the following \(\mathrm{GL}_{n+m}\) example, p. 344](sources.md#sh81), [Sh84, Theorem 5.1, p. 103](sources.md#sh84), and [Sh85, Theorem 3.1 and Remark 2, pp. 990-991](sources.md#sh85). The first is a global partial functional equation with local coefficients; the second identifies finite-place factors with the requisite sign and measures; the third supplies the archimedean Artin-factor comparison. The archimedean fineness hypothesis in Sh81 is accounted for in the stated GL example. H00's reference to HH95, 8.15 should include the actual discussion in 8.16.

6. **Highly ramified twisting.** H86, Lemma 4.2 invokes [DH81, Theorem 4.6, p. 110](sources.md#dh81), on stability of constants for virtual Weil representations with the stated ramification bounds, and [JS85, sections 1, 4.1-4.2, 5.1-5.2, pp. 319, 326-327, 331](sources.md#js85), for the representation side. After sufficiently ramified twists the relevant \(L\) factors are one and the pair constants depend on the appropriate central characters. Existence of a global Hecke character with the needed finite local specifications is another step in H86's place-isolation argument.

7. **Conductor and finiteness inputs.** The numerical theorem and H00, 4.3 need finite sets with fixed invariants, not a finite entire supercuspidal dual. [J81, 1.1, 5.1, pp. 199, 211](sources.md#j81) connects the epsilon exponent at conductor-zero \(\psi\) with the generic newvector conductor. [J12, pp. 515-517](sources.md#j12) explicitly corrects an error in the essential-vector existence proof and mentions its use in JS85. Any implementation following this part of the proof must use the corrected argument. Reading the correction's theorem is not a claim that the full correction has already been formalized or audited.

The alternative constructions and historical comparisons in H00's introduction are not all mandatory prerequisites of its proof. In particular, the full Harris-Taylor bad-reduction calculation is not what H00 imports to deduce Theorem 2.4; the appendix supplies that step from gamma factors and classification. This avoids the stronger general-place compatibility requested in Ha98, Conjectures 4.9 and 4.9 bis, p. 203. It does **not** remove the supercuspidal-place Theorem 1.7 used upstream to prove Proposition 4.8.

### 3.2 The appendix needs a corrected pole argument

H00, A.2 invokes Zelevinsky's generic classification and Tadic's unitary classification to write a unitary generic local component as a product of twists \(\nu^{s_i}\delta_i^0\), with \(-1/2<s_i<1/2\), each \(\delta_i^0\) unitary square integrable. The data occur in Hermitian pairs \(s_i,-s_i\). The genericity restriction eliminates the nontrivial Speh blocks in Tadic's general unitary classification. This use of [Ze80, 9.7](sources.md#ze80) and [Ta86, Theorem D, pp. 338-339](sources.md#ta86) is essential; unitarity alone does not imply temperedness.

Write \(\delta_i^0\) as the special quotient of
\(\nu^{-r_i/2}\rho_i,\ldots,\nu^{r_i/2}\rho_i\), where \(r_i\geq0\) is an integer and \(\rho_i\) is unitary supercuspidal. The pair \(L\)-formula gives real poles only at
\[
  s=-(r_i+r_j)/2+k-s_i+s_j,\qquad
  0\leq k\leq\min(r_i,r_j),
\]
when the underlying supercuspidal pair has a real pole. For unitary supercuspidals that real pole is zero and requires the matching dual condition; [J83, 8.1-8.2, pp. 443-445](sources.md#j83).

H00, A.3, p. 454 prints \(r+2\sigma\) as the most positive real pole, where \(r=\max r_i\) and \(\sigma=\max_{r_i=r}s_i\). That equality is not correct as stated: a single centered Steinberg block with \(r>0\) has pair poles \(-r,-r+1,\ldots,0\). The printed step must not be translated verbatim.

The needed conclusion follows from the following direct replacement argument, supplied here as an unformalized derived lemma for independent checking. Every displayed real pole is strictly less than \(1\), since \(k\leq(r_i+r_j)/2\) and \(s_j-s_i<1\). Also
\[
 r_i/2+|s_i|\leq r/2+\sigma.
\]
For \(r_i=r\), this uses Hermitian pairing; for \(r_i<r\), it uses the integer gap and \(|s_i|<1/2\). Thus no pole is smaller than \(-r-2\sigma\). The Hermitian pair with \(r_i=r_j=r\), \(s_i=\sigma\), \(s_j=-\sigma\), the same \(\rho_i=\rho_j\), and \(k=0\) attains that pole. Since an \(L\) factor is the reciprocal of a polynomial, other factors do not cancel it.

Consequently all real poles of \(L(1-s,\Pi_v^\vee\times\Pi_v)\) lie strictly above zero, whereas \(-r-2\sigma\leq0\). The epsilon monomial has no zero or pole at a finite \(s\). Hence gamma has a zero at \(-r-2\sigma\). The Weil-side unitary factor in A.1 permits a real zero only at zero. It follows that \(r=\sigma=0\), so all \(r_i=s_i=0\), giving induction from unitary supercuspidals as required. This explains the correction without claiming that the published theorem fails.

A separate locator correction: H00, A.2 cites J83 “Proposition 8.3” for its product of \(L\) factors. J83, 8.3, p. 448 is a convergence statement. Use the product results in 8.4 and 9.4 for this application.

## 4. Extending to all irreducibles

This section spells out the additional proof interfaces; it is not an identification of a roadmap with a completed proof.

### 4.1 Parameter decomposition and special quotients

Use the uncentered block \(S_m\), \(m\geq1\), with basis \(e_0,\ldots,e_{m-1}\),
\[
 r(w)e_j=\nu(w)^j e_j,\qquad
 Ne_j=e_{j+1}\ (j<m-1),\quad Ne_{m-1}=0.
\]
The kernel of \(N\) is the **top** weight \(\nu^{m-1}\). Every Frobenius-semisimple Weil-Deligne parameter decomposes uniquely, up to order, as
\[
  D=\bigoplus_i \sigma_i\otimes S_{m_i},
\]
with \(\sigma_i\) irreducible. This classification is recalled and used in [H02, 2.1-2.4, pp. 593-594](sources.md#h02), with the underlying Weil-Deligne formalism in [D73, 8.4-8.6](sources.md#d73) and [T79, 4.1](sources.md#t79). Its implementation requires the semisimple Weil decomposition and compatible Jordan chains, not just the existence of Jordan normal form for \(N\).

For a supercuspidal \(\rho\), put
\[
 \delta_m(\rho)=\text{the unique irreducible quotient of }
       \rho\times\nu\rho\times\cdots\times\nu^{m-1}\rho
\]
using the upper normalized induction fixed above. This is [H02, 2.6, p. 595](sources.md#h02). These are exactly the essentially square-integrable classes: [Ze80, 9.1-9.3, pp. 197-198](sources.md#ze80). Zelevinsky's earlier notation \(\langle\Delta\rangle\) in 3.1 denotes the other segment constituent, a submodule of the increasing induction; 9.1 uses the special constituent \(\langle\Delta\rangle^t\). Confusing them interchanges, for example, the one-dimensional and Steinberg constituents of a reducible principal series.

Ze80, Theorem 6.1, p. 188 gives the multisegment classification with its specified order and **submodule** convention. It must not be imported as though it were already the preceding special-quotient convention. Ze80, 9.3 states the converse square-integrability classification but explicitly omits its proof, attributing it to Bernstein. This is a real proof-source boundary, not a license to treat the converse as proved by the displayed forward argument.

The full map sends an indecomposable \(\sigma\otimes S_m\) to
\(\delta_m(\operatorname{rec}^{\,0}(\sigma))\). For a direct sum, form these essentially square-integrable blocks, order them by decreasing real exponents relative to unitary square-integrable blocks, and take the unique irreducible Langlands quotient. [H02, 2.7-2.9, pp. 595-596](sources.md#h02). Equal exponents cause no ambiguity in the isomorphism class. Exhaustion and uniqueness require the Langlands classification, not just finite length or unique supercuspidal support.

The earlier representation-theoretic inputs are [BZ77, Theorems 2.8-2.9, pp. 447-448, and 4.1-4.2, p. 454](sources.md#bz77): finite length of cuspidally induced representations, uniqueness of cuspidal support, and the irreducibility criterion for a product of cuspidals without adjacent norm twists. In particular, products of unitary supercuspidals satisfy that criterion. These statements support H00's local support calculation as well as the later classification.

For that classification H02 cites [Ca77, 2.2, pp. 684-685](sources.md#ca77), which states the result but explicitly says that a written proof of the \(p\)-adic version was not then available. J83, 9.5, p. 462 instead refers to [S78, Theorem 4.1, p. 99](sources.md#s78). The exact Silberger original has now been supplied, registered and read in full, including its proof in sections 5-7, pp. 99-104. The theorem gives the unique irreducible quotient for regular positive tempered Levi data, uniqueness of those data, and exhaustion. Its Jacquet-module and tempered-exponent prerequisites, multiplicity argument, and root/weight cone lemma are mapped in [the companion note](silberger.md). S78, p. 96 and [S79, 0.4-0.5, pp. 7-9](sources.md#s79) give the convention translation: \(\sigma_{-i\lambda}\) twists by \(q^{\langle\lambda,H_M\rangle}\), with \(\langle\chi,H_M(m)\rangle=\log_q|\chi(m)|\). For upper \(\mathrm{GL}_n\) parabolics this is the decreasing-\(|\det|\)-exponent quotient convention above. Equal exponents are grouped into a tempered Levi class before imposing regularity. The extra special/tempered block classification for \(\mathrm{GL}_n\) remains a separate prerequisite; Silberger's general reductive theorem alone does not supply it.

### 4.2 Factors for the extension

For irreducible Weil representations \(\sigma,\sigma'\), or their corresponding supercuspidals \(\rho,\rho'\), the matching indecomposable factors obey
\[
 L\bigl(s,(\sigma\otimes S_m)\otimes(\sigma'\otimes S_\ell)\bigr)
   =\prod_{j=1}^{\min(m,\ell)}
      L(s+m+\ell-1-j,\sigma\otimes\sigma'),
\]
\[
 L(s,\delta_m(\rho)\times\delta_\ell(\rho'))
   =\prod_{j=1}^{\min(m,\ell)}
      L(s+m+\ell-1-j,\rho\times\rho').
\]
The parameter formula comes from the monodromy blocks of \(S_m\otimes S_\ell\), not from the entire inertia-invariant space. On both sides gamma is
\[
 \prod_{i=0}^{m-1}\prod_{j=0}^{\ell-1}
       \gamma(s+i+j,\sigma\otimes\sigma',\psi)
\]
or the identical product with \(\rho\times\rho'\). See [H02, 2.4, 2.6-2.7](sources.md#h02); the original representation calculation is [J83, Theorem 8.2, pp. 444-445, and Theorem 3.1, pp. 404-405](sources.md#j83). The centered formulas in J83's introduction, notably equation (13), p. 371, agree after shifting each block by \(\nu^{(m-1)/2}\).

For arbitrary direct sums of parameter blocks, \(L,\epsilon,\gamma\) are multiplicative over block pairs. The representation counterpart is **Langlands-sum** multiplicativity, [J83, 9.4-9.5, pp. 458-463](sources.md#j83), including the definition for nongeneric quotients. This establishes equality of \(L\) and gamma from the supercuspidal equalities; epsilon then follows from its defining relation to gamma and \(L\), also using the dual formula. It does not assert that \(L\) is multiplicative over an arbitrary composition series of a parabolically induced representation.

The required dual formula is
\[
  \delta_m(\rho)^\vee
       \simeq\delta_m(\rho^\vee\nu^{1-m}),
 \qquad
  (\sigma\otimes S_m)^\vee
       \simeq(\sigma^\vee\nu^{1-m})\otimes S_m.
\]
[Ze80, 9.4](sources.md#ze80) supplies the special-representation dual. H02, 2.6, p. 595 prints the first formula with \(\rho\) rather than \(\rho^\vee\) on the right. The missing dual is visible in the original, and the rank-one case already detects it. The corrected formula is required for H02's following factor calculation.

Twisting passes through each block and the Langlands quotient. Central characters can be checked directly: if \(\dim\sigma=d\), both sides of a block have abelian character
\[
  (\det\sigma)^m\,\nu^{d\,m(m-1)/2}.
\]
Products of these characters handle direct sums. Duality, twists, the two pair factors, and rank are therefore separate extension lemmas with exact classification dependencies.

### 4.3 Compatibility map

| Required assertion | Supercuspidal source and construction | Additional full-correspondence obligation |
| --- | --- | --- |
| Rank and bijection | H00, 1.2-1.3, 2.8, 4.2-4.4; H88, Theorem 1.2 | Unique Weil-Deligne block decomposition, special classification, and unique exhaustive Langlands quotient; H02, 2.1-2.9. |
| Determinant equals central character | H00, 1.2(1), 2.2, 2.8, 3.8 | Determinant and central-character calculation of each block and its quotient, as above. |
| Arbitrary quasi-character twists | H00, 1.2(2), 3.8, 4.4; H93, section 4 | Twist induction, special quotients and Langlands data; H02, 2.3, 2.5-2.9. |
| Contragredients | H00, 1.2(3), 2.2, 2.8, 3.8 | Dual block formula, contragredient Langlands classification; Ze80, 9.4; H02, 2.6-2.9 with the correction above. |
| Pair \(L\) | H00, 1.2(4), 2.3-2.4, 2.8, 4.3 | Monodromy tensor-block calculation and JPSS special and Langlands-sum products. |
| Pair epsilon, every \(\psi\) | H00, 1.2(4), 1.3, 2.3, 2.8, 4.3-4.4 | JPSS gamma products plus both \(L\) formulas, duality, and the change-of-character determinant formula. |
| Pair gamma | Defined by epsilon and \(L\) in H00, 2.3 | Derived compatibility, with JPSS multiplicativity used in the extension. It is insufficient by itself to identify the monodromy. |
| Unramified normalization | H00, 2.2 uses unramified local correspondence in weak association; rank one uses local class field theory | Match the spherical Langlands quotient of unramified characters with the \(N=0\) parameter, using the same normalized induction and geometric Frobenius. Higher-rank supercuspidals are not spherical. |

H02, 1.8 gives the full characterization by \(L\) and epsilon factors; 1.9 and section 5 explain the limitation of gamma-only data. For example, the centered \(S_2\) and the direct sum \(\nu^{-1/2}\oplus\nu^{1/2}\) have the same underlying semisimple Weil representation but different \(N\) and different \(L\) factors. Their gamma factors, including pair tests, cannot supply the missing monodromy distinction. Thus a specification using only gamma equalities would weaken the intended full theorem.

## 5. Remaining boundaries and planning consequences

The reciprocity direction, absolute value, additive character, intrinsic self-dual measure, Deligne/Langlands half shift, monodromy sign, segment orientation, twists, and duals have explicit resolutions above. Two convention issues should remain visible:

- Tate, p. 17, in the scalar measure-ratio formula following 3.6.2, appears to give an exponent inconsistent with his conductor definition in 3.2.6, p. 13. If \(n(\psi)\) is the largest integer for which \(\psi\) is trivial on \(\varpi^{-n(\psi)}\mathcal O_F\), self-duality gives \(\operatorname{vol}_{dx_\psi}(\mathcal O_F)=q^{-n(\psi)/2}\) and consequently \(dx/dx_\psi=q^{n(\psi)/2}\operatorname{vol}_{dx}(\mathcal O_F)\). This audit uses the intrinsic Fourier definition and its derived scaling, rather than the suspect printed ratio. A future scalar conductor interface should prove this conversion explicitly.
- The complete change of conventions from arbitrary Shahidi local-coefficient implementations to the fixed JPSS factors is not resolved here. The source theorem includes a chosen measure normalization and central-character sign. Those choices must be instantiated if that implementation route is used; they do not leave the stated JPSS-normalized correspondence ambiguous.

The Silberger original-source reading obligation is now satisfied; its transitive Jacquet-module, exponent and cone-lemma inputs are recorded without claiming their complete proofs have also been audited. The supplied Ha99 resolves the general-coefficient proof-source lead for the split supercuspidal application of Ha98's Proposition 4.8, and B96 supplies the requested equivariant-resolution construction. Historical-version identities, a nonsplit extension of Ha99's displayed theorem, and the transitive cohomological foundations remain distinct issues, as recorded in [the companion](harris-1999.md). The omitted converse proof in Ze80, 9.3, the other transitive inputs to Harris's global existence theorem, and the corrected essential-vector argument remain proof-development boundaries even when the statements are available.

The shared DAG refinement retains the existing stable nodes and distinguishes:

1. actual local factors and their conventions, normalized induction, special blocks, and the free abelian groups used by H00;
2. global functional equations and ramified-twist isolation from the appendix's unitary local-component result;
3. gamma-to-\(L,\epsilon\) separation from the virtual pairing/isometry construction;
4. fixed-invariant finiteness and finite-witness choice independence from the numerical surjectivity theorem;
5. Weil-Deligne decomposition and the local classification from their subsequent use to extend the already constructed supercuspidal map;
6. pair-factor propagation for that extension from the construction of the map itself.

Classification of unitary generic local representations is needed **before** H00's supercuspidal construction finishes. The full correspondence extension occurs **after** it. Treating those as one node would obscure a dependency and can introduce a false cycle. Planning edges record expected proof requirements; a checked acyclic graph neither proves them nor makes them accepted Library results.

Worker 3 merged these refinements into the complete revision-6 pair, preserved unrelated nodes and edges, ran the supplied checker to a successful terminal result, and saved shared DAG revision **7**, content key `a452fea31ebacd28521978fd6f7c3bfe7769b669cf54342132594757ec793402`, manifest SHA-256 `d75067ecd42aa72918c3a4d8b87636a8b8f098a3786ea3e4794a8850984b785e`. This is a revision-specific planning receipt; later workers may refine it further.

The Harris correction was subsequently merged into the then-current revision-13 pair, preserving every definition, unrelated proof node, and existing edge. The checker again passed. Shared DAG revision **14**, content key `095e2fa56c7d75db4e0d70ca0f19c3a80398f94613c02127f3f4877fe7c574ba`, manifest SHA-256 `bd3eb6740a554ad9cff68843b503a6167c882620c8394ced244f2ab53c3575cc`, separates `proof.harris-global-galois-existence` from `proof.harris-supercuspidal-local-global` and makes the existing `proof.harris-global-input` depend on both. It recorded the then-unresolved general-coefficient proof source; the subsequent Ha99 reading resolves the application as described above.

After reading S78, Worker 3 merged its classification refinements into the then-current revision-16 pair, preserving every existing edge and all unrelated nodes. The checker passed. Shared DAG revision **17**, content key `1770eb213a39a3f7fff7d8b387dbcaff2799390da075ab6c70a193e39477b05d`, manifest SHA-256 `195d77a22ee0fad1481966d29fb1791a4226653acbe216b26be34509d16524de`, replaces the outdated missing-source reference and separates Jacquet exponents, Jacquet/tempered prerequisites, the cone lemma and the quotient theorem. These remain planning interfaces.

After reading Ha99, Worker 3 merged the coefficient-system refinements into the then-current revision-21 pair, preserving every existing edge and all unrelated nodes. The checker passed. Shared DAG revision **22**, content key `64d1045c945937e2f2d372bc76af2907f347b23007de01b188a87d379a81e93a`, manifest SHA-256 `fd75343d1dca1b399e6b5504bac139e834ac52b22bdb36ed054272e46e6ad385`, records the required split-place hypothesis and separates the coefficient-system spectral sequence from its Berkovich equivariant-resolution input. It recorded the then-pending Berkovich request, subsequently supplied and checked as above. This receipt establishes a planning update, not a cohomological or Lean proof.

After reading B96, Worker 3 updated only the two relevant source interfaces in the intact revision-22 pair, preserving every edge and all unrelated nodes. The checker passed. Shared DAG revision **23**, content key `d9182c9b599513f61a16aea0518ea483b10ecc85ca8f582fb91ec62a7ea64154`, manifest SHA-256 `8edf06529d80e93af43a232cadde450bffbd6ef6b3f4e2b79add9f909e94cab9`, replaces the pending acquisition lead with the registered PDF and precise construction/proof locations, retaining the historical-version distinction and transitive prerequisites.

Bibliographic discrepancies in H00 should not propagate to the register: JPSS 1983 ends on p. 464, J81 is volume **256**, and HH95 was published in **1995**. H84's retained filename says 1983 although the published volume is dated 1984. Source identity in this note is fixed by the registered bytes and locators, not by those filename or bibliography discrepancies.
