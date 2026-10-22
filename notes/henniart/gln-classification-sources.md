# GL_n classification: Auel's converse and Jacquet's unitary induction theorem

Author: Worker 47. This source note supports the GL_n classification branch
and complements [the Henniart audit](audit.md). It records what two supplied
originals establish, the conventions needed to use them, and the dependencies
they leave open. It is neither a Lean theorem nor a classification proof.

Ze80 §9.3 states the classification of irreducible essentially
square-integrable GL_n representations by special segments and explicitly
omits Bernstein's converse proof. Au04 supplies a written route in
Theorem 6.1 and pp.18-22 using later duality theory. Ja77 Theorem 3.2
and Corollary 3.3 prove irreducibility and genericity of certain unitary
inductions. They do not supply tempered exhaustion or uniqueness.

Here F is a nonarchimedean local field, nu(g) = |det(g)|_F, and
|varpi|_F = q^(-1). For a cuspidal rho and positive m,
Delta = [rho, nu^(m-1)rho]. The project uses the upper block parabolic,
right translation, and covariance by delta_P^(1/2). In this convention
Z(Delta) is the unique irreducible subrepresentation of the increasing
product, while delta(Delta) is its unique irreducible quotient (Ze80
§§3.1 and 9.1). Their existence and uniqueness are theorem obligations.
They are not interchangeable definitions of a chosen constituent.

## Auel's written route and its conventions

Au04 Theorem 6.1, p.18, states the equivalence between irreducible
quasi-square-integrable representations and special constituents. The
memoir uses upper normalized induction with right translation in §4.6,
p.11; Definition 3.1 and Example 3.3, pp.6-7, fix the modulus. Its
`<Delta>` is Z(Delta), the submodule of the increasing product (§5.1,
p.15). Its `D<Delta>` is delta(Delta), the quotient of that product
(§5.3, p.17). Example 5.11 sends the centered trivial-character segment's
Z constituent to Steinberg under D.

The notation `Irr^u` means irreducibles with unitary central character,
not the predicate of unitarizability: see Definition 4.7, p.9. Definitions 4.14
and 4.16, p.10, distinguish square integrability modulo the center from
quasi-square-integrability. Proposition 4.17 then proves unitarizability
for an irreducible square-integrable representation. No general inference
from a unitary central character to unitarizability is available.

The route of §6, pp.18-22, is:

1. Reduce by real norm twists to unitary central character and centered
   segments (Lemma 4.15, Proposition 5.5, and Theorem 5.13).
2. Use the normalized Jacquet calculation for a special block, equation
   (8), and Casselman's strict square-integrability criterion (Theorem 6.8,
   p.19, citing Casselman Theorem 6.5.1) to establish the special direction.
3. Transfer the criterion across the involution D, obtaining Theorem 6.14,
   pp.20-21. On the upper contracting cone it changes the strict bound
   from `|chi(t)| < 1` for pi to `|chi(t)| > 1` for D pi, using the
   opposite/reversed Levi formula in Theorem 5.13(d).
4. Apply the Z multisegment classification (Theorems 5.8 and 5.10,
   pp.16-17). For two or more segments, Proposition 6.18, p.22, orders
   segment exponent means decreasingly while preserving nonprecedence.
   The obvious minimal-cuspidal-support Jacquet exponent from §5.9 has
   zero total weight. Its first segment has nonnegative total weight.
   Lemma 6.16, p.21, therefore gives a contracting element with
   `|chi(t)| <= 1`, contradicting the criterion for D pi to be square
   integrable. Involutivity and irreducible preservation yield the converse.

In the combinatorial criterion (Definition 6.11 and Theorem 6.12, p.20),
if the i-th cuspidal factor has rank n_i and real exponent s_i, then
`p_i = n_i*s_i`, not s_i. For a central Levi element with scalar blocks t_i,

    -log_q |chi(t)| = sum_i p_i*v_F(t_i).

The cone is `v_F(t_1) >= ... >= v_F(t_r)`, with nonconstant valuation
sequences after removing the center times the compact torus
(Definition 6.6 and Example 6.7, p.19). A unitary central character gives
`sum_i p_i = 0`. The reduction to Levis associated to minimal cuspidal
support is Remark 6.9; it uses cuspidal support, the geometric/Jacquet
results and transitivity, not a definition of temperedness.

Theorem 5.13, pp.17-18, supplies the essential later duality input:
involutivity, commutation with induction, the reversed-Levi Jacquet formula,
fixing cuspidals, preservation of irreducibles, and preservation of central
characters. Its proof cites Aubert 1995 Theorems 1.7, 2.3 and Corollary 3.9
(with the 1996 erratum in the bibliography), Schneider--Stuhler 1997
III.3.1 and IV.5, and Ze80 §9.12. These are the memoir's explicit
upstream citations; the Aubert and Schneider--Stuhler originals have not
been read in this branch. This is a retained dependency boundary, not a
claim that the memoir proves those inputs or that Ze80 §9.17 proves the
duality conjecture. Casselman's cited full criterion is likewise a
separate original-source and proof dependency.

## Corrections needed when using the memoir

The following were checked against the page images and the argument.

* Theorem 5.12, p.17, calls the single-segment classes an additive basis
  of R. The cited original, Ze80 Corollary 7.5, p.193 (PDF p.30), says
  that R is a polynomial ring over Z on those classes. Products of
  segment classes are the additive basis. Extend D as an algebra
  homomorphism using the latter assertion; do not adopt the printed
  additive-basis assertion.
* The reference to Ze80 "§8.9.3" preceding Theorem 6.1, p.18, means §9.3.
* Example 6.13, p.20, prints the centered exponent vector without the
  common positive cuspidal-rank factor m. Definition 6.11 gives the
  vector `m*((k-1)/2, ..., -(k-1)/2)`. This factor does not change the
  inequalities but must be retained in numerical statements.
* The proof of Theorem 6.12 prints `T^+` where the preceding criterion
  uses `T^=`. Its nonconstant valuation-sequence formulation and
  Theorems 6.8/6.14 determine the excluded set.
* The last sentence on p.22 says that pi is not square integrable.
  The argument establishes that **D pi** is not square integrable:
  Theorem 6.15 violates the dual criterion 6.14. This is a correction
  inferred from the explicit preceding argument, not a separate theorem
  asserted for all multi-segment Z representations.

These corrections concern the cited route; reading the memoir in full
does not certify every auxiliary assertion in its introductory survey.

## What Jacquet's article establishes

The complete Ja77 article, printed pp.91-101 (one-based PDF pp.97-107), was read; Theorem 3.2 and Corollary 3.3 were also checked visually. Access to this article does not resolve the whole tempered classification proof-source obligation.

Ja77 §0, p.91, restricts throughout to unitary Hilbert representations
and Mackey induction. Its "generic" means that restriction to the mirabolic
group is a multiple of its distinguished irreducible induced representation
T_r. Lemma 3.1, pp.96-97, proves that an irreducible generic representation
restricts to exactly T_r, using Whittaker multiplicity one. Theorem 2.1(3),
pp.95-96, establishes genericity for square-integrable representations.
Theorem 3.2, pp.98-99, then proves that a product induced from irreducible
unitary generic factors is irreducible and generic; Corollary 3.3, p.99,
specializes to square-integrable factors.

The unitary hypothesis from §0 must not disappear when quoting Theorem 3.2.
The parabolic on p.98 is explicitly the transpose of a standard parabolic.
To use it for the upper normalized smooth induction here requires the
actual comparison between Mackey unitary induction and smooth normalized
induction, together with conjugation/block reversal for the opposite
parabolic. That comparison is not an axiom or an implicit change of
normalization.

Ja77 Theorem 2.2, p.96, states multiplicity freeness without proving it
there. Lemma 3.1 uses the Gelfand--Kazhdan and Shalika uniqueness results
listed in its references. The discussion after Corollary 3.3, pp.99-100,
distinguishes mirabolic genericity from "weakly generic" (a nonzero
Whittaker functional); their equivalence is described as likely, not
proved. Theorem 3.4 gives a necessary genericity condition on the factors
and refers to a Bruhat argument (Rodier for the p-adic case).

There is no assertion or proof of tempered exhaustion or unordered
uniqueness in this article, despite the title of §3 and Ro82's citation.
Thus the exact general tempered-support/exhaustion input and its
specialization with uniqueness to GL_n remain explicit source/proof
obligations. The assertions read in Ro82 and JS83 remain valid
statement sources; Ja77 should support only the directions it actually
establishes. This is a source-coverage finding, not a claim that tempered
classification is unknown.

## Consequences for the formalization

The eventual statement family must distinguish the special quotient from
the Z submodule, a unitary central character from an invariant positive
Hermitian form, and the unitary induction theorem from tempered exhaustion.
The rank-weighted exponents and opposite-Levi comparison belong explicitly
in the supporting definitions and theorem dependencies.

No classification proof has been formalized by this source reading.
The present branch's constituent relation definitions and their proposed
compatibility statements do not provide segment existence, the duality
involution, Casselman's criterion, tempered exhaustion, or any full local
Langlands correspondence. Those remain separate mathematical and Lean
obligations. A bibliographic reference in Au04 is not evidence that the
referenced original was read or formalized.

## Retained originals and reading extent

The local links below identify the unchanged retained originals. They
require access to this project's literature collection or Central-Library;
they are not claims of public internet availability. All PDF page numbers
are one-based. Registered IDs and file hashes identify the exact source
copies, not mathematical acceptance.

### Au04

Asher N. Auel, Une demonstration d'un theoreme de Bernstein sur les representations de quasi-carre-integrable de GL_n(F) ou F est un corps local non archimedien, DEA memoir, Universite Paris-Sud XI Orsay, July 2004, advisor Guy Henniart.

- [Retained original](<C:/CS projects/Math-Tomorrow/Auto-lean-test-2/literature/Auel (2004), proof of Bernstein's quasi-square-integrable GL_n classification.pdf>)
- Literature ID: `provided-dd2424348af1ddf73426a58cb44a42985d610bade9fb26dd0da2739fbc2494d1`
- File SHA-256: `3a6bcabbd0fa06a16e530cd3e7381c42742e3f1e4545316e2bf047e62afb1e65`

Read the complete memoir, pp.1-24 (PDF pages 1-24). Visually checked pp.8-10 and 17-22, including the convention and correction locations above.

### Ja77

Herve Jacquet, Generic representations, in J. Carmona and M. Vergne (eds.), Non-Commutative Harmonic Analysis, Lecture Notes in Mathematics 587, Springer (1977), pp.91-101.

- [Retained original](<C:/CS projects/Math-Tomorrow/Auto-lean-test-2/literature/Jacquet (1977), Generic representations, LNM 587.pdf>)
- Literature ID: `provided-7fa6dd7a9bc39b0ef92f41d27dd4970725cdfbe795124370c63ffe3d8743b116`
- File SHA-256: `073cdfbdac1db264653544249d1060ba47704cc1678a5f545b9cd0ca5df46c8a`

Read the complete article, printed pp.91-101 (PDF pp.97-107), in the retained 249-page volume. Visually checked pp.98-99. The rest of the volume was not read.

### Ze80

A. V. Zelevinsky, Induced representations of reductive p-adic groups II. On irreducible representations of GL(n), Ann. Sci. ENS (4) 13 (1980), pp.165-210.

- [Retained original](<C:/Central-Library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf>)
- Literature ID: `zelevinsky-1980-induced-ii`
- File SHA-256: `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`

Read the segment/classification sections 3, 6 and 9 and relevant sections 4, 7 and 8. Rechecked Corollary 7.5, p.193 (PDF p.30), for the polynomial-ring correction. Sections 3.1, 9.1 and 9.3 are on pp.180-181, 197 and 198; PDF page = printed page minus 163. No full-paper reading is claimed.

### Ro82

F. Rodier, Representations de GL(n,k) ou k est un corps p-adique, Seminaire Bourbaki, expose 587 (1982), Asterisque 92-93, pp.201-218.

- [Retained original](<C:/Central-Library/Rodier--Representations de GL(n,k) ou k est un corps p-adique--1982.pdf>)
- Literature ID: `rodier-1982-gln`
- File SHA-256: `389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`

Read sections 3.4 and 4.1-4.4. Section 4.3, Proposition 12, p.212 (PDF p.13), states tempered exhaustion and cites reference [19], Ja77 section 3. This citation does not mean that the cited article proves exhaustion.

### JS83

H. Jacquet and J. A. Shalika, The Whittaker models of induced representations, Pacific J. Math. 109 (1983), pp.107-120.

- [Retained original](<C:/Central-Library/Jacquet-Shalika--The Whittaker models of induced representations--1983.pdf>)
- Literature ID: `jacquet-shalika-1983-whittaker`
- File SHA-256: `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`

Read sections 1.1-1.3, pp.107-110 (PDF pp.2-5). Page 109 explains the unitary-mirabolic irreducibility input and invokes tempered classification for exhaustion; it sketches the square-integrable converse rather than replacing the complete later proof reading.

