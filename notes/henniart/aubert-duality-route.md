# Aubert duality: corrected sources and the upstream classification boundary

Author: Worker 320.

The duality route to the segment classification needs both the formal
Grothendieck-group identities and preservation of irreducibility. These have
different proof dependencies. The original Aubert irreducibility argument
cannot be used as printed; the erratum needs the two-sided support correction
explained below. Even after that repair, the cited proof of one formal identity
uses Langlands classification. An upstream classification proof must supply an
independent replacement for that input.

This note extends the original-reading boundary in
[GL_n classification source boundaries](gln-classification-sources.md).
It records source checks and remaining formalization obligations, not a Lean
proof or a certificate that every transitive dependency is independent.
The retained [audit and citation guide][audit] supplied the correction map;
the relevant original passages were then checked as specified below.

## The operator and its sign

Aubert works with the Grothendieck group of smooth finite-length
representations. For standard Levi subgroups indexed by subsets of the simple
roots, Definition 1.5, printed p.2181, defines

    D_G = sum_{I subset S} (-1)^|I| i_I r_I.

Here induction and Jacquet restriction are normalized. Theorem 1.7 gives
involutivity, commutation with induction and contragredients, and compatibility
with Jacquet restriction after changing the Levi by the specified longest
Weyl element. These identities precede the defective Proposition 3.2 and do not
use its module-complex argument. They still have the separate dependency
discussed below.

The sign-adjusted GL operator in Definition 2.1, printed p.2184, multiplies
`D_G` by `(-1)^|I|` on a cuspidal-support component. For a segment of length
`k` and total rank `n`, Remark 2.2 gives `|I| = n - k`. Thus the unadjusted
alternating sum and the involution that takes actual irreducibles to actual
irreducibles must not be identified without the support-dependent sign.

Theorem 2.3, p.2185, identifies the adjusted operator with Zelevinsky's
involution. Its proof uses the polynomial-ring structure from Ze80 Corollary
7.5, the segment Jacquet calculation from Proposition 3.4, the expansion from
Proposition 9.13, and alternating-subset cancellation. It exchanges the
irreducible submodule of the increasing segment product with its special
quotient. The claim that the segment generators themselves are an additive
basis is not needed: their monomials form the additive basis.

Two corrections from the retained audit matter here. On p.2184 the tensor
product of the two Grothendieck groups is the group for the product Levi;
parabolic induction maps it into the group for the larger GL group. It is not
an identification with that larger group's Grothendieck group. The induction
compatibility used there is Theorem 1.7(2), not 1.7(1).

## What the irreducibility repair establishes

The [1996 erratum][erratum], p.4687, withdraws the proof of Proposition 3.2
and says the proposition itself was not known to be true. The original proof
of Theorem 3.6, p.2188, repeatedly uses it. The failure of a step in that proof
does not disprove Proposition 3.2.

The replacement proof filters a Jacquet module of the duality complex by
Bruhat support and reduces its associated graded pieces to Koszul complexes.
The retained audit identifies a circularity in the printed erratum: the
geometric-lemma calculation assumes that `w` is a minimal representative of
`W_J w W_I`, while the support condition supplied at that point only gives
left-coset minimality. The subsequent use of that calculation to infer
right-coset minimality cannot justify the initial assumption.

[Ban–Jantzen 2016][bj], §4, pp.161–162, repairs this by taking the largest
subset of each support set invariant under both left `W_J` and right `W_I`.
In the audit's notation it is

    theta^{J,I} = {x in theta : W_J x W_I subset theta}.

When `theta_i \ theta_(i+1) = {w}` and the graded piece is nonzero,
the entire double coset lies in `theta_i` and its other elements lie in
`theta_(i+1)`. The length filtration now establishes double-coset minimality
before the geometric lemma is applied. The cuspidal-support hypothesis then
gives `w W_I w^-1 subset W_J`. On p.162 the transition maps are checked to be
the identity up to the exterior-algebra signs, producing the needed Koszul
complex.

Keep the terminal homology. The p.160 sentence calling the entire displayed
complex ending in zero exact cannot be used literally: it would kill the
duality class. The required assertion is exactness before the terminal
homology, or the corresponding truncation without a final zero. The p.161
parenthetical also needs the comparison between consecutive modified support
sets, `theta_i' != theta_(i+1)'`, rather than the printed comparison with
`theta_i`. Both corrections are explained in the retained audit.

This repairs the relevant complex argument, subject to its other inputs.
Corollary 3.9 additionally applies the construction to a finite-length induced
representation. The finite-length extension needs termwise exactness and
induction on composition length. The length comparison then shows that the
nonzero images of its irreducible constituents each have length one. Neither
this extension nor the input functor exactness is supplied merely by naming
the corrected source.

## A separate independence issue

Ban–Jantzen Proposition 4.1(3), p.158, establishes invariance of induced
Grothendieck classes under Weyl conjugacy of Levi subgroups. Its proof
explicitly invokes linear independence of characters, **Langlands
classification**, and the geometric lemma. Theorem 4.2 uses Proposition
4.1(1)–(3) for the formal duality identities. Aubert's corresponding identity
(1.2), p.2181, cites Bernstein–Deligne–Kazhdan Lemma 5.4(iii), and is explicitly
used on p.2182.

Consequently, reading the corrected complex is insufficient to certify the
entire route as an independent input to the present upstream classification
task. This is a source-dependency finding, not evidence of an already formed
Lean dependency cycle. The actual transitive proof dependencies must be
checked, and any prohibited classification input replaced.

There is a concrete GL-specific alternative to investigate. Ze80 Theorem 1.9,
p.174, proves commutativity of the induction-product Grothendieck ring.
Its proof uses the transpose-inverse automorphism conjugated by the specified
antidiagonal matrix. Pullback by that automorphism reverses the induction
factors. Its effect on irreducible constituents agrees with the smooth
contragredient by the cited Gelfand–Kazhdan result. Compatibility of normalized
induction with contragredients, cited there as 1.1(d), then proves equality
of composition-factor multiplicities.

This passage provides a distinct proof route, rather than a request to assume
commutativity. Gelfand–Kazhdan and the relevant smooth-dual results remain
original-source and formal proof obligations here. One must also pass from
composition multiplicities to the actual exact Grothendieck group and derive
the needed arbitrary block permutations and Levi-conjugacy comparison.
Equality of Grothendieck classes does not assert that the two induced
representations are isomorphic.

## Schneider–Stuhler as an alternative

[Schneider–Stuhler 1997][ss], Theorem III.3.1 and Corollary III.3.2,
p.132, give a different route to irreducible preservation. Write `E^i` for
their Ext functors and `E(V) = E^(d - |Theta|)(V)` on objects of support type
`Theta`. Concentration and biduality yield an exact contravariant equivalence

    E : Alg^fl_(chi,Theta)(G) -> Alg^fl_(chi^-1,Theta)(G).

Applying it twice gives back the original object. In particular, it preserves
irreducibility, but it inverts the central character; it is not an
endofunctor of a single fixed-`chi` category in general.

The Grothendieck-group operator in IV.5, p.183, also uses the smooth
contragredient. Writing `V^vee` for that smooth dual, the source defines

    iota([V]) = sum_{i >= 0} (-1)^i [E^i(V^vee)]
             = (-1)^(d - |Theta|) [E(V^vee)]

for `V` of support type `Theta`. The first expression defines an endomorphism
of `R_Z(G; chi)`: the smooth dual changes `chi` to `chi^-1`, and Ext duality
changes it back. Propositions IV.5.1–5.2, pp.183–184, concern this operator.
Its preservation of irreducible classes up to sign uses irreducible
preservation by the smooth contragredient together with Corollary III.3.2.
The alternating induction–Jacquet formula is the formula for `iota`,
not for the signed class of `E(V)` alone.

This is an alternative to the defective Aubert module proof, not a completed
audit of the entire building-theoretic argument. Theorem III.3.1 uses
Proposition III.2.1 and Theorem III.2.2. The former cites Casselman 6.3.7 and
6.3.11; the latter is established later as IV.4.18. Those proofs and their
transitive independence have not all been checked here.

Their induction convention on pp.130–131 uses left translations, and the
modulus convention and the sign `(-1)^(d - |Theta|)` in IV.5 must be translated
explicitly. The project uses upper block parabolics, positive half-modulus
covariance, and right translation. Opposite-parabolic and block-reversal
comparisons are mathematical inputs, not silent notation changes.

## Consequences for the Lean work

The first construction must be the exact Grothendieck group of actual smooth
finite-length representations, using actual short exact sequences. The
existing finite-dimensional virtual-representation construction is not that
category. A free abelian group on irreducible labels cannot substitute for it
without the Jordan–Holder identification.

Subsequent units must supply the actual induction and Jacquet maps on this
group, including exactness, finite-length preservation and universe
comparisons; the alternating operator and its formal identities; an
independently justified irreducible-image theorem; and the segment
socle-to-special-quotient and reversed-Levi formulas. Definitions must be
published before statement units, and statement targets before their exact
proofs. None of these obligations is discharged by this note.

The analytic classification also still requires Casselman's strict
square-integrability criterion, admissibility, character normalization and
real-twist bridges. In the Auel route, retain the rank weights in exponent
vectors and apply the final contradiction to the dual representation, as
explained in the companion source note. Ordinary contragredience alone does
not exchange the segment socle and special quotient.

## Retained copies and reading extent

Links below are to retained project-accessible local sources, not claims of
public availability. PDF page numbers in this paragraph are one-based.
Source registration records identity and access, not mathematical acceptance.

| Source | Registered ID and SHA-256 | Passages checked for this note |
| --- | --- | --- |
| [Aubert 1995][aubert] | `aubert-1995-duality`; `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Printed pp.2179–2185 and 2187–2189; p.2185 visually checked. |
| [Aubert 1996][erratum] | `aubert-1996-duality-erratum`; `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f` | Printed pp.4687–4688 directly read; the diagnosis on p.4689 follows the retained audit. No complete original-erratum reading is claimed. |
| [Ban–Jantzen 2016][bj] | `ban-jantzen-2016-duality`; `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | §4, printed pp.158–163, PDF pp.6–11; p.161 visually checked. |
| [Schneider–Stuhler 1997][ss] | `schneider-stuhler-1997-building`; `bf8b6a61a3bc11ae1f00e6d14fc48221fbc5efbfb41e8e7e69b2efd88564b5c6` | Printed pp.129–133 and 183–184, PDF pp.34–38 and 88–89; pp.132, 183 and 184 visually checked, including the inverse central character and smooth-dual marks in III.3 and IV.5. |
| [Zelevinsky 1980][ze80] | `zelevinsky-1980-induced-ii`; `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac` | Theorem 1.9, printed p.174, PDF p.11, text and image; surrounding pp.173–175 read. Other reading extents are in the companion source note. |
| [Retained audit][audit] | `aubert-duality-audit-2026-08-13`; `a1b7f421c6e2f0096dfd15f681448c6b8668a205d3e959d36b49b37c8d1082e1` | Complete secondary guide dated 2026-08-13; attribution for the correction map and the erratum circularity diagnosis. |

[aubert]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995.pdf>
[erratum]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Erratum a Dualite dans le groupe de Grothendieck des representations lisses--1996.pdf>
[bj]: </home/taskhub/central-library/Ban-Jantzen--The Langlands quotient theorem for finite central extensions of p-adic groups II--2016.pdf>
[ss]: </home/taskhub/central-library/Schneider-Stuhler--Representation theory and sheaves on the Bruhat-Tits building--1997.pdf>
[ze80]: </home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf>
[audit]: </home/taskhub/central-library/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995/Aubert--Dualite dans le groupe de Grothendieck des representations lisses de longueur finie--1995--audit-and-citation-guide.md>
