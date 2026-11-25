# Milne 16.27 and 16.29: sections of trigonalizable groups need smoothness

This note (18 November 2026, revised 19 November 2026) gives two paper counterexamples, over any algebraically closed
field \(k\) of characteristic \(p>0\):

- one to part (a) of Milne's Theorem 16.27, conjugacy of sections;
- one to part (b), the description of maximal diagonalizable subgroups.

The second example has a smooth diagonalizable quotient, so it also
contradicts the maximal-subgroup sentence of Summary 16.29.

The note locates the step of Milne's proof that fails. It then records what
SGA 3, Exp. XVII, 5.1.1 ii) does prove, and the smoothness hypothesis under
which both parts of 16.27 hold.

The group of the first example is Raynaud's. SGA 3, Exp. XVII, §5.9(d),
final paragraph, takes the same \(\alpha_p\rtimes\mu_p\) over an algebraically
closed field. It shows \(H^1(\mu_p,\alpha_p)\neq0\) from the Frobenius
sequence and concludes that two liftings of \(\mu_p\) need not be conjugate
(§3, §5). This note adds a coordinate proof with explicit sections and a
strengthening: the sections are not conjugate even fppf-locally. The second
example, a maximal diagonalizable subgroup with smooth quotient, and Lemma A
are derived here; the sources read for this note do not contain them.
Lemma B is the case \(G_u=\alpha_p\) of the opening of Milne's proof of
16.27(b).

This is a mathematical note. It is not a
Lean construction and not a formal disproof. It concerns the published
Library statement
`Langlands.GroupScheme.TrigonalizableSectionConjugacyStatement`, which encodes
16.27 with no smoothness hypothesis (§7).

## 1. The source statements

Milne 2017, Theorem 16.27, printed p.333 (one-based PDF p.349), reads:

> Let G be a trigonalizable algebraic group over an algebraically closed
> field k, and let q: G → D be the quotient of G by G_u.
> (a) Let s1, s2: D → G be sections of q (as a homomorphism of algebraic
> groups). Then there exists a u ∈ G_u(k) such that s2 = inn(u) ∘ s1.
> (b) The maximal diagonalizable subgroups of G are those of the form s(D)
> with s a section of q; any two are conjugate by an element of G_u(k).

The proof of (a) inducts on the normal series of Theorem 16.21. Its last
step is "As H¹(D, N) = 0 (see 15.3), there exists a u ∈ N(k) …".
Proposition 15.3, printed p.303 (PDF p.319), assumes smoothness on both sides:

> Let G be a diagonalizable group variety over an algebraically closed field
> k and M a commutative unipotent group variety on which it acts. Then every
> crossed homomorphism f: G → M is principal.

The proof of (b) applies "Theorem 16.26" to \(G'=q^{-1}(q(S))\) to obtain
\(u\in G_u(k)\) with \(S=\operatorname{inn}(u)\,s'(q(S))\). That is a
conjugacy of sections, so the step uses part (a) for \(G'\), not the
existence result 16.26.

Summary 16.29, printed p.334 (PDF p.350), cites SGA 3, XVII, 5.2.3 and 5.3.1.
It assumes "D a smooth group of multiplicative type" and concludes, in
case (b) "k is algebraically closed", that:

> any two sections s1, s2: D → G of q as a homomorphism of algebraic groups
> are conjugate by an element of G_u(k); the maximal subgroups of
> multiplicative type in G are those of the form s(D) with s a section of q

The 2022 corrected reprint makes the same assertions. It places 15.3 on
printed p.303 (PDF p.314) and 16.29 on printed p.334 (PDF p.345). 16.27
starts on printed p.333 (PDF p.344), and its proof continues on printed
p.334 (PDF p.345).

- The statement of Proposition 15.3 is unchanged. In its proof, the 2022
  text replaces the descending chain \(M(n)\supseteq M(n+1)\) indexed by
  consecutive integers with a chain \(M(n_i)\supseteq M(n_{i+1})\) indexed
  by divisibility, \(n_i\mid n_{i+1}\).
- The mathematical statement and argument of Theorem 16.27 are the same. The
  only change seen is punctuation: the 2022 text adds a comma after
  "\(q\colon G\to D\)" in the opening sentence of the proof of (b).
- In Summary 16.29, the hypotheses, case (b), and the conjugacy and
  maximal-subgroup conclusions are unchanged. The one wording change seen is
  in case (a), where "a section as a map of schemes" becomes "a section as a
  morphism of schemes".

Neither the 2017 nor the 2022 official errata snapshot has an entry for
printed pp.303, 332, 333 or 334.

## 2. Conventions for the examples

Let \(H\subseteq\mathbb G_m\) be a closed subgroup, that is \(\mu_n\) or
\(\mathbb G_m\). Let \(H\) act on \(\mathbb G_a\) by multiplication,
\(t\cdot x=tx\). This action preserves \(\alpha_p\), since
\((tx)^p=t^px^p\).

On every \(k\)-algebra \(R\), the semidirect product
\(\alpha_p\rtimes H\) has the points \((x,t)\) with \(x\in R\), \(x^p=0\) and
\(t\in H(R)\). The group law is
\[
 (x_1,t_1)(x_2,t_2)=(x_1+t_1x_2,\;t_1t_2).
\]
As a scheme it is \(\alpha_p\times H\), so it is affine and of finite type.

Let \(q\) be the projection to \(H\). Then \(q\) is flat, surjective and of
finite presentation, and its kernel is \(U=\alpha_p\). The subgroup \(U\) is
closed, normal and unipotent (Corollary 14.7, printed p.282: subgroups of the
unipotent group \(\mathbb G_a\) are unipotent). \(H\) is diagonalizable, so
\(\alpha_p\rtimes H\) is trigonalizable with \(G_u=\alpha_p\)
(Proposition 16.2(d), printed pp.324–325).

A homomorphic section of \(q\) over a closed subgroup \(H'\subseteq H\) has
the form \(t\mapsto(F(t),t)\). Here \(F:H'\to\alpha_p\) is a crossed
homomorphism, \(F(t_1t_2)=F(t_1)+t_1F(t_2)\). For a point \(u\) of
\(\alpha_p\),
\[
 (u,1)(F(t),t)(-u,1)=(F(t)+u(1-t),\;t). \tag{1}
\]

**Lemma A.** Let \(H'\) be \(\mu_n\) with \(n\ge 2\), or \(\mathbb G_m\).
Every crossed homomorphism \(F:H'\to\mathbb G_a\) for this action has the form
\(F(t)=a(1-t)\) with \(a\in k\). Such an \(F\) lands in \(\alpha_p\) if and
only if \(a=0\), or \(H'=\mu_n\) with \(n\mid p\).

*Proof.* Write \(F=\sum_i a_it^i\) in \(k[H']=k[\mathbb Z/n]\), or
\(k[\mathbb Z]\). Compare the coefficients of \(s^it^j\) in
\(F(st)=F(s)+sF(t)\):

- the left side contributes \(a_i\) when \(i=j\);
- the right side contributes \(a_i\) when \(j=0\), and \(a_j\) when \(i=1\).

The pair \((1,0)\) gives \(a_0+a_1=0\). The pairs \((i,0)\) with
\(i\ne0,1\) give \(a_i=0\). So \(F=a_0(1-t)\).

Then \(F^p=a_0^p(1-t^p)\). The elements \(t^i\) are a basis of the group
algebra, so \(F^p=0\) if and only if \(a_0=0\) or \(t^p=1\) in \(k[H']\). The
second case means \(H'=\mu_n\) with \(n\mid p\). ∎

**Lemma B.** A closed diagonalizable subgroup \(S'\) of
\(\alpha_p\rtimes H\) meets \(\alpha_p\) trivially, so \(q|_{S'}\) is a closed
immersion.

This is the case \(G_u=\alpha_p\) of the opening of Milne's proof of
16.27(b) (printed p.333, PDF p.349; 2022 reprint printed p.334, PDF p.345).
There a diagonalizable subgroup \(S\) meets \(G_u\) trivially (14.17), so
\(q\) induces an isomorphism of \(S\) onto \(q(S)\). The proof below spells
out that specialization.

*Proof.* \(S'\cap\alpha_p\) is diagonalizable (Theorem 12.9, printed p.233)
and unipotent (14.7). It is therefore trivial by Corollary 14.17, printed
p.284. A homomorphism of algebraic groups with trivial kernel is a
monomorphism, hence a closed immersion (Proposition 5.31 and Theorem 5.34,
printed pp.106–107). ∎

## 3. Counterexample to 16.27(a)

This group is Raynaud's example in SGA 3, Exp. XVII, §5.9(d), final
paragraph (printed p.358, PDF p.34, original p.601), with \(\mu_p\) acting on
\(\alpha_p\) by homotheties. Raynaud uses the exact sequence
\(0\to\alpha_p\to\mathbb G_a\xrightarrow{x\mapsto x^p}\mathbb G_a\to0\). In
it, \(\mu_p\) acts by homotheties on the middle \(\mathbb G_a\), as in §2,
and trivially on the right-hand \(\mathbb G_a\). The Frobenius map is
equivariant for these actions, since \((tx)^p=t^px^p=x^p\) for
\(t\in\mu_p\).

Raynaud cites "App. I, prop. 11". In the recomposed edition this is
Proposition A.1.1 of Appendix I of Exp. XVII (printed pp.366–367, PDF
pp.42–43), on Hochschild cohomology. Its part a), the usual long exact
sequence, assumes a scheme section of the quotient map. Frobenius
\(x\mapsto x^p\) has none: a section would be a polynomial \(f\) with
\(f(y)^p=y\) in \(k[y]\). Its part b) assumes only that the quotient map is
surjective on \(k\)-points. Here that map is \(a\mapsto a^p\) on \(k\), which
is surjective because \(k\) is algebraically closed. So A.1.1 b) gives the
low-degree exact sequence
\[
 0\to\alpha_p^{\mu_p}(k)\to\mathbb G_a^{\mu_p}(k)\to\mathbb G_a^{\mu_p}(k)
 \to H^1(\mu_p,\alpha_p)\to H^1(\mu_p,\mathbb G_a)\to H^1(\mu_p,\mathbb G_a),
\]
with the homothety action on the middle \(\mathbb G_a\) and the trivial
action on the right-hand one. The middle \(\mathbb G_a\) has no nonzero
invariants: \(a(t-1)=0\) in \(k[t]/(t^p-1)\) forces \(a=0\). The right-hand
\(\mathbb G_a\), with the trivial action, has all of \(k\) as invariants.
This gives Raynaud's exact sequence
\[
 0\to\mathbb G_a(k)\to H^1(\mu_p,\alpha_p)\to H^1(\mu_p,\mathbb G_a),
\]
where the last term is the cohomology of the middle \(\mathbb G_a\), with
homotheties. The connecting injection \(k\hookrightarrow H^1(\mu_p,\alpha_p)\)
already gives \(H^1(\mu_p,\alpha_p)\neq0\). Raynaud also notes that the last
term vanishes, citing SGA 3, Exp. I, 5.3.3, so this injection is a
bijection. So two liftings of \(\mu_p\) in \(G\) need not be conjugate.

The coordinate arguments below do not use this cohomology. They write the
liftings down and check the failure directly, also after any extension of
scalars.

Take \(G=\alpha_p\rtimes\mu_p\) and \(D=\mu_p=D(\mathbb Z/p)\). For each
\(c\in k\), put
\[
 s_c(t)=(c(1-t),\,t).
\]
By Lemma A this is a homomorphic section of \(q\). Directly:
\(c(1-t_1)+t_1c(1-t_2)=c(1-t_1t_2)\), and
\((c(1-t))^p=c^p(1-t^p)=0\) on \(\mu_p\).

\(G_u(k)=\alpha_p(k)=\{0\}\), so \(\operatorname{inn}(u)\) is the identity
for every \(u\in G_u(k)\). Part (a) would force \(s_c=s_0\). For \(c\ne0\),
the two sections differ on the universal point \(t\) of
\(\mu_p\) over \(k[t]/(t^p-1)\).

The failure is not only a lack of rational points. Let \(R\neq0\) be a
\(k\)-algebra and \(u\in\alpha_p(R)\) with
\(\operatorname{inn}(u)\circ s_0=s_c\) over \(R\). By (1),
\((u-c)(1-t)=0\) in \(R[t]/(t^p-1)\), so \(u=c\). But then \(c^p=0\) in
\(R\), which is impossible for \(c\in k^\times\). Conjugation by
\((0,\tau)\in\mu_p(R)\) only replaces \(c\) by \(\tau c\).

In particular \(H^1(\mu_p,\alpha_p)\ne0\) for this action, as Raynaud shows.
This is exactly the vanishing that the proof of (a) takes from 15.3, where
neither group is smooth.

## 4. Counterexample to 16.27(b) and to 16.29, with smooth \(D\)

Take \(G=\alpha_p\rtimes\mathbb G_m\) and \(D=\mathbb G_m=D(\mathbb Z)\),
which is smooth. Fix \(c\in k^\times\) and put
\[
 S=\{(c(1-t),\,t):t\in\mu_p\}.
\]
\(S\) is the image of the homomorphism \(s_c:\mu_p\to G\) of §3, which is a
closed immersion. So \(S\cong\mu_p\) is a closed diagonalizable subgroup.

**\(S\) is maximal.** Let \(S'\supseteq S\) be a closed diagonalizable
subgroup. By Lemma B, \(q\) maps \(S'\) isomorphically onto a closed subgroup
\(q(S')\supseteq\mu_p\) of \(\mathbb G_m\), so \(q(S')\) is
\(\mathbb G_m\) or \(\mu_n\) with \(p\mid n\). Hence \(S'\) is the graph
\(\{(F(t),t)\}\) of a crossed homomorphism \(F:q(S')\to\alpha_p\) that
restricts to \(c(1-t)\) on \(\mu_p\).

By Lemma A, \(F=a(1-t)\), and \(a\ne0\) is possible only when
\(q(S')=\mu_p\). Since \(c\ne0\), we get \(q(S')=\mu_p\) and \(a=c\), so
\(S'=S\).

**\(S\) is not \(s(D)\) for a section \(s\).** By Lemma A with
\(H'=\mathbb G_m\), the only section of \(q\) is \(t\mapsto(0,t)\). Its image
\(0\times\mathbb G_m\) differs from \(S\).

So the forward implication of 16.27(b) fails. Over an algebraically closed
field, multiplicative type and diagonalizable coincide, so the same \(S\)
contradicts the maximal-subgroup sentence of 16.29 in its case (b). The
implication "image of a section ⇒ maximal" does hold in general. If
\(S'\supseteq s(D)\) is diagonalizable and \(x\) is a point of \(S'\), then
\(x\,s(q(x))^{-1}\) lies in \(S'\cap G_u\), which is trivial.

The proof of 16.27(b) breaks at the conjugacy step for
\(G'=q^{-1}(q(S))=\alpha_p\rtimes\mu_p\). There the quotient \(q(S)=\mu_p\)
is not smooth, even though \(D\) is.

Replacing \(\mathbb G_m\) by \(\mu_{p^2}\) gives a second counterexample to
16.27(b), with a finite \(G\). The same \(S\) is maximal, by Lemma A with
\(n=p^2\), and the only section is again \(t\mapsto(0,t)\).

## 5. What SGA 3 proves

SGA 3, Exp. XVII (Raynaud), Theorem 5.1.1, printed p.345 of the recomposed
edition (PDF p.21; original pp.573–574), treats an extension
\(1\to U\to E\to H\to1\) of a multiplicative-type group by a unipotent
algebraic group:

- i) The extension splits in four cases, including a) \(k\) algebraically
  closed. This is the existence statement, Milne 16.26, which these examples
  do not touch.
- ii) Two liftings of \(H\) in \(E\) are conjugate by an element of \(U(k)\)
  when a) \(k\) is algebraically closed and \(H\) is smooth, or b) \(k\) is
  algebraically closed and \(U\) is smooth.

Proposition 5.3.1 and Proposition 5.6.1 (printed pp.348–352) state the
conjugacy results with \(H\) smooth. The Exposé statements read for this note
concern liftings of the whole of \(H\). In 5.1.1, 5.2.3, 5.3.1 and 5.6.1, none
asserts the maximal-subgroup description that Milne adds in 16.29.

§5.9(d) (printed p.358, PDF p.34) shows that the hypotheses of ii) are
needed. Its first paragraph takes \(\mathbb G_a\rtimes\mu_p\) with a twisted
action over a field that is not algebraically closed; there two liftings of
\(\mu_p\) need not be conjugate by \(U(k)\). Its final paragraph is the
example of §3, over an algebraically closed field with neither \(H\) nor
\(U\) smooth.

### Why 16.26 is not affected

Milne's Theorem 16.26 (printed p.332, PDF p.348) asserts only existence: the
extension \(e\to G_u\to G\to D\to e\) splits in each of the cases

- (a) \(k\) is algebraically closed;
- (b) \(k\) is perfect and \(G_u\) is smooth and connected;
- (c) \(k\) is perfect and \(D\) is connected.

These examples leave it intact, for three reasons.

1. **Its statement is proved in SGA 3.** Case (a) is 5.1.1 i) a). Cases (b)
   and (c) are instances of 5.1.1 i) b), "k est parfait et l'un des groupes
   U ou H est connexe". Neither part asks for smoothness of \(H\), and part
   i) a) asks for nothing beyond \(k\) algebraically closed. The
   counterexamples concern only part ii), conjugacy.
2. **The examples satisfy it.** In \(\alpha_p\rtimes H\), the map
   \(t\mapsto(0,t)\) is a homomorphic section of \(q\).
3. **Its proof avoids the failing step.** The step that fails in 16.27 is
   the vanishing of \(H^1(D,N)\), that is, that every crossed homomorphism
   \(D\to N\) is principal, taken from 15.3. The proof of 16.26 instead
   shows that certain extensions of \(D\) by \(N\) split. In case (a) it
   uses Theorem 15.34(d) (printed p.319, PDF p.335), which states
   \(\operatorname{Ext}^1(G,U)=0\) for an algebraic subgroup \(U\) of
   \(\mathbb G_a\) and a group \(G\) of multiplicative type, with no
   smoothness hypothesis, when \(k\) is algebraically closed and the action
   comes from a linear action on \(\mathbb G_a\). These are different
   conditions: for \(\mu_p\) acting on \(\alpha_p\) by homotheties,
   \(H^1(\mu_p,\alpha_p)\neq0\) (§3), yet the extension
   \(\alpha_p\rtimes\mu_p\) splits.

This note does not audit the proof of 15.34. The 2017 errata
(entry for p.317) delete 15.29 and 15.30 and say that "the proofs in Section
15h have been rewritten"; 15.34 is in Section 15h. The statement of 16.26
rests in any case on SGA 3 XVII 5.1.1 i).

## 6. The corrected scope

Let \(k\) be algebraically closed. Keep the notation of 16.27.

- **\(D\) smooth.** Part (a) holds, by SGA 3 XVII 5.1.1 ii a). Part (b) can
  fail, by §4.
- **\(G_u\) smooth.** Both parts hold.
  - (a) is SGA 3 XVII 5.1.1 ii b).
  - For (b), let \(S\) be maximal diagonalizable and \(s\) a section (16.26).
    \(G'=q^{-1}(q(S))\) is an extension of \(q(S)\) by the same smooth
    \(G_u\). Both \(q|_S^{-1}\) and \(s|_{q(S)}\) are sections of it, so part
    (a) for \(G'\) gives \(u\in G_u(k)\) with
    \(S=\operatorname{inn}(u)\,s(q(S))\subseteq\operatorname{inn}(u)\,s(D)\).
    The right-hand side is the image of the section
    \(\operatorname{inn}(u)\circ s\), so maximality gives equality.
  - The converse is the general implication of §4.
- **Characteristic 0.** Every algebraic group is smooth (Cartier), so 16.27
  holds as printed.

## 7. Consequences for the Library

`Langlands.GroupScheme.TrigonalizableSectionConjugacyStatement`, in
`Langlands/GroupScheme/Trigonalizable/SectionConjugacyStatement.lean`, encodes
16.27 for every algebraically closed field. It has no smoothness hypothesis.

The examples satisfy its hypotheses:

- \(G\) is affine and of finite type.
- \(i:\alpha_p\to G\) is a closed immersion.
- \(\alpha_p\) is unipotent with normal range.
- \(q\) is a flat, surjective morphism of finite presentation with kernel
  \(\alpha_p\).
- \(\Lambda=\mathbb Z/p\) (§3) or \(\mathbb Z\) (§4) is finitely generated.
  Lift it to any universe with `ULift` as needed.

So, by §3 and §4, both conjuncts of its conclusion are false for every
algebraically closed field of positive characteristic. **Do not use that
proposition as a premise or as a proof target.**

As decided on 19 November 2026, the Library treats the proposition as follows.

- The proposition stays in the Library unproved, with its Lean text
  unchanged. Its Markdown marks it as not to be used as a target or as a
  premise and points to this note.
- The corrected statement
  `Langlands.GroupScheme.TrigonalizableSectionConjugacySmoothStatement`, in
  `Langlands/GroupScheme/Trigonalizable/SectionConjugacySmoothStatement.lean`,
  adds the explicit binder `Smooth U.X.hom`, justified by §6. Its Markdown
  says that (a) also holds when \(D\) is smooth and \(G_u\) is arbitrary
  (SGA 3 XVII 5.1.1 ii) a)). That case is neither stated nor proved there,
  so smoothness of \(G_u\) is not presented as necessary for (a).
- The Library proves the corrected statement, as
  `trigonalizableSectionConjugacySmooth`
  (`Langlands/GroupScheme/Trigonalizable/SectionConjugacySmoothProof.lean`).

The related statement `TrigonalizableExtensionSplitStatement` (Milne 16.26, existence
of a section) is consistent with these examples and is not affected (§5,
"Why 16.26 is not affected").

This note supplies no Lean disproof and changes no Lean or paired Markdown
file.

## 8. Sources and provenance

PDF page numbers are one-based. The group \(\alpha_p\rtimes\mu_p\) of §3 and
the non-vanishing of \(H^1(\mu_p,\alpha_p)\) are Raynaud's (SGA 3, XVII,
§5.9(d)). Lemma B is the case \(G_u=\alpha_p\) of the opening of Milne's
proof of 16.27(b); its proof here spells out that case from 14.17, 5.31 and
5.34. The explicit sections and the coordinate and fppf-local argument of §3,
Lemma A, the example of §4, the comparison with 16.26 at the end of §5 and
the derivation in §6 are arguments of this note. They use only the cited
structural results.

| Registered source | Locations used |
| --- | --- |
| `milne-2017-algebraic-groups`: J. S. Milne, *Algebraic Groups*, CUP 2017 | Proposition 5.31 and Theorem 5.34, printed pp.106–107/PDF pp.122–123; Theorem 12.9, printed p.233/PDF p.249; Proposition 16.2, printed pp.324–325/PDF pp.340–341; Corollaries 14.7 and 14.17, printed pp.282, 284/PDF pp.298, 300; Proposition 15.3, printed p.303/PDF p.319; Theorem 15.34, printed p.319/PDF p.335; Theorems 16.26–16.27, printed pp.332–333/PDF pp.348–349, including the opening of the proof of 16.27(b) on printed p.333/PDF p.349 (the source of Lemma B); Summary 16.29, printed p.334/PDF p.350. |
| `milne-2022-algebraic-groups`: corrected reprint, 2022 | Proposition 15.3, printed p.303/PDF p.314: same statement; the proof uses a chain indexed by divisibility in place of consecutive indices. Theorem 16.27, printed pp.333–334/PDF pp.344–345: the same mathematical statement and argument, with the proof continuing on printed p.334, where the proof of (b) opens; that opening sentence adds a comma after "q: G → D". Summary 16.29, printed p.334/PDF p.345: the assertions at issue are unchanged; case (a) reads "morphism of schemes" for "map of schemes". |
| `milne-2017-algebraic-groups-errata-2026-11-02` | Complete official HTML snapshot. Its Chapter 15 entry (p.317) deletes 15.29–15.30 and says that the proofs in Section 15h, which contains 15.34, have been rewritten. Its Chapter 16 entries concern pp.324, 330 and 349. None touches 15.3, 16.26, 16.27 or 16.29. |
| `milne-2022-algebraic-groups-errata-2026-11-04` | Complete official HTML snapshot. Its nearby entries concern 15.37 and 15.39 (pp.321–322). None touches 15.3, 16.27 or 16.29. |
| `sga3-expose-xvii-gille-polo-2008`: M. Raynaud, SGA 3 Exp. XVII, Gille–Polo recomposed edition, version of November 2008 | Theorem 5.1.1 i) and ii), printed p.345/PDF p.21 (original pp.573–574); Lemma 5.2.3, printed p.346/PDF p.22; Proposition 5.3.1, printed p.348/PDF p.24; Proposition 5.6.1, printed pp.351–352/PDF pp.27–28; §5.9(d), first and final paragraphs, printed p.358/PDF p.34 (original p.601): the source of the group in §3 and of \(H^1(\mu_p,\alpha_p)\neq0\); Appendix I, Proposition A.1.1 b) (Raynaud's "App. I, prop. 11"), printed pp.366–367/PDF pp.42–43: the low-degree exact sequence used in §3. |
