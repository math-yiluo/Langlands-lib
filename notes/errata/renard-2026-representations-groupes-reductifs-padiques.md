# Renard VII.1.2 and the strict root cone

The printed necessity in VII.1.2 fails for a square-integrable representation
of split \(\mathrm{Sp}_4(\mathbb Q_3)\). Its normalized Jacquet exponent at the
standard Borel has real part on a wall of the coroot chamber. The decay
inequalities at the end of Renard's proof give the strict root cone instead.

## The two cones

In VII.1.2 (printed p. 221, PDF p. 227), the theorem requires the real part of
each normalized exponent for \(P=MN\) to lie in
\({}^{G}_{P}[\mathfrak a_M^*]^+\). The third display of V.3.15 (printed p. 113,
PDF p. 119) defines that chamber by \(\langle\lambda,\check\beta\rangle>0\)
for every \(\beta\in\Delta(P)\), with \(\check\beta\) the projected coroot
of V.3.14. The first display defines \({}^{+}[\mathfrak a^*]^G_P\) as the
cone of sums \(\sum_{\beta\in\Delta(P)}c_\beta\beta\) with every \(c_\beta>0\).
For a minimal parabolic of a split group, the projected coroots are the
simple coroots of its standard split torus.

## A Jacquet exponent on a coroot wall

Take \(F=\mathbb Q_3\), \(G=\mathrm{Sp}_4\), and write \(B=TN\) for the
upper triangular Borel with diagonal torus
\(t=\operatorname{diag}(t_1,t_2,t_2^{-1},t_1^{-1})\). This is the standard
minimal parabolic of Sally–Tadić's \(\mathrm{Sp}(2,F)\). Use
\(\nu=|\cdot|_F\), \(v_F(3)=1\), and the smooth quadratic character
\(\xi(x)=(-1)^{v_F(x)}\).

Sally–Tadić, Theorem 5.1(i), gives two irreducible square-integrable smooth
subrepresentations of the normalized principal series
\((\nu\xi)\times\xi\rtimes 1\). Take either one and call it \(\pi\).
The proof computes its normalized Jacquet module at \(B\) as the
one-dimensional character \(\nu\xi\otimes\xi\otimes 1\). In the coordinates
of §1 this character is
\[
  \chi(t)=|t_1|_F\,\xi(t_1)\xi(t_2).
\]
In particular the entire Jacquet module is a nonzero \(\chi\)-weight space.
The normalization in §1 twists the Jacquet action by the inverse square
root of the usual modulus. This agrees with the twist by
\(\delta_B^{1/2}\) in Renard's (VI.1.2.2), since the remark in VI.1.2
(printed p. 136, PDF p. 142) specifies that his \(\delta_B\) is the
inverse of the usual modulus. [Sally–Tadić, §1 and Theorem 5.1(i)](https://www.numdam.org/article/MSMF_1993_2_52__75_0.pdf#page=47)

The principal series is admissible. For any compact open \(K\) of \(G(F)\),
the images of the double cosets \(B(F)gK\) form an open partition of
the compact flag quotient \(B(F)\backslash G(F)\), so there are finitely
many. Each \(K\)-fixed inducing function is determined by its scalar values
on their representatives. Thus \(\pi^K\) is finite-dimensional as well.
The center \(\{I,-I\}\) acts trivially because the inducing character at
\(-I\) has value \(\nu(-1)\xi(-1)^2=1\) and the modulus is trivial there.
The square integrability from Theorem 5.1(i) gives square integrability
modulo this finite center. Hence \(\pi\) meets the hypotheses of VII.1.2.

Let \(e_i\in X^*(T)\) be the character \(t\mapsto t_i\) and let \(e_i^\vee\)
be the dual basis of \(X_*(T)\). The \(q^{-s}\) convention of V.3.20 gives
\(\mathop{\rm Re}\chi=e_1\) since \(|\chi(t)|=|t_1|_F\). For the upper
triangular Borel the type \(C_2\) simple roots are
\(\alpha_1=e_1-e_2\) and \(\alpha_2=2e_2\), with long simple coroot
\(\alpha_2^\vee=e_2^\vee\). Thus
\[
  \mathop{\rm Re}\chi=\alpha_1+\tfrac12\alpha_2,
  \qquad
  \langle\mathop{\rm Re}\chi,\alpha_2^\vee\rangle=0.
\]
The first equality gives membership in the strict root cone. The second
violates the printed strict coroot inequality. The zero pairing also
persists with the raw-log parameter \(-(\log q)e_1\) mentioned in V.3.20.

## The concluding decay test and its Lean formulation

On printed p. 224 (PDF p. 230), the proof uses
\(|\chi(t_{\alpha_i})|<1\) on the generators from printed p. 222 (PDF p. 228).
They have \(v_F(\alpha_j(t_{\alpha_i}))=0\) for \(j\ne i\) and
\(v_F(\alpha_i(t_{\alpha_i}))>0\). In the \(q^{-s}\) convention,
\(|\chi(t)|=q^{-\langle\mathop{\rm Re}\chi,H_M(t)\rangle}\).
The unitary central character makes the exponent's real part vanish
on the split central directions of \(G\). Expanding it as
\(\sum_j c_j\alpha_j\), the decay test on \(t_{\alpha_i}\) becomes
\[
  c_i v_F(\alpha_i(t_{\alpha_i}))>0.
\]
This yields \(c_i>0\) for every \(i\), the first cone of V.3.15.

The published `ArbitraryParabolicCasselmanCriterionStatement` uses this
condition through `normalizedRealPart` and `pres.positiveCone`. The
published `arbitraryParabolicCasselmanNecessity` proves the corresponding
forward direction. The Library states the complete corrected criterion
and does not prove it. The example above is
a paper counterexample to the printed assertion. [Criterion statement](../../Langlands/Representation/Exponents/ArbitraryParabolicCasselmanStatement.md) · [Necessity proof](../../Langlands/Representation/Exponents/CasselmanNecessity.md)

## Sources

- David Renard, *Représentations des groupes réductifs p-adiques*, French
  version dated 9 July 2026. V.3.14–15, printed p. 113 (PDF p. 119).
  V.3.20–21, printed pp. 115–116 (PDF pp. 121–122).
  VI.1.2, printed pp. 135–136 (PDF pp. 141–142).
  VII.1.2, printed pp. 221–224 (PDF pp. 227–230).
  Registered as `renard-2026-representations-groupes-reductifs-padiques`,
  SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Paul J. Sally Jr. and Marko Tadić, *Induced representations and classification
  for GSp(2,F) and Sp(2,F)*, Mémoires de la Société Mathématique de France,
  no. 52 (1993), pp. 75–133. Section 1, printed pp. 85–88 (PDF pp. 12–15).
  Theorem 5.1(i) and its proof, printed pp. 120–121 (PDF pp. 47–48).
  Registered as `sally-tadic-1993-gsp2-sp2-induced-representations`,
  SHA256 `876d25e45bd74cbd6bcd96f63a22d4b76c8ce5a0f8b3156421985e8a2a857c80`.
  [Numdam article](https://www.numdam.org/item/MSMF_1993_2_52__75_0/)
