# Milne 16.62–16.63: a torus can have no fixed tangents without definite weights

Worker 75, Task 3483.

The action of \(\mathbb G_m\) on \(\mathbb G_a^2\) by opposite weights refutes the
strict-definiteness clause of Milne 16.62 and the assertion in 16.63 that every
Luna map is an isomorphism. This is a paper counterexample, not a Lean proof.

## Source and exact scope

James S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over a
Field* (Cambridge University Press), registered copies `milne-2017-algebraic-groups`
and `milne-2022-algebraic-groups` (2022 corrected reprint). Page numbers below are
printed; PDF pages are printed pages plus 16 and 11 respectively.

- Proposition 16.62, p.347 in both editions: for a smooth connected algebraic group
  \(G\) with an action of a torus \(T\), if \(\operatorname{Lie}(G)^T=0\), then
  \(G\) is unipotent and the action on \(\operatorname{Lie}(G)\) is strictly definite.
- Proposition 16.63, p.347 in both editions: in the split-torus case the same
  hypothesis gives \(G^T=e\), asserts that every Luna map from \(G\) to the affine
  space of its tangent space at the identity is an equivariant isomorphism, and
  asserts that \(G\) is split unipotent.
- Definition 13.40, p.269 in both editions: *definite* means the weights after extension
  to a separable closure are contained in the nonnegative integral span of some basis
  of the character lattice. *Strictly definite* adds that zero is not a weight.
- Lemma 13.36 and the paragraph following its proof: the Luna map associated to a
  stable complement \(W\) of \(\mathfrak m^2\) in the maximal ideal \(\mathfrak m\) of
  the fixed point comes from \(\operatorname{Sym}_k(W)\to\mathcal O(X)\). See pp.267–268
  in 2017 and p.268 in 2022. Theorem 13.41, p.269 in both editions, assumes
  **strict** definiteness on the tangent space to obtain the global isomorphism.

Neither registered author errata snapshot (`milne-2017-algebraic-groups-errata-2026-11-02`,
`milne-2022-algebraic-groups-errata-2026-11-04`) gives a correction to these claims.

## Opposite weights

Take an algebraically closed field \(k\), \(G=\mathbb G_{a,k}^2\), and
\(T=\mathbb G_{m,k}\). On each \(k\)-algebra \(R\), the action of \(t\in R^\times\) is
\[
  t\cdot(x,y)=(tx,t^{-1}y).
\]
It is an action by group automorphisms, and \(G\) is smooth, connected and affine.
The derivatives at the identity have the two weights \(1,-1\) in \(X^*(T)=\mathbb Z\),
so the fixed tangent subspace is zero. The only bases of \(\mathbb Z\) are \(\{1\}\)
and \(\{-1\}\); neither nonnegative span contains both weights. This refutes the
strict-definiteness conclusion of 16.62.

This obstruction occurs within the setting of the printed proof. Embed \(G\) in
upper unitriangular \(3\times 3\) matrices as \(I+xE_{12}+yE_{13}\), and let \(T\)
act by conjugation by \(\operatorname{diag}(1,t^{-1},t)\). The weights of the
full diagonal torus on the upper triangular Lie directions lie in its positive
cone, but the restrictions of the two displayed directions to \(T\) are opposite.
The last step of the proof of 16.62, passing definiteness to the restricted
action, does not hold.

## A Luna map which is not an isomorphism

In \(k[x,y]\) with \(\mathfrak m=(x,y)\), choose
\[
  W=k(x-x^2y)\ \oplus\ k y.
\]
The two summands are weight lines: the action on the coordinate \(x^2y\) has the
same weight as on \(x\), since \(xy\) is invariant. This holds whether the action
on functions is written by pullback or by inverse pullback. The reductions of
\(x-x^2y\) and \(y\) are the basis \(\overline x,\overline y\) of
\(\mathfrak m/\mathfrak m^2\). Thus \(W\) is a stable complement and defines a Luna
map in the source's sense, with coordinates
\[
  (x,y)\longmapsto (x(1-xy),y).
\]
It is equivariant and has identity differential at the origin, but it sends both
\((1,1)\) and \((0,1)\) to \((0,1)\). This refutes the universal isomorphism
claim of 16.63 even over \(k\) algebraically closed.

## What this example leaves intact

Here \(G\) is split unipotent and \(G^T=e\) even on all scheme tests: for an
\(R\)-point use the universal unit \(z\) over \(R[z,z^{-1}]\); invariance forces
\((z-1)x=(z^{-1}-1)y=0\), which by the Laurent coefficients gives \(x=y=0\).
Thus the example does not refute the unipotence, split unipotence or trivial
fixed-subgroup clauses. Those clauses should be handled separately. For the
Luna-isomorphism clause, retaining the strict-definiteness hypothesis of 13.41
rather than deducing it from vanishing tangent invariants avoids this obstruction.
No assertion with the false clauses is proposed for the Library.
