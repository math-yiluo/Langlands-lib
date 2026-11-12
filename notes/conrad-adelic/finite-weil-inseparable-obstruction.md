# Finite Weil restriction: an inseparable obstruction over incomplete fields

Author: Worker 111, Task 5256 (`926b44cd-4772-49e6-bacb-9c3337206e14`).

Conrad's Proposition 5.11(1), as printed on p.18 of *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), fails for some finite purely
inseparable extensions of incomplete henselian valued fields. This note gives
an ordinary mathematical counterexample. It is not a Lean refutation of the
published `HenselianWeilRestrictionPointHomeomorphStatement`; the statement and
its import closure have not been changed.

## Counterexample

Fix a prime `p`. Give `M = F_p((t))` its nontrivial `t`-adic norm, for example
normalized by `|t| = 1/2`. Choose `s` in `M` transcendental over `F_p(t)`, set
`K_0 = F_p(t,s^p)`, and let `K` be the henselization of `K_0` inside `M`.
Put `L = K(s)` and give both fields their restricted norms.

The extension `K/K_0` is separable algebraic, while `s` is purely inseparable
of degree `p` over `K_0`. Hence `s` is not in `K` and `[L:K] = p`. The field
`K` is henselian, and its algebraic extension `L` is henselian. These are
nontrivially normed fields with a finite dimensional normed-algebra extension.
Because `F_p(t)` is dense in `M`, their completions are both `M`, and `K` is
dense and proper in `L`.

Take `Y' = A^1_L`, a separated affine scheme of finite type. Its Weil
restriction is `A^p_K`. In the basis `(1,s,...,s^(p-1))` of `L/K`, the canonical
point bijection is

```
f : K^p -> L,      f(x_0,...,x_(p-1)) = sum_i x_i s^i.
```

The topology on affine-space points is the product topology. On schemes, the
Library's etale-chart topology agrees with the scheme point topology by
`isHomeomorph_schemeRingPointsEquiv`. Thus these are the same topologies as
those used in the published target.

Let `a_n` be polynomial or Laurent-polynomial truncations of `s`, so that
`a_n` is in `F_p(t)`, hence in `K`, and `a_n -> s` in `L`. The vectors

```
v_n = (-a_n,1,0,...,0)
```

satisfy `f(v_n) = s-a_n -> 0`. They do not converge to zero in `K^p`, since
their second coordinate is constantly `1`. The open neighborhood
`{v : |v_1| < 1}` of zero contains none of them. Therefore `f^{-1}` is not
continuous at zero. An equivalent argument is that the first coordinate axis
is closed in `K^p` but maps onto the dense proper subfield `K` in `L`.

All geometric hypotheses of the target hold already in this affine example.
The obstruction concerns the topology of the valued extension and does not
concern algebraic-space representability.

## Source evidence

The original source is Brian Conrad, *Weil and Grothendieck approaches to
adelic points*, December 31, 2011, Proposition 5.11(1) and its proof, printed
p.18; registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad's p.14 discussion of tensor products with completions explicitly treats
finite **separable** extensions. His proof on p.18 appeals to the affine
comparison without imposing separability or completeness in the statement.

Michael Temkin's *Valued Fields*, Exercise 1.8.11(i)-(ii), printed p.22,
provides the inseparable subextension construction and a stronger example
whose entire completion is algebraic and purely inseparable. Remark 1.9.6,
printed p.25, explicitly identifies a henselian DVR not algebraically closed
in its completion. Theorem 1.9.5 and Section 1.9.7 on p.25 explain the
henselianity and henselization used above. Registered source
`temkin-valued-fields-2018-course-notes`, SHA-256
`60cbfd7681abcb39ee111aff005434bd6b11054089cf48a78068c97e3d53abe3`, retained at
`/home/taskhub/pilot/literature/Michael Temkin, Valued Fields (course notes).pdf`.
The author-hosted original is
[Temkin's course notes](https://math.huji.ac.il/~temkin/teach/math583/notes.pdf).
The PDF does not state a date; the source-ID label is not an edition claim.
The counterexample to Conrad's topology assertion is derived here from these
valued-field examples.

## Formal progress and remaining scope decision

Worker 111's candidate `7cd56404-460b-4151-88f2-c5beb8477b0d` contains the
auxiliary construction `ringWeilRestrictionPointHomeomorph`, in module
`Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionPointComparison`.
At submission this candidate is staged and is not an accepted Library result.
Its Lake build and selected-declaration inspection succeeded in private check
`4ebc7e45-8a12-449e-a0a5-9c61b33233cc` with only `propext`, `Classical.choice`
and `Quot.sound` among the inspected assumptions. This does not establish
independent acceptance or completion of the exact task.

The construction takes explicit representability and quasi-separated local
finite-type hypotheses for the restriction, and **`IsModuleTopology K L`**.
It gives forward continuity without the latter hypothesis; inverse continuity
uses the published affine homeomorphism and open surjective affine chart
families. This avoids any local-separatedness requirement on the spaces.

`IsModuleTopology K L` is false in the counterexample above. For a complete
base field, finite dimensionality does provide the module topology. A
correction imposing that topology, or completeness of the base, excludes this
example. No corrected general target or complete-base specialization is
claimed as published by this note. Task 5256's unchanged contract forbids
additional hypotheses, so operator request `aeae120297a75a7c9cbd2862ceb97e68`
records the needed scope decision. Lemma 5.10's representability claim remains
a separate obligation of Task 5255 (`e276f80d-e140-4579-90fc-cc3dceba3c06`).
