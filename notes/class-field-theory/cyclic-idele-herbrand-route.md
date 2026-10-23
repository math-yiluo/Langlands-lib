# Cyclic idele-class Herbrand quotient: source and dependency map

This note records a proof route for
`Langlands.ClassField.Global.CyclicIdeleClassHerbrandQuotient` and the
infrastructure gaps found by Worker 343 on 2026-10-23. It is a source audit
and implementation plan, not a proof or a report of completed formalization.
The statement is in
[`CyclicIdeleClassHerbrandQuotientStatement.lean`](../../Langlands/ClassField/Global/CyclicIdeleClassHerbrandQuotientStatement.lean).

## Exact target and conventions

For number fields `F : Type u` and `E : Type v` with independent universes,
`Algebra F E`, `IsGalois F E`, and `IsCyclic (E ≃ₐ[F] E)`, the target asserts
that the actual first and second idele-class cohomology groups are finite
and

`|H²(Gal(E/F), C_E)| = [E:F] * |H¹(Gal(E/F), C_E)|`.

Here `C_E` is the published `NumberField.IdeleClassGroup (𝓞 E) E`,
with `relativeIdeleClassAut F E`; cohomology means the published
`relativeIdeleClassCohomology F E n`, using Mathlib ordinary group
cohomology of the additive coefficient representation. Degree one
extensions are included. Finiteness must be proved separately:
`Nat.card` is zero on infinite types, so a cardinal equality by itself
would not express the intended Herbrand quotient.

Write `h(A) = |H²(G,A)| / |H¹(G,A)|` only when both groups are finite.
The planned Lean interfaces express its identities by multiplication
of natural-number cardinalities.

## A route using ordinary units

Artin–Tate, Chapter V §3, permits any finite nonempty set `S` of base
places containing all infinite places. For number fields choose `S`
to be exactly the infinite places. Let:

- `J∞` be the subgroup of actual ideles whose every finite component
  is a valuation unit;
- `U = (𝓞 E)ˣ`, embedded by the principal-idele map;
- `C∞` be the image of `J∞` in the actual `C_E`;
- `Q = C_E / C∞`;
- `D∞` be the product of the orders of stabilizers of representatives
  of the Galois orbits on the infinite places of `E`.

The arithmetic obligations are an exact sequence
`1 → U → J∞ → C∞ → 1`, finiteness of `Q`, and the two finite
Herbrand-quotient formulas

`h(J∞) = D∞`,  `[E:F] * h(U) = D∞`.

Finiteness of `Q` follows from the finite ideal class group, as in
Artin–Tate V §3. Thus the chosen set need not contain class-group
generators. Multiplicativity and the quotient-one result for finite
coefficients then give

`h(C_E) = h(C∞) = h(J∞) / h(U) = [E:F]`.

Every use of multiplicativity must also propagate finiteness. In the
division-free implementation the final cancellations are legitimate
because finite cohomology groups have positive cardinality.

This is a specialization of Artin–Tate's argument, not a new arithmetic
theorem. It avoids requiring a formalization of the full S-unit theorem:
the selected unit group is exactly the ordinary ring-integer unit group.
It does not avoid the equivariant content of Dirichlet's theorem.

## Units: equivariance is essential

Milne VII Proposition 3.1 proves the unit formula by comparing two full
invariant lattices in the permutation representation
`V = (InfinitePlace E → ℝ)`. Use the normalized logarithms
`w.mult * Real.log (w x)`. Their image `M₀` lies in the sum-zero
hyperplane; its kernel on units is finite torsion. The lattice
`M = M₀ + ℤ·(1,…,1)` is full in `V`. The constant summand is trivial
under `G`, giving `h(M) = [E:F] * h(U)`. The permutation lattice
`N = (InfinitePlace E → ℤ)` has quotient `D∞` by orbit decomposition,
Shapiro, and `h(H,ℤ) = |H|` for finite cyclic `H`.

The needed comparison is Milne VII Lemma 3.5: two full invariant
lattices in the same real representation have the same quotient,
provided one quotient is defined. Equal ranks alone do not give this.
Nor may one simply assert that the two lattices are commensurable as
subgroups of the real space. Milne first descends an isomorphism of
real representations to rational representations (Lemma 3.2), and then
uses finite-index invariance (Lemma 3.4).

Mathlib's `Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`
already supplies `NumberField.Units.logEmbedding`, `unitLattice`,
`logEmbeddingEquiv`, and the full-lattice result. Its `logSpace` omits
one chosen infinite place. An implementation still needs to restore
the missing coordinate using the sum-zero identity and prove
equivariance for the resulting full logarithmic hyperplane. The unit
rank theorem alone is insufficient.

## Ideles: the local arithmetic input is not yet discharged

Artin–Tate V §§2–3 writes the finite part of `J∞` as products of
semilocal unit groups. For cyclic local extensions the required
calculation is

`|H¹(G_w,U_w)| = |H²(G_w,U_w)| = e_w`.

It includes finiteness and yields trivial cohomology at unramified
places. Only finitely many places ramify. Together with cohomology
of products and Shapiro, this gives quotient one for the finite-unit
part. The infinite-place factors give `D∞`.

The following Library interfaces are useful but do not by themselves
supply that unconditional calculation:

- [`LocalUnitCohomology.lean`](../../Langlands/ClassField/Global/LocalUnitCohomology.lean)
  defines the actual valuation-unit subgroup, its action, and
  `unitsValuationSequence_shortExact`; it also supplies
  `isZero_H1_trivial_integers` and `mono_map_localUnitsInclusion_two`.
- [`LocalUnitVanishing.lean`](../../Langlands/ClassField/Global/LocalUnitVanishing.lean),
  theorem `isZero_H2_localUnits`, assumes an unramified place,
  finiteness of actual local `H²(E_wˣ)`, and the cardinal bound by the
  local degree. Its conclusion does not discharge those hypotheses.
- [`RelativeInvariantEquivalences.lean`](../../Langlands/ClassFieldTheory/Local/RelativeInvariantEquivalences.lean)
  supplies `InvariantFamily.relativeH2_card` and
  `InvariantFamily.relativeH2_finite` from a supplied invariant family
  satisfying `RelativeImages`. These are consequences of that image
  law, not existence theorems for such a family.

The local prerequisite therefore needs either an unconditional local
invariant/norm-index result or a separate proof of the cyclic unit
calculation. The present audit has not established that either is
available. Coordinate with the local class-field workers before
duplicating their arithmetic work.

The published `IdeleArchimedean` and `IdeleSemilocal` modules supply
coordinate, action, and semilocal infrastructure; their presence is not
evidence that the entire `h(J∞)` formula has been proved. Several
existing helpers, including `IdeleCoefficientSequence`, use a common
field universe. New arithmetic interfaces must handle the target's
independent universes without changing the target's imported definitions.

## Work decomposition recorded on 2026-10-23

The following tasks were published; none of their intended conclusions
is being asserted as an accepted result here:

| Task | Scope |
| --- | --- |
| `0425e75a-8b9f-446a-b471-050b6b43cfb0` | Actual `J∞`, ordinary units, `C∞`, quotient, arithmetic actions and coefficient maps. |
| `8e89288e-24db-41a4-84e0-0d019b344a51` | Cyclic Herbrand multiplicativity and finite-coefficient proposition statements, then exact proof follow-ups. |
| `e92da4ea-e03e-4d7e-868d-9a7d459a4125` | Full invariant real-lattice comparison statement, then an exact proof follow-up. |

After the coefficient definitions publish, the remaining arithmetic
statements concern the unit formula, the integral-idele formula, and
the exact sequence with finite quotient. Parent proof task
`04294c5a-fea1-46f3-b7ea-e20d88ae0870` will assemble those results.
The downstream idele-class `H¹` vanishing and fundamental-class tasks
cannot serve as unproved inputs to this calculation.

## Sources and reading extent

Registered originals:

- Emil Artin and John Tate, *Class Field Theory* (2009), literature ID
  `artin-tate-2009-class-field-theory`, retained at
  `/home/taskhub/central-library/Artin-Tate--Class Field Theory--2009.pdf`.
  Preliminaries §3, printed pp.5–7 (PDF14–16), gives the cyclic quotient
  calculus; V §1, printed p.11 (PDF20), states the target; V §§2–3,
  printed pp.12–13 (PDF21–22), gives the local-unit and finite-quotient
  reduction used here.
- J. S. Milne, *Class Field Theory*, v4.03 (2020), literature ID
  `milne-2020-class-field-theory`, retained at
  `/home/taskhub/central-library/Milne--Class Field Theory (v4.03)--2020.pdf`.
  VII §§2–4, printed pp.205–211 (PDF214–220), was read. In particular,
  Proposition 3.1 and Lemmas 3.2, 3.4, 3.5, printed pp.208–209
  (PDF217–218), supply the lattice route.

No errata file for either source was found in the workspace or the
public notes during this audit.
