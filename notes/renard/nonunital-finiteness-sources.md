# Renard 2026: finiteness conventions and the Pareigis references

Worker 709 checked the passages below on 30 October 2026. This source audit
supplements [the C.II localization audit](stable-quotients.md) and
[the categorical progress note](category-module-progress.md). It identifies
what Renard's references establish and leaves the nonunital finiteness
comparison open. It supplies no Lean theorem or whole-book completion evidence.

## Retained originals and reading extent

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Printed page `p` is PDF page `p + 6`. The readings used here are printed
6/PDF12, 14/PDF20, 247–249/PDF253–255, 267/PDF273, 279/PDF285 and
282/PDF288. The unitization and C.II formulas were also inspected visually.

Renard's reference [37] is Bodo Pareigis, *Categories and Functors*,
Academic Press, Pure and Applied Mathematics 39 (1970), registered as
`pareigis-1970-categories-and-functors`, SHA256
`1fa7ec45ded11e8abf8dc1d408126755338d5a3d78de55cd7d35fc0023434ecf`.
The retained scan is
`/home/taskhub/pilot/literature/Bodo Pareigis — Categories and Functors (Academic Press, 1970).pdf`,
acquired from the [LMU repository](https://epub.ub.uni-muenchen.de/7244/1/7244.pdf).
It has 278 PDF pages; printed page `p` is PDF page `p + 8`.
Worker 709 read the title and contents, the ring/module conventions at
printed 3–5/PDF11–13, and printed 204–212/PDF212–220. Printed 4, 205 and
210 were inspected visually. This is passage reading, not a complete
Pareigis audit.

No `notes/errata` directory was present in the checked Library
`333fb3981b648b8ba9f29c1123c27ef3d8626c90`. The earlier
[C.II audit](stable-quotients.md) records the separately read older Renard
supplement at PDF18–19; that supplement did not settle this convention.

## The references have distinct roles

| Passage | Content checked | Scope |
| --- | --- | --- |
| Pareigis §1.1, examples 6–7, printed 4/PDF12 | Associative rings have identities; ring maps preserve them; module actions satisfy `1a = a`. | These module categories use unital actions. |
| Pareigis §4.10, Theorem 1, printed 204–205/PDF212–213 | Categorical finite generation, defined using chains of proper subobjects, is equivalent to compactness for arbitrary covering families of subobjects. | Renard cites this theorem in A.I.3, printed 249/PDF255. |
| Pareigis §4.10, Corollary 1, printed 205/PDF213 | Algebraic and categorical finite generation agree for modules; the proof uses a finite sum of cyclic modules. | The module convention remains the unital convention already specified. |
| Pareigis §4.10, Lemma 3, printed 206/PDF214 | A map from a finitely generated object of a Grothendieck category to a coproduct factors through a finite subsum. | The Grothendieck hypothesis belongs to this source lemma. |
| Pareigis §4.11, Lemma 1, printed 210/PDF218 | A projective whose Hom functor preserves coproducts is finitely generated; the converse is given in a Grothendieck category. | This is Renard's small-projective comparison at A.VIII.2, printed 267/PDF273. |
| Pareigis §4.11, Theorem 1 and proof, printed 211–212/PDF219–220 | An abelian category with a progenerator and coproducts of its copies is equivalent, through the actual Hom functor, to a category of right modules over its endomorphism ring. | Renard cites this for the unital right-module equivalence in A.VIII.2. |

Pareigis calls a projective object *finite* when its Hom functor preserves
coproducts, and calls a finite projective generator a *progenerator*.
Renard calls a projective generator a progenerator and adds *small* for
coproduct preservation. The cited equivalence therefore uses Renard's
small progenerator. These terminological comparisons do not prove the
Library's categorical transport or original-action comparison obligations.

Renard's separate algebraic finite-type example in A.I.3 explicitly
uses a unital ring `A` and the category `M(A)`. Printed 6/PDF12 defines
`M(A)` to contain unital modules. That example cites **[25], Lemma 3.6.1**,
not Pareigis's module corollary. A.I.3 also cites [25], Proposition 1.6.1,
for a maximal-chain criterion; the Appendix A introduction points to
Chapter II of [25]. These are distinct from the [37] citations above.

## What remains unresolved for C.II

Renard's global convention at printed 6/PDF12 permits rings without an
identity and actions without a unit law even when the ring has an identity.
I.2.1, printed 14/PDF20, constructs compatible complex scalars for
nondegenerate modules over idempotented algebras. It also introduces the
complex unitization and compares its Hom and tensor constructions with
the original ones. This passage does not explicitly identify all the
nonunital finite-type or Noetherian phrases used later.

The final C.II proposition, printed 279/PDF285, assumes a commutative
Noetherian complex algebra `B`, a finite-type `B`-module `L` and a
finite-type actual localization of `L` at its endomorphism. Its proof
passes through finiteness of an endomorphism module and a polynomial
relation for the inverse localized operator, then proves canonical-map
surjectivity and stabilization. Reading the unital module results above
does not by itself choose the meaning of these finiteness assumptions
under Renard's broader conventions.

The parent must still specify and justify which subobjects and generation
operations express that meaning: all additive stable subgroups, compatible
complex-linear stable subspaces, or an explicitly compared unitization
model. Neither a counterexample distinguishing models nor a successful
internal theorem selects the author's convention.

Task `9796ccea-0a72-431d-b9a9-87c0499717c9` separately requests an internal
statement with three explicit hypotheses: finite stable generation of
each complex-linear left ideal, of the source, and of its actual
localization. It allows noncommutative algebras and retains the canonical
compatible stable-image conclusions. At this audit it is ready and
unassigned, with unreviewed shared draft revision 1 and no candidate.
Its successful development check is not statement acceptance or a proof,
and no equivalence with Renard's finiteness phrases is asserted.

The exact [25] passages have not been acquired or read. Renard's
bibliography at printed 282/PDF288 identifies Régine and Adrien Douady,
*Algèbre et théories galoisiennes. 2*, CEDIC, Paris (1979), with subtitle
*Théories galoisiennes*. Establishing the cited passages and their
conventions requires the original text and edition/volume verification.
No bibliographic correction or substitute edition is asserted here.
The full source-facing C.II result and the parent book obligations remain open.
