# Dynamic subgroups: field and arbitrary-base proof obligations

This note, dated 13 November 2026, supplements the [family-4 ledger](ledger-family-4-absolute.md),
rows C3, C7 and C8, and the [family-8 ledger](ledger-family-8-relative.md),
rows D2 and F1–F2. The four statements below are in the Library, and so
are their proofs (see "Proofs in the Library" below).

## Four published statements

Lean declaration names in this note have prefix `Langlands.GroupScheme`.
Every statement quantifies over actual group schemes and cocharacters.
An `IsRepresentedBy j` hypothesis means monomorphism and equality of the
range with the dynamic subgroup on every test scheme, including
nonreduced tests. These four statements assume representatives; they do
not assert their existence.

| Declaration and source | Exact scope and conclusion |
| --- | --- |
| [`DynamicBaseUnipotentFibresStatement`](../../Langlands/GroupScheme/Dynamic/BaseUnipotentFibresStatement.md). CGP, Lemma 2.1.5, printed pp.49–51/PDF pp.75–77; Conrad, discussion after Example 4.1.9, p.114. | Over any scheme `S`, let `G → S` be affine and locally of finite type. Every representative `H` of `U_G(χ)` becomes an `IsUnipotent` field group after every field-valued base change `Spec K → S`. No smoothness, ambient connectedness or local finite-presentation hypothesis is imposed. |
| [`DynamicBaseOppositeCellStatement`](../../Langlands/GroupScheme/Dynamic/BaseOppositeCellStatement.md). Conrad, Theorem 4.1.7(4), pp.112–113, and the arbitrary-base extension on p.114. | Over any scheme `S`, for smooth affine `G → S` and representatives of `U_G(−χ)` and `P_G(χ)`, ordered multiplication `U ×_S P → G` is an open immersion. Ambient connectedness is unnecessary. |
| [`DynamicFieldOppositeCellStatement`](../../Langlands/GroupScheme/Dynamic/FieldOppositeCellStatement.md). CGP, Proposition 2.1.8(3), printed p.53/PDF p.79. | Over every field `k`, for affine locally finite-type `G` and the same representatives, ordered multiplication `U ×_k P → G` is an open immersion. No smoothness or connectedness is assumed. The subsequent ambient-intersection assertion in the source is not included. |
| [`DynamicBaseConnectedStatement`](../../Langlands/GroupScheme/Dynamic/BaseConnectedStatement.md). Conrad, Theorem 4.1.7(2), pp.112–114, including the arbitrary-base extension; CGP, Proposition 2.1.8(4), printed p.53/PDF p.79. | Over any scheme `S`, let `G → S` be affine and locally of finite presentation. Every representative of `U_G(χ)` has geometrically connected fibres. Representatives of `P_G(χ)` and `Z_G(χ)` have geometrically connected fibres if `G → S` does. No smoothness or reducedness is assumed. |

Here `−χ` means precomposition with inversion on `G_m`; the order of
multiplication is `(u,p) ↦ iU(u)iP(p)`. Geometric connectedness concerns
all field-valued fibres and does not assert connectedness of the total
space over a disconnected base.

The field open-cell target and the arbitrary-base open-cell target have
different hypotheses. The former retains finite type directly and
permits nonsmooth field groups. The latter retains smoothness and permits
non-affine base schemes. The earlier smooth field theorem
`oppositeCellStatement` (`Absolute/OppositeCellProof.lean`) remains in the
Library.

The cited originals are registered as
`conrad-gabber-prasad-2015-pseudo-reductive` and
`conrad-2014-reductive-group-schemes`. Their file hashes and the derivations
from their precise finiteness hypotheses are recorded in the linked
statement Markdown. In particular, affineness and local finite type over
a field imply finite presentation; affineness and local finite
presentation over an arbitrary scheme give finite presentation.

## First appearance in the Library

Both files of each statement pair were checked against the versions that
first entered the Library. All four are statements; none is a proof.

| Statement suffix | First appeared at Library commit |
| --- | --- |
| `BaseUnipotentFibresStatement` | `17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e` |
| `BaseOppositeCellStatement` | `cfedefb680f317b0ea5d351023e1c9dd886b2547` |
| `FieldOppositeCellStatement` | `730bd1f25b056b8106a2697e003c1ef1733a6b30` |
| `BaseConnectedStatement` | `730bd1f25b056b8106a2697e003c1ef1733a6b30` |

## Proofs in the Library

Every target in this table is proved in the Library, in the
`Langlands/GroupScheme/Dynamic/` file named.

| Target | Proof |
| --- | --- |
| `DynamicBaseSmoothConnectedStatement`: smoothness over every base, and geometric connectedness of `U`, or of `P/Z` when the ambient smooth affine group has geometrically connected fibres. | `dynamicBaseSmoothConnected` (`BaseSmoothConnectedProof.lean`) |
| `DynamicBaseRepresentabilityStatement`: for affine locally finitely presented `G` over every base, construct locally finitely presented closed representatives of `P/U/Z`. | `dynamicBaseRepresentability` (`BaseRepresentabilityProof.lean`) |
| `DynamicBaseUnipotentFibresStatement`. | `dynamicBaseUnipotentFibres` (`BaseUnipotentFibresProof.lean`) |
| `DynamicRingLieStatement`: for every commutative ring and affine locally finitely presented group, identify the actual dual-number Lie kernels of `Z/P/U` with weight zero, nonnegative integer-power weights and positive integer-power weights. | `dynamicRingLie` (`RingLieProof.lean`) |
| `DynamicBaseOppositeCellStatement`. | `dynamicBaseOppositeCell` (`BaseOppositeCellProof.lean`) |
| `DynamicFieldOppositeCellStatement`. | `dynamicFieldOppositeCell` (`FieldOppositeCellProof.lean`) |
| `DynamicBaseConnectedStatement`. | `dynamicBaseConnected` (`BaseConnectedProof.lean`) |

A compilation of the field open-cell and connectedness proof modules
together completed with zero errors or warnings; inspection of
`dynamicBaseConnected` reported only `propext`, `Classical.choice` and
`Quot.sound`.

The field open-cell proof uses the published closed linear embedding and
diagonal-cocharacter open-cell theorems. The connectedness proof first
uses the rational unit to obtain geometric connectedness. Perfect-field
reduction gives irreducibility, which descends from an algebraic closure.
The field open cell then gives connectedness of `P`; the split limit map
gives connectedness of `Z`. Published unipotent connectedness and the
dynamic base-change identities assemble the arbitrary-base result.
This route is described in the page `Dynamic/BaseConnectedProof.md`.

The connectedness proof imports the field open-cell proof. The published
dynamic base-change and scheme-decomposition constructions are
independent of both proofs.

These statements remove the corresponding missing-statement entries in the
older ledgers. The other field, relative, Galois, classification and
example obligations of the program are recorded in those ledgers.
