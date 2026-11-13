# Dynamic subgroups: field and arbitrary-base proof obligations

Worker 3483, 13 November 2026, for Task 3483
(`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`).

This dated update supplements the [family-4 ledger](ledger-family-4-absolute.md),
rows C3, C7 and C8, and the [family-8 ledger](ledger-family-8-relative.md),
rows D2 and F1–F2. It describes Library
`7dc9118a3eb340e83e65d6e4174763b7a61e573c` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`. The four statement pairs below
are independently accepted and published. Their proofs remain obligations.
The shared drafts and successful development checks described here supply
neither independent proof acceptance nor publication.

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
`oppositeCellStatement` remains published.

The cited originals are registered as
`conrad-gabber-prasad-2015-pseudo-reductive` and
`conrad-2014-reductive-group-schemes`. Their file hashes and the derivations
from their precise finiteness hypotheses are recorded in the linked
statement Markdown. In particular, affineness and local finite type over
a field imply finite presentation; affineness and local finite
presentation over an arbitrary scheme give finite presentation.

## Independent acceptance and publication

Worker 3483 fetched the publication ledgers and checked that both files of
each pair in the current Library match the frozen candidate hashes.
All four are statement artifacts; none is proof evidence.

| Statement suffix | Accepted candidate | Independent reviewer | Library publication |
| --- | --- | --- | --- |
| `BaseUnipotentFibresStatement` | `2ac1f041-1300-4dcf-9f31-c7d8233e6f5f` | Reviewer 6 | `17dd94ea3f677b20fb5ab95b285cbc3fd7cde03e` |
| `BaseOppositeCellStatement` | `1b01a9d7-f3f9-4ca2-a45f-6ff1608a67bf` | Reviewer 143 | `cfedefb680f317b0ea5d351023e1c9dd886b2547` |
| `FieldOppositeCellStatement` | `d0f87bc9-bad8-4a08-9b68-a4de1a235bcf` | Reviewer 563 | `730bd1f25b056b8106a2697e003c1ef1733a6b30` |
| `BaseConnectedStatement` | `a17b8e75-eead-4531-945e-8f033577b4ef` | Reviewer 506 | `730bd1f25b056b8106a2697e003c1ef1733a6b30` |

## Focused proof owners

The following proof tasks retain the unchanged published propositions.
Their existence does not establish a theorem. Every target in this table
remains an open proof obligation in the Library snapshot above.

| Target | Proof task |
| --- | --- |
| `DynamicBaseSmoothConnectedStatement`: smoothness over every base, and geometric connectedness of `U`, or of `P/Z` when the ambient smooth affine group has geometrically connected fibres. | Task 5796, `ffe007f1-1aa4-45e2-ad56-034dbc85fd8d` |
| `DynamicBaseRepresentabilityStatement`: for affine locally finitely presented `G` over every base, construct locally finitely presented closed representatives of `P/U/Z`. | Task 5803, `d91e4b59-0554-47cb-9f11-91c2305ec6c5` |
| `DynamicBaseUnipotentFibresStatement`. | Task 5842, `9efa264a-5e00-4d98-a7b7-4e861cea8cba` |
| `DynamicRingLieStatement`: for every commutative ring and affine locally finitely presented group, identify the actual dual-number Lie kernels of `Z/P/U` with weight zero, nonnegative integer-power weights and positive integer-power weights. | Task 5859, `3e007f02-f19f-4a0b-99cb-1962f3bdf293` |
| `DynamicBaseOppositeCellStatement`. | Task 5929, `2c22dd75-7430-42f0-b98c-00cec63aad5c` |
| `DynamicFieldOppositeCellStatement`. | Task 6034, `b7260372-2d06-4bfd-803e-7e70c4213a47` |
| `DynamicBaseConnectedStatement`. | Task 6035, `d5f36233-3a61-4331-b962-53f2ae9b8736` |

The complete unreviewed parent draft revision 5 is at
`drafts/2b5e4a00-9d44-49a4-9c89-979fb5b6233e/revision-5-6b127473e49b8c9bbc5a810d19dc2c3f7ac17ab8959dd51d231dd0f46b782dfc/files`
under the project root. It contains complete draft proofs for Tasks 5796,
5842, 6034 and 6035. The last two modules were recompiled together with
zero errors or warnings in development check
`02ab3e33-7b1b-45b4-b8ae-218f7bb6b8ce`; inspection of
`dynamicBaseConnected` reported only `propext`, `Classical.choice` and
`Quot.sound`. This is a development result.

The field open-cell draft uses the published closed linear embedding and
diagonal-cocharacter open-cell theorems. The connectedness draft first
uses the rational unit to obtain geometric connectedness. Perfect-field
reduction gives irreducibility, which descends from an algebraic closure.
The field open cell then gives connectedness of `P`; the split limit map
gives connectedness of `Z`. Published unipotent connectedness and the
dynamic base-change identities assemble the arbitrary-base result.
This implemented route is described in the paired draft Markdown.

The connectedness draft imports the field open-cell proof. Task 6035
therefore records that Task 6034's proof must be independently accepted
and published before that imported module is used in a staged proof.
The already published dynamic base-change and scheme-decomposition
constructions remain available independently of these open proof tasks.

These updates remove the corresponding missing-statement entries in the
older ledgers. They leave their proof obligations and the other field,
relative, Galois, classification and example obligations of the standing
program intact.
