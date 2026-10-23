# NYLL finite local reciprocity: bounded port feasibility

Worker 25, 23 October 2026. This report implements unit 1 of the
[reviewed source audit](nyll-finite-local-reciprocity-audit.md#6-verdict-and-smallest-next-units),
for task `ece1c58f-95d0-4ad6-9ddd-adb07dc29028`, revision 1. Worker 215's audit
supplies the source map and follow-up plan; the closure reconstruction, adaptation
and build evidence here are Worker 25's work.

**Verdict: build-feasible at the approved pin, subject to separate mathematical
port acceptance and the explicit Library bridges below.** The unchanged
258-module `NormResidue` baseline failed with 14 errors in three modules.
After nine compatibility edits, all six selected roots compile with zero errors
and zero warnings. Their union contains 422 NYLL modules. No compilation blocker
remains in this bounded union. No external repository was installed in the
Library, and this report establishes none of the host finite reciprocity Props.

The builds are private development evidence. Independent review and publication
of this note assess the evidence and feasibility conclusion; they do not accept
422 modules of mathematics. Any future public port needs paired source
explanations, independent semantic review and the normal validation for each
focused contribution. A proof must name a previously published Prop target and
pass the Lake build and exact-target checks. No whole-repository build or
external Lean execution was used.

## 1. Pins, evidence and reproducibility

| Input | Exact identity |
| --- | --- |
| NYLL repository | `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709` |
| Upstream environment | Lean `4.35.0-rc2`; Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Approved environment | `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`; Lean `4.34.0` (commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`); Mathlib `5ed2965256430c3649e86755f9576b54eca72435` |
| Library interfaces compared | Commit `4fb020971c95d7e55757266feff9f2efdfcbbcdc` |
| Registered original | `external-lean-reuse-snapshots-2026-10-21`, fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01` |
| Registered supplement | `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330` |

The original is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The supplement was registered by the source audit. No matching source errata
file was found in the checked project notes. The prior audit's eleven-module
probes and upstream CI claims are distinct from this task's checks.

[The evidence index](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/INDEX.md) is immutable shared draft revision 3. Its manifest SHA-256 is
`e4bab331d2c067a9c16f5eeaaff28d23ef4e0c3cdd4ffd725f02c4c8a7749f1d`.
It retains exact requests, terminal records, failed attempts, input inventories,
patches, nine modified source texts, original license/notice, and declaration
output. These are unreviewed development records supporting this report, not
accepted mathematical dependencies. The diagnostic Lean/Markdown pair only
imports and prints declarations; the external 422 modules are intentionally
omitted from the shared draft, so that draft alone is not a compilable port.
The originals and final patch reconstruct its private build input.

`reconstruct.py` recursively follows ordinary `import` lines after removing
nested block and line comments. It rejects unsupported `module`/`public import`
syntax in the visited files. Each `Nyll.*` module is counted once, including the
root; non-NYLL imports are recorded separately. It compares each file's Git blob
SHA-1 (`blob <bytes>\0<contents>`) with the non-truncated retained Git tree for
the exact commit, then records the file SHA-256. The tree JSON SHA-256 is
`c4e52800231113cce45be53549b2a5c33c00bcb22f39f597edf6f10f7aaae2f8`.
The aggregate hashes below are SHA-256 of UTF-8 lines
`<file SHA-256><two spaces><relative path>\n`, sorted by module name.
This counts NYLL's textual closure; it does not count Mathlib's transitive closure.

Six verbatim copies remain in `.private/drafts/nyll-original-<root label>/`;
only `.private/drafts/nyll-adapted/` was patched. Every original copy was rehashed
after the builds and still matches its manifest. The scripts do not run Lean;
all compilation used `lean_check` in the approved environment.

## 2. Exact closures

The root labels in the tables expand as follows:

| Label | Full root |
| --- | --- |
| NormResidue | `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue` |
| GeneralTowerNaturality | `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality` |
| UnramifiedNormalization | `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization` |
| NormRestriction | `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction` |
| FiniteAbelian | `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.FiniteAbelian` |
| ShrinkTransport | `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport` |

| Root | NYLL modules | Direct external import names | Raw NYLL lines | Original aggregate SHA-256 |
| --- | ---: | ---: | ---: | --- |
| [NormResidue](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/NormResidue.json.md) | 258 | 155 | 115017 | `39215df33558965a5b76b252132893e8c8b3f6f3fdc806244e00be07b464af99` |
| [GeneralTowerNaturality](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/GeneralTowerNaturality.json.md) | 262 | 155 | 116062 | `cdb6b1b4c78832019a41f367c1637b4f063283faf1fab4c6cff7211d49eaec1b` |
| [UnramifiedNormalization](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/UnramifiedNormalization.json.md) | 265 | 156 | 117552 | `3fb23e5d2aebad36f78943af4c77a9efcc2c98458be52406f0baf919faef09cd` |
| [NormRestriction](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/NormRestriction.json.md) | 280 | 157 | 127365 | `2c258b23a697b32679a27466b9fa4100845ba82de9e68c30d23bcfd53e4ccfac` |
| [FiniteAbelian](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/FiniteAbelian.json.md) | 402 | 231 | 159883 | `fc6cbb36825d587af6bd5b03aec13bedee6c48eddf53b93b4cd7203388eb669f` |
| [ShrinkTransport](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/closures/ShrinkTransport.json.md) | 33 | 48 | 17506 | `afe753b75140f778828d07a89ab817802bf5f564ec2b4ff2417dd9da56ba149d` |

The closures are not nested. In the displayed order their contributions to the
union are 258, 4, 7, 19, 132 and 2 new modules. The union has 422 modules and
aggregate SHA-256
`579f3b4f6850af659cd5c29728dee728bab44b53f26723621bbb604612044676`.
Each linked manifest includes the complete file list, per-file hashes, Git blob
IDs, imports and dependency order. The final adapted input has these same NYLL
paths, with the nine changes in section 4; the diagnostic modules are additional
private tooling and are not included in the 422 count.

## 3. Complete check history

Every row links its exact request and full terminal result in the immutable
evidence. The private diagnostic record IDs are also retained for TaskHub lookup.
`E/W` means reported errors/warnings. Successful rows all have `ok: true`,
process return code 0 and `proof_accepted: false`.

| Run | Request / terminal result | Diagnostic ID | E/W | Outcome |
| --- | --- | --- | --- | --- |
| 01 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/01-NormResidue-original-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/01-NormResidue-original-result.json.md) | `3518572c-0e3e-4331-8296-deecbc34a65f` | 14/0 | Unchanged NormResidue failed: KummerDelta, HenselianFinite, ValuedAdicComplete. |
| 02 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/02-NormResidue-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/02-NormResidue-adapted-result.json.md) | `e42a2c92-b6f6-4d52-89c0-c0be90f3b1af` | 10/1 | Patch01 failed: additive-hom conversion selected incompatible integer-module instance. |
| 03 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/03-leaves-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/03-leaves-adapted-result.json.md) | `3034f7b6-e195-4d5f-a0fe-cb8592a4aa3e` | 0/0 | Patch02 edited leaves passed. |
| 04 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/04-NormResidue-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/04-NormResidue-adapted-result.json.md) | `fbc615a4-7128-4861-8eaa-08a7829afb72` | 0/0 | Adapted NormResidue passed; Artin-map inspection. |
| 05 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/05-GeneralTowerNaturality-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/05-GeneralTowerNaturality-adapted-result.json.md) | `ac4404d1-7fd2-48f9-9e57-aac7ca496e0a` | 0/0 | Adapted GeneralTowerNaturality passed; tower inspection. |
| 06 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/06-UnramifiedNormalization-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/06-UnramifiedNormalization-adapted-result.json.md) | `03328b94-6952-479d-a0d5-8bcbe008fd1c` | 0/0 | Adapted UnramifiedNormalization passed; residue-formula inspection. |
| 07 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/07-NormRestriction-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/07-NormRestriction-adapted-result.json.md) | `622c7107-58e0-41bb-8da9-052bf83e0d51` | 7/2 | NormRestriction failed: older Valuation.map API. |
| 08 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/08-NormRestriction-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/08-NormRestriction-adapted-result.json.md) | `d9110091-5de8-4d9b-baab-252705aa9ec4` | 1/2 | Patch03 failed: order isomorphism has no .monotone projection. |
| 08r | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/08r-resume-leaf-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/08r-resume-leaf-result.json.md) | `e658942d-51b1-4f4a-9f78-328b6d0d24ca` | 1/2 | Resume leaf check reproduced run08. |
| 09 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/09-NormRestriction-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/09-NormRestriction-adapted-result.json.md) | `73d11a28-2e1c-4841-b792-e89f51bf9497` | 1/1 | Patch04 failed: valuation-map simplification left surjectivity goal. |
| 10 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/10-NormRestriction-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/10-NormRestriction-adapted-result.json.md) | `02a32997-59b2-4f17-92e5-52cdb17c44ad` | 1/2 | Patch05 failed: adding map_apply did not discharge that goal. |
| 11 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/11-NormRestriction-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/11-NormRestriction-adapted-result.json.md) | `71921ef0-faa4-4432-8379-7da6777e63d9` | 0/0 | Patch06 NormRestriction passed; norm-square inspection. |
| 12 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/12-FiniteAbelian-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/12-FiniteAbelian-adapted-result.json.md) | `c2f17bd3-4316-4b28-858b-83b518a331d7` | 4/0 | FiniteAbelian failed: coe_ofClass name, valuation coercion, two consequent timeouts. |
| 13 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/13-FiniteAbelian-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/13-FiniteAbelian-adapted-result.json.md) | `1624549e-2f37-4720-ab4f-1a7574e6ded1` | 1/0 | Patch07 failed: missing Valuation.ofClass_eq_toMonoidWithZeroHom. |
| 14 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/14-FiniteAbelian-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/14-FiniteAbelian-adapted-result.json.md) | `eb59f77b-6d67-40ce-b68f-5e6131265e6c` | 1/0 | Patch08 failed: rewrite expected ofClass, not toMonoidWithZeroHom. |
| 15 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/15-FiniteAbelian-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/15-FiniteAbelian-adapted-result.json.md) | `7918c040-3243-4059-91c8-ed0940c6e2ec` | 5/0 | Patch09 failed: two further valuation coercions, consequent goal/timeouts. |
| 16 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/16-FiniteAbelian-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/16-FiniteAbelian-adapted-result.json.md) | `75a0948a-5e35-4372-85b2-cb780f0839e9` | 0/0 | Patch10 FiniteAbelian passed; filtered theorem inspection. |
| 17 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/17-ShrinkTransport-adapted-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/17-ShrinkTransport-adapted-result.json.md) | `3a0b7569-da78-4f54-a0e5-92268495c2f5` | 0/0 | ShrinkTransport passed; universe-polymorphic local-field instance inspection. |
| 18 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/18-Declarations-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/18-Declarations-result.json.md) | `ccb09f04-5bc8-4903-b5d5-c3566b6a5203` | 1/0 | Diagnostic failed only on unsupported pp.width option. |
| 19 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/19-Declarations-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/19-Declarations-result.json.md) | `e0d2ce20-20b3-46ac-bb8d-d5e0977a07e5` | 0/0 | Twelve complete binder signatures and transitive axiom lists passed. |
| 20 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/20-ExplicitDeclarations-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/20-ExplicitDeclarations-result.json.md) | `0df21ace-8798-4a8b-9f43-0f4334d362e5` | 0/0 | Same twelve with explicit implicit arguments passed. |
| 21 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/21-Declarations-resume-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/21-Declarations-resume-result.json.md) | `9ed9ccb3-ed5a-4cae-a3ce-2b8f22e4e4ae` | 0/0 | Resumed final six-root diagnostic passed; all 24 messages equal run19. |
| 22 | [request](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/22-Declarations-resume-request.json.md) / [result](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/receipts/22-Declarations-resume-result.json.md) | `2ffb9676-c4af-465a-8324-2ccace7df8ee` | 0/0 | Second resumed diagnostic passed; all 24 messages equal run19. |

Only run01 tested an unchanged selected root. Later roots were checked in the
adapted copy, including shared baseline fixes; they are not independent
unchanged-build successes. Runs04–17 requested the selected declaration for
inspection as well as the root build. Runs19–22 import all six roots in the final
adapted workspace. Their final signature checks use service compilation and
loaded dependencies; they are not a claim of a fresh uncached build of each
module on every run. No check was abandoned with its result unknown.

The per-run `*-inputs.json.md` files record cumulative adapted NYLL hashes where
present. For the initial runs, originals plus patches01/02 specify the source
changes; diagnostic source texts and both printers are retained separately.
Failed compiler diagnostics may contain Lean's recovery placeholder text; those
failures are retained as failures, not accepted source or proof evidence.
No proof holes were inserted into the port sources.

## 4. Compatibility changes and semantic assessment

[Patch10](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/patches/patch-10.diff.md) is the final cumulative nine-module diff (payload SHA-256
`385b2353d0b3a0942433de5adfa4ab948687e70a5f33790284973b584e52421b`).
Patches01–09 preserve intermediate attempts; patch03 contains only its new leaf
edit, whereas patch10 contains every final change. The inventory records both
original and final SHA-256 for each changed source. All changes retain the
original header and add an explicit Worker 25 modification notice.

Paths below are relative to `Nyll/`; the diff supplies exact original/adapted
line locations and the evidence's `modified/` directory supplies full texts.

| Module path without `.lean` | Break and final change | Assessment |
| --- | --- | --- |
| `GaloisCohomology/Kummer/Abstract/KummerDelta` | Six missing `AddMonoidHom.ofClass` uses become `AddMonoidHomClass.toAddMonoidHom wp.hom`. The first attempted coercion selected a different `ℤ`-module structure and failed. | Explicitly extracts the same additive map from `wp.hom`; no fixed subgroup, radical or kernel condition is changed. |
| `ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite` | Missing `IsConcreteLE.le_iff` is replaced by `change ¬ (∀ x, x ∈ I.map (algebraMap R S) → x ∈ Q) at hle`. | Unfolds the same ideal containment for the proof. |
| `ValuedFieldTheory/Valuation/ValuedAdicComplete` | The local `MulArchimedean` witness explicitly uses `(MonoidWithZeroHom.ofClass val).ValueGroup₀` and is installed with `let`. | Supplies the instance at the exact value-group type used by the older API. |
| `ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormalizedIntegerValuation` | Older `Valuation.map` needs the underlying hom and a separate monotonicity argument; use `MonoidWithZeroHom.ofClass e` and `e.toOrderIso.monotone`. Surjectivity uses `localIntegerValuation_apply`, the preimage equation, and `e.apply_symm_apply`. | Same value-group isomorphism and normalized valuation; explicit proof replaces unsuccessful simplification. |
| `ValuedFieldTheory/Ramification/LocalField/Core` | `MonoidHom.coe_ofClass` becomes the older `MonoidHom.coe_coe`. | Same coercion identity in the restriction proof. |
| `ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CyclicValueGroup` | Supply `MonoidWithZeroHom.ofClass v` in the value-group type and embedding. | Same valuation hom; resolves casts and associated heartbeat failures. |
| `ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CompleteRangeRestriction` | Delete the unavailable `Valuation.ofClass_eq_toMonoidWithZeroHom` rewrite. | The older generator theorem already uses `ofClass`; changing the expression to `toMonoidWithZeroHom` was the failed intermediate patch08. |
| `ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/UniformizerIntegerValuation` | Explicit `MonoidWithZeroHom.ofClass F.valuation` in two value-group membership expressions. | Same valuation and membership proof. |
| `ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/RangeRestrictedTopology` | Explicit `MonoidWithZeroHom.ofClass (Valued.v : Valuation ...)` for the value-group embedding. | Same embedding; resolves cast elaboration and associated heartbeat failures. |

These are assessed as API/elaboration adaptations. None changes a selected
reciprocity theorem's hypotheses or conclusion, and no new mathematical
assumption was added. The changed definition of `localIntegerValuation` retains
its original evaluation formula, which compiled in the target environment.
This assessment is based on the diff and successful checks, and still requires
independent semantic review in a public port. It is not a semantic audit of every
line of the 422-module dependency union. No heartbeat limit was increased.
The unsupported `pp.width` was only a diagnostic setting, removed before run19.

## 5. Attribution and proof-evidence limits

[The inventory verification](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/inventory-verification.json.md) records the following byte-level inventory. All 422 source files
have the same header: copyright 2026 Naganori Yamaguchi, Apache-2.0, authors
Naganori Yamaguchi (assisted by OpenAI Codex). Root `LICENSE` and `NOTICE` were
preserved in every original copy and the adapted workspace; verbatim copies are
in the shared evidence. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The root NOTICE inventory names 926 Lean paths. Five
`ANTHROPIC_FLT_SOURCE.md` tables list 908 paths in total: AlgebraicCurves 686,
ClassFieldTheory 2, ProCGroups 2, SchemeTheory 214, ValuedFieldTheory 4.
Both listed-path sets have empty intersection with this selected 422-module
union. No selected path is a Pi1 path. This is a scoped attribution inventory,
not a claim that NYLL as a whole has no third-party code. A future public subset
must preserve original headers, Apache license and applicable NOTICE material,
and record each modification and any additional imported attribution.

After removing comments, the adapted NYLL union has no token occurrences of
`sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern`,
`run_cmd` or `initialize`. This textual scan is not semantic validation.
The twelve selected declarations' transitive axiom lists are in the appendix:
all use only `propext`, `Classical.choice`, `Quot.sound`, except
`hasExtension_of_isEquiv`, which uses `propext` and `Quot.sound`.
This describes those selected dependencies, not an independent axioms inspection
of every declaration in the imported closure.

The diagnostic uses `#check` on the declarations themselves with
`pp.universes` and `pp.fullNames`; run20 additionally uses `pp.explicit`.
The printer can abbreviate proof terms. The evidence does not claim retention of
complete raw kernel-expression files: service inspections recorded expression
hashes and byte counts, while their temporary expression files were removed.
Likewise, `statement_returns_prop: false` in theorem/definition inspections is
not a failed validation of a submitted host Prop: none was submitted here.

## 6. Required Library adapters

The comparison is against the exact interfaces pinned in [the host-file inventory](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/host-files.json.md). The
unchanged host targets are
[`FiniteAbelianReciprocity`, `FiniteAbelianNormTransfer`, and `FiniteAbelianRestriction`](../../Langlands/ClassFieldTheory/Local/FiniteReciprocityStatement.lean)
in namespace `Langlands.LocalClassField`. They quantify over all primes and
independent field universes and, where used, arbitrary supplied `TF` and `TE`.
The following are future proof obligations, not accomplishments of this build.

1. **Actual norm quotient and its evaluation.** NYLL's
   `LocalFieldTheory.normUnits` is `Units.map (Algebra.norm K)`, and its
   `localNormSubgroup` is that map's range. This matches the actual subgroup in
   the host [`Norms`](../../Langlands/ClassFieldTheory/Local/Norms.lean) interface
   after unfolding and aligning finite-dimensional instances. Use NYLL's
   `abelianLocalArtinMap_ker` and surjectivity to descend the named continuous
   map, prove the quotient evaluation formula on `QuotientGroup.mk a`, and
   prove continuity of its inverse using the finite discrete Galois group.
   [`finiteNormResidueEquiv`](../../Langlands/ClassFieldTheory/Local/FiniteArtin.lean)
   already implements this first-isomorphism mechanism conditionally, but its
   extension argument is a `FiniteAbelianExtension K` in `AlgebraicClosure K`.
   A standalone `E.Carrier` is not that argument. Either transport it to the
   existing image-field index or apply the same quotient mechanism directly
   to the standalone extension and prove agreement. Reuse the existing
   `normQuotientTowerProjection` and `normQuotientTowerNorm` where applicable.
2. **One map throughout the finite family.** Use
   `LocalClassFieldTheory.abelianLocalArtinMap K L` for every quotient witness.
   `abelianLocalArtinMap_toMonoidHom` connects the continuous map to the
   algebraic map in the norm and filtration theorems. The compiled tower
   theorem supplies restriction for these exact maps; the compiled norm square
   supplies norm compatibility. Specialize its four-field square to a tower,
   prove the restriction/scalar-inclusion identifications, and use the norm of
   an included scalar (the degree power) for the host transfer formula.
   The audit's `transfer_of_norm` probe is prior evidence for that route, not a
   new host transfer proof here. Do not select unrelated existential maps for
   normalization, inertia and tower clauses.
3. **Geometric sign and residue formulation.** The required comparison is
   `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap F.Carrier
   (Additive.ofMul a) = - TF.ord (a : F.Carrier)` with the
   exact installed valuation. The audit's sign probe establishes its proposed
   formula in its tested setting; the public adapter must prove it for the
   supplied host data. If `TF.ord a = 1`, the input satisfying NYLL's
   `valuationMap π = 1` is `π = a⁻¹`. The compiled unramified theorem then acts
   by residue-cardinality power under `Artin(a⁻¹) = Artin(a)⁻¹`, which is the
   inverse automorphism in the host geometric clause. Identify NYLL's integer
   ring and residue map with those of `TF`/`TE`; `TF.residueCardinality` is
   `Nat.card TF.ResidueField`. Convert equality in the residue field to the
   host inequality `TE.discreteValuation (σ x - x^q) < 1` for integral `x`.
4. **Ramified normalization.** The printed normalization theorem assumes
   `IsUnramifiedValuedExtension K L`; the host reciprocity Prop does not.
   Construct the maximal unramified subextension in a finite abelian
   extension, prove its unramifiedness and residue-field identification with
   the full extension, and prove compatibility of residue action with
   restriction. Combine this with the same Artin family's tower theorem and
   the unramified formula. The six-root build alone does not provide this host
   ramified bridge. It needs a separate statement and proof.
5. **The `t = 0` inertia clause.** Specialize
   `finiteAbelian_filteredLocalReciprocity` at zero, identify its zeroth unit
   step using `LocalFieldTheory.principalUnits_zero`, and use
   `localUpperRamificationGroup_zero_eq_residue_ker`. The latter explicitly
   requires an extension valuation, integral closure and finiteness of the
   integer-ring module. Translate the valuation-ring units to
   `TF.ord a = 0`, the residue-kernel condition to the host congruence on every
   integral `x`, and carry the equality through the quotient evaluation lemma.
   A subgroup equality by itself is not the displayed host existential iff.
6. **Extension-field instances with the supplied data.** `TF` supplies the
   base topology, valuative relation and local-field instance. Normalization
   also needs an extension `UniformSpace` compatible with `TE.topology` and
   `IsUniformAddGroup`; norm and residue results need
   `Valuation.HasExtension (valuation F) (valuation E)`. Each host
   `TopologicalData` carries a valuative extension over `Padic p`; that alone
   is not the requested instance over the intermediate field `F`. Prove the
   compatibility through the tower, using uniqueness/comparison of extended
   valuations, and supply the integer-ring finiteness/integral-closure
   instances explicitly or through verified NYLL instances. The full printed
   types distinguish explicit binders from instances already elaborated into
   the terms; do not silently drop either.
7. **Independent universes and coherent transport.** The nine reciprocity/
   ramification declarations in the appendix are specialized to `Type 0`.
   `shrinkLocalField_isNonarchimedeanLocalField` has universe parameter `u_1`,
   and each printed `HasExtension` helper has six universe parameters. Their
   compiled availability does not transport the Artin family automatically.
   Use `Small.{0}`/`Shrink` models or another explicitly chosen universe-0
   model, transport compatible algebra structures along all field maps in a
   tower, and prove transport of units, norms, Galois automorphisms,
   restrictions, topology, valuation and residue action. Return the same
   family to arbitrary `F : Type u`, `E : Type v`, `L : Type w`.
   The published
   [`ExtensionFieldTransport`](../../Langlands/ClassFieldTheory/Local/ExtensionFieldTransport.lean)
   supplies `extensionFiniteIntermediate`, `extensionIntermediatePadicEquiv`
   and `extensionIntermediateUnitsEquiv` for an image field in
   `AlgebraicClosure F.Carrier`; it stays in the universe of `F` and so does
   not alone solve the universe-0 reduction. The published
   [`ExtensionValuationTransport`](../../Langlands/ClassFieldTheory/Local/ExtensionValuationTransport.lean)
   and [`CanonicalTransport`](../../Langlands/LocalField/CanonicalTransport.lean)
   provide residue-cardinality, order and valuation identities for canonical
   topological data. The target quantifies over arbitrary `TF` and `TE`;
   comparison with those canonical data remains necessary.

## 7. Small public boundaries and retained follow-up plan

Unit 1 has resolved the compilation uncertainty. It has not chosen the public
architecture. Worker 0 and owners 21, 42, 49, 45 and 4 must make unit 2's explicit
decision using this report: a separate namespaced construction alongside the
cohomological route, or use of NYLL as a proof route. Their earlier in-principle
agreement authorized these private checks only. Existing construction,
class-formation and cup/transfer ownership stays in place.

If that decision authorizes a port, submit focused dependency-first units.
The smallest evidenced compatibility boundaries are the nine source modules in
section 4; group only tightly related small leaves, each with its own paired
explanation and relevant Prop targets for proofs. The 422-module union is a
build input, not one reviewable public contribution. Unchanged dependencies
also need reviewable boundaries and original-source correspondence. The closure
manifests permit an exact dependency-first partition: the initial 258 modules
must be divided into definitions, statements and proofs; subsequent root stages
add 4, 7, 19, 132 and 2 new modules respectively. Those counts are incremental
build scope, not suitable automatic review-unit sizes. Keep the norm quotient,
map evaluation, tower, norm square, residue and inertia adapters separately
reviewable. Choose any smaller replacement proof route only after a new focused
check; no smaller import closure is claimed here.

Retain all remaining audit section 6 units in this order:

1. Make the unit 2 owner decision, then separately authorize the necessary
   public definition/statement/proof tasks. Existing host definitions and exact
   target statements stay unchanged.
2. Publish Prop-valued targets for the `Type 0` instances
   `FiniteAbelianReciprocity.{0,0}`, `FiniteAbelianNormTransfer.{0,0,0}` and
   `FiniteAbelianRestriction.{0,0,0}`, the implication to their
   arbitrary-universe counterparts, and ramified residue normalization via
   the maximal unramified subextension. Define required adapters first.
3. After the relevant port dependencies have independent acceptance and
   publication, prove the norm-quotient equivalences with evaluation on the
   named Artin map, then the universe-0 restriction theorem, then norm/transfer.
4. Prove geometric residue normalization for unramified extensions and then
   the ramified case, followed by the `t = 0` inertia clause.
5. Prove the universe-transport implication and assemble the arbitrary-universe
   host Props. Every proof task names an already published Prop declaration.

NYLL's class-field axiom does not discharge the project's class formation,
one simultaneous invariant family, relative fundamental classes, genuine
cup/transfer, ordinary-cochain/Tate comparison or absolute corestriction
obligations. Equality with `geometricReciprocityOfCup` requires a separate
proved comparison if consumed later. There is no Weil-group component here,
so no `ReciprocitySystemStatement` or common-closure/Weil coherent system follows.
Historical task `7b4a513d-a3bc-4cb7-af3c-03c4580608f7` was absent in the owner's
checks; the active construction owner is Worker 21 on
`6abce376-f18c-478f-9309-c0c1010f7a99`. This report invents no task migration.

## Appendix. Selected full binder types, universes and axioms

Original declaration locations at the NYLL pin are listed below. Root labels
refer to the exact paths corresponding to section 2's full module names.
The selected declaration modules themselves were unchanged by patch10.

| Declaration (namespace as printed below) | Original source location |
| --- | --- |
| `abelianLocalArtinMap` | `NormResidue.lean:78` |
| `abelianLocalArtinMap_toMonoidHom` | `NormResidue.lean:86` |
| `abelianLocalArtinMap_surjective` | `NormResidue.lean:98` |
| `abelianLocalArtinMap_ker` | `NormResidue.lean:105` |
| `finiteAbelianLocalArtinMap_restrict_tower` | `GeneralTowerNaturality.lean:468` |
| `finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow` | `UnramifiedNormalization.lean:561` |
| `abelianLocalArtinMonoidHom_norm_restriction` | `NormRestriction.lean:686` |
| `finiteAbelian_filteredLocalReciprocity` | `FiniteAbelian.lean:41` |
| `localUpperRamificationGroup_zero_eq_residue_ker` | `Nyll/ValuedFieldTheory/Ramification/LocalField/ResidueInertia.lean:97` |
| `shrinkLocalField_isNonarchimedeanLocalField` | `ShrinkTransport.lean:192` |
| `hasExtension_comap_ringEquivs` | `ShrinkTransport.lean:210` |
| `hasExtension_of_isEquiv` | `ShrinkTransport.lean:234` |

Additional source locations for the adapters are
`Nyll/ValuedFieldTheory/LocalField/NormUnits.lean:33` (the norm on units),
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean:27`
(the norm subgroup), `ValuationExactSequence.lean:39` and `:283` in the same
directory (valuation map and integer-unit image), `PrincipalUnits.lean:73`
there (zeroth unit group), and
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:107`
(the Artin image of the real-indexed unit step). Section 4's diff gives the
exact changed-source locations and preserves their original headers.

The following is the verbatim successful run19 output. Runs21 and22 produced
the same 24 messages. The evidence also retains one file per declaration under
`binder-signatures/`, and run20's expanded `pp.explicit` output under
`explicit-signatures/`, with payload hashes in its index. These are complete
binder types with universe annotations; implicit term arguments are visible in
the expanded version, and printer-elided proof terms remain subject to the
limitations in section 5. In particular, an available helper with general
universes does not make a `Type 0` Artin declaration universe-polymorphic.

```text
LocalClassFieldTheory.abelianLocalArtinMap : (K L : Type) →
  [inst : Field.{0} K] →
    [inst_1 : Field.{0} L] →
      [inst_2 : Algebra.{0, 0} K L] →
        [inst_3 : ValuativeRel.{0} K] →
          [inst_4 : TopologicalSpace.{0} K] →
            [IsNonarchimedeanLocalField.{0} K] →
              [FiniteDimensional.{0, 0} K L] →
                [IsAbelianGalois.{0, 0} K L] → ContinuousMonoidHom.{0, 0} (Units.{0} K) Gal(L/K)

'LocalClassFieldTheory.abelianLocalArtinMap' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]

LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom : ∀ (K L : Type) [inst : Field.{0} K] [inst_1 : Field.{0} L]
  [inst_2 : Algebra.{0, 0} K L] [inst_3 : ValuativeRel.{0} K] [inst_4 : TopologicalSpace.{0} K]
  [inst_5 : IsNonarchimedeanLocalField.{0} K] [inst_6 : FiniteDimensional.{0, 0} K L]
  [inst_7 : IsAbelianGalois.{0, 0} K L],
  Eq.{1} (ContinuousMonoidHom.toMonoidHom.{0, 0} (LocalClassFieldTheory.abelianLocalArtinMap K L))
    (LocalClassFieldTheory.abelianLocalArtinMonoidHom K L)

'LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

LocalClassFieldTheory.abelianLocalArtinMap_surjective : ∀ (K L : Type) [inst : Field.{0} K] [inst_1 : Field.{0} L]
  [inst_2 : Algebra.{0, 0} K L] [inst_3 : ValuativeRel.{0} K] [inst_4 : TopologicalSpace.{0} K]
  [inst_5 : IsNonarchimedeanLocalField.{0} K] [inst_6 : FiniteDimensional.{0, 0} K L]
  [inst_7 : IsAbelianGalois.{0, 0} K L], Function.Surjective.{1, 1} ⇑(LocalClassFieldTheory.abelianLocalArtinMap K L)

'LocalClassFieldTheory.abelianLocalArtinMap_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

LocalClassFieldTheory.abelianLocalArtinMap_ker : ∀ (K L : Type) [inst : Field.{0} K] [inst_1 : Field.{0} L]
  [inst_2 : Algebra.{0, 0} K L] [inst_3 : ValuativeRel.{0} K] [inst_4 : TopologicalSpace.{0} K]
  [inst_5 : IsNonarchimedeanLocalField.{0} K] [inst_6 : FiniteDimensional.{0, 0} K L]
  [inst_7 : IsAbelianGalois.{0, 0} K L],
  Eq.{1}
    (MonoidHom.ker.{0, 0} (ContinuousMonoidHom.toMonoidHom.{0, 0} (LocalClassFieldTheory.abelianLocalArtinMap K L)))
    (LocalFieldTheory.localNormSubgroup.{0} K L)

'LocalClassFieldTheory.abelianLocalArtinMap_ker' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]

ClassFieldTheory.finiteAbelianLocalArtinMap_restrict_tower : ∀ (K E L : Type) [inst : Field.{0} K]
  [inst_1 : Field.{0} E] [inst_2 : Field.{0} L] [inst_3 : Algebra.{0, 0} K E] [inst_4 : Algebra.{0, 0} E L]
  [inst_5 : Algebra.{0, 0} K L] [inst_6 : IsScalarTower.{0, 0, 0} K E L] [inst_7 : FiniteDimensional.{0, 0} K E]
  [inst_8 : FiniteDimensional.{0, 0} K L] [inst_9 : IsAbelianGalois.{0, 0} K E] [inst_10 : IsAbelianGalois.{0, 0} K L]
  [inst_11 : ValuativeRel.{0} K] [inst_12 : TopologicalSpace.{0} K] [inst_13 : IsNonarchimedeanLocalField.{0} K],
  Eq.{1}
    (MonoidHom.comp.{0, 0, 0} (AlgEquiv.restrictNormalHom.{0, 0, 0} E)
      (ContinuousMonoidHom.toMonoidHom.{0, 0} (LocalClassFieldTheory.abelianLocalArtinMap K L)))
    (ContinuousMonoidHom.toMonoidHom.{0, 0} (LocalClassFieldTheory.abelianLocalArtinMap K E))

'ClassFieldTheory.finiteAbelianLocalArtinMap_restrict_tower' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow : ∀ (K L : Type) [inst : Field.{0} K]
  [inst_1 : ValuativeRel.{0} K] [inst_2 : TopologicalSpace.{0} K] [inst_3 : IsNonarchimedeanLocalField.{0} K]
  [inst_4 : Field.{0} L] [inst_5 : ValuativeRel.{0} L] [inst_6 : UniformSpace.{0} L] [IsUniformAddGroup.{0} L]
  [inst_8 : IsNonarchimedeanLocalField.{0} L] [inst_9 : Algebra.{0, 0} K L] [inst_10 : FiniteDimensional.{0, 0} K L]
  [inst_11 : IsAbelianGalois.{0, 0} K L]
  [inst_12 : Valuation.HasExtension.{0, 0, 0, 0} (ValuativeRel.valuation.{0} K) (ValuativeRel.valuation.{0} L)]
  [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension.{0} K L] (π : Units.{0} K),
  Eq.{1} ((LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap.{0} K) (Additive.ofMul.{0} π)) 1 →
    ∀ (x : ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} L))),
      ∃ z,
        Eq.{1} (↑z) (((LocalClassFieldTheory.abelianLocalArtinMap K L) π) ↑x) ∧
          Eq.{1} ((IsLocalRing.residue.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} L))) z)
            (HPow.hPow.{0, 0, 0}
              ((IsLocalRing.residue.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} L))) x)
              (Nat.card.{0} (IsLocalRing.ResidueField.{0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K)))))

'ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction : ∀ (K K' L L' : Type) [inst : Field.{0} K]
  [inst_1 : ValuativeRel.{0} K] [inst_2 : TopologicalSpace.{0} K] [inst_3 : IsNonarchimedeanLocalField.{0} K]
  [inst_4 : Field.{0} K'] [inst_5 : ValuativeRel.{0} K'] [inst_6 : TopologicalSpace.{0} K']
  [inst_7 : IsNonarchimedeanLocalField.{0} K'] [inst_8 : Field.{0} L] [inst_9 : Field.{0} L']
  [inst_10 : Algebra.{0, 0} K K'] [inst_11 : Algebra.{0, 0} K L] [inst_12 : Algebra.{0, 0} K L']
  [inst_13 : Algebra.{0, 0} K' L'] [inst_14 : Algebra.{0, 0} L L'] [inst_15 : IsScalarTower.{0, 0, 0} K K' L']
  [inst_16 : IsScalarTower.{0, 0, 0} K L L'] [FiniteDimensional.{0, 0} K K'] [Algebra.IsSeparable.{0, 0} K K']
  [Valuation.HasExtension.{0, 0, 0, 0} (ValuativeRel.valuation.{0} K) (ValuativeRel.valuation.{0} K')]
  [inst_20 : FiniteDimensional.{0, 0} K L] [inst_21 : IsAbelianGalois.{0, 0} K L]
  [inst_22 : FiniteDimensional.{0, 0} K' L'] [inst_23 : IsAbelianGalois.{0, 0} K' L'],
  Eq.{1}
    (MonoidHom.comp.{0, 0, 0}
      (MonoidHom.comp.{0, 0, 0} (AlgEquiv.restrictNormalHom.{0, 0, 0} L) (AlgEquiv.restrictScalarsHom.{0, 0, 0} K))
      (LocalClassFieldTheory.abelianLocalArtinMonoidHom K' L'))
    (MonoidHom.comp.{0, 0, 0} (LocalClassFieldTheory.abelianLocalArtinMonoidHom K L)
      (LocalFieldTheory.normUnits.{0, 0} K K'))

'LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity : ∀ (K L : Type) [inst : Field.{0} K]
  [inst_1 : Field.{0} L] [inst_2 : Algebra.{0, 0} K L] [inst_3 : ValuativeRel.{0} K] [inst_4 : TopologicalSpace.{0} K]
  [inst_5 : IsNonarchimedeanLocalField.{0} K] [inst_6 : FiniteDimensional.{0, 0} K L]
  [inst_7 : IsAbelianGalois.{0, 0} K L] (t : ℝ),
  LE.le.{0} 0 t →
    Eq.{1} (LocalClassFieldTheory.artinPrincipalUnitStepGroup K L t)
      (RamificationTheory.LocalField.localUpperRamificationGroup K L t)

'LocalClassFieldTheory.finiteAbelian_filteredLocalReciprocity' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker : ∀ (K L : Type) [inst : Field.{0} K]
  [inst_1 : ValuativeRel.{0} K] [inst_2 : TopologicalSpace.{0} K] [inst_3 : IsNonarchimedeanLocalField.{0} K]
  [inst_4 : Field.{0} L] [inst_5 : ValuativeRel.{0} L] [inst_6 : TopologicalSpace.{0} L]
  [IsNonarchimedeanLocalField.{0} L] [inst_8 : Algebra.{0, 0} K L] [inst_9 : FiniteDimensional.{0, 0} K L]
  [inst_10 : IsGalois.{0, 0} K L]
  [inst_11 : Valuation.HasExtension.{0, 0, 0, 0} (ValuativeRel.valuation.{0} K) (ValuativeRel.valuation.{0} L)]
  [inst_12 :
    IsIntegralClosure.{0, 0, 0} (↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} L)))
      (↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))) L]
  [Module.Finite.{0, 0} ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} K))
      ↥(Valuation.integer.{0, 0} (ValuativeRel.valuation.{0} L))],
  Eq.{1} (RamificationTheory.LocalField.localUpperRamificationGroup K L 0)
    (MonoidHom.ker.{0, 0} (LocalFieldTheory.galoisGroupResidueAlgEquivHomOfIsIntegralClosure.{0} K L))

'RamificationTheory.LocalField.localUpperRamificationGroup_zero_eq_residue_ker' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField.{u_1} : ∀ (K : Type u_1) [inst : Field.{u_1} K]
  [inst_1 : ValuativeRel.{u_1} K] [inst_2 : TopologicalSpace.{u_1} K] [inst_3 : IsNonarchimedeanLocalField.{u_1} K],
  IsNonarchimedeanLocalField.{0} (Shrink.{0, u_1} K)

'LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

@LocalFieldTheory.hasExtension_comap_ringEquivs.{u_1, u_2, u_3, u_4, u_5,
    u_6} : ∀ {F : Type u_1} {G : Type u_2} {F₀ : Type u_3} {G₀ : Type u_4} [inst : Field.{u_1} F]
  [inst_1 : Field.{u_2} G] [inst_2 : Field.{u_3} F₀] [inst_3 : Field.{u_4} G₀] [inst_4 : Algebra.{u_1, u_2} F G]
  [inst_5 : Algebra.{u_3, u_4} F₀ G₀] {ΓF : Type u_5} {ΓG : Type u_6} [inst_6 : LinearOrderedCommGroupWithZero.{u_5} ΓF]
  [inst_7 : LinearOrderedCommGroupWithZero.{u_6} ΓG] (eF : RingEquiv.{u_3, u_1} F₀ F) (eG : RingEquiv.{u_4, u_2} G₀ G),
  (∀ (a : F₀),
      Eq.{u_2 + 1} (eG ((Algebra.algebraMap.{u_3, u_4} F₀ G₀) a)) ((Algebra.algebraMap.{u_1, u_2} F G) (eF a))) →
    ∀ (vF : Valuation.{u_1, u_5} F ΓF) (vG : Valuation.{u_2, u_6} G ΓG)
      [Valuation.HasExtension.{u_1, u_2, u_5, u_6} vF vG],
      Valuation.HasExtension.{u_3, u_4, u_5, u_6}
        (Valuation.comap.{u_1, u_5, u_3} (RingEquiv.toRingHom.{u_3, u_1} eF) vF)
        (Valuation.comap.{u_2, u_6, u_4} (RingEquiv.toRingHom.{u_4, u_2} eG) vG)

'LocalFieldTheory.hasExtension_comap_ringEquivs' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]

@LocalFieldTheory.hasExtension_of_isEquiv.{u_1, u_2, u_3, u_4, u_5,
    u_6} : ∀ {F : Type u_1} {G : Type u_2} [inst : CommRing.{u_1} F] [inst_1 : Ring.{u_2} G]
  [inst_2 : Algebra.{u_1, u_2} F G] {ΓF : Type u_3} {ΓF' : Type u_4} {ΓG : Type u_5} {ΓG' : Type u_6}
  [inst_3 : LinearOrderedCommMonoidWithZero.{u_3} ΓF] [inst_4 : LinearOrderedCommMonoidWithZero.{u_4} ΓF']
  [inst_5 : LinearOrderedCommMonoidWithZero.{u_5} ΓG] [inst_6 : LinearOrderedCommMonoidWithZero.{u_6} ΓG']
  (vF : Valuation.{u_1, u_3} F ΓF) (vF' : Valuation.{u_1, u_4} F ΓF') (vG : Valuation.{u_2, u_5} G ΓG)
  (vG' : Valuation.{u_2, u_6} G ΓG') [Valuation.HasExtension.{u_1, u_2, u_3, u_5} vF vG],
  Valuation.IsEquiv.{u_1, u_3, u_4} vF vF' →
    Valuation.IsEquiv.{u_2, u_5, u_6} vG vG' → Valuation.HasExtension.{u_1, u_2, u_4, u_6} vF' vG'

'LocalFieldTheory.hasExtension_of_isEquiv' depends on axioms: [propext, Quot.sound.{u}]
```
