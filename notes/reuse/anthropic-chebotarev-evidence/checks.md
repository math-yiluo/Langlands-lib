# Check history and evidence limits

| Check | Diagnostic ID | Result | Errors / warnings |
|---|---|---|---|
| [01](check-01.md) | `07aee092-cb40-4afb-816d-1c786096ccd1` | failed | 15 / 224 |
| [02](check-02.md) | `5b25ca0b-4185-4f1f-8188-b5c676a3e634` | failed | 4 / 271 |
| [03](check-03.md) | `8acf1d36-4a1b-4020-a2b3-31eb70b12416` | failed | 4 / 146 |
| [04](check-04.md) | `c63e28d8-0eb4-45d9-ac99-838091d195e6` | passed | 0 / 197 |
| [05](check-05.md) | `e36e544d-3d25-46a7-b17c-a937c7d92222` | failed | 3 / 298 |
| [06](check-06.md) | `236711df-e7dd-48c0-acaf-17d1319e700c` | passed | 0 / 197 |
| [07](check-07.md) | `757330b8-54ac-4991-946b-715acaa49b82` | failed | 1 / 14 |
| [08](check-08.md) | `b294069f-9f5a-4e1a-8390-d6b23f7e73b1` | passed | 0 / 52 |
| [09](check-09.md) | `36e1cd6c-0f83-4099-8a9c-309f1370f503` | passed | 0 / 0 |
| [10](check-10.md) | `53193736-afc0-4619-a896-8979e5b75820` | passed | 0 / 0 |
| [11](check-11.md) | `2993c8d4-bbcd-4c5e-90a9-57024b5c3848` | failed | 4 / 3 |
| [12](check-12.md) | `0744779c-80b8-4f7c-8a07-15813987b581` | failed | 1 / 6 |
| [13](check-13.md) | `49fceb20-0d25-49a6-83b9-924eeaf89b42` | passed | 0 / 6 |
| [14](check-14.md) | `314f5cb8-bf3a-4c2d-8e7c-d78f09fd8616` | passed | 0 / 3 |
| [15](check-15.md) | `2043e15a-b9bc-402a-b16a-5ce11086b655` | passed | 0 / 4 |
| [16](check-16.md) | `aab56eab-d617-463b-837e-0916d858532d` | passed | 0 / 0 |
| [17](check-17.md) | `93a2cbec-84ae-4224-820d-f5eaad9bb4ed` | passed | 0 / 0 |

# Worker 159: terminal check history

Terminal machine evidence, official full JSON under `.private/notes/records/<id>.json`:
- Original **07aee092-cb40-4afb-816d-1c786096ccd1** fails 15 errors.
- Patched attempts **5b25ca0b-4185-4f1f-8188-b5c676a3e634**, **8acf1d36-4a1b-4020-a2b3-31eb70b12416** each fail4. Raising heartbeat to1,600,000 failed; removed.
- Patched **c63e28d8-0eb4-45d9-ac99-838091d195e6** succeeds, 0 errors/197 warnings, level_parameters=[], axioms only propext/Classical.choice/Quot.sound. sources_sha256 87c56f13aeb58d94e73869e13e239476afc2c3a119f2233c80c471659db1cb45.
- First universe **e36e544d-3d25-46a7-b17c-a937c7d92222** fails3 at two existential index universes and consumer. Pinned `∃ (ι : Type audit_u)` in complete private theorems hole_T2/hole_top, whose witnesses are ClassGroup(𝓞 K). These names do NOT denote proof holes.
- Universe **236711df-e7dd-48c0-acaf-17d1319e700c** succeeds0/197; root level_parameters=[audit_u,audit_v], standard3 axioms; sources_sha256 2ff4349cbb15d238016d719cbec8a76ee9e31bfbd066c08b067f65b43baa8546.
- First clean **757330b8-54ac-4991-946b-715acaa49b82** fails1: apply cannot infer cyclotomic m, fixed by named `(m := m)` in four wrappers.
- Clean **b294069f-9f5a-4e1a-8390-d6b23f7e73b1** succeeds0/52 (incremental downstream build), independent audit_u/audit_v, standard3 axioms; sources_sha256 607aec98a3f26606b7feac7b09a6addcd99fddd8dba3b3f9e2e2f71004ff2e95. Root type hash **3947a480b5b576718094cd7dba79d66c903b9e17396b4d9146cfba4c005318fc**, identical to universe version.
- stdout including full pretty root type/universes and #print axioms saved root-compatibility-output.txt, root-universes-output.txt, root-cleaned-output.txt in chebotarev notes. Structured inspection retains repr hash/bytes; transient service scratch expression path has been deleted (do not claim local raw repr file retained).
**All checks terminal; no processes running. proof_accepted=false throughout; no target match/semantic acceptance/publication.**


## Restoration check

Check 17 recompiles the unchanged AuditInspection module after context rotation at Library base `6066ffe8da8e977f40af9c75eda35cdbe1989d74`. It reports zero errors/warnings, independent `audit_u`/`audit_v`, the same root type fingerprint and the three standard axioms. All nine compared Library files still byte-match; no adapter or target source changed.

## Bridge continuation

Checks 11 and 12 fail on interface elaboration; check 13 passes all four ideal, avoidance, unramifiedness and completion lemmas. Check 14 passes base residue cardinality and relative Frobenius. Check 15 passes the assembled unchanged realization proposition. Check 16 prints the full universe-explicit source and all seven adapter types plus their axioms, and reinspects the source root. Raw expression files were transient service scratch output and are unavailable; exact repr hashes/byte lengths and readable types are retained in the terminal reports. No target-specific receipt or independent semantic acceptance is claimed.

Historical source snapshots for every failed intermediate edit were not all retained. Their exact terminal diagnostics are retained; the final successful stage patches and bridge sources are fully reconstructible. The failed first bridge can be reconstructed from the final bridge by reverting Pointwise scope, the reversed over_def and the local Subsingleton instance.

## Cancelled service operation

The earlier transport timeout job `859338cca2684d00850aa42d8dd6e14e` was reconciled to terminal done/cancelled before it started. It produced no mathematical result. The read-only service record retained at the time follows.

```json
{
  "id": "859338cca2684d00850aa42d8dd6e14e",
  "content_key": null,
  "estimate_key": "7127e7f5594a08c127c2347a305684a87532948d0cd5b62ed322fb85ba0aeb85",
  "lane": "interactive",
  "kind": "check",
  "owner": "f9654ee6-b957-4264-a7d0-b291b3fcc8d3",
  "label": "lean_check AuditRoot",
  "blocking": 0,
  "spec_json": "{\"kind\":\"check\",\"lane\":\"interactive\",\"owner\":\"f9654ee6-b957-4264-a7d0-b291b3fcc8d3\",\"label\":\"lean_check AuditRoot\",\"blocking\":false,\"request\":{\"environment\":{\"schema_version\":1,\"name\":\"Pinned Lean 4.34.0 and mathlib 5ed296525643\",\"version\":1,\"supersedes\":null,\"qualifications\":[],\"object_type\":\"environment\",\"lean_executable\":\"/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean\",\"lean_executable_sha256\":\"e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550\",\"lean_version\":\"Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)\",\"lake_executable_sha256\":\"6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d\",\"library_roots\":[{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean\",\"manifest_sha256\":\"e6f54197957fdfee0fddf7f171116e1453b8d071eaeb4e843c429b86c7f518c6\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean\",\"manifest_sha256\":\"6205e61c3a468bdc58c19ff7e9128fd68f3f1d7f48dbd8492f69c16a79b06377\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean\",\"manifest_sha256\":\"74809069994f9c475a5fe99475ae72a84b19139ed1ae3c30dc7c5fa01da8b620\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean\",\"manifest_sha256\":\"7d65def5ba5901be5f2a5a7c2f3c950e4609936f51b92682d7f24656b57e2fff\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean\",\"manifest_sha256\":\"9a24afec51a00531cd7453c59c3173ba92a3700ca3d474e95c55137d6983399d\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean\",\"manifest_sha256\":\"a505ef2805fbb9cfadfaefcf7e34c7481a57c3cd0bf54253a0ae3d3a48f106fd\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean\",\"manifest_sha256\":\"e29bcc0c91ae387860b32bbddae45ddd0c4bb9aea4462363775cd82bf4ee5e2b\"},{\"path\":\"/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean\",\"manifest_sha256\":\"2ea475f10f25c1213494db44b83d3fe41e2cdacd42390369494280904d8af63f\"}],\"allowed_axioms\":[\"propext\",\"Classical.choice\",\"Quot.sound\"],\"local_execution\":\"trusted-code-only\",\"limits\":{\"timeout_seconds\":null,\"output_bytes\":1048576,\"snapshot_bytes\":1073741824,\"snapshot_files\":20000}},\"blobs\":\"/home/taskhub/pilot/.task-based/objects/sha256\",\"snapshot\":null,\"directory\":\"/home/taskhub/pilot/.task-based/workers/f9654ee6-b957-4264-a7d0-b291b3fcc8d3/work\",\"overlay\":\"/home/taskhub/pilot/.task-based/workers/f9654ee6-b957-4264-a7d0-b291b3fcc8d3/work/.private/drafts/chebotarev-patched\",\"modules\":[\"AuditRoot\"],\"kernel_replay\":false,\"inspections\":[{\"module\":\"AuditRoot\",\"declaration\":\"NumberField.exists_prime_isArithFrobAt_of_isGalois\",\"statement\":null}]}}",
  "state": "done",
  "outcome": "cancelled",
  "result_json": null,
  "definitive": 0,
  "submitted_at": 1792936337.636406,
  "started_at": null,
  "finished_at": 1792936523.9553394,
  "last_polled_at": 1792936337.636406,
  "threads": 0,
  "requeues": 0,
  "suspensions": 0,
  "suspended_seconds": 0.0,
  "queue_seconds": null,
  "run_seconds": null,
  "cpu_seconds": 0.0,
  "peak_private_memory": null,
  "peak_committed_memory": null
}
```

## root-compatibility-output.txt

```text
✔ [29/43] Built P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (17s)
✔ [30/43] Built Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO (10s)
⚠ [31/43] Built P2M.Sol.S_M4aTorus_completedRayL_fe (363s)
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:149:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:153:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:521:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:569:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:605:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1074:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1292:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1293:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1358:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2863:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2864:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3005:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3074:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3469:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3475:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3479:60: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3501:24: This simp argument is unused:
  smul_eq_mul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3500:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4841:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4877:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4886:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5271:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:37: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5280:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5285:10: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5315:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5482:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5484:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5506:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5515:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5757:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5802:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5815:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5821:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5826:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5857:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5978:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6137:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6138:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6164:51: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6165:78: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6246:17: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6257:75: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6263:15: `if_true` has been deprecated: Use `ite_true` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6486:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:23: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:19: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:44: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7039:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7203:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7207:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7712:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7720:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8293:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:28: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:40: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8479:28: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8622:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8624:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8754:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8756:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8872:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8873:16: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9050:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9442:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9451:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9451:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9455:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9455:19: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9569:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9569:32: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9579:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9579:32: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9588:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9632:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9639:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9639:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:23: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9725:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9733:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9733:27: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9738:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9739:6: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9906:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9931:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9927:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9932:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9983:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9983:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10010:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10011:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10057:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10057:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10262:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10262:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10459:28: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10606:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10608:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10635:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10637:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10676:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10775:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10776:16: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10851:53: `if_true` has been deprecated: Use `ite_true` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10857:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10925:24: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11129:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12050:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12051:4: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12070:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12119:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [32/43] Built Theorems.Thm_M4aTorus_completedRayL_fe (25s)
warning: source/Theorems/Thm_M4aTorus_completedRayL_fe.lean:18:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [33/43] Built P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (18s)
✔ [34/43] Built Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (9.4s)
⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (61s)
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:54:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:63:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:102:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:159:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:200:40: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:208:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:215:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:247:10: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:320:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:320:18: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:321:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:321:18: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:335:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:335:20: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:336:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:336:20: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:362:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:367:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:652:14: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:653:14: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:703:17: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (75s)
⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (83s)
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:34:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:36:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:91:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:91:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:98:54: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (34s)
⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (19s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:76:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:104:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:120:18: This simp argument is unused:
  hζ.coe_toInteger

Hint: Omit it from the simp argument list.
  [apply] simp [hζ'def] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:144:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (9.0s)
⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (24s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:67:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:68:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:90:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:119:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:203:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:204:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:305:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:343:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:344:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:386:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:387:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:390:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:394:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:403:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:404:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:416:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:417:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:418:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
✔ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (8.8s)
ℹ [43/43] Built AuditRoot (15s)
info: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois : ∀ (K L : Type) [inst : Field.{0} K] [NumberField.{0} K]
  [inst_2 : Field.{0} L] [NumberField.{0} L] [inst_4 : Algebra.{0, 0} K L] [IsGalois.{0, 0} K L] (σ : Gal(L/K))
  (S : Finset.{0} ℕ),
  ∃ p, Nat.Prime p ∧ p ∉ S ∧ ∃ P, Ideal.IsMaximal.{0} P ∧ Membership.mem.{0, 0} P ↑p ∧ IsArithFrobAt.{0, 0, 0} ℤ σ P
info: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (43 jobs).

STDERR
```

## root-universes-output.txt

```text
⚠ [31/43] Built P2M.Sol.S_M4aTorus_completedRayL_fe (324s)
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:152:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:156:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:524:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:572:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:608:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1077:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1295:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1296:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1361:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2491:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2866:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2867:2: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3008:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3077:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3472:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3481:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3482:60: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3504:24: This simp argument is unused:
  smul_eq_mul

Hint: Omit it from the simp argument list.
  [apply] simp only [smul_smul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3503:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4199:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4844:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4880:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4889:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5277:37: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5283:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5288:10: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5318:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5485:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5487:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5509:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5518:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5760:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5805:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5818:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5824:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5829:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5860:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5981:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6140:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6141:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6167:51: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6168:78: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6249:17: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6260:75: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6266:15: `if_true` has been deprecated: Use `ite_true` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6489:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:23: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:19: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:44: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7042:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7206:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7210:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:
  [NumberField K]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NumberField K] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7715:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7723:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8296:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:28: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:40: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8482:28: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8625:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8627:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8757:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8759:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8875:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:16: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8879:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9053:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9445:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:19: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:32: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:32: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9591:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9635:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:25: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:23: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9728:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:27: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9742:6: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9909:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9930:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9935:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9937:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10014:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10462:28: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10609:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10611:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10638:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10640:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10682:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:16: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10782:12: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10854:53: `if_true` has been deprecated: Use `ite_true` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10860:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10928:24: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11132:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12054:4: Try this: 
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12073:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12122:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [32/43] Built Theorems.Thm_M4aTorus_completedRayL_fe (47s)
warning: source/Theorems/Thm_M4aTorus_completedRayL_fe.lean:21:23: Variable name `h𝔣'` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _h𝔣'

Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [33/43] Built P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (14s)
✔ [34/43] Built Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (10s)
⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (82s)
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:57:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:66:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:105:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:162:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:203:40: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:211:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:218:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:253:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:18: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:18: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:20: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:20: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:365:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:370:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:655:14: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:656:14: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:706:17: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (74s)
⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (22s)
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:39:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:40:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:101:54: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (11s)
⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (12s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:79:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:107:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:123:18: This simp argument is unused:
  hζ.coe_toInteger

Hint: Omit it from the simp argument list.
  [apply] simp [hζ'def] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:147:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (8.6s)
⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (14s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:70:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:71:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:93:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:122:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:206:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:207:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:308:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:346:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:347:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:389:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:390:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:393:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:397:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:406:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:407:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:419:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:420:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:421:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
✔ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (55s)
ℹ [43/43] Built AuditRoot (14s)
info: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,
  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]
  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),
  ∃ p,
    Nat.Prime p ∧
      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P
info: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (43 jobs).

STDERR
```

## root-cleaned-output.txt

```text
✔ [34/43] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (68s)
⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (50s)
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:57:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:66:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:105:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:162:12: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:203:40: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:211:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:218:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:253:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:8: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:18: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:8: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:18: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:20: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:20: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:365:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:370:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:655:14: `if_pos` has been deprecated: Use `ite_eq_left` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:656:14: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:706:17: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (46s)
⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (41s)
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:39:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:40:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:10: `if_neg` has been deprecated: Use `ite_eq_right` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead
warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:101:54: `if_neg` has been deprecated: Use `ite_eq_right` instead
✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (23s)
⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (20s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:78:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:106:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:122:18: This simp argument is unused:
  hζ.coe_toInteger

Hint: Omit it from the simp argument list.
  [apply] simp [hζ'def] at h

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:146:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (10s)
⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (142s)
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:69:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:70:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:92:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:121:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:205:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:206:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:307:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:345:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:346:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:388:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:389:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:392:4: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:396:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:405:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:406:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:418:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:419:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:420:2: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
⚠ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (29s)
warning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
warning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: Unused tactic linter: `assumption` does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
ℹ [43/43] Built AuditRoot (13s)
info: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,
  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]
  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),
  ∃ p,
    Nat.Prime p ∧
      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P
info: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (43 jobs).

STDERR
```
