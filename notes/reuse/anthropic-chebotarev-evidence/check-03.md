# Terminal development check 03

Official diagnostic `8acf1d36-4a1b-4020-a2b3-31eb70b12416`. Exact UTF-8 JSON SHA256 `d51a5d4db0a2e637ec421c49a9dfd4932d229c0d53385dd132bbfb32dc241cbc`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

```json
{
  "ok": false,
  "proof_accepted": false,
  "validation_method": "lake-build",
  "process": {
    "argv": [
      "/home/taskhub/src/Task-based-auto-formalize/.tools/codex-0.160.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex",
      "-c",
      "permissions.lean.extends=\":workspace\"",
      "-c",
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/a35b326c3820406da6558ec85c709f84\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+AuditRoot:olean"
    ],
    "returncode": 1,
    "stdout": "✖ [29/43] Building P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (52s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.setup.json --json\nerror: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:259:4: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\nerror: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:265:4: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n✖ [31/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (314s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:149:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:153:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:521:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:569:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:605:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1074:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1292:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1293:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1358:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2863:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2864:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3005:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3074:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3469:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3475:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3479:60: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3501:24: This simp argument is unused:\n  smul_eq_mul\n\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3500:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4841:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4877:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4886:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5271:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:37: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5280:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5285:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5315:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5482:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5484:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5506:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5515:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5757:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5802:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5815:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5821:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5826:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5857:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5978:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6137:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6138:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6164:51: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6165:78: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6246:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6257:75: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6263:15: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6486:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:23: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:44: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7039:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7203:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7207:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7712:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7720:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8293:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:28: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8479:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8622:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8624:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8754:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8756:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8872:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8873:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9050:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9317:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (1600000) has been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9340:16: (kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9445:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:32: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:32: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9591:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9635:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:23: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9728:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:27: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9742:6: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9909:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9930:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9935:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9937:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10014:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10462:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10609:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10611:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10638:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10640:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10682:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10782:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10854:53: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10860:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10928:24: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11132:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12054:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12073:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12122:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nSome required targets logged failures:\n- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO\n- P2M.Sol.S_M4aTorus_completedRayL_fe\n",
    "stderr": "error: build failed\n",
    "duration_seconds": 315.0091001279943,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
        "pos": {
          "line": 259,
          "column": 4
        },
        "data": "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
        "pos": {
          "line": 265,
          "column": 4
        },
        "data": "(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\n✖ [31/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (314s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 149,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 153,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 521,
          "column": 51
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 569,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 605,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1074,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1292,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1293,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1358,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 29
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 53
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 65
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 88
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2469,
          "column": 100
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2476,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2476,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2485,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2485,
          "column": 28
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2488,
          "column": 16
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2863,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2864,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3005,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3006,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3006,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3074,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3469,
          "column": 20
        },
        "data": "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3475,
          "column": 6
        },
        "data": "`ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3478,
          "column": 6
        },
        "data": "`ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3479,
          "column": 60
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3501,
          "column": 24
        },
        "data": "This simp argument is unused:\n  smul_eq_mul\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3500,
          "column": 82
        },
        "data": "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3528,
          "column": 13
        },
        "data": "`ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3528,
          "column": 45
        },
        "data": "`ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4187,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4187,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4187,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4190,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4193,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4193,
          "column": 8
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4196,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4841,
          "column": 47
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4877,
          "column": 15
        },
        "data": "`OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4886,
          "column": 24
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5271,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5274,
          "column": 37
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5280,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5285,
          "column": 10
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5315,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5482,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5484,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5506,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5515,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5757,
          "column": 39
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5802,
          "column": 22
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5815,
          "column": 6
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5821,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5826,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5857,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5978,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6137,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6138,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6164,
          "column": 51
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6165,
          "column": 78
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6246,
          "column": 17
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6257,
          "column": 75
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6263,
          "column": 15
        },
        "data": "`if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6486,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6878,
          "column": 12
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6878,
          "column": 56
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6891,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6891,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6892,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6892,
          "column": 23
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6896,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6896,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6896,
          "column": 31
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6896,
          "column": 44
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7039,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7203,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7207,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7712,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7720,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8293,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8477,
          "column": 28
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8477,
          "column": 40
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8479,
          "column": 28
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8622,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8624,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8754,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8756,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8872,
          "column": 17
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8873,
          "column": 16
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8876,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9050,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9317,
          "column": 0
        },
        "data": "(deterministic) timeout at `whnf`, maximum number of heartbeats (1600000) has been reached\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9340,
          "column": 16
        },
        "data": "(kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9445,
          "column": 12
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9454,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9454,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9458,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9458,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9572,
          "column": 19
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9572,
          "column": 32
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9582,
          "column": 19
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9582,
          "column": 32
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9591,
          "column": 19
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9635,
          "column": 36
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9642,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9642,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9645,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9645,
          "column": 23
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9728,
          "column": 14
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9736,
          "column": 14
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9736,
          "column": 27
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9741,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9742,
          "column": 6
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9909,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9934,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9930,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9935,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9937,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9986,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9986,
          "column": 32
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10013,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10014,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10060,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10060,
          "column": 35
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10265,
          "column": 18
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10265,
          "column": 69
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10462,
          "column": 28
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10609,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10611,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10638,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10640,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10679,
          "column": 12
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10682,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10778,
          "column": 17
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10779,
          "column": 16
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10782,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10854,
          "column": 53
        },
        "data": "`if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10860,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10928,
          "column": 24
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 11132,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12053,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12054,
          "column": 4
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12073,
          "column": 23
        },
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12122,
          "column": 23
        },
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nSome required targets logged failures:\n- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO\n- P2M.Sol.S_M4aTorus_completedRayL_fe"
      }
    ],
    "other_output": [
      {
        "stream": "stdout",
        "text": "✖ [29/43] Building P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (52s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.setup.json --json"
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:259:4: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"
      },
      {
        "stream": "stdout",
        "text": "Note: Use `set_option maxHeartbeats <num>` to set the limit."
      },
      {
        "stream": "stdout",
        "text": "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:265:4: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached"
      },
      {
        "stream": "stdout",
        "text": "Note: Use `set_option maxHeartbeats <num>` to set the limit."
      },
      {
        "stream": "stdout",
        "text": "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "stream": "stdout",
        "text": "✖ [31/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (314s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:149:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:153:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:521:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:569:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:605:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1074:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1292:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1293:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1358:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2863:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  letI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `let` is preferred over `letI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `let` and `letI` is that `letI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2864:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  letI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `let` is preferred over `letI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `let` and `letI` is that `letI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3005:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3074:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3469:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3475:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3479:60: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3501:24: This simp argument is unused:"
      },
      {
        "stream": "stdout",
        "text": "  smul_eq_mul"
      },
      {
        "stream": "stdout",
        "text": "Hint: Omit it from the simp argument list."
      },
      {
        "stream": "stdout",
        "text": "  [apply] simp only [smul_smul]"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3500:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4841:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4877:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4886:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5271:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:37: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5280:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5285:10: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5315:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5482:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5484:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5506:4: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5515:4: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5757:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5802:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5815:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5821:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5826:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5857:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5978:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6137:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6138:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6164:51: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6165:78: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6246:17: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6257:75: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6263:15: `if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6486:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:23: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:44: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7039:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7203:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7207:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField K]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField K] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7712:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7720:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8293:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:28: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:40: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8479:28: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8622:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8624:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8754:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8756:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8872:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8873:16: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9050:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9317:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (1600000) has been reached"
      },
      {
        "stream": "stdout",
        "text": "Note: Use `set_option maxHeartbeats <num>` to set the limit."
      },
      {
        "stream": "stdout",
        "text": "Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9340:16: (kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9445:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:32: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:32: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9591:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9635:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:23: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9728:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:27: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9742:6: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9909:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9930:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9935:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9937:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10014:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10462:28: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10609:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10611:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10638:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10640:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10682:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:16: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10782:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10854:53: `if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10860:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10928:24: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11132:2: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  haveI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `have` is preferred over `haveI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `have` and `haveI` is that `haveI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12054:4: Try this: "
      },
      {
        "stream": "stdout",
        "text": "  letI̵"
      },
      {
        "stream": "stdout",
        "text": "The goal is a proposition, so `let` is preferred over `letI`."
      },
      {
        "stream": "stdout",
        "text": "The difference between `let` and `letI` is that `letI` inlines the value."
      },
      {
        "stream": "stdout",
        "text": "But this is not relevant for proofs because of proof irrelevance."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12073:23: Variable name `h𝔣'` is not explicitly referenced."
      },
      {
        "stream": "stdout",
        "text": "Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:"
      },
      {
        "stream": "stdout",
        "text": "  [apply] _h𝔣'"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12122:23: Variable name `h𝔣'` is not explicitly referenced."
      },
      {
        "stream": "stdout",
        "text": "Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:"
      },
      {
        "stream": "stdout",
        "text": "  [apply] _h𝔣'"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "stream": "stdout",
        "text": "Some required targets logged failures:"
      },
      {
        "stream": "stdout",
        "text": "- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO"
      },
      {
        "stream": "stdout",
        "text": "- P2M.Sol.S_M4aTorus_completedRayL_fe"
      },
      {
        "stream": "stderr",
        "text": "error: build failed"
      }
    ],
    "errors": 4,
    "warnings": 146
  },
  "threads": 2,
  "modules": [
    {
      "module": "AuditRoot",
      "source_sha256": "ac38a6e118e553a2053c1963892ca993f443fb55dbe5acbe5b67f54ff3c1f061"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/2/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792937763.299757,
    "bytes": 0,
    "removed_bytes": 0,
    "target_bytes": 4294967296,
    "size_scope": "observed_idle_namespaces",
    "active_namespaces_skipped": 1,
    "errors": []
  },
  "reused_modules": [],
  "built_modules": [
    "AuditRoot"
  ],
  "sources_sha256": "f8ddd7e7d8bf11a2ea901acc37430aee18d7c8d00305382c18e7b2b9060b17f7"
}
```
