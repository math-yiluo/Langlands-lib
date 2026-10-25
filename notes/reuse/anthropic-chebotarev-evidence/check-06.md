# Terminal development check 06

Official diagnostic `236711df-e7dd-48c0-acaf-17d1319e700c`. Exact UTF-8 JSON SHA256 `9e4bb377cf6c61edcacab2617e0e987cb1bfff05e8cb36b0408276838f52c678`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

```json
{
  "ok": true,
  "proof_accepted": false,
  "validation_method": "lake-build",
  "process": {
    "argv": [
      "/home/taskhub/src/Task-based-auto-formalize/.tools/codex-0.160.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex",
      "-c",
      "permissions.lean.extends=\":workspace\"",
      "-c",
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/b22878283aa14986b3f3ddf2d579861e\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+AuditRoot:olean"
    ],
    "returncode": 0,
    "stdout": "⚠ [31/43] Built P2M.Sol.S_M4aTorus_completedRayL_fe (324s)\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:152:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:156:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:524:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:572:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:608:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1077:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1295:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1296:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1361:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2491:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2866:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2867:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3008:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3077:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3472:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3481:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3482:60: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3504:24: This simp argument is unused:\n  smul_eq_mul\n\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3503:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4199:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4844:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4880:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4889:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5277:37: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5283:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5288:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5318:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5485:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5487:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5509:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5518:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5760:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5805:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5818:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5824:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5829:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5860:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5981:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6140:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6141:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6167:51: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6168:78: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6249:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6260:75: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6266:15: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6489:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:23: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:44: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7042:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7206:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7210:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7715:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7723:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8296:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:28: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8482:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8625:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8627:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8757:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8759:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8875:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8879:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9053:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9445:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:32: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:32: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9591:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9635:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:23: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9728:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:27: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9742:6: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9909:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9930:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9935:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9937:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10014:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10462:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10609:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10611:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10638:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10640:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10682:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10782:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10854:53: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10860:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10928:24: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11132:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12054:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12073:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12122:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n⚠ [32/43] Built Theorems.Thm_M4aTorus_completedRayL_fe (47s)\nwarning: source/Theorems/Thm_M4aTorus_completedRayL_fe.lean:21:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n✔ [33/43] Built P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (14s)\n✔ [34/43] Built Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (10s)\n⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (82s)\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:57:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:66:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:105:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:162:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:203:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:211:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:218:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:253:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:18: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:20: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:20: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:365:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:370:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:655:14: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:656:14: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:706:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (74s)\n⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (22s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:39:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:40:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:101:54: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (11s)\n⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (12s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:79:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:107:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:123:18: This simp argument is unused:\n  hζ.coe_toInteger\n\nHint: Omit it from the simp argument list.\n  [apply] simp [hζ'def] at h\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:147:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (8.6s)\n⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (14s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:70:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:71:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:93:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:122:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:206:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:207:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:308:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:346:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:347:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:389:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:390:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:393:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:397:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:406:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:407:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:419:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:420:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:421:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (55s)\nℹ [43/43] Built AuditRoot (14s)\ninfo: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,\n  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]\n  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),\n  ∃ p,\n    Nat.Prime p ∧\n      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P\ninfo: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]\nBuild completed successfully (43 jobs).\n",
    "stderr": "",
    "duration_seconds": 695.7609886669961,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 152,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 156,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 524,
          "column": 51
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 572,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 608,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1077,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1295,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1296,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 1361,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 29
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 53
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 65
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 88
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2472,
          "column": 100
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2479,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2479,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2488,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2488,
          "column": 28
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2491,
          "column": 16
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2866,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 2867,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3008,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3009,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3009,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3077,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3472,
          "column": 20
        },
        "data": "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3478,
          "column": 6
        },
        "data": "`ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3481,
          "column": 6
        },
        "data": "`ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3482,
          "column": 60
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3504,
          "column": 24
        },
        "data": "This simp argument is unused:\n  smul_eq_mul\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3503,
          "column": 82
        },
        "data": "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3531,
          "column": 13
        },
        "data": "`ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 3531,
          "column": 45
        },
        "data": "`ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`)."
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
          "line": 4190,
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
          "line": 4196,
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
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4199,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4844,
          "column": 47
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4880,
          "column": 15
        },
        "data": "`OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 4889,
          "column": 24
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5274,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5277,
          "column": 37
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5283,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5288,
          "column": 10
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5318,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5485,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5487,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5509,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5518,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5760,
          "column": 39
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5805,
          "column": 22
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5818,
          "column": 6
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5824,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5829,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5860,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 5981,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6140,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6141,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6167,
          "column": 51
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6168,
          "column": 78
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6249,
          "column": 17
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6260,
          "column": 75
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6266,
          "column": 15
        },
        "data": "`if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6489,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6881,
          "column": 12
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6881,
          "column": 56
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6894,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6894,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6895,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6895,
          "column": 23
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6899,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6899,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6899,
          "column": 31
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 6899,
          "column": 44
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7042,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7206,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7210,
          "column": 8
        },
        "data": "automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7715,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 7723,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8296,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8480,
          "column": 28
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8480,
          "column": 40
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8482,
          "column": 28
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8625,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8627,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8757,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8759,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8875,
          "column": 17
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8876,
          "column": 16
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 8879,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9053,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
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
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n⚠ [32/43] Built Theorems.Thm_M4aTorus_completedRayL_fe (47s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Theorems/Thm_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 21,
          "column": 23
        },
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n✔ [33/43] Built P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (14s)\n✔ [34/43] Built Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (10s)\n⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (82s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 57,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 66,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 105,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 162,
          "column": 12
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 203,
          "column": 40
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 211,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 218,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 250,
          "column": 10
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 253,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 323,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 323,
          "column": 18
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 324,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 324,
          "column": 18
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 338,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 338,
          "column": 20
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 339,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 339,
          "column": 20
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 365,
          "column": 10
        },
        "data": "`MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 370,
          "column": 10
        },
        "data": "`MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 655,
          "column": 14
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 656,
          "column": 14
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 706,
          "column": 17
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (74s)\n⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (22s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 37,
          "column": 55
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 39,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 40,
          "column": 29
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 94,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 94,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 101,
          "column": 54
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (11s)\n⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (12s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 79,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 107,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 123,
          "column": 18
        },
        "data": "This simp argument is unused:\n  hζ.coe_toInteger\nHint: Omit it from the simp argument list.\n  [apply] simp [hζ'def] at h\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 147,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (8.6s)\n⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (14s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 70,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 71,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 93,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 122,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 206,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 207,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 308,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 346,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 347,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 389,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 390,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 393,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 397,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 406,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 407,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 419,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 420,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 421,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (55s)\nℹ [43/43] Built AuditRoot (14s)"
      },
      {
        "severity": "info",
        "fileName": "source/AuditRoot.lean",
        "pos": {
          "line": 3,
          "column": 0
        },
        "data": "NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,\n  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]\n  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),\n  ∃ p,\n    Nat.Prime p ∧\n      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P"
      },
      {
        "severity": "info",
        "fileName": "source/AuditRoot.lean",
        "pos": {
          "line": 4,
          "column": 0
        },
        "data": "'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]\nBuild completed successfully (43 jobs)."
      }
    ],
    "other_output": [
      {
        "stream": "stdout",
        "text": "⚠ [31/43] Built P2M.Sol.S_M4aTorus_completedRayL_fe (324s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:152:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:156:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:524:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:572:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:608:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1077:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1295:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1296:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1361:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2491:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2866:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2867:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3008:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3077:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3472:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3481:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3482:60: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3504:24: This simp argument is unused:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3503:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`)."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4199:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4844:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4880:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4889:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5277:37: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5283:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5288:10: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5318:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5485:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5487:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5509:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5518:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5760:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5805:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5818:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5824:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5829:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5860:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5981:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6140:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6141:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6167:51: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6168:78: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6249:17: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6260:75: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6266:15: `if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6489:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:23: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:44: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7042:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7206:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7210:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:"
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7715:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7723:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8296:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:28: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:40: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8482:28: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8625:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8627:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8757:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8759:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8875:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:16: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8879:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9053:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
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
        "text": "⚠ [32/43] Built Theorems.Thm_M4aTorus_completedRayL_fe (47s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Theorems/Thm_M4aTorus_completedRayL_fe.lean:21:23: Variable name `h𝔣'` is not explicitly referenced."
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
        "text": "✔ [33/43] Built P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (14s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [34/43] Built Theorems.Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (10s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (82s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:57:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:66:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:105:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:162:12: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:203:40: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:211:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:218:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:253:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:18: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:18: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:20: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:20: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:365:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:370:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:655:14: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:656:14: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:706:17: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (74s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (22s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:39:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:40:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:101:54: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (11s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (12s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:79:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:107:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:123:18: This simp argument is unused:"
      },
      {
        "stream": "stdout",
        "text": "  hζ.coe_toInteger"
      },
      {
        "stream": "stdout",
        "text": "Hint: Omit it from the simp argument list."
      },
      {
        "stream": "stdout",
        "text": "  [apply] simp [hζ'def] at h"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:147:2: Try this: "
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
        "text": "✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (8.6s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (14s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:70:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:71:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:93:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:122:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:206:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:207:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:308:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:346:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:347:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:389:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:390:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:393:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:397:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:406:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:407:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:419:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:420:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:421:2: Try this: "
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
        "text": "✔ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (55s)"
      },
      {
        "stream": "stdout",
        "text": "ℹ [43/43] Built AuditRoot (14s)"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,"
      },
      {
        "stream": "stdout",
        "text": "  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),"
      },
      {
        "stream": "stdout",
        "text": "  ∃ p,"
      },
      {
        "stream": "stdout",
        "text": "    Nat.Prime p ∧"
      },
      {
        "stream": "stdout",
        "text": "      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "Build completed successfully (43 jobs)."
      }
    ],
    "errors": 0,
    "warnings": 197
  },
  "threads": 2,
  "modules": [
    {
      "module": "AuditRoot",
      "source_sha256": "ac38a6e118e553a2053c1963892ca993f443fb55dbe5acbe5b67f54ff3c1f061"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792941184.5593243,
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
  "sources_sha256": "2ff4349cbb15d238016d719cbec8a76ee9e31bfbd066c08b067f65b43baa8546",
  "inspection": {
    "module": "AuditRoot",
    "declaration": "NumberField.exists_prime_isArithFrobAt_of_isGalois",
    "ok": true,
    "metadata": {
      "axiom_modules": {
        "Classical.choice": "Init.Prelude",
        "Quot.sound": "Init.Prelude",
        "propext": "Init.Core"
      },
      "axioms": [
        "propext",
        "Classical.choice",
        "Quot.sound"
      ],
      "declaration": "NumberField.exists_prime_isArithFrobAt_of_isGalois",
      "kind": "theorem",
      "level_parameters": [
        "audit_u",
        "audit_v"
      ],
      "module": "AuditRoot",
      "protocol": "task-based-lean-inspect@3",
      "statement_module": "",
      "statement_returns_prop": false,
      "statement_target_encoding": null,
      "target_matches": false,
      "type_encoding": "repr",
      "type_sha256": "3947a480b5b576718094cd7dba79d66c903b9e17396b4d9146cfba4c005318fc",
      "type_bytes": 157329,
      "expression_transport": "private files; exact UTF-8 fingerprints retained"
    },
    "process": {
      "argv": [
        "/home/taskhub/src/Task-based-auto-formalize/.tools/codex-0.160.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex",
        "-c",
        "permissions.lean.extends=\":workspace\"",
        "-c",
        "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/b22878283aa14986b3f3ddf2d579861e\" = \"write\"}",
        "sandbox",
        "-P",
        "lean",
        "-C",
        "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean",
        "--",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean",
        "--run",
        "/home/taskhub/src/Task-based-auto-formalize/src/task_based_auto_formalize/lean_tools/Inspect.lean",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0",
        "AuditRoot",
        "NumberField.exists_prime_isArithFrobAt_of_isGalois",
        "--output",
        "/home/taskhub/pilot/.task-based/lean-service/scratch/b22878283aa14986b3f3ddf2d579861e/inspect-0230ff1ccb7f4cc08c6d4279033eb9c9/result.json"
      ],
      "returncode": 0,
      "stdout": "",
      "stderr": "",
      "duration_seconds": 127.3998769200116,
      "timed_out": false,
      "output_limited": false,
      "error": null,
      "tree_quiet": true
    },
    "proof_accepted": false,
    "validation_method": "lake-build"
  }
}
```
