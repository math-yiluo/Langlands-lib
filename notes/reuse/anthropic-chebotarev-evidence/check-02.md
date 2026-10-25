# Terminal development check 02

Official diagnostic `5b25ca0b-4185-4f1f-8188-b5c676a3e634`. Exact UTF-8 JSON SHA256 `7e56220ad0d7af2feeabf7fe7f3179ab0c1ccb034e5ce8c9149a4b359b245e8d`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/439693be7c4d47fab08f211c4bbc8523\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+AuditRoot:olean"
    ],
    "returncode": 1,
    "stdout": "⚠ [8/14] Built Definitions.Def_FrobeniusDensity_BadPrimes (70s)\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:61:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:63:31: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:90:19: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:96:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:109:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:110:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:122:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (11s)\n⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (33s)\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:58:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:87:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:88:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:109:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:108:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:202:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:213:34: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:288:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:284:6: Unused tactic linter: `beta_reduce` does nothing\n\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n⚠ [11/22] Built Definitions.Def_NumberField_NormResidueCharacter (116s)\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:94:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:96:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:96:20: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:116:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:120:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:149:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:149:34: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:177:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:178:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:179:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:200:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:201:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:203:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:237:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:251:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:253:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:254:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:255:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:256:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:271:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:278:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:279:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:281:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:294:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:303:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:304:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:334:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\n⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (27s)\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:29:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:35:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:42:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:56:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:33: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:97:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:100:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:101:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:162:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:161:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:201:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:206:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:220:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:222:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:231:30: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:234:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:247:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:255:9: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:260:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:269:32: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:274:5: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:273:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:292:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:293:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:310:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:313:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:316:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:318:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:320:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:331:68: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:333:16: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:480:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:482:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:483:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:487:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:489:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:490:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:499:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:499:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:501:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:505:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:505:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:507:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:514:35: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:515:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:559:14: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\n⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (12s)\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:70:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:71:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:138:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:139:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:180:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:181:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:184:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:204:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:205:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:206:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:207:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:218:15: `Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead.\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:218:69: `Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead.\n✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (8.0s)\n✔ [17/26] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (7.0s)\n⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (9.0s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:35:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:68:46: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:104:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:106:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (8.7s)\n✖ [25/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (275s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:149:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:153:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:521:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:569:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:605:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1074:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1292:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1293:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1358:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2469:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2476:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2485:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2863:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2864:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3005:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3006:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3074:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3469:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3475:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3479:60: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3501:24: This simp argument is unused:\n  smul_eq_mul\n\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3500:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3528:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4187:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4841:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4877:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4886:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5271:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:37: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5280:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5285:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5315:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5482:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5484:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5506:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5515:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5757:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5802:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5815:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5821:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5826:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5857:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5978:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6137:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6138:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6164:51: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6165:78: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6246:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6257:75: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6263:15: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6486:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6878:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6891:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6892:23: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6896:44: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7039:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7203:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7207:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7712:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7720:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8293:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:28: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8477:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8479:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8622:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8624:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8754:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8756:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8872:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8873:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9050:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9316:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\n\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\n\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command.\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9339:16: (kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9444:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9453:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9453:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9457:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9457:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9571:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9571:32: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9581:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9581:32: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9590:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9634:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9641:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9641:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9644:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9644:23: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9727:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9735:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9735:27: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9740:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:6: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9908:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9933:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9929:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9936:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9985:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9985:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10012:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10059:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10059:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10264:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10264:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10461:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10608:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10610:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10637:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10639:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10678:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10681:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10777:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10781:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10853:53: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10859:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10927:24: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11131:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12052:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12072:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12121:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n⚠ [29/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (202s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:27:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:28:2: `Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:34:45: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:35:4: `Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:36:41: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:41:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:97:8: `Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:108:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:109:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:139:14: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:144:14: `if_neg` has been deprecated: Use `ite_eq_right` instead\n⚠ [30/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (39s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:36:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:69:46: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:105:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:107:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [31/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (40s)\n✔ [32/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (8.3s)\n✖ [33/43] Building P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (8.5s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.setup.json --json\nerror: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:257:4: Type mismatch\n  ENNReal.le_tsum ⟨⊤, of_eq_true (Eq.trans (congrArg Not top_ne_bot._simp_1) not_false_eq_true)⟩\nhas type\n  ?m.20 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // I ≠ ⊥ }), ?m.20 a\nbut is expected to have type\n  normRpow K s ⊤ ≤ idealSum K s\nerror: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:263:4: Type mismatch\n  ENNReal.le_tsum ⟨⊤, isFactoredBy_top T⟩\nhas type\n  ?m.22 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // IsFactoredBy T I }), ?m.22 a\nbut is expected to have type\n  normRpow K s ⊤ ≤ factoredSum K T s\nSome required targets logged failures:\n- P2M.Sol.S_M4aTorus_completedRayL_fe\n- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO\n",
    "stderr": "error: build failed\n",
    "duration_seconds": 449.34159905600245,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 61,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 63,
          "column": 31
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 90,
          "column": 19
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 96,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 109,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 110,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 122,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (11s)\n⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (33s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 58,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 87,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 88,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 109,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 108,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 202,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 213,
          "column": 34
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 288,
          "column": 17
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 284,
          "column": 6
        },
        "data": "Unused tactic linter: `beta_reduce` does nothing\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n⚠ [11/22] Built Definitions.Def_NumberField_NormResidueCharacter (116s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 94,
          "column": 22
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 96,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 96,
          "column": 20
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 99,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 99,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 116,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 120,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 149,
          "column": 22
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 149,
          "column": 34
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 177,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 178,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 179,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 200,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 201,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 203,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 237,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 251,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 253,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 254,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 255,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 256,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 271,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 278,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 279,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 281,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 294,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 303,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 304,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 334,
          "column": 19
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead\n⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (27s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 29,
          "column": 28
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 35,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 42,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 56,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 93,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 93,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 93,
          "column": 33
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 97,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 100,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 101,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 162,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 161,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 201,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 206,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 220,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 222,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 231,
          "column": 30
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 234,
          "column": 52
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 247,
          "column": 52
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 255,
          "column": 9
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 260,
          "column": 13
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 269,
          "column": 32
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 274,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 273,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 292,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 293,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 310,
          "column": 13
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 313,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 316,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 318,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 320,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 331,
          "column": 68
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 333,
          "column": 16
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 480,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 482,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 483,
          "column": 29
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 487,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 489,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 490,
          "column": 29
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 499,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 499,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 501,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 505,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 505,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 507,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 514,
          "column": 35
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 515,
          "column": 51
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 559,
          "column": 14
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\n⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (12s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 70,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 71,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 138,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 139,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 180,
          "column": 6
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 181,
          "column": 6
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 184,
          "column": 6
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 204,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 205,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 206,
          "column": 4
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 207,
          "column": 4
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 218,
          "column": 15
        },
        "data": "`Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 218,
          "column": 69
        },
        "data": "`Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead.\n✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (8.0s)\n✔ [17/26] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (7.0s)\n⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (9.0s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 35,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 68,
          "column": 46
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 104,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 106,
          "column": 18
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (8.7s)\n✖ [25/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (275s)"
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
          "line": 9316,
          "column": 0
        },
        "data": "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached\nNote: Use `set_option maxHeartbeats <num>` to set the limit.\nHint: Additional diagnostic information may be available using the `set_option diagnostics true` command."
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9339,
          "column": 16
        },
        "data": "(kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9444,
          "column": 12
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9453,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9453,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9457,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9457,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9571,
          "column": 19
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9571,
          "column": 32
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9581,
          "column": 19
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9581,
          "column": 32
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9590,
          "column": 19
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9634,
          "column": 36
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9641,
          "column": 12
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9641,
          "column": 25
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9644,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9644,
          "column": 23
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9727,
          "column": 14
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9735,
          "column": 14
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9735,
          "column": 27
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9740,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9741,
          "column": 6
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9908,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9933,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9929,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9934,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9936,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9985,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 9985,
          "column": 32
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10012,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
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
          "line": 10059,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10059,
          "column": 35
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10264,
          "column": 18
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10264,
          "column": 69
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10461,
          "column": 28
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10608,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10610,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10637,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10639,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10678,
          "column": 12
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10681,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10777,
          "column": 17
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10778,
          "column": 16
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10781,
          "column": 12
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10853,
          "column": 53
        },
        "data": "`if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10859,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 10927,
          "column": 24
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 11131,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12052,
          "column": 4
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
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12072,
          "column": 23
        },
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12121,
          "column": 23
        },
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n⚠ [29/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (202s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 27,
          "column": 51
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 28,
          "column": 2
        },
        "data": "`Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 34,
          "column": 45
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 35,
          "column": 4
        },
        "data": "`Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 36,
          "column": 41
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 41,
          "column": 51
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 97,
          "column": 8
        },
        "data": "`Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 108,
          "column": 10
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 109,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 139,
          "column": 14
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 144,
          "column": 14
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n⚠ [30/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (39s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 36,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 69,
          "column": 46
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 105,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 107,
          "column": 18
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [31/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (40s)\n✔ [32/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (8.3s)\n✖ [33/43] Building P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (8.5s)"
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
        "pos": {
          "line": 257,
          "column": 4
        },
        "data": "Type mismatch\n  ENNReal.le_tsum ⟨⊤, of_eq_true (Eq.trans (congrArg Not top_ne_bot._simp_1) not_false_eq_true)⟩\nhas type\n  ?m.20 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // I ≠ ⊥ }), ?m.20 a\nbut is expected to have type\n  normRpow K s ⊤ ≤ idealSum K s"
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean",
        "pos": {
          "line": 263,
          "column": 4
        },
        "data": "Type mismatch\n  ENNReal.le_tsum ⟨⊤, isFactoredBy_top T⟩\nhas type\n  ?m.22 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // IsFactoredBy T I }), ?m.22 a\nbut is expected to have type\n  normRpow K s ⊤ ≤ factoredSum K T s\nSome required targets logged failures:\n- P2M.Sol.S_M4aTorus_completedRayL_fe\n- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO"
      }
    ],
    "other_output": [
      {
        "stream": "stdout",
        "text": "⚠ [8/14] Built Definitions.Def_FrobeniusDensity_BadPrimes (70s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:61:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:63:31: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:90:19: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:96:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:109:2: Try this: "
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
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:110:2: Try this: "
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
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:122:2: Try this: "
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
        "text": "✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (11s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (33s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:58:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:87:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:88:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:109:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:108:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:202:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:213:34: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:288:17: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:284:6: Unused tactic linter: `beta_reduce` does nothing"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedTactic false`"
      },
      {
        "stream": "stdout",
        "text": "⚠ [11/22] Built Definitions.Def_NumberField_NormResidueCharacter (116s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:94:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:96:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:96:20: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:116:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:120:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:149:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:149:34: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:177:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:178:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:179:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:200:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:201:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:203:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:237:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:251:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:253:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:254:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:255:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:256:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:271:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:278:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:279:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:281:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:294:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:303:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:304:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:334:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (27s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:29:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:35:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:42:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:56:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:93:33: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:97:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:100:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:101:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:162:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:161:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:201:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:206:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:220:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:222:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:231:30: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:234:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:247:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:255:9: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:260:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:269:32: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:274:5: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:273:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:292:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:293:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:310:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:313:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:316:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:318:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:320:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:331:68: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:333:16: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:480:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:482:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:483:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:487:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:489:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:490:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:499:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:499:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:501:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:505:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:505:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:507:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:514:35: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:515:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:559:14: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (12s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:70:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:71:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:138:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:139:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:180:6: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:181:6: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:184:6: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:204:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:205:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:206:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:207:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:218:15: `Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:218:69: `Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "stream": "stdout",
        "text": "✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (8.0s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [17/26] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (7.0s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (9.0s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:35:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:68:46: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:104:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:106:18: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (8.7s)"
      },
      {
        "stream": "stdout",
        "text": "✖ [25/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (275s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json"
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
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9316:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"
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
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9339:16: (kernel) unknown constant '_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.summable_setIntegral_foldDomain_rayOrbitKernel'"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9444:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9453:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9453:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9457:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9457:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9571:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9571:32: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9581:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9581:32: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9590:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9634:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9641:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9641:25: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9644:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9644:23: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9727:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9735:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9735:27: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9740:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:6: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9908:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9933:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9929:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9936:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9985:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9985:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10012:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10059:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10059:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10264:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10264:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10461:28: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10608:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10610:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10637:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10639:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10678:12: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10681:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10777:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:16: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10781:12: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10853:53: `if_true` has been deprecated: Use `ite_true` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10859:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10927:24: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11131:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12052:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12072:23: Variable name `h𝔣'` is not explicitly referenced."
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
        "text": "warning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12121:23: Variable name `h𝔣'` is not explicitly referenced."
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
        "text": "⚠ [29/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (202s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:27:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:28:2: `Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:34:45: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:35:4: `Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:36:41: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:41:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:97:8: `Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:108:10: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:109:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:139:14: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:144:14: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "⚠ [30/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (39s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:36:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:69:46: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:105:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:107:18: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [31/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (40s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [32/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (8.3s)"
      },
      {
        "stream": "stdout",
        "text": "✖ [33/43] Building P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (8.5s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/ir/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.setup.json --json"
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:257:4: Type mismatch"
      },
      {
        "stream": "stdout",
        "text": "  ENNReal.le_tsum ⟨⊤, of_eq_true (Eq.trans (congrArg Not top_ne_bot._simp_1) not_false_eq_true)⟩"
      },
      {
        "stream": "stdout",
        "text": "has type"
      },
      {
        "stream": "stdout",
        "text": "  ?m.20 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // I ≠ ⊥ }), ?m.20 a"
      },
      {
        "stream": "stdout",
        "text": "but is expected to have type"
      },
      {
        "stream": "stdout",
        "text": "  normRpow K s ⊤ ≤ idealSum K s"
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean:263:4: Type mismatch"
      },
      {
        "stream": "stdout",
        "text": "  ENNReal.le_tsum ⟨⊤, isFactoredBy_top T⟩"
      },
      {
        "stream": "stdout",
        "text": "has type"
      },
      {
        "stream": "stdout",
        "text": "  ?m.22 ⟨⊤, ⋯⟩ ≤ ∑' (a : { I // IsFactoredBy T I }), ?m.22 a"
      },
      {
        "stream": "stdout",
        "text": "but is expected to have type"
      },
      {
        "stream": "stdout",
        "text": "  normRpow K s ⊤ ≤ factoredSum K T s"
      },
      {
        "stream": "stdout",
        "text": "Some required targets logged failures:"
      },
      {
        "stream": "stdout",
        "text": "- P2M.Sol.S_M4aTorus_completedRayL_fe"
      },
      {
        "stream": "stdout",
        "text": "- P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO"
      },
      {
        "stream": "stderr",
        "text": "error: build failed"
      }
    ],
    "errors": 4,
    "warnings": 271
  },
  "threads": 2,
  "modules": [
    {
      "module": "AuditRoot",
      "source_sha256": "ac38a6e118e553a2053c1963892ca993f443fb55dbe5acbe5b67f54ff3c1f061"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792936948.060368,
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
  "sources_sha256": "28af08e76e27a19c52e1651dfef40af8bd2951a0d3afe253555fd0ae6303e9ea"
}
```
