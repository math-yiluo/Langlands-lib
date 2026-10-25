# Terminal development check 08

Official diagnostic `b294069f-9f5a-4e1a-8390-d6b23f7e73b1`. Exact UTF-8 JSON SHA256 `7101dac4329ea8d63a5984b40035c857e695a0eefd438251dabdeb7061bea072`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/092191a470ec4163bb711b4b9a7e842b\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
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
    "returncode": 0,
    "stdout": "✔ [34/43] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (68s)\n⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (50s)\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:57:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:66:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:105:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:162:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:203:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:211:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:218:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:250:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:253:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:323:18: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:324:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:338:20: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:339:20: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:365:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:370:10: `MonoidHom.restrict_apply` has been deprecated: Use `MonoidHom.domRestrict_apply` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:655:14: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:656:14: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean:706:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (46s)\n⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (41s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:37:55: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:39:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:40:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:94:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean:101:54: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (23s)\n⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (20s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:78:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:106:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:122:18: This simp argument is unused:\n  hζ.coe_toInteger\n\nHint: Omit it from the simp argument list.\n  [apply] simp [hζ'def] at h\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:146:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (10s)\n⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (142s)\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:69:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:70:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:92:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:121:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:205:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:206:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:307:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:345:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:346:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:388:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:389:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:392:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:396:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:405:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:406:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:418:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:419:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:420:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n⚠ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (29s)\nwarning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: this tactic is never executed\n\nNote: This linter can be disabled with `set_option linter.unreachableTactic false`\nwarning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: Unused tactic linter: `assumption` does nothing\n\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\nℹ [43/43] Built AuditRoot (13s)\ninfo: source/AuditRoot.lean:3:0: NumberField.exists_prime_isArithFrobAt_of_isGalois.{u_1,\n  u_2} : ∀ (K : Type u_1) (L : Type u_2) [inst : Field.{u_1} K] [NumberField.{u_1} K] [inst_2 : Field.{u_2} L]\n  [NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L] (σ : Gal(L/K)) (S : Finset.{0} ℕ),\n  ∃ p,\n    Nat.Prime p ∧\n      p ∉ S ∧ ∃ P, Ideal.IsMaximal.{u_2} P ∧ Membership.mem.{u_2, u_2} P ↑p ∧ IsArithFrobAt.{0, u_2, u_2} ℤ σ P\ninfo: source/AuditRoot.lean:4:0: 'NumberField.exists_prime_isArithFrobAt_of_isGalois' depends on axioms: [propext, Classical.choice, Quot.sound]\nBuild completed successfully (43 jobs).\n",
    "stderr": "",
    "duration_seconds": 449.5989805650024,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
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
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (46s)\n⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (41s)"
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
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (23s)\n⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (20s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 78,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 106,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 122,
          "column": 18
        },
        "data": "This simp argument is unused:\n  hζ.coe_toInteger\nHint: Omit it from the simp argument list.\n  [apply] simp [hζ'def] at h\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean",
        "pos": {
          "line": 146,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (10s)\n⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (142s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 69,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
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
          "line": 92,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 121,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 205,
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
          "line": 307,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 345,
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
          "line": 388,
          "column": 4
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
          "line": 392,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 396,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 405,
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
          "line": 418,
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
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n⚠ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (29s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 18,
          "column": 87
        },
        "data": "this tactic is never executed\nNote: This linter can be disabled with `set_option linter.unreachableTactic false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean",
        "pos": {
          "line": 18,
          "column": 87
        },
        "data": "Unused tactic linter: `assumption` does nothing\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\nℹ [43/43] Built AuditRoot (13s)"
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
        "text": "✔ [34/43] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (68s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [35/43] Built P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (50s)"
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
        "text": "✔ [36/43] Built Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension (46s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [37/43] Built P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (41s)"
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
        "text": "✔ [38/43] Built Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension (23s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [39/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (20s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:78:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:106:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:122:18: This simp argument is unused:"
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean:146:2: Try this: "
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
        "text": "✔ [40/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension (10s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [41/43] Built P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (142s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:69:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:92:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:121:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:205:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:307:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:345:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:388:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:392:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:396:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:405:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:418:2: Try this: "
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
        "text": "⚠ [42/43] Built Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois (29s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: this tactic is never executed"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unreachableTactic false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean:18:87: Unused tactic linter: `assumption` does nothing"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedTactic false`"
      },
      {
        "stream": "stdout",
        "text": "ℹ [43/43] Built AuditRoot (13s)"
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
    "warnings": 52
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
    "checked_at": 1792943078.3508449,
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
  "sources_sha256": "607aec98a3f26606b7feac7b09a6addcd99fddd8dba3b3f9e2e2f71004ff2e95",
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
        "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/092191a470ec4163bb711b4b9a7e842b\" = \"write\"}",
        "sandbox",
        "-P",
        "lean",
        "-C",
        "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/4/.lake/build/lib/lean",
        "--",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean",
        "--run",
        "/home/taskhub/src/Task-based-auto-formalize/src/task_based_auto_formalize/lean_tools/Inspect.lean",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0",
        "AuditRoot",
        "NumberField.exists_prime_isArithFrobAt_of_isGalois",
        "--output",
        "/home/taskhub/pilot/.task-based/lean-service/scratch/092191a470ec4163bb711b4b9a7e842b/inspect-5ce2ee2901f1446bbf12e6b00a45ecb6/result.json"
      ],
      "returncode": 0,
      "stdout": "",
      "stderr": "",
      "duration_seconds": 207.6446004449972,
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
