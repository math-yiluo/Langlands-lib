# Terminal development check 12

Official diagnostic `0744779c-80b8-4f7c-8a07-15813987b581`. Exact UTF-8 JSON SHA256 `bf1bc766987a35e8c361fd2bc7320b9acb6dc620758c04e3a1a0fb0e6a01f64f`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/3090dfa66d844d88b3085412c07d6cec\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+AuditRoot:olean",
      "+AuditBridges:olean"
    ],
    "returncode": 1,
    "stdout": "✖ [57/57] Building AuditBridges (22s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/source/AuditBridges.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean/AuditBridges.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean/AuditBridges.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/ir/AuditBridges.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/ir/AuditBridges.setup.json --json\nwarning: source/AuditBridges.lean:14:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.liesOver_of_prime_mem`:\n  [NumberField L]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField L] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/AuditBridges.lean:20:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.unramified_of_not_dvd_discr`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/AuditBridges.lean:28:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.outside_finite_set`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/AuditBridges.lean:29:13: Variable name `hp` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _hp\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nwarning: source/AuditBridges.lean:46:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nerror: source/AuditBridges.lean:54:4: Unknown constant `Nat.card_le_one_iff_subsingleton.mp`\nwarning: source/AuditBridges.lean:53:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\ninfo: source/AuditBridges.lean:60:0: @ChebotarevAudit.localDegree_ne_one.{u_1,\n    u_2} : ∀ {K : Type u_1} {L : Type u_2} [inst : Field.{u_1} K] [inst_1 : NumberField.{u_1} K]\n  [inst_2 : Field.{u_2} L] [inst_3 : NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L]\n  (v : HeightOneSpectrum.{u_1} (RingOfIntegers.{u_1} K)) (w : HeightOneSpectrum.{u_2} (RingOfIntegers.{u_2} L))\n  [inst_6 : Ideal.LiesOver.{u_1, u_2} (HeightOneSpectrum.asIdeal.{u_2} w) (HeightOneSpectrum.asIdeal.{u_1} v)]\n  (σ : Gal(L/K)),\n  Ne.{u_2 + 1} σ 1 →\n    IsArithFrobAt.{0, u_2, u_2} ℤ σ (HeightOneSpectrum.asIdeal.{u_2} w) →\n      Ne.{1}\n        (Module.finrank.{u_1, u_2} (HeightOneSpectrum.adicCompletion.{u_1, u_1} K v)\n          (HeightOneSpectrum.adicCompletion.{u_2, u_2} L w))\n        1\ninfo: source/AuditBridges.lean:61:0: 'ChebotarevAudit.localDegree_ne_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]\ninfo: source/AuditBridges.lean:62:0: 'ChebotarevAudit.outside_finite_set' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/AuditBridges.lean:63:0: 'ChebotarevAudit.unramified_of_not_dvd_discr' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/AuditBridges.lean:64:0: 'ChebotarevAudit.liesOver_of_prime_mem' depends on axioms: [propext, Classical.choice, Quot.sound]\nSome required targets logged failures:\n- AuditBridges\n",
    "stderr": "error: build failed\n",
    "duration_seconds": 24.171228908002377,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 14,
          "column": 1
        },
        "data": "automatically included section variable(s) unused in theorem `ChebotarevAudit.liesOver_of_prime_mem`:\n  [NumberField L]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField L] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 20,
          "column": 1
        },
        "data": "automatically included section variable(s) unused in theorem `ChebotarevAudit.unramified_of_not_dvd_discr`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 28,
          "column": 1
        },
        "data": "automatically included section variable(s) unused in theorem `ChebotarevAudit.outside_finite_set`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 29,
          "column": 13
        },
        "data": "Variable name `hp` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _hp\nNote: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 46,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "error",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 54,
          "column": 4
        },
        "data": "Unknown constant `Nat.card_le_one_iff_subsingleton.mp`"
      },
      {
        "severity": "warning",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 53,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "info",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 60,
          "column": 0
        },
        "data": "@ChebotarevAudit.localDegree_ne_one.{u_1,\n    u_2} : ∀ {K : Type u_1} {L : Type u_2} [inst : Field.{u_1} K] [inst_1 : NumberField.{u_1} K]\n  [inst_2 : Field.{u_2} L] [inst_3 : NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L]\n  (v : HeightOneSpectrum.{u_1} (RingOfIntegers.{u_1} K)) (w : HeightOneSpectrum.{u_2} (RingOfIntegers.{u_2} L))\n  [inst_6 : Ideal.LiesOver.{u_1, u_2} (HeightOneSpectrum.asIdeal.{u_2} w) (HeightOneSpectrum.asIdeal.{u_1} v)]\n  (σ : Gal(L/K)),\n  Ne.{u_2 + 1} σ 1 →\n    IsArithFrobAt.{0, u_2, u_2} ℤ σ (HeightOneSpectrum.asIdeal.{u_2} w) →\n      Ne.{1}\n        (Module.finrank.{u_1, u_2} (HeightOneSpectrum.adicCompletion.{u_1, u_1} K v)\n          (HeightOneSpectrum.adicCompletion.{u_2, u_2} L w))"
      },
      {
        "severity": "info",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 61,
          "column": 0
        },
        "data": "'ChebotarevAudit.localDegree_ne_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 62,
          "column": 0
        },
        "data": "'ChebotarevAudit.outside_finite_set' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 63,
          "column": 0
        },
        "data": "'ChebotarevAudit.unramified_of_not_dvd_discr' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/AuditBridges.lean",
        "pos": {
          "line": 64,
          "column": 0
        },
        "data": "'ChebotarevAudit.liesOver_of_prime_mem' depends on axioms: [propext, Classical.choice, Quot.sound]\nSome required targets logged failures:\n- AuditBridges"
      }
    ],
    "other_output": [
      {
        "stream": "stdout",
        "text": "✖ [57/57] Building AuditBridges (22s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/source/AuditBridges.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean/AuditBridges.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean/AuditBridges.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/ir/AuditBridges.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/ir/AuditBridges.setup.json --json"
      },
      {
        "stream": "stdout",
        "text": "warning: source/AuditBridges.lean:14:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.liesOver_of_prime_mem`:"
      },
      {
        "stream": "stdout",
        "text": "  [NumberField L]"
      },
      {
        "stream": "stdout",
        "text": "consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:"
      },
      {
        "stream": "stdout",
        "text": "  omit [NumberField L] in theorem ..."
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/AuditBridges.lean:20:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.unramified_of_not_dvd_discr`:"
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
        "text": "warning: source/AuditBridges.lean:28:1: automatically included section variable(s) unused in theorem `ChebotarevAudit.outside_finite_set`:"
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
        "text": "warning: source/AuditBridges.lean:29:13: Variable name `hp` is not explicitly referenced."
      },
      {
        "stream": "stdout",
        "text": "Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:"
      },
      {
        "stream": "stdout",
        "text": "  [apply] _hp"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedVariables false`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/AuditBridges.lean:46:2: Try this: "
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
        "text": "error: source/AuditBridges.lean:54:4: Unknown constant `Nat.card_le_one_iff_subsingleton.mp`"
      },
      {
        "stream": "stdout",
        "text": "warning: source/AuditBridges.lean:53:2: Try this: "
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
        "text": "info: source/AuditBridges.lean:60:0: @ChebotarevAudit.localDegree_ne_one.{u_1,"
      },
      {
        "stream": "stdout",
        "text": "    u_2} : ∀ {K : Type u_1} {L : Type u_2} [inst : Field.{u_1} K] [inst_1 : NumberField.{u_1} K]"
      },
      {
        "stream": "stdout",
        "text": "  [inst_2 : Field.{u_2} L] [inst_3 : NumberField.{u_2} L] [inst_4 : Algebra.{u_1, u_2} K L] [IsGalois.{u_1, u_2} K L]"
      },
      {
        "stream": "stdout",
        "text": "  (v : HeightOneSpectrum.{u_1} (RingOfIntegers.{u_1} K)) (w : HeightOneSpectrum.{u_2} (RingOfIntegers.{u_2} L))"
      },
      {
        "stream": "stdout",
        "text": "  [inst_6 : Ideal.LiesOver.{u_1, u_2} (HeightOneSpectrum.asIdeal.{u_2} w) (HeightOneSpectrum.asIdeal.{u_1} v)]"
      },
      {
        "stream": "stdout",
        "text": "  (σ : Gal(L/K)),"
      },
      {
        "stream": "stdout",
        "text": "  Ne.{u_2 + 1} σ 1 →"
      },
      {
        "stream": "stdout",
        "text": "    IsArithFrobAt.{0, u_2, u_2} ℤ σ (HeightOneSpectrum.asIdeal.{u_2} w) →"
      },
      {
        "stream": "stdout",
        "text": "      Ne.{1}"
      },
      {
        "stream": "stdout",
        "text": "        (Module.finrank.{u_1, u_2} (HeightOneSpectrum.adicCompletion.{u_1, u_1} K v)"
      },
      {
        "stream": "stdout",
        "text": "          (HeightOneSpectrum.adicCompletion.{u_2, u_2} L w))"
      },
      {
        "stream": "stdout",
        "text": "        1"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditBridges.lean:61:0: 'ChebotarevAudit.localDegree_ne_one' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditBridges.lean:62:0: 'ChebotarevAudit.outside_finite_set' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditBridges.lean:63:0: 'ChebotarevAudit.unramified_of_not_dvd_discr' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/AuditBridges.lean:64:0: 'ChebotarevAudit.liesOver_of_prime_mem' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "Some required targets logged failures:"
      },
      {
        "stream": "stdout",
        "text": "- AuditBridges"
      },
      {
        "stream": "stderr",
        "text": "error: build failed"
      }
    ],
    "errors": 1,
    "warnings": 6
  },
  "threads": 2,
  "modules": [
    {
      "module": "AuditRoot",
      "source_sha256": "ac38a6e118e553a2053c1963892ca993f443fb55dbe5acbe5b67f54ff3c1f061"
    },
    {
      "module": "AuditBridges",
      "source_sha256": "bcc22369a8bb56de117b389458064438692812ba75f2224ad67b14c8ac95128f"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792946734.5128171,
    "bytes": 0,
    "removed_bytes": 0,
    "target_bytes": 4294967296,
    "size_scope": "observed_idle_namespaces",
    "active_namespaces_skipped": 1,
    "errors": []
  },
  "reused_modules": [],
  "built_modules": [
    "AuditRoot",
    "AuditBridges"
  ],
  "sources_sha256": "0e2a89bc16af98e1ea418abee73fc79707888575e87ca36eef34a322e6697186"
}
```
