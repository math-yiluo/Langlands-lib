# Hasse–Arf evidence: check 09

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

Exact private diagnostic record: `cdf02c6c-3423-4a53-aadd-763389bef704`.

<!-- evidence-file: 09-restoration-result.json -->

## 09-restoration-result.json

SHA256 of the exact UTF-8 block: `4ee31f91516ce688cf43c5880554f5ba9597637907486263c190419bb1ca4213`.

````json
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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/f741299c84374409bd9761171850850e\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+HasseArfAudit:olean"
    ],
    "returncode": 0,
    "stdout": "Build completed successfully (66 jobs).\n",
    "stderr": "",
    "duration_seconds": 0.7429881609859876,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [],
    "other_output": [
      {
        "stream": "stdout",
        "text": "Build completed successfully (66 jobs)."
      }
    ],
    "errors": 0,
    "warnings": 0
  },
  "threads": 2,
  "modules": [
    {
      "module": "HasseArfAudit",
      "source_sha256": "0edb569e3e4066cbed331a3a416a0776ce7f38bb8e8512e0b438442185140e5f"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792940764.2118294,
    "bytes": 0,
    "removed_bytes": 0,
    "target_bytes": 4294967296,
    "size_scope": "observed_idle_namespaces",
    "active_namespaces_skipped": 1,
    "errors": []
  },
  "reused_modules": [],
  "built_modules": [
    "HasseArfAudit"
  ],
  "sources_sha256": "31d4506cb57b40f436f4d717007675ff47002ef5e6c5bc0643d418053517dfc2",
  "inspection": {
    "module": "HasseArfAudit",
    "declaration": "HasseArfAudit.integrality",
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
      "declaration": "HasseArfAudit.integrality",
      "kind": "theorem",
      "level_parameters": [
        "uK",
        "uL"
      ],
      "module": "HasseArfAudit",
      "protocol": "task-based-lean-inspect@3",
      "statement_module": "",
      "statement_returns_prop": false,
      "statement_target_encoding": null,
      "target_matches": false,
      "type_encoding": "repr",
      "type_sha256": "5bb489391670f9b123db2fda14c812652b59bcf2f8b08dd52fc46747a6c26c31",
      "type_bytes": 22301,
      "expression_transport": "private files; exact UTF-8 fingerprints retained"
    },
    "process": {
      "argv": [
        "/home/taskhub/src/Task-based-auto-formalize/.tools/codex-0.160.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex",
        "-c",
        "permissions.lean.extends=\":workspace\"",
        "-c",
        "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/f741299c84374409bd9761171850850e\" = \"write\"}",
        "sandbox",
        "-P",
        "lean",
        "-C",
        "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/0/.lake/build/lib/lean",
        "--",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean",
        "--run",
        "/home/taskhub/src/Task-based-auto-formalize/src/task_based_auto_formalize/lean_tools/Inspect.lean",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0",
        "HasseArfAudit",
        "HasseArfAudit.integrality",
        "--output",
        "/home/taskhub/pilot/.task-based/lean-service/scratch/f741299c84374409bd9761171850850e/inspect-96c2abbddf3940968a8461b5d35b83f5/result.json"
      ],
      "returncode": 0,
      "stdout": "",
      "stderr": "",
      "duration_seconds": 44.08657333999872,
      "timed_out": false,
      "output_limited": false,
      "error": null,
      "tree_quiet": true
    },
    "proof_accepted": false,
    "validation_method": "lake-build"
  }
}
````
