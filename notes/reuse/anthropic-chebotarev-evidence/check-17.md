# Terminal development check 17

Official diagnostic `93a2cbec-84ae-4224-820d-f5eaad9bb4ed`. Exact UTF-8 JSON SHA256 `b6d336f088a4c52ff930db07d62dc0d4c40af893801fbb8fe4b0c953831c6ed4`. Restoration check of the unchanged AuditInspection module after context rotation. This is development evidence; `proof_accepted` is false.

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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/583be2a9bb3940e48f3cb0a40e167f2c\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
      "sandbox",
      "-P",
      "lean",
      "-C",
      "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1",
      "--",
      "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lake",
      "build",
      "+AuditInspection:olean"
    ],
    "returncode": 0,
    "stdout": "Build completed successfully (61 jobs).\n",
    "stderr": "",
    "duration_seconds": 1.177701500011608,
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
        "text": "Build completed successfully (61 jobs)."
      }
    ],
    "errors": 0,
    "warnings": 0
  },
  "threads": 2,
  "modules": [
    {
      "module": "AuditInspection",
      "source_sha256": "c36233614b9cb21d0fe5da0232c398960b6500122aa9a60a3361910b90b7b28f"
    }
  ],
  "environment_key": "22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "workspace": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1",
  "cache_directory": "/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3",
  "build_directory": "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1/.lake/build/lib/lean",
  "cache_retention": {
    "checked_at": 1792949402.116557,
    "bytes": 0,
    "removed_bytes": 0,
    "target_bytes": 4294967296,
    "size_scope": "observed_idle_namespaces",
    "active_namespaces_skipped": 1,
    "errors": []
  },
  "reused_modules": [],
  "built_modules": [
    "AuditInspection"
  ],
  "sources_sha256": "48f585f25027ea67e9ff5cbed675ec74d864a0ab941bac3b9c555388fd1c3997",
  "inspection": {
    "module": "AuditInspection",
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
      "module": "AuditInspection",
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
        "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1/.lake/build/lib/lean\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/583be2a9bb3940e48f3cb0a40e167f2c\" = \"write\"}",
        "sandbox",
        "-P",
        "lean",
        "-C",
        "/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/1/.lake/build/lib/lean",
        "--",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean",
        "--run",
        "/home/taskhub/src/Task-based-auto-formalize/src/task_based_auto_formalize/lean_tools/Inspect.lean",
        "/home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0",
        "AuditInspection",
        "NumberField.exists_prime_isArithFrobAt_of_isGalois",
        "--output",
        "/home/taskhub/pilot/.task-based/lean-service/scratch/583be2a9bb3940e48f3cb0a40e167f2c/inspect-a2271c92a75049c4a366078fedb7c1d3/result.json"
      ],
      "returncode": 0,
      "stdout": "",
      "stderr": "",
      "duration_seconds": 408.0268538380042,
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
