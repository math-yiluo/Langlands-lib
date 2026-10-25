# Terminal development check 05

Official diagnostic `e36e544d-3d25-46a7-b17c-a937c7d92222`. Exact UTF-8 JSON SHA256 `82f162aeda4e9896583503b76c8cae5dfd49eb0a61006e5fe639d287f16dc47a`. This record is development evidence; `proof_accepted` is false. Generated `sorryAx` entries in failed-check diagnostics are Lean error-recovery output, not accepted proofs or authored proof holes.

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
      "permissions.lean.filesystem={\":slash_tmp\" = \"read\", \"/run/user/1000\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/codex/auth.json\" = \"deny\", \"/home/taskhub/.local/share/task-based-auto-formalize/claude/.credentials.json\" = \"deny\", \"/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3\" = \"write\", \"/home/taskhub/pilot/.task-based/lean-service/scratch/ee22a75666c144f38c892ea91862a3de\" = \"write\", \"/home/taskhub/pilot/.task-based/objects/lake/cache/22845659c203b55e98bc8f4a938eb8c33879c2aa450dfa031290b57358b321c3\" = \"write\"}",
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
    "returncode": 1,
    "stdout": "⚠ [2/11] Built Definitions.Def_TaylorWiles_Primes (26s)\nwarning: source/Definitions/Def_TaylorWiles_Primes.lean:3:0: 'Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients' has been deprecated: please replace this import by\n\nimport Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic\nimport Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm\n⚠ [3/12] Built Definitions.Def_NarrowRayClassGroup (36s)\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:5:0: 'Mathlib.RingTheory.ClassGroup' has been deprecated: please replace this import by\n\nimport Mathlib.RingTheory.ClassGroup.Basic\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:8:0: 'Mathlib.Data.Fintype.Units' has been deprecated: please replace this import by\n\nimport Mathlib.Data.Finset.Attr\nimport Mathlib.Tactic.Bound.Init\nimport Mathlib.Tactic.Common\nimport Mathlib.Tactic.Finiteness.Attr\nimport Mathlib.Tactic.SetLike\nimport Mathlib.Util.CompileInductive\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:104:0: automatically included section variable(s) unused in theorem `Deep.NTSupply.mem_narrowRaySet_iff`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:178:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:219:0: automatically included section variable(s) unused in theorem `Deep.NTSupply.narrowRaySet_subset_raySet`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:353:13: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:452:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:490:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:518:18: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:544:17: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:594:20: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:797:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NarrowRayClassGroup.lean:832:15: `dif_pos` has been deprecated: Use `dite_eq_left` instead\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:966:0: 'Deep.NTSupply.coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:967:0: 'Deep.NTSupply.mem_coprimeToModulus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:968:0: 'Deep.NTSupply.narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:969:0: 'Deep.NTSupply.narrowRaySubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:970:0: 'Deep.NTSupply.narrowRaySubgroup_le_coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:971:0: 'Deep.NTSupply.NarrowRayClassGroup' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:972:0: 'Deep.NTSupply.NarrowRayClassGroup.mk' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:973:0: 'Deep.NTSupply.one_mem_narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:974:0: 'Deep.NTSupply.raySymbol' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:975:0: 'Deep.NTSupply.raySymbol_mul' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:976:0: 'Deep.NTSupply.raySymbolHom' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:977:0: 'Deep.NTSupply.raySymbolHom_prime' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:978:0: 'Deep.NTSupply.raySymbolDescend' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:979:0: 'Deep.NTSupply.raySymbolDescend_mk' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:980:0: 'Deep.NTSupply.raySymbolDescend_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:981:0: 'Deep.NTSupply.raySymbolIdealHom' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:982:0: 'Deep.NTSupply.primeUnit' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:983:0: 'Deep.NTSupply.primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:984:0: 'Deep.NTSupply.movingLemma' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:985:0: 'Deep.NTSupply.finite' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:986:0: 'Deep.NTSupply.coprimeToModulus_top' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NarrowRayClassGroup.lean:987:0: 'Deep.NTSupply.finite_closure_of_involutions' depends on axioms: [propext, Classical.choice, Quot.sound]\n✔ [4/12] Built Definitions.Def_FrobeniusDensity_DegOneAsymptotic (42s)\n⚠ [5/12] Built Definitions.Def_NumberField_RayCharacterData (37s)\nwarning: source/Definitions/Def_NumberField_RayCharacterData.lean:69:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_RayCharacterData.lean:69:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:79:0: 'M4aP2.signAt' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:80:0: 'M4aP2.chiIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:81:0: 'M4aP2.IsParity' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:82:0: 'M4aP2.chiFin' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:83:0: 'M4aP2.IsPrimitiveMod' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:84:0: 'M4aP2.addChar' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:85:0: 'M4aP2.gaussSumAt' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:86:0: 'M4aP2.IsGaussDatum' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:87:0: 'M4aP2.isParity_one_empty' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_NumberField_RayCharacterData.lean:88:0: 'M4aP2.isPrimitiveMod_top' depends on axioms: [propext, Classical.choice, Quot.sound]\n✔ [6/14] Built Definitions.Def_NumberField_CompletedRayL (11s)\n⚠ [7/14] Built Definitions.Def_LanglandsTunnell_NormClass (11s)\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:107:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:108:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:109:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:110:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:139:17: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:204:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:218:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:282:0: 'LanglandsTunnell.P2.Artin.norm_int_cast_eq_one_of_sub_one_mem' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:283:0: 'LanglandsTunnell.P2.Artin.norm_int_pos_of_totPos' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:284:0: 'LanglandsTunnell.P2.Artin.absNorm_coprime_of_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:285:0: 'LanglandsTunnell.P2.Artin.normClass' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:286:0: 'LanglandsTunnell.P2.Artin.normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:287:0: 'LanglandsTunnell.P2.Artin.raySymbol_normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:288:0: 'LanglandsTunnell.P2.Artin.normClassKillsRay' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:289:0: 'LanglandsTunnell.P2.Artin.normClassChar' depends on axioms: [propext, Classical.choice, Quot.sound]\ninfo: source/Definitions/Def_LanglandsTunnell_NormClass.lean:290:0: 'LanglandsTunnell.P2.Artin.normClassChar_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]\n⚠ [8/14] Built Definitions.Def_FrobeniusDensity_BadPrimes (5.9s)\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:64:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:66:31: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:93:19: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:99:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:112:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:113:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:125:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (4.7s)\n⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (70s)\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:61:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:90:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:91:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:112:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:111:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:205:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:216:34: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:291:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_PrimeNormSums.lean:287:6: Unused tactic linter: `beta_reduce` does nothing\n\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n⚠ [11/14] Built Definitions.Def_NumberField_NormResidueCharacter (78s)\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:97:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:20: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:102:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:102:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:119:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:123:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:152:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:152:34: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:180:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:181:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:182:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:203:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:204:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:206:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:240:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:254:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:256:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:257:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:258:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:259:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:274:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:281:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:282:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:284:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:297:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:306:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:307:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:337:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\n✔ [12/20] Built Definitions.Def_NumberField_EuclideanIdealLattice (7.6s)\n✔ [13/22] Built Definitions.Def_FrobeniusDensity_ClassGroupLSeries (18s)\n⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (37s)\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:32:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:38:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:45:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:59:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:33: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:100:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:103:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:104:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:165:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:164:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:204:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:209:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:223:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:225:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:234:30: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:237:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:250:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:258:9: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:263:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:272:32: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:277:5: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:276:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:295:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:296:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:313:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:316:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:319:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:321:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:323:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:334:68: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:336:16: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:483:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:485:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:486:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:490:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:492:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:493:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:502:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:502:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:504:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:508:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:508:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:510:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:517:35: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:518:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:562:14: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\n⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (17s)\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:73:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:74:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:141:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:142:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:183:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:184:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:187:6: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:207:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:208:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:209:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:210:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:221:15: `Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead.\nwarning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:221:69: `Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead.\n✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (19s)\n✔ [17/24] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (50s)\n⚠ [18/26] Built P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (17s)\nwarning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:40:42: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:46:37: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:80:21: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:87:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\n✔ [19/32] Built Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (10s)\n⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (6.7s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:38:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:71:46: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:107:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:109:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (7.3s)\n⚠ [25/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (12s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:30:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:31:2: `Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:37:45: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:38:4: `Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:39:41: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:44:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead.\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:100:8: `Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:111:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:112:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:142:14: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:147:14: `if_neg` has been deprecated: Use `ite_eq_right` instead\n⚠ [26/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (14s)\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:39:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:72:46: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:108:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead\nwarning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:110:18: `if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [27/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (11s)\n✔ [28/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (3.8s)\n✖ [29/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (183s)\ntrace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:152:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_fst`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:156:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic.mixedConjDil_apply_snd`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:524:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:572:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:608:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1077:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1295:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1296:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:1361:5: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:53: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:65: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:88: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2472:100: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2479:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2488:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2491:16: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2866:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:2867:2: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3008:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3009:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3077:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3472:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3478:6: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3481:6: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3482:60: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3504:24: This simp argument is unused:\n  smul_eq_mul\n\nHint: Omit it from the simp argument list.\n  [apply] simp only [smul_smul]\n\nNote: This linter can be disabled with `set_option linter.unusedSimpArgs false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3503:82: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice\n\nNote: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:13: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:3531:45: `ContinuousLinearMap.add_apply` has been deprecated: Use `add_apply` instead\n\nNote: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.add_apply` to `add_apply x`).\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4190:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4193:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4196:8: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4199:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aP2.mem_raySub`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4844:47: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4880:15: `OpenPartialHomeomorph.to_isOpenEmbedding` has been deprecated: Use `OpenPartialHomeomorph.isOpenEmbedding` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:4889:24: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5274:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5277:37: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5283:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5288:10: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5318:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5485:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5487:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5509:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5518:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5760:39: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5805:22: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5818:6: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5824:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5829:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5860:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:5981:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.unit_mul_mem_fracIdeal`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6140:8: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6141:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6167:51: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6168:78: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6249:17: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6260:75: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6266:15: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6489:10: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6881:56: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6894:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6895:23: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:31: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:6899:44: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7042:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7206:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_none`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7210:8: automatically included section variable(s) unused in theorem `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.fracIdealNonzeroEquiv_symm_some`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\n\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7715:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:7723:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8296:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:28: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8480:40: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8482:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8625:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8627:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8757:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8759:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8875:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8876:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:8879:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9053:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9445:12: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9454:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9458:19: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9572:32: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9582:32: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9591:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9635:36: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:12: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9642:25: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9645:23: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9728:14: `dif_neg` has been deprecated: Use `dite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:14: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9736:27: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9741:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9742:6: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9909:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9934:7: `Ideal.finite_setOf_absNorm_le₀` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_le₀` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9930:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9935:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9937:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:9986:32: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10013:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10014:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10060:35: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:18: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10265:69: `dif_pos` has been deprecated: Use `dite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10462:28: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10609:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10611:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10638:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10640:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10679:12: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10682:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10778:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10779:16: `if_pos` has been deprecated: Use `ite_eq_left` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10782:12: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10854:53: `if_true` has been deprecated: Use `ite_true` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10860:8: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:10928:24: `if_neg` has been deprecated: Use `ite_eq_right` instead\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11132:2: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11748:23: Application type mismatch: The argument\n  K\nhas type\n  Type audit_u\nof sort `Type (audit_u + 1)` but is expected to have type\n  Type u_1\nof sort `Type (u_1 + 1)` in the application\n  @RingOfIntegers K\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12028:23: Application type mismatch: The argument\n  K\nhas type\n  Type audit_u\nof sort `Type (audit_u + 1)` but is expected to have type\n  Type u_1\nof sort `Type (u_1 + 1)` in the application\n  @RingOfIntegers K\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12053:4: Try this: \n  haveI̵\n\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12054:4: Try this: \n  letI̵\n\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\n\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\nerror: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12041:0: declaration `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol.fe_of_ne_bot` contains universe level metavariables at the expression\n  Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)\n    fun (ι : Type ?u.39)\n      (h :\n        Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>\n          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n    Exists.casesOn.{?u.39 + 1} h\n      fun (w : Fintype.{?u.39} ι)\n        (h :\n          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n      Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h\n        fun 𝔞\n          (h :\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n        Exists.casesOn.{?u.39 + 1} h\n          fun α\n            (h :\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n          Exists.casesOn h\n            fun P₀\n              (h :\n                ∃ P₀',\n                  (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n            Exists.casesOn h\n              fun P₀'\n                (h :\n                  (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n              And.casesOn h\n                fun hα\n                  (right :\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                And.casesOn right\n                  fun\n                    (hT :\n                      ∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                    (right :\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                  And.casesOn right\n                    fun\n                      (hT' :\n                        ∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                      (right :\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                    And.casesOn right\n                      fun hinv\n                        (right :\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      ⋯ ∧ (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ⋯ (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      ⋯ ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                      And.casesOn right\n                        fun hinv' (right : (χ ≠ ⋯ → ∀ (x₀ : ι → K), ⋯) ∧ (χ ≠ ⋯ → ∀ (x₀' : ι → K), ⋯)) =>\n                        And.casesOn right fun (hcancel : ⋯) => ⋯\nin the declaration body\n  fun K [⋯] [⋯] 𝔣 χ S hpar h𝔣 =>\n    if h𝔣' : 𝔣 = ⊤ then\n      Eq.ndrec (motive := fun 𝔣 =>\n        ∀ (χ : NarrowRayClassGroup K 𝔣 →* ℂ), IsParity K 𝔣 χ S → 𝔣 ≠ ⊥ → ∃ F G, WallConj K 𝔣 χ S F G)\n        (fun χ hpar h𝔣 =>\n          Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)\n            fun (ι : Type ?u.39)\n              (h :\n                Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>\n                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n            Exists.casesOn.{?u.39 + 1} h\n              fun (w : Fintype.{?u.39} ι)\n                (h :\n                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n              Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h\n                fun 𝔞\n                  (h :\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n                Exists.casesOn.{?u.39 + 1} h\n                  fun α\n                    (h :\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n                  Exists.casesOn h\n                    fun P₀\n                      (h :\n                        ∃ P₀',\n                          (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                    Exists.casesOn h\n                      fun P₀'\n                        (h :\n                          (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                      And.casesOn h\n                        fun hα\n                          (right :\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                        And.casesOn right\n                          fun\n                            (hT :\n                              ∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                            (right :\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                          And.casesOn right\n                            fun\n                              (hT' :\n                                ∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                              (right :\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ⋯) ∧\n                                    (χ ≠ 1 → ∀ (x₀ : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯) ∧\n                                      (χ ≠ 1 → ∀ (x₀' : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯)) =>\n                            And.casesOn right\n                              fun hinv\n                                (right : (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), ⋯) ∧ (⋯ → ⋯) ∧ (⋯ → ⋯)) =>\n                              And.casesOn right fun hinv' => ⋯)\n        (Eq.symm h𝔣') χ hpar h𝔣\n    else\n      Exists.casesOn.{?u.69 + 2} (hole_T2.{audit_u, ?u.69} K 𝔣 χ S hpar h𝔣 h𝔣') fun (ι : ⋯) (h : ⋯) =>\n        Exists.casesOn.{?u.69 + 1} h fun (w : ⋯) (h : ⋯) =>\n          Exists.casesOn.{max (audit_u + 1) (?u.69 + 1)} h fun 𝔞 (h : ⋯) =>\n            Exists.casesOn.{?u.69 + 1} h\n              fun α\n                (h :\n                  Exists.{?u.69 + 1} fun α' =>\n                    (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ⋯),\n                                  (∀ (i : ⋯), IsCoprimeGenerator K 𝔣 χ (𝔞 ⋯) ⋯) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ⋯) =>\n              Exists.casesOn.{?u.69 + 1} h\n                fun α'\n                  (h :\n                    (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                And.casesOn h\n                  fun hα\n                    (right :\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                  And.casesOn right\n                    fun hα'\n                      (right :\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                    And.casesOn right\n                      fun\n                        (hT :\n                          ∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)\n                        (right :\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ⋯ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                      And.casesOn right\n                        fun\n                          (hT' :\n                            ∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s)\n                          (right :\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) =>\n                        And.casesOn right\n                          fun hαα'\n                            (right :\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → χ ≠ ⋯ → ∀ (s : ℂ), ⋯) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 ⋯ (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i)) →\n                                    χ ≠ ⋯ → ∀ (s : ℂ), ⋯) =>\n                          And.casesOn right\n                            fun (hcancel : ∀ (x₀ : ι → K), (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → ⋯)\n                              (hcancel' : ⋯) =>\n                            ⋯\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12073:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\nwarning: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12122:23: Variable name `h𝔣'` is not explicitly referenced.\n\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n✔ [33/43] Built P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (9.1s)\n✔ [34/43] Built Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO (3.6s)\nSome required targets logged failures:\n- P2M.Sol.S_M4aTorus_completedRayL_fe\n",
    "stderr": "error: build failed\n",
    "duration_seconds": 386.1249779780046,
    "timed_out": false,
    "output_limited": false,
    "error": null,
    "tree_quiet": true
  },
  "diagnostics": {
    "messages": [
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_TaylorWiles_Primes.lean",
        "pos": {
          "line": 3,
          "column": 0
        },
        "data": "'Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients' has been deprecated: please replace this import by\nimport Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic\nimport Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm\n⚠ [3/12] Built Definitions.Def_NarrowRayClassGroup (36s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 5,
          "column": 0
        },
        "data": "'Mathlib.RingTheory.ClassGroup' has been deprecated: please replace this import by\nimport Mathlib.RingTheory.ClassGroup.Basic"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 8,
          "column": 0
        },
        "data": "'Mathlib.Data.Fintype.Units' has been deprecated: please replace this import by\nimport Mathlib.Data.Finset.Attr\nimport Mathlib.Tactic.Bound.Init\nimport Mathlib.Tactic.Common\nimport Mathlib.Tactic.Finiteness.Attr\nimport Mathlib.Tactic.SetLike\nimport Mathlib.Util.CompileInductive"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 104,
          "column": 0
        },
        "data": "automatically included section variable(s) unused in theorem `Deep.NTSupply.mem_narrowRaySet_iff`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 178,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 219,
          "column": 0
        },
        "data": "automatically included section variable(s) unused in theorem `Deep.NTSupply.narrowRaySet_subset_raySet`:\n  [NumberField K]\nconsider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:\n  omit [NumberField K] in theorem ...\nNote: This linter can be disabled with `set_option linter.unusedSectionVars false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 353,
          "column": 13
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 452,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 490,
          "column": 17
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 518,
          "column": 18
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 544,
          "column": 17
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 594,
          "column": 20
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 797,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 832,
          "column": 15
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 966,
          "column": 0
        },
        "data": "'Deep.NTSupply.coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 967,
          "column": 0
        },
        "data": "'Deep.NTSupply.mem_coprimeToModulus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 968,
          "column": 0
        },
        "data": "'Deep.NTSupply.narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 969,
          "column": 0
        },
        "data": "'Deep.NTSupply.narrowRaySubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 970,
          "column": 0
        },
        "data": "'Deep.NTSupply.narrowRaySubgroup_le_coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 971,
          "column": 0
        },
        "data": "'Deep.NTSupply.NarrowRayClassGroup' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 972,
          "column": 0
        },
        "data": "'Deep.NTSupply.NarrowRayClassGroup.mk' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 973,
          "column": 0
        },
        "data": "'Deep.NTSupply.one_mem_narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 974,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbol' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 975,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbol_mul' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 976,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolHom' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 977,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolHom_prime' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 978,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolDescend' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 979,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolDescend_mk' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 980,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolDescend_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 981,
          "column": 0
        },
        "data": "'Deep.NTSupply.raySymbolIdealHom' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 982,
          "column": 0
        },
        "data": "'Deep.NTSupply.primeUnit' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 983,
          "column": 0
        },
        "data": "'Deep.NTSupply.primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 984,
          "column": 0
        },
        "data": "'Deep.NTSupply.movingLemma' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 985,
          "column": 0
        },
        "data": "'Deep.NTSupply.finite' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 986,
          "column": 0
        },
        "data": "'Deep.NTSupply.coprimeToModulus_top' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NarrowRayClassGroup.lean",
        "pos": {
          "line": 987,
          "column": 0
        },
        "data": "'Deep.NTSupply.finite_closure_of_involutions' depends on axioms: [propext, Classical.choice, Quot.sound]\n✔ [4/12] Built Definitions.Def_FrobeniusDensity_DegOneAsymptotic (42s)\n⚠ [5/12] Built Definitions.Def_NumberField_RayCharacterData (37s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 69,
          "column": 16
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 69,
          "column": 29
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 79,
          "column": 0
        },
        "data": "'M4aP2.signAt' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 80,
          "column": 0
        },
        "data": "'M4aP2.chiIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 81,
          "column": 0
        },
        "data": "'M4aP2.IsParity' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 82,
          "column": 0
        },
        "data": "'M4aP2.chiFin' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 83,
          "column": 0
        },
        "data": "'M4aP2.IsPrimitiveMod' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 84,
          "column": 0
        },
        "data": "'M4aP2.addChar' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 85,
          "column": 0
        },
        "data": "'M4aP2.gaussSumAt' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 86,
          "column": 0
        },
        "data": "'M4aP2.IsGaussDatum' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 87,
          "column": 0
        },
        "data": "'M4aP2.isParity_one_empty' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_NumberField_RayCharacterData.lean",
        "pos": {
          "line": 88,
          "column": 0
        },
        "data": "'M4aP2.isPrimitiveMod_top' depends on axioms: [propext, Classical.choice, Quot.sound]\n✔ [6/14] Built Definitions.Def_NumberField_CompletedRayL (11s)\n⚠ [7/14] Built Definitions.Def_LanglandsTunnell_NormClass (11s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 107,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 108,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 109,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 110,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 139,
          "column": 17
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 204,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 218,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 282,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.norm_int_cast_eq_one_of_sub_one_mem' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 283,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.norm_int_pos_of_totPos' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 284,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.absNorm_coprime_of_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 285,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.normClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 286,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 287,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.raySymbol_normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 288,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.normClassKillsRay' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 289,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.normClassChar' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "severity": "info",
        "fileName": "source/Definitions/Def_LanglandsTunnell_NormClass.lean",
        "pos": {
          "line": 290,
          "column": 0
        },
        "data": "'LanglandsTunnell.P2.Artin.normClassChar_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]\n⚠ [8/14] Built Definitions.Def_FrobeniusDensity_BadPrimes (5.9s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 64,
          "column": 15
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 66,
          "column": 31
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 93,
          "column": 19
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 99,
          "column": 19
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 112,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 113,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_FrobeniusDensity_BadPrimes.lean",
        "pos": {
          "line": 125,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`\n✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (4.7s)\n⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (70s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 61,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 90,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 91,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 112,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 111,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 205,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 216,
          "column": 34
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 291,
          "column": 17
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_PrimeNormSums.lean",
        "pos": {
          "line": 287,
          "column": 6
        },
        "data": "Unused tactic linter: `beta_reduce` does nothing\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n⚠ [11/14] Built Definitions.Def_NumberField_NormResidueCharacter (78s)"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 97,
          "column": 22
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 99,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 99,
          "column": 20
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 102,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 102,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 119,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 123,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 152,
          "column": 22
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 152,
          "column": 34
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 180,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 181,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 182,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
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
          "line": 204,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 206,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 240,
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
          "line": 256,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 257,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 258,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 259,
          "column": 2
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 274,
          "column": 2
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
          "line": 282,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 284,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 297,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 306,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 307,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/Definitions/Def_NumberField_NormResidueCharacter.lean",
        "pos": {
          "line": 337,
          "column": 19
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead\n✔ [12/20] Built Definitions.Def_NumberField_EuclideanIdealLattice (7.6s)\n✔ [13/22] Built Definitions.Def_FrobeniusDensity_ClassGroupLSeries (18s)\n⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (37s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 32,
          "column": 28
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 38,
          "column": 28
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 45,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 59,
          "column": 6
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 96,
          "column": 8
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 96,
          "column": 20
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 96,
          "column": 33
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 100,
          "column": 8
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 103,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 104,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 165,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 164,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 204,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 209,
          "column": 10
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 223,
          "column": 10
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 225,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 234,
          "column": 30
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 237,
          "column": 52
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 250,
          "column": 52
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 258,
          "column": 9
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 263,
          "column": 13
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 272,
          "column": 32
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 277,
          "column": 5
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 276,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 295,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 296,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 313,
          "column": 13
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 316,
          "column": 8
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 319,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 321,
          "column": 8
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 323,
          "column": 33
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 334,
          "column": 68
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 336,
          "column": 16
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 483,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 485,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 486,
          "column": 29
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 490,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 492,
          "column": 13
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 493,
          "column": 29
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 502,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 502,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 504,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 508,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 508,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 510,
          "column": 37
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 517,
          "column": 35
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 518,
          "column": 51
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean",
        "pos": {
          "line": 562,
          "column": 14
        },
        "data": "`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead\n⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (17s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 73,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 74,
          "column": 2
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 141,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 142,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 183,
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
          "line": 187,
          "column": 6
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
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 208,
          "column": 4
        },
        "data": "Try this: \n  haveI̵\nThe goal is a proposition, so `have` is preferred over `haveI`.\nThe difference between `have` and `haveI` is that `haveI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 209,
          "column": 4
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 210,
          "column": 4
        },
        "data": "Try this: \n  letI̵\nThe goal is a proposition, so `let` is preferred over `letI`.\nThe difference between `let` and `letI` is that `letI` inlines the value.\nBut this is not relevant for proofs because of proof irrelevance.\nNote: This linter can be disabled with `set_option linter.style.haveILetI false`"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 221,
          "column": 15
        },
        "data": "`Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean",
        "pos": {
          "line": 221,
          "column": 69
        },
        "data": "`Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead.\n✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (19s)\n✔ [17/24] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (50s)\n⚠ [18/26] Built P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (17s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean",
        "pos": {
          "line": 40,
          "column": 42
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean",
        "pos": {
          "line": 46,
          "column": 37
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean",
        "pos": {
          "line": 80,
          "column": 21
        },
        "data": "`dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean",
        "pos": {
          "line": 87,
          "column": 19
        },
        "data": "`dif_pos` has been deprecated: Use `dite_eq_left` instead\n✔ [19/32] Built Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (10s)\n⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (6.7s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 38,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 71,
          "column": 46
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 107,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean",
        "pos": {
          "line": 109,
          "column": 18
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (7.3s)\n⚠ [25/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (12s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 30,
          "column": 51
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 31,
          "column": 2
        },
        "data": "`Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 37,
          "column": 45
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 38,
          "column": 4
        },
        "data": "`Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 39,
          "column": 41
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 44,
          "column": 51
        },
        "data": "`Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 100,
          "column": 8
        },
        "data": "`Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 111,
          "column": 10
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 112,
          "column": 10
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 142,
          "column": 14
        },
        "data": "`if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean",
        "pos": {
          "line": 147,
          "column": 14
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n⚠ [26/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (14s)"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 39,
          "column": 59
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 72,
          "column": 46
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 108,
          "column": 7
        },
        "data": "`Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "severity": "warning",
        "fileName": "source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean",
        "pos": {
          "line": 110,
          "column": 18
        },
        "data": "`if_neg` has been deprecated: Use `ite_eq_right` instead\n✔ [27/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (11s)\n✔ [28/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (3.8s)\n✖ [29/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (183s)"
      },
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
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 11748,
          "column": 23
        },
        "data": "Application type mismatch: The argument\n  K\nhas type\n  Type audit_u\nof sort `Type (audit_u + 1)` but is expected to have type\n  Type u_1\nof sort `Type (u_1 + 1)` in the application\n  @RingOfIntegers K"
      },
      {
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12028,
          "column": 23
        },
        "data": "Application type mismatch: The argument\n  K\nhas type\n  Type audit_u\nof sort `Type (audit_u + 1)` but is expected to have type\n  Type u_1\nof sort `Type (u_1 + 1)` in the application\n  @RingOfIntegers K"
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
        "severity": "error",
        "fileName": "source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean",
        "pos": {
          "line": 12041,
          "column": 0
        },
        "data": "declaration `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol.fe_of_ne_bot` contains universe level metavariables at the expression\n  Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)\n    fun (ι : Type ?u.39)\n      (h :\n        Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>\n          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n    Exists.casesOn.{?u.39 + 1} h\n      fun (w : Fintype.{?u.39} ι)\n        (h :\n          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n      Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h\n        fun 𝔞\n          (h :\n            Exists.{?u.39 + 1} fun α =>\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n        Exists.casesOn.{?u.39 + 1} h\n          fun α\n            (h :\n              ∃ P₀ P₀',\n                (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                  (∀ (s : ℂ),\n                      1 < s.re →\n                        completedRayL K ⊤ χ S s =\n                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                            ∀ t ∈ orthant K,\n                              ∀ (s : ℂ),\n                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                  topInvDual K χ S 𝔟 x₀ s t +\n                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (χ ≠ 1 →\n                              ∀ (x₀ : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                            (χ ≠ 1 →\n                              ∀ (x₀' : ι → K),\n                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                  ∀ (s : ℂ),\n                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                          α i s *\n                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                              (x₀' i)) =\n                                        0 ∧\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n          Exists.casesOn h\n            fun P₀\n              (h :\n                ∃ P₀',\n                  (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n            Exists.casesOn h\n              fun P₀'\n                (h :\n                  (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n              And.casesOn h\n                fun hα\n                  (right :\n                    (∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                And.casesOn right\n                  fun\n                    (hT :\n                      ∀ (s : ℂ),\n                        1 < s.re →\n                          completedRayL K ⊤ χ S s =\n                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                    (right :\n                      (∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t +\n                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                            α i s *\n                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                (x₀' i)) =\n                                          0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                  And.casesOn right\n                    fun\n                      (hT' :\n                        ∀ (s : ℂ),\n                          1 < s.re →\n                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                      (right :\n                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                              ∀ t ∈ orthant K,\n                                ∀ (s : ℂ),\n                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                    topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                ∀ t ∈ orthant K,\n                                  ∀ (s : ℂ),\n                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                      ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                    And.casesOn right\n                      fun hinv\n                        (right :\n                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧\n                            (χ ≠ 1 →\n                                ∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                    ∀ (s : ℂ),\n                                      ⋯ ∧ (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧\n                              (χ ≠ 1 →\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ⋯ (𝔞 i) (x₀' i)) →\n                                    ∀ (s : ℂ),\n                                      ⋯ ∧\n                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>\n                      And.casesOn right\n                        fun hinv' (right : (χ ≠ ⋯ → ∀ (x₀ : ι → K), ⋯) ∧ (χ ≠ ⋯ → ∀ (x₀' : ι → K), ⋯)) =>\n                        And.casesOn right fun (hcancel : ⋯) => ⋯\nin the declaration body\n  fun K [⋯] [⋯] 𝔣 χ S hpar h𝔣 =>\n    if h𝔣' : 𝔣 = ⊤ then\n      Eq.ndrec (motive := fun 𝔣 =>\n        ∀ (χ : NarrowRayClassGroup K 𝔣 →* ℂ), IsParity K 𝔣 χ S → 𝔣 ≠ ⊥ → ∃ F G, WallConj K 𝔣 χ S F G)\n        (fun χ hpar h𝔣 =>\n          Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)\n            fun (ι : Type ?u.39)\n              (h :\n                Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>\n                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n            Exists.casesOn.{?u.39 + 1} h\n              fun (w : Fintype.{?u.39} ι)\n                (h :\n                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n              Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h\n                fun 𝔞\n                  (h :\n                    Exists.{?u.39 + 1} fun α =>\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n                Exists.casesOn.{?u.39 + 1} h\n                  fun α\n                    (h :\n                      ∃ P₀ P₀',\n                        (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K ⊤ χ S s =\n                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s *\n                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                    ∀ t ∈ orthant K,\n                                      ∀ (s : ℂ),\n                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                          topInvDual K χ S 𝔟 x₀ s t +\n                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s\n                                              t⁻¹ =\n                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (χ ≠ 1 →\n                                      ∀ (x₀ : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                0) ∧\n                                    (χ ≠ 1 →\n                                      ∀ (x₀' : ι → K),\n                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                          ∀ (s : ℂ),\n                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                  α i s *\n                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot\n                                                      (x₀' i)) =\n                                                0 ∧\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                0)) =>\n                  Exists.casesOn h\n                    fun P₀\n                      (h :\n                        ∃ P₀',\n                          (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                    Exists.casesOn h\n                      fun P₀'\n                        (h :\n                          (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                      And.casesOn h\n                        fun hα\n                          (right :\n                            (∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t +\n                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *\n                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +\n                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *\n                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                                    α i s *\n                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)\n                                                        top_ne_bot (x₀' i)) =\n                                                  0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                        And.casesOn right\n                          fun\n                            (hT :\n                              ∀ (s : ℂ),\n                                1 < s.re →\n                                  completedRayL K ⊤ χ S s =\n                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                            (right :\n                              (∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))\n                                            s) ∧\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →\n                                      ∀ t ∈ orthant K,\n                                        ∀ (s : ℂ),\n                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ =\n                                            topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +\n                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →\n                                        ∀ t ∈ orthant K,\n                                          ∀ (s : ℂ),\n                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)\n                                                s t⁻¹ =\n                                              ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧\n                                    (χ ≠ 1 →\n                                        ∀ (x₀ : ι → K),\n                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) =\n                                                  0) ∧\n                                      (χ ≠ 1 →\n                                        ∀ (x₀' : ι → K),\n                                          (∀ (i : ι),\n                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →\n                                            ∀ (s : ℂ),\n                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧\n                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) =\n                                                  0)) =>\n                          And.casesOn right\n                            fun\n                              (hT' :\n                                ∀ (s : ℂ),\n                                  1 < s.re →\n                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s =\n                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>\n                                        α i s *\n                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)\n                              (right :\n                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧\n                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),\n                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ⋯) ∧\n                                    (χ ≠ 1 → ∀ (x₀ : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯) ∧\n                                      (χ ≠ 1 → ∀ (x₀' : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯)) =>\n                            And.casesOn right\n                              fun hinv\n                                (right : (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), ⋯) ∧ (⋯ → ⋯) ∧ (⋯ → ⋯)) =>\n                              And.casesOn right fun hinv' => ⋯)\n        (Eq.symm h𝔣') χ hpar h𝔣\n    else\n      Exists.casesOn.{?u.69 + 2} (hole_T2.{audit_u, ?u.69} K 𝔣 χ S hpar h𝔣 h𝔣') fun (ι : ⋯) (h : ⋯) =>\n        Exists.casesOn.{?u.69 + 1} h fun (w : ⋯) (h : ⋯) =>\n          Exists.casesOn.{max (audit_u + 1) (?u.69 + 1)} h fun 𝔞 (h : ⋯) =>\n            Exists.casesOn.{?u.69 + 1} h\n              fun α\n                (h :\n                  Exists.{?u.69 + 1} fun α' =>\n                    (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ⋯),\n                                  (∀ (i : ⋯), IsCoprimeGenerator K 𝔣 χ (𝔞 ⋯) ⋯) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ⋯) =>\n              Exists.casesOn.{?u.69 + 1} h\n                fun α'\n                  (h :\n                    (∀ (i : ι), Differentiable ℂ (α i)) ∧\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                And.casesOn h\n                  fun hα\n                    (right :\n                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                  And.casesOn right\n                    fun hα'\n                      (right :\n                        (∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                    And.casesOn right\n                      fun\n                        (hT :\n                          ∀ (s : ℂ),\n                            1 < s.re →\n                              completedRayL K 𝔣 χ S s =\n                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)\n                        (right :\n                          (∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α i s *\n                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) =\n                                          0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 →\n                                      ∀ (s : ℂ),\n                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                            α' i s *\n                                              ((∑ a, chiFin K 𝔣 ⋯ S (Quotient.out a)) *\n                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S\n                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) =\n                                          0) =>\n                      And.casesOn right\n                        fun\n                          (hT' :\n                            ∀ (s : ℂ),\n                              1 < s.re →\n                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s =\n                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>\n                                    α' i s *\n                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s)\n                          (right :\n                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →\n                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι),\n                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))\n                                        (x₀' i)) →\n                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) =>\n                        And.casesOn right\n                          fun hαα'\n                            (right :\n                              (∀ (x₀ : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → χ ≠ ⋯ → ∀ (s : ℂ), ⋯) ∧\n                                ∀ (x₀' : ι → K),\n                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 ⋯ (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i)) →\n                                    χ ≠ ⋯ → ∀ (s : ℂ), ⋯) =>\n                          And.casesOn right\n                            fun (hcancel : ∀ (x₀ : ι → K), (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → ⋯)\n                              (hcancel' : ⋯) =>\n                            ⋯"
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
        "data": "Variable name `h𝔣'` is not explicitly referenced.\nHint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:\n  [apply] _h𝔣'\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n✔ [33/43] Built P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (9.1s)\n✔ [34/43] Built Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO (3.6s)\nSome required targets logged failures:\n- P2M.Sol.S_M4aTorus_completedRayL_fe"
      }
    ],
    "other_output": [
      {
        "stream": "stdout",
        "text": "⚠ [2/11] Built Definitions.Def_TaylorWiles_Primes (26s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_TaylorWiles_Primes.lean:3:0: 'Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients' has been deprecated: please replace this import by"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm"
      },
      {
        "stream": "stdout",
        "text": "⚠ [3/12] Built Definitions.Def_NarrowRayClassGroup (36s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:5:0: 'Mathlib.RingTheory.ClassGroup' has been deprecated: please replace this import by"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.RingTheory.ClassGroup.Basic"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:8:0: 'Mathlib.Data.Fintype.Units' has been deprecated: please replace this import by"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Data.Finset.Attr"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Tactic.Bound.Init"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Tactic.Common"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Tactic.Finiteness.Attr"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Tactic.SetLike"
      },
      {
        "stream": "stdout",
        "text": "import Mathlib.Util.CompileInductive"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:104:0: automatically included section variable(s) unused in theorem `Deep.NTSupply.mem_narrowRaySet_iff`:"
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
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:178:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:219:0: automatically included section variable(s) unused in theorem `Deep.NTSupply.narrowRaySet_subset_raySet`:"
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
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:353:13: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:452:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:490:17: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:518:18: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:544:17: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:594:20: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:797:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NarrowRayClassGroup.lean:832:15: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:966:0: 'Deep.NTSupply.coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:967:0: 'Deep.NTSupply.mem_coprimeToModulus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:968:0: 'Deep.NTSupply.narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:969:0: 'Deep.NTSupply.narrowRaySubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:970:0: 'Deep.NTSupply.narrowRaySubgroup_le_coprimeToModulus' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:971:0: 'Deep.NTSupply.NarrowRayClassGroup' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:972:0: 'Deep.NTSupply.NarrowRayClassGroup.mk' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:973:0: 'Deep.NTSupply.one_mem_narrowRaySet' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:974:0: 'Deep.NTSupply.raySymbol' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:975:0: 'Deep.NTSupply.raySymbol_mul' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:976:0: 'Deep.NTSupply.raySymbolHom' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:977:0: 'Deep.NTSupply.raySymbolHom_prime' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:978:0: 'Deep.NTSupply.raySymbolDescend' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:979:0: 'Deep.NTSupply.raySymbolDescend_mk' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:980:0: 'Deep.NTSupply.raySymbolDescend_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:981:0: 'Deep.NTSupply.raySymbolIdealHom' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:982:0: 'Deep.NTSupply.primeUnit' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:983:0: 'Deep.NTSupply.primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:984:0: 'Deep.NTSupply.movingLemma' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:985:0: 'Deep.NTSupply.finite' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:986:0: 'Deep.NTSupply.coprimeToModulus_top' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NarrowRayClassGroup.lean:987:0: 'Deep.NTSupply.finite_closure_of_involutions' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "✔ [4/12] Built Definitions.Def_FrobeniusDensity_DegOneAsymptotic (42s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [5/12] Built Definitions.Def_NumberField_RayCharacterData (37s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_RayCharacterData.lean:69:16: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_RayCharacterData.lean:69:29: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:79:0: 'M4aP2.signAt' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:80:0: 'M4aP2.chiIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:81:0: 'M4aP2.IsParity' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:82:0: 'M4aP2.chiFin' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:83:0: 'M4aP2.IsPrimitiveMod' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:84:0: 'M4aP2.addChar' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:85:0: 'M4aP2.gaussSumAt' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:86:0: 'M4aP2.IsGaussDatum' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:87:0: 'M4aP2.isParity_one_empty' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_NumberField_RayCharacterData.lean:88:0: 'M4aP2.isPrimitiveMod_top' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "✔ [6/14] Built Definitions.Def_NumberField_CompletedRayL (11s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [7/14] Built Definitions.Def_LanglandsTunnell_NormClass (11s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:107:2: Try this: "
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
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:108:2: Try this: "
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
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:109:2: Try this: "
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
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:110:2: Try this: "
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
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:139:17: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:204:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_LanglandsTunnell_NormClass.lean:218:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:282:0: 'LanglandsTunnell.P2.Artin.norm_int_cast_eq_one_of_sub_one_mem' depends on axioms: [propext,"
      },
      {
        "stream": "stdout",
        "text": " Classical.choice,"
      },
      {
        "stream": "stdout",
        "text": " Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:283:0: 'LanglandsTunnell.P2.Artin.norm_int_pos_of_totPos' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:284:0: 'LanglandsTunnell.P2.Artin.absNorm_coprime_of_not_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:285:0: 'LanglandsTunnell.P2.Artin.normClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:286:0: 'LanglandsTunnell.P2.Artin.normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:287:0: 'LanglandsTunnell.P2.Artin.raySymbol_normClass_coe' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:288:0: 'LanglandsTunnell.P2.Artin.normClassKillsRay' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:289:0: 'LanglandsTunnell.P2.Artin.normClassChar' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "info: source/Definitions/Def_LanglandsTunnell_NormClass.lean:290:0: 'LanglandsTunnell.P2.Artin.normClassChar_primeClass' depends on axioms: [propext, Classical.choice, Quot.sound]"
      },
      {
        "stream": "stdout",
        "text": "⚠ [8/14] Built Definitions.Def_FrobeniusDensity_BadPrimes (5.9s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:64:15: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:66:31: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:93:19: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:99:19: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:112:2: Try this: "
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
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:113:2: Try this: "
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
        "text": "warning: source/Definitions/Def_FrobeniusDensity_BadPrimes.lean:125:2: Try this: "
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
        "text": "✔ [9/14] Built Definitions.Def_FrobeniusDensity_PrimeSums (4.7s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [10/14] Built Definitions.Def_NumberField_PrimeNormSums (70s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:61:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:90:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:91:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:112:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:111:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:205:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:216:34: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:291:17: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_PrimeNormSums.lean:287:6: Unused tactic linter: `beta_reduce` does nothing"
      },
      {
        "stream": "stdout",
        "text": "Note: This linter can be disabled with `set_option linter.unusedTactic false`"
      },
      {
        "stream": "stdout",
        "text": "⚠ [11/14] Built Definitions.Def_NumberField_NormResidueCharacter (78s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:97:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:99:20: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:102:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:102:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:119:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:123:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:152:22: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:152:34: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:180:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:181:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:182:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:204:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:206:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:240:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:256:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:257:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:258:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:259:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:274:2: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:282:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:284:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:297:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:306:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:307:4: Try this: "
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
        "text": "warning: source/Definitions/Def_NumberField_NormResidueCharacter.lean:337:19: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [12/20] Built Definitions.Def_NumberField_EuclideanIdealLattice (7.6s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [13/22] Built Definitions.Def_FrobeniusDensity_ClassGroupLSeries (18s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [14/22] Built P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (37s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:32:28: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:38:28: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:45:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:59:6: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:8: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:20: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:96:33: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:100:8: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:103:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:104:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:165:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:164:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:204:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:209:10: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:223:10: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:225:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:234:30: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:237:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:250:52: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:258:9: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:263:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:272:32: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:277:5: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:276:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:295:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:296:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:313:13: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:316:8: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:319:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:321:8: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:323:33: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:334:68: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:336:16: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:483:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:485:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:486:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:490:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:492:13: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:493:29: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:502:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:502:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:504:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:508:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:508:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:510:37: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:517:35: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:518:51: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean:562:14: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "⚠ [15/22] Built P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (17s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:73:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:74:2: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:141:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:142:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:183:6: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:187:6: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:208:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:209:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:210:4: Try this: "
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
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:221:15: `Ideal.inertiaDeg'_eq_inertiaDeg` has been deprecated: Use `inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean:221:69: `Ideal.inertiaDeg'_algebraMap` has been deprecated: Use `Ideal.inertiaDeg_eq_of_isMaximal` instead."
      },
      {
        "stream": "stdout",
        "text": "✔ [16/24] Built Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (19s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [17/24] Built Theorems.Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (50s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [18/26] Built P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (17s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:40:42: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:46:37: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:80:21: `dif_neg` has been deprecated: Use `dite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean:87:19: `dif_pos` has been deprecated: Use `dite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [19/32] Built Theorems.Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal (10s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [23/43] Built P2M.Sol.S_FrobeniusDensity_idealSum_ne_top (6.7s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:38:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:71:46: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:107:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean:109:18: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [24/43] Built Theorems.Thm_FrobeniusDensity_idealSum_ne_top (7.3s)"
      },
      {
        "stream": "stdout",
        "text": "⚠ [25/43] Built P2M.Sol.S_FrobeniusDensity_tailSum_le (12s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:30:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:31:2: `Ideal.absNorm_eq_pow_inertiaDeg'` has been deprecated: Use `Ideal.natAbs_pow_inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:37:45: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:38:4: `Ideal.inertiaDeg'_pos` has been deprecated: Use `Ideal.inertiaDeg_pos` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:39:41: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:44:51: `Ideal.inertiaDeg'` has been deprecated: Use `Ideal.inertiaDeg` instead."
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:100:8: `Ideal.card_primesOverFinset_le_finrank` has been deprecated: Use results of RingTheory.RamificationInertia.Basic"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:111:10: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:112:10: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:142:14: `if_pos` has been deprecated: Use `ite_eq_left` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tailSum_le.lean:147:14: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "⚠ [26/43] Built P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (14s)"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:39:59: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:72:46: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:108:7: `Ideal.finite_setOf_absNorm_eq` has been deprecated: Use `Ideal.finite_setOfPred_absNorm_eq` instead"
      },
      {
        "stream": "stdout",
        "text": "warning: source/P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean:110:18: `if_neg` has been deprecated: Use `ite_eq_right` instead"
      },
      {
        "stream": "stdout",
        "text": "✔ [27/43] Built Theorems.Thm_FrobeniusDensity_tailSum_le (11s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [28/43] Built Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (3.8s)"
      },
      {
        "stream": "stdout",
        "text": "✖ [29/43] Building P2M.Sol.S_M4aTorus_completedRayL_fe (183s)"
      },
      {
        "stream": "stdout",
        "text": "trace: .> LEAN_PATH=/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/plausible/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/importGraph/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/aesop/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/Qq/.lake/build/lib/lean:/home/taskhub/pilot/.dependencies/lm-8666e50ce94d/mathlib/.lake/packages/batteries/.lake/build/lib/lean:/home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean /home/taskhub/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean --json /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean -o /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.olean -i /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/lib/lean/P2M/Sol/S_M4aTorus_completedRayL_fe.ilean -c /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.c --setup /home/taskhub/pilot/.task-based/objects/lake/workspaces/22845659c203b55e98bc/3/.lake/build/ir/P2M/Sol/S_M4aTorus_completedRayL_fe.setup.json --json"
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
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:11748:23: Application type mismatch: The argument"
      },
      {
        "stream": "stdout",
        "text": "  K"
      },
      {
        "stream": "stdout",
        "text": "has type"
      },
      {
        "stream": "stdout",
        "text": "  Type audit_u"
      },
      {
        "stream": "stdout",
        "text": "of sort `Type (audit_u + 1)` but is expected to have type"
      },
      {
        "stream": "stdout",
        "text": "  Type u_1"
      },
      {
        "stream": "stdout",
        "text": "of sort `Type (u_1 + 1)` in the application"
      },
      {
        "stream": "stdout",
        "text": "  @RingOfIntegers K"
      },
      {
        "stream": "stdout",
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12028:23: Application type mismatch: The argument"
      },
      {
        "stream": "stdout",
        "text": "  K"
      },
      {
        "stream": "stdout",
        "text": "has type"
      },
      {
        "stream": "stdout",
        "text": "  Type audit_u"
      },
      {
        "stream": "stdout",
        "text": "of sort `Type (audit_u + 1)` but is expected to have type"
      },
      {
        "stream": "stdout",
        "text": "  Type u_1"
      },
      {
        "stream": "stdout",
        "text": "of sort `Type (u_1 + 1)` in the application"
      },
      {
        "stream": "stdout",
        "text": "  @RingOfIntegers K"
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
        "text": "error: source/P2M/Sol/S_M4aTorus_completedRayL_fe.lean:12041:0: declaration `_private.P2M.Sol.S_M4aTorus_completedRayL_fe.0.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus.WallSol.fe_of_ne_bot` contains universe level metavariables at the expression"
      },
      {
        "stream": "stdout",
        "text": "  Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)"
      },
      {
        "stream": "stdout",
        "text": "    fun (ι : Type ?u.39)"
      },
      {
        "stream": "stdout",
        "text": "      (h :"
      },
      {
        "stream": "stdout",
        "text": "        Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>"
      },
      {
        "stream": "stdout",
        "text": "          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>"
      },
      {
        "stream": "stdout",
        "text": "            Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "              ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                      1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                        completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                            ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                  topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                              (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "    Exists.casesOn.{?u.39 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "      fun (w : Fintype.{?u.39} ι)"
      },
      {
        "stream": "stdout",
        "text": "        (h :"
      },
      {
        "stream": "stdout",
        "text": "          Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>"
      },
      {
        "stream": "stdout",
        "text": "            Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "              ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                      1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                        completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                            ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                  topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                              (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "      Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h"
      },
      {
        "stream": "stdout",
        "text": "        fun 𝔞"
      },
      {
        "stream": "stdout",
        "text": "          (h :"
      },
      {
        "stream": "stdout",
        "text": "            Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "              ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                      1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                        completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                            ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                  topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                              (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "        Exists.casesOn.{?u.39 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "          fun α"
      },
      {
        "stream": "stdout",
        "text": "            (h :"
      },
      {
        "stream": "stdout",
        "text": "              ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                      1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                        completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                          Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                            α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                          IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                            ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                  topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                      rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                    P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                          ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                          α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                            rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                              (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                        0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "          Exists.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "            fun P₀"
      },
      {
        "stream": "stdout",
        "text": "              (h :"
      },
      {
        "stream": "stdout",
        "text": "                ∃ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                          1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "            Exists.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "              fun P₀'"
      },
      {
        "stream": "stdout",
        "text": "                (h :"
      },
      {
        "stream": "stdout",
        "text": "                  (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                          1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "              And.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "                fun hα"
      },
      {
        "stream": "stdout",
        "text": "                  (right :"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                          1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                  fun"
      },
      {
        "stream": "stdout",
        "text": "                    (hT :"
      },
      {
        "stream": "stdout",
        "text": "                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                        1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                          completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                            Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                              α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)"
      },
      {
        "stream": "stdout",
        "text": "                    (right :"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                          1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                        rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                      topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                          rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                            ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                        P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                  And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                    fun"
      },
      {
        "stream": "stdout",
        "text": "                      (hT' :"
      },
      {
        "stream": "stdout",
        "text": "                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                          1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                            completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                              Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                α i s * rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)"
      },
      {
        "stream": "stdout",
        "text": "                      (right :"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                            IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                    topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                      P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                  ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                    rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                      ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                    And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                      fun hinv"
      },
      {
        "stream": "stdout",
        "text": "                        (right :"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      ⋯ ∧ (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K ⊤ ⋯ (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                      ⋯ ∧"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) = 0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                      And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                        fun hinv' (right : (χ ≠ ⋯ → ∀ (x₀ : ι → K), ⋯) ∧ (χ ≠ ⋯ → ∀ (x₀' : ι → K), ⋯)) =>"
      },
      {
        "stream": "stdout",
        "text": "                        And.casesOn right fun (hcancel : ⋯) => ⋯"
      },
      {
        "stream": "stdout",
        "text": "in the declaration body"
      },
      {
        "stream": "stdout",
        "text": "  fun K [⋯] [⋯] 𝔣 χ S hpar h𝔣 =>"
      },
      {
        "stream": "stdout",
        "text": "    if h𝔣' : 𝔣 = ⊤ then"
      },
      {
        "stream": "stdout",
        "text": "      Eq.ndrec (motive := fun 𝔣 =>"
      },
      {
        "stream": "stdout",
        "text": "        ∀ (χ : NarrowRayClassGroup K 𝔣 →* ℂ), IsParity K 𝔣 χ S → 𝔣 ≠ ⊥ → ∃ F G, WallConj K 𝔣 χ S F G)"
      },
      {
        "stream": "stdout",
        "text": "        (fun χ hpar h𝔣 =>"
      },
      {
        "stream": "stdout",
        "text": "          Exists.casesOn.{?u.39 + 2} (hole_top.{audit_u, ?u.39} K χ S hpar)"
      },
      {
        "stream": "stdout",
        "text": "            fun (ι : Type ?u.39)"
      },
      {
        "stream": "stdout",
        "text": "              (h :"
      },
      {
        "stream": "stdout",
        "text": "                Exists.{?u.39 + 1} fun (x : Fintype.{?u.39} ι) =>"
      },
      {
        "stream": "stdout",
        "text": "                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>"
      },
      {
        "stream": "stdout",
        "text": "                    Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "                      ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                          topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s"
      },
      {
        "stream": "stdout",
        "text": "                                              t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                      (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0)) =>"
      },
      {
        "stream": "stdout",
        "text": "            Exists.casesOn.{?u.39 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "              fun (w : Fintype.{?u.39} ι)"
      },
      {
        "stream": "stdout",
        "text": "                (h :"
      },
      {
        "stream": "stdout",
        "text": "                  Exists.{max (audit_u + 1) (?u.39 + 1)} fun 𝔞 =>"
      },
      {
        "stream": "stdout",
        "text": "                    Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "                      ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                          topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s"
      },
      {
        "stream": "stdout",
        "text": "                                              t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                      (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0)) =>"
      },
      {
        "stream": "stdout",
        "text": "              Exists.casesOn.{max (audit_u + 1) (?u.39 + 1)} h"
      },
      {
        "stream": "stdout",
        "text": "                fun 𝔞"
      },
      {
        "stream": "stdout",
        "text": "                  (h :"
      },
      {
        "stream": "stdout",
        "text": "                    Exists.{?u.39 + 1} fun α =>"
      },
      {
        "stream": "stdout",
        "text": "                      ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                          topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s"
      },
      {
        "stream": "stdout",
        "text": "                                              t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                      (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                Exists.casesOn.{?u.39 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "                  fun α"
      },
      {
        "stream": "stdout",
        "text": "                    (h :"
      },
      {
        "stream": "stdout",
        "text": "                      ∃ P₀ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                  IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                    ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                          topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                              rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                            P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟) s"
      },
      {
        "stream": "stdout",
        "text": "                                              t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                        (∀ (i : ι), IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                  α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                    rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) top_ne_bot"
      },
      {
        "stream": "stdout",
        "text": "                                                      (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                  Exists.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "                    fun P₀"
      },
      {
        "stream": "stdout",
        "text": "                      (h :"
      },
      {
        "stream": "stdout",
        "text": "                        ∃ P₀',"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                        α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                            s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)"
      },
      {
        "stream": "stdout",
        "text": "                                                s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)"
      },
      {
        "stream": "stdout",
        "text": "                                                        top_ne_bot (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                    Exists.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "                      fun P₀'"
      },
      {
        "stream": "stdout",
        "text": "                        (h :"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                        α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                            s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)"
      },
      {
        "stream": "stdout",
        "text": "                                                s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)"
      },
      {
        "stream": "stdout",
        "text": "                                                        top_ne_bot (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                      And.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "                        fun hα"
      },
      {
        "stream": "stdout",
        "text": "                          (right :"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                        α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                            s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K χ S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K ⊤ χ S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                  ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)"
      },
      {
        "stream": "stdout",
        "text": "                                                s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                              topInvDual K ((↑(starRingEnd ℂ)).comp χ) S 𝔟 x₀ s t +"
      },
      {
        "stream": "stdout",
        "text": "                                                  rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 top_ne_bot x₀ *"
      },
      {
        "stream": "stdout",
        "text": "                                                    ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                                P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s * rayInvPolarCoeff K ⊤ χ S (𝔞 i) top_ne_bot (x₀ i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                                    α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                                      rayInvPolarCoeff K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i)"
      },
      {
        "stream": "stdout",
        "text": "                                                        top_ne_bot (x₀' i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                        And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                          fun"
      },
      {
        "stream": "stdout",
        "text": "                            (hT :"
      },
      {
        "stream": "stdout",
        "text": "                              ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                  completedRayL K ⊤ χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                    Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                      α i s * rayFoldMellin K ⊤ χ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)"
      },
      {
        "stream": "stdout",
        "text": "                            (right :"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                        α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                            s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellinIntegrand K ⊤ χ S 𝔟 (rayScale K ⊤ 𝔟) s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                            topInvDual K χ S 𝔟 x₀ s t + ⋯ * ↑(torusNorm K t) ^ ((1 - s) / 2) +"
      },
      {
        "stream": "stdout",
        "text": "                                              P₀ 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ t ∈ orthant K,"
      },
      {
        "stream": "stdout",
        "text": "                                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                            rayFoldMellinIntegrand K ⊤ ((↑(starRingEnd ℂ)).comp χ) S 𝔟 (rayScale K ⊤ 𝔟)"
      },
      {
        "stream": "stdout",
        "text": "                                                s t⁻¹ ="
      },
      {
        "stream": "stdout",
        "text": "                                              ⋯ + ⋯ + P₀' 𝔟 * ↑(torusNorm K t) ^ (-s / 2)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι), IsCoprimeGenerator K ⊤ χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀ (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                        ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                          (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                              IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) (𝔞 i) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                              (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => ⋯) = 0 ∧"
      },
      {
        "stream": "stdout",
        "text": "                                                (Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i => α i s * P₀' (𝔞 i)) ="
      },
      {
        "stream": "stdout",
        "text": "                                                  0)) =>"
      },
      {
        "stream": "stdout",
        "text": "                          And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                            fun"
      },
      {
        "stream": "stdout",
        "text": "                              (hT' :"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                  1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                    completedRayL K ⊤ ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                      Finset.sum.{?u.39, 0} Finset.univ.{?u.39} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                        α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                          rayFoldMellin K ⊤ ((↑(starRingEnd ℂ)).comp χ) S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s)"
      },
      {
        "stream": "stdout",
        "text": "                              (right :"
      },
      {
        "stream": "stdout",
        "text": "                                (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                    IsCoprimeGenerator K ⊤ χ 𝔟 x₀ → ∀ t ∈ orthant K, ∀ (s : ℂ), ⋯) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K ⊤ ((↑(starRingEnd ℂ)).comp χ) 𝔟 x₀ → ∀ t ∈ orthant K, ⋯) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                    (χ ≠ 1 → ∀ (x₀ : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                      (χ ≠ 1 → ∀ (x₀' : ι → K), (∀ (i : ι), ⋯) → ∀ (s : ℂ), ⋯)) =>"
      },
      {
        "stream": "stdout",
        "text": "                            And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                              fun hinv"
      },
      {
        "stream": "stdout",
        "text": "                                (right : (∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : K), ⋯) ∧ (⋯ → ⋯) ∧ (⋯ → ⋯)) =>"
      },
      {
        "stream": "stdout",
        "text": "                              And.casesOn right fun hinv' => ⋯)"
      },
      {
        "stream": "stdout",
        "text": "        (Eq.symm h𝔣') χ hpar h𝔣"
      },
      {
        "stream": "stdout",
        "text": "    else"
      },
      {
        "stream": "stdout",
        "text": "      Exists.casesOn.{?u.69 + 2} (hole_T2.{audit_u, ?u.69} K 𝔣 χ S hpar h𝔣 h𝔣') fun (ι : ⋯) (h : ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "        Exists.casesOn.{?u.69 + 1} h fun (w : ⋯) (h : ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "          Exists.casesOn.{max (audit_u + 1) (?u.69 + 1)} h fun 𝔞 (h : ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "            Exists.casesOn.{?u.69 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "              fun α"
      },
      {
        "stream": "stdout",
        "text": "                (h :"
      },
      {
        "stream": "stdout",
        "text": "                  Exists.{?u.69 + 1} fun α' =>"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                            1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                              completedRayL K 𝔣 χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ⋯),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ⋯), IsCoprimeGenerator K 𝔣 χ (𝔞 ⋯) ⋯) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "              Exists.casesOn.{?u.69 + 1} h"
      },
      {
        "stream": "stdout",
        "text": "                fun α'"
      },
      {
        "stream": "stdout",
        "text": "                  (h :"
      },
      {
        "stream": "stdout",
        "text": "                    (∀ (i : ι), Differentiable ℂ (α i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                            1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                              completedRayL K 𝔣 χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S"
      },
      {
        "stream": "stdout",
        "text": "                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) =>"
      },
      {
        "stream": "stdout",
        "text": "                And.casesOn h"
      },
      {
        "stream": "stdout",
        "text": "                  fun hα"
      },
      {
        "stream": "stdout",
        "text": "                    (right :"
      },
      {
        "stream": "stdout",
        "text": "                      (∀ (i : ι), Differentiable ℂ (α' i)) ∧"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                            1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                              completedRayL K 𝔣 χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S"
      },
      {
        "stream": "stdout",
        "text": "                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) =>"
      },
      {
        "stream": "stdout",
        "text": "                  And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                    fun hα'"
      },
      {
        "stream": "stdout",
        "text": "                      (right :"
      },
      {
        "stream": "stdout",
        "text": "                        (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                            1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                              completedRayL K 𝔣 χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S"
      },
      {
        "stream": "stdout",
        "text": "                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) =>"
      },
      {
        "stream": "stdout",
        "text": "                    And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                      fun"
      },
      {
        "stream": "stdout",
        "text": "                        (hT :"
      },
      {
        "stream": "stdout",
        "text": "                          ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                            1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                              completedRayL K 𝔣 χ S s ="
      },
      {
        "stream": "stdout",
        "text": "                                Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                  α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)"
      },
      {
        "stream": "stdout",
        "text": "                        (right :"
      },
      {
        "stream": "stdout",
        "text": "                          (∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s) ∧"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 χ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 χ S (𝔞 i) h𝔣 (x₀ i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 →"
      },
      {
        "stream": "stdout",
        "text": "                                      ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                                        (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                            α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                              ((∑ a, chiFin K 𝔣 ⋯ S (Quotient.out a)) *"
      },
      {
        "stream": "stdout",
        "text": "                                                rayInvPolarCoeff K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S"
      },
      {
        "stream": "stdout",
        "text": "                                                  (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) h𝔣 (x₀' i))) ="
      },
      {
        "stream": "stdout",
        "text": "                                          0) =>"
      },
      {
        "stream": "stdout",
        "text": "                      And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                        fun"
      },
      {
        "stream": "stdout",
        "text": "                          (hT' :"
      },
      {
        "stream": "stdout",
        "text": "                            ∀ (s : ℂ),"
      },
      {
        "stream": "stdout",
        "text": "                              1 < s.re →"
      },
      {
        "stream": "stdout",
        "text": "                                completedRayL K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S s ="
      },
      {
        "stream": "stdout",
        "text": "                                  Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i =>"
      },
      {
        "stream": "stdout",
        "text": "                                    α' i s *"
      },
      {
        "stream": "stdout",
        "text": "                                      rayFoldMellin K 𝔣 ((↑(starRingEnd ℂ)).comp χ) S (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (rayScale K 𝔣 (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))) s)"
      },
      {
        "stream": "stdout",
        "text": "                          (right :"
      },
      {
        "stream": "stdout",
        "text": "                            (∀ (i : ι) (s : ℂ), α' i s = α i (1 - s) * (1 / ↑(rayScale K 𝔣 (𝔞 i))) ^ S.card) ∧"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι),"
      },
      {
        "stream": "stdout",
        "text": "                                      IsCoprimeGenerator K 𝔣 ((↑(starRingEnd ℂ)).comp χ) (rayDualIdeal K 𝔣 h𝔣 (𝔞 i))"
      },
      {
        "stream": "stdout",
        "text": "                                        (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ 1 → ∀ (s : ℂ), (Finset.sum.{?u.69, 0} Finset.univ.{?u.69} fun i => ⋯) = 0) =>"
      },
      {
        "stream": "stdout",
        "text": "                        And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                          fun hαα'"
      },
      {
        "stream": "stdout",
        "text": "                            (right :"
      },
      {
        "stream": "stdout",
        "text": "                              (∀ (x₀ : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → χ ≠ ⋯ → ∀ (s : ℂ), ⋯) ∧"
      },
      {
        "stream": "stdout",
        "text": "                                ∀ (x₀' : ι → K),"
      },
      {
        "stream": "stdout",
        "text": "                                  (∀ (i : ι), IsCoprimeGenerator K 𝔣 ⋯ (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i)) →"
      },
      {
        "stream": "stdout",
        "text": "                                    χ ≠ ⋯ → ∀ (s : ℂ), ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "                          And.casesOn right"
      },
      {
        "stream": "stdout",
        "text": "                            fun (hcancel : ∀ (x₀ : ι → K), (∀ (i : ι), IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i)) → ⋯)"
      },
      {
        "stream": "stdout",
        "text": "                              (hcancel' : ⋯) =>"
      },
      {
        "stream": "stdout",
        "text": "                            ⋯"
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
        "text": "✔ [33/43] Built P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO (9.1s)"
      },
      {
        "stream": "stdout",
        "text": "✔ [34/43] Built Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO (3.6s)"
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
        "stream": "stderr",
        "text": "error: build failed"
      }
    ],
    "errors": 3,
    "warnings": 298
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
    "checked_at": 1792940345.1685157,
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
  "sources_sha256": "2c97237a0287065953d42ebac0735b70ffbe7e1a134517a9797f1ac1d65b56b2"
}
```
