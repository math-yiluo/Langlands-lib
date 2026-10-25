# Hasse–Arf evidence: source inventory

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

The JSON gives the complete dependency-first import closure and boundary. The second block gives hashes after the two-file patch; all module names stay unchanged.

<!-- evidence-file: closure.json -->

## closure.json

SHA256 of the exact UTF-8 block: `5a3c111ebd2f00eb4894bd98e5ae43dd2eb85ada64fb87308ea05c706cec2cff`.

````json
{
  "root": "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative",
  "source": "/home/taskhub/pilot/literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2",
  "files": [
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean",
      "sha256": "f8db223941b714c707b057398f4fa5b99cc38f2b47fab4103a1a91f02e2e7689",
      "lines": 213,
      "imports": [
        "Mathlib"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean",
      "sha256": "d0f2deb5720a630198c7889503957bbe89900eb2d047088dd49953f64a253da0",
      "lines": 374,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
      "path": "Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean",
      "sha256": "96cafbd97505550f1037d243c833709d3f54836bcd6317ce4732b7d371338a8d",
      "lines": 202,
      "imports": [
        "Mathlib"
      ]
    },
    {
      "module": "Definitions.Def_RamificationChain_Wild",
      "path": "Definitions/Def_RamificationChain_Wild.lean",
      "sha256": "0a61fe8ff72f34dfd72a8f338b8565cd97083b5d0dd680da5244f203193ff678",
      "lines": 20,
      "imports": [
        "Mathlib.Algebra.Group.Subgroup.Finite",
        "Mathlib.Algebra.BigOperators.Intervals"
      ]
    },
    {
      "module": "P2M.Util",
      "path": "P2M/Util.lean",
      "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
      "lines": 127,
      "imports": [
        "Lean"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean",
      "sha256": "ac2a05e1808f08e38eea156dec4f7f4f6f6d1861b7c10a44dde4be8c5dbadc1e",
      "lines": 419,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean",
      "sha256": "fa80a6898dc9335dc7df8537916b4c305f89dc76c37ede4d5be1b4da79963dd9",
      "lines": 174,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup"
      ]
    },
    {
      "module": "P2M.Sol.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq",
      "path": "P2M/Sol/S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean",
      "sha256": "c2e7b5e747b182df30ee2c2001f25f7e90c650c6ffa9c6f1b791ddd3d1e18ea1",
      "lines": 320,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq",
      "path": "Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean",
      "sha256": "0d8b99478d961e8d5631cb78d2eabce54ff3dc9cf36cca6e7659268086536045",
      "lines": 19,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq"
      ]
    },
    {
      "module": "P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq",
      "path": "P2M/Sol/S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean",
      "sha256": "293c413e0536a6efbf2909bb7d76b6af267ec284c3fc8478c7d46e9d2b2ea0b3",
      "lines": 152,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi",
        "Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq",
      "path": "Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean",
      "sha256": "9874f72be193bdaa3ba15b397b574e7bcda72beb240cc31c6e95ed1c4c3b8d6b",
      "lines": 17,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth.lean",
      "sha256": "f130a371334ba03ad45fbba66a99fadddc50bf9943eccbc8f52d9dc714c1b3a0",
      "lines": 266,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup",
      "path": "Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean",
      "sha256": "245169faf7fac39485e67df511eadca7f35bd9b478fa542e5eef3f6cb51d9777",
      "lines": 20,
      "imports": [
        "Mathlib"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator.lean",
      "sha256": "e145c02f0b0c40aa47e22352ac8e904ecc39e7b0d61518427a4e5ca67f17d04d",
      "lines": 272,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean",
      "sha256": "fa5c7bb764aa86ef1db2568317ee8caea583d7c3ad316142748041436b853543",
      "lines": 304,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top",
      "path": "Theorems/Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean",
      "sha256": "35a5f6af1fdef81f02c586cea94f6062981c3d7f3ef8fcb5b150dda4f6e9ff5a",
      "lines": 21,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean",
      "sha256": "dbb55a5454038a9234d43bfc054a13fdc8bc2b930146599359e1635e4573e493",
      "lines": 560,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth",
      "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean",
      "sha256": "392584439fa690ecab2b309ae7f415217af6c9ace455f19eabd5b556cc1716a1",
      "lines": 25,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean",
      "sha256": "a9f320de95bb349f6e2b3814b50f59c2c006a223a9836e68ca9e543a9ecbd5da",
      "lines": 32,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Theorems.Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top",
        "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top",
      "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean",
      "sha256": "a5ae099ca26c93ce504743f153631208e39cacf32c0fafbcd7a605093c290680",
      "lines": 26,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top"
      ]
    },
    {
      "module": "Definitions.Def_DifferentFiltrationFormula",
      "path": "Definitions/Def_DifferentFiltrationFormula.lean",
      "sha256": "f4140b0dab073df7fae997a7b880481bae25bd05f7fc33ed84ad48dc92355ede",
      "lines": 91,
      "imports": [
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
        "Mathlib.RingTheory.DedekindDomain.Different"
      ]
    },
    {
      "module": "Definitions.Def_Compat_Mathlib430",
      "path": "Definitions/Def_Compat_Mathlib430.lean",
      "sha256": "0d80c765130229fcd9bbeb5b234bfc4af5afaff2354b56ae0acc90e04b8b8e54",
      "lines": 340,
      "imports": [
        "Mathlib.RepresentationTheory.Rep.Basic",
        "Mathlib.Algebra.Group.End",
        "Mathlib.Algebra.GroupWithZero.Action.Basic",
        "Mathlib.Algebra.Ring.AddAut",
        "Mathlib.Algebra.Ring.Action.Submonoid",
        "Mathlib.NumberTheory.RamificationInertia.Galois",
        "Mathlib.RingTheory.Invariant.Galois",
        "Mathlib.FieldTheory.Galois.Basic",
        "Mathlib.Tactic.LinearCombination",
        "Mathlib.Tactic.Ring"
      ]
    },
    {
      "module": "P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn",
      "path": "P2M/Sol/S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean",
      "sha256": "5f0888fa3a0329beb5585321af14403a756b681d89b0e6b9a7b54c99cb09d4d2",
      "lines": 21,
      "imports": [
        "Definitions.Def_DifferentFiltrationFormula",
        "Mathlib.NumberTheory.RamificationInertia.Galois",
        "Definitions.Def_Compat_Mathlib430",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn",
      "path": "Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean",
      "sha256": "920e933d99ed4a3f77fc0ffe23fc4d779017e5a2f0fc3fc21a7605b4fb95e12a",
      "lines": 16,
      "imports": [
        "Definitions.Def_DifferentFiltrationFormula",
        "Mathlib.NumberTheory.RamificationInertia.Galois",
        "P2M.Util",
        "P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean",
      "sha256": "e55a7e5135f6892f57df8ff28650f9a77192d3360861b721bc887403fd9d27ff",
      "lines": 110,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup",
        "Theorems.Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints",
      "path": "Theorems/Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean",
      "sha256": "03c54dc7ab834efe2bea7919c0e1346eabdc1e05acf8d49f6ac8ba038f35945a",
      "lines": 20,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean",
      "sha256": "b3ac6f2fbb39aebd2b34f4eec84cc1bd7fdcbaa727f3f97d0e5ff4fce957dbd8",
      "lines": 222,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField",
      "path": "Theorems/Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean",
      "sha256": "16b06522efd69613241281d30d1f47cc84ba84aa2b9cf3d7a1ad43a356b0aabc",
      "lines": 15,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField"
      ]
    },
    {
      "module": "P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring",
      "path": "P2M/Sol/S_FixedPoints_isDiscreteValuationRing_subring.lean",
      "sha256": "5e7267644ede2f6357847ea7217b7e8646a9275267e3a9a19217beff9c167c00",
      "lines": 148,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring",
      "path": "Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean",
      "sha256": "db799038bdd3b8d22026ddbc00e5cb365b521828a58b322c675a3773e4d8abaf",
      "lines": 11,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean",
      "sha256": "79b3a46861d4da2d5fff5788c76b179cc64f5bab58efc3ce01f813a107bccd93",
      "lines": 119,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup",
        "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top",
        "Theorems.Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints",
        "Theorems.Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField",
        "Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField",
      "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean",
      "sha256": "7bfc77536ab368e026b317fd2bdc85aace6c7b14e78173e820621c0448125a34",
      "lines": 19,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean",
      "sha256": "b0ba21b611119d1b594897931772e9b67e815a2402394866a80cb4692d26effe",
      "lines": 151,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq",
        "Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient",
      "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean",
      "sha256": "dfc9e1e61ff072ddd85550fa687ebb2f733c9565856f93eb692ac0298954fe08",
      "lines": 23,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient"
      ]
    },
    {
      "module": "P2M.Sol.S_IsLocalRing_pow_mem_lowerRamificationGroup_succ",
      "path": "P2M/Sol/S_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean",
      "sha256": "22f8167a337b90e4fbafdf96408bdc660ab65936aa3304af072e6be9d0603079",
      "lines": 88,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ",
      "path": "Theorems/Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean",
      "sha256": "a9dd9b5d64d65620f82fcc3897d344a9d313852469ddaad95a0db23eda4bb346",
      "lines": 11,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_pow_mem_lowerRamificationGroup_succ"
      ]
    },
    {
      "module": "P2M.Sol.S_IsLocalRing_isPGroup_lowerRamificationGroup_one",
      "path": "P2M/Sol/S_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean",
      "sha256": "2b26bd99590e32f3cd41a4fec371bc5af7955f97aaa6db2f3301e5554eaa26b8",
      "lines": 28,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Theorems.Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one",
      "path": "Theorems/Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean",
      "sha256": "219f5a52bc303f91f395e1abfce324f37081848e3650b39c906456e9177570ce",
      "lines": 11,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup",
        "P2M.Util",
        "P2M.Sol.S_IsLocalRing_isPGroup_lowerRamificationGroup_one"
      ]
    },
    {
      "module": "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass",
      "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass.lean",
      "sha256": "24631aa71dbaeeb7d6ad149bf96fa108e3373618810433d5981c0a88c8f3c29a",
      "lines": 314,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean",
      "sha256": "8a3ba1fe108d7ba80acf95a63162749f86bc0228a026c8327351b0eaf581b6b6",
      "lines": 290,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units",
      "path": "Theorems/Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean",
      "sha256": "56d5275177b8d8581079e337d150d0239b5360f83a161df0e818de85b3fc2ff7",
      "lines": 23,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean",
      "sha256": "58fceddfe15f9216e0d88c3845d14a19bc08eab966f85f25c34e723017e323d3",
      "lines": 337,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute",
      "path": "Theorems/Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean",
      "sha256": "245e2e7e582aaddcec47cbcc58b22a27e0a608625ec0c1221ffefd86dc39ecff",
      "lines": 19,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean",
      "sha256": "18ae866a724a32746a92bfee2315794d9ef17688b6ea1024c44e58656549dd37",
      "lines": 878,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one",
      "path": "Theorems/Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean",
      "sha256": "e89f1dca18010e48baf6980277ffc9a2c372cd97fd8cc03c15ba7869e8e4706d",
      "lines": 18,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean",
      "sha256": "730b199d0c6350cfdbdf2464d5039f0c976486f052f1c77d0bc10ba0e07bffa4",
      "lines": 474,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq",
      "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean",
      "sha256": "d0cd9654430fb84e46221b2f5a6b8321ab628c6059e871c66b4357c9e6efc5ac",
      "lines": 24,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean",
      "sha256": "7727de32744112ee1ae031b4aea44a48d6e749f52d943703221246a155ee3965",
      "lines": 344,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth",
        "Theorems.Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one",
        "Theorems.Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units",
        "Theorems.Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute",
        "Theorems.Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one",
        "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic",
      "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean",
      "sha256": "af69d93af0acf82ee834f7374374fc082698299ed3d660e261f07da45208c4df",
      "lines": 19,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic"
      ]
    },
    {
      "module": "P2M.Sol.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring",
      "path": "P2M/Sol/S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean",
      "sha256": "3c45eb739409b94989d6450cb044a52baa0611b8a3321b6c1759394ebbb926ac",
      "lines": 340,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring",
      "path": "Theorems/Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean",
      "sha256": "dd3df56afc95f3f07e4465134fb08f71a05168b95335a92ccbea241b7b7578e1",
      "lines": 26,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring"
      ]
    },
    {
      "module": "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative",
      "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean",
      "sha256": "e9875d4e8cf98ae5fdd97d5235ea61acb96fb08e007dc36816aeb30a3717efa6",
      "lines": 37,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient",
        "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic",
        "Theorems.Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring",
        "Theorems.Thm_FixedPoints_isDiscreteValuationRing_subring",
        "P2M.Util"
      ]
    },
    {
      "module": "Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative",
      "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean",
      "sha256": "da36162e438f9865b42c03b3f9b46e9bdd28d0f918b802ab2b2b50c2e7e5a4db",
      "lines": 20,
      "imports": [
        "Mathlib",
        "Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup",
        "Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal",
        "Definitions.Def_RamificationChain_Wild",
        "P2M.Util",
        "P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative"
      ]
    }
  ],
  "external_imports": [
    "Lean",
    "Mathlib",
    "Mathlib.Algebra.BigOperators.Intervals",
    "Mathlib.Algebra.Group.End",
    "Mathlib.Algebra.Group.Subgroup.Finite",
    "Mathlib.Algebra.GroupWithZero.Action.Basic",
    "Mathlib.Algebra.Ring.Action.Submonoid",
    "Mathlib.Algebra.Ring.AddAut",
    "Mathlib.FieldTheory.Galois.Basic",
    "Mathlib.NumberTheory.RamificationInertia.Galois",
    "Mathlib.RepresentationTheory.Rep.Basic",
    "Mathlib.RingTheory.DedekindDomain.Different",
    "Mathlib.RingTheory.Invariant.Galois",
    "Mathlib.Tactic.LinearCombination",
    "Mathlib.Tactic.Ring"
  ],
  "module_count": 53,
  "line_count": 8170
}
````

<!-- evidence-file: adapted-hashes.json -->

## adapted-hashes.json

SHA256 of the exact UTF-8 block: `2dfed61a68b334d3b0599d108e23240d9144ff37776a09d1c0e3bb65224356b4`.

````json
[
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean",
    "sha256": "5378b94ebaa011cb385bbac14c7b003748798e43a54b89e097ff57ee80f1c0e0"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean",
    "sha256": "d0f2deb5720a630198c7889503957bbe89900eb2d047088dd49953f64a253da0"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean",
    "sha256": "96cafbd97505550f1037d243c833709d3f54836bcd6317ce4732b7d371338a8d"
  },
  {
    "path": "Definitions/Def_RamificationChain_Wild.lean",
    "sha256": "0a61fe8ff72f34dfd72a8f338b8565cd97083b5d0dd680da5244f203193ff678"
  },
  {
    "path": "P2M/Util.lean",
    "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean",
    "sha256": "ac2a05e1808f08e38eea156dec4f7f4f6f6d1861b7c10a44dde4be8c5dbadc1e"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupSubgroup.lean",
    "sha256": "fa80a6898dc9335dc7df8537916b4c305f89dc76c37ede4d5be1b4da79963dd9"
  },
  {
    "path": "P2M/Sol/S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean",
    "sha256": "c2e7b5e747b182df30ee2c2001f25f7e90c650c6ffa9c6f1b791ddd3d1e18ea1"
  },
  {
    "path": "Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean",
    "sha256": "0d8b99478d961e8d5631cb78d2eabce54ff3dc9cf36cca6e7659268086536045"
  },
  {
    "path": "P2M/Sol/S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean",
    "sha256": "293c413e0536a6efbf2909bb7d76b6af267ec284c3fc8478c7d46e9d2b2ea0b3"
  },
  {
    "path": "Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean",
    "sha256": "9874f72be193bdaa3ba15b397b574e7bcda72beb240cc31c6e95ed1c4c3b8d6b"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth.lean",
    "sha256": "f130a371334ba03ad45fbba66a99fadddc50bf9943eccbc8f52d9dc714c1b3a0"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringGaloisGroup.lean",
    "sha256": "245169faf7fac39485e67df511eadca7f35bd9b478fa542e5eef3f6cb51d9777"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator.lean",
    "sha256": "e145c02f0b0c40aa47e22352ac8e904ecc39e7b0d61518427a4e5ca67f17d04d"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean",
    "sha256": "fa5c7bb764aa86ef1db2568317ee8caea583d7c3ad316142748041436b853543"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top.lean",
    "sha256": "35a5f6af1fdef81f02c586cea94f6062981c3d7f3ef8fcb5b150dda4f6e9ff5a"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean",
    "sha256": "dbb55a5454038a9234d43bfc054a13fdc8bc2b930146599359e1635e4573e493"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean",
    "sha256": "392584439fa690ecab2b309ae7f415217af6c9ace455f19eabd5b556cc1716a1"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean",
    "sha256": "a9f320de95bb349f6e2b3814b50f59c2c006a223a9836e68ca9e543a9ecbd5da"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean",
    "sha256": "a5ae099ca26c93ce504743f153631208e39cacf32c0fafbcd7a605093c290680"
  },
  {
    "path": "Definitions/Def_DifferentFiltrationFormula.lean",
    "sha256": "f4140b0dab073df7fae997a7b880481bae25bd05f7fc33ed84ad48dc92355ede"
  },
  {
    "path": "Definitions/Def_Compat_Mathlib430.lean",
    "sha256": "56060711d10192f005720fa612264a9115c3e1388ebaa74e2936c3efe5db4280"
  },
  {
    "path": "P2M/Sol/S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean",
    "sha256": "5f0888fa3a0329beb5585321af14403a756b681d89b0e6b9a7b54c99cb09d4d2"
  },
  {
    "path": "Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean",
    "sha256": "920e933d99ed4a3f77fc0ffe23fc4d779017e5a2f0fc3fc21a7605b4fb95e12a"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean",
    "sha256": "e55a7e5135f6892f57df8ff28650f9a77192d3360861b721bc887403fd9d27ff"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_addVal_coe_eq_lowerRamificationCard_zero_mul_addVal_fixedPoints.lean",
    "sha256": "03c54dc7ab834efe2bea7919c0e1346eabdc1e05acf8d49f6ac8ba038f35945a"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean",
    "sha256": "b3ac6f2fbb39aebd2b34f4eec84cc1bd7fdcbaa727f3f97d0e5ff4fce957dbd8"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean",
    "sha256": "16b06522efd69613241281d30d1f47cc84ba84aa2b9cf3d7a1ad43a356b0aabc"
  },
  {
    "path": "P2M/Sol/S_FixedPoints_isDiscreteValuationRing_subring.lean",
    "sha256": "5e7267644ede2f6357847ea7217b7e8646a9275267e3a9a19217beff9c167c00"
  },
  {
    "path": "Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean",
    "sha256": "db799038bdd3b8d22026ddbc00e5cb365b521828a58b322c675a3773e4d8abaf"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean",
    "sha256": "79b3a46861d4da2d5fff5788c76b179cc64f5bab58efc3ce01f813a107bccd93"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean",
    "sha256": "7bfc77536ab368e026b317fd2bdc85aace6c7b14e78173e820621c0448125a34"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean",
    "sha256": "b0ba21b611119d1b594897931772e9b67e815a2402394866a80cb4692d26effe"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_forall_isCyclic_quotient.lean",
    "sha256": "dfc9e1e61ff072ddd85550fa687ebb2f733c9565856f93eb692ac0298954fe08"
  },
  {
    "path": "P2M/Sol/S_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean",
    "sha256": "22f8167a337b90e4fbafdf96408bdc660ab65936aa3304af072e6be9d0603079"
  },
  {
    "path": "Theorems/Thm_IsLocalRing_pow_mem_lowerRamificationGroup_succ.lean",
    "sha256": "a9dd9b5d64d65620f82fcc3897d344a9d313852469ddaad95a0db23eda4bb346"
  },
  {
    "path": "P2M/Sol/S_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean",
    "sha256": "2b26bd99590e32f3cd41a4fec371bc5af7955f97aaa6db2f3301e5554eaa26b8"
  },
  {
    "path": "Theorems/Thm_IsLocalRing_isPGroup_lowerRamificationGroup_one.lean",
    "sha256": "219f5a52bc303f91f395e1abfce324f37081848e3650b39c906456e9177570ce"
  },
  {
    "path": "Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass.lean",
    "sha256": "24631aa71dbaeeb7d6ad149bf96fa108e3373618810433d5981c0a88c8f3c29a"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean",
    "sha256": "8a3ba1fe108d7ba80acf95a63162749f86bc0228a026c8327351b0eaf581b6b6"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_exists_monoidHom_lowerRamificationGroup_zero_residueField_units.lean",
    "sha256": "56d5275177b8d8581079e337d150d0239b5360f83a161df0e818de85b3fc2ff7"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean",
    "sha256": "58fceddfe15f9216e0d88c3845d14a19bc08eab966f85f25c34e723017e323d3"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean",
    "sha256": "245e2e7e582aaddcec47cbcc58b22a27e0a608625ec0c1221ffefd86dc39ecff"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean",
    "sha256": "18ae866a724a32746a92bfee2315794d9ef17688b6ea1024c44e58656549dd37"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_ramificationDepth_pow_prime_pow_modEq_of_mem_lowerRamificationGroup_one.lean",
    "sha256": "e89f1dca18010e48baf6980277ffc9a2c372cd97fd8cc03c15ba7869e8e4706d"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean",
    "sha256": "730b199d0c6350cfdbdf2464d5039f0c976486f052f1c77d0bc10ba0e07bffa4"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_of_isCyclic_of_dvd_of_modEq.lean",
    "sha256": "d0cd9654430fb84e46221b2f5a6b8321ab628c6059e871c66b4357c9e6efc5ac"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean",
    "sha256": "7727de32744112ee1ae031b4aea44a48d6e749f52d943703221246a155ee3965"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean",
    "sha256": "af69d93af0acf82ee834f7374374fc082698299ed3d660e261f07da45208c4df"
  },
  {
    "path": "P2M/Sol/S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean",
    "sha256": "3c45eb739409b94989d6450cb044a52baa0611b8a3321b6c1759394ebbb926ac"
  },
  {
    "path": "Theorems/Thm_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.lean",
    "sha256": "dd3df56afc95f3f07e4465134fb08f71a05168b95335a92ccbea241b7b7578e1"
  },
  {
    "path": "P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean",
    "sha256": "e9875d4e8cf98ae5fdd97d5235ea61acb96fb08e007dc36816aeb30a3717efa6"
  },
  {
    "path": "Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.lean",
    "sha256": "da36162e438f9865b42c03b3f9b46e9bdd28d0f918b802ab2b2b50c2e7e5a4db"
  }
]
````

<!-- evidence-file: inventory.py -->

## inventory.py

SHA256 of the exact UTF-8 block: `6f9d841f70f4e29b8dbf8056d325d489dcd733a1fc74f5f4401f7bf3b4bd4493`.

````python
import re, json, hashlib
from pathlib import Path
src=Path('/home/taskhub/pilot/literature/Anthropic - Fermat\'s Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2')
root='Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative'
seen={}; order=[]; external=set()
def visit(m):
 if m in seen: return
 p=src/ (m.replace('.','/')+'.lean')
 if not p.exists():
  external.add(m); return
 b=p.read_bytes(); t=b.decode(); imports=[]
 for line in t.splitlines():
  match=re.match(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
  if match: imports.extend(match[1].split('--')[0].split())
 seen[m]={'module':m,'path':str(p.relative_to(src)),'sha256':hashlib.sha256(b).hexdigest(),'lines':len(t.splitlines()),'imports':imports}
 for dep in imports: visit(dep)
 order.append(m)
visit(root)
r={'root':root,'source':str(src),'files':[seen[m] for m in order],'external_imports':sorted(external),'module_count':len(order),'line_count':sum(x['lines'] for x in seen.values())}
Path('.private/hasse-arf/closure.json').write_text(json.dumps(r,indent=2)+'\n')
print(r['module_count'],r['line_count'], 'boundary',r['external_imports'])
for n,m in enumerate(order,1): print(f'{n:02} {seen[m]["lines"]:4} {seen[m]["path"]}')
````
