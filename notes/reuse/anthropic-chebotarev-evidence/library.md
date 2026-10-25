# Library and Mathlib interfaces

The checked workspace base is Library `b5df466b356db508f072a2481307ed641ffa76a7`. All nine host files below match that immutable publication byte for byte. Searches for the exact root and both target names in the workspace Langlands tree and pinned Mathlib found the statement definitions, conjunction reference and conditional nonsplit consumers; no same-named realization proof was found. A name-based search does not exclude differently named results.

```json
{
  "library_commit": "b5df466b356db508f072a2481307ed641ffa76a7",
  "files": [
    {
      "path": "Langlands/Global/Arithmetic/ChebotarevStatement.lean",
      "workspace_sha256": "34a27ae3d4c433d610ace02ec79a6f1e4b4b4626c6cf7131897d6125b72b203a",
      "library_sha256": "34a27ae3d4c433d610ace02ec79a6f1e4b4b4626c6cf7131897d6125b72b203a",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/ChebotarevStatement.md",
      "workspace_sha256": "33592151d29ffb8dbfb6fe117efe59d19f95ba1b97cc8fd740aaa49f593acd50",
      "library_sha256": "33592151d29ffb8dbfb6fe117efe59d19f95ba1b97cc8fd740aaa49f593acd50",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/CyclicNonsplitPrimeStatement.lean",
      "workspace_sha256": "9f0efc5fc39b2f83b09ba8c4d0c1f642042a00a885d80078234ac908ea4f0d3f",
      "library_sha256": "9f0efc5fc39b2f83b09ba8c4d0c1f642042a00a885d80078234ac908ea4f0d3f",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/CyclicNonsplitPrimeStatement.md",
      "workspace_sha256": "656ecbfc63f46d91101a859f5b4bc4226e6a60c299376d9b71038ae8d64b0653",
      "library_sha256": "656ecbfc63f46d91101a859f5b4bc4226e6a60c299376d9b71038ae8d64b0653",
      "equal": true
    },
    {
      "path": "Langlands/Global/AdelicFunctoriality/LocalDegree.lean",
      "workspace_sha256": "aded272a00ea1aa3f239571969a1687b8c1ef69b619f21635d6a26b625f2fc89",
      "library_sha256": "aded272a00ea1aa3f239571969a1687b8c1ef69b619f21635d6a26b625f2fc89",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/CyclotomicSymbol.lean",
      "workspace_sha256": "64cc63df86fd96a31184f3498f6fed869bd02415cc060f8eda6c4f40d493652e",
      "library_sha256": "64cc63df86fd96a31184f3498f6fed869bd02415cc060f8eda6c4f40d493652e",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/FrobeniusNormClass.lean",
      "workspace_sha256": "5b3c9f00948c12507567867e74333a0e6de390ed95502faafb5e878c36b0f00f",
      "library_sha256": "5b3c9f00948c12507567867e74333a0e6de390ed95502faafb5e878c36b0f00f",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/CyclotomicSplitting.lean",
      "workspace_sha256": "3561e9c23f09cc37ccdfa180de7e042134a007554844e5d391e33c2423d6151a",
      "library_sha256": "3561e9c23f09cc37ccdfa180de7e042134a007554844e5d391e33c2423d6151a",
      "equal": true
    },
    {
      "path": "Langlands/Global/Arithmetic/CyclotomicAuxiliary.lean",
      "workspace_sha256": "7ad1c6fa0b106403568497773fc714ae2e53acce55acf81abeec240d6dd8c064",
      "library_sha256": "7ad1c6fa0b106403568497773fc714ae2e53acce55acf81abeec240d6dd8c064",
      "equal": true
    }
  ]
}
```

A restoration comparison at Library `6066ffe8da8e977f40af9c75eda35cdbe1989d74` confirmed that all nine hashes above remain unchanged. Check 17 used this refreshed workspace.

The pinned Mathlib is `5ed2965256430c3649e86755f9576b54eca72435`. Reused interfaces are `Ideal.liesOver_span_iff`, `Ideal.over_def`, `Ideal.absNorm_span_natCast`, `Int.card_ideal_quot`, `Ideal.algebraMap_quotient_injective`, `NumberField.not_dvd_discr_iff_forall_mem`, `Algebra.IsUnramifiedAt.of_restrictScalars`, `Ideal.bot_lt_of_maximal`, `RingOfIntegers.not_isField`, `Ideal.IsIntegral.under_ne_bot`, `Ideal.under_liesOver_of_liesOver`, `IsGaloisGroup.of_isFractionRing`, `Ideal.card_stabilizer_eq`, and `IsArithFrobAt.mem_stabilizer`. Their use is checked in the private bridge code.

The Library `Langlands.Global.AdelicFunctoriality.localDegree_eq` identifies the canonical completion finrank with ramification index times inertia degree. `CyclotomicSymbol`, `FrobeniusNormClass`, `CyclotomicSplitting` and `CyclotomicAuxiliary` were read in full; they supply existing cyclotomic/norm-character and local-degree infrastructure, but none supplies arbitrary-Galois prime realization. `CyclotomicAuxiliary.intermediateField_numberField` has a common universe for base and extension; our tested source generalization did not require that lemma.
