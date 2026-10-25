# Hasse–Arf evidence: bounded current Library scan

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

<!-- evidence-file: current-library-scan.json -->

## current-library-scan.json

SHA256 of the exact UTF-8 block: `c5e6b07b1af3934349d2949d5cc66482135664912d26885ffef66349e2e7a6eb`.

````json
{
  "commit": "3e255196ad168b37f73124db5bdb4d6a5168a4da",
  "root": "/home/taskhub/pilot/library/3e255196ad168b37f73124db5bdb4d6a5168a4da/files",
  "files": [
    {
      "path": "Langlands/LocalFactor/Ramification/Galois.lean",
      "sha256": "faefe597db6582a5d580431839ea96a37d04b867b163591cba2c605cb3e16a0a",
      "same_as_workspace": true
    },
    {
      "path": "Langlands/LocalFactor/Ramification/Herbrand/Finite.lean",
      "sha256": "8b72fd85dc88d6573b35c7d3da5cbf9dc00574b9deec6f25a9de539dad2548d2",
      "same_as_workspace": true
    },
    {
      "path": "Langlands/LocalFactor/Ramification/Herbrand/ArithmeticStatement.lean",
      "sha256": "4ead657d6e09885e3292499be9718a9639592c94272a99bb212fa1bf31286f18",
      "same_as_workspace": true
    }
  ],
  "search": {
    "pattern": "HasseArf|hasseArf|Hasse.Arf",
    "scope": [
      "Library Langlands/**/*.lean",
      "pinned Mathlib/**/*.lean"
    ],
    "returncode": 0,
    "stdout": "/home/taskhub/pilot/library/3e255196ad168b37f73124db5bdb4d6a5168a4da/files/Langlands/LocalFactor/Ramification/Herbrand/ArithmeticStatement.lean:72:def HasseArfIntegrality [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) : Prop :=\n/home/taskhub/pilot/library/3e255196ad168b37f73124db5bdb4d6a5168a4da/files/Langlands/LocalFactor/Ramification/Herbrand/ArithmeticStatement.lean:120:    HasseArfIntegrality K L T \u2227\n",
    "stderr": ""
  }
}
````
