# Galois cohomology in the Library: overview

The Library has the cohomology of profinite groups with smooth coefficients and, on it, the Galois
cohomology of fields, of nonarchimedean local fields and of number fields up to Poitou–Tate
duality, Tate's global Euler characteristic formula and the formula of Greenberg and Wiles for
Selmer groups. This note says where each layer is and what it holds; the layers are described in
four notes:

1. [Cohomology of profinite groups and Galois cohomology of fields](profinite-and-fields.md):
   `Langlands/Cohomology/Profinite/` and `Langlands/GaloisCohomology/Field/`.
2. [Galois cohomology of local fields](local.md): `Langlands/GaloisCohomology/Local/`.
3. [Global Galois cohomology: G_S, compact support, the Brauer sequence, dimension and finiteness](global.md):
   `Langlands/Galois/RestrictedRamification/`, `Langlands/GaloisCohomology/CompactSupport/` and the
   arithmetic of G_S in `Langlands/GaloisCohomology/Global/`.
4. [Poitou–Tate duality, the global Euler characteristic and Selmer groups](poitou-tate.md):
   `Langlands/GaloisCohomology/Global/PoitouTate/`, `Global/EulerCharacteristic/`, `Global/Selmer/`.

## The layers and their order

| Layer | Namespace | Main results |
| --- | --- | --- |
| `Cohomology/Profinite` | `Langlands.ProfiniteCohomology` | cochain model and its comparisons, Shapiro, corestriction, inflation–restriction, cup products, `cd`, Euler–Poincaré characteristic, class formations, duality from a dualizing datum (`DualizingData.dualityMap_bijective`) |
| `GaloisCohomology/Field` | `Langlands.GaloisCohomology` | Hilbert 90 (`subsingleton_cohomology_one_unitsModule`), Kummer theory (`kummerEquiv`), `Br(K) ≅ H²` (`Langlands.GaloisCohomology.brauerEquiv`) |
| `GaloisCohomology/Local` | `Langlands.GaloisCohomology.Local` | the invariant and cup symbol (`invariant_characterClass_cup`), `cd_ℓ ≤ 2` (`Langlands.GaloisCohomology.Local.cd_le_two`), local Tate duality (`tatePairing_bijective`), the local Euler characteristic (`Langlands.GaloisCohomology.Local.eulerCharacteristic_eq`), unramified classes |
| `Galois/RestrictedRamification` | `Langlands.Galois` | K_S and G_S (`GaloisGroupUnramifiedOutside`), localization homomorphisms |
| `GaloisCohomology/CompactSupport` | `Langlands.GaloisCohomology` | cohomology with compact support relative to a family of homomorphisms, abstract duality and nine-term sequence |
| `GaloisCohomology/Global` | `Langlands.GaloisCohomology`, `Langlands.GaloisCohomology.PoitouTate` | `Ш`, the `S`-units, the Brauer sequence (`brauerSequenceStatement`), `cd_ℓ(G_S) ≤ 2` (`cohomologicalDimensionStatement`), finiteness, the real places, characters of G_S, Poitou–Tate (`poitouTateDualityStatement`, `poitouTateNineTermStatement`, `poitouTateShaStatement`), the Euler characteristic (`globalEulerCharacteristic`), Greenberg–Wiles (`greenbergWilesStatement`) |

Each layer imports only those above it in the table, except that `Galois/RestrictedRamification`
and `GaloisCohomology/CompactSupport` are independent of each other and of `Local`. Every
`…Statement` of the six directories is proved, by a theorem of its type without hypotheses,
except the internal `GlobalEulerCharacteristicBaseStatement`, which is derived inside the proof
of the global Euler characteristic formula.

## Conventions common to the layers

- Coefficient modules are objects of Mathlib's `Rep k G` with the class `Langlands.IsSmoothRep`;
  abelian groups are modules over `ULift ℤ` (`Langlands.ClassFieldTheory.Local.IntegerScalars`), and
  ring, group and module are in one universe. The local and global theorems are stated for fields in
  an arbitrary universe `u`, the field and its separable closure in the same universe.
- Cohomology is `Langlands.ProfiniteCohomology.cohomology`, computed by locally constant
  inhomogeneous cochains, with comparison isomorphisms to Mathlib's `groupCohomology` and
  `continuousCohomology` and to the Library's colimit over finite quotients.
- ℚ/ℤ is `Langlands.ClassFieldTheory.Local.RationalModIntegers`.
- The local invariant is the Library's `localBrauerInvariant`, normalized by the arithmetic
  Frobenius; the cup symbol is stated with arithmetic Artin lifts
  (`IsArithmeticArtinLift`). The global Artin map used for the characters of G_S is
  `Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap`, in the geometric normalization.
- Locally the dual of `M` is the Cartier dual `Hom(M, Ksepˣ)`; for G_S it is `Hom(M, μ_N)`
  (`PoitouTate.dual`), and the trace of Poitou–Tate duality is the sum of the local invariants
  (`PoitouTate.trace_localToCompact`).
- `S` is a set of finite places; real places are added in every local term; K_S may be ramified
  at the infinite places.

## Why the Galois cohomology is built this way

- **One model of cohomology, compared with the others.** The locally constant cochains give
  explicit cocycles, needed by the cup symbol, the invariants and the mapping cones of compact
  support. Mathlib's `continuousCohomology` and `groupCohomology` and the Library's colimit over
  finite quotients are reached by isomorphisms, and the Library's Tate cohomology and Brauer
  comparison are used rather than written again.
- **The Library's coefficients and class field theory.** The coefficients are the Library's smooth
  representations; the local invariant, the local Artin maps and the global Artin map are those of
  `Langlands/ClassFieldTheory/` (in part from the NYLL copy through its bridges, see
  [class field theory through the copies](../class-field-theory/through-the-copies.md)); the Galois
  cohomology constructs no class field theory of its own.
- **An abstract layer under the arithmetic.** Compact support, duality by dévissage and the
  nine-term sequence are proved for a compact group with a family of homomorphisms; the arithmetic
  layer supplies the hypotheses for G_S.
- **No restriction where the mathematics has none.** The real places are treated by the
  Tate-modified compact support, so Poitou–Tate duality and the formulas hold without a parity
  condition on `N`; the local theory holds for every nonarchimedean local field and modules of order
  invertible in it, in every universe.

## Origin of the text

Much of the text of these directories is ported from the repository leanprover-community/riemann-hypothesis (commit `f1f6d65`); the pages of the files
name their sources, and `licenses/RiemannHypothesis/SOURCE.md` describes the source and the terms of
its use. Each note above says which of its files are ported.
