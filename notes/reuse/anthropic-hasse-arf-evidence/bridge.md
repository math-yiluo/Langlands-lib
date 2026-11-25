# Hasse–Arf evidence: private adapter and complete declarations

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

The code is retained as an experiment transcript, not a public Lean module or accepted theorem. The adapter adapts a faithful-action argument of the Library’s `Galois.lean`. Check 08 retains the complete elaborated `#check @` types and `#print axioms` output; the terminal encoded-expression fingerprints are in checks 04, 08 and 09.

<!-- evidence-file: source-root.lean -->

## source-root.lean

SHA256 of the exact UTF-8 block: `da36162e438f9865b42c03b3f9b46e9bdd28d0f918b802ab2b2b50c2e7e5a4db`.

````lean
import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
attribute [-simp] IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf

set_option autoImplicit false

theorem IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsMulCommutative G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    RamificationChain.HasseArfChain (IsLocalRing.lowerRamificationGroup R G) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative.solution
````

<!-- evidence-file: HasseArfAudit.lean -->

## HasseArfAudit.lean

SHA256 of the exact UTF-8 block: `566ff31d67da322ad19bda203b0a579a8f9255eab70fcb29c0af87fe3fa53715`.

````lean
import Theorems.Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isMulCommutative
import Langlands.LocalFactor.Ramification.Herbrand.ArithmeticStatement

/-! Private feasibility experiment. The faithfulness argument is
adapted from the Library's Galois.lean. The remaining adapters are derived
from the displayed source and host definitions; this file is not a publication. -/
noncomputable section
namespace HasseArfAudit
open Langlands Langlands.Ramification.Padic
open IsLocalRing
universe uK uL
variable {p : ℕ} [Fact p.Prime]
  (K : PadicField.{uK} p) (L : PadicField.{uL} p)
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  (T : L.TopologicalData)

 theorem action_faithful :
    letI := integerAction T K.Carrier
    FaithfulSMul Gal(L.Carrier/K.Carrier) T.Integers := by
  letI := integerAction T K.Carrier
  letI := T.valuativeRel
  haveI : IsFractionRing T.Integers L.Carrier :=
    inferInstanceAs (IsFractionRing
      (ValuativeRel.valuation L.Carrier).valuationSubring L.Carrier)
  refine ⟨fun {σ τ} h => ?_⟩
  have heq : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.ringHom_ext (A := T.Integers) (fun x =>
      congrArg (fun y : T.Integers => (y : L.Carrier)) (h x))
  exact AlgEquiv.ext fun x => RingHom.congr_fun heq x

 theorem groups_eq (i : ℕ) :
    letI := integerAction T K.Carrier
    IsLocalRing.lowerRamificationGroup T.Integers Gal(L.Carrier/K.Carrier) i =
      Langlands.Ramification.Padic.lowerRamificationGroup T K.Carrier i := by
  letI := integerAction T K.Carrier
  ext σ
  rfl

 theorem source_chain [IsMulCommutative Gal(L.Carrier/K.Carrier)] :
    letI := integerAction T K.Carrier
    RamificationChain.HasseArfChain
      (IsLocalRing.lowerRamificationGroup T.Integers Gal(L.Carrier/K.Carrier)) := by
  letI := integerAction T K.Carrier
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  haveI : IsDiscreteValuationRing T.Integers := inferInstance
  haveI : FiniteDimensional K.Carrier L.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier L.Carrier
  haveI := action_faithful K L T
  haveI : Finite T.ResidueField := inferInstance
  haveI : Finite (T.Integers ⧸ maximalIdeal T.Integers) :=
    inferInstanceAs (Finite T.ResidueField)
  haveI : (maximalIdeal T.Integers).LiesOver
      (maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    ⟨FixedPoints.maximalIdeal_subring_eq_comap⟩
  letI : Field (T.Integers ⧸ maximalIdeal T.Integers) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    Ideal.Quotient.field _
  haveI : Finite (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier))) :=
    Finite.of_injective (algebraMap _ (T.Integers ⧸ maximalIdeal T.Integers))
      (algebraMap
        (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier) ⧸
          maximalIdeal (FixedPoints.subring T.Integers Gal(L.Carrier/K.Carrier)))
        (T.Integers ⧸ maximalIdeal T.Integers)).injective
  exact IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative

 theorem sum_Icc_eq_range (f : ℕ → ℕ) (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, f j) = ∑ j ∈ Finset.range i, f (j + 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

 theorem phi_nat (i : ℕ) :
    Langlands.Ramification.Padic.herbrandPhi T K.Carrier i =
      ((∑ j ∈ Finset.Icc 1 i, lowerGroupOrder T K.Carrier j : ℕ) : ℝ) /
        (lowerGroupOrder T K.Carrier 0 : ℝ) := by
  rw [Langlands.Ramification.Padic.herbrandPhi_floor T K.Carrier (Nat.cast_nonneg i)]
  simp only [Nat.floor_natCast, sub_self, zero_mul, add_zero]
  rw [sum_Icc_eq_range, Nat.cast_sum]

 theorem integrality [IsGalois K.Carrier L.Carrier] : HasseArfIntegrality K L T := by
  intro hcomm i hi
  letI := hcomm
  letI := integerAction T K.Carrier
  have hchain := source_chain K L T
  have hbreak : IsLocalRing.lowerRamificationGroup T.Integers Gal(L.Carrier/K.Carrier) i ≠
      IsLocalRing.lowerRamificationGroup T.Integers Gal(L.Carrier/K.Carrier) (i + 1) := by
    simpa only [groups_eq] using hi
  have hdiv := hchain i hbreak
  simp only [groups_eq] at hdiv
  obtain ⟨n, hn⟩ := hdiv
  refine ⟨(n : ℤ), ?_⟩
  rw [phi_nat]
  change ((∑ j ∈ Finset.Icc 1 i,
    Nat.card (Langlands.Ramification.Padic.lowerRamificationGroup T K.Carrier j) : ℕ) : ℝ) /
    (lowerGroupOrder T K.Carrier 0 : ℝ) = ((n : ℤ) : ℝ)
  rw [hn, Nat.cast_mul]
  have h0 : (lowerGroupOrder T K.Carrier 0 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerGroupOrder_pos T K.Carrier 0).ne'
  simpa only [Int.cast_natCast, lowerGroupOrder] using mul_div_cancel_left₀ (n : ℝ) h0

end HasseArfAudit

set_option pp.universes true in
#check @IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
#print axioms IsDiscreteValuationRing.hasseArfChain_lowerRamificationGroup_of_isMulCommutative
set_option pp.universes true in
#check @HasseArfAudit.integrality
#print axioms HasseArfAudit.integrality
#print axioms HasseArfAudit.groups_eq
#print axioms HasseArfAudit.source_chain
#print axioms HasseArfAudit.phi_nat
````

<!-- evidence-file: HasseArfAudit.md -->

## HasseArfAudit.md

SHA256 of the exact UTF-8 block: `bbc9163865ed57261a8b86dbde63b162e1f01cb7c0677aa7c0752c9a041e4135`.

````markdown
# Private Hasse–Arf adapter experiment

This private feasibility experiment specializes the adapted Anthropic FLT root at commit 6e837e75355538c7f80bab5b956861e86c4eacc2 to the actual supplied integer ring and full automorphism group. It preserves arbitrary p and independent K/L universes, and makes no choice of canonical topological data. The faithful-action proof is adapted from a private proof in the Library's Galois.lean, using fraction-ring extensionality. Group equality uses identical membership conditions. Fixed-ring maximal-ideal comparison supplies lies-over; finiteness of the actual residue field descends along its injective fixed-residue algebra map, giving perfectness and separability. The numeric step rewrites the host floor formula at a natural index, converts the Icc sum to a shifted range, and cancels the positive inertia order. The final experimental theorem has exactly the host HasseArfIntegrality target. No independent acceptance or publication is asserted. The Lean-service check a6772f3b-634c-4fad-92ec-3c7760dc0f24 succeeded with zero errors and only propext, Classical.choice, and Quot.sound. This is development evidence; the target was not submitted for exact-target validation or independent mathematical review. Raw quotient types require explicit Ideal.Quotient.field local instances before applying field injectivity and finite-field separability.
````

<!-- evidence-file: bridge-hashes.json -->

## bridge-hashes.json

SHA256 of the exact UTF-8 block: `3103647e21f013107278aa64f4c21e187a683d671271eb1fee2f6efe2ecb3e38`.

````json
[
  {
    "path": "HasseArfAudit.lean",
    "sha256": "566ff31d67da322ad19bda203b0a579a8f9255eab70fcb29c0af87fe3fa53715"
  },
  {
    "path": "HasseArfAudit.md",
    "sha256": "bbc9163865ed57261a8b86dbde63b162e1f01cb7c0677aa7c0752c9a041e4135"
  }
]
````
