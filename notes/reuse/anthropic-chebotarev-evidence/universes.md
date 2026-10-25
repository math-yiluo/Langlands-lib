# Exact universes patch

Apply this diff after the preceding stage, with zero fuzz. It contains the actual modification notices. All edits are private feasibility work; no public mathematical port follows from this document.

```diff
--- Definitions/Def_FrobeniusDensity_BadPrimes.lean
+++ Definitions/Def_FrobeniusDensity_BadPrimes.lean
@@ -4,6 +4,9 @@
 import Mathlib.RingTheory.DedekindDomain.Factorization
 import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
 import Mathlib.Data.ZMod.QuotientRing
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -15,14 +18,14 @@
     Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
   rw [ratPrimeIdeal, Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]
 
-theorem card_quotient_under_int {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
+theorem card_quotient_under_int {L : Type audit_v} [Field L] [NumberField L] {ℓ : ℕ}
     (Q : Ideal (𝓞 L)) [Q.LiesOver (ratPrimeIdeal ℓ)] :
     Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
   rw [← Q.over_def (ratPrimeIdeal ℓ), card_quotient_ratPrimeIdeal]
 
 section Ramified
 
-variable {K : Type*} [Field K] [NumberField K]
+variable {K : Type audit_u} [Field K] [NumberField K]
 
 lemma finite_setOf_dvd {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
     {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ I}.Finite := by
@@ -34,7 +37,7 @@
   exact Multiset.mem_toFinset.mpr
     ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩)
 
-variable (L : Type*) [Field L] [NumberField L]
+variable (L : Type audit_v) [Field L] [NumberField L]
 
 theorem exists_smul_ne {g : L ≃ₐ[ℚ] L} (hg : g ≠ 1) :
     ∃ x : 𝓞 L, g • x ≠ x := by
@@ -83,7 +86,7 @@
 
 section DegOneCount
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 omit [NumberField K] in
 theorem degOneCount_of_not_prime {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) : degOneCount K ℓ = 0 := by
@@ -99,7 +102,7 @@
 
 section Frob
 
-variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
+variable {L : Type audit_v} [Field L] [NumberField L] [IsGalois ℚ L]
 
 theorem isConj_arithFrobAt_of_liesOver {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₁ Q₂ : Ideal (𝓞 L))
     [Q₁.IsPrime] [Q₂.IsPrime] [Q₁.LiesOver (ratPrimeIdeal ℓ)] [Q₂.LiesOver (ratPrimeIdeal ℓ)] :
--- Definitions/Def_FrobeniusDensity_ClassGroupLSeries.lean
+++ Definitions/Def_FrobeniusDensity_ClassGroupLSeries.lean
@@ -1,4 +1,7 @@
 import Mathlib
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -9,7 +12,7 @@
 
 namespace FrobeniusDensity
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 noncomputable section
 
--- Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean
+++ Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean
@@ -3,6 +3,9 @@
 import Mathlib.Analysis.SpecialFunctions.Log.Basic
 import Mathlib.Analysis.SpecialFunctions.Pow.Real
 import Mathlib.FieldTheory.Fixed
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -15,7 +18,7 @@
 
 section DegOneCount
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 open scoped Classical in
 
@@ -28,7 +31,7 @@
 
 section AnalyticInput
 
-variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
+variable (L : Type audit_v) [Field L] [NumberField L] [IsGalois ℚ L]
 
 def DegOneAsymptotic : Prop :=
   ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
--- Definitions/Def_FrobeniusDensity_PrimeSums.lean
+++ Definitions/Def_FrobeniusDensity_PrimeSums.lean
@@ -1,6 +1,9 @@
 import Definitions.Def_FrobeniusDensity_BadPrimes
 import Mathlib.NumberTheory.NumberField.DedekindZeta
 import Mathlib.RingTheory.DedekindDomain.Factorization
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -10,7 +13,7 @@
 
 namespace FrobeniusDensity
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 noncomputable def normRpow (s : ℝ) (I : Ideal (𝓞 K)) : ℝ≥0∞ :=
   (Ideal.absNorm I : ℝ≥0∞) ^ (-s)
--- Definitions/Def_LanglandsTunnell_NormClass.lean
+++ Definitions/Def_LanglandsTunnell_NormClass.lean
@@ -1,4 +1,7 @@
 import Definitions.Def_NarrowRayClassGroup
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 set_option maxHeartbeats 800000
@@ -9,7 +12,7 @@
 
 open NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply
 
-variable (K : Type*) [Field K] [NumberField K] (q : ℕ)
+variable (K : Type audit_u) [Field K] [NumberField K] (q : ℕ)
 
 theorem norm_int_cast_eq_one_of_sub_one_mem {α : 𝓞 K}
     (hα : α - 1 ∈ Ideal.span {(q : 𝓞 K)}) :
--- Definitions/Def_NarrowRayClassGroup.lean
+++ Definitions/Def_NarrowRayClassGroup.lean
@@ -6,6 +6,9 @@
 import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
 import Mathlib.GroupTheory.QuotientGroup.Finite
 import Mathlib.Data.Fintype.Units
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 open NumberField nonZeroDivisors IsDedekindDomain
 
@@ -70,7 +73,7 @@
 
 section Carriers
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 def coprimeToModulus (𝔣 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal ((𝓞 K)⁰) K)ˣ where
   carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
@@ -159,7 +162,7 @@
 
 section Symbol
 
-variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
+variable (K : Type audit_u) [Field K] [NumberField K] {M : Type*} [CommGroup M]
 
 def raySymbol (f : HeightOneSpectrum (𝓞 K) → M) (I : FractionalIdeal ((𝓞 K)⁰) K) : M :=
   ∏ᶠ v : HeightOneSpectrum (𝓞 K), f v ^ FractionalIdeal.count K v I
@@ -206,7 +209,7 @@
 
 section Finiteness
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 def raySet (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
   {I | ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣 ∧
@@ -853,7 +856,7 @@
 
 section Packaging
 
-variable (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
+variable (K : Type audit_u) [Field K] [NumberField K] {M : Type*} [CommGroup M]
 
 def primeUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
   FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero (by
@@ -949,7 +952,7 @@
 
 section Degenerate
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 theorem coprimeToModulus_top : coprimeToModulus K (⊤ : Ideal (𝓞 K)) = ⊤ := by
   rw [eq_top_iff]
--- Definitions/Def_NumberField_CompletedRayL.lean
+++ Definitions/Def_NumberField_CompletedRayL.lean
@@ -1,6 +1,9 @@
 import Definitions.Def_NarrowRayClassGroup
 import Mathlib.NumberTheory.LSeries.Basic
 import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -10,7 +13,7 @@
 
 noncomputable section
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 def rayZetaCoeff (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) : ℕ :=
   Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
--- Definitions/Def_NumberField_EuclideanIdealLattice.lean
+++ Definitions/Def_NumberField_EuclideanIdealLattice.lean
@@ -1,6 +1,9 @@
 import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
 import Mathlib.NumberTheory.NumberField.Discriminant.Defs
 import Mathlib.Analysis.SpecialFunctions.Pow.Real
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -11,7 +14,7 @@
 
 namespace Deep.Analytic
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 open Classical in
 
@@ -23,7 +26,7 @@
 
 namespace M4aP2
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 def heckeScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
   (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
--- Definitions/Def_NumberField_NormResidueCharacter.lean
+++ Definitions/Def_NumberField_NormResidueCharacter.lean
@@ -4,6 +4,9 @@
 import Definitions.Def_LanglandsTunnell_NormClass
 import Definitions.Def_NumberField_RayCharacterData
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 set_option autoImplicit false
 set_option linter.unusedSectionVars false
 
@@ -15,7 +18,7 @@
 open LanglandsTunnell.P2.Artin
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]
+variable (K : Type audit_u) [Field K] [NumberField K] (m : ℕ) [NeZero m]
 
 abbrev fm : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}
 
@@ -166,7 +169,7 @@
 
 section Cyclo
 
-variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
+variable {L : Type audit_v} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
 
 theorem absNorm_cast_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ m) (w : HeightOneSpectrum (𝓞 L))
     (hw : (m : 𝓞 L) ∉ w.asIdeal) : (Ideal.absNorm w.asIdeal : ZMod m) = 1 := by
--- Definitions/Def_NumberField_PrimeNormSums.lean
+++ Definitions/Def_NumberField_PrimeNormSums.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import Definitions.Def_FrobeniusDensity_PrimeSums
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 set_option autoImplicit false
 set_option linter.unusedSectionVars false
 
@@ -13,7 +16,7 @@
 
 section PrimeSums
 
-variable (F : Type) [Field F] [NumberField F] {m : ℕ} [NeZero m]
+variable (F : Type*) [Field F] [NumberField F] {m : ℕ} [NeZero m]
 
 def pw (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)
 
@@ -219,7 +222,7 @@
 
 section Residue
 
-variable (F : Type) [Field F] [NumberField F] (m : ℕ) [NeZero m]
+variable (F : Type*) [Field F] [NumberField F] (m : ℕ) [NeZero m]
 
 def T (a : ZMod m) (s : ℝ) : ℝ :=
   ∑' v : HeightOneSpectrum (𝓞 F), if (Ideal.absNorm v.asIdeal : ZMod m) = a then pw F s v else 0
--- Definitions/Def_NumberField_RayCharacterData.lean
+++ Definitions/Def_NumberField_RayCharacterData.lean
@@ -1,5 +1,8 @@
 import Definitions.Def_NarrowRayClassGroup
 import Mathlib.RingTheory.DedekindDomain.Different
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -10,7 +13,7 @@
 open Real NumberField NumberField.InfinitePlace Deep.NTSupply
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 def signAt (S : Finset {w : InfinitePlace K // IsReal w}) (x : K) : ℂ :=
   ∏ v ∈ S, ((SignType.sign (embedding_of_isReal v.2 x) : ℤ) : ℂ)
--- Definitions/Def_TaylorWiles_Primes.lean
+++ Definitions/Def_TaylorWiles_Primes.lean
@@ -3,6 +3,9 @@
 import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
 import Mathlib.LinearAlgebra.Matrix.Trace
 import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -37,7 +40,7 @@
 
 open NumberField Ideal
 
-variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
+variable (L : Type audit_v) [Field L] [NumberField L] [IsGalois ℚ L]
 
 abbrev ratPrimeIdeal (ℓ : ℕ) : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
 
@@ -78,7 +81,7 @@
 
 open NumberField Ideal FrobeniusDensity
 
-variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
+variable {L : Type audit_v} [Field L] [NumberField L] [IsGalois ℚ L]
 variable {𝕜 : Type*} [Field 𝕜]
 
 variable (L) in
--- P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean
+++ P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean
@@ -1,6 +1,9 @@
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Mathlib.NumberTheory.NumberField.DedekindZeta
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_FrobeniusDensity_idealSum_ne_top
 
 set_option autoImplicit false
@@ -12,7 +15,7 @@
 p2m_export "FrobeniusDensity" "normRpow idealSum idealCount zetaTerm"
 p2m_open "FrobeniusDensity"
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
   unfold zetaTerm
@@ -121,7 +124,7 @@
 
 end FrobeniusDensity
 
-theorem solution (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
+theorem solution (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
     FrobeniusDensity.idealSum K s ≠ ⊤ := by
   rw [FrobeniusDensity.idealSum_eq_tsum_zetaTerm,
     ← ENNReal.ofReal_tsum_of_nonneg (FrobeniusDensity.zetaTerm_nonneg K s)
--- P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
+++ P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
@@ -5,6 +5,9 @@
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Mathlib.NumberTheory.NumberField.DedekindZeta
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO
 
 set_option autoImplicit false
@@ -17,7 +20,7 @@
 p2m_export "FrobeniusDensity" "tendsto_sub_one_mul_idealSum_test normRpow idealSum primeSum primeSqSum IsFactoredBy factoredSum one_le_absNorm primeFactors idealSum_ne_top"
 p2m_open "FrobeniusDensity"
 
-variable {K : Type*} [Field K] [NumberField K]
+variable {K : Type audit_u} [Field K] [NumberField K]
 
 private lemma tsum_equiv {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
     ∑' a, f (e a) = ∑' b, f b := by
@@ -469,7 +472,7 @@
 
 p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.FrobeniusDensity"
 
-theorem solution (K : Type*) [Field K] [NumberField K] :
+theorem solution (K : Type audit_u) [Field K] [NumberField K] :
     (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
       =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
   have h := (primeSum_sub_log_idealSum_isBigO K).add (log_idealSum_add_log_isBigO K)
--- P2M/Sol/S_FrobeniusDensity_tailSum_le.lean
+++ P2M/Sol/S_FrobeniusDensity_tailSum_le.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_FrobeniusDensity_tailSum_le
 
 p2m_open "Ideal NumberField Filter Topology Asymptotics IsDedekindDomain Ideal.IsDedekindDomain"
@@ -11,7 +14,7 @@
 namespace TEPort
 p2m_open "FrobeniusDensity"
 
-variable {K : Type*} [Field K] [NumberField K]
+variable {K : Type audit_u} [Field K] [NumberField K]
 
 lemma one_le_cast_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
     (1 : ℝ≥0∞) ≤ (Ideal.absNorm I : ℝ≥0∞) := by
@@ -153,6 +156,6 @@
 
 open scoped ENNReal in
 theorem solution
-    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
+    (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
     FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst :=
   FrobeniusDensity.TEPort.tailSum_le K hs
--- P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
+++ P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
@@ -2,6 +2,9 @@
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Mathlib.NumberTheory.NumberField.DedekindZeta
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test
 
 set_option autoImplicit false
@@ -13,7 +16,7 @@
 p2m_export "FrobeniusDensity" "normRpow idealSum idealCount zetaTerm"
 p2m_open "FrobeniusDensity"
 
-variable (K : Type*) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
   unfold zetaTerm
@@ -136,7 +139,7 @@
 
 p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.FrobeniusDensity"
 
-theorem solution (K : Type*) [Field K] [NumberField K] :
+theorem solution (K : Type audit_u) [Field K] [NumberField K] :
     Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
       (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
   rw [← Filter.tendsto_ofReal_iff]
--- P2M/Sol/S_M4aTorus_completedRayL_fe.lean
+++ P2M/Sol/S_M4aTorus_completedRayL_fe.lean
@@ -58,6 +58,9 @@
 import Mathlib.Analysis.Normed.Module.Connected
 import Mathlib.LinearAlgebra.Complex.FiniteDimensional
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_M4aTorus_completedRayL_fe
 
 section TcFold_M4aTheta_ClassSum
@@ -73,7 +76,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def classCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
   Nat.card {I : (Ideal (𝓞 K))⁰ //
@@ -124,7 +127,7 @@
 
 open scoped Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def twoConjEquiv : ℂ ≃ₗ[ℝ] ℂ where
   toFun z := 2 * (starRingEnd ℂ) z
@@ -215,7 +218,7 @@
 
 open scoped Classical ComplexConjugate RealInnerProductSpace
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem mkFiber_of_isReal {w : InfinitePlace K} (hw : IsReal w) :
     ({φ : K →+* ℂ | InfinitePlace.mk φ = w} : Finset _) = {w.embedding} := by
@@ -252,7 +255,7 @@
     rw [ComplexEmbedding.isReal_iff]; exact h.symm
   exact (not_isReal_iff_isComplex.mpr hw) (isReal_iff.mpr this)
 
-private theorem sum_embeddings_eq_sum_infinitePlace {M : Type} [AddCommMonoid M]
+private theorem sum_embeddings_eq_sum_infinitePlace {M : Type*} [AddCommMonoid M]
     (f : (K →+* ℂ) → M) :
     ∑ φ : K →+* ℂ, f φ
       = (∑ w : {w : InfinitePlace K // IsReal w}, f w.1.embedding)
@@ -371,7 +374,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {d : Type} [Fintype d]
+variable {d : Type*} [Fintype d]
 
 private def intVec (n : d → ℤ) : d → ℝ := fun i => (n i : ℝ)
 
@@ -734,8 +737,8 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {ι : Type} [Fintype ι] [DecidableEq ι]
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {ι : Type*} [Fintype ι] [DecidableEq ι]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -1035,7 +1038,7 @@
 private def LatticeThetaSummable (L : Submodule ℤ E) (t : ℝ) : Prop :=
   Summable fun v : L => Real.exp (-π * t * ‖(v : E)‖ ^ 2)
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 end Deep.Analytic
 
@@ -1130,7 +1133,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -1240,7 +1243,7 @@
 
 section Duality
 
-variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
+variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
 
 end Duality
 
@@ -1268,7 +1271,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def heckeDensity : ℝ :=
   (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
@@ -1349,7 +1352,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private scoped instance finite_classNormFiber (C : ClassGroup (𝓞 K)) (n : ℕ) :
     Finite {I : (Ideal (𝓞 K))⁰ //
@@ -1381,7 +1384,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 end Deep.Analytic
 p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
@@ -1407,7 +1410,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 end Deep.Analytic
 p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
@@ -1433,7 +1436,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 open Classical in
 
@@ -1473,7 +1476,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 end Deep.Analytic
 p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
@@ -1501,7 +1504,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 end Deep.Analytic
 p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
@@ -1529,7 +1532,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E)
 
@@ -1573,7 +1576,7 @@
 open Real MeasureTheory Set Function Topology Module Filter Asymptotics
 open scoped RealInnerProductSpace
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
   (L : Submodule ℤ E)
 
@@ -1603,7 +1606,7 @@
 
 open scoped nonZeroDivisors RealInnerProductSpace Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private scoped instance discreteTopology_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
     DiscreteTopology (Deep.Analytic.euclideanIdealLattice K I) := by
@@ -1662,7 +1665,7 @@
 
 open scoped nonZeroDivisors RealInnerProductSpace Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def mixedConjDilCLE :
     euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
@@ -1735,7 +1738,7 @@
 
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (L : Submodule ℤ (euclidean.mixedSpace K))
   [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -1776,7 +1779,7 @@
 
 open scoped nonZeroDivisors Classical ComplexConjugate
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def euclideanEmbedding : K →ₗ[ℤ] euclidean.mixedSpace K :=
   (((euclidean.toMixed K).symm.toLinearMap).restrictScalars ℤ).comp
@@ -1867,7 +1870,7 @@
     ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
     (basisOfFractionalIdeal K I) (fractionalIdeal_restrictScalars_eq_span K I)).symm
 
-private theorem inner_ext_basis {ι : Type} [Finite ι] (b : Basis ι ℝ (euclidean.mixedSpace K))
+private theorem inner_ext_basis {ι : Type*} [Finite ι] (b : Basis ι ℝ (euclidean.mixedSpace K))
     {v w : euclidean.mixedSpace K}
     (h : ∀ j, inner ℝ v (b j) = (inner ℝ w (b j) : ℝ)) : v = w := by
   have hz : innerₗ (euclidean.mixedSpace K) (v - w) = 0 := by
@@ -1965,7 +1968,7 @@
 
 open scoped nonZeroDivisors Classical ComplexConjugate
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 variable (reps dreps : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
 
@@ -1993,7 +1996,7 @@
 
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem abs_discr_pos : 0 < |(discr K : ℝ)| :=
   abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
@@ -2064,7 +2067,7 @@
 
 open scoped nonZeroDivisors RealInnerProductSpace Classical ComplexConjugate
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def sqrtTwoEquiv : ℂ ≃ₗ[ℝ] ℂ where
   toFun z := ((Real.sqrt 2 : ℝ) : ℂ) * z
@@ -2321,7 +2324,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def heckeForm (x : K) : ℝ :=
   (∑ v : {w : InfinitePlace K // IsReal w}, (v.1 x) ^ 2)
@@ -2368,7 +2371,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 section H1
 open NumberField.mixedEmbedding
@@ -2639,7 +2642,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 section Torsor
 
@@ -3060,7 +3063,7 @@
 p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
 open scoped nonZeroDivisors
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 variable {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 
@@ -3134,7 +3137,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -3188,7 +3191,7 @@
 p2m_export "Deep.Analytic" "euclideanIdealLattice"
 p2m_open "Deep.Analytic Deep"
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -3221,7 +3224,7 @@
 
 section Abstract
 
-variable {α : Type} [AddCommGroup α] (H : AddSubgroup α)
+variable {α : Type*} [AddCommGroup α] (H : AddSubgroup α)
 
 private theorem tsum_partition_quotient {f : α → ℂ} (hf : Summable f) :
     ∑' v : α, f v
@@ -3256,7 +3259,7 @@
 end Abstract
 p2m_reactivate "P2MW.S_M4aTorus_completedRayL_fe.Deep P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
   [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
 
@@ -3308,7 +3311,7 @@
 p2m_open "Real Complex MeasureTheory Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped FourierTransform InnerProductSpace
 
-variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
+variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
   [MeasurableSpace E] [BorelSpace E]
 
 private def oddConst (t : ℝ) (j : ℕ) : ℝ := 1 + (j.factorial : ℝ) / (π * t / 2) ^ j
@@ -3372,7 +3375,7 @@
   rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
   exact norm_pow_mul_gaussian_le ht j v
 
-variable {σ : Type} (e : σ → E)
+variable {σ : Type*} (e : σ → E)
 
 private def polyS (S : Finset σ) (x : E) : ℂ := ∏ u ∈ S, ((⟪e u, x⟫_ℝ : ℝ) : ℂ)
 
@@ -3685,7 +3688,7 @@
     rw [fourier_oddTranslatedMap e he ht S v₀ (w : E), Circle.smul_def, smul_eq_mul]
     ring
 
-private theorem weightedOddCoset_poisson [DecidableEq σ] {ι : Type} [Fintype ι] (he : Orthonormal ℝ e)
+private theorem weightedOddCoset_poisson [DecidableEq σ] {ι : Type*} [Fintype ι] (he : Orthonormal ℝ e)
     (rep : ι → E) (wt : ι → ℂ) {t : ℝ} (ht : 0 < t) (S : Finset σ) :
     ∑ i, wt i * ∑' v : L, oddGaussian e t S ((v : E) + rep i)
       = (ZLattice.covolume L volume : ℂ)⁻¹ * ((-Complex.I) ^ S.card * (1 / (t : ℂ)) ^ S.card)
@@ -3739,7 +3742,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -4407,7 +4410,7 @@
 p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -4449,7 +4452,7 @@
 
 open scoped nonZeroDivisors RealInnerProductSpace Classical ComplexConjugate
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def mulEquiv (a : ℝ) (ha : 0 < a) : ℝ ≃ₗ[ℝ] ℝ where
   toFun x := a * x
@@ -4723,7 +4726,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def foldBox : Set (realSpace K) :=
   {x | ∀ w : InfinitePlace K, w ≠ dirichletUnitTheorem.w₀ → x w ∈ Ico (0 : ℝ) 2}
@@ -4762,7 +4765,7 @@
 
 open scoped nonZeroDivisors RealInnerProductSpace Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem continuous_torusNorm : Continuous (torusNorm K) := by
   unfold torusNorm
@@ -4825,7 +4828,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def orthant : Set (realSpace K) := {t | ∀ w, 0 < t w}
 
@@ -5230,7 +5233,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem unitScale_of_mem_torsion {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) : unitScale K ζ = 1 := by
   funext w
@@ -5341,7 +5344,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def orbitExp (σ : ℝ) (w : InfinitePlace K) : ℝ := (mult w : ℝ) * (σ / 2)
 
@@ -5401,7 +5404,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem classZetaCoeff_eq_classCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) :
     classZetaCoeff K C n = Deep.Analytic.classCoeff K C n :=
@@ -5544,7 +5547,7 @@
     Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN)]
   simp
 
-private theorem tsum_ofReal_ne_top_of_summable {α : Type} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
+private theorem tsum_ofReal_ne_top_of_summable {α : Type*} {f : α → ℝ} (h0 : ∀ a, 0 ≤ f a)
     (hf : Summable f) : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by
   rw [← ENNReal.ofReal_tsum_of_nonneg h0 hf]
   exact ENNReal.ofReal_ne_top
@@ -5570,7 +5573,7 @@
 p2m_export "M4aTorus" "rayZetaCoeff rayZeta rayClassLSeries completedRayL"
 p2m_open "M4aTorus"
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private scoped instance countable_euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
     Countable (euclideanIdealLattice K I) :=
@@ -5600,7 +5603,7 @@
 p2m_open "NumberField.InfinitePlace NumberField.Units MeasureTheory Set Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2"
 open scoped nonZeroDivisors ENNReal Classical Real
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem expMapBasis_neg (x : realSpace K) :
     expMapBasis (-x) = (expMapBasis x)⁻¹ := by
@@ -5890,7 +5893,7 @@
 p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 
 private def raySWeight (t : realSpace K) : ℂ := ∏ v ∈ S, ((Real.sqrt (t v) : ℝ) : ℂ)
@@ -5970,7 +5973,7 @@
 p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
 open scoped nonZeroDivisors Classical Real
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -6061,7 +6064,7 @@
 p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
 open scoped nonZeroDivisors Classical Real
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 
@@ -6126,7 +6129,7 @@
 open MeasureTheory Set Filter
 open scoped nonZeroDivisors ENNReal Classical Real
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def highBox : Set (realSpace K) :=
   Set.univ.pi fun w => if w = w₀ then Set.Ici (0 : ℝ) else Set.Ico 0 2
@@ -6732,7 +6735,7 @@
 open NumberField.Units MeasureTheory Filter
 open scoped nonZeroDivisors Classical Real ENNReal
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -7316,7 +7319,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic MeasureTheory"
 open scoped nonZeroDivisors Classical FourierTransform InnerProductSpace
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def realUnit (v : {w : InfinitePlace K // IsReal w}) : euclidean.mixedSpace K :=
   euclidean.stdOrthonormalBasis K (Sum.inl v)
@@ -7403,7 +7406,7 @@
 p2m_open "Real NumberField Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic IsDedekindDomain"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
 
@@ -7650,7 +7653,7 @@
 p2m_open "NumberField NumberField.InfinitePlace Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic IsDedekindDomain"
 open scoped nonZeroDivisors Classical
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private abbrev dualFI (𝔣 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K :=
   ((𝔣 : FractionalIdeal (𝓞 K)⁰ K) * diffFI K)⁻¹
@@ -7965,7 +7968,7 @@
 p2m_open "Real NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic MeasureTheory"
 open scoped nonZeroDivisors Classical FourierTransform InnerProductSpace
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 section Weights
 
@@ -8138,7 +8141,7 @@
 p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical Real FourierTransform InnerProductSpace
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem polyS_placeScale (S : Finset {w : InfinitePlace K // IsReal w})
     (c : InfinitePlace K → ℝ) (hc : ∀ w, 0 < c w)
@@ -9152,7 +9155,7 @@
 p2m_open "MeasureTheory Deep.NTSupply M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic"
 open scoped nonZeroDivisors Classical Real FourierTransform InnerProductSpace
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -9213,7 +9216,7 @@
 p2m_open "MeasureTheory Deep.NTSupply Deep.Analytic P2MW.S_M4aTorus_completedRayL_fe.Deep.Analytic M4aP2 P2MW.S_M4aTorus_completedRayL_fe.M4aP2 Complex"
 open scoped nonZeroDivisors Classical Real
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 
@@ -9998,7 +10001,7 @@
     rw [chiIdeal_eq_zero_of_not_mem χ h0 (by rw [hmk]; exact hc), zero_mul]
     exact (Finset.sum_eq_zero fun C _ => by rw [Set.indicator_of_notMem (hI C), mul_zero]).symm
 
-private theorem sum_tsum_chiIdeal_eq_rayClassLSeries {ι : Type} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
+private theorem sum_tsum_chiIdeal_eq_rayClassLSeries {ι : Type*} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
     (𝔞' : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
     (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞' i))
     {s : ℂ} (hs : 1 < s.re) :
@@ -10172,7 +10175,7 @@
             * Gammaℂ s ^ nrComplexPlaces K)) by ring,
     div_mul_cancel₀ _ hw, h1, mul_one, h2, one_mul]
 
-private theorem completedRayL_eq_sum_rayFoldMellin {ι : Type} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
+private theorem completedRayL_eq_sum_rayFoldMellin {ι : Type*} [Fintype ι] (h𝔣 : 𝔣 ≠ ⊥)
     (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
     (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i))
     {s : ℂ} (hs : 1 < s.re) :
@@ -10332,7 +10335,7 @@
   · obtain ⟨y, hy, hyχ⟩ := key 𝔞 x₀ hx₀
     rw [uWeight, signAt, Finset.prod_empty, mul_one, ← hyχ, ← hψ, hy]
 
-private theorem tc2Cancel {ι : Type} [Fintype ι] [Fintype (𝓞 K ⧸ 𝔣)] (hpar : IsParity K 𝔣 χ S)
+private theorem tc2Cancel {ι : Type*} [Fintype ι] [Fintype (𝓞 K ⧸ 𝔣)] (hpar : IsParity K 𝔣 χ S)
     (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
     (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
     (hbij : Function.Bijective fun i => ClassGroup.mk K (𝔞 i))
@@ -10882,7 +10885,7 @@
               * ((Real.exp (-π * (1 / rayScale K ⊤ 𝔞)
                   * torusForm K t (mixedEmbedding K (z.1 : K))) : ℝ) : ℂ)) * hSWc
 
-private theorem tc2CancelTop {ι : Type} [Fintype ι]
+private theorem tc2CancelTop {ι : Type*} [Fintype ι]
     (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (_hpar : IsParity K ⊤ χ S)
     (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -10995,7 +10998,7 @@
   exact (hf.analyticOnNhd isOpen_U01).eqOn_of_preconnected_of_eventuallyEq
     (hg.analyticOnNhd isOpen_U01) isPreconnected_U01 h2 hev
 
-variable {ι : Type} [Fintype ι]
+variable {ι : Type*} [Fintype ι]
 
 private def perIdeal (High ID q₁ q₀ : ℂ → ℂ) (P₁ P₀ : ℂ) (s : ℂ) : ℂ :=
   High s + ID s + P₁ * q₁ s + P₀ * q₀ s
@@ -11063,7 +11066,7 @@
 
 section Bot
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private theorem completedRayL_bot (χ : NarrowRayClassGroup K ⊥ →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) {s : ℂ} (hs : s ≠ 0) :
@@ -11079,7 +11082,7 @@
 
 section Holes
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 variable (S : Finset {w : InfinitePlace K // IsReal w})
 variable (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
@@ -11383,7 +11386,7 @@
 
 section Assembly
 
-variable (K : Type) [Field K] [NumberField K]
+variable (K : Type audit_u) [Field K] [NumberField K]
 
 private def WallConj (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (F G : ℂ → ℂ) : Prop :=
@@ -11544,7 +11547,7 @@
 variable {ψ S}
 
 private theorem wallHalf_of_T2 [Fintype (𝓞 K ⧸ 𝔣)] (hS : IsParity K 𝔣 ψ S) (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
-    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
+    {ι : Type*} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
     (hx₀ : ∀ i, IsCoprimeGenerator K 𝔣 ψ (𝔞 i) (x₀ i)) (α : ι → ℂ → ℂ)
     (hα : ∀ i, Differentiable ℂ (α i)) (Λ : ℂ → ℂ)
     (hT : ∀ s : ℂ, 1 < s.re → Λ s = ∑ i, α i s * rayFoldMellin K 𝔣 ψ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s)
@@ -11576,7 +11579,7 @@
 private theorem wallConj_of_T2 [Fintype (𝓞 K ⧸ 𝔣)] (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K 𝔣 χ S)
     (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤)
-    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
+    {ι : Type*} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
     (x₀ : ι → K) (hx₀ : ∀ i, IsCoprimeGenerator K 𝔣 χ (𝔞 i) (x₀ i))
     (x₀' : ι → K) (hx₀' : ∀ i, IsCoprimeGenerator K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ)
       (rayDualIdeal K 𝔣 h𝔣 (𝔞 i)) (x₀' i))
@@ -11715,7 +11718,7 @@
 private theorem hole_T2 (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K 𝔣 χ S)
     (h𝔣 : 𝔣 ≠ ⊥) (h𝔣' : 𝔣 ≠ ⊤) [Fintype (𝓞 K ⧸ 𝔣)] :
-    ∃ (ι : Type) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α α' : ι → ℂ → ℂ),
+    ∃ (ι : Type audit_u) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α α' : ι → ℂ → ℂ),
       (∀ i, Differentiable ℂ (α i)) ∧ (∀ i, Differentiable ℂ (α' i)) ∧
       (∀ s : ℂ, 1 < s.re → completedRayL K 𝔣 χ S s
         = ∑ i, α i s * rayFoldMellin K 𝔣 χ S (𝔞 i) (rayScale K 𝔣 (𝔞 i)) s) ∧
@@ -11898,7 +11901,7 @@
 
 variable {ψ S}
 
-private theorem wallHalf_top {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
+private theorem wallHalf_top {ι : Type*} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : ι → K)
     (P₀ : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ)
     (hinv : ∀ i, ∀ t ∈ orthant K, ∀ s : ℂ,
       rayFoldMellinIntegrand K ⊤ ψ S (𝔞 i) (rayScale K ⊤ (𝔞 i)) s t⁻¹
@@ -11919,7 +11922,7 @@
 
 private theorem wallConj_top (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w})
-    {ι : Type} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
+    {ι : Type*} [Fintype ι] (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
     (x₀ x₀' : ι → K) (α : ι → ℂ → ℂ) (hα : ∀ i, Differentiable ℂ (α i))
     (P₀ P₀' : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ)
     (hinv : ∀ i, ∀ t ∈ orthant K, ∀ s : ℂ,
@@ -11983,7 +11986,7 @@
 
 private theorem hole_top (χ : NarrowRayClassGroup K (⊤ : Ideal (𝓞 K)) →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : IsParity K ⊤ χ S) :
-    ∃ (ι : Type) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : ι → ℂ → ℂ)
+    ∃ (ι : Type audit_u) (_ : Fintype ι) (𝔞 : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (α : ι → ℂ → ℂ)
       (P₀ P₀' : (FractionalIdeal (𝓞 K)⁰ K)ˣ → ℂ),
       (∀ i, Differentiable ℂ (α i)) ∧
       (∀ s : ℂ, 1 < s.re → completedRayL K ⊤ χ S s
@@ -12058,7 +12061,7 @@
       (hcancel x₀ hx₀) (hcancel' x₀' hx₀')
 
 private theorem completedRayL_fe_impl
-    (K : Type) [Field K] [NumberField K]
+    (K : Type audit_u) [Field K] [NumberField K]
     (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ F G : ℂ → ℂ,
@@ -12107,7 +12110,7 @@
 
 open _root_.M4aTorus _root_.P2MW.S_M4aTorus_completedRayL_fe.M4aTorus in
 theorem solution
-    (K : Type) [Field K] [NumberField K]
+    (K : Type audit_u) [Field K] [NumberField K]
     (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ F G : ℂ → ℂ,
--- P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
+++ P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
@@ -1,5 +1,8 @@
 import Mathlib
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
 
 set_option autoImplicit false
@@ -9,10 +12,10 @@
 open NumberField NumberField.InfinitePlace
 open scoped Classical
 
-noncomputable def placeFactor {K : Type} [Field K] (w : InfinitePlace K) (x : K) : ℝ :=
+noncomputable def placeFactor {K : Type audit_u} [Field K] (w : InfinitePlace K) (x : K) : ℝ :=
   if hw : IsReal w then embedding_of_isReal hw x else Complex.normSq (w.embedding x)
 
-theorem prod_fiber_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : K) :
+theorem prod_fiber_eq {K : Type audit_u} [Field K] [NumberField K] (w : InfinitePlace K) (x : K) :
     (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (placeFactor w x : ℂ) := by
   classical
   have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
@@ -42,7 +45,7 @@
     rw [hfibset, Finset.prod_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
       Complex.mul_conj, placeFactor, dif_neg hw]
 
-theorem norm_eq_prod_placeFactor {K : Type} [Field K] [NumberField K] (x : K) :
+theorem norm_eq_prod_placeFactor {K : Type audit_u} [Field K] [NumberField K] (x : K) :
     ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, placeFactor w x := by
   classical
   have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) =
@@ -59,7 +62,7 @@
   exact Complex.ofReal_inj.mp hofreal
 
 open scoped Classical in
-theorem main (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
+theorem main (K : Type audit_u) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
     SignType.sign (Algebra.norm ℚ x) =
       ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
   have hcast : SignType.sign (Algebra.norm ℚ x) = SignType.sign ((Algebra.norm ℚ x : ℚ) : ℝ) := by
@@ -88,7 +91,7 @@
 open NumberField NumberField.InfinitePlace in
 open scoped Classical in
 theorem solution
-    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
+    (K : Type audit_u) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
     SignType.sign (Algebra.norm ℚ x) =
       ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) :=
   P2mSignNorm.main K hx
--- P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
+++ P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
@@ -4,6 +4,9 @@
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Definitions.Def_NumberField_PrimeNormSums
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries
 
 set_option autoImplicit false
@@ -17,7 +20,7 @@
 
 set_option linter.unusedSectionVars false
 
-variable {K : Type} [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)}
+variable {K : Type audit_u} [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)}
   (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
 
 def chiI (I : Ideal (𝓞 K)) : ℂ := M4aP2.chiIdeal K 𝔣 χ (I : FractionalIdeal (𝓞 K)⁰ K)
@@ -670,7 +673,7 @@
 open NumberField IsDedekindDomain Deep.NTSupply in
 open scoped nonZeroDivisors in
 theorem solution
-    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
+    (K : Type audit_u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
     ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
       (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
--- P2M/Sol/S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
+++ P2M/Sol/S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
@@ -3,6 +3,9 @@
 import Definitions.Def_NumberField_RayCharacterData
 import Theorems.Thm_M4aTorus_completedRayL_fe
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one
 
 set_option autoImplicit false
@@ -55,7 +58,7 @@
       rw [hexp, mul_inv_cancel₀ hΓ1, mul_inv_cancel₀ hΓ2]
       simp
 
-theorem main (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
+theorem main (K : Type audit_u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
     (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
@@ -94,7 +97,7 @@
 
 open NumberField NumberField.InfinitePlace Deep.NTSupply in
 theorem solution
-    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
+    (K : Type audit_u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
     (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
--- P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
+++ P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
@@ -13,6 +13,9 @@
 import Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO
 import Theorems.Thm_FrobeniusDensity_tailSum_le
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
 
 set_option autoImplicit false
@@ -27,7 +30,7 @@
 
 set_option linter.unusedSectionVars false
 
-variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]
+variable (K : Type audit_u) [Field K] [NumberField K] (m : ℕ) [NeZero m]
 
 variable {K m}
 
@@ -81,7 +84,7 @@
 
 section PrimeSums
 
-variable {F : Type} [Field F] [NumberField F]
+variable {F : Type*} [Field F] [NumberField F]
 
 theorem tail_le {s : ℝ} (hs : 1 ≤ s) :
     (∑' v : HeightOneSpectrum (𝓞 F), if (Ideal.absNorm v.asIdeal).Prime then 0 else pw F s v) ≤ Ctail F := by
@@ -89,7 +92,7 @@
   refine ENNReal.toReal_mono ?_ (FrobeniusDensity.tailSum_le F hs)
   exact (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top tailConst_lt_top).ne
 
-theorem exists_logpole (F : Type) [Field F] [NumberField F] :
+theorem exists_logpole (F : Type*) [Field F] [NumberField F] :
     ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
       |(∑' v, pw F s v) + Real.log (s - 1)| ≤ C := by
   have h := FrobeniusDensity.primeSum_toReal_add_log_isBigO F
@@ -106,13 +109,13 @@
 
 section Bounds
 
-variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
+variable {L : Type audit_v} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
 
 def good (w : HeightOneSpectrum (𝓞 L)) : Prop := (Ideal.absNorm w.asIdeal).Prime ∧ (m : 𝓞 L) ∉ w.asIdeal
 
 variable (K m) in
 
-def XL (L : Type) [Field L] [NumberField L] (s : ℝ) : ℝ :=
+def XL (L : Type audit_v) [Field L] [NumberField L] (s : ℝ) : ℝ :=
   ∑' w : HeightOneSpectrum (𝓞 L), if good (m := m) w then pw L s w else 0
 
 theorem XL_term_nonneg (s : ℝ) (w : HeightOneSpectrum (𝓞 L)) :
@@ -422,7 +425,7 @@
   rw [mul_add, mul_div_cancel₀ _ hc.ne', mul_one] at h2
   linarith
 
-variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
+variable {L : Type audit_v} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
 
 def Lr (ψ : DirichletCharacter ℂ m) (s : ℝ) : ℂ := M4aTorus.rayClassLSeries K (fm K m) (chi K m ψ) s
 
@@ -452,7 +455,7 @@
 
 section Squeeze
 
-variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
+variable {L : Type audit_v} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]
 
 omit [IsCyclotomicExtension {m} K L] in
 
@@ -836,7 +839,7 @@
 
 open NumberField in
 theorem solution
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (C : ℝ) :
     ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
--- P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
+++ P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
@@ -4,6 +4,9 @@
 import Theorems.Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
 import Theorems.Thm_FrobeniusDensity_tailSum_le
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
 attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 
@@ -18,7 +21,7 @@
 
 set_option linter.unusedSectionVars false
 
-variable {K : Type} [Field K] [NumberField K]
+variable {K : Type audit_u} [Field K] [NumberField K]
 
 theorem tsum_le_card_of_support {E : Set (HeightOneSpectrum (𝓞 K))} (hE : E.Finite)
     (f : HeightOneSpectrum (𝓞 K) → ℝ) (hf : ∀ v, f v ≤ 1) (hsupp : ∀ v, v ∉ E → f v = 0) :
@@ -43,7 +46,7 @@
   refine ENNReal.toReal_mono ?_ (FrobeniusDensity.tailSum_le K hs)
   exact (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top tailConst_lt_top).ne
 
-variable {L : Type} [Field L] [NumberField L] [Algebra K L]
+variable {L : Type audit_v} [Field L] [NumberField L] [Algebra K L]
 
 theorem main (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
@@ -112,7 +115,7 @@
 
 open NumberField in
 theorem solution
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
--- P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
+++ P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
@@ -13,7 +16,7 @@
 
 set_option linter.unusedSectionVars false
 
-variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+variable {K : Type audit_u} {L : Type audit_v} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
 
 theorem under_int_eq_span_of_natCast_mem {p : ℕ} (hp : p.Prime) (Q : Ideal (𝓞 L)) (hQ : Q ≠ ⊤)
     (hpQ : (p : 𝓞 L) ∈ Q) : Q.under ℤ = Ideal.span {(p : ℤ)} := by
@@ -132,7 +135,7 @@
 
 open NumberField in
 theorem solution
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
--- P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
+++ P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
@@ -156,7 +159,7 @@
 
 section Crossing
 
-variable (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
+variable (K : Type audit_u) (L : Type audit_v) (L' : Type audit_w) [Field K] [NumberField K] [Field L] [NumberField L]
   [Field L'] [NumberField L'] [Algebra K L] [Algebra L L'] [Algebra K L'] [IsScalarTower K L L']
   [IsGalois K L] [IsGalois K L'] (q : ℕ) [hq : Fact q.Prime] [IsCyclotomicExtension {q} L L']
 
@@ -194,7 +197,7 @@
   left_inv g := by ext; rfl
   right_inv gL := by ext; rfl
 
-theorem crossing (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] [Algebra K L']
+theorem crossing (L' : Type audit_w) [Field L'] [NumberField L'] [Algebra L L'] [Algebra K L']
     [IsScalarTower K L L'] [IsGalois K L'] [IsCyclotomicExtension {q} L L'] (σ : L ≃ₐ[K] L)
     (hqmod : orderOf σ * (Module.finrank ℚ L).factorial ∣ q - 1) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
@@ -376,7 +379,7 @@
 
 section Assembly
 
-variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+variable (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
   [IsGalois K L]
 
 theorem isGalois_cyclotomicField (q : ℕ) [NeZero q] : IsGalois K (CyclotomicField q L) := by
@@ -428,7 +431,7 @@
 p2m_reactivate "P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.P2mChebotarevCrossing"
 
 open NumberField in
-theorem solution (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+theorem solution (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
       IsArithFrobAt ℤ σ P :=
--- P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
+++ P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
@@ -3,6 +3,9 @@
 import Mathlib
 import Definitions.Def_LanglandsTunnell_NormClass
 import P2M.Util
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
 
 set_option autoImplicit false
@@ -13,7 +16,7 @@
 
 set_option linter.unusedSectionVars false
 
-variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+variable {K : Type audit_u} {L : Type audit_v} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
 
 theorem algEquiv_eq_of_apply_eq (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L}
     (hζ : IsPrimitiveRoot ζ m) {σ τ : L ≃ₐ[K] L} (h : σ ζ = τ ζ) : σ = τ := by
@@ -226,7 +229,7 @@
 
 open NumberField in
 theorem solution
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
     (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
     (h1 : (Ideal.absNorm v : ZMod m) = 1) :
--- Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean
+++ Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean
@@ -2,6 +2,9 @@
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_idealSum_ne_top
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 theorem FrobeniusDensity.idealSum_ne_top
-    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
+    (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
     FrobeniusDensity.idealSum K s ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution
--- Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
+++ Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
@@ -2,8 +2,11 @@
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 open Filter Topology Asymptotics
 theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
-    (K : Type*) [Field K] [NumberField K] :
+    (K : Type audit_u) [Field K] [NumberField K] :
     (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
       =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution
--- Theorems/Thm_FrobeniusDensity_tailSum_le.lean
+++ Theorems/Thm_FrobeniusDensity_tailSum_le.lean
@@ -3,9 +3,12 @@
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_tailSum_le
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 open NumberField
 open scoped ENNReal
 
 theorem FrobeniusDensity.tailSum_le
-    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
+    (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
     FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tailSum_le.solution
--- Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
+++ Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
@@ -3,8 +3,11 @@
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 open NumberField
 theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
-    (K : Type*) [Field K] [NumberField K] :
+    (K : Type audit_u) [Field K] [NumberField K] :
     Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
       (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution
--- Theorems/Thm_M4aTorus_completedRayL_fe.lean
+++ Theorems/Thm_M4aTorus_completedRayL_fe.lean
@@ -2,11 +2,14 @@
 import Definitions.Def_NumberField_RayCharacterData
 import P2M.Util
 import P2M.Sol.S_M4aTorus_completedRayL_fe
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 set_option autoImplicit false
 noncomputable section
 open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors
 theorem M4aTorus.completedRayL_fe
-    (K : Type) [Field K] [NumberField K]
+    (K : Type audit_u) [Field K] [NumberField K]
     (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
     (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ F G : ℂ → ℂ,
--- Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
+++ Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 
 set_option autoImplicit false
 
@@ -9,6 +12,6 @@
 open scoped Classical in
 
 theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
-    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
+    (K : Type audit_u) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
     SignType.sign (Algebra.norm ℚ x) =
       ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution
--- Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
+++ Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
@@ -3,6 +3,9 @@
 import Definitions.Def_NumberField_RayCharacterData
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
@@ -12,7 +15,7 @@
 open scoped nonZeroDivisors
 
 theorem NumberField.exists_continuousOn_exp_eq_rayClassLSeries
-    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
+    (K : Type audit_u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
     ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
       (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
--- Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
+++ Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
@@ -4,12 +4,15 @@
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one
 
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
+
 set_option autoImplicit false
 
 open NumberField NumberField.InfinitePlace Deep.NTSupply
 
 theorem NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one
-    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
+    (K : Type audit_u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
     (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
--- Theorems/Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
@@ -9,7 +12,7 @@
 open NumberField
 
 theorem NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (C : ℝ) :
     ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
--- Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
@@ -9,7 +12,7 @@
 open NumberField
 
 theorem NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
--- Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
@@ -9,7 +12,7 @@
 open NumberField
 
 theorem NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
--- Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
+++ Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
@@ -9,7 +12,7 @@
 open NumberField
 
 theorem NumberField.exists_prime_isArithFrobAt_of_isGalois
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
       IsArithFrobAt ℤ σ P := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.solution
--- Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
+++ Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
@@ -1,6 +1,9 @@
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
+
+/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
+universe audit_u audit_v audit_w
 attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup
 
 set_option autoImplicit false
@@ -8,7 +11,7 @@
 open NumberField
 
 theorem NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
-    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
+    (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
     (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
     (h1 : (Ideal.absNorm v : ZMod m) = 1) :
```

## Original preparation script

The original experiment used the following script. For a clean reproduction use the procedure in reproduce.md; the historical script assumes its named private input tree already exists.

```python
from pathlib import Path
import re, shutil, difflib
base=Path('.private/drafts/chebotarev-patched'); dest=Path('.private/drafts/chebotarev-universes')
shutil.copytree(base,dest,dirs_exist_ok=True)
diff=[]; changes=[]
for p in sorted(dest.rglob('*.lean')):
    s=(base/p.relative_to(dest)).read_text()
    t=re.sub(r': Type(?=[)}])', ': Type*',s)
    for op,cl in [('(',')'),('{','}')]:
        t=t.replace(op+"K L L' : Type*"+cl,op+'K : Type audit_u'+cl+' '+op+'L : Type audit_v'+cl+' '+op+"L' : Type audit_w"+cl)
        t=t.replace(op+'K L : Type*'+cl,op+'K : Type audit_u'+cl+' '+op+'L : Type audit_v'+cl)
        t=t.replace(op+'K : Type*'+cl,op+'K : Type audit_u'+cl)
        t=t.replace(op+'L : Type*'+cl,op+'L : Type audit_v'+cl)
        t=t.replace(op+"L' : Type*"+cl,op+"L' : Type audit_w"+cl)
    if p.name == 'S_M4aTorus_completedRayL_fe.lean':
        # These existential witnesses are ClassGroup (RingOfIntegers K).
        # Their universe must be K's, not a fresh universally quantified level.
        t=t.replace('∃ (ι : Type*)', '∃ (ι : Type audit_u)')
    if t!=s:
        lines=t.splitlines(True); last=max(i for i,l in enumerate(lines) if l.startswith('import '))
        lines.insert(last+1,'\n/- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/\nuniverse audit_u audit_v audit_w\n')
        t=''.join(lines);p.write_text(t)
        md=p.with_suffix('.md');md.write_text(md.read_text()+'\nWorker 159 changed bare carrier universes to polymorphic binders and gave K, L and L\' independent named universes. This is an unaccepted feasibility experiment; see universes.patch.\n')
        diff.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile=str(p.relative_to(dest)),tofile=str(p.relative_to(dest))))
        changes.append(str(p.relative_to(dest)))
Path('.private/notes/chebotarev/universes.patch').write_text(''.join(diff))
Path('.private/notes/chebotarev/universes-files.txt').write_text('\n'.join(changes)+'\n')
print(f'Prepared universe experiment with {len(changes)} modified files.')
```
