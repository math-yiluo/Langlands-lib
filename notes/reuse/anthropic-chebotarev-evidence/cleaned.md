# Exact cleaned patch

Apply this diff after the preceding stage, with zero fuzz. It contains the actual modification notices. All edits are private feasibility work; no public mathematical port follows from this document.

```diff
--- P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
+++ P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Definitions.Def_NumberField_PrimeNormSums
@@ -8,7 +9,6 @@
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
-attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
 
 set_option autoImplicit false
 
--- P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
+++ P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
 import P2M.Util
@@ -5,8 +6,6 @@
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
--- P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
+++ P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
 import P2M.Util
@@ -5,8 +6,6 @@
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
 namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 set_option linter.unusedSectionVars false
--- Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean
+++ Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
@@ -8,4 +9,5 @@
     {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
     (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
     (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
-    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution
+    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by
+  apply @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution <;> assumption
--- Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean
+++ Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_idealSum_ne_top
@@ -7,4 +8,5 @@
 
 theorem FrobeniusDensity.idealSum_ne_top
     (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
-    FrobeniusDensity.idealSum K s ≠ ⊤ := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution
+    FrobeniusDensity.idealSum K s ≠ ⊤ := by
+  apply @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution <;> assumption
--- Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
+++ Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import P2M.Util
 import P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO
@@ -9,4 +10,5 @@
 theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
     (K : Type audit_u) [Field K] [NumberField K] :
     (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
-      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution
+      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
+  apply @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution <;> assumption
--- Theorems/Thm_FrobeniusDensity_tailSum_le.lean
+++ Theorems/Thm_FrobeniusDensity_tailSum_le.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import P2M.Util
@@ -11,4 +12,5 @@
 
 theorem FrobeniusDensity.tailSum_le
     (K : Type audit_u) [Field K] [NumberField K] {s : ℝ} (hs : 1 ≤ s) :
-    FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tailSum_le.solution
+    FrobeniusDensity.tailSum K s ≤ (Module.finrank ℚ K : ℝ≥0∞) * FrobeniusDensity.tailConst := by
+  apply @_root_.P2MW.S_FrobeniusDensity_tailSum_le.solution <;> assumption
--- Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
+++ Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Definitions.Def_FrobeniusDensity_PrimeSums
 import Mathlib.NumberTheory.NumberField.DedekindZeta
 import P2M.Util
@@ -10,4 +11,5 @@
 theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
     (K : Type audit_u) [Field K] [NumberField K] :
     Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
-      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution
+      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
+  apply @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution <;> assumption
--- Theorems/Thm_M4aTorus_completedRayL_fe.lean
+++ Theorems/Thm_M4aTorus_completedRayL_fe.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Definitions.Def_NumberField_CompletedRayL
 import Definitions.Def_NumberField_RayCharacterData
 import P2M.Util
@@ -23,4 +24,5 @@
         ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
           F (1 - s) = (-Complex.I) ^ S.card *
             (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
-      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by p2m_exact_reverting @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution
+      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by
+  apply @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution <;> assumption
--- Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
+++ Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal
@@ -14,4 +15,5 @@
 theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
     (K : Type audit_u) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
     SignType.sign (Algebra.norm ℚ x) =
-      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution
+      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
+  apply @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution <;> assumption
--- Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
+++ Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Definitions.Def_NumberField_CompletedRayL
 import Definitions.Def_NumberField_RayCharacterData
@@ -6,8 +7,6 @@
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
@@ -25,4 +24,5 @@
       ∃ C : ℝ, ∀ s : ℝ, 1 < s →
         ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
             M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
-              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution
+              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
+  apply @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution <;> assumption
--- Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
+++ Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean
@@ -1,3 +1,4 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import Definitions.Def_NumberField_CompletedRayL
 import Definitions.Def_NumberField_RayCharacterData
@@ -16,4 +17,5 @@
     (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
     (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
     ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
-      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution
+      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by
+  apply @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution <;> assumption
--- Theorems/Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean
@@ -1,11 +1,10 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
@@ -18,4 +17,5 @@
     ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 1 < s → s < 1 + δ →
       C ≤ ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
         (if (Ideal.absNorm v.asIdeal : ZMod m) = ((hζ.autToPow K τ : (ZMod m)ˣ) : ZMod m)
-          then (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) else 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.solution
+          then (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) else 0) := by
+  apply @_root_.P2MW.S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.solution (m := m) <;> assumption
--- Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean
@@ -1,11 +1,10 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
@@ -16,4 +15,5 @@
     (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
-      ∃ v : Ideal (𝓞 K), v.IsMaximal ∧ Ideal.absNorm v = p ∧ τ ζ = ζ ^ p := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.solution
+      ∃ v : Ideal (𝓞 K), v.IsMaximal ∧ Ideal.absNorm v = p ∧ τ ζ = ζ ^ p := by
+  apply @_root_.P2MW.S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.solution (m := m) <;> assumption
--- Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
+++ Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean
@@ -1,11 +1,10 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
@@ -16,4 +15,5 @@
     [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
     (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
-      IsArithFrobAt ℤ τ P := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.solution
+      IsArithFrobAt ℤ τ P := by
+  apply @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.solution (m := m) <;> assumption
--- Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
+++ Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean
@@ -1,11 +1,10 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G
-attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec
 
 set_option autoImplicit false
 
@@ -15,4 +14,5 @@
     (K : Type audit_u) (L : Type audit_v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
     [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
     ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
-      IsArithFrobAt ℤ σ P := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.solution
+      IsArithFrobAt ℤ σ P := by
+  apply @_root_.P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.solution <;> assumption
--- Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
+++ Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
@@ -1,10 +1,10 @@
+/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/
 import Mathlib
 import P2M.Util
 import P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
 
 /- Worker 159: bounded universe-generalization experiment, 25 October 2026. -/
 universe audit_u audit_v audit_w
-attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup
 
 set_option autoImplicit false
 
@@ -16,4 +16,5 @@
     (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
     (h1 : (Ideal.absNorm v : ZMod m) = 1) :
     (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
-      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution
+      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by
+  apply @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution (m := m) <;> assumption
```

## Original preparation script

The original experiment used the following script. For a clean reproduction use the procedure in reproduce.md; the historical script assumes its named private input tree already exists.

```python
from pathlib import Path
import re,shutil,difflib
base=Path('.private/drafts/chebotarev-universes');dest=Path('.private/drafts/chebotarev-cleaned')
shutil.copytree(base,dest,dirs_exist_ok=True)
diff=[];changes=[]
for p in sorted(dest.rglob('*.lean')):
    if p.name=='Util.lean':continue
    s=(base/p.relative_to(dest)).read_text()
    t=re.sub(r'^attribute \[-(?:instance|simp)\].*\n','',s,flags=re.M)
    t=re.sub(r'by p2m_exact_reverting (@\S+)',r'by\n  apply \1 <;> assumption',t)
    if '(m : ℕ)' in t and 'Theorems' in p.parts:
        t=re.sub(r'(apply @\S+\.solution) <;>',r'\1 (m := m) <;>',t)
    if s!=t:
        t='/- Worker 159: remove global attribute resets and proof-wrapper calls; 25 October 2026. -/\n'+t
        p.write_text(t);md=p.with_suffix('.md');md.write_text(md.read_text()+'\nWorker 159 removed file-global instance/simp resets and replaced proof-wrapper calls with standard apply/assumption tactics. Namespace/alias utilities remain. See cleaned.patch for exact changes; this is a private feasibility experiment.\n')
        diff.extend(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile=str(p.relative_to(dest)),tofile=str(p.relative_to(dest))))
        changes.append(str(p.relative_to(dest)))
Path('.private/notes/chebotarev/cleaned.patch').write_text(''.join(diff))
print(f'Prepared clean experiment with {len(changes)} modified files.')
```
