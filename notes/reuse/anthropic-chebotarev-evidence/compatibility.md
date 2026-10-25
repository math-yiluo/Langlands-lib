# Exact compatibility patch

Apply this diff after the preceding stage, with zero fuzz. It contains the actual modification notices. All edits are private feasibility work; no public mathematical port follows from this document.

```diff
--- Definitions/Def_NumberField_NormResidueCharacter.lean
+++ Definitions/Def_NumberField_NormResidueCharacter.lean
@@ -1,3 +1,5 @@
+/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.
+Copyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/
 import Mathlib
 import Definitions.Def_LanglandsTunnell_NormClass
 import Definitions.Def_NumberField_RayCharacterData
@@ -313,7 +315,8 @@
     have hφζ : φ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
       have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
       have h2 : ((φ • hζ.toInteger : 𝓞 L) : L) = φ ζ := rfl
-      simpa [h2, hζ.coe_toInteger] using h
+      change φ ζ = ζ ^ Ideal.absNorm v.asIdeal at h
+      exact h
     have hspec := hζ.autToPow_spec K φ
     rw [hφζ] at hspec
     have hmod : ((hζ.autToPow K φ : ZMod m)).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
--- Definitions/Def_FrobeniusDensity_BadPrimes.lean
+++ Definitions/Def_FrobeniusDensity_BadPrimes.lean
@@ -1,3 +1,5 @@
+/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.
+Copyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/
 import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
 import Mathlib.RingTheory.DedekindDomain.Factorization
 import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
@@ -29,8 +31,8 @@
   refine Set.Finite.of_finite_image ?_ hinj
   refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
   rintro J ⟨v, hv, rfl⟩
-  simpa [Multiset.mem_toFinset] using
-    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩
+  exact Multiset.mem_toFinset.mpr
+    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩)
 
 variable (L : Type*) [Field L] [NumberField L]
 
--- P2M/Sol/S_M4aTorus_completedRayL_fe.lean
+++ P2M/Sol/S_M4aTorus_completedRayL_fe.lean
@@ -1,3 +1,5 @@
+/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.
+Copyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/
 import Definitions.Def_NumberField_CompletedRayL
 import Definitions.Def_NumberField_RayCharacterData
 import Mathlib.NumberTheory.NumberField.ClassNumber
@@ -3392,7 +3394,7 @@
 private theorem norm_polyS_le (he : Orthonormal ℝ e) (S : Finset σ) (x : E) : ‖polyS e S x‖ ≤ ‖x‖ ^ S.card := by
   unfold polyS
   rw [norm_prod, ← Finset.prod_const]
-  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun u _ => ?_
+  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun u _ => ?_
   rw [Complex.norm_real, Real.norm_eq_abs]
   calc |⟪e u, x⟫_ℝ| ≤ ‖e u‖ * ‖x‖ := abs_real_inner_le_norm _ _
     _ = ‖x‖ := by rw [he.norm_eq_one u, one_mul]
@@ -4324,7 +4326,7 @@
   have hPle : (∏ v ∈ S, Real.sqrt c * v.1 (x : K))
       ≤ (Real.sqrt c * ‖dilEmbed K (x : K)‖) ^ k := by
     rw [hkdef, ← Finset.prod_const]
-    refine Finset.prod_le_prod (fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _))
+    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _))
       (fun v _ => ?_)
     refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
     have h1 : v.1 (x : K) = |(dilEmbed K (x : K)).fst v| := by
@@ -5617,7 +5619,7 @@
 
 omit [NumberField K] in
 private theorem measurable_inv_realSpace : Measurable (Inv.inv : realSpace K → realSpace K) :=
-  measurable_pi_lambda _ fun w => (measurable_pi_apply w).inv
+  measurable_pi_iff.mpr fun w => (measurable_pi_apply w).inv
 
 private theorem lintegral_comp_inv_torusHaar {g : realSpace K → ℝ≥0∞} (hg : Measurable g) :
     ∫⁻ t, g t⁻¹ ∂(torusHaar K) = ∫⁻ t, g t ∂(torusHaar K) := by
@@ -6477,7 +6479,7 @@
   obtain ⟨w₁, -, hw₁⟩ := Finset.exists_min_image Finset.univ βw Finset.univ_nonempty
   refine ⟨βw w₁, hβw w₁, fun x hx w => ?_⟩
   have hle : βw w ≤ ∏ i : {w : InfinitePlace K // w ≠ w₀}, A w i ^ x i.1 := by
-    refine Finset.prod_le_prod (fun i _ => (lt_min one_pos (Real.rpow_pos_of_pos (hA w i) _)).le)
+    refine Finset.prod_le_prod₀ (fun i _ => (lt_min one_pos (Real.rpow_pos_of_pos (hA w i) _)).le)
       fun i _ => ?_
     have hxi : x i.1 ∈ Set.Ico (0 : ℝ) 2 := by
       have h := (Set.mem_univ_pi.mp hx) i.1
@@ -6664,7 +6666,7 @@
     have hF : P * W * ∏ v ∈ S, Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2)))
         ≤ cS := by
       rw [hPdef, hWdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, hcS, ← Finset.prod_const]
-      refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
+      refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => ?_
       have := sqrt_mul_mul_exp_neg_le (r := (v.1 : InfinitePlace K) Y) (htpos v.1).le hπκ
       calc (v.1 : InfinitePlace K) Y * Real.sqrt (t v.1)
             * Real.exp (-(π * κ' * (t v.1 * ((v.1 : InfinitePlace K) Y) ^ 2)))
@@ -9330,7 +9332,7 @@
     exact congrArg (‖·‖ₑ) (rayOrbitKernel_unit_mul K 𝔣 χ S 𝔞 c s p.2 t (fracIdealGen K 𝔞 p.1))
   refine Summable.of_norm_bounded (ENNReal.summable_toReal hfin') fun p => ?_
   exact (toReal_enorm _).symm.trans_le (ENNReal.toReal_mono
-    (ne_top_of_le_ne_top hfin' (ENNReal.le_tsum p)) (enorm_integral_le_lintegral_enorm _))
+    (ENNReal.lt_top_of_tsum_ne_top hfin' p).ne (enorm_integral_le_lintegral_enorm _))
 
 private theorem rayFoldMellin_unfold (h𝔣 : 𝔣 ≠ ⊥) (c : ℝ) (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
     rayFoldMellin K 𝔣 χ S 𝔞 c s
--- P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
+++ P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean
@@ -1,3 +1,5 @@
+/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.
+Copyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/
 import Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test
 import Theorems.Thm_FrobeniusDensity_idealSum_ne_top
 import Definitions.Def_FrobeniusDensity_PrimeSums
@@ -254,13 +256,13 @@
 
 lemma one_le_idealSum (s : ℝ) : 1 ≤ idealSum K s := by
   have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ idealSum K s :=
-    ENNReal.le_tsum (⟨⊤, by simp⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})
+    ENNReal.le_tsum (f := fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => normRpow K s I.1) (⟨⊤, by simp⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})
   rwa [normRpow_top] at h
 
 lemma one_le_factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
     1 ≤ factoredSum K T s := by
   have h : normRpow K s (⊤ : Ideal (𝓞 K)) ≤ factoredSum K T s :=
-    ENNReal.le_tsum (⟨⊤, isFactoredBy_top T⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})
+    ENNReal.le_tsum (f := fun I : {I : Ideal (𝓞 K) // IsFactoredBy T I} => normRpow K s I.1) (⟨⊤, isFactoredBy_top T⟩ : {I : Ideal (𝓞 K) // IsFactoredBy T I})
   rwa [normRpow_top] at h
 
 lemma factoredSum_toReal_pos {T : Finset (HeightOneSpectrum (𝓞 K))} {s : ℝ}
--- P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
+++ P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean
@@ -1,3 +1,5 @@
+/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.
+Copyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/
 import Mathlib
 import Definitions.Def_LanglandsTunnell_NormClass
 import P2M.Util
@@ -148,7 +150,7 @@
           rw [← smul_pow', hζ'.pow_eq_one, smul_one]
         have hfixL : (σ : L ≃ₐ[K] L) ζ = ζ := by
           have h := congrArg (fun x : 𝓞 L => (x : L)) hfix
-          simp [hζ'def, hζ.coe_toInteger] at h
+          change (σ : L ≃ₐ[K] L) ζ = ζ at h
           exact h
         exact algEquiv_eq_of_apply_eq m hζ (by rw [hfixL, AlgEquiv.one_apply])
       exact Subtype.ext ((hmem a).trans (hmem b).symm)
@@ -162,7 +164,7 @@
         exact h
       have hφζ : φ ζ = ζ := by
         have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
-        simp [hζ'def, hζ.coe_toInteger] at h
+        change φ ζ = ζ at h
         exact h
       have hφ1 : φ = 1 := algEquiv_eq_of_apply_eq m hζ (by rw [hφζ, AlgEquiv.one_apply])
       have hpow : ∀ y : 𝓞 L ⧸ w, y ^ q = y := by
```

## Original preparation script

The original experiment used the following script. For a clean reproduction use the procedure in reproduce.md; the historical script assumes its named private input tree already exists.

```python
from pathlib import Path
import shutil,json,difflib
base=Path('.private/drafts/chebotarev-baseline'); dest=Path('.private/drafts/chebotarev-patched')
shutil.copytree(base,dest,dirs_exist_ok=True)
def patch(name,a,b):
 p=dest/name;s=p.read_text();assert a in s,name;p.write_text(s.replace(a,b))
patch('Definitions/Def_FrobeniusDensity_BadPrimes.lean','  simpa [Multiset.mem_toFinset] using\n    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩','  exact Multiset.mem_toFinset.mpr\n    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩)')
patch('Definitions/Def_NumberField_NormResidueCharacter.lean','      simpa [h2, hζ.coe_toInteger] using h','      change φ ζ = ζ ^ Ideal.absNorm v.asIdeal at h\n      exact h')
f='P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean'
patch(f,'          simp [hζ\'def, hζ.coe_toInteger] at h','          change (σ : L ≃ₐ[K] L) ζ = ζ at h')
patch(f,'        simp [hζ\'def, hζ.coe_toInteger] at h','        change φ ζ = ζ at h')
f='P2M/Sol/S_M4aTorus_completedRayL_fe.lean'
patch(f,'Finset.prod_le_prod (','Finset.prod_le_prod₀ (')
patch(f,'measurable_pi_lambda _ fun w => (measurable_pi_apply w).inv','measurable_pi_iff.mpr fun w => (measurable_pi_apply w).inv')
patch(f,"(ne_top_of_le_ne_top hfin' (ENNReal.le_tsum p))",
  "(ENNReal.lt_top_of_tsum_ne_top hfin' p).ne")
f='P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean'
patch(f,'ENNReal.le_tsum (⟨⊤, by simp⟩', 'ENNReal.le_tsum (f := fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => normRpow K s I.1) (⟨⊤, by simp⟩')
patch(f,'ENNReal.le_tsum (⟨⊤, isFactoredBy_top T⟩', 'ENNReal.le_tsum (f := fun I : {I : Ideal (𝓞 K) // IsFactoredBy T I} => normRpow K s I.1) (⟨⊤, isFactoredBy_top T⟩')
patches=[]
for p in dest.rglob('*.lean'):
 orig=(base/p.relative_to(dest)).read_text();new=p.read_text()
 if orig!=new:
  new='/- Modified by Worker 159, 25 October 2026: Mathlib 4.34 compatibility probe.\nCopyright 2026 Anthropic, PBC. Apache-2.0; retained LICENSE/NOTICE/ATTRIBUTION apply. -/\n'+new
  p.write_text(new)
  p.with_suffix('.md').write_text(p.with_suffix('.md').read_text().replace('copied this file unchanged','adapted this file with the exact compatibility edits in `.private/notes/chebotarev/compatibility.patch`; the original has been retained unchanged in chebotarev-baseline'))
  patches+=difflib.unified_diff(orig.splitlines(True),new.splitlines(True),fromfile=str(p.relative_to(dest)),tofile=str(p.relative_to(dest)))
Path('.private/notes/chebotarev/compatibility.patch').write_text(''.join(patches))
print('Prepared patched private closure; baseline unchanged.')
```
