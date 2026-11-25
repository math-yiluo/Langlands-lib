# Edits to NYLL fbd320cd for the Library's pin

Evidence for [the audit note](../nyll-global-cft-audit.md), section 4. This is the complete unified diff from the files of NYLL ClassFieldTheory at commit `fbd320cd8b1b06487c58227e92eb135794267709` (registered source `external-lean-reuse-snapshots-2026-10-21`, folder `n-yamaguchi-0729--ClassFieldTheory/source`) to the adapted copy that compiles on the Library's pin (Lean `v4.34.0`, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). It changes 14 files in 22 hunks. Every other file of the 957-module closure is byte-identical to the snapshot.

The diff has 249 lines; its SHA-256 is `2d734a1499b59ba94d1b84089ce536500251ef38e001086d1676f7919faa6150`. Paths are relative to the repository root.

```diff
--- a/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/MaximalUnramifiedSymbol.lean
+++ b/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/MaximalUnramifiedSymbol.lean
@@ -140,7 +140,7 @@
   rw [finiteUnramifiedRestriction, MonoidHom.comp_apply,
     maximalUnramifiedRestriction_frobenius]
   apply L.extensionQuotientMulEquiv.injective
-  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
+  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
     MulEquiv.apply_symm_apply]
   exact
     L.toGaloisSubextension.extensionQuotientMulEquiv.apply_symm_apply
--- a/Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/IntegerRingComparison.lean
+++ b/Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/IntegerRingComparison.lean
@@ -95,7 +95,7 @@
     (𝓞 K ⧸ v.asIdeal) ≃+*
       IsLocalRing.ResidueField (v.valuationSubringAtPrime K) :=
   (IsLocalization.AtPrime.equivQuotMaximalIdeal
-    v.asIdeal (v.valuationSubringAtPrime K)).toRingEquiv
+    v.asIdeal (v.valuationSubringAtPrime K))
 
 /-- The residue field at a finite prime is canonically the residue field of
 its normalized absolute-value completion. -/
--- a/Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormProperties.lean
+++ b/Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/NormProperties.lean
@@ -44,7 +44,7 @@
   simp only [Units.coe_map, Units.coe_prod]
   convert
     (_root_.Algebra.norm_eq_prod_automorphisms K (x : L))
-    using 1; rfl
+    using 1 <;> rfl
 
 omit [NumberField L] in
 /-- On the diagonal copy of `Lˣ`, after extending the norm
--- a/Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean
+++ b/Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean
@@ -58,7 +58,7 @@
     (A : Rep ℤ G) (wp : A ⟶ A) (K L : ClosedSubgroup G) :
     AddSubgroup A.V :=
   (ambientFixedAddSubgroup A L).map
-      (AddMonoidHom.ofClass wp.hom) ⊓
+      (AddMonoidHomClass.toAddMonoidHom wp.hom) ⊓
     ambientFixedAddSubgroup A K
 
 /-- The radical set `wp⁻¹(Delta)` in the additive abstract model. -/
@@ -66,7 +66,7 @@
     (A : Rep ℤ G) (wp : A ⟶ A) (K L : ClosedSubgroup G) :
     AddSubgroup A.V :=
   (kummerDeltaAddSubgroup A wp K L).comap
-    (AddMonoidHom.ofClass wp.hom)
+    (AddMonoidHomClass.toAddMonoidHom wp.hom)
 
 /-- The Kummer radical consists of fixed elements annihilated by the Kummer exponent. -/
 @[simp]
@@ -84,7 +84,7 @@
     (hLK : L.toSubgroup ≤ K.toSubgroup)
     (xi : A.V)
     (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
-    (hker : AddMonoidHom.ker (AddMonoidHom.ofClass wp.hom) ≤
+    (hker : AddMonoidHom.ker (AddMonoidHomClass.toAddMonoidHom wp.hom) ≤
       AddSubgroup.zmultiples xi)
     {a : A.V} (ha : a ∈ kummerRadicalAddSubgroup A wp K L)
     (l : L.toSubgroup) :
@@ -92,12 +92,12 @@
   have haDelta : wp.hom a ∈ kummerDeltaAddSubgroup A wp K L := ha
   have haImage : wp.hom a ∈
       (ambientFixedAddSubgroup A L).map
-        (AddMonoidHom.ofClass wp.hom) :=
+        (AddMonoidHomClass.toAddMonoidHom wp.hom) :=
     haDelta.1
   obtain ⟨b, hb_fixed, hba⟩ := haImage
   have hba' : wp.hom b = wp.hom a := hba
   have hd_ker : a - b ∈
-      AddMonoidHom.ker (AddMonoidHom.ofClass wp.hom) := by
+      AddMonoidHom.ker (AddMonoidHomClass.toAddMonoidHom wp.hom) := by
     rw [AddMonoidHom.mem_ker]
     change wp.hom (a - b) = 0
     rw [map_sub, ← hba', sub_self]
@@ -132,7 +132,7 @@
     (hxi_order : addOrderOf xi = (n : ℕ))
     (hxi_kernel : wp.hom xi = 0)
     (hxi_fixed : ∀ k : K.toSubgroup, A.ρ k.1 xi = xi)
-    (hker : AddMonoidHom.ker (AddMonoidHom.ofClass wp.hom) ≤
+    (hker : AddMonoidHom.ker (AddMonoidHomClass.toAddMonoidHom wp.hom) ≤
       AddSubgroup.zmultiples xi)
     (hexponent :
       ∀ q : K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK,
--- a/Nyll/ValuedFieldTheory/LocalField/Analytic/ContinuousFieldUnitLog.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/Analytic/ContinuousFieldUnitLog.lean
@@ -119,7 +119,7 @@
   intro γ _
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   obtain ⟨N₀, hN₀γ⟩ :=
     WithZero.exists_exp_neg_natCast_lt γ'.ne_zero
   obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ,
--- a/Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/ExpConvergence.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/ExpConvergence.lean
@@ -104,7 +104,7 @@
   rcases hs with ⟨γ, hγs⟩
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
   have hterm :=
     eventually_le_ofWithZeroValuation_val_exp_term_of_one_lt
@@ -291,7 +291,7 @@
   rcases hs with ⟨γ, hγs⟩
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
   have hterm :=
     eventually_le_ofWithZeroValuation_val_exp_term_scaled_of_threshold
--- a/Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/SeriesTerms.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/SeriesTerms.lean
@@ -766,7 +766,7 @@
   rcases hs with ⟨γ, hγs⟩
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
   have hterm :=
     eventually_le_ofWithZeroValuation_val_log_term_of_pos
@@ -811,7 +811,7 @@
   rcases hs with ⟨γ, hγs⟩
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
   have hterm :=
     eventually_le_ofWithZeroValuation_val_log_term_of_pos
@@ -1051,7 +1051,7 @@
   rcases hs with ⟨γ, hγs⟩
   let γ' : (WithZero (Multiplicative ℤ))ˣ :=
     Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
-      (f := (v : K →*₀ WithZero (Multiplicative ℤ)))) γ
+      (f := MonoidWithZeroHom.ofClass v)) γ
   rcases WithZero.exists_exp_neg_natCast_lt γ'.ne_zero with ⟨N, hNγ⟩
   have hterm :=
     eventually_le_ofWithZeroValuation_val_log_term_scaled_of_pos
--- a/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CompleteRangeRestriction.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CompleteRangeRestriction.lean
@@ -178,7 +178,6 @@
           (MonoidWithZeroHom.ofClass F.valuation) :=
       MonoidWithZeroHom.mem_valueGroup
         (MonoidWithZeroHom.ofClass F.valuation) ⟨x, hx⟩
-    rw [_root_.Valuation.ofClass_eq_toMonoidWithZeroHom] at hηΓ_mem
     rw [← _root_.Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
       F.valuation, Subgroup.mem_zpowers_iff] at hηΓ_mem
     rcases hηΓ_mem with ⟨z, hz⟩
--- a/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CyclicValueGroup.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/CyclicValueGroup.lean
@@ -125,12 +125,12 @@
     units_isCyclic_mulArchimedean Gamma
   haveI :
       MulArchimedean
-        v.ValueGroup₀ :=
+        (MonoidWithZeroHom.ofClass v).ValueGroup₀ :=
     MulArchimedean.comap
       (MonoidWithZeroHom.ValueGroup₀.embedding
-        (f := (v : R →*₀ Gamma))).toMonoidHom
+        (f := MonoidWithZeroHom.ofClass v)).toMonoidHom
       (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
-        (f := (v : R →*₀ Gamma)))
+        (f := MonoidWithZeroHom.ofClass v))
   exact
     Classical.choice
       ((_root_.Valuation.nonempty_rankOne_iff_mulArchimedean
--- a/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/RangeRestrictedTopology.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/RangeRestrictedTopology.lean
@@ -179,11 +179,10 @@
     change
       F.valuation ((z : K) - (b : K)) <
         ((MonoidWithZeroHom.ValueGroup₀.embedding
-            (f := ((Valued.v :
+            (f := MonoidWithZeroHom.ofClass (Valued.v :
                 _root_.Valuation K
                   (MonoidHom.mrange
-                    F.valuation.toMonoidWithZeroHom)) :
-                K →*₀ MonoidHom.mrange F.valuation.toMonoidWithZeroHom))
+                    F.valuation.toMonoidWithZeroHom)))
             (↑gamma) :
           MonoidHom.mrange F.valuation.toMonoidWithZeroHom) : F.ValueGroup)
     simpa [gamma'] using hlt
--- a/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/UniformizerIntegerValuation.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/UniformizerIntegerValuation.lean
@@ -75,10 +75,10 @@
   have hxmem :
       (fieldUnitValueUnit F) x ∈
         MonoidWithZeroHom.valueGroup
-          (F.valuation : K →*₀ F.ValueGroup) := by
+          (MonoidWithZeroHom.ofClass F.valuation) := by
     exact
       MonoidWithZeroHom.mem_valueGroup
-        (F.valuation : K →*₀ F.ValueGroup)
+        (MonoidWithZeroHom.ofClass F.valuation)
         (show (((fieldUnitValueUnit F) x : F.ValueGroup)) ∈
             Set.range F.valuation from
           ⟨(x : K), by simp [fieldUnitValueUnit]⟩)
--- a/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormalizedIntegerValuation.lean
+++ b/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormalizedIntegerValuation.lean
@@ -36,7 +36,8 @@
 noncomputable def localIntegerValuation :
     _root_.Valuation K (WithZero (Multiplicative ℤ)) :=
   _root_.Valuation.map
-    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
+    (MonoidWithZeroHom.ofClass (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K))
+    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone
     (ValuativeRel.valuation K)
 
 /-- The integer-valued valuation applies the canonical value-group isomorphism. -/
@@ -134,7 +135,8 @@
     ValuativeRel.valuation_surjective
       ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm gamma)
   refine ⟨x, ?_⟩
-  simp [localIntegerValuation, hx]
+  rw [localIntegerValuation_apply, hx]
+  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).apply_symm_apply gamma
 
 /-- Identity on field elements gives the valuation-ring equivalence attached
 to the normalization of the value group. -/
--- a/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean
+++ b/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/HenselianFinite.lean
@@ -66,7 +66,7 @@
   rw [Ideal.jacobson, le_sInf_iff]
   rintro Q ⟨-, hQmax⟩
   by_contra hle
-  rw [IsConcreteLE.le_iff] at hle
+  change ¬ (∀ x, x ∈ I.map (algebraMap R S) → x ∈ Q) at hle
   push Not at hle
   rcases hle with ⟨x, hxI, hxQ⟩
   let : Q.IsMaximal := hQmax
--- a/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean
+++ b/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean
@@ -95,7 +95,7 @@
       ⟨t, ht, hts⟩
     rcases (Valued.hasBasis_nhds_zero K Gamma).mem_iff.mp ht with
       ⟨gamma, _hgamma, hgamma_t⟩
-    have : MulArchimedean val.ValueGroup₀ :=
+    let : MulArchimedean (MonoidWithZeroHom.ofClass val).ValueGroup₀ :=
       (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt val).symm.mulArchimedean
     have hpi_restrict : val.restrict (pi : K) < 1 :=
       val.restrict_lt_one_iff.mpr hpi.val_lt_one
```
