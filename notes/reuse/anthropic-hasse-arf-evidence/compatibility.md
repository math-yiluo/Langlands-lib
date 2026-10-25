# Hasse–Arf evidence: exact compatibility patch

Supporting evidence for the [audit note](../anthropic-hasse-arf-audit.md). These records are development evidence, not mathematical acceptance.

<!-- evidence-file: patch01.diff -->

## patch01.diff

SHA256 of the exact UTF-8 block: `748e4e0934f045e540909f67c9786bf304ab6200704b1c126923c60e0ec46579`.

````diff
--- a/Definitions/Def_Compat_Mathlib430.lean
+++ b/Definitions/Def_Compat_Mathlib430.lean
@@ -1,3 +1,4 @@
+/- Adapted by Worker 25 for Lean 4.34.0 / Mathlib 5ed2965256430c3649e86755f9576b54eca72435. Original notices in LICENSE, NOTICE and ATTRIBUTION.md. -/
 /-
 Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
 release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
@@ -65,7 +66,7 @@
   have hg : Function.Injective (g • · : H → H) := by
     intro h₁ h₂
     simp
-  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply, hg]
+  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.mapDomain_apply_of_injective hg]
 
 end Group
 
--- a/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean
+++ b/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean
@@ -1,3 +1,4 @@
+/- Adapted by Worker 25 for Lean 4.34.0 / Mathlib 5ed2965256430c3649e86755f9576b54eca72435. Original notices in LICENSE, NOTICE and ATTRIBUTION.md. -/
 import Mathlib
 
 set_option autoImplicit false
@@ -8,8 +9,7 @@
 
 variable {M : Type*} [AddGroup M] {G : Type*} [Group G] [MulAction G M]
 
-theorem inertia_mono {I J : AddSubgroup M} (h : I ≤ J) : I.inertia G ≤ J.inertia G :=
-  fun _ hσ x => h (hσ x)
+-- Adapted by Worker 25: reuse the pinned Mathlib AddSubgroup.inertia_mono.
 
 end AddSubgroup
 
@@ -19,7 +19,7 @@
 
 theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
     I.inertia G ≤ J.inertia G :=
-  AddSubgroup.inertia_mono (Submodule.toAddSubgroup_mono h)
+  AddSubgroup.inertia_mono G (Submodule.toAddSubgroup_mono h)
 
 @[simp]
 theorem inertia_top : (⊤ : Ideal R).inertia G = ⊤ := by
````
