# Stacks sample 2: complete edits

Unified diff of the 30 files that were edited, against AxiomMath/Stacks commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, to compile the 318-module closure with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. The final check compiled it with 0 errors and 0 warnings. The diff has 95 added and 48 removed lines. Its SHA-256 as a patch file (the text between the fences, ending with a newline) is `ed02bb1fcb633a18433a9dd1ab51a491cff5a2f5541bf9d5fc2f057f18235c47`. Paths are relative to the repository root. The per-file hashes are in [stacks-sample2-manifest.md](stacks-sample2-manifest.md).

Part of the [audit of the étale-cohomology premises](../etale-premises-sheaf-libraries-audit.md#72-focused-compiles-on-the-librarys-pin). These are unreviewed development records.

```diff
--- a/StacksCore/Algebra/Homology/SpectralSequence/PageInfinity.lean
+++ b/StacksCore/Algebra/Homology/SpectralSequence/PageInfinity.lean
@@ -1,6 +1,6 @@
 module
 
-public import Mathlib.Order.Int.LeastGreatest
+public import Mathlib.Data.Int.LeastGreatest
 public import StacksCore.Algebra.Homology.SpectralSequence.EdgeStep
 
 /-!
--- a/StacksCore/CategoryTheory/Subobject/Limits.lean
+++ b/StacksCore/CategoryTheory/Subobject/Limits.lean
@@ -26,6 +26,49 @@
 
 variable {C : Type*} [Category* C]
 
+/-! ### Backport for the Library pin: three lemmas of mathlib#42759 used below
+(copied from Mathlib 56a0058, `Mathlib/CategoryTheory/Subobject/Limits.lean`) -/
+
+namespace Limits
+
+theorem imageSubobject_comp_of_strongEpi [HasStrongEpiMonoFactorisations C] {X Y X' : C}
+    (e : X' ⟶ X) (f : X ⟶ Y) [StrongEpi e] [Mono f] :
+    imageSubobject (e ≫ f) = imageSubobject f :=
+  Subobject.mk_eq_mk_of_comm (image.ι (e ≫ f)) (image.ι f)
+    ((image.isoStrongEpiMono e f rfl).symm ≪≫
+      (image.isoStrongEpiMono (𝟙 _) f (Category.id_comp _))) (by simp)
+
+end Limits
+
+namespace Subobject
+
+lemma exists_eq_imageSubobject [HasImages C] {X Y : C}
+    (f : X ⟶ Y) (X' : Subobject X) : («exists» f).obj X' = imageSubobject (X'.arrow ≫ f) := by
+  apply eq_of_comm ((existsIsoImage f X').trans (imageSubobjectIso (X'.arrow ≫ f)).symm)
+  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, imageSubobject_arrow']
+  exact ((Subobject.existsCompRepresentativeIso f).app X').hom.hom.w
+
+lemma exists_mk_eq_imageSubobject [HasImages C] {X Y : C}
+    {A : C} (g : A ⟶ X) [Mono g] (f : X ⟶ Y) :
+    («exists» f).obj (mk g) = imageSubobject (g ≫ f) := rfl
+
+/- Backport (Mathlib 56a0058, `Mathlib/CategoryTheory/Subobject/Lattice.lean`). -/
+theorem exists_pullback_eq_inf_of_mono [HasPullbacks C] [HasImages C] {X Y : C} (f : X ⟶ Y)
+    [Mono f] (Y' : Subobject Y) :
+    («exists» f).obj ((pullback f).obj Y') = Y' ⊓ mk f := by
+  rw [exists_iso_map]
+  change (map (MonoOver.mk f).arrow).obj ((pullback (MonoOver.mk f).arrow).obj Y') = _
+  rw [← inf_eq_map_pullback', inf_comm]
+  rfl
+
+/- Backport (Mathlib 56a0058, `Mathlib/CategoryTheory/Subobject/Limits.lean`). -/
+lemma pullback_kernelSubobject [HasZeroMorphisms C] {X Y W : C} (f : X ⟶ Y) [HasKernel f]
+    (h : W ⟶ X) [HasPullbacks C] [HasKernel (h ≫ f)] :
+    (Subobject.pullback h).obj (kernelSubobject f) = kernelSubobject (h ≫ f) := by
+  simpa only [kernelSubobject, comp_zero] using pullback_equalizer f 0 h
+
+end Subobject
+
 /-! ### Own lemmas -/
 
 namespace Subobject
--- a/StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ULiftUnit.lean
+++ b/StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ULiftUnit.lean
@@ -491,7 +491,7 @@
   (_root_.SheafOfModules.forget R).mono_of_mono_map
     (PresheafOfModules.mono_of_injective
       (f := ((moduleULift.{t, v} R).map φ).val)
-      (fun {X} _ _ h => ULift.ext (injective_app_of_mono φ X (congrArg ULift.down h))))
+      (fun {X} _ _ h => ULift.ext _ _ (injective_app_of_mono φ X (congrArg ULift.down h))))
 
 /-! ### Separatedness, and killing the local closure of a range -/
 
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/ExtAndYonedaExtensions.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/ExtAndYonedaExtensions.lean
@@ -6,7 +6,7 @@
 public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
 import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.Int.Interval
 public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
 import Mathlib.RingTheory.WittVector.IsPoly
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/ExtOneAndVanishing.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/ExtOneAndVanishing.lean
@@ -6,7 +6,7 @@
 public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
 import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.Int.Interval
 public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
 import Mathlib.RingTheory.WittVector.IsPoly
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/SplittingAndResolutions.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/SplittingAndResolutions.lean
@@ -6,7 +6,7 @@
 public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
 import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.Int.Interval
 public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
 import Mathlib.RingTheory.WittVector.IsPoly
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/YonedaClassMap.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic/YonedaClassMap.lean
@@ -7,7 +7,7 @@
 public import Mathlib.CategoryTheory.Abelian.Refinements
 import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.Int.Interval
 public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
 import Mathlib.RingTheory.WittVector.IsPoly
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/AdjointAndProducts.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/AdjointAndProducts.lean
@@ -21,7 +21,7 @@
 public import Mathlib.Combinatorics.Enumerative.DyckWord
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
 public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.NNRat.Floor
 public import Mathlib.Data.Nat.Choose.Multinomial
 public import Mathlib.Geometry.Euclidean.Altitude
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/InverseLimit.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/InverseLimit.lean
@@ -21,7 +21,7 @@
 public import Mathlib.Combinatorics.Enumerative.DyckWord
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
 public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.NNRat.Floor
 public import Mathlib.Data.Nat.Choose.Multinomial
 public import Mathlib.Geometry.Euclidean.Altitude
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/Locality.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/KInjective/Locality.lean
@@ -21,7 +21,7 @@
 public import Mathlib.Combinatorics.Enumerative.DyckWord
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
 public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.NNRat.Floor
 public import Mathlib.Data.Nat.Choose.Multinomial
 public import Mathlib.Geometry.Euclidean.Altitude
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/Products.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/Products.lean
@@ -7,7 +7,7 @@
 public import Mathlib.CategoryTheory.ExtremalEpi
 public import Mathlib.CategoryTheory.Localization.Adjunction
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 import StacksCore.Tactic.EgaSgaAttribute
 
 @[expose] public section
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/AcyclicResolutions.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/AcyclicResolutions.lean
@@ -12,7 +12,7 @@
 import Mathlib.CategoryTheory.Limits.Types.Filtered
 import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
 public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
-import Mathlib.Algebra.Order.Star.Int
+import Mathlib.Data.Int.Star
 import Mathlib.Tactic.ENatToNat
 public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
 public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/DeltaFunctor.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/DeltaFunctor.lean
@@ -13,7 +13,7 @@
 import Mathlib.CategoryTheory.Limits.Types.Filtered
 import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
 public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
-import Mathlib.Algebra.Order.Star.Int
+import Mathlib.Data.Int.Star
 import Mathlib.Tactic.ENatToNat
 public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
 public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
--- a/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/Exactness.lean
+++ b/StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/Exactness.lean
@@ -13,7 +13,7 @@
 import Mathlib.CategoryTheory.Limits.Types.Filtered
 import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
 public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
-import Mathlib.Algebra.Order.Star.Int
+import Mathlib.Data.Int.Star
 import Mathlib.Tactic.ENatToNat
 public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
 public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
--- a/StacksFrontier/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean
+++ b/StacksFrontier/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean
@@ -16,7 +16,7 @@
 public import Mathlib.Combinatorics.Enumerative.DyckWord
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
 public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.Data.NNRat.Floor
 public import Mathlib.Data.Nat.Choose.Multinomial
 public import Mathlib.Geometry.Euclidean.Altitude
--- a/StacksFrontier/Algebra/Homology/HomotopyCategory/Triangulated.lean
+++ b/StacksFrontier/Algebra/Homology/HomotopyCategory/Triangulated.lean
@@ -5,7 +5,7 @@
 public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
 public import Mathlib.CategoryTheory.Triangulated.Basic
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
 public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
 
--- a/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/BoundedAbove.lean
+++ b/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/BoundedAbove.lean
@@ -15,9 +15,9 @@
 public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
 import Mathlib.CategoryTheory.Monoidal.Mon
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
-public import Mathlib.Algebra.Order.Star.Int
-public import Mathlib.Order.SuccPred.Int
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.Star
+public import Mathlib.Data.Int.SuccPred
 import Mathlib.RingTheory.WittVector.IsPoly
 import Mathlib.Tactic.ReduceModChar
 public import Mathlib.Tactic.Ring.Basic
--- a/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/EpiResData.lean
+++ b/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/EpiResData.lean
@@ -15,9 +15,9 @@
 public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
 import Mathlib.CategoryTheory.Monoidal.Mon
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
-public import Mathlib.Algebra.Order.Star.Int
-public import Mathlib.Order.SuccPred.Int
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.Star
+public import Mathlib.Data.Int.SuccPred
 import Mathlib.RingTheory.WittVector.IsPoly
 import Mathlib.Tactic.ReduceModChar
 public import Mathlib.Tactic.Ring.Basic
--- a/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/HomotopyLift.lean
+++ b/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/HomotopyLift.lean
@@ -15,9 +15,9 @@
 public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
 import Mathlib.CategoryTheory.Monoidal.Mon
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
-public import Mathlib.Algebra.Order.Star.Int
-public import Mathlib.Order.SuccPred.Int
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.Star
+public import Mathlib.Data.Int.SuccPred
 import Mathlib.RingTheory.WittVector.IsPoly
 import Mathlib.Tactic.ReduceModChar
 public import Mathlib.Tactic.Ring.Basic
--- a/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/KProjective.lean
+++ b/StacksFrontier/Algebra/Homology/Resolution/ProjectiveResolution/KProjective.lean
@@ -15,9 +15,9 @@
 public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
 import Mathlib.CategoryTheory.Monoidal.Mon
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
-public import Mathlib.Algebra.Order.Star.Int
-public import Mathlib.Order.SuccPred.Int
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.Star
+public import Mathlib.Data.Int.SuccPred
 import Mathlib.RingTheory.WittVector.IsPoly
 import Mathlib.Tactic.ReduceModChar
 public import Mathlib.Tactic.Ring.Basic
--- a/StacksFrontier/AlgebraicGeometry/Topologies/EtaleDescentIntegral.lean
+++ b/StacksFrontier/AlgebraicGeometry/Topologies/EtaleDescentIntegral.lean
@@ -248,8 +248,8 @@
   let k : Y ⟶ pullback p p := pullback.lift f g hfg
   have hjk : j ≫ k = (j ≫ f) ≫ δ := by
     apply pullback.hom_ext
-    · simp [Category.assoc, k, δ, pullback.diagonal_fst]
-    · simp [Category.assoc, k, δ, h, pullback.diagonal_snd]
+    · simp only [Category.assoc, k, δ, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
+    · simp only [Category.assoc, k, δ, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, h]
   have hkRange : Set.range k ⊆ Set.range δ := by
     rintro z ⟨y, rfl⟩
     obtain ⟨y₀, hy₀⟩ := hj y
@@ -356,10 +356,12 @@
         pullback.fst Y.hom i ≫ f.left =
             ((Over.pullback i).map f).left ≫ pullback.fst X.hom i := by
           simp [Over.pullback_map_left]
+          exact (pullback.lift_fst _ _ _).symm
         _ = ((Over.pullback i).map g).left ≫ pullback.fst X.hom i := by
           rw [congrArg Over.Hom.left h]
         _ = pullback.fst Y.hom i ≫ g.left := by
           simp [Over.pullback_map_left]
+          exact pullback.lift_fst _ _ _
     exact hom_ext_of_surjective (pullback.fst Y.hom i) hj X.hom f.left g.left
       ((Over.w f).trans (Over.w g).symm) hrestrict
   · have gw : g.left ≫ pullback.snd X.hom i = pullback.snd Y.hom i := by
--- a/StacksFrontier/AlgebraicGeometry/Topologies/EtaleUniversalHomeomorphism.lean
+++ b/StacksFrontier/AlgebraicGeometry/Topologies/EtaleUniversalHomeomorphism.lean
@@ -129,10 +129,12 @@
       pullback.fst Y.hom g ≫ f.left =
           ((Over.pullback g).map f).left ≫ pullback.fst X.hom g := by
         simp [Over.pullback_map_left]
+        exact (pullback.lift_fst _ _ _).symm
       _ = ((Over.pullback g).map h).left ≫ pullback.fst X.hom g := by
         rw [congrArg Over.Hom.left hfh]
       _ = pullback.fst Y.hom g ≫ h.left := by
         simp [Over.pullback_map_left]
+        exact pullback.lift_fst _ _ _
   exact hom_ext_of_surjective (pullback.fst Y.hom g) this.surj X.hom f.left h.left hbase hrestrict
 
 /-- Base change along a universal homeomorphism is injective on morphisms into an étale scheme:
--- a/StacksFrontier/CategoryTheory/Triangulated/Elementary.lean
+++ b/StacksFrontier/CategoryTheory/Triangulated/Elementary.lean
@@ -169,9 +169,7 @@
     ∃ q : Y ⟶ Y, q ≫ q = q ∧ f ≫ q = a ≫ f ∧ g ≫ c = q ≫ g := by
   have hq : (𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b)) ≫ (𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b)) =
       𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b) := by
-    have h := isIdempotentElem_one_sub_one_sub_mul_self_mul_self (R := End Y) (x := End.of b)
-      (by ext; simpa using he)
-    simpa using congr(($h).asHom)
+    exact isIdempotentElem_one_sub_one_sub_mul_self_mul_self (R := End Y) (x := b) he
   refine ⟨𝟙 Y - (𝟙 Y - b ≫ b) ≫ (𝟙 Y - b ≫ b), hq, ?_, ?_⟩
   · simp only [comp_sub, sub_comp, Category.comp_id, Category.id_comp, ← Category.assoc,
       comp_comp_self hf ha]
--- a/StacksFrontier/Homology/Injectives/KInjective/SmallAcyclicComplexes.lean
+++ b/StacksFrontier/Homology/Injectives/KInjective/SmallAcyclicComplexes.lean
@@ -300,7 +300,7 @@
   cases n with
   | zero =>
     apply ((smallChain hK S).exactAt_iff' 1 0 0 (by simp) (by simp)).2
-    apply (ShortComplex.exact_iff_epi _ (by simp [HomologicalComplex.sc'])).2
+    apply (ShortComplex.exact_iff_epi _ (by simp [HomologicalComplex.sc'] <;> rfl)).2
     change Epi ((smallChain hK S).d (0 + 1) 0)
     simpa only [smallChain_d] using (inferInstanceAs (Epi S.d))
   | succ n =>
--- a/StacksFrontier/Homology/Perfect/FibreCriterion/BaseChangeSurjective.lean
+++ b/StacksFrontier/Homology/Perfect/FibreCriterion/BaseChangeSurjective.lean
@@ -167,7 +167,7 @@
       using hex m
   have hsurj := LinearMap.lTensor_surjective S d.surjective_rangeRestrict
   have ht := lTensor_exact S hex' d.surjective_rangeRestrict
-  rw [LinearMap.baseChange_eq_lTensor, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
+  rw [LinearMap.baseChange_eq_ltensor, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
   intro x hx
   obtain ⟨y, rfl⟩ := hsurj x
   have hy : d.lTensor S y = 0 := by
@@ -188,15 +188,15 @@
     ∃ f : R, f ∉ p ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[R] W) := by
   let A := Localization.AtPrime p
   have hqA : Function.Surjective (LinearMap.baseChange A q) := by
-    rw [LinearMap.baseChange_eq_lTensor]
+    rw [LinearMap.baseChange_eq_ltensor]
     exact LinearMap.lTensor_surjective A hq
   have hexA : Function.Exact (LinearMap.baseChange A d) (LinearMap.baseChange A q) := by
-    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact A hex hq
+    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact A hex hq
   have : Module.Free A (A ⊗[R] W) :=
     Module.free_of_lTensor_residueField_injective
       (LinearMap.baseChange A d) (LinearMap.baseChange A q) hqA hexA
       (lTensor_residueField_localization_injective p d
-        (by simpa only [LinearMap.baseChange_eq_lTensor] using hfib))
+        (by simpa only [LinearMap.baseChange_eq_ltensor] using hfib))
   obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
     p.primeCompl ((TensorProduct.mk R A W) 1) A
   refine ⟨f, hf, ?_⟩
@@ -256,7 +256,7 @@
       Function.Exact (LinearMap.baseChange p.ResidueField (P.iCycles i).hom)
         (LinearMap.baseChange p.ResidueField d)) at hexκ
     rw [toAlgebra_algebraMap] at hexκ
-    simpa only [LinearMap.baseChange_eq_lTensor] using hexκ
+    simpa only [LinearMap.baseChange_eq_ltensor] using hexκ
   have hq : Function.Surjective q :=
     (ModuleCat.epi_iff_surjective (P.pOpcycles (i + 1))).mp inferInstance
   have hdq : Function.Exact d q := exact_d_pOpcycles P i (i + 1) rfl
--- a/StacksFrontier/Homology/Perfect/FibreCriterion/FibreCohomologyVanishing.lean
+++ b/StacksFrontier/Homology/Perfect/FibreCriterion/FibreCohomologyVanishing.lean
@@ -261,9 +261,9 @@
     Function.Injective ((LinearMap.baseChange (Localization.AtPrime p) d).lTensor
       (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
   let A := Localization.AtPrime p
-  rw [← LinearMap.baseChange_eq_lTensor]
+  rw [← LinearMap.baseChange_eq_ltensor]
   have hfib : Function.Injective (LinearMap.baseChange p.ResidueField d) := by
-    rwa [LinearMap.baseChange_eq_lTensor]
+    rwa [LinearMap.baseChange_eq_ltensor]
   change Function.Injective
     (LinearMap.baseChange p.ResidueField (LinearMap.baseChange A d))
   rw [LinearMap.baseChange_baseChange]
@@ -331,10 +331,10 @@
   have hexι : Function.Exact ι q := fun x =>
     (hex x).trans ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩
   have hqA : Function.Surjective (LinearMap.baseChange A q) := by
-    rw [LinearMap.baseChange_eq_lTensor]
+    rw [LinearMap.baseChange_eq_ltensor]
     exact LinearMap.lTensor_surjective A hq
   have hexA : Function.Exact (LinearMap.baseChange A ι) (LinearMap.baseChange A q) := by
-    simpa only [LinearMap.baseChange_eq_lTensor] using lTensor_exact A hexι hq
+    simpa only [LinearMap.baseChange_eq_ltensor] using lTensor_exact A hexι hq
   have : Module.Free A (A ⊗[R] W) :=
     Module.free_of_lTensor_residueField_injective
       (LinearMap.baseChange A ι) (LinearMap.baseChange A q) hqA hexA
@@ -391,7 +391,7 @@
     Function.Exact (LinearMap.baseChange κ (P.d (i - 1) i).hom)
       (LinearMap.baseChange κ (P.d i (i + 1)).hom)) at hexf
   rw [toAlgebra_algebraMap] at hexf
-  simp only [LinearMap.baseChange_eq_lTensor] at hexf
+  simp only [LinearMap.baseChange_eq_ltensor] at hexf
   exact fun x hx => (hexf x).mp hx
 
 /-- An element `r` with `D(f) ⊆ D(r)` becomes a unit in `R_f`. -/
--- a/StacksFrontier/Homology/Perfect/ProjectiveAmplitude.lean
+++ b/StacksFrontier/Homology/Perfect/ProjectiveAmplitude.lean
@@ -857,7 +857,8 @@
   have : Module.FinitePresentation R ((↑T : Set M) →₀ Shrink.{v} R) :=
     Module.finitePresentation_of_projective _ _
   let : Module.FinitePresentation R ((↑T : Set M) →₀ Shrink.{v} R) := this
-  exact Module.FinitePresentation.of_equiv
+  exact Module.FinitePresentation.of_equiv (R := R) (M := (↑T : Set M) →₀ Shrink.{v} R)
+    (N := freePart R M T)
     (Finsupp.supportedEquivFinsupp (↑T : Set M) : _ ≃ₗ[R] ((↑T : Set M) →₀ Shrink.{v} R)).symm
 
 private theorem finitePresentation_quotient
@@ -875,8 +876,9 @@
     Module.FinitePresentation R (presentation R M j) := by
   let : Module.FinitePresentation R (freePart R M j.1) :=
     finitePresentation_freePart R M j.1
-  exact finitePresentation_quotient R (freePart R M j.1) (relations R M j) <| Submodule.fg_span
+  have h := finitePresentation_quotient R (freePart R M j.1) (relations R M j) <| Submodule.fg_span
     (Set.Finite.subset (j.2.finite_toSet.preimage Subtype.coe_injective.injOn) fun _ hy ↦ hy.1)
+  exact h
 
 private theorem exists_presentationToModule_eq (R : Type u) [CommRing R] [Small.{v} R]
     (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
--- a/StacksFrontier/Homology/PseudoCoherent/Homology.lean
+++ b/StacksFrontier/Homology/PseudoCoherent/Homology.lean
@@ -5,7 +5,7 @@
 public import Mathlib.Algebra.Module.FinitePresentation
 public import Mathlib.Algebra.Module.StablyFree.Basic
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import StacksFrontier.Algebra.Homology.PseudoCoherent
 import StacksCore.Tactic.EgaSgaAttribute
 
--- a/StacksFrontier/Homology/PseudoCoherent/Triangle.lean
+++ b/StacksFrontier/Homology/PseudoCoherent/Triangle.lean
@@ -7,7 +7,7 @@
 public import Mathlib.CategoryTheory.EffectiveEpi.Comp
 public import Mathlib.CategoryTheory.ExtremalEpi
 public import Mathlib.Combinatorics.Quiver.ReflQuiver
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.LinearAlgebra.Basis.Prod
 public import Mathlib.RingTheory.Finiteness.Basic
 public import Mathlib.RingTheory.Finiteness.Prod
--- a/StacksFrontier/Homology/TorAmplitude/Termwise.lean
+++ b/StacksFrontier/Homology/TorAmplitude/Termwise.lean
@@ -3,7 +3,7 @@
 public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
 public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
 public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
-public import Mathlib.Order.Int.ConditionallyCompleteOrder
+public import Mathlib.Data.Int.ConditionallyCompleteOrder
 public import Mathlib.RingTheory.LocalRing.Module
 
 @[expose] public section
```
