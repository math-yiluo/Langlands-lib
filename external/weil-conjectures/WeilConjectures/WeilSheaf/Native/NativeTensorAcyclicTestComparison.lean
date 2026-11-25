/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.NativeWeilTensorPresentation.NativeWeilTensorPresentation
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import all WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedComplexes
import all WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Localization.Prod

/-! # Comparing the two native K-flat predicates

The public result is the cone criterion for the native acyclic-test predicate.
Private helpers assemble tensor models and descend natural comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  CategoryTheory.Mod.tensorLeft CategoryTheory.Mod.ihomAdjunction
  AlgebraicGeometry.ProEtaleWeilSheaf.tensorIhomAdjunction

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace NativeOpenComparisonProof

private theorem flat_tests {C : Type*} [Category C] [Abelian C]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ P Q : CochainComplex C ℤ, P.HasMapBifunctor Q F]
    (P : CochainComplex C ℤ)
    (h₁ : ∀ N : CochainComplex C ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor P N F).Acyclic)
    (h₂ : ∀ N : CochainComplex C ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P F).Acyclic) :
    (∀ {Q Q' : CochainComplex C ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.map₂CochainComplex.obj P).map f)) ∧
    (∀ {Q Q' : CochainComplex C ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.map₂CochainComplex.flip.obj P).map f)) := by
  constructor
  · intro Q Q' f hf
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    exact fun n ↦ (h₁ _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf) n).of_iso
      (CochainComplex.mapBifunctorMappingCone₂Iso P f F)
  · intro Q Q' f hf
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    exact fun n ↦ (h₂ _ ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf) n).of_iso
      (CochainComplex.mapBifunctorMappingCone₁Iso f P F)

end NativeOpenComparisonProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]

private structure FlatTest (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) : Prop where
  test : NativeIsKFlat k₀ l X P

-- The data structure was elaborated without this shortcut instance; using it here makes the
-- kernel compare two `IsGrothendieckAbelian` instances by deep unfolding.
attribute [-instance] ModuleCat.isGrothendieckAbelian_of_commRing in
private theorem FlatTest.restrict (s : NativeOpenTensorData k₀ l j)
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) (hP : FlatTest k₀ l Z P) :
    FlatTest k₀ l U (((upperStar k₀ l j).mapHomologicalComplex (.up ℤ)).obj P) :=
  ⟨s.restriction_kflat P hP.test⟩

-- The data structure was elaborated without this shortcut instance; using it here makes the
-- kernel compare two `IsGrothendieckAbelian` instances by deep unfolding.
attribute [-instance] ModuleCat.isGrothendieckAbelian_of_commRing in
private theorem FlatTest.extend (s : NativeOpenTensorData k₀ l j)
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l U) ℤ) (hP : FlatTest k₀ l U P) :
    FlatTest k₀ l Z (((extensionByZero k₀ l j).mapHomologicalComplex (.up ℤ)).obj P) :=
  ⟨s.extension_kflat P hP.test⟩

private instance nativeTensor_additive (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (nativeTensorBifunctor k₀ l X).Additive := by
  constructor
  intro A B f g
  apply NatTrans.ext
  funext N
  exact (nativeTensorBifunctor_flip_obj_additive k₀ l X N).map_add

private instance nativeTensor_obj_additive (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] (M : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).obj M).Additive :=
  (tensorIhomAdjunction k₀ l X M).left_adjoint_additive

private instance nativeTensor_hasTotal (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    P.HasMapBifunctor Q (nativeTensorBifunctor k₀ l X) := inferInstance

/-- The acyclic-test native tensor predicate implies both quasi-isomorphism tests.

Source: Stacks 06YN, lemma-K-flat-quasi-isomorphism, and total tensor symmetry.
(blueprint: new-sf-native-tensor-acyclic-test-comparison).

Proof: use the native-to-ringed total comparison to exchange tensor factors.
The equivalence is exact and faithful, so it preserves and reflects acyclicity.
Apply tensor to the cone of a quasi-isomorphism and use the two tensor/cone
isomorphisms. Acyclicity of both resulting cones proves both tests. -/
theorem native_tensor_acyclic_test_kflat (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [(nativeTensorBifunctor k₀ l X).Additive]
    [∀ M, ((nativeTensorBifunctor k₀ l X).obj M).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      P.HasMapBifunctor Q (nativeTensorBifunctor k₀ l X)]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X (nativeTensorBifunctor k₀ l X) P) :
    NativeIsKFlat k₀ l X P := by
  let T := nativeTensorBifunctor k₀ l X
  have : T.Additive := by
    constructor
    intro A B f g
    apply NatTrans.ext
    funext N
    exact (nativeTensorBifunctor_flip_obj_additive k₀ l X N).map_add
  have : ∀ M, (T.obj M).Additive := fun M ↦
    (tensorIhomAdjunction k₀ l X M).left_adjoint_additive
  obtain ⟨b⟩ := native_weil_tensor_ringed_bridge k₀ l X
  obtain ⟨c⟩ := native_weil_tensor_ringed_complexes b T
    (nativeTensorParametrizedAdjunction k₀ l X)
  let E := b.native.functor
  let : HasColimitsOfSize.{0, 0} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have hac (N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hN : N.Acyclic) :
      (CochainComplex.mapBifunctor N P T).Acyclic := by
    have h := (hP N hN).map E
    have h' : ((WeilConjectures.coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj N,
          (E.mapHomologicalComplex (.up ℤ)).obj P)).Acyclic :=
      fun n ↦ (h n).of_iso (c.chain P N)
    have hrev := SheafOfModules.tensor_acyclic_swap
      ((E.mapHomologicalComplex (.up ℤ)).obj N)
      ((E.mapHomologicalComplex (.up ℤ)).obj P) h'
    have h'' : ((E.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor N P T)).Acyclic :=
      fun n ↦ (hrev n).of_iso (c.chain N P).symm
    intro n
    exact ((CochainComplex.mapBifunctor N P T).sc n).exact_map_iff_of_faithful E |>.1
      (h'' n)
  apply NativeOpenComparisonProof.flat_tests T.flip P
  · intro N hN n
    exact (hac N hN n).of_iso
      (HomologicalComplex.mapBifunctorFlipIso N P T (.up ℤ)).symm
  · intro N hN n
    exact (hP N hN n).of_iso
      (HomologicalComplex.mapBifunctorFlipIso P N T (.up ℤ)).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
