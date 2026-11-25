/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

/-! # Native exact open operations and tensor models

These are the unchanged concrete operations, representative maps and forget
comparisons extracted from NativeOpenDerivedTensor to bound compilation time.
Source: Stacks 0GL1, 0E8I, 03D8 and the original declaration docstrings
(blueprint: lem-sf-native-open-derived-tensor).
-/

/-! Factored construction (blueprint: def-sf-native-open-tensor-operations). -/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The existing termwise pullback, localized on the ambient Weil category.
Source: native framework, Category.lean (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenPull {V W : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [W.Over (Spec (CommRingCat.of k₀))] (f : V ⟶ W)
    [f.IsOver (Spec (CommRingCat.of k₀))] :=
  (upperStar k₀ l f).mapDerivedCategory

/-- The existing exact extension, localized on the ambient Weil category.
Source: Stacks 03DJ; OpenImmersion.lean
(blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenExtension {V W : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    [W.Over (Spec (CommRingCat.of k₀))] (j : V ⟶ W) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :=
  (extensionByZero k₀ l j).mapDerivedCategory

/-- The canonical balanced compositor, oriented from iterated to composite pullback.
The underlying module compositor is the adjunction-determined balanced map
b tensor (c tensor t) to b j*(c) tensor t; its inverse inserts the coefficient 1.
This definition localizes that actual sheaf compositor, including its Weil action.
Source: Stacks 03D8; UpperStarComp.lean
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenPullComp {V W Y : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [W.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (j : V ⟶ W) (p : W ⟶ Y)
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))] :
    nativeOpenPull k₀ l p ⋙ nativeOpenPull k₀ l j ≅ nativeOpenPull k₀ l (j ≫ p) :=
  Functor.mapDerivedCategoryCompIso (upperStar k₀ l p) (upperStar k₀ l j) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarCompIso k₀ l j p).symm

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The two-variable tensor, with left argument first, on Weil sheaves.
Source: diagonal tensor in the native framework
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenSheafTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf k₀ l X × ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X :=
  Functor.uncurry.obj (nativeTensorBifunctor k₀ l X).flip

/-- The left side of the ordinary sheaf open tensor comparison on native objects.
Source: Stacks 0E8I (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenSheafLeft :=
  (extensionByZero k₀ l j).prod (𝟭 _) ⋙ nativeOpenSheafTensor k₀ l Z

/-- The right side of the ordinary sheaf open tensor comparison on native objects.
Source: Stacks 0E8I (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenSheafRight :=
  (𝟭 _).prod (upperStar k₀ l j) ⋙ nativeOpenSheafTensor k₀ l U ⋙ extensionByZero k₀ l j

/-- The left side of the ambient derived open tensor comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenDerivedLeft :=
  (nativeOpenExtension k₀ l j).prod (𝟭 _) ⋙ nativeDerivedTensor k₀ l Z

/-- The right side of the ambient derived open tensor comparison.
Source: Stacks 0GL1 (blueprint: lem-sf-native-open-derived-tensor). -/
abbrev nativeOpenDerivedRight :=
  (𝟭 _).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U ⋙
    nativeOpenExtension k₀ l j

/-- The actual summand inclusion for the recorded left-first total tensor.
Source: Stacks 012Z and nativeTensorTotal
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenTensorInsertion (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    tensor k₀ l X (T.X q) (P.X p) ⟶
      (((nativeTensorTotal k₀ l X).obj P).obj T).X n :=
  HomologicalComplex.ιMapBifunctor P T (nativeTensorBifunctor k₀ l X).flip
    (.up ℤ) p q n h

/-- The K-flat model fixed by the signed tensor--Hom evaluation normalization.
Source: Stacks 0A96 and 08J9, native_normalized_tensor_models
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenTensorModel (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeIsKFlat k₀ l X P) (hT : NativeIsKFlat k₀ l X T) :
    (nativeDerivedTensor k₀ l X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
      DerivedCategory.Q.obj (((nativeTensorTotal k₀ l X).obj P).obj T) :=
  (native_normalized_tensor_models k₀ l X).choose P T hP hT

/-- Forgetting commutes with the actual open extension, using exact-functor factors.
Source: OpenImmersion.lean, mapOfNatIso; Stacks 015F
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenForgetExtension :
    nativeOpenExtension k₀ l j ⋙ nativeForget k₀ l Z ≅
      nativeForget k₀ l U ⋙
        (ProEtale.adicOpenImmersionLowerShriek l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (extensionByZero k₀ l j)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z)) ≪≫
  Functor.mapDerivedCategoryNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    rfl)) ≪≫
  (Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U))
    (ProEtale.adicOpenImmersionLowerShriek l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)))).symm

/-- Forgetting commutes with the actual open pullback, with the same exact factors.
Source: Category.lean, mapOfNatIso; Stacks 015F
(blueprint: lem-sf-native-open-derived-tensor). -/
def nativeOpenForgetPull :
    nativeOpenPull k₀ l j ⋙ nativeForget k₀ l U ≅
      nativeForget k₀ l Z ⋙
        (ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (upperStar k₀ l j)
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l U)) ≪≫
  Functor.mapDerivedCategoryNatIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    rfl)) ≪≫
  (Functor.mapDerivedCategoryCompIso
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Z))
    (ProEtale.adicUpperStar l (Scheme.Hom.geometricFiberMap j (comp_over j _)))).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
