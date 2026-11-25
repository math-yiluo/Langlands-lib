/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Representative data for native derived tensors

Source: Stacks 06YS, 08J9 and 0FPT; the action-site tensor and its localization.
These data concern the tensor on complexes and its derived model. They contain
no native derived closed adjunction or derived internal-Hom comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- A sum-total tensor preserves acyclicity in the other factor.
Source: Stacks 06YS (blueprint: def-sf-native-weil-tensor-presentation). -/
def NativeTensorKFlat
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) : Prop :=
  ∀ N : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    N.Acyclic → (CochainComplex.mapBifunctor P N T).Acyclic

/-- The native tensor's representative presentation, including normalization
under ordinary forgetting. The underived adjunction is part of the chain
calculation; the derived adjunction is not part of these data.

Source: Stacks 06YS, 08J9 and 0FPT; native ringed tensor model, steps 1 and 3.
(blueprint: def-sf-native-weil-tensor-presentation). -/
structure NativeWeilTensorComplexData
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X))) where
  /-- Right tensor parameter first, as in ordinaryTensorBifunctor. -/
  tensor : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X
  /-- Additivity of the native relative tensor. -/
  [tensor_additive : tensor.Additive]
  /-- Additivity in its other variable. -/
  [tensor_obj_additive : ∀ P, (tensor.obj P).Additive]
  /-- The countable sum totals exist. -/
  [total_exists : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    P.HasMapBifunctor Q tensor]
  /-- The actual underived tensor--Hom adjunction in both variables. -/
  adjunction : tensor ⊣₂ ihomBifunctor k₀ l X
  /-- Forgetting the native tensor gives the ordinary relative tensor. -/
  underived : Functor.uncurry.obj tensor ⋙
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
        Functor.uncurry.obj
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  /-- A one-K-flat model for the native derived tensor. -/
  model (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X tensor P) :
    m.tensorObj (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P Q tensor)
  /-- The specified ordinary model, taken from hS. -/
  ordinaryModel (P Q : CochainComplex (ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
      (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P) :
    S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q)
  /-- The chain comparison is the sum of the underived tensor comparisons. -/
  chain (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    ((Endofunctor.IsoAlgebra.forget
      (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q tensor) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)

attribute [instance] NativeWeilTensorComplexData.tensor_additive
  NativeWeilTensorComplexData.tensor_obj_additive NativeWeilTensorComplexData.total_exists

/-- Equations for the explicit native tensor data. Keeping the equations in Prop
avoids repeatedly generating large equality tests for their proof fields.
Source: Stacks 06YS, 08J9, 0FPT
(blueprint: def-sf-native-weil-tensor-presentation). -/
structure NativeWeilTensorPresentationAxioms
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)))
    (t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    (D : NativeWeilTensorComplexData k₀ l X M S m) : Prop where
  /-- The underived comparison is evaluation-normalized. -/
  underived_uncurry (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I) :
    D.underived.inv.app (P, Q) ≫
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (((D.adjunction.adj P).homEquiv Q I).symm f) =
      ((Mod.ihomAdjunction P.carrier).homEquiv Q.carrier I.carrier).symm f.hom.f
  /-- K-flat representatives present the entire unbounded derived category. -/
  localization :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X D.tensor)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X D.tensor)))
  /-- Forgetting preserves the acyclic-test K-flat condition. -/
  preserves_flat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X D.tensor P) :
    NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
  /-- Naturality includes source replacements by quasi-isomorphisms. -/
  model_naturality (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X D.tensor P)
      (hP' : NativeTensorKFlat k₀ l X D.tensor P') (f : P ⟶ P') (g : Q ⟶ Q') :
    (@MonoidalCategory.tensor _ _ m).map
        (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
        (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
        (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
        (D.model P' Q' hP').hom =
      (D.model P Q hP).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f g D.tensor (.up ℤ))
  /-- Its adjunction is componentwise uncurrying. -/
  ordinaryNormalization : NativeAdjunctionNormalization
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (fun P ↦ Mod.ihomAdjunction P) M.ordinaryHom M.ordinaryRepresentatives S
    (NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) D.ordinaryModel
  /-- Its summands are fixed, ruling out an arbitrary comparison automorphism. -/
  chain_summand (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) :
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
        (HomologicalComplex.ιMapBifunctor P Q D.tensor (.up ℤ) p q n hpq) ≫
          (D.chain P Q).hom.f n =
      D.underived.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
        (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        (.up ℤ) p q n hpq
  /-- The derived comparison is the localization of this chain comparison. -/
  model_forget (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X D.tensor P) :
    (nativeForget k₀ l X).map (D.model P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q D.tensor)) ≫
        DerivedCategory.Q.map (D.chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (D.ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (preserves_flat P hP)).hom

/-- The native tensor data and their representative equations.
Source: Stacks 06YS, 08J9, 0FPT
(blueprint: def-sf-native-weil-tensor-presentation). -/
structure NativeWeilTensorPresentation
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X)))
    (t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor)
    extends NativeWeilTensorComplexData k₀ l X M S m where
  /-- Localization, normalization and forgetting equations. -/
  axioms : NativeWeilTensorPresentationAxioms k₀ l X M S m t toNativeWeilTensorComplexData

namespace NativeWeilTensorPresentation
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {M : NativeClosedHomModels k₀ l X} {S : CoefficientClosedStructure M.ordinaryHom}
  {m : MonoidalCategory (DerivedCategory (ProEtaleWeilSheaf k₀ l X))}
  {t : @MonoidalCategory.tensor _ _ m ⋙ nativeForget k₀ l X ≅
    (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor}
  (N : NativeWeilTensorPresentation k₀ l X M S m t)

@[inherit_doc NativeWeilTensorPresentationAxioms.underived_uncurry]
abbrev underived_uncurry := N.axioms.underived_uncurry

@[inherit_doc NativeWeilTensorPresentationAxioms.localization]
abbrev localization := N.axioms.localization

@[inherit_doc NativeWeilTensorPresentationAxioms.preserves_flat]
abbrev preserves_flat := N.axioms.preserves_flat

@[inherit_doc NativeWeilTensorPresentationAxioms.model_naturality]
abbrev model_naturality := N.axioms.model_naturality

@[inherit_doc NativeWeilTensorPresentationAxioms.ordinaryNormalization]
abbrev ordinaryNormalization := N.axioms.ordinaryNormalization

@[inherit_doc NativeWeilTensorPresentationAxioms.chain_summand]
abbrev chain_summand := N.axioms.chain_summand

@[inherit_doc NativeWeilTensorPresentationAxioms.model_forget]
abbrev model_forget := N.axioms.model_forget

end NativeWeilTensorPresentation

end AlgebraicGeometry.ProEtaleWeilSheaf
