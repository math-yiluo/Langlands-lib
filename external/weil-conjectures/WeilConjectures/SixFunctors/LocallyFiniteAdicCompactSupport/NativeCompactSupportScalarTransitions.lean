/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData

/-! # Integral scalar-mate steps for native compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

/-- The common-field scalar arrow before the final integral realization.
Source: Bhatt--Scholze, Proposition 6.8.14; the `commonField` normalization.
(blueprint: def-sf-native-compact-support-scalar-transition-maps). -/
def nativeScalarTransition [_G : NativeGeometry.{u} l]
    (T : Scheme.{u}) (R : Realization l T)
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (M : DerivedCategory (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) i) T)) :
    (pbcDerivedExtend ((R.coefficient i).integralMap l T)).obj M ⟶
      (pbcDerivedExtend ((R.coefficient E).integralMap l T)).obj
        ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
          (Coefficient.{u} l (PadicAlgCl l) E)
          (coefficientInclusion l (PadicAlgCl l) i E h) T).obj M) :=
  (pbcReductionNormalization
    (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) i)
      (Coefficient.{u} l (PadicAlgCl l) E)
      (coefficientInclusion l (PadicAlgCl l) i E h) T)
    ((R.coefficient E).integralMap l T) ((R.coefficient i).integralMap l T)
    (R.coefficient_scalar i E h) M).inv ≫
    (pbcDerivedExtend ((R.coefficient E).integralMap l T)).map
      ((completedTensorComparison l T (Coefficient.{u} l (PadicAlgCl l) i)
        (Coefficient.{u} l (PadicAlgCl l) E)
        (coefficientInclusion l (PadicAlgCl l) i E h)).app M)

/-- Compact support of the finite coefficient change, followed by completed scalar change.
Source: Bhatt--Scholze, Remark 6.8.15; the normalized proper/open scalar comparison.
(blueprint: def-sf-native-compact-support-scalar-transition-maps). -/
def supportScalarTransition [_G : NativeGeometry.{u} l]
    (target : Realization l Y) (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (M : DerivedCategory (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) i) X)) :
    (pbcDerivedExtend ((target.coefficient i).integralMap l Y)).obj
        ((PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) i)) c).obj M) ⟶
      (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj
        ((PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)) c).obj
            ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
              (Coefficient.{u} l (PadicAlgCl l) E)
              (coefficientInclusion l (PadicAlgCl l) i E h) X).obj M)) :=
  (pbcReductionNormalization
    (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) i)
      (Coefficient.{u} l (PadicAlgCl l) E)
      (coefficientInclusion l (PadicAlgCl l) i E h) Y)
    ((target.coefficient E).integralMap l Y) ((target.coefficient i).integralMap l Y)
    (target.coefficient_scalar i E h)
    ((PurCompactSupport.image (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) i)) c).obj M)).inv ≫
    (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
      ((PurCompactSupport.comparison
        (PurCompactSupport.completedChange l (Coefficient.{u} l (PadicAlgCl l) i)
          (Coefficient.{u} l (PadicAlgCl l) E)
          (coefficientInclusion l (PadicAlgCl l) i E h)) c).app M ≫
        (PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)) c).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) i)
            (Coefficient.{u} l (PadicAlgCl l) E)
            (coefficientInclusion l (PadicAlgCl l) i E h)).app M))

/-- The specified native scalar mate, transported along the given coefficient equalities.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-native-compact-support-scalar-transition-maps). -/
def nativeScalarComponent [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (E : Index l (PadicAlgCl l))
    (change : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : change.map X = (source.coefficient E).integralMap l X)
    (ht : change.map Y = (target.coefficient E).integralMap l Y)
    (M : DerivedCategory (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) E) X)) :
    (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj
        ((PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)) c).obj M) ⟶
      (PurCompactSupport.image (nativeCoefficients l) c).obj
        ((pbcDerivedExtend ((source.coefficient E).integralMap l X)).obj M) :=
  eqToHom (congrArg (fun a ↦ (pbcDerivedExtend a).obj
    ((PurCompactSupport.image (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) c).obj M)) ht.symm) ≫
    (PurCompactSupport.comparison change c).app M ≫
    eqToHom (congrArg (fun a ↦ (PurCompactSupport.image (nativeCoefficients l) c).obj
      ((pbcDerivedExtend a).obj M)) hs)

end WeilConjectures.LocallyFiniteAdicCompactSupport
