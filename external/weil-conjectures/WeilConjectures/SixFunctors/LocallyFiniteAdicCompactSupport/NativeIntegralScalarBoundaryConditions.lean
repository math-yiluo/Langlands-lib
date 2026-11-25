/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.CategoryTheory.ArrowHEq.ArrowHEq

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
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
attribute [local instance 2000] Shrink.instField
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

/-- The first three arrows of the normalized integral compact-support comparison.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-native-integral-scalar-boundary-conditions). -/
def IntegralSourceBoundary [G : NativeGeometry.{u} l]
    (target : Realization l Y) (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U V : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y))} (b : U ⟶ V) : Prop :=
  let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
  ∃ (A B : sfRationalConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
      (r : A ⟶ B),
      ArrowHEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
  ∃ (M₁ M₂ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : U ⟶ M₁) (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ V),
      ArrowHEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      ArrowHEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      ArrowHEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      b = a₀ ≫ a₁ ≫ a₂

/-- The final two arrows of the normalized integral compact-support comparison.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-native-integral-scalar-boundary-conditions). -/
def IntegralTargetBoundary [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U V : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y))} (d : U ⟶ V) : Prop :=
  let rationalInput :=
    (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
  let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
  ∃ (M₅ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₄ : U ⟶ M₅) (a₅ : M₅ ⟶ V),
      ArrowHEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      ArrowHEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      d = a₄ ≫ a₅

/-- The six-arrow formula with an arbitrary, endpoint-recorded scalar arrow.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: def-sf-native-integral-scalar-boundary-conditions). -/
def IntegralScalarFormula [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U₃ V₃ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y))}
    (beta : U₃ ⟶ V₃)
    {U V : DerivedCategory (ProEtale.AdicSheaf l Y)} (m : U ⟶ V) : Prop :=
  let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
  let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
  ∃ (A B : sfRationalConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y)
      (r : A ⟶ B),
      ArrowHEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
  ∃ (M₁ M₂ M₃ M₄ M₅ : DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        U ⟶ M₁)
      (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) (a₃ : M₃ ⟶ M₄) (a₄ : M₄ ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        V),
      ArrowHEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      ArrowHEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient.{u} l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      ArrowHEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient.{u} l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      ArrowHEq a₃ beta ∧
      ArrowHEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))) ∧
      ArrowHEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      (sections l Y).mapDerivedCategory.map m =
        a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅

end WeilConjectures.LocallyFiniteAdicCompactSupport
