/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphismNormalization

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

/-- Source of the finite-stage comparison, before extending morphisms to fractions.
Source: the finite-stage inclusion (blueprint: lem-sf-native-integral-scalar-morphism). -/
abbrev finiteSource (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J

/-- Target of the finite-stage comparison.
Source: the finite-stage inclusion (blueprint: lem-sf-native-integral-scalar-morphism). -/
abbrev finiteTarget (source : Realization l X)
    (E : Index l (PadicAlgCl l)) :=
  GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c

/-- The original six-arrow formula at one integral finite-Tor input.
Source: Bhatt--Scholze, Remark 6.8.15; the existing IntegralNormalization definition.
(blueprint: lem-sf-native-integral-scalar-morphism). -/
def IntegralComponent [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U V : DerivedCategory (ProEtale.AdicSheaf l Y)} (m : U ⟶ V) : Prop :=
  IntegralScalarFormula l D hl P c source target E K
    ((PurCompactSupport.comparison (change E) c).app K.obj) m

/-- Construct the integral natural morphism, with its typed scalar-mate factorization.
This theorem asserts neither invertibility nor naturality on rationalized arrows.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15;
steps 4 and 8 of the native compact-support finite comparison plan.
(blueprint: lem-sf-native-integral-scalar-morphism).

Proof: restrict the StageAction inclusion comparison to integral objects and compose
with P.ring.rationalLeft. The recorded rational compact-support operation is the raw
localization of its integral functor. The target integral realization followed by the
inverse of sfQcqsCompactSupportRealization therefore gives the first three arrows of
the original formula. Apply the proper/open scalar mate, then compact support of the
inverse source integral realization and inverse operationTransport. All operations and
comparisons are natural on integral derived morphisms, giving tau. The factors before
and after the scalar mate are composites of isomorphisms; group them as b and d.
The coefficient equalities hs and ht transport their endpoints without changing maps.
Unpack their definitions to get exactly the six-arrow IntegralComponent formula.
This construction uses the specified compactification and quotient transitions. -/
theorem native_integral_scalar_morphism [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (E : Index l (PadicAlgCl l)) :
    ∃ tau : sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteSource l D hl P c target stage E ⟶
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        finiteTarget l c source E,
      ∀ K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X,
        (∃ (b : (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                finiteSource l D hl P c target stage E).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) ≅
            (PurCompactSupport.image (PurCompactSupport.completed l
              (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
              pbcDerivedExtend ((change E).map Y)).obj K.obj)
          (d : (pbcDerivedExtend ((change E).map X) ⋙
              PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ≅
            (sections l Y).mapDerivedCategory.obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
                finiteTarget l c source E).obj
                  ((PurCompactSupport.finiteTorIntegralInclusion l
                    (Coefficient.{u} l (PadicAlgCl l) E) X).obj K))),
          (sections l Y).mapDerivedCategory.map
              (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) =
            b.hom ≫ (PurCompactSupport.comparison (change E) c).app K.obj ≫ d.hom) ∧
        IntegralComponent l D hl P c source target change E K
          (tau.app ((PurCompactSupport.finiteTorIntegralInclusion l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)) := by
  refine (native_integral_scalar_morphism_normalization l D hl P c
    source target stage E ((change E).map X) ((change E).map Y) (hs E) (ht E)
    (PurCompactSupport.comparison (change E) c)).elim ?_
  intro tau hcomponents
  refine ⟨tau, fun K ↦ ?_⟩
  exact ⟨(hcomponents K).1, (hcomponents K).2⟩

end WeilConjectures.LocallyFiniteAdicCompactSupport
