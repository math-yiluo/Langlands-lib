/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

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

/-- The initial three-arrow boundary respects a completed finite coefficient change.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the initial-boundary
part of the integral numerator calculation.

Proof: first use `P.localizationIdentity` and
`P.fields.rationalization_normalized` to identify the recorded rationalLeft arrow
with localization of integralLeft. Naturality of the target integral realization
and `P.ring.integralLeft_normalized` then identify each boundary with that integral
realization followed by extension of the recorded ordinary left realization.
Express the stage transition by `stage.system.β h`. Its scalar normalization and
`P.fields.rational_normalized` give the localized integral comparison. The target
realization's `common_field` equation gives its balanced scalar associator and
completion map. Naturality of the target integral realization moves the localized
integral comparison into the ordinary derived category. Apply
`P.ring.comparison_normalized` and replace ordinary scalar realization by its
prescribed balanced tensor map using `integralScalar_normalized`. Cancel the adjacent
realization isomorphisms. The resulting composite consists of
the completed proper/open scalar mate and compact support of the completion map.
Naturality of the balanced scalar associator moves the ordinary left realization
past it, giving exactly bi followed by `supportScalarTransition`.
This calculation uses only the initial three arrows; it contains neither the native
scalar mate nor the final source-realization boundary. Identity field changes use
the same normalized tensor unit, so the argument includes `i = E`.
(blueprint: lem-sf-native-integral-source-boundary-transition). -/
theorem integralSourceBoundary_transition [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (hKE : KE.obj =
      (integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
        (Coefficient.{u} l (PadicAlgCl l) E)
        (coefficientInclusion l (PadicAlgCl l) i E h) X).obj K.obj)
    (bi : (sections l Y).mapDerivedCategory.obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) i ⋙
          stage.system.functor ⋙ target.J).obj
          ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K)) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) i)) c ⋙
        pbcDerivedExtend ((target.coefficient i).integralMap l Y)).obj K.obj)
    (bE : (sections l Y).mapDerivedCategory.obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙
          stage.system.functor ⋙ target.J).obj
          ((⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩ :
            generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h)) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj KE.obj)
    (hbi : IntegralSourceBoundary l D hl P c target i K bi)
    (hbE : IntegralSourceBoundary l D hl P c target E KE bE) :
    ArrowHEq
      ((sections l Y).mapDerivedCategory.map
          ((stage.system.functor ⋙ target.J).map
            ((StageSystem.isoToStage
              (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
              ⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩
              h).hom)) ≫ bE)
      (bi ≫ supportScalarTransition l c target i E h K.obj) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
