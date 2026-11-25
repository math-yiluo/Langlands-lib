/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralCanonicalTargetTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralTargetBoundaryFormula

/-! # Integral scalar-mate steps for native compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.LocallyFiniteAdicCompactSupport.actual
  WeilConjectures.PurCompactSupport.image
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.LocallyFiniteAdicRealization.sections
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} {f : X ⟶ Y}
  (c : Compactification f)

private theorem app_arrow_congr {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (α : F ⟶ H) {A B : C} (h : A = B) :
    ArrowHEq (α.app A) (α.app B) := by
  cases h
  exact ArrowHEq.refl _

-- The formulas compare cached finite-stage and native coefficient presentations.
/-- The final two-arrow boundary respects the canonical common-field scalar arrow.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
Proof: the endpoint-aware component equations identify both boundaries with compact
support of the inverse integral realization followed by inverse operationTransport.
The common_field equation writes the realized stage transition as the integral
realization, nativeScalarTransition, and inverse integral realization. Naturality of
operationTransport moves the realized transition through its inverse. Cancel the
integral realization and its inverse. The remaining equation is precisely this square.
(blueprint: lem-sf-native-integral-target-boundary-transition). -/
theorem integralTargetBoundary_transition [G : NativeGeometry.{u} l]
    (source : Realization l X) (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (hKE : (PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj KE =
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        i E h).obj ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) i) X).obj K))
    (di : (pbcDerivedExtend ((source.coefficient i).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ⟶
      (sections l Y).mapDerivedCategory.obj
        (((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) i) ⋙ source.J ⋙ actual l c).obj
          ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K)))
    (dE : (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c).obj KE.obj ⟶
      (sections l Y).mapDerivedCategory.obj
        (((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E) ⋙ source.J ⋙ actual l c).obj
          ((⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩ :
            generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h)))
    (hdi : IntegralTargetBoundary l c source i K di)
    (hdE : IntegralTargetBoundary l c source E KE dE) :
    ArrowHEq (C := DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
      ((PurCompactSupport.image (nativeCoefficients l) c).map
          (nativeScalarTransition l X source i E h K.obj) ≫
        eqToHom (congrArg (fun L : sfIntegralConstructibleCategory l
          (Coefficient.{u} l (PadicAlgCl l) E) X ↦
            (PurCompactSupport.image (nativeCoefficients l) c).obj
              ((pbcDerivedExtend ((source.coefficient E).integralMap l X)).obj L.obj))
          hKE.symm) ≫ dE)
      (di ≫ (sections l Y).mapDerivedCategory.map
        ((source.J ⋙ actual l c).map
          ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩
            h).hom))) := by
  let Ki := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient.{u} l (PadicAlgCl l) i) X).obj K
  have hi := integralTargetBoundary_formula l c source i K di hdi
  have he := integralTargetBoundary_formula l c source E KE dE hdE
  have h₄ := (app_arrow_congr (source.integral E).inv hKE).map
    (PurCompactSupport.image (nativeCoefficients l) c)
  have hinput := congrArg (fun L : sfIntegralConstructibleCategory l
    (Coefficient.{u} l (PadicAlgCl l) E) X ↦
      source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj L))) hKE
  have h₅ := app_arrow_congr (operationTransport l c).inv hinput
  have he' := he.trans (h₄.comp h₅)
  let p := congrArg (fun L : sfIntegralConstructibleCategory l
    (Coefficient.{u} l (PadicAlgCl l) E) X ↦
      (PurCompactSupport.image (nativeCoefficients l) c).obj
        ((pbcDerivedExtend ((source.coefficient E).integralMap l X)).obj L.obj)) hKE.symm
  have hcast : ArrowHEq (eqToHom p) (𝟙 _) :=
    ⟨rfl, p.symm, eqToHom_heq_id_dom _ _ p⟩
  have he'' := (hcast.comp he').trans
    (show ArrowHEq _ _ from ⟨rfl, rfl, heq_of_eq (Category.id_comp _)⟩)
  have hp := canonicalIntegralTargetTransition l c source i E h Ki
  exact ((ArrowHEq.refl _).comp he'').trans
    (hp.trans (hi.comp (ArrowHEq.refl _)).symm)

end WeilConjectures.LocallyFiniteAdicCompactSupport
