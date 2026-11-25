/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarBoundaries
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralBoundaryIsoFactorization
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralStageObject

/-! # The normalized integral component at a common scalar stage -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
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

private theorem component_transport {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (alpha : F ⟶ H) {A B : C} (p : A = B) {U V : D}
    (b : F.obj A ⟶ U) (q : U ⟶ V) (d : V ⟶ H.obj A)
    (Pb Pd : ∀ {A B : D}, (A ⟶ B) → Prop)
    (hb : Pb b) (hd : Pd d) (hf : alpha.app A = b ≫ q ≫ d) :
    ∃ (b' : F.obj B ⟶ U) (d' : V ⟶ H.obj B),
      Pb b' ∧ Pd d' ∧ alpha.app B = b' ≫ q ≫ d' := by
  subst B
  exact ⟨b, d, hb, hd, hf⟩

attribute [local irreducible] IntegralSourceBoundary IntegralTargetBoundary
  IntegralComponent IntegralScalarFormula nativeScalarComponent

-- Compare the cached finite-stage types without unfolding their constructions.
/-- Move one normalized integral component to its canonical common scalar stage.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
Proof: use the constructed boundary isomorphisms at E and factor the normalized
component through them. The stage-system transition equation and rational scalar
extension's object formula identify rationalization of KE with the common-stage
object. Eliminate this equality in a generic categorical helper: the original
boundaries become witnesses at the common stage, their prescribed-arrow predicates
are preserved, and the same factorization holds there. The witnesses are explicit
equality transports of the constructed boundary components.
(blueprint: lem-sf-native-integral-stage-component). -/
theorem integralStageComponent [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ j : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) j)) (nativeCoefficients l))
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (hs : (change E).map X = (source.coefficient E).integralMap l X)
    (ht : (change E).map Y = (target.coefficient E).integralMap l Y)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (hKE : (PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj KE =
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        i E h).obj ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) i) X).obj K))
    (alpha : finiteSource l D hl P c target stage E ⟶ finiteTarget l c source E)
    (hm : IntegralComponent l D hl P c source target change E KE
      (alpha.app ((rationalization.{u, u} l (ULift.{u} (PadicAlgCl l))
        (finiteField l E) X).obj KE))) :
    let Q := ((⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l))
        (finiteField l i) X).obj K⟩ :
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h)
    ∃ (b : (sections l Y).mapDerivedCategory.obj
        ((finiteSource l D hl P c target stage E).obj Q) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
          pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj KE.obj)
      (d : (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c).obj KE.obj ⟶
      (sections l Y).mapDerivedCategory.obj ((finiteTarget l c source E).obj Q)),
      IntegralSourceBoundary l D hl P c target E KE b ∧
      IntegralTargetBoundary l c source E KE d ∧
      (sections l Y).mapDerivedCategory.map (alpha.app Q) =
        b ≫ nativeScalarComponent l c source target E (change E) hs ht KE.obj ≫ d := by
  classical
  dsimp only [rationalization, Functor.comp_obj]
  obtain ⟨bE, dE, hboundE⟩ :=
    native_integral_scalar_boundaries l D hl P c source target stage E
  let Ke := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient.{u} l (PadicAlgCl l) E) X).obj KE
  let Ki := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient.{u} l (PadicAlgCl l) i) X).obj K
  have hfE := integralComponent_factorization_of_isos l D hl P c source target stage E
    change hs ht KE alpha bE dE (hboundE KE).1 (hboundE KE).2 hm
  -- Match the localization presentation used by the stage-object lemma.
  have hQ : (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj Ke =
      ((⟨i, (sfRationalConstructibleLocalization l
        (Coefficient.{u} l (PadicAlgCl l) i) X).obj Ki⟩ :
        generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h) :=
    (congrArg (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj hKE).trans
        (integralStageObject l X i E h Ki).symm
  have hh := component_transport
    (U := (PurCompactSupport.image (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj KE.obj)
    (V := (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
      PurCompactSupport.image (nativeCoefficients l) c).obj KE.obj)
    (Functor.whiskerRight alpha (sections l Y).mapDerivedCategory) hQ
    (bE.hom.app Ke)
    (nativeScalarComponent l c source target E (change E) hs ht KE.obj)
    (dE.hom.app Ke)
    (fun {_ _} b ↦ IntegralSourceBoundary l D hl P c target E KE b)
    (fun {_ _} d ↦ IntegralTargetBoundary l c source E KE d)
    (hboundE KE).1 (hboundE KE).2 hfE
  dsimp only [Ki, Ke, finiteField, Functor.comp_obj, Functor.whiskerRight_app] at hh ⊢
  exact hh

end WeilConjectures.LocallyFiniteAdicCompactSupport
