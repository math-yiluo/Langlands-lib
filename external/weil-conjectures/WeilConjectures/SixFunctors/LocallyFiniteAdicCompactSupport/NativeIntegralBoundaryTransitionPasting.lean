/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralSourceBoundaryTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedScalarMateTransition
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralTargetBoundaryTransition

/-! # Pasting the three normalized integral boundary squares -/

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

private theorem cast_source_arrow {C : Type*} [Category C]
    {A A' B : C} (p : A = A') (f : A' ⟶ B) : ArrowHEq (eqToHom p ≫ f) f := by
  subst A'
  exact ⟨rfl, rfl, heq_of_eq (Category.id_comp _)⟩

private theorem family_arrow_congr {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (a : ∀ M, F.obj M ⟶ H.obj M) {M N : C} (h : M = N) :
    ArrowHEq (a M) (a N) := by
  cases h
  exact ArrowHEq.refl _

private theorem normalized_three_squares_heq {C : Type*} [Category C]
    {A B U V V' W Z Z' A' B' : C}
    (t : A ⟶ A') (r : B ⟶ B')
    (bi : A ⟶ U) (bE : A' ⟶ V') (qi : U ⟶ W)
    (qE : V' ⟶ Z') (qEcanonical : V ⟶ Z)
    (di : W ⟶ B) (dE : Z' ⟶ B') (dEcanonical : Z ⟶ B')
    (u : U ⟶ V) (v : W ⟶ Z) (mi : A ⟶ B) (mE : A' ⟶ B')
    (hi : mi = bi ≫ qi ≫ di) (hE : mE = bE ≫ qE ≫ dE)
    (hb : ArrowHEq (t ≫ bE) (bi ≫ u))
    (hq : u ≫ qEcanonical = qi ≫ v) (hd : v ≫ dEcanonical = di ≫ r)
    (he : ArrowHEq qE qEcanonical) (hde : ArrowHEq dE dEcanonical) :
    t ≫ mE = mi ≫ r := by
  have hh := hb.comp (he.comp hde)
  have hc : t ≫ (bE ≫ qE ≫ dE) = bi ≫ u ≫ qEcanonical ≫ dEcanonical := by
    simpa only [Category.assoc] using eq_of_heq hh.heq
  rw [hi, hE]
  refine hc.trans ?_
  calc
    _ = bi ≫ (u ≫ qEcanonical) ≫ dEcanonical := by simp only [Category.assoc]
    _ = bi ≫ (qi ≫ v) ≫ dEcanonical := by rw [hq]
    _ = bi ≫ qi ≫ (v ≫ dEcanonical) := by simp only [Category.assoc]
    _ = _ := by rw [hd]; simp only [Category.assoc]

-- The three square interfaces use several equivalent coefficient presentations.
/-- The three boundary transition squares paste on their prescribed factors.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
Proof: the first boundary square moves the stage map past the initial boundary.
The completed-to-native scalar-mate square then moves the ordinary finite scalar
map past the native scalar component. The final boundary square moves it past
the last boundary. Transport the E component and final boundary along the given
underlying-object equality, using endpoint-recorded equality, and compose the three
squares by associativity. This statement has no alpha family or rational component morphisms.
(blueprint: lem-sf-native-integral-boundary-transition-pasting). -/
theorem integralBoundaryTransitionPasting [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c)
    (change : ∀ E : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (hs : ∀ E, (change E).map X = (source.coefficient E).integralMap l X)
    (ht : ∀ E, (change E).map Y = (target.coefficient E).integralMap l Y)
    (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) i) X)
    (KE : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    (hKE : (PurCompactSupport.finiteTorIntegralInclusion l
        (Coefficient.{u} l (PadicAlgCl l) E) X).obj KE =
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
        i E h).obj ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient.{u} l (PadicAlgCl l) i) X).obj K))
    (hM : KE.obj = (integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
      (Coefficient.{u} l (PadicAlgCl l) E)
      (coefficientInclusion l (PadicAlgCl l) i E h) X).obj K.obj) :
    let Ai := (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l))
      (finiteField l i) X).obj K
    let Q := (⟨i, Ai⟩ :
      generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X).toStage h
    ∀ (bi : (sections l Y).mapDerivedCategory.obj
        ((finiteSource l D hl P c target stage i).obj Ai) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) i)) c ⋙
        pbcDerivedExtend ((target.coefficient i).integralMap l Y)).obj K.obj)
      (bE : (sections l Y).mapDerivedCategory.obj
        ((finiteSource l D hl P c target stage E).obj Q) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj KE.obj)
      (di : (pbcDerivedExtend ((source.coefficient i).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ⟶
      (sections l Y).mapDerivedCategory.obj ((finiteTarget l c source i).obj Ai))
      (dE : (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c).obj KE.obj ⟶
      (sections l Y).mapDerivedCategory.obj ((finiteTarget l c source E).obj Q)),
      IntegralSourceBoundary l D hl P c target i K bi →
      IntegralSourceBoundary l D hl P c target E KE bE →
      IntegralTargetBoundary l c source i K di →
      IntegralTargetBoundary l c source E KE dE →
      (sections l Y).mapDerivedCategory.map
        ((stage.system.functor ⋙ target.J).map
          ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨i, Ai⟩ h).hom)) ≫
        (bE ≫ nativeScalarComponent l c source target E (change E) (hs E) (ht E) KE.obj ≫
          dE) =
      (bi ≫ nativeScalarComponent l c source target i (change i) (hs i) (ht i) K.obj ≫
          di) ≫ (sections l Y).mapDerivedCategory.map
        ((source.J ⋙ actual l c).map
          ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨i, Ai⟩ h).hom)) := by
  dsimp only
  intro bi bE di dE hbi hbE hdi hdE
  have hb := integralSourceBoundary_transition l D hl P c target stage i E h K KE hM
    bi bE hbi hbE
  have hd := integralTargetBoundary_transition l c source i E h K KE hKE
    di dE hdi hdE
  have hq := nativeScalarComponent_transition l c source target change hs ht i E h K.obj
  let p := congrArg (fun M : DerivedCategory
    (scalarReductionSource l (Coefficient.{u} l (PadicAlgCl l) E) X) ↦
      (PurCompactSupport.image (nativeCoefficients l) c).obj
        ((pbcDerivedExtend ((source.coefficient E).integralMap l X)).obj M)) hM.symm
  let dEcast := eqToHom p ≫ dE
  have hqe := family_arrow_congr
    (F := PurCompactSupport.image (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y))
    (H := pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
      PurCompactSupport.image (nativeCoefficients l) c)
    (nativeScalarComponent l c source target E (change E) (hs E) (ht E)) hM
  let σ := (StageSystem.isoToStage
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
    ⟨i, (rationalization.{u, u} l (ULift.{u} (PadicAlgCl l)) (finiteField l i) X).obj K⟩ h).hom
  have hdiagram := normalized_three_squares_heq
    (C := DerivedCategory (proEtaleRingModules Y (ringSheaf l Y)))
    ((sections l Y).mapDerivedCategory.map ((stage.system.functor ⋙ target.J).map σ))
    ((sections l Y).mapDerivedCategory.map ((source.J ⋙ actual l c).map σ))
    bi bE
    (nativeScalarComponent l c source target i (change i) (hs i) (ht i) K.obj)
    (nativeScalarComponent l c source target E (change E) (hs E) (ht E) KE.obj)
    (nativeScalarComponent l c source target E (change E) (hs E) (ht E)
      ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) i)
        (Coefficient.{u} l (PadicAlgCl l) E)
        (coefficientInclusion l (PadicAlgCl l) i E h) X).obj K.obj))
    di dE dEcast
    (supportScalarTransition l c target i E h K.obj)
    ((PurCompactSupport.image (nativeCoefficients l) c).map
      (nativeScalarTransition l X source i E h K.obj))
    (bi ≫ nativeScalarComponent l c source target i (change i) (hs i) (ht i) K.obj ≫ di)
    (bE ≫ nativeScalarComponent l c source target E (change E) (hs E) (ht E) KE.obj ≫ dE)
    rfl rfl hb hq (eq_of_heq hd.heq) hqe
      (cast_source_arrow p dE).symm
  exact hdiagram

end WeilConjectures.LocallyFiniteAdicCompactSupport
