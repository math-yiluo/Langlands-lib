/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions
public import WeilConjectures.CategoryTheory.ArrowHEq.ArrowHEq

import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralStageObject

/-! # The canonical target-realization transition square -/

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

private theorem paste_after_functor {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B U V : C} {S T R : D}
    (ei : A ≅ U) (eE : B ≅ V) (v : U ⟶ V)
    (di : H.obj A ⟶ S) (dE : H.obj B ⟶ T) (r : S ⟶ R)
    (h : ArrowHEq (H.map (ei.hom ≫ v ≫ eE.inv) ≫ dE) (di ≫ r)) :
    ArrowHEq (H.map v ≫ (H.map eE.inv ≫ dE))
      ((H.map ei.inv ≫ di) ≫ r) := by
  have hp := (ArrowHEq.refl (H.map ei.inv)).comp h
  have hc : H.map ei.inv ≫ (H.map (ei.hom ≫ v ≫ eE.inv) ≫ dE) =
      H.map v ≫ (H.map eE.inv ≫ dE) := by
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun q ↦ H.map q ≫ dE) (Iso.inv_hom_id_assoc ei (v ≫ eE.inv))
  exact (show ArrowHEq _ _ from ⟨rfl, rfl, heq_of_eq hc.symm⟩).trans
    (hp.trans ⟨rfl, rfl, heq_of_eq (Category.assoc (H.map ei.inv) di r).symm⟩)

private theorem arrow_of_heq {C : Type*} [Category C]
    {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (hA : A = A') (hB : B = B') (h : HEq f g) : ArrowHEq f g := ⟨hA, hB, h⟩

private theorem fourArrow_regroup {C : Type*} [Category C]
    {A B D E F : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    a ≫ b ≫ c ≫ d = a ≫ (b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem app_arrow_congr {C D : Type*} [Category C] [Category D]
    {F H : C ⥤ D} (α : F ⟶ H) {A B : C} (h : A = B) :
    ArrowHEq (α.app A) (α.app B) := by
  cases h
  exact ArrowHEq.refl _

-- Compare the common-field normalization with the canonical target realization.
/-- The inverse integral realization and operation transport respect stage change.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
Proof: common_field expresses the realized stage transition through the two integral
realization isomorphisms and the native scalar map. The stage-object formula identifies
its target with raw localization of the integral transition. Naturality of inverse
operationTransport moves this realized transition past the final transport. Precompose
by the inverse initial integral realization and cancel its composite with the forward
realization. Functoriality and associativity give the two canonical target boundaries.
(blueprint: lem-sf-native-integral-canonical-target-transition). -/
theorem canonicalIntegralTargetTransition [G : NativeGeometry.{u} l]
    (source : Realization l X) (i E : Index l (PadicAlgCl l)) (h : i ≤ E)
    (Ki : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) i) X) :
    let Ke := (GeneralAlgebraicallyClosedCoefficients.integralTransition l
      (PadicAlgCl l) X i E h).obj Ki
    let Ai := (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) i) X).obj Ki
    let Ae := (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) E) X).obj Ke
    ArrowHEq
      ((PurCompactSupport.image (nativeCoefficients l) c).map
          (nativeScalarTransition l X source i E h Ki.obj) ≫
        ((PurCompactSupport.image (nativeCoefficients l) c).map
            ((source.integral E).inv.app Ke) ≫
          (operationTransport l c).inv.app (source.J.obj
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj Ae))))
      (((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral i).inv.app Ki) ≫
        (operationTransport l c).inv.app (source.J.obj
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := PadicAlgCl l) (Y := X) i).obj Ai))) ≫
        (actual l c ⋙ (sections l Y).mapDerivedCategory).map
          (source.J.map ((StageSystem.isoToStage
            (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X)
            ⟨i, Ai⟩ h).hom))) := by
  dsimp only
  let Ke := (GeneralAlgebraicallyClosedCoefficients.integralTransition l (PadicAlgCl l) X
    i E h).obj Ki
  have hce := (source.common_field i E h Ki).trans
    (heq_of_eq (fourArrow_regroup
      (C := DerivedCategory (proEtaleRingModules X (ringSheaf l X))) _ _ _ _))
  have hstage := integralStageObject l X i E h Ki
  have hpair := congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj hstage
  let A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
    ⟨i, (sfRationalConstructibleLocalization l
      (Coefficient.{u} l (PadicAlgCl l) i) X).obj Ki⟩
  let B := (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj (A.toStage h)
  let σ := StageSystem.isoToStage
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X) A h
  let t := source.J.map σ.hom
  have hJ := congrArg source.J.obj hpair
  have hc := arrow_of_heq
    (C := DerivedCategory (proEtaleRingModules X (ringSheaf l X)))
    (A := (sections l X).mapDerivedCategory.obj (source.J.obj A))
    (B := (sections l X).mapDerivedCategory.obj (source.J.obj B))
    (A' := (sections l X).mapDerivedCategory.obj (source.J.obj A))
    (B' := (sections l X).mapDerivedCategory.obj
      (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj Ke))))
    (f := (sections l X).mapDerivedCategory.map
      (X := source.J.obj A) (Y := source.J.obj B) t)
    rfl (congrArg (sections l X).mapDerivedCategory.obj hJ) hce
  have ha := (hc.map (PurCompactSupport.image (nativeCoefficients l) c)).comp
    (app_arrow_congr (operationTransport l c).inv hJ)
  have hn := (operationTransport l c).inv.naturality t
  have hh := ha.symm.trans (show ArrowHEq _ _ from ⟨rfl, rfl, heq_of_eq hn⟩)
  have hp := paste_after_functor (PurCompactSupport.image (nativeCoefficients l) c)
    ((source.integral i).app Ki) ((source.integral E).app Ke)
    (nativeScalarTransition l X source i E h Ki.obj)
    ((operationTransport l c).inv.app (source.J.obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) i).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) i) X).obj Ki))))
    ((operationTransport l c).inv.app (source.J.obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
          ((sfRationalConstructibleLocalization l
            (Coefficient.{u} l (PadicAlgCl l) E) X).obj Ke))))
    ((actual l c ⋙ (sections l Y).mapDerivedCategory).map t) hh
  exact hp

end WeilConjectures.LocallyFiniteAdicCompactSupport
