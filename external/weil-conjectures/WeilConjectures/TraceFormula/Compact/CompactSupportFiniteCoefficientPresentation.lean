/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Compact.CompactSupportSystemEvaluationDiagram
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientPullbackExact
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Finite coefficient comparisons for compact support

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks 03DI, 03DJ, 07A4, 0941.
This module specializes the ordinary system calculus to the actual pro-etale functors.
(blueprint: lem-trf-compact-support-finite-coefficient-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor

universe t u c₁ c₂ d₁ d₂ v w

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteRingMap_naturality
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f ≫
        Scheme.coefficientProEtaleDirectRingMap.{t, u} p B =
      Scheme.coefficientProEtaleDirectRingMap.{t, u} p A ≫
        ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology Z)).map
            ((constantSheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}).map f) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv _ _)
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map
      ((Functor.const Y.ProEtᵒᵖ).map f) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.coefficientProEtaleDirectRingMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext W
  exact congrArg (fun z ↦ z.app ((Scheme.proEtaleBaseChange p).op.obj W))
    ((toSheafification (ProEt.topology Z) CommRingCat.{max u (t + 1)}).naturality
      ((Functor.const Z.ProEtᵒᵖ).map f))

private abbrev ringRho {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
      ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology Z)).obj
        ((sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((constantSheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}).obj A)) :=
  ⟨Functor.whiskerRight (Scheme.coefficientProEtaleDirectRingMap.{t, u} p A).hom
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

private abbrev finiteRho {Z Y : Scheme.{t}} (p : Z ⟶ Y) (n : ℕ) :
    integralCoefficientSheaf l E Y n ⟶
      ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology Z)).obj (integralCoefficientSheaf l E Z n) :=
  ringRho p (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

attribute [local irreducible] constantSheaf presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CommRingCat.hasForgetToRingCat integralCoefficientSheaf integralCoefficientSheafSystem
  integralCoefficientSheafTransition

private theorem finiteRingMap_naturality_forget
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (f : A ⟶ B) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map f) ≫
      ringRho p B =
    ringRho p A ≫
      ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology Z)).map
        ((sheafCompose (ProEt.topology Z)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          ((constantSheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}).map f)) := by
  ext V x
  exact congrArg (fun z ↦ (z.hom.app V).hom x) (finiteRingMap_naturality p f)

private theorem finiteRho_transition {Z Y : Scheme.{t}} (p : Z ⟶ Y) (i : ℕ) :
    integralCoefficientSheafTransition l E Y i ≫ finiteRho l E p i =
      finiteRho l E p (i + 1) ≫
        ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology Z)).map
            (integralCoefficientSheafTransition l E Z i) := by
  let f : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (i + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (i + 1))) :=
    CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (i + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact finiteRingMap_naturality_forget p f

private theorem finiteRho_square {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    normalizedDVRQuotient l E Y h ≫ finiteRho l E p n =
      finiteRho l E p m ≫
        ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology Z)).map
            (normalizedDVRQuotient l E Z h) := by
  let rho : integralCoefficientSheafSystem l E Y ⟶ integralCoefficientSheafSystem l E Z ⋙
      (Scheme.proEtaleBaseChange p).sheafPushforwardContinuous RingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology Z) :=
    NatTrans.ofOpSequence (fun i ↦ finiteRho l E p i) (fun i ↦ by
      simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.comp_map] using finiteRho_transition l E p i)
  exact rho.naturality (homOfLE h).op

attribute [local irreducible] normalizedDVRQuotient
  Functor.leftAdjoint HasDerivedCategory.standard MorphismProperty.Over.pullback
attribute [local implicit_reducible] Scheme.coefficientProEtaleModuleDirectImage
  SheafOfModules.pushforward
  SheafOfModules.restrictScalars PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

-- Construct section identities with abstract rings before specializing: reducing
-- concrete coefficient-sheaf data here is expensive for the kernel.
private def ordinaryRestrictionSquare
    {C : Type c₁} {D : Type c₂} [Category.{d₁} C] [Category.{d₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    {R S : Sheaf J RingCat.{v}} {R' S' : Sheaf K RingCat.{v}}
    (a : R ⟶ S) (a' : R' ⟶ S')
    (rhoR : R' ⟶ (F.sheafPushforwardContinuous RingCat K J).obj R)
    (rhoS : S' ⟶ (F.sheafPushforwardContinuous RingCat K J).obj S)
    (square : a' ≫ rhoS = rhoR ≫
      (F.sheafPushforwardContinuous RingCat K J).map a) :
    SheafOfModules.restrictScalars.{v} a ⋙ SheafOfModules.pushforward rhoR ≅
      SheafOfModules.pushforward rhoS ⋙ SheafOfModules.restrictScalars a' := by
  refine NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_)) ?_
  · intro r
    ext x
    change rhoS.hom.app V (a'.hom.app V r) •
        (show N.val.obj (F.op.obj V) from x) =
      a.hom.app (F.op.obj V) (rhoR.hom.app V r) •
        (show N.val.obj (F.op.obj V) from x)
    exact congrArg (fun z : S.obj.obj (F.op.obj V) ↦
      z • (show N.val.obj (F.op.obj V) from x))
        (congrArg (fun f ↦ f.hom.app V r) square)
  · intros
    ext x
    rfl
  · intros
    ext V x
    rfl

private theorem ordinaryRestrictionSquare_sections
    {C : Type c₁} {D : Type c₂} [Category.{d₁} C] [Category.{d₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    {R S : Sheaf J RingCat.{v}} {R' S' : Sheaf K RingCat.{v}}
    (a : R ⟶ S) (a' : R' ⟶ S')
    (rhoR : R' ⟶ (F.sheafPushforwardContinuous RingCat K J).obj R)
    (rhoS : S' ⟶ (F.sheafPushforwardContinuous RingCat K J).obj S)
    (square : a' ≫ rhoS = rhoR ≫
      (F.sheafPushforwardContinuous RingCat K J).map a) (N : SheafOfModules.{v} S) (V : Dᵒᵖ) :
    HEq (fun x ↦ ((ordinaryRestrictionSquare F a a' rhoR rhoS square).hom.app N).val.app V x)
      (fun x : N.val.obj (F.op.obj V) ↦ x) := by
  rfl

attribute [local irreducible] ordinaryRestrictionSquare

private def finiteOrdinaryComparison {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    normalizedDVRModuleRes l E Z h ⋙ compactSupportLevelDirectImage l E p m ≅
      compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y h :=
  ordinaryRestrictionSquare (Scheme.proEtaleBaseChange p)
    (normalizedDVRQuotient l E Z h) (normalizedDVRQuotient l E Y h)
    (finiteRho l E p m) (finiteRho l E p n) (finiteRho_square l E p h)

private theorem finiteOrdinaryComparison_sections {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (N : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ) :
    HEq (fun x ↦ ((finiteOrdinaryComparison l E p h).hom.app N).val.app V x)
      (fun x : N.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x) := by
  exact ordinaryRestrictionSquare_sections _ _ _ _ _ _ N V

attribute [local irreducible] finiteOrdinaryComparison

-- Keep the categorical transport independent of the concrete coefficient models.
private theorem derivedUnit_isIso_of_eq
    {A : Type c₁} {B : Type c₂} [Category.{d₁} A] [Category.{d₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (h : F = G)
    (M : CochainComplex A ℤ) (hM : IsIso (F.rightDerivedFunctorUnitQ M)) :
    IsIso (G.rightDerivedFunctorUnitQ M) := by
  subst G
  exact hM

private theorem derivedUnit_isIso_of_iso
    {A : Type c₁} {B : Type c₂} [Category.{d₁} A] [Category.{d₂} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]
    {M N : CochainComplex A ℤ} (q : M ≅ N) (hM : IsIso (F.rightDerivedFunctorUnitQ M)) :
    IsIso (F.rightDerivedFunctorUnitQ N) := by
  let := hM
  have hq := F.rightDerivedFunctorUnitQ_naturality q.hom
  have hcomp : IsIso (DerivedCategory.Q.map
      ((F.mapHomologicalComplex (.up ℤ)).map q.hom) ≫ F.rightDerivedFunctorUnitQ N) := by
    rw [hq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map q.hom)) _

private theorem derivedUnit_isIso_of_equivalences
    {A B C D : Type (v + 1)} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (e : A ≌ C) (e' : B ≌ D) [e.functor.Additive] [e.inverse.Additive]
    [e'.functor.Additive] [e'.inverse.Additive]
    (c : F ⋙ e'.functor ≅ e.functor ⋙ G) (M : CochainComplex A ℤ)
    (hM : IsIso (G.rightDerivedFunctorUnitQ
      ((e.functor.mapHomologicalComplex (.up ℤ)).obj M))) :
    IsIso (F.rightDerivedFunctorUnitQ M) := by
  obtain ⟨b, hb⟩ := CategoryTheory.ExactDerivedSquare.square_exists F G e.functor e'.functor c
    (fun I hI ↦ by
      have := hI
      have : CochainComplex.IsKInjective
          ((e.functor.mapHomologicalComplex (.up ℤ)).obj I) := inferInstance
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance)
  have hh := (CategoryTheory.ExactDerivedSquare.square_unit_iso_iff
    F G e.functor e'.functor c b hb M).mpr hM
  let := hh
  exact isIso_of_reflects_iso _ e'.functor.mapDerivedCategory

private theorem continuousCoefficient_acyclic
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    (L : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type v) K J) [PreservesFiniteLimits L]
    (R S : Sheaf J CommRingCat.{v}) (T : Sheaf K CommRingCat.{v})
    [HasDerivedCategory.{w} (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))]
    [HasDerivedCategory.{w} (SheafOfModules.{v}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj T))]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    (rho : T ⟶ (F.sheafPushforwardContinuous CommRingCat K J).obj R)
    [(SheafOfModules.pushforward.{v} (F := F) (J := K) (K := J)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj T)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map rho)).Additive]
    (I : CochainComplex (SheafOfModules.{v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ℤ) [I.IsKInjective] :
    IsIso ((SheafOfModules.pushforward.{v} (F := F) (J := K) (K := J)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj T)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map rho)).rightDerivedFunctorUnitQ
        (((SheafOfModules.restrictScalars a).mapHomologicalComplex (.up ℤ)).obj I)) := by
  obtain ⟨f, hf⟩ := continuousRingedToposModuleDirectImage_exists F L adj R T rho
  have hsmall := CategoryTheory.ExactDerivedSquare.coefficient_canonical_acyclic
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj T)
    (fun V x y ↦ @mul_comm (R.obj.obj V) inferInstance x y)
    (fun V x y ↦ @mul_comm (S.obj.obj V) inferInstance x y)
    (fun V x y ↦ @mul_comm (T.obj.obj V) inferInstance x y) a f I
  exact derivedUnit_isIso_of_eq _ _ hf _ hsmall

private theorem modulePushforward_additive
    {C : Type c₁} {D : Type c₂} [Category.{d₁} C] [Category.{d₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : D ⥤ C} [F.IsContinuous K J]
    {R : Sheaf J RingCat.{v}} {S : Sheaf K RingCat.{v}}
    (rho : S ⟶ (F.sheafPushforwardContinuous RingCat K J).obj R) :
    (SheafOfModules.pushforward.{v} rho).Additive :=
  ⟨by intros; ext V x; rfl⟩

private theorem modelModuleEquivalence_additive (W : Scheme.{t})
    (R : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}) :
    (Scheme.moduleEquivalence.{t, u} W R).inverse.Additive ∧
      (Scheme.moduleEquivalence.{t, u} W R).functor.Additive :=
  ⟨⟨by intros; ext V x; rfl⟩, ⟨by intros; ext V x; rfl⟩⟩

private abbrev modelRingMap {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    {R : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)}}
    {S : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)}}
    (rho : S ⟶ ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology Z)).obj R) :
    (Scheme.modelEquivalence.{t, u} Y RingCat.{max u (t + 1)}).inverse.obj S ⟶
      ((Scheme.coefficientProEtaleModelBaseChange.{t, u} p).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (Scheme.coefficientProEtaleModelTopology.{t, u} Y)
        (Scheme.coefficientProEtaleModelTopology.{t, u} Z)).obj
          ((Scheme.modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.obj R) :=
  ⟨Functor.whiskerLeft AsSmall.down.op rho.hom⟩

private def modelDirectComparison {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    (R : Sheaf (ProEt.topology Z) RingCat.{max u (t + 1)})
    (S : Sheaf (ProEt.topology Y) RingCat.{max u (t + 1)})
    (rho : S ⟶ ((Scheme.proEtaleBaseChange p).sheafPushforwardContinuous
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology Z)).obj R) :
    SheafOfModules.pushforward.{max u (t + 1)} rho ⋙
        (Scheme.moduleEquivalence.{t, u} Y S).inverse ≅
      (Scheme.moduleEquivalence.{t, u} Z R).inverse ⋙
        SheafOfModules.pushforward.{max u (t + 1)} (modelRingMap p rho) := by
  refine NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _)
        (by intro r; ext x; rfl)) (by intros; ext x; rfl))) ?_
  intros
  ext V x
  rfl

private def modelRestrictionComparison (W : Scheme.{t})
    {R S : Sheaf (ProEt.topology W) RingCat.{max u (t + 1)}} (a : R ⟶ S) :
    (Scheme.moduleEquivalence.{t, u} W S).inverse ⋙
        SheafOfModules.restrictScalars.{max u (t + 1)}
          ((Scheme.modelEquivalence.{t, u} W RingCat.{max u (t + 1)}).inverse.map a) ≅
      SheafOfModules.restrictScalars.{max u (t + 1)} a ⋙
        (Scheme.moduleEquivalence.{t, u} W R).inverse := by
  refine NatIso.ofComponents (fun N ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; ext x; rfl))) ?_
  intros
  ext V x
  rfl

attribute [local irreducible] modelDirectComparison modelRestrictionComparison

private theorem finiteRestriction_acyclic
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    [∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
    [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)]
    {m n : ℕ} (h : n ≤ m)
    (J : CochainComplex (normalizedDVRModules l E Z n) ℤ) [J.IsKInjective] :
    IsIso ((compactSupportLevelDirectImage l E p m).rightDerivedFunctorUnitQ
      (((normalizedDVRModuleRes l E Z h).mapHomologicalComplex (.up ℤ)).obj J)) := by
  let S (W : Scheme.{t}) (i : ℕ) :=
    (Scheme.modelEquivalence.{t, u} W CommRingCat.{max u (t + 1)}).inverse.obj
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (i + 1)))))
  let R (W : Scheme.{t}) (i : ℕ) :=
    (sheafCompose (Scheme.coefficientProEtaleModelTopology.{t, u} W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj (S W i)
  have modelSheafify (W : Scheme.{t}) :
      HasSheafify (Scheme.coefficientProEtaleModelTopology.{t, u} W)
        AddCommGrpCat.{max u (t + 1)} := hasSheafifyEssentiallySmallSite _ _
  have modelBijective (W : Scheme.{t}) :
      (Scheme.coefficientProEtaleModelTopology.{t, u} W).WEqualsLocallyBijective
        AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have modelGrothendieck (W : Scheme.{t}) (i : ℕ) :
      IsGrothendieckAbelian.{max u (t + 1)} (SheafOfModules.{max u (t + 1)} (R W i)) :=
    SheafOfModules.isGrothendieckAbelian _
  let e (W : Scheme.{t}) (i : ℕ) :
      SheafOfModules.{max u (t + 1)} (R W i) ≌ normalizedDVRModules l E W i :=
    Scheme.moduleEquivalence.{t, u} W (integralCoefficientSheaf l E W i)
  let G : SheafOfModules.{max u (t + 1)} (R Z m) ⥤
      SheafOfModules.{max u (t + 1)} (R Y m) :=
    SheafOfModules.pushforward.{max u (t + 1)}
      ((sheafCompose (Scheme.coefficientProEtaleModelTopology.{t, u} Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (Scheme.modelCommRingMap.{t, u} p
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (m + 1))))))
  let a : R Z m ⟶ R Z n :=
    (Scheme.modelEquivalence.{t, u} Z RingCat.{max u (t + 1)}).inverse.map
      (normalizedDVRQuotient l E Z h)
  have : G.Additive := modulePushforward_additive _
  have heAdd (W : Scheme.{t}) (i : ℕ) : (e W i).inverse.Additive :=
    (modelModuleEquivalence_additive W (integralCoefficientSheaf l E W i)).1
  have heAdd' (W : Scheme.{t}) (i : ℕ) : (e W i).functor.Additive :=
    (modelModuleEquivalence_additive W (integralCoefficientSheaf l E W i)).2
  let c : compactSupportLevelDirectImage l E p m ⋙ (e Y m).inverse ≅
      (e Z m).inverse ⋙ G :=
    modelDirectComparison p (integralCoefficientSheaf l E Z m)
      (integralCoefficientSheaf l E Y m) (finiteRho l E p m)
  have hG (I : CochainComplex (SheafOfModules.{max u (t + 1)} (R Z n)) ℤ)
      [I.IsKInjective] :
      IsIso (G.rightDerivedFunctorUnitQ
        (((SheafOfModules.restrictScalars a).mapHomologicalComplex (.up ℤ)).obj I)) := by
    let F := Scheme.coefficientProEtaleModelBaseChange.{t, u} p
    let TZ := Scheme.coefficientProEtaleModelTopology.{t, u} Z
    let TY := Scheme.coefficientProEtaleModelTopology.{t, u} Y
    have : PreservesFiniteLimits F := by
      dsimp [F, Scheme.coefficientProEtaleModelBaseChange]
      infer_instance
    have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
    have : PreservesFiniteLimits (F.sheafPullback (Type (max u (t + 1))) TY TZ) :=
      Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
        F (Type (max u (t + 1))) TY TZ
    exact continuousCoefficient_acyclic F
      (F.sheafPullback (Type (max u (t + 1))) TY TZ)
      (F.sheafAdjunctionContinuous (Type (max u (t + 1))) TY TZ)
      (S Z m) (S Z n) (S Y m) a
      (Scheme.modelCommRingMap.{t, u} p
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (m + 1))))) I
  let s : (e Z n).inverse ⋙ SheafOfModules.restrictScalars a ≅
      normalizedDVRModuleRes l E Z h ⋙ (e Z m).inverse :=
    modelRestrictionComparison Z (normalizedDVRQuotient l E Z h)
  let I := ((e Z n).inverse.mapHomologicalComplex (.up ℤ)).obj J
  have : CochainComplex.IsKInjective I := inferInstance
  have hsource : IsIso (G.rightDerivedFunctorUnitQ
      ((((e Z n).inverse ⋙ SheafOfModules.restrictScalars a).mapHomologicalComplex
        (.up ℤ)).obj J)) := hG I
  let q := (NatIso.mapHomologicalComplex s (.up ℤ)).app J
  have htarget : IsIso (G.rightDerivedFunctorUnitQ
      (((e Z m).inverse.mapHomologicalComplex (.up ℤ)).obj
        (((normalizedDVRModuleRes l E Z h).mapHomologicalComplex (.up ℤ)).obj J))) :=
    derivedUnit_isIso_of_iso G q hsource
  have : (e Z m).symm.functor.Additive := heAdd Z m
  have : (e Z m).symm.inverse.Additive := heAdd' Z m
  have : (e Y m).symm.functor.Additive := heAdd Y m
  have : (e Y m).symm.inverse.Additive := heAdd' Y m
  exact derivedUnit_isIso_of_equivalences (compactSupportLevelDirectImage l E p m) G
    (e Z m).symm (e Y m).symm c _ htarget

/-- Finite-coefficient restriction commutes with the actual direct image, with its
ordinary section and arbitrary-resolution normalizations. This assertion involves
neither strict systems nor an open immersion.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03D2, 03DA and 07A4
(blueprint: lem-trf-compact-support-finite-coefficient-presentation).
Proof: the constant-section structure maps for p are natural in the quotient ring.
Apply this naturality to B_m → B_n. Restriction of scalars changes only the action,
so the comparison of sectionwise direct images is the identity on every section.
Transport the module sheaves to the coefficient-sized small models of the sites.
There the ringed-topos coefficient-acyclicity theorem shows that restricting a
K-injective complex gives a direct-image-acyclic complex. Exact module equivalences
and naturality of the derived unit transport this assertion back to the original
sites. Apply the normalized derived-square construction to the ordinary comparison.
For a K-injective J and any K-injective resolution r of its coefficient restriction,
naturality of the derived unit at r and cancellation give the displayed equality.
This argument needs no preservation of K-injectivity by restriction and includes n=m. -/
theorem compactSupportFiniteCoefficientPresentation
    {Z Y : Scheme.{t}} (p : Z ⟶ Y)
    [∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
    [∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E Z n)] :
    ∃ (a : ∀ {m n : ℕ} (h : n ≤ m),
        normalizedDVRModuleRes l E Z h ⋙ compactSupportLevelDirectImage l E p m ≅
          compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y h)
      (d : ∀ {m n : ℕ} (h : n ≤ m),
        normalizedDVRRes l E Z h ⋙
            (compactSupportLevelDirectImage l E p m).rightDerivedFunctor ≅
          (compactSupportLevelDirectImage l E p n).rightDerivedFunctor ⋙
            normalizedDVRRes l E Y h),
      (∀ {m n : ℕ} (h : n ≤ m)
              (N : normalizedDVRModules l E Z n) (V : Y.ProEtᵒᵖ),
              HEq (fun x ↦ ((a h).hom.app N).val.app V x)
                (fun x : N.val.obj ((Scheme.proEtaleBaseChange p).op.obj V) ↦ x)) ∧
      (∀ {m n : ℕ} (h : n ≤ m),
        letI := normalizedDVRModuleRes_limits l E Z h
        letI := normalizedDVRModuleRes_colimits l E Z h
        letI := normalizedDVRModuleRes_limits l E Y h
        letI := normalizedDVRModuleRes_colimits l E Y h
        CompactSupportDerivedSquareNormalization
            (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p m)
            (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h)
            (a h)
              (d h)) := by
  classical
  let a : ∀ {m n : ℕ} (h : n ≤ m),
      normalizedDVRModuleRes l E Z h ⋙ compactSupportLevelDirectImage l E p m ≅
        compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y h :=
    fun h ↦ finiteOrdinaryComparison l E p h
  have comparisons (m n : ℕ) (h : n ≤ m) :=
    CategoryTheory.ExactDerivedSquare.square_exists
      (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p m)
      (normalizedDVRModuleRes l E Z h) (normalizedDVRModuleRes l E Y h) (a h).symm
  have hacyc (m n : ℕ) (h : n ≤ m)
      (J : CochainComplex (normalizedDVRModules l E Z n) ℤ) (hJ : J.IsKInjective) :
      IsIso ((compactSupportLevelDirectImage l E p m).rightDerivedFunctorUnitQ
        (((normalizedDVRModuleRes l E Z h).mapHomologicalComplex (.up ℤ)).obj J)) := by
    have := hJ
    exact finiteRestriction_acyclic l E p h J
  choose b hb using fun m n h ↦ comparisons m n h (hacyc m n h)
  refine ⟨a, fun {m n} h ↦ (b m n h).symm, ?_, ?_⟩
  · intro m n h N V
    exact finiteOrdinaryComparison_sections l E p h N V
  · intro m n h J hJ I hI r hr
    let G := compactSupportLevelDirectImage l E p n
    let G' := compactSupportLevelDirectImage l E p m
    let H := normalizedDVRModuleRes l E Z h
    let K := normalizedDVRModuleRes l E Y h
    have hu := hb m n h J
    change K.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ J) ≫
        (b m n h).hom.app (DerivedCategory.Q.obj J) ≫
        G'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app J) =
      K.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (a h).symm (.up ℤ)).hom.app J) ≫
        G'.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj J) at hu
    rw [Functor.rightDerivedFunctorUnitQ_eq] at hu
    have hn := G'.rightDerivedFunctorUnitQ_naturality r
    rw [Functor.rightDerivedFunctorUnitQ_eq] at hn
    apply (cancel_mono (G'.rightDerivedFunctorObjQIso I).inv).mp
    simp only [Iso.symm_hom, Category.assoc]
    erw [hn]
    have hh := congrArg (fun f ↦
      (b m n h).inv.app (DerivedCategory.Q.obj J) ≫
        K.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso J).hom ≫ f ≫
        G'.rightDerivedFunctor.map (DerivedCategory.Q.map r)) hu
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id] at hh
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at hh
    simpa only [G, G', H, K, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      NatIso.mapHomologicalComplex, Iso.symm_hom] using hh.symm

end WeilConjectures
