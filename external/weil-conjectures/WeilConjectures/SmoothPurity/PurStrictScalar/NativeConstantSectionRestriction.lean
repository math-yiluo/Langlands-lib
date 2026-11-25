/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # The explicit constant section tower and its scalar-restriction interface

Source: Stacks Project, Modules on Sites, Tags 03CZ and 03DA; Cohomology on Sites, 0940.
(blueprint: def-pur-native-constant-section-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
universe u v c d c' d'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual horizontal map between two vertical inclusions.
Source: Stacks 0940 (blueprint: def-pur-native-constant-section-restriction). -/
def nativeSectionVertical {C : Type c} [Category.{d} C]
    {m n : ℕ} (h : n ≤ m) : Prod.sectR n C ⟶ Prod.sectR m C where
  app U := Prod.mkHom (homOfLE h) (𝟙 U)
  naturality := by
    intro U V f
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · change f ≫ 𝟙 V = 𝟙 U ≫ f
      simp

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeConstantLevelMap (W : Scheme.{u}) (n : ℕ) :=
  integralConstantQuotientOfUniverses l E W n ≫
    eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
theorem nativeConstantLevelMap_horizontal (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    nativeConstantLevelMap l E W m ≫
      (Functor.sheafPushforwardContinuousNatTrans (nativeSectionVertical h) RingCat.{u + 1}
        (ProEt.topology W) (coefficientSequenceTopology (ProEt.topology W))).app
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W)) = nativeConstantLevelMap l E W n := by
  have he : nativeSectionVertical (C := W.ProEt) h = verticalNat h := rfl
  rw [he]
  dsimp only [nativeConstantLevelMap]
  rw [Category.assoc, coefficientSequenceRingHorizontal, ← Category.assoc]
  exact congrArg (fun q ↦ q ≫ eqToHom
    (coefficientSequenceEvaluationRing_eq l E W n).symm)
      ((integralConstantConeOfUniverses l E W).w (homOfLE h).op)

/-- Section maps determine a morphism of module sheaves.
Source: Stacks 03CZ (blueprint: def-pur-native-constant-section-restriction). -/
theorem nativeSectionHom_ext {C : Type c} [Category.{d} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{v}}
    {M N : SheafOfModules.{v} R} (f g : M ⟶ N)
    (h : ∀ U x, f.val.app U x = g.val.app U x) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact LinearMap.ext (h U)

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeSectionTowerTransition
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{v}) (A : Sheaf J RingCat.{v})
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v}
      J (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m), ρ m ≫
      (Functor.sheafPushforwardContinuousNatTrans (nativeSectionVertical h) RingCat.{v}
        J (coefficientSequenceTopology J)).app R = ρ n)
    {m n : ℕ} (h : n ≤ m) :
    SheafOfModules.pushforward.{v} (ρ m) ⟶ SheafOfModules.pushforward.{v} (ρ n) :=
  SheafOfModules.pushforwardNatTrans (ρ m) (nativeSectionVertical h) ≫
    (SheafOfModules.pushforwardCongr (hρ h)).hom

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeSectionTowerFunctor
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{v}) (A : Sheaf J RingCat.{v})
    [∀ n : ℕ, (Prod.sectR n C).IsContinuous J (coefficientSequenceTopology J)]
    (ρ : ∀ n : ℕ, A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous RingCat.{v}
      J (coefficientSequenceTopology J)).obj R)
    (hρ : ∀ {m n : ℕ} (h : n ≤ m), ρ m ≫
      (Functor.sheafPushforwardContinuousNatTrans (nativeSectionVertical h) RingCat.{v}
        J (coefficientSequenceTopology J)).app R = ρ n) :
    SheafOfModules.{v} R ⥤ (ℕᵒᵖ ⥤ SheafOfModules.{v} A) :=
  { obj N :=
      { obj n := (SheafOfModules.pushforward (ρ n.unop)).obj N
        map {m n} f := (nativeSectionTowerTransition J R A ρ hρ (leOfHom f.unop)).app N
        map_id n := by
          apply nativeSectionHom_ext
          intro V x
          change N.val.presheaf.map _ x = x
          have he : (nativeSectionVertical (Nat.le_refl n.unop)).app V.unop = 𝟙 _ := by
            apply Prod.hom_ext
            · apply Subsingleton.elim
            · rfl
          change N.val.presheaf.map ((nativeSectionVertical _).app V.unop).op x = x
          rw [he, op_id, N.val.presheaf.map_id]
          rfl
        map_comp {k m n} f g := by
          apply nativeSectionHom_ext
          intro V x
          change N.val.presheaf.map _ x = N.val.presheaf.map _ (N.val.presheaf.map _ x)
          have he :
              ((nativeSectionVertical (leOfHom (f ≫ g).unop)).app V.unop).op =
                ((nativeSectionVertical (leOfHom f.unop)).app V.unop).op ≫
                  ((nativeSectionVertical (leOfHom g.unop)).app V.unop).op := by
            apply Quiver.Hom.unop_inj
            apply Prod.hom_ext
            · exact Subsingleton.elim _ _
            · change 𝟙 V.unop = (𝟙 V.unop) ≫ 𝟙 V.unop
              rw [Category.id_comp]
          exact (congrArg (fun h ↦ N.val.presheaf.map h
            (show N.val.obj (op (k.unop, V.unop)) from x)) he).trans
              (N.val.presheaf.map_comp_apply _ _ x) }
    map f :=
      { app n := (SheafOfModules.pushforward (ρ n.unop)).map f
        naturality {m n} g :=
          ((nativeSectionTowerTransition J R A ρ hρ (leOfHom g.unop)).naturality f).symm }
    map_id N := by
      apply NatTrans.ext
      funext n
      exact (SheafOfModules.pushforward (ρ n.unop)).map_id N
    map_comp f g := by
      apply NatTrans.ext
      funext n
      exact (SheafOfModules.pushforward (ρ n.unop)).map_comp f g }

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeConstantSectionTower (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤
      Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W :=
  nativeSectionTowerFunctor (ProEt.topology W)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E W)) (integralConstantRingOfUniverses l E W)
    (nativeConstantLevelMap l E W) (fun h ↦ nativeConstantLevelMap_horizontal l E W h)

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativePushforwardRestrictIso
    {C : Type c} {D : Type c'} [Category.{d} C] [Category.{d'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K]
    {A B : Sheaf J RingCat.{v}} {R : Sheaf K RingCat.{v}}
    (ε : B ⟶ (F.sheafPushforwardContinuous RingCat.{v} J K).obj R) (ψ : A ⟶ B) :
    SheafOfModules.pushforward.{v} ε ⋙ SheafOfModules.restrictScalars ψ ≅
      SheafOfModules.pushforward.{v} (F := F) (ψ ≫ ε) := Iso.refl _

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeConstantScalarMap (n : ℕ) :
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      compactSupportSystemLevel l E n :=
  CommRingCat.ofHom (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).ulift

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
theorem nativeConstantScalarMap_compatibility (n : ℕ) :
    nativeConstantScalarMap l E (n + 1) ≫ compactSupportSystemQuotient l E n =
      nativeConstantScalarMap l E n := by
  apply CommRingCat.hom_ext
  ext x
  rfl

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeConstantScalarLevel (W : Scheme.{u}) (n : ℕ) :
    nativeConstantSectionTower l E W ⋙
      (evaluation ℕᵒᵖ (AlgebraicGeometry.ProEtale.StrictTower.Modules
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)).obj (op n) ≅
      ProEtale.VaryingRing.eval (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) W n ⋙
      SemilinearSections.res (ProEtale.VaryingRing.ordinaryScalarMap
        (compactSupportSystemLevel l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (nativeConstantScalarMap l E) W n) :=
  (nativePushforwardRestrictIso
    (eqToHom (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
      (ProEt.topology W) (ProEtale.VaryingRing.coefficients (compactSupportSystemLevel l E) W)
      (ProEtale.VaryingRing.coefficientTransition (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) W) n).symm)
    ((sheafCompose (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (ProEtale.VaryingRing.ordinaryScalarMap (compactSupportSystemLevel l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (nativeConstantScalarMap l E) W n))).symm

/-- Explicit section construction and its coefficient compatibility.
Source: Stacks 03CZ, 03DA and 0940
(blueprint: def-pur-native-constant-section-restriction). -/
def nativeConstantScalarRestriction
    (hadd : ∀ W : Scheme.{u}, (nativeConstantSectionTower l E W).Additive)
    (hlim : ∀ W : Scheme.{u}, PreservesFiniteLimits (nativeConstantSectionTower l E W))
    (hcolim : ∀ W : Scheme.{u}, PreservesFiniteColimits (nativeConstantSectionTower l E W)) :
    ProEtale.VaryingRing.OrdinaryScalarRestriction (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (nativeConstantScalarMap l E) where
  rho := nativeConstantSectionTower l E
  additive := hadd
  limits := hlim
  colimits := hcolim
  level W n := nativeConstantScalarLevel l E W n
  level_sections := by intros; rfl
  transitions := by intros; rfl

end WeilConjectures.PurStrictScalar
