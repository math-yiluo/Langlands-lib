/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralDerivedOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear

/-! # Constant-scalar linearity of the normalized integral pullback

Source: the rational paragraph of `prose-03-02`;
Bhatt--Scholze, Lemma 6.5.9(4), and Stacks Tag 099N(5).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

open CategoryTheory.Limits Opposite

private theorem adjoint_action {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (μ : 𝟭 C ⟶ 𝟭 C) (ν : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ N, R.map (ν.app N) = μ.app (R.obj N)) (M : C) :
    L.map (μ.app M) = ν.app (L.obj M) := by
  apply (adj.homEquiv M (L.obj M)).injective
  calc
    adj.homEquiv M (L.obj M) (L.map (μ.app M)) =
        adj.homEquiv M (L.obj M) (L.map (μ.app M) ≫ 𝟙 _) :=
      congrArg (adj.homEquiv M (L.obj M)) (CategoryTheory.Category.comp_id _).symm
    _ = μ.app M ≫ adj.homEquiv M (L.obj M) (𝟙 _) :=
      adj.homEquiv_naturality_left (μ.app M) (𝟙 _)
    _ = μ.app M ≫ adj.unit.app M :=
      congrArg (fun k ↦ μ.app M ≫ k) (adj.homEquiv_id M)
    _ = adj.unit.app M ≫ μ.app (R.obj (L.obj M)) :=
      (μ.naturality (adj.unit.app M)).symm
    _ = adj.unit.app M ≫ R.map (ν.app (L.obj M)) :=
      congrArg (fun k ↦ adj.unit.app M ≫ k) (h (L.obj M)).symm
    _ = adj.homEquiv M (L.obj M) (ν.app (L.obj M)) :=
      (adj.homEquiv_unit M (L.obj M) (ν.app (L.obj M))).symm

section Representatives

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteConstant_naturality (W : Scheme.{u}) (n : ℕ)
    {U V : W.ProEtᵒᵖ} (g : U ⟶ V) (a : Padic.coefficientExtensionIntegers l E) :
    (integralCoefficientSheaf l E W n).obj.map g
      (integralScalarFiniteConstant l E W n U a) =
        integralScalarFiniteConstant l E W n V a := by
  exact (congrArg (fun k ↦ k.hom (ULift.up
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    ((toSheafify (Scheme.ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality g)).symm

private noncomputable def finiteAction (W : Scheme.{u}) (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (integralOperationsFiniteModules l E W n) ⟶
      𝟭 (integralOperationsFiniteModules l E W n) where
  app M :=
    { val :=
        { app := fun U ↦ by
            let : CommRing ((integralCoefficientSheaf l E W n).obj.obj U) :=
              inferInstanceAs (CommRing
                ((integralCoefficientCommRingSheaf l E W n).obj.obj U))
            exact ModuleCat.ofHom
              { toFun := fun x ↦ integralScalarFiniteConstant l E W n U a • x
                map_add' := smul_add _
                map_smul' := fun r x ↦ smul_comm _ r x }
          naturality := by
            intro U V g
            ext x
            change integralScalarFiniteConstant l E W n V a • M.val.map g x =
              M.val.map g (integralScalarFiniteConstant l E W n U a • x)
            rw [M.val.map_smul, finiteConstant_naturality] } }
  naturality := by
    intro M N g
    ext U x
    exact ((g.val.app U).hom.map_smul
      (integralScalarFiniteConstant l E W n U a) x).symm

private theorem reduction_action (W : Scheme.{u}) (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) (M : integralTowerModules l E W) :
    (unrestrictedIntegralReductionFunctor l E W n).map
        ((integralScalarModuleAction l E W a).app M) =
      (finiteAction l E W n a).app
        ((unrestrictedIntegralReductionFunctor l E W n).obj M) := by
  apply adjoint_action (scalarReductionExtension_adjunction l E W n).choose
    (integralScalarModuleAction l E W a) (finiteAction l E W n a)
  intro N
  ext U x
  change integralScalarFiniteConstant l E W n U a • (show N.val.obj U from x) =
    ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) • (show N.val.obj U from x)
  rw [show ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) = integralScalarFiniteConstant l E W n U a
    from (integralScalarConstant_existsUnique l E W U a).exists.choose_spec n]

private theorem directRingMap_constant {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEtᵒᵖ) (a : Padic.coefficientExtensionIntegers l E) :
    ((Scheme.coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app U)
        (integralScalarFiniteConstant l E Y n U a) =
      integralScalarFiniteConstant l E X n ((Scheme.proEtaleBaseChange f).op.obj U) a := by
  let A := CommRingCat.of
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  let target := ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
    CommRingCat.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A)
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) target).apply_symm_apply
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ (k.app U).hom (ULift.up
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a))) h

private theorem finitePullback_action {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E)
    (M : integralOperationsFiniteModules l E Y n) :
    (integralOperationsLevelPullback l E f n).map ((finiteAction l E Y n a).app M) =
      (finiteAction l E X n a).app ((integralOperationsLevelPullback l E f n).obj M) := by
  apply adjoint_action (Scheme.coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (finiteAction l E Y n a) (finiteAction l E X n a)
  intro N
  ext U x
  change integralScalarFiniteConstant l E X n ((Scheme.proEtaleBaseChange f).op.obj U) a •
      (show N.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from x) =
    ((Scheme.coefficientProEtaleDirectRingMap.{u, u} f
      (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app U)
      (integralScalarFiniteConstant l E Y n U a) •
        (show N.val.obj ((Scheme.proEtaleBaseChange f).op.obj U) from x)
  rw [directRingMap_constant]

private theorem restrict_action (W : Scheme.{u}) (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E)
    (M : integralOperationsFiniteModules l E W n) :
    (integralCompletedRestrict l E W n).map ((finiteAction l E W n a).app M) =
      (integralScalarModuleAction l E W a).app ((integralCompletedRestrict l E W n).obj M) := by
  ext U x
  change integralScalarFiniteConstant l E W n U a • (show M.val.obj U from x) =
    ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) • (show M.val.obj U from x)
  rw [show ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom
      (integralScalarConstant l E W U a) = integralScalarFiniteConstant l E W n U a
    from (integralScalarConstant_existsUnique l E W U a).exists.choose_spec n]

attribute [local instance] coefficientModuleLinear

private noncomputable def pullModule {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙ integralOperationsLevelPullback l E f n ⋙
    integralCompletedRestrict l E X n

private theorem moduleAction_eq (W : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E)
    (M : integralTowerModules l E W) :
    (integralScalarModuleAction l E W a).app M = a • 𝟙 M := by
  ext U x
  rfl

private instance pullModule_linear {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (pullModule l E f n).Linear (Padic.coefficientExtensionIntegers l E) := by
  rw [Functor.linear_iff]
  intro M a
  rw [← moduleAction_eq, ← moduleAction_eq]
  dsimp only [pullModule, Functor.comp_map, Functor.comp_obj]
  rw [reduction_action, finitePullback_action, restrict_action]

private instance pullLevel_additive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsPullbackLevel l E f n).Additive := by
  unfold integralOperationsPullbackLevel integralOperationsRestrict
  infer_instance

private instance pullLevel_linear {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsPullbackLevel l E f n).Linear
      (Padic.coefficientExtensionIntegers l E) where
  map_smul := by
    intro P Q g a
    apply HomologicalComplex.hom_ext
    intro i
    exact (pullModule l E f n).map_smul a (g.f i)

section RoosLinearity

variable {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
open CochainComplex

private theorem roosMap_eq {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (α : C ⟶ C') :
    integralOperationsRoosMap α =
      (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map
        (mappingCone.map
          (towerTransitionEndomorphism (integralOperationsTowerStep C))
          (towerTransitionEndomorphism (integralOperationsTowerStep C'))
          (Limits.Pi.map (fun n ↦ α.app (op n)))
          (Limits.Pi.map (fun n ↦ α.app (op n))) (integralOperationsRoos_square α)) := by
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square α)]

private instance roos_additive :
    (integralOperationsRoosFunctor (A := A)).Additive where
  map_add := by
    intro C C' α β
    change integralOperationsRoosMap (α + β) =
      integralOperationsRoosMap α + integralOperationsRoosMap β
    have hp : Limits.Pi.map (fun n ↦ α.app (op n) + β.app (op n)) =
        Limits.Pi.map (fun n ↦ α.app (op n)) +
          Limits.Pi.map (fun n ↦ β.app (op n)) := by
      apply Limits.Pi.hom_ext
      intro n
      simp [Preadditive.add_comp, Preadditive.comp_add]
    rw [roosMap_eq, roosMap_eq, roosMap_eq, ← CategoryTheory.Functor.map_add]
    congr 1
    ext i
    apply mappingCone.ext_from _ (i + 1) i rfl
    all_goals simp [mappingCone.map, Preadditive.comp_add, Preadditive.add_comp, hp]

private instance roos_linear (R : Type*) [Ring R] [Linear R A] :
    (integralOperationsRoosFunctor (A := A)).Linear R where
  map_smul := by
    intro C C' α a
    change integralOperationsRoosMap (a • α) = a • integralOperationsRoosMap α
    have hp : Limits.Pi.map (fun n ↦ a • α.app (op n)) =
        a • Limits.Pi.map (fun n ↦ α.app (op n)) := by
      apply Limits.Pi.hom_ext
      intro n
      simp [Linear.smul_comp, Linear.comp_smul]
    rw [roosMap_eq, roosMap_eq, ← Functor.map_smul]
    congr 1
    ext i
    apply mappingCone.ext_from _ (i + 1) i rfl
    all_goals simp [mappingCone.map, Linear.comp_smul, Linear.smul_comp, hp]

end RoosLinearity

private instance pullTower_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralOperationsPullbackTowerFunctor l E f).Additive where
  map_add := by
    intro P Q g h
    apply NatTrans.ext
    funext n
    exact (integralOperationsPullbackLevel l E f n.unop).map_add (f := g) (g := h)

private instance pullTower_linear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralOperationsPullbackTowerFunctor l E f).Linear
      (Padic.coefficientExtensionIntegers l E) where
  map_smul := by
    intro P Q g a
    apply NatTrans.ext
    funext n
    exact (integralOperationsPullbackLevel l E f n.unop).map_smul a g

private instance pullComplex_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralOperationsPullbackComplexFunctor l E f).Additive := by
  unfold integralOperationsPullbackComplexFunctor
  infer_instance

private instance pullComplex_linear {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralOperationsPullbackComplexFunctor l E f).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  unfold integralOperationsPullbackComplexFunctor
  infer_instance

private theorem pullComplex_action {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : Padic.coefficientExtensionIntegers l E)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (integralOperationsPullbackComplexFunctor l E f).map
        ((integralScalarChainAction l E Y a).app P) =
      (integralScalarChainAction l E X a).app
        ((integralOperationsPullbackComplexFunctor l E f).obj P) := by
  rw [coefficientChain_eq, coefficientChain_eq]
  change (integralOperationsPullbackComplexFunctor l E f).map (a • 𝟙 P) = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end Representatives

/-- The normalized integral pullback preserves addition and the published constant
valuation-ring action on ambient derived morphisms.
Source: blueprint `prose-03-02`, rational paragraph;
Bhatt--Scholze, Lemma 6.5.9(4), and Stacks Tag 099N(5).
(blueprint: lem-sf-integral-derived-pullback-linear).

Proof: use the good flat-term K-flat representatives and the natural comparison
`integralDerivedPullbackComparison`. On each finite reduction the constant scalar a
acts by its quotient class. Reduction, exact finite inverse image and restriction of
scalars preserve addition and multiplication by this class. The quotient transition
maps commute with these scalar actions. Thus the diagonal map on the two product
coordinates of the shifted cone defining the Roos complex preserves addition and
the constant scalar a, including the signed differential. Localization of complexes
preserves the same action by `integralCoefficientLinear_existsUnique`. The good
localization inverts quasi-isomorphisms and presents the entire ambient derived
category. Addition descends through this localization; scalar multiplication is
composition with the natural scalar endomorphism a times the identity, which is
preserved on good representatives and hence on inverses and composites of localized
maps. Finally conjugate by the specified natural representative comparison. Its
components commute with the constant scalar action by linearity of composition.
This proves both equations for the existing normalized descent, without selecting
another pullback functor. The argument works for the zero object, identity maps,
zero scalars and arbitrary scheme morphisms, and uses no coefficient flatness. -/
theorem integralDerivedPullback_linear (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).Additive ∧
      (integralDerivedPullback l E f).Linear (Padic.coefficientExtensionIntegers l E) := by
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E Y).ι
  let Λ := integralOperationsGoodLocalization l E Y
  let F := integralDerivedPullback l E f
  let : Λ.IsLocalization V := integralOperationsGoodLocalization_isLocalization.{u, u} l E Y
  let : Λ.EssSurj := Localization.essSurj Λ V
  let : HasBinaryBiproducts (integralOperationsGoodComplex l E Y).FullSubcategory :=
    integralScalarGood_biproducts.{u, u} l E Y
  let : Λ.Additive := by
    dsimp only [Λ, integralOperationsGoodLocalization]
    infer_instance
  let : (integralOperationsPullbackComplexFunctor l E f).Additive := pullComplex_additive l E f
  let : (integralOperationsPullbackOnGood l E f).Additive := by
    unfold integralOperationsPullbackOnGood
    infer_instance
  let : (Λ ⋙ F).Additive :=
    Functor.additive_of_iso (integralDerivedPullbackComparison l E f).symm
  refine ⟨IntegralScalarAux.additive_descent Λ F, ?_⟩
  constructor
  intro K K' g a
  rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec,
    (integralCoefficientLinear_existsUnique l E X).exists.choose_spec]
  exact IntegralScalarAux.action_descent_via_complex
    (integralOperationsGoodComplex l E Y)
    (DerivedCategory.Q (C := integralTowerModules l E Y))
    (DerivedCategory.Q (C := integralTowerModules l E X)) Λ V rfl
    (integralOperationsPullbackComplexFunctor l E f) F
    (integralDerivedPullbackComparison l E f)
    (integralScalarDerivedAction l E Y a) (integralScalarDerivedAction l E X a)
    (integralScalarChainAction l E Y a) (integralScalarChainAction l E X a)
    (integralScalarDerivedAction_app_Q l E Y a)
    (integralScalarDerivedAction_app_Q l E X a) (pullComplex_action l E f a) K K' g

end WeilConjectures
