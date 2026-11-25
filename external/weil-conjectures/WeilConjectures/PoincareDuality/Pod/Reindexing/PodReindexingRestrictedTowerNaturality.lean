/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingStrictData.PodReindexingStrictComparisons
import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingGoodComplex

/-! # Naturality of the normalized restricted-tower comparison

(blueprint: lem-pod-reindexing-restricted-tower-naturality) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

private abbrev restrictedFunctor (W : Scheme.{t}) :
    CochainComplex (coefficientSequenceModules l E W) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

private abbrev sequenceComplex :
    CochainComplex (coefficientSequenceModules l E Y) ℤ ⥤
      CochainComplex (coefficientSequenceModules l E X) ℤ :=
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)

private def coefficientIso : isoReductionIntegralInverse l E g ≅
    inverseImageIntegralModules l E g := by
  apply SheafOfModules.pushforwardCongr
  apply (cancel_mono (inverseImageCompletedCoefficientMap l E g)).mp
  exact (congrArg (CategoryTheory.inv (isoReductionCompletedMap l E g).hom ≫ ·)
    (podCompletedCoefficientMap_eq l E g).symm).trans
      ((IsIso.inv_hom_id _).trans (IsIso.inv_hom_id _).symm)

private def restrictedModuleIso :
    coefficientSequenceRestriction l E Y ⋙
        (whiskeringRight ℕᵒᵖ _ _).obj (isoReductionIntegralInverse l E g) ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X :=
  isoWhiskerLeft (coefficientSequenceRestriction l E Y)
    ((whiskeringRight ℕᵒᵖ _ _).mapIso (coefficientIso l E g)) ≪≫
      integralTowerInverseImageUnit l E g

private def liftRestrictionIso
    {J A B C D : Type*} [Category* J] [Category* A] [Category* B]
    [Category* C] [Category* D] [Preadditive A] [Preadditive B]
    [Preadditive C] [Preadditive D]
    (R : A ⥤ J ⥤ B) (F : B ⥤ C) (P : A ⥤ D) (T : D ⥤ J ⥤ C)
    [R.Additive] [F.Additive] [P.Additive] [T.Additive]
    (e : R ⋙ (whiskeringRight J _ _).obj F ≅ P ⋙ T) :
    (R.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙
        (whiskeringRight J _ _).obj (F.mapHomologicalComplex (.up ℤ)) ≅
      P.mapHomologicalComplex (.up ℤ) ⋙ T.mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex :=
  NatIso.ofComponents (fun K ↦
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K))
    (by
      intro K K' f
      have h := (NatIso.mapHomologicalComplex e (.up ℤ)).hom.naturality f
      apply NatTrans.ext
      funext n
      apply HomologicalComplex.hom_ext
      intro i
      exact congrArg (fun a ↦ (a.f i).app n) h)

private def restrictedIso :
    restrictedFunctor l E Y ⋙ podReindexTower l E g ≅
      sequenceComplex l E g ⋙ restrictedFunctor l E X :=
  liftRestrictionIso (coefficientSequenceRestriction l E Y) (isoReductionIntegralInverse l E g)
    (integralComparisonSequencePullback l E g) (coefficientSequenceRestriction l E X)
    (restrictedModuleIso l E g)

private theorem restrictedIso_generators
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (C.X i).val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    ((((restrictedIso l E g).app C).hom.app (op n)).f i).val.app (op U)
        (integralComparisonRestrictedSection l E Y (C.X i) n
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
      integralComparisonRestrictedSection l E X
        ((integralComparisonSequencePullback l E g).obj (C.X i)) n (op U)
        (((integralComparisonSequencePullback l E g).obj (C.X i)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (C.X i) n
            ((proEtaleIsoPostcompose g).obj U) x)) := by
  change (((integralTowerInverseImageUnit l E g).hom.app (C.X i)).app (op n)).val.app
    (op U) (((coefficientIso l E g).hom.app _).val.app (op U) _) = _
  dsimp only [coefficientIso]
  erw [SheafOfModules.pushforwardCongr_hom_app_val_app]
  exact (integralTowerInverseImageUnit_existsUnique l E g).exists.choose_spec
    (C.X i) n U x

private theorem restricted_eq (S : PodReindexingStrictData l E g)
    (hS : S.RestrictedGenerators l E g)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    S.restricted C = (restrictedIso l E g).app C := by
  apply Iso.ext
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro i
  ext U x
  change (((S.restricted C).hom.app n).f i).val.app U x =
    ((((restrictedIso l E g).app C).hom.app n).f i).val.app U x
  have hx : Function.Surjective (integralComparisonRestrictedSection l E Y (C.X i)
      n.unop (op ((proEtaleIsoPostcompose g).obj U.unop))) := by
    intro z
    exact ⟨cast (integralComparisonRestrictedSectionType l E Y (C.X i)
      n.unop (op ((proEtaleIsoPostcompose g).obj U.unop))) z, by
        simp [integralComparisonRestrictedSection]⟩
  obtain ⟨x, rfl⟩ := hx x
  exact (hS C n.unop i U.unop x).trans
    (restrictedIso_generators l E g C n.unop i U.unop x).symm

/-- The generator-normalized restricted-tower maps form a natural isomorphism.

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 0941. The equality of completed coefficient maps identifies the scalar
restriction functors. Whisker the inverse-image unit with this identification
and lift it to complexes. Its section formula agrees with the specified
restricted generators. Those generators cover every section, so extensionality
identifies the specified family with the natural lifted unit.
(blueprint: lem-pod-reindexing-restricted-tower-naturality) -/
theorem podReindexingRestrictedTower_naturalIso
    (S : PodReindexingStrictData l E g) (hS : S.RestrictedGenerators l E g) :
    ∃ e : ((coefficientSequenceRestriction l E Y).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex) ⋙ podReindexTower l E g ≅
      ((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)) ⋙
        ((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex), ∀ C, S.restricted C = e.app C := by
  exact ⟨restrictedIso l E g, restricted_eq l E g S hS⟩

end WeilConjectures
