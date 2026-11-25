/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.OpenCompletedRestriction.OpenCompletedRestrictionIdentification
import WeilConjectures.SixFunctors.Clopen.ClopenPullbackQuotientTower
import all WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # Clopen restriction of quotient completion before imposing completeness

Source: Stacks Project, derived.tex, Tag 08TC; sites-cohomology.tex, Tag 0941.
(blueprint: lem-fix-clopen-integral-completion-restriction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralDerivedPullback

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true
attribute [local reducible] WeilConjectures.IntegralOnSlice.Site
  WeilConjectures.IntegralOnSlice.topology WeilConjectures.IntegralOnSlice.restrict
  WeilConjectures.IntegralOnSlice.ring

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] OpenCompletedRestriction.coefficients

private theorem restriction_products
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens) :
    PreservesLimitsOfShape (Discrete ℕ) (OpenCompletedRestriction.ordinary l E U.ι) := by
  let R := IntegralOnSlice.rings l E V none
  let S := IntegralOnSlice.rings l E U.toScheme none
  let F := OpenCompletedRestriction.ordinary l E U.ι
  let T := SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ T) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft U.toScheme.ProEtᵒᵖ V.ProEtᵒᵖ
          AddCommGrpCat.{u + 1}).obj (OpenCompletedRestriction.inclusion U.ι).op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℕ) T :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F T

private noncomputable def restriction_roos
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor := by
  have : PreservesLimitsOfShape (Discrete ℕ) (F.mapHomologicalComplex (.up ℤ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun n ↦ by
      change PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.eval _ (.up ℤ) n ⋙ F)
      infer_instance)
  let T := (HomologicalComplex.functorEquivalence
    A (.up ℤ) ℕᵒᵖ).inverse
  have (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
      IsIso (CategoryTheory.roosComparison F (T.obj C)) := by
    dsimp only [CategoryTheory.roosComparison]
    infer_instance
  exact NatIso.ofComponents (fun C ↦ CategoryTheory.roosTheta F (T.obj C)) (by
    intro C D f
    exact CategoryTheory.roosTheta_map F _ _
      (strictRoosProductMap_comm (T.map f)) _ _
      (strictRoosProductMap_comm ((CategoryTheory.roosTowerMap F).map (T.map f)))
      (CategoryTheory.roosComparison_map F (T.map f))
      (CategoryTheory.roosComparison_map F (T.map f)))

attribute [local irreducible] restriction_roos IntegralOnSlice.tower
  IntegralOnSlice.completion IntegralOnSlice.completionComparison
  CategoryTheory.Functor.mapDerivedCategory

/-- Completed pullback to a clopen is exact restriction of quotient completion.
This is an isomorphism of functors on all complexes, before using a completion unit.

Source: Stacks Project, derived.tex, Tag 08TC; sites-cohomology.tex, Tag 0941;
steps 1 and 2 of lem-fix-clopen-completed-restriction-comparison.
(blueprint: lem-fix-clopen-integral-completion-restriction).

Proof: the strict clopen pullback-tower comparison identifies ordinary restriction
of the quotient tower with the specified finite pullback tower on all complexes.
Ordinary restriction preserves countable products: after forgetting modules and
sheaves it is precomposition of presheaves, and the forgetful composite reflects
limits. Its additive product comparison identifies the shifted Roos cones,
naturally in the input complex. Whisker the strict tower isomorphism through the
Roos functor. On good representatives compose with completionComparison and the
exact restriction functor's mapDerivedCategoryFactors. The universal property of
integralPullbackDescent then gives the natural isomorphism of derived functors.
No invertibility of the prime or completeness of the input is used. Empty clopens
use the same comparisons in the zero module category. -/
theorem clopenIntegralCompletionRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Scheme.{u}) (U : V.Opens) (_hU : IsClosed (U : Set V)) :
    Nonempty (IntegralOnSlice.completion l E V none ⋙
      OpenCompletedRestriction.derivedRestriction l E U.ι ≅
        integralDerivedPullback l E U.ι) := by
  have := restriction_products l E V U
  let r := restriction_roos (OpenCompletedRestriction.ordinary l E U.ι)
  obtain ⟨a⟩ := clopenPullbackQuotientTower l E V U _hU
  let c : IntegralOnSlice.roos l E V none ⋙
      OpenCompletedRestriction.complexRestriction l E U.ι ≅
      integralOperationsPullbackComplexFunctor l E U.ι :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ r ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight a integralOperationsRoosFunctor
  let d := OpenCompletedRestriction.derivedRestriction l E U.ι
  let G := (IntegralOnSlice.Good l E V none).ι
  let e : integralOperationsGoodLocalization l E V ⋙
      (IntegralOnSlice.completion l E V none ⋙ d) ≅
      integralOperationsPullbackOnGood l E U.ι :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (IntegralOnSlice.completionComparison l E V none) d ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (G ⋙ IntegralOnSlice.roos l E V none)
        (OpenCompletedRestriction.ordinary l E U.ι).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G c) DerivedCategory.Q ≪≫
      Functor.associator _ _ _
  obtain ⟨i, _, _⟩ := (integralPullbackDescent l E U.ι).universal _ e
  exact ⟨by simpa only [integralDerivedPullback] using i.symm⟩

end WeilConjectures
