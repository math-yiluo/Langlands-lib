/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMatePresentation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # Restricted native proper scalar mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.PurCompactSupport.properComparison
  AlgebraicGeometry.Scheme.pbcDerivedRestrict
  AlgebraicGeometry.Scheme.reductionDerivedChange
  CategoryTheory.Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom
  AlgebraicGeometry.ProEtale.CondensedRing.localizedDirectImageComparison

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Limits AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact
attribute [local irreducible] Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct

private theorem scalarMate_mapIso_of_arrowIso
    {A B : Type*} [Category A] [Category B]
    {X Y X' Y' : A} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (F : A ⥤ B) (q : Arrow.mk f ≅ Arrow.mk g) (hg : IsIso g) :
    IsIso (F.map f) := by
  have : IsIso f := (Arrow.isIso_iff_isIso_of_isIso q.hom).2 hg
  infer_instance

/-- The native proper scalar mate becomes invertible after restriction to the
completed coefficient ring. This is the coefficient-presentation comparison,
proved by normalized finite quotient projections, localization comparison, and
bounded proper push comparison described in the parent node.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 5.3(1).
(blueprint: lem-sf-native-proper-scalar-mate-bounded-below-restricted).
-/
theorem native_proper_scalar_mate_bounded_below_restricted
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) [IsProper g]
    (M : DerivedCategory (pbcModules U
      ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).ring U)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((pbcDerivedRestrict (a.map V)).map
      ((PurCompactSupport.properComparison a g).app M)) := by
  obtain ⟨e, d, he, hd, h⟩ := native_proper_scalar_mate_presentation l E a ha g
  have := he
  have := hd
  have : PreservesFiniteLimits e.functor := inferInstance
  have : PreservesFiniteColimits e.functor := inferInstance
  have : PreservesFiniteLimits d.functor := inferInstance
  have : PreservesFiniteColimits d.functor := inferInstance
  let C := e.functor.mapDerivedCategory.obj M
  obtain ⟨b, hb⟩ := hM
  have : M.IsGE b := hb
  have : C.IsGE b := e.functor.isGE_mapDerivedCategory_obj M b
  have hC : DerivedCategory.TStructure.t.plus C := ⟨b, inferInstance⟩
  let L := Mod.extendScalars (padicIntegersToPadicSubfield U l E)
  have : PreservesFiniteLimits L :=
    (padicIntegers_invertEll U l E).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
  have hLC : (L.mapDerivedCategory.obj C).IsGE b := L.isGE_mapDerivedCategory_obj C b
  have : (L.leftDerivedFunctor.obj C).IsGE b :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (L.leftDerivedFunctorIsoMapDerivedCategory.app C).symm b
  have hlocal := CondensedRing.localizedDirectImageComparison_isIso l E g C hC
  let D := nativeScalarIntegralDerived U l E
  have : (D.obj C).IsGE b := by
    change (L.leftDerivedFunctor.obj C).IsGE b
    infer_instance
  have hpush := CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE
    l g E (D.obj C) b
  let F := nativeScalarClosureDerived V l E
  let β := CondensedRing.localizedDirectImageComparison l E g C
  let γ := (CondensedRing.derivedPushHom
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g).app (D.obj C)
  have hβ : IsIso β := hlocal
  have hγ : IsIso γ := hpush
  have hFβ : IsIso (F.map β) := inferInstance
  have hcomp : IsIso (F.map β ≫ γ) := IsIso.comp_isIso' hFβ hγ
  have hcanonical : IsIso (nativeScalarCondensedComposite l E g C) := by
    dsimp only [nativeScalarCondensedComposite]
    exact hcomp
  have hmap : IsIso (d.functor.mapDerivedCategory.map
      (nativeScalarCondensedComposite l E g C)) := inferInstance
  obtain ⟨q⟩ := h M
  exact scalarMate_mapIso_of_arrowIso (pbcDerivedRestrict (a.map V)) q hmap

end WeilConjectures.LocallyFiniteAdicCompactSupport
