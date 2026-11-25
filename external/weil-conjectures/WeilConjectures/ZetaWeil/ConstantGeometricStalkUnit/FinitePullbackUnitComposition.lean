/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates

import all WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.CoefficientPullbackUnitCoordinates
import all WeilConjectures.ZetaWeil.FiniteRegularCoefficientComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Composition of finite coefficient multiplication

Source: the constant-sheaf clause of `theorem-grothendieck-lefschetz-trace-formula--8`, reviewed
expansion step 3 (blueprint: lem-zl-finite-pullback-unit-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [local implicit_reducible] integralCoefficientSheaf openSquarePullbackModel
  SheafOfModules.unit PresheafOfModules.unit
  AlgebraicGeometry.Scheme.ProEt CategoryTheory.MorphismProperty
  proEtaleConstantModuleDirectImage proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  sfIntrinsicPullback sfIntrinsicConstantModuleAdjunction

section Categorical
variable {C D B : Type*} [Category C] [Category D] [Category B]

private theorem transport_unit_composition
    {F F' : C ⥤ D} {G G' : D ⥤ B} {H H' : C ⥤ B}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') (a : H ≅ F ⋙ G)
    {M : C} {N : D} {P : B}
    (x : F'.obj M ⟶ N) (y : G'.obj N ⟶ P) (z : H'.obj M ⟶ P)
    (h : a.hom.app M ≫ G.map (eF.hom.app M ≫ x) ≫ eG.hom.app N ≫ y =
      eH.hom.app M ≫ z) :
    (eH.symm ≪≫ a ≪≫ Functor.isoWhiskerRight eF G ≪≫
      Functor.isoWhiskerLeft F' eG).hom.app M ≫ G'.map x ≫ y = z := by
  rw [← cancel_epi (eH.hom.app M)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← eG.hom.naturality_assoc x, ← G.map_comp_assoc]
  exact h

end Categorical

section Derived
variable {C D B : Type*} [Category C] [Category D] [Category B]
  [Abelian C] [Abelian D] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory B]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_unit_composition
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G) {M : C} {N : D} {P : B}
    (x : F.obj M ⟶ N) (y : G.obj N ⟶ P) (z : H.obj M ⟶ P)
    (h : a.hom.app M ≫ G.map x ≫ y = z) :
    (Functor.mapDerivedCategoryNatIso a ≪≫ (Functor.mapDerivedCategoryCompIso F G).symm).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      G.mapDerivedCategory.map
        ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor D 0).map x) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor B 0).map y =
      (H.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map z := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have hn := (G.mapDerivedCategorySingleFunctor 0).hom.naturality x
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor F G H a M)]
  simp only [← Functor.map_comp, h]

end Derived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def ordinaryUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) f).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ⟶
      SheafOfModules.unit (integralCoefficientSheaf l E X m) :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  (openSquarePullbackModel (Padic.coefficientExtensionRing l E (m + 1)) f).hom.app _ ≫
    finiteUnitHom l E f m

private theorem ordinaryUnit_one {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ)
    (U : Y.ProEt) :
    (ordinaryUnit l E f m).val.app (op ((proEtaleBaseChange f).obj U))
      (((proEtaleConstantRingAdjunction
        (Padic.coefficientExtensionRing l E (m + 1)) f).unit.app
          (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app (op U)
            (1 : (integralCoefficientSheaf l E Y m).obj.obj (op U))) =
      (1 : (integralCoefficientSheaf l E X m).obj.obj
        (op ((proEtaleBaseChange f).obj U))) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  have he := (openSquarePullbackModel_existsUnique
    (Padic.coefficientExtensionRing l E (m + 1)) f).exists.choose_spec
  change (finiteUnitHom l E f m).val.app _
    (((openSquarePullbackModel _ f).hom.app _).val.app _ _) = _
  erw [he (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) U
    (1 : (integralCoefficientSheaf l E Y m).obj.obj (op U)),
    finiteUnitHom_generator]
  change ((coefficientProEtaleDirectRingMap.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))))).hom.app
      (op U)) (1 : (integralCoefficientSheaf l E Y m).obj.obj (op U)) =
    (1 : (integralCoefficientSheaf l E X m).obj.obj (op ((proEtaleBaseChange f).obj U)))
  exact map_one _

private theorem ordinaryUnit_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ)
    (a : proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1))
        (f ≫ g) ≅
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) g ⋙
        proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) f)
    (ha : ∀ (M : proEtaleRingModules Z
        (proEtaleConstantRing Z (Padic.coefficientExtensionRing l E (m + 1))))
      (U : Z.ProEt) (z : M.val.obj (op U)),
      (a.hom.app M).val.app (op ((proEtaleBaseChange (f ≫ g)).obj U))
        (((proEtaleConstantRingAdjunction
          (Padic.coefficientExtensionRing l E (m + 1)) (f ≫ g)).unit.app M).val.app
            (op U) z) =
      ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) f).obj
        ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) g).obj
          M)).val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op
        (((proEtaleConstantRingAdjunction
          (Padic.coefficientExtensionRing l E (m + 1)) f).unit.app
            ((proEtaleConstantRingPullback
              (Padic.coefficientExtensionRing l E (m + 1)) g).obj M)).val.app
                (op ((proEtaleBaseChange g).obj U))
          (((proEtaleConstantRingAdjunction
            (Padic.coefficientExtensionRing l E (m + 1)) g).unit.app M).val.app (op U) z))) :
    a.hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Z m)) ≫
      (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (m + 1)) f).map
        (ordinaryUnit l E g m) ≫ ordinaryUnit l E f m = ordinaryUnit l E (f ≫ g) m := by
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let adj := proEtaleConstantRingAdjunction A (f ≫ g)
  apply (adj.homEquiv _ _).injective
  apply (SheafOfModules.unitHomEquiv _).injective
  ext U
  simp only [SheafOfModules.unitHomEquiv_apply_coe, Adjunction.homEquiv_unit]
  change (ordinaryUnit l E f m).val.app _
    (((proEtaleConstantRingPullback A f).map (ordinaryUnit l E g m)).val.app _
      ((a.hom.app _).val.app _ ((adj.unit.app _).val.app U
        (1 : (integralCoefficientSheaf l E Z m).obj.obj U)))) =
    (ordinaryUnit l E (f ≫ g) m).val.app _ ((adj.unit.app _).val.app U
        (1 : (integralCoefficientSheaf l E Z m).obj.obj U))
  let v := (proEtaleConstantRingPullback A f).map (ordinaryUnit l E g m) ≫
    ordinaryUnit l E f m
  change v.val.app _ (_ ) = _
  have hgen := congrArg (fun t ↦ v.val.app ((proEtaleBaseChange (f ≫ g)).op.obj U) t)
    (ha (SheafOfModules.unit (integralCoefficientSheaf l E Z m)) U.unop
      (1 : (integralCoefficientSheaf l E Z m).obj.obj U))
  refine hgen.trans ?_
  refine (PresheafOfModules.naturality_apply v.val
    ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop).op _).trans ?_
  have hu := congrArg (fun k ↦ k.val.app
    (op ((proEtaleBaseChange g).obj U.unop))
    (((proEtaleConstantRingAdjunction A g).unit.app _).val.app U
        (1 : (integralCoefficientSheaf l E Z m).obj.obj U)))
    ((proEtaleConstantRingAdjunction A f).unit.naturality (ordinaryUnit l E g m))
  change ((proEtaleConstantRingAdjunction A f).unit.app
    (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app
      (op ((proEtaleBaseChange g).obj U.unop))
        ((ordinaryUnit l E g m).val.app (op ((proEtaleBaseChange g).obj U.unop))
          (((proEtaleConstantRingAdjunction A g).unit.app
            (SheafOfModules.unit (integralCoefficientSheaf l E Z m))).val.app U
              (1 : (integralCoefficientSheaf l E Z m).obj.obj U))) =
    ((proEtaleConstantRingPullback A f).map (ordinaryUnit l E g m)).val.app _ (_) at hu
  have hmul : v.val.app
      (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U.unop)))
        (((proEtaleConstantRingAdjunction A f).unit.app
          ((proEtaleConstantRingPullback A g).obj
            (SheafOfModules.unit (integralCoefficientSheaf l E Z m)))).val.app
              (op ((proEtaleBaseChange g).obj U.unop))
            (((proEtaleConstantRingAdjunction A g).unit.app
              (SheafOfModules.unit (integralCoefficientSheaf l E Z m))).val.app U
                (1 : (integralCoefficientSheaf l E Z m).obj.obj U))) =
      (1 : (integralCoefficientSheaf l E X m).obj.obj
        (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj U.unop)))) := by
    change (ordinaryUnit l E f m).val.app _
      (((proEtaleConstantRingPullback A f).map (ordinaryUnit l E g m)).val.app _ _) = _
    erw [← hu]
    erw [ordinaryUnit_one l E g m U.unop,
      ordinaryUnit_one l E f m ((proEtaleBaseChange g).obj U.unop)]
  refine Eq.trans ?_ (ordinaryUnit_one l E (f ≫ g) m U.unop).symm
  change (integralCoefficientSheaf l E X m).obj.map _ (v.val.app _ _) =
    (1 : (integralCoefficientSheaf l E X m).obj.obj
      (op ((proEtaleBaseChange (f ≫ g)).obj U.unop)))
  erw [hmul]
  exact map_one _

private theorem derivedUnit_coordinates {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (m + 1))
      f).hom.app (finiteConstantCoefficientObject l E Y m) ≫ (finiteUnit l E f m).hom =
      ((proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (m + 1)) f).mapDerivedCategorySingleFunctor
          0).hom.app (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ≫
        (DerivedCategory.singleFunctor _ 0).map (ordinaryUnit l E f m) := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  change (Functor.mapDerivedCategoryNatIso (openSquarePullbackModel _ f)).hom.app
    ((DerivedCategory.singleFunctor _ 0).obj _) ≫
      ((sfIntrinsicPullback _ f).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map (finiteUnitHom l E f m) = _
  rw [← Category.assoc, Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [Category.assoc, ← Functor.map_comp]
  rfl

/-- The actual finite compositor preserves regular coefficient multiplication.
Source: current blueprint, sec-zeta-weil/sk-thm-intfactors,
`prop-every-iterate-trace.proof.md`, constant-sheaf clause, reviewed expansion step 3.
(blueprint: lem-zl-finite-pullback-unit-composition).

Proof: transpose the regular multiplication maps along the module adjunctions.
Each is the section one. The constant coefficient direct-image ring maps respect
composition by `proEtaleCoefficientInverseImageMap_comp`. The unit-normalized
changes of pullback presentation preserve these transposes. The canonical tensor
compositor sends an iterated pure tensor to its associated tensor, so both paths
multiply its coefficients in the same order. The regular sheaf in degree zero is
K-flat, and the single-complex comparison is natural, giving the displayed equation
in the derived category. This also applies to identity maps, empty schemes and m=0. -/
theorem finiteUnit_composition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    (finiteCanonicalPullbackComposition l E f g m).hom.app
        (finiteConstantCoefficientObject l E Z m) ≫
      (finiteDerivedPullback l E m f).map (finiteUnit l E g m).hom ≫
        (finiteUnit l E f m).hom = (finiteUnit l E (f ≫ g) m).hom := by
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
  let A := Padic.coefficientExtensionRing l E (m + 1)
  obtain ⟨a, ha, hd⟩ := proEtaleConstantRingPullbackComposition_ordinary f g A
  have ho := ordinaryUnit_composition l E f g m a ha
  have h := derived_unit_composition
    (proEtaleConstantRingPullback A g) (proEtaleConstantRingPullback A f)
    (proEtaleConstantRingPullback A (f ≫ g)) a
    (ordinaryUnit l E g m) (ordinaryUnit l E f m) (ordinaryUnit l E (f ≫ g) m) ho
  rw [hd] at h
  have hc := transport_unit_composition
    (openSquareDerivedPullbackModel A g) (openSquareDerivedPullbackModel A f)
    (openSquareDerivedPullbackModel A (f ≫ g))
    (proEtaleConstantRingPullbackComposition f g A).symm
    (finiteUnit l E g m).hom (finiteUnit l E f m).hom (finiteUnit l E (f ≫ g) m).hom
  unfold finiteCanonicalPullbackComposition integralFiniteCanonicalPullbackComposition
  apply hc
  rw [← derivedUnit_coordinates l E g m, ← derivedUnit_coordinates l E f m,
    ← derivedUnit_coordinates l E (f ≫ g) m] at h
  exact h

end WeilConjectures.ConstantGeometricStalkUnit
