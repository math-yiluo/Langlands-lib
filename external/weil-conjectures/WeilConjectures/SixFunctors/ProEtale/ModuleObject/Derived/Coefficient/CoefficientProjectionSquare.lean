/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-!
# Coefficient compatibility of the actual projection mate

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (3), projection on integral-model pairs before invertibility
(blueprint: lem-sfb-coefficient-projection-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the internal-Hom construction and the inverse image from the point opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.Abelian
open scoped CategoryTheory.Obj

universe v u₁ u₂ u₃ u₄
namespace CategoryTheory.Adjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type u₁} {B : Type u₂} {B' : Type u₃} {C : Type u₄}
  [Category.{v} A] [Category.{v} B] [Category.{v} B'] [Category.{v} C]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Compare each path with the common right adjoint of the underived composite.
private theorem rightSquare (e : U₂ ⋙ U₁ ≅ V₂ ⋙ V₁) (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (ht : e.hom = conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t.hom) :
    (Functor.rightDerivedFunctorCompIso U₂ U₁).inv ≫
      (Functor.rightDerivedFunctorNatIso e).hom ≫
      (Functor.rightDerivedFunctorCompIso V₂ V₁).hom =
    conjugateEquiv
      (a₁.mapDerivedCategoryRightDerivedAdjunction.comp a₂.mapDerivedCategoryRightDerivedAdjunction)
      (b₁.mapDerivedCategoryRightDerivedAdjunction.comp
          b₂.mapDerivedCategoryRightDerivedAdjunction)
      (Functor.mapDerivedCategorySquareIso t).hom := by
  have : U₂.PreservesKInjectiveComplexes := a₂.preservesKInjectiveComplexes
  have : V₂.PreservesKInjectiveComplexes := b₂.preservesKInjectiveComplexes
  have h₁ := rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv a₂ a₁ (b₁.comp b₂) e t ht
  have h₂ := rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv b₂ b₁ (b₁.comp b₂)
    (Iso.refl (V₂ ⋙ V₁)) (Iso.refl (G₁ ⋙ G₂)) (by
      ext X
      simp only [Iso.refl_hom, NatTrans.id_app, conjugateEquiv_id])
  have h₂' : (Functor.rightDerivedFunctorCompIso V₂ V₁).inv =
      conjugateEquiv
        (b₁.mapDerivedCategoryRightDerivedAdjunction.comp
          b₂.mapDerivedCategoryRightDerivedAdjunction)
        (b₁.comp b₂).mapDerivedCategoryRightDerivedAdjunction
        (Functor.mapDerivedCategoryCompIso G₁ G₂).inv := by
    simpa [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorNatIso,
      Functor.rightDerivedFunctorNatTrans, Functor.mapDerivedCategoryNatIso_refl] using h₂
  apply (cancel_mono (Functor.rightDerivedFunctorCompIso V₂ V₁).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (Functor.rightDerivedFunctorCompIso' U₂ U₁ e).hom = _
  rw [h₁, h₂']
  rw [conjugateEquiv_comp]
  congr 1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  ext X
  simp only [NatTrans.comp_app, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

variable [PreservesFiniteLimits f] [PreservesFiniteColimits f]
set_option backward.defeqAttrib.useBackward true in
-- Exact left derivation transports the canonical adjunction along its counit comparison.
private lemma mapDerived_eq (adj : f ⊣ g) :
    adj.mapDerivedCategoryRightDerivedAdjunction =
      adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory := by
  refine (adj.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ)) _ _ _
    f.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]
end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
set_option backward.defeqAttrib.useBackward true in
-- Changing the exact right adjoints inserts their comparison at the two ends.
private lemma conjugate_right_transport {U₂' : C ⥤ B} {V₁' : B' ⥤ A}
    (r : U₂ ≅ U₂') (s : V₁ ≅ V₁') (t : G₁ ⋙ G₂ ⟶ F₁ ⋙ F₂) :
    conjugateEquiv (a₁.comp (a₂.ofNatIsoRight r))
        ((b₁.ofNatIsoRight s).comp b₂) t =
      Functor.whiskerRight r.inv U₁ ≫
        conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t ≫
        Functor.whiskerLeft V₂ s.hom := by
  ext K
  simp only [conjugateEquiv_apply_app, comp_unit_app, comp_counit_app,
    ofNatIsoRight_unit, ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Category.assoc]
  simp only [← V₁'.map_comp]
  erw [← s.hom.naturality]
  erw [b₁.unit.naturality_assoc]
  simp only [Functor.comp_map]
  simp only [← V₁.map_comp_assoc]
  congr 2
  erw [b₂.unit.naturality_assoc]
  simp only [Functor.comp_map, ← V₂.map_comp]
  congr 2
  erw [t.naturality_assoc]
  simp only [Functor.comp_map]
  congr 1
  simp only [← F₂.map_comp_assoc]
  have hn := a₁.counit.naturality (r.inv.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [← hn]
  rfl
set_option backward.defeqAttrib.useBackward true in
-- Conjugation is natural in all four left adjoints.
private lemma conjugate_left_transport
    {F₁' : A ⥤ B} {F₂' : B ⥤ C} {G₁' : A ⥤ B'} {G₂' : B' ⥤ C}
    (e₁ : F₁ ≅ F₁') (e₂ : F₂ ≅ F₂') (d₁ : G₁ ≅ G₁') (d₂ : G₂ ≅ G₂')
    (t : G₁' ⋙ G₂' ⟶ F₁' ⋙ F₂') :
    conjugateEquiv ((a₁.ofNatIsoLeft e₁).comp (a₂.ofNatIsoLeft e₂))
        ((b₁.ofNatIsoLeft d₁).comp (b₂.ofNatIsoLeft d₂)) t =
      conjugateEquiv (a₁.comp a₂) (b₁.comp b₂)
        (Functor.whiskerRight d₁.hom G₂ ≫ Functor.whiskerLeft G₁' d₂.hom ≫ t ≫
          Functor.whiskerLeft F₁' e₂.inv ≫ Functor.whiskerRight e₁.inv F₂) := by
  ext K
  simp only [conjugateEquiv_apply_app, comp_unit_app, comp_counit_app,
    ofNatIsoLeft_unit, ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Functor.comp_map, Category.assoc]
  simp only [← V₁.map_comp]
  erw [b₂.unit.naturality_assoc]
  simp only [Functor.comp_map, ← V₂.map_comp]
  congr 2
  erw [e₂.inv.naturality_assoc]
  erw [e₂.inv.naturality_assoc]
  rfl
end CategoryTheory.Adjunction

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option backward.defeqAttrib.useBackward true in
-- The composite left-derived square is the levelwise square in exact coordinates.
private lemma left_path_comparison (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) :
    whiskerRight G₁.leftDerivedFunctorIsoMapDerivedCategory.hom G₂.leftDerivedFunctor ≫
      whiskerLeft G₁.mapDerivedCategory G₂.leftDerivedFunctorIsoMapDerivedCategory.hom ≫
      (mapDerivedCategorySquareIso t).hom ≫
      whiskerLeft F₁.mapDerivedCategory F₂.leftDerivedFunctorIsoMapDerivedCategory.inv ≫
      whiskerRight F₁.leftDerivedFunctorIsoMapDerivedCategory.inv F₂.leftDerivedFunctor =
    ((G₁.leftDerivedFunctorCompIso G₂).symm ≪≫
      (G₁ ⋙ G₂).leftDerivedFunctorNatIso t ≪≫ F₁.leftDerivedFunctorCompIso F₂).hom := by
  ext K
  simp only [leftDerivedFunctorNatIso, leftDerivedFunctorCompIso,
    mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [← F₂.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  rw [G₂.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Combine exact transport with the right-derived composition/conjugation identity.
private theorem derived_square_conjugate
    (e : U₂ ⋙ U₁ ≅ V₂ ⋙ V₁) (t : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂)
    (ht : e.hom = conjugateEquiv (a₁.comp a₂) (b₁.comp b₂) t.hom) :
    conjugateEquiv
      (a₁.derivedAdjunction.comp (a₂.derivedAdjunction.ofNatIsoRight
        U₂.rightDerivedFunctorIsoMapDerivedCategory))
      ((b₁.derivedAdjunction.ofNatIsoRight V₁.rightDerivedFunctorIsoMapDerivedCategory).comp
        b₂.derivedAdjunction)
      ((G₁.leftDerivedFunctorCompIso G₂).symm ≪≫
        (G₁ ⋙ G₂).leftDerivedFunctorNatIso t ≪≫ F₁.leftDerivedFunctorCompIso F₂).hom =
      (isoWhiskerRight U₂.rightDerivedFunctorIsoMapDerivedCategory.symm U₁.rightDerivedFunctor ≪≫
        (rightDerivedFunctorCompIso U₂ U₁).symm ≪≫ rightDerivedFunctorNatIso e ≪≫
        rightDerivedFunctorCompMapDerivedCategoryIso V₂ V₁).hom := by
  have hraw := CategoryTheory.Adjunction.rightSquare a₁ a₂ b₁ b₂ e t ht
  simp only [CategoryTheory.Adjunction.mapDerived_eq,
    CategoryTheory.Adjunction.conjugate_left_transport,
    CategoryTheory.Functor.left_path_comparison] at hraw
  simp only [CategoryTheory.Adjunction.conjugate_right_transport, ← hraw]
  rw [rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived]
  simp only [rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
    rightDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Category.assoc]
end CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
private theorem push_eq_mate_pull_inv
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {T : A ⥤ B} {S : B ⥤ A} {T' : A' ⥤ B'} {S' : B' ⥤ A'}
    {l : A' ⥤ A} {r : A ⥤ A'} {l' : B' ⥤ B} {r' : B ⥤ B'}
    (a : T ⊣ S) (b : T' ⊣ S') (c : l ⊣ r) (d : l' ⊣ r')
    (e : r' ⋙ S' ≅ S ⋙ r) :
    Adjunction.pushHomOfComapIso a b e =
      (mateEquiv c d (TwoSquare.mk _ _ _ _
        (Adjunction.pullIsoOfComapIso a b c d e).inv)) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm c d b a
    (TwoSquare.mk _ _ _ _ e.inv)
  apply (mateEquiv c d).symm.injective
  change (mateEquiv c d).symm ((mateEquiv a b).symm (.mk _ _ _ _ e.inv)) =
    (mateEquiv c d).symm
      (mateEquiv c d (.mk _ _ _ _ (Adjunction.pullIsoOfComapIso a b c d e).inv))
  rw [Equiv.symm_apply_apply]
  exact h

-- Preserve the concrete geometric functors while checking the abstract identities.
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The comparison specializes four large derived adjunctions.
private theorem path_conjugate :
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction R f).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
        (derivedUpperStarLowerStarAdjunction S f))
      (coefficientScalarPathIso a f).hom =
        (derivedComapLowerStarIso a f).inv := by
  let := (upperStarLowerStarAdjunction S f).preservesKInjectiveComplexes
  have h := Functor.derived_square_conjugate (upperStar R f)
    (Mod.extendScalars (coefficientMap a X)) (Mod.extendScalars (coefficientMap a Y))
    (upperStar S f) (upperStarLowerStarAdjunction R f)
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (Mod.extendRestrictAdjunction (coefficientMap a Y)) (upperStarLowerStarAdjunction S f)
    (comapLowerStarIso a f).symm (pullIso a f).symm
    (((conjugateEquiv _ _).apply_symm_apply _).symm)
  exact h.trans (by
    simp only [derivedComapLowerStarIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.rightDerivedFunctorNatIso, Iso.symm_hom, Category.assoc])

-- Do not expand the canonical comparisons during tactic matching.
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The statement shares geometric and scalar derived tensor instances.
-- The categorical square specializes large derived adjunctions.
/-- The specified scalar push mate and pull comparison commute with the actual projection
morphism, on ordinary unbounded derived module-object categories.
Source: blueprint main-20261015, proper-base-change-rational.proof.md (3)
(blueprint: lem-sfb-coefficient-projection-square).

Proof:
1. Transport the module tensors and geometric derived adjunctions to section-ring modules
using lem-pd-module-ringed-topos-derived-comparison. Transport scalar extension, restriction
and their units and counits using lem-sfb-internal-section-scalar-adjunction. Exact extension
makes restriction preserve K-injectives (lem-sfb-comap-preserves-k-injectives). The coefficient
square commutes. The K-injective normalization of derived pushforward composition identifies
its direct-image comparison with the inverse of derivedComapLowerStarIso. The conjugate
pullback comparison in lem-sfb-ringed-comparison-tensor-adjunction is therefore c inverse.
2. The tensor equation of that ringed comparison lemma identifies the composite tensorators
for T_X P_R and P_S T_Y. On flat-term K-flat representatives the scalar tensorator sends
s tensor (x tensor y) to (s tensor x) tensor (1 tensor y), so it is precisely mu here.
3. Expand derivedPushHom as the scalar-unit, inverse restriction comparison, scalar-counit
composite. Conjugacy of derivedPullIso and the composite adjunction counits, naturality,
and the scalar triangle identity give epsilon_S P_S(gamma_K) = T_X(epsilon_R) c_inverse.
4. Transpose the left composite under P_S adjoint to G_S. The definition of the projection
mate and naturality of the pullback tensor map give counit tensor identity after the
comparison. Insert step 3, then the tensor equation of step 2; naturality of mu rewrites it
as q T_X((epsilon_R tensor identity) d_R) c_inverse, with q = (identity tensor c_M) mu_X.
5. Transpose the right composite. Naturality of the counit and step 3 give
q T_X(epsilon_R) c_inverse P_S T_Y(pi_R). Naturality of c_inverse and the defining
transpose of pi_R rewrite this to the same expression as step 4. Injectivity of the
adjunction Hom bijection proves equality, without cancelling any projection or push map. -/
theorem coefficientProjectionSquare
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj R X.left)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj R Y.left))) :
    ((internalScalarTensorComparison a Y.left).app
        ((moduleObjectDerivedPushforward R f.left).obj K)).app M ≫
      ((derivedTensor S Y.left).map ((derivedPushHom a f.left).app K)).app
        ((internalScalarExtension a Y.left).obj M) ≫
      moduleObjectProjectionMap S f.left
        ((internalScalarExtension a X.left).obj K)
        ((internalScalarExtension a Y.left).obj M) =
    (internalScalarExtension a Y.left).map
        (moduleObjectProjectionMap R f.left K M) ≫
      (derivedPushHom a f.left).app
        (((derivedTensor R X.left).obj K).obj
          ((moduleObjectDerivedPullback R f.left).obj M)) ≫
      (moduleObjectDerivedPushforward S f.left).map
        (((internalScalarTensorComparison a X.left).app K).app
            ((moduleObjectDerivedPullback R f.left).obj M) ≫
          ((derivedTensor S X.left).obj
            ((internalScalarExtension a X.left).obj K)).map
              ((derivedPullIso a f.left).hom.app M)) := by
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R Z) := fun Z ↦ by
    have := IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence R Z)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules S Z) := fun Z ↦ by
    have := IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence S Z)
    exact HasDerivedCategory.ofIsGrothendieckAbelian _
  let α := (derivedPullIso a f.left).symm
  have hpath : coefficientScalarPathIso a f.left = α := by
    apply Iso.ext
    apply (conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction R f.left).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X.left)))
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y.left)).comp
        (derivedUpperStarLowerStarAdjunction S f.left))).injective
    calc
      _ = (derivedComapLowerStarIso a f.left).inv := path_conjugate a f.left
      _ = _ := ((conjugateEquiv _ _).apply_symm_apply _).symm
  have ht := (coefficientScalarTensorRealization a ℓ k f).2.2
  have hcompat : Adjunction.ComparisonCompatible
      (T_C := derivedTensor R X.left) (T_D := derivedTensor R Y.left)
      (T_C' := derivedTensor S X.left) (T_D' := derivedTensor S Y.left) α
      (leftDerivedUpperStarTensor R f.left) (leftDerivedUpperStarTensor S f.left)
      (internalScalarTensorIso a X.left) (internalScalarTensorIso a Y.left) := by
    intro A B
    have h := ht A B
    simp only [hpath] at h
    exact (Iso.eq_inv_comp (α.app (((derivedTensor R Y.left).obj A).obj B))).2 h.symm
  have hm : derivedPushHom a f.left =
      (mateEquiv (derivedUpperStarLowerStarAdjunction R f.left)
        (derivedUpperStarLowerStarAdjunction S f.left) (TwoSquare.mk _ _ _ _ α.hom)) := by
    exact push_eq_mate_pull_inv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X.left))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y.left))
      (derivedUpperStarLowerStarAdjunction R f.left)
      (derivedUpperStarLowerStarAdjunction S f.left) (derivedComapLowerStarIso a f.left)
  have h := Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv
      (T_C := derivedTensor R X.left) (T_D := derivedTensor R Y.left)
      (T_C' := derivedTensor S X.left) (T_D' := derivedTensor S Y.left)
      (derivedUpperStarLowerStarAdjunction R f.left)
      (derivedUpperStarLowerStarAdjunction S f.left) hcompat K M
  simp only [← hm] at h
  simpa only [moduleObjectProjectionMap, moduleObjectProjectionData,
    internalScalarTensorComparison, moduleObjectDerivedPushforward,
    moduleObjectDerivedPullback, internalScalarExtension, α, Iso.symm_inv] using h.symm

end AlgebraicGeometry.ProEtale.CondensedRing
