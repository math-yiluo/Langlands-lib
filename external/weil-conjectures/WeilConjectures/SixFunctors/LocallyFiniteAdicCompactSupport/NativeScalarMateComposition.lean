/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateData
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Composition of the canonical condensed scalar mates

Source: the formal-properties paragraph of the blueprint scalar direct-image proof.
(blueprint: lem-sf-native-scalar-derived-mate-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Mod.extendScalars
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  AlgebraicGeometry.ProEtale.upperStarFromPoint

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace CategoryTheory.TwoSquare

private theorem pasteComponent
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {T : A ⥤ D} {L : A ⥤ B} {R : D ⥤ E} {S : B ⥤ E}
    {L' : B ⥤ C} {R' : E ⥤ F} {B' : C ⥤ F}
    (w : TwoSquare T L R S) (w' : TwoSquare S L' R' B') (X : A) :
    (w.vComp w').app X = R'.map (w.app X) ≫ w'.app (L.obj X) := by
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

private theorem inverseMatePasteComponent
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (v : TwoSquare R₁ H G R₂) (w : TwoSquare R₃ K H R₄) (M : A) :
    (((mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (w.hComp v)).app M) =
      L₄.map (((mateEquiv a₁ a₂).symm v).app M) ≫
        ((mateEquiv a₃ a₄).symm w).app (L₁.obj M) := by
  have hp := mateEquiv_hcomp a₁ a₂ a₃ a₄
    ((mateEquiv a₁ a₂).symm v) ((mateEquiv a₃ a₄).symm w)
  simp only [Equiv.apply_symm_apply] at hp
  have he := congrArg (fun z ↦ (mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm z) hp
  simp only [Equiv.symm_apply_apply] at he
  exact (congrArg (fun z ↦ z.app M) he.symm).trans (pasteComponent _ _ M)

end CategoryTheory.TwoSquare

universe u
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicGeometry.ProEtale

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight

/-- The canonical derived extension/restriction adjunction for a condensed coefficient map.
Source: the existing derived extension/levelwise restriction adjunction.
(blueprint: lem-sf-native-scalar-derived-mate-composition). -/
def nativeScalarDerivedAdjunction
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (b : Λ ⟶ Γ) [IsMonHom b] (T : Scheme.{u}) :=
  @Mod.derivedExtendMapDerivedCategoryAdjunction _ _ _ _ _ _ _ _ _
    (condensedRingObj Λ T) (condensedRingObj Γ T) _ _
    (show IsCommMonObj (condensedRingObj Λ T) from isCommMonObj_condensedRingObj Λ T)
    (show IsCommMonObj (condensedRingObj Γ T) from isCommMonObj_condensedRingObj Γ T)
    (coefficientMap b T) _

/-- The inverse restriction/direct-image square, with the published geometric
functor names retained. Source: the canonical unbounded restriction comparison.
(blueprint: lem-sf-native-scalar-derived-mate-composition). -/
def nativeScalarDerivedRestrictionSquare
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (b : Λ ⟶ Γ) [IsMonHom b]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b T))]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    TwoSquare (Mod.comap (coefficientMap b U)).mapDerivedCategory
      (CondensedRing.moduleObjectDerivedPushforward Γ g)
      (CondensedRing.moduleObjectDerivedPushforward Λ g)
      (Mod.comap (coefficientMap b V)).mapDerivedCategory :=
  TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapLowerStarIso b g).inv

private theorem scalarDerivedMate
    {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    (b : Λ ⟶ Γ) [IsMonHom b]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b T))]
    {U V : Scheme.{u}} (g : U ⟶ V) :
    (mateEquiv (nativeScalarDerivedAdjunction b U) (nativeScalarDerivedAdjunction b V)).symm
        (nativeScalarDerivedRestrictionSquare b g) =
      TwoSquare.mk _ _ _ _ (CondensedRing.derivedPushHom b g) := by
  delta nativeScalarDerivedRestrictionSquare CondensedRing.moduleObjectDerivedPushforward
  rfl

/-- The composite of the two canonical scalar adjunctions, with the actual composite
restriction functor as right adjoint. Source: adjunction composition.
(blueprint: lem-sf-native-scalar-derived-mate-composition). -/
def nativeScalarDerivedCompositeAdjunction
    {Λ Γ Δ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    [MonObj Δ] [IsCommMonObj Δ]
    (b : Λ ⟶ Γ) (c : Γ ⟶ Δ) [IsMonHom b] [IsMonHom c] (T : Scheme.{u}) :=
  (nativeScalarDerivedAdjunction b T).comp (nativeScalarDerivedAdjunction c T)

/-- Inverse mates of the pasted restriction square are the successive scalar mates.
No geometric mate is assumed invertible. The two coefficient maps are flat so that
the specified unbounded restriction/direct-image comparisons exist.

Source: the formal-properties paragraph of the blueprint scalar direct-image proof;
Mathlib's mateEquiv_hcomp and the canonical derived extension/restriction adjunctions.
(blueprint: lem-sf-native-scalar-derived-mate-composition).

Proof in words: identify each derivedPushHom with the inverse mate of the inverse
restriction comparison, directly from its definition. The mate equivalence respects
horizontal composition of the right-adjoint squares and vertical composition of
the left-adjoint squares. Apply this equality to M. The component of vertical pasting
is the second extension functor applied to the first component, followed by the
second component at the first extended object. This is exactly the displayed formula. -/
theorem nativeScalarDerivedCompositeMate
    {Λ Γ Δ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
    [MonObj Δ] [IsCommMonObj Δ]
    (b : Λ ⟶ Γ) (c : Γ ⟶ Δ) [IsMonHom b] [IsMonHom c]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap b T))]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap c T))]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U))) :
    ((mateEquiv (nativeScalarDerivedCompositeAdjunction b c U)
        (nativeScalarDerivedCompositeAdjunction b c V)).symm
      ((nativeScalarDerivedRestrictionSquare c g).hComp
        (nativeScalarDerivedRestrictionSquare b g))).app M =
      (Mod.extendScalars (coefficientMap c V)).leftDerivedFunctor.map
          ((CondensedRing.derivedPushHom b g).app M) ≫
        (CondensedRing.derivedPushHom c g).app
          ((Mod.extendScalars (coefficientMap b U)).leftDerivedFunctor.obj M) := by
  let v := nativeScalarDerivedRestrictionSquare b g
  let w := nativeScalarDerivedRestrictionSquare c g
  have hi := scalarDerivedMate b g
  have hc := scalarDerivedMate c g
  have h := TwoSquare.inverseMatePasteComponent
    (nativeScalarDerivedAdjunction b U) (nativeScalarDerivedAdjunction b V)
    (nativeScalarDerivedAdjunction c U) (nativeScalarDerivedAdjunction c V) v w M
  have hs := congrArg₂
    (fun p q ↦ (Mod.extendScalars (coefficientMap c V)).leftDerivedFunctor.map p ≫ q)
    (congrArg (fun z ↦ z.app M) hi)
    (congrArg (fun z ↦ z.app
      ((Mod.extendScalars (coefficientMap b U)).leftDerivedFunctor.obj M)) hc)
  exact h.trans hs

end WeilConjectures.LocallyFiniteAdicCompactSupport
