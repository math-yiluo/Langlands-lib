/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Coherence of the commutation of scalar extension with pullback

The isomorphisms `g^* (S ⊗_R F) ≅ S ⊗_R g^* F` of
`AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso` are compatible with the identity
isomorphisms `(𝟙 X)^* ≅ 𝟭` and with the composition isomorphisms
`(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*` of pullbacks of pro-étale sheaves. All of these are conjugates of
isomorphisms between the right adjoints, which commute strictly with restriction of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]

/-- The conjugate of the inverse associator of left adjoints is the inverse associator of the
right adjoints. (A private copy of the lemma of the same name in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars`, which this file
cannot import.) -/
private lemma conjugateEquiv_associator_inv {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C}
    {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  have := conjugateEquiv_comm ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
    (α := (Functor.associator L₀₁ L₁₂ L₂₃).inv) (β := (Functor.associator L₀₁ L₁₂ L₂₃).hom)
    (by simp)
  rw [conjugateEquiv_associator_hom] at this
  rw [← cancel_mono (Functor.associator R₃₂ R₂₁ R₁₀).hom, this]
  simp

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

/-- `sheafExtendScalarsCompUpperStarIso` is conjugate to the identity. -/
lemma conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom {X Y : Scheme.{u}} (g : Y ⟶ X) :
    conjugateEquiv ((ProEtale.upperStarLowerStarAdjunction _ g).comp
        (sheafExtendScalarsAdjunction φ Y))
      ((sheafExtendScalarsAdjunction φ X).comp (ProEtale.upperStarLowerStarAdjunction _ g))
      (sheafExtendScalarsCompUpperStarIso φ g).hom = 𝟙 _ :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
    (lowerStarCompSheafComposeRestrictScalarsIso φ g).symm)

/-- `sheafExtendScalarsCompUpperStarIso` is compatible with the identity isomorphisms
`(𝟙 X)^* ≅ 𝟭`. -/
lemma sheafExtendScalarsCompUpperStarIso_hom_app_id (X : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (sheafExtendScalarsCompUpperStarIso φ (𝟙 X)).hom.app F ≫
        (sheafExtendScalars φ X).map
          ((ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom.app F) =
      (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom.app
        ((sheafExtendScalars φ X).obj F) := by
  have key : (sheafExtendScalarsCompUpperStarIso φ (𝟙 X)).hom ≫
      Functor.whiskerRight (ProEtale.upperStarId (ModuleCat.{u + 1} R) X).hom _ ≫
        (Functor.leftUnitor _).hom =
      Functor.whiskerLeft _ (ProEtale.upperStarId (ModuleCat.{u + 1} S) X).hom ≫
        (Functor.rightUnitor _).hom := by
    apply (conjugateEquiv (sheafExtendScalarsAdjunction φ X)
      ((sheafExtendScalarsAdjunction φ X).comp
        (ProEtale.upperStarLowerStarAdjunction _ (𝟙 X)))).injective
    rw [← conjugateEquiv_comp _ ((sheafExtendScalarsAdjunction φ X).comp Adjunction.id),
      ← conjugateEquiv_comp _ ((ProEtale.upperStarLowerStarAdjunction _ (𝟙 X)).comp
        (sheafExtendScalarsAdjunction φ X)),
      ← conjugateEquiv_comp _ (Adjunction.id.comp (sheafExtendScalarsAdjunction φ X)),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_rightUnitor_hom,
      conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom]
    have h₁ := congrArg Iso.hom (ProEtale.conjugateIsoEquiv_upperStarId (ModuleCat.{u + 1} R) X)
    have h₂ := congrArg Iso.hom (ProEtale.conjugateIsoEquiv_upperStarId (ModuleCat.{u + 1} S) X)
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at h₁ h₂
    rw [h₁, h₂]
    ext F U
    rfl
  simpa using NatTrans.congr_app key F

set_option hygiene false in
local notation "aS" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} S)
set_option hygiene false in
local notation "aR" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R)

/-- `sheafExtendScalarsCompUpperStarIso` is compatible with the composition isomorphisms
`(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*`. -/
lemma sheafExtendScalarsCompUpperStarIso_hom_app_comp {T Z Y : Scheme.{u}} (g₁ : T ⟶ Z)
    (g : Z ⟶ Y) (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)) :
    (sheafExtendScalarsCompUpperStarIso φ (g₁ ≫ g)).hom.app F ≫
        (sheafExtendScalars φ T).map
          ((ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom.app F) =
      (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom.app
          ((sheafExtendScalars φ Y).obj F) ≫
        (ProEtale.upperStar _ g₁).map ((sheafExtendScalarsCompUpperStarIso φ g).hom.app F) ≫
        (sheafExtendScalarsCompUpperStarIso φ g₁).hom.app ((ProEtale.upperStar _ g).obj F) := by
  have key : (sheafExtendScalarsCompUpperStarIso φ (g₁ ≫ g)).hom ≫
      Functor.whiskerRight (ProEtale.upperStarComp (ModuleCat.{u + 1} R) g₁ g).hom _ =
      Functor.whiskerLeft _ (ProEtale.upperStarComp (ModuleCat.{u + 1} S) g₁ g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (sheafExtendScalarsCompUpperStarIso φ g).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (sheafExtendScalarsCompUpperStarIso φ g₁).hom ≫
        (Functor.associator _ _ _).inv := by
    let eY := sheafExtendScalarsAdjunction φ Y
    let eZ := sheafExtendScalarsAdjunction φ Z
    let eT := sheafExtendScalarsAdjunction φ T
    apply (conjugateEquiv ((aR g).comp (aR g₁) |>.comp eT) (eY.comp (aS (g₁ ≫ g)))).injective
    rw [← conjugateEquiv_comp _ ((aR (g₁ ≫ g)).comp eT),
      ← conjugateEquiv_comp _ (eY.comp ((aS g).comp (aS g₁))),
      ← conjugateEquiv_comp _ ((eY.comp (aS g)).comp (aS g₁)),
      ← conjugateEquiv_comp _ (((aR g).comp eZ).comp (aS g₁)),
      ← conjugateEquiv_comp _ ((aR g).comp (eZ.comp (aS g₁))),
      ← conjugateEquiv_comp _ ((aR g).comp ((aR g₁).comp eT))]
    rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
      conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom, conjugateEquiv_associator_inv,
      conjugateEquiv_associator_inv, conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      conjugateEquiv_sheafExtendScalarsCompUpperStarIso_hom,
      ProEtale.conjugateEquiv_upperStarComp_hom, ProEtale.conjugateEquiv_upperStarComp_hom]
    ext F U
    simp
    rfl
  simpa using NatTrans.congr_app key F

end AlgebraicGeometry.ProEtale
