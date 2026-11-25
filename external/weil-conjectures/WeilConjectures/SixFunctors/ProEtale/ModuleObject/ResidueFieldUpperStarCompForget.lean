/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Coherence of the commutation of underlying abelian sheaves with pullback

The isomorphisms `g^* (forget₂ F) ≅ forget₂ (g^* F)` of
`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso` are compatible with the
composition isomorphisms `(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*` of pullbacks of pro-étale sheaves
(`AlgebraicGeometry.ProEtale.sheafComposeForget₂CompUpperStarIso_hom_app_comp`). Both are
conjugates of isomorphisms between the right adjoints, which commute strictly with
`sheafCompose`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- `sheafComposeForget₂CompUpperStarIso` is conjugate to the identity. -/
lemma conjugateEquiv_sheafComposeForget₂CompUpperStarIso_hom {X Y : Scheme.{u}} (g : Y ⟶ X) :
    conjugateEquiv
      ((upperStarLowerStarAdjunction _ g).comp (sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))))
      ((sheafComposeAdjunction _ (Adjunction.ofIsLeftAdjoint
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))).comp
          (upperStarLowerStarAdjunction _ g))
      (sheafComposeForget₂CompUpperStarIso Λ g).hom = 𝟙 _ :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (Iso.refl _))

set_option hygiene false in
local notation "aM" => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
set_option hygiene false in
local notation "aA" => ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}

/-- `sheafComposeForget₂CompUpperStarIso` is compatible with the composition isomorphisms
`(g₁ ≫ g)^* ≅ g^* ⋙ g₁^*`. -/
lemma sheafComposeForget₂CompUpperStarIso_hom_app_comp {T Z Y : Scheme.{u}} (g₁ : T ⟶ Z)
    (g : Z ⟶ Y) (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} Λ)) :
    (sheafComposeForget₂CompUpperStarIso Λ (g₁ ≫ g)).hom.app F ≫
        (sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g₁ g).hom.app F) =
      (ProEtale.upperStarComp AddCommGrpCat.{u + 1} g₁ g).hom.app
          ((sheafCompose (ProEt.topology Y)
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) ≫
        (ProEtale.upperStar _ g₁).map ((sheafComposeForget₂CompUpperStarIso Λ g).hom.app F) ≫
        (sheafComposeForget₂CompUpperStarIso Λ g₁).hom.app
          ((ProEtale.upperStar _ g).obj F) := by
  have key : (sheafComposeForget₂CompUpperStarIso Λ (g₁ ≫ g)).hom ≫
      Functor.whiskerRight (ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g₁ g).hom _ =
      Functor.whiskerLeft _ (ProEtale.upperStarComp AddCommGrpCat.{u + 1} g₁ g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (sheafComposeForget₂CompUpperStarIso Λ g).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (sheafComposeForget₂CompUpperStarIso Λ g₁).hom ≫
        (Functor.associator _ _ _).inv := by
    let a := Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    let eY := sheafComposeAdjunction (ProEt.topology Y) a
    let eZ := sheafComposeAdjunction (ProEt.topology Z) a
    let eT := sheafComposeAdjunction (ProEt.topology T) a
    apply (conjugateEquiv ((aM g).comp (aM g₁) |>.comp eT) (eY.comp (aA (g₁ ≫ g)))).injective
    rw [← conjugateEquiv_comp _ ((aM (g₁ ≫ g)).comp eT),
      ← conjugateEquiv_comp _ (eY.comp ((aA g).comp (aA g₁))),
      ← conjugateEquiv_comp _ ((eY.comp (aA g)).comp (aA g₁)),
      ← conjugateEquiv_comp _ (((aM g).comp eZ).comp (aA g₁)),
      ← conjugateEquiv_comp _ ((aM g).comp (eZ.comp (aA g₁))),
      ← conjugateEquiv_comp _ ((aM g).comp ((aM g₁).comp eT))]
    rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
      conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom, conjugateEquiv_associator_inv,
      conjugateEquiv_associator_inv, conjugateEquiv_sheafComposeForget₂CompUpperStarIso_hom,
      conjugateEquiv_sheafComposeForget₂CompUpperStarIso_hom,
      conjugateEquiv_sheafComposeForget₂CompUpperStarIso_hom,
      ProEtale.conjugateEquiv_upperStarComp_hom, ProEtale.conjugateEquiv_upperStarComp_hom]
    ext F U
    simp
    rfl
  simpa using NatTrans.congr_app key F

end AlgebraicGeometry.ProEtale
