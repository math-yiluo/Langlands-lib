/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Ring

/-! # Scalar localization of a permitted contravariant bilinear functor

Extracted proved scalar-localization calculus used by the derived-operation construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v r s u₁ v₁ u₂ v₂
open Opposite TensorProduct CategoryTheory
namespace WeilConjectures.OperationsScalarLocalization

section HomLocalization
set_option backward.defeqAttrib.useBackward false
variable {D : Type*} [Category* D] [Preadditive D]
  (A : Type*) [CommRing A] [Linear A D] (p : A)
  (q : ObjectProperty (Dᵒᵖ × D)) (B : q.FullSubcategory ⥤ D)

variable (q' : ObjectProperty ((ScalarLocalization A D p)ᵒᵖ × ScalarLocalization A D p))
  (hq' : ∀ X, q' X → q (op X.1.unop.obj, X.2.obj))

private abbrev homLocalizationIntegralPair
    (P : q'.FullSubcategory) : q.FullSubcategory :=
  ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq' P.obj P.property⟩

variable (β : ∀ P Q : q.FullSubcategory,
    (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[A] (P.obj.2 ⟶ Q.obj.2) →ₗ[A]
      (B.obj P ⟶ B.obj Q))
  (hβ : ∀ (P Q : q.FullSubcategory)
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (b : P.obj.2 ⟶ Q.obj.2),
    β P Q a b = B.map (ObjectProperty.homMk (Prod.mkHom a.op b)))

private def homLocalizedAction
    (P Q : q'.FullSubcategory) :
    (Localization.Away p ⊗[A] (Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj))
      →ₗ[Localization.Away p]
      (Localization.Away p ⊗[A] (P.obj.2.obj ⟶ Q.obj.2.obj))
      →ₗ[Localization.Away p]
        (Localization.Away p ⊗[A]
          (B.obj (homLocalizationIntegralPair A p q q' hq' P) ⟶
            B.obj (homLocalizationIntegralPair A p q q' hq' Q))) :=
  TensorProduct.curry
    (((TensorProduct.lift (β (homLocalizationIntegralPair A p q q' hq' P)
      (homLocalizationIntegralPair A p q q' hq' Q))).baseChange (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange A (Localization.Away p)
          (Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (P.obj.2.obj ⟶ Q.obj.2.obj)).symm.toLinearMap)

include hβ

private theorem homLocalizedAction_tmul
    (P Q : q'.FullSubcategory)
    (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (b : P.obj.2.obj ⟶ Q.obj.2.obj)
    (x y : Localization.Away p) :
    homLocalizedAction A p q B q' hq' β P Q (x ⊗ₜ[A] a) (y ⊗ₜ[A] b) =
      (x * y) ⊗ₜ[A] B.map
        (ObjectProperty.homMk (X := homLocalizationIntegralPair A p q q' hq' P)
          (Y := homLocalizationIntegralPair A p q q' hq' Q) (Prod.mkHom a.op b)) := by
  simp [homLocalizedAction, hβ]

attribute [local irreducible] homLocalizedAction

private theorem homLocalizedAction_comp
    (P Q T : q'.FullSubcategory)
    (a : Q.obj.1.unop ⟶ P.obj.1.unop) (a' : T.obj.1.unop ⟶ Q.obj.1.unop)
    (b : P.obj.2 ⟶ Q.obj.2) (b' : Q.obj.2 ⟶ T.obj.2) :
    homLocalizedAction A p q B q' hq' β P T (a' ≫ a) (b ≫ b') =
      ScalarLocalization.composition A D p _ _ _
        (homLocalizedAction A p q B q' hq' β Q T a' b')
        (homLocalizedAction A p q B q' hq' β P Q a b) := by
  change homLocalizedAction A p q B q' hq' β P T
      (ScalarLocalization.composition A D p _ _ _ a a')
      (ScalarLocalization.composition A D p _ _ _ b' b) = _
  change Localization.Away p ⊗[A] (Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) at a
  change Localization.Away p ⊗[A] (T.obj.1.unop.obj ⟶ Q.obj.1.unop.obj) at a'
  change Localization.Away p ⊗[A] (P.obj.2.obj ⟶ Q.obj.2.obj) at b
  change Localization.Away p ⊗[A] (Q.obj.2.obj ⟶ T.obj.2.obj) at b'
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul x a =>
    induction a' using TensorProduct.inductionOn with
    | add a' c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
    | tmul x' a' =>
      induction b using TensorProduct.inductionOn with
      | add b c hb hc => simp only [map_add, hb, hc]
      | tmul y b =>
        induction b' using TensorProduct.inductionOn with
        | add b' c hb hc => simp only [map_add, LinearMap.add_apply, hb, hc]
        | tmul y' b' =>
          simp only [ScalarLocalization.composition_tmul,
            homLocalizedAction_tmul A p q B q' hq' β hβ]
          have he : B.map (ObjectProperty.homMk
              (X := homLocalizationIntegralPair A p q q' hq' P)
              (Y := homLocalizationIntegralPair A p q q' hq' T)
              (Prod.mkHom (a' ≫ a).op (b ≫ b'))) =
              B.map (ObjectProperty.homMk
                (X := homLocalizationIntegralPair A p q q' hq' P)
                (Y := homLocalizationIntegralPair A p q q' hq' Q) (Prod.mkHom a.op b)) ≫
              B.map (ObjectProperty.homMk
                (X := homLocalizationIntegralPair A p q q' hq' Q)
                (Y := homLocalizationIntegralPair A p q q' hq' T) (Prod.mkHom a'.op b')) := by
            exact B.map_comp
              (ObjectProperty.homMk (X := homLocalizationIntegralPair A p q q' hq' P)
                (Y := homLocalizationIntegralPair A p q q' hq' Q) (Prod.mkHom a.op b))
              (ObjectProperty.homMk (X := homLocalizationIntegralPair A p q q' hq' Q)
                (Y := homLocalizationIntegralPair A p q q' hq' T) (Prod.mkHom a'.op b'))
          rw [he]
          congr 1
          ring

private def homLocalizedFunctor :
    q'.FullSubcategory ⥤ ScalarLocalization A D p where
  obj P := ⟨B.obj (homLocalizationIntegralPair A p q q' hq' P)⟩
  map {P Q} f := homLocalizedAction A p q B q' hq' β P Q f.hom.1.unop f.hom.2
  map_id P := by
    change homLocalizedAction A p q B q' hq' β P P (1 ⊗ₜ[A] 𝟙 _) (1 ⊗ₜ[A] 𝟙 _) = _
    rw [homLocalizedAction_tmul A p q B q' hq' β hβ, one_mul]
    congr 1
    exact B.map_id _
  map_comp {P Q T} f g :=
    homLocalizedAction_comp A p q B q' hq' β hβ P Q T f.hom.1.unop g.hom.1.unop f.hom.2 g.hom.2

/-- Scalar localization of a permitted contravariant bilinear functor.
Source: module base change (Stacks 00CV, 00CX), and the rational paragraph of
blueprint `prose-03-02`.
(blueprint: lem-sf-localized-permitted-hom).
Proof: Base change the integral bilinear Hom map and compose with the inverse distribution
isomorphism for base change of tensor products. Curry to obtain the localized separately linear
action. Its value on pure tensors multiplies the two coefficients. Four tensor inductions prove
compatibility with composition from the integral functor laws and commutativity of coefficients;
identities follow from the pure-tensor formula. This constructs the functor on the permitted full
subcategory. Double tensor induction and functor extensionality prove uniqueness. The object
restriction is used only to supply the underlying permitted integral pairs. -/
theorem restrictedHom_existsUnique :
    ∃! F : q'.FullSubcategory ⥤ ScalarLocalization A D p,
      (∀ P, F.obj P = ⟨B.obj (⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq' P.obj P.property⟩)⟩) ∧
      (∀ P Q : q'.FullSubcategory,
        ∃ b : (Q.obj.1.unop ⟶ P.obj.1.unop) →ₗ[Localization.Away p]
          (P.obj.2 ⟶ Q.obj.2) →ₗ[Localization.Away p] (F.obj P ⟶ F.obj Q),
          (∀ a b', F.map (ObjectProperty.homMk (Prod.mkHom a.op b')) = b a b') ∧
          ∀ (a : Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) (b' : P.obj.2.obj ⟶ Q.obj.2.obj)
            (c d : Localization.Away p),
            HEq (b (c ⊗ₜ[A] a) (d ⊗ₜ[A] b'))
              ((c * d) ⊗ₜ[A] B.map (ObjectProperty.homMk
                (X := ⟨(op P.obj.1.unop.obj, P.obj.2.obj), hq' P.obj P.property⟩)
                (Y := ⟨(op Q.obj.1.unop.obj, Q.obj.2.obj), hq' Q.obj Q.property⟩)
                (Prod.mkHom a.op b')))) := by
  let F := homLocalizedFunctor A p q B q' hq' β hβ
  refine ⟨F, ⟨fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro P Q
    refine ⟨homLocalizedAction A p q B q' hq' β P Q, fun _ _ ↦ rfl, ?_⟩
    intro a b c d
    exact heq_of_eq (homLocalizedAction_tmul A p q B q' hq' β hβ P Q a b c d)
  · intro G hG
    refine CategoryTheory.Functor.ext hG.1 ?_
    intro P Q f
    obtain ⟨γ, hγ, pγ⟩ := hG.2 P Q
    change G.map (ObjectProperty.homMk (Prod.mkHom f.hom.1.unop.op f.hom.2)) = _
    rw [hγ]
    change γ f.hom.1.unop f.hom.2 = _ ≫
      homLocalizedAction A p q B q' hq' β P Q f.hom.1.unop f.hom.2 ≫ _
    generalize f.hom.1.unop = a, f.hom.2 = b
    change Localization.Away p ⊗[A] (Q.obj.1.unop.obj ⟶ P.obj.1.unop.obj) at a
    change Localization.Away p ⊗[A] (P.obj.2.obj ⟶ Q.obj.2.obj) at b
    induction a using TensorProduct.inductionOn with
    | tmul c a =>
      induction b using TensorProduct.inductionOn with
      | tmul d b =>
        apply (conj_eqToHom_iff_heq _ _ (hG.1 P) (hG.1 Q)).2
        exact (pγ a b c d).trans
          (heq_of_eq (homLocalizedAction_tmul A p q B q' hq' β hβ P Q a b c d).symm)
      | add a b ha hb =>
        simp only [map_add]
        erw [Preadditive.add_comp, Preadditive.comp_add]
        exact congrArg₂ (· + ·) ha hb
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply]
      erw [Preadditive.add_comp, Preadditive.comp_add]
      exact congrArg₂ (· + ·) ha hb

end HomLocalization

end WeilConjectures.OperationsScalarLocalization
