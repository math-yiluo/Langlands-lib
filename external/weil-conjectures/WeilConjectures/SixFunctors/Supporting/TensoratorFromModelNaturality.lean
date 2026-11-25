/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # Naturality of a tensorator given by finite models and a unit comparison -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace WeilConjectures

/-- Correct a natural tensor model by its unit isomorphism, component by component.
Source: thm-sf-pf-field.proof.md, Compatibility; naturality of the coefficient-unit maps.
(blueprint: lem-sf-tensorator-from-model-naturality).
Proof: assemble the model isomorphisms into a natural isomorphism, compose it with
its whiskered unit comparison, and take the inverse. Its naturality equation is
exactly the stated equation after evaluating the two components. -/
theorem tensoratorFromModel_naturality
    {A B : Type*} [Category* A] [Category* B]
    (I : A ⥤ B) (R : A × A ⥤ A) (T : B × B ⥤ B)
    {S : A ⥤ A} (U : S ≅ 𝟭 A)
    (m : ∀ K : A × A, T.obj (I.obj K.1, I.obj K.2) ≅
      I.obj (R.obj (S.obj K.1, S.obj K.2)))
    (hm : ∀ {K L : A × A} (f : K ⟶ L),
      T.map (Prod.mkHom (I.map f.1) (I.map f.2)) ≫ (m L).hom =
        (m K).hom ≫ I.map (R.map (Prod.mkHom (S.map f.1) (S.map f.2))))
    {K L : A × A} (f : K ⟶ L) :
    (R ⋙ I).map f ≫
        (m L ≪≫ I.mapIso (R.mapIso (Iso.prod (U.app L.1) (U.app L.2)))).inv =
      (m K ≪≫ I.mapIso (R.mapIso (Iso.prod (U.app K.1) (U.app K.2)))).inv ≫
        (I.prod I ⋙ T).map f := by
  let a : I.prod I ⋙ T ≅ S.prod S ⋙ (R ⋙ I) := NatIso.ofComponents m hm
  let t := (a ≪≫ Functor.isoWhiskerRight (NatIso.prod U U) (R ⋙ I)).symm
  exact t.hom.naturality f

end WeilConjectures
