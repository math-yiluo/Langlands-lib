/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import all WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData

/-! # Components of ambient pullback coherence

Source: Stacks 03CB, 03D3, 03EL, 07A4 and 04VG.
(blueprint: lem-sf-ambient-coefficient-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

private theorem ringUnit_composition {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    ringUnit ell E g s ≫ (ringPush g s).map (ringUnit ell E f s) ≫
      (ringPushComp f g s).hom.app (coefficients ell E X s) =
        ringUnit ell E (f ≫ g) s := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  cases s with
  | some n => exact constantMap_comp f g _ U
  | none =>
    change (Scheme.coefficientProEtaleDirectRingMap.{t, u} g _).hom.app (op U.unop.2) ≫
        (Scheme.coefficientProEtaleDirectRingMap.{t, u} f _).hom.app
          (op ((Scheme.proEtaleBaseChange g).obj U.unop.2)) ≫
        (coefficientSequenceCommRingSheaf ell E X).obj.map
          (Prod.mkHom (𝟙 U.unop.1)
            ((MorphismProperty.Over.pullbackComp f g).hom.app U.unop.2)).op = _
    rw [sequenceRing_map_vertical]
    exact constantMap_comp f g _ (op U.unop.2)

private theorem homEquiv_comparison
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {X : C} {Y : D} (z : L'.obj X ⟶ Y) :
    a.homEquiv X Y (((conjugateIsoEquiv a b).symm d.symm).inv.app X ≫ z) =
      b.homEquiv X Y z ≫ d.hom.app Y := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app X ≫
      R.map (((conjugateEquiv b a).symm d.hom).app X)) ≫ R.map z = _
  rw [← unit_conjugateEquiv_symm b a d.hom X, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

private theorem adjunct_composition
    {C D F : Type*} [Category C] [Category D] [Category F]
    {L₁ : C ⥤ D} {L₂ : D ⥤ F} {L₃ : C ⥤ F}
    {R₁ : D ⥤ C} {R₂ : F ⥤ D} {R₃ : F ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃)
    (e : R₂ ⋙ R₁ ≅ R₃) {X : C} {Y : D} {Z : F}
    (r₁ : X ⟶ R₁.obj Y) (r₂ : Y ⟶ R₂.obj Z) (r₃ : X ⟶ R₃.obj Z)
    (h : r₁ ≫ R₁.map r₂ ≫ e.hom.app Z = r₃) :
    (c.homEquiv X Z).symm r₃ =
      (Adjunction.leftAdjointCompIso a b c e).inv.app X ≫
        L₂.map ((a.homEquiv X Y).symm r₁) ≫ (b.homEquiv Y Z).symm r₂ := by
  apply (c.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  change _ = c.homEquiv _ _
    (((conjugateIsoEquiv c (a.comp b)).symm e.symm).inv.app _ ≫ _)
  rw [homEquiv_comparison, Adjunction.comp_homEquiv]
  change _ = a.homEquiv _ _ (b.homEquiv _ _ _) ≫ _
  rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simpa only [Category.assoc] using h.symm

/-- Composition of the actual coefficient adjuncts, with the specified mate.
Source: Stacks 03CB and 03D3 (blueprint: lem-sf-ambient-coefficient-composition). -/
theorem ringMap_composition {X Y Z : Scheme.{t}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (s : Option ℕ) :
    ringMap ell E (f ≫ g) s =
      (ringComp f g s).hom.app (coefficients ell E Z s) ≫
        (ringPull f s).map (ringMap ell E g s) ≫ ringMap ell E f s := by
  exact adjunct_composition
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} g s))
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} f s))
    (Adjunction.ofIsRightAdjoint (ringPush.{t, u} (f ≫ g) s))
    (ringPushComp f g s) (ringUnit ell E g s) (ringUnit ell E f s)
    (ringUnit ell E (f ≫ g) s) (ringUnit_composition ell E f g s)

end WeilConjectures.AmbientPullbackTensor
