/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! The canonical derived pullback comparison of a section respects the tensor unit. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

private theorem iso_component_congr {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} {s t : F ≅ G} (h : s = t) (M : C) :
    s.hom.app M = t.hom.app M := congrArg (fun e ↦ e.hom.app M) h

private theorem comp_right_congr {C : Type*} [Category* C]
    {A B D : C} (f : A ⟶ B) {g k : B ⟶ D} (h : g = k) : f ≫ g = f ≫ k :=
  congrArg (fun m ↦ f ≫ m) h

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local implicit_reducible] moduleObjectDerivedPullback

attribute [local irreducible] upperStar lowerStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor leftDerivedUpperStarComp leftDerivedUpperStarId
  leftDerivedUpperStarUnitIso

private def unit_comparison (X : Scheme.{u}) (f : X ⟶ X) :
    (moduleObjectDerivedPullback Λ f).obj (𝟙_ (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ⟶
        (𝟙_ (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) :=
  (leftDerivedUpperStarUnitIso Λ f).hom

private theorem unit_transport (X : Scheme.{u}) {f k : X ⟶ X} (h : f = k) :
    (eqToIso (congrArg (fun g : X ⟶ X ↦ moduleObjectDerivedPullback Λ g) h)).hom.app
        (𝟙_ (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ≫
          unit_comparison Λ X k = unit_comparison Λ X f := by
  subst k
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem transport_identity {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X) (h : g ≫ p = 𝟙 X) :
    (eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h)).hom.app
      (𝟙_ (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ≫
        (leftDerivedUpperStarId Λ X).hom.app (𝟙_ _) =
      (leftDerivedUpperStarUnitIso Λ (g ≫ p)).hom := by
  erw [leftDerivedUpperStarId_hom_app_unit]
  exact unit_transport Λ X (f := g ≫ p) (k := 𝟙 X) h

private def pullback_compositor {X S : Scheme.{u}} (g : X ⟶ S) (p : S ⟶ X) :
    moduleObjectDerivedPullback Λ (g ≫ p) ≅
      moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g :=
  leftDerivedUpperStarComp Λ g p

private theorem compositor_inverse {X S : Scheme.{u}} (g : X ⟶ S) (p : S ⟶ X) :
    (pullback_compositor Λ g p).inv.app (𝟙_ (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) ≫
        (leftDerivedUpperStarUnitIso Λ (g ≫ p)).hom =
      (upperStar Λ g).leftDerivedFunctor.map (leftDerivedUpperStarUnitIso Λ p).hom ≫
        (leftDerivedUpperStarUnitIso Λ g).hom := by
  apply (Iso.inv_comp_eq ((pullback_compositor Λ g p).app (𝟙_ _))).mpr
  exact (leftDerivedUpperStarComp_hom_app_unit Λ g p).symm

private theorem section_component_expansion {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X) (h : g ≫ p = 𝟙 X) :
    (((pullback_compositor Λ g p).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h) ≪≫
        leftDerivedUpperStarId Λ X).hom.app (𝟙_ (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))) =
      (pullback_compositor Λ g p).inv.app (𝟙_ _) ≫
        (eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h)).hom.app
          (𝟙_ _) ≫ (leftDerivedUpperStarId Λ X).hom.app (𝟙_ _) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

private theorem canonical_unit_components {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X) (h : g ≫ p = 𝟙 X) :
    (((pullback_compositor Λ g p).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h) ≪≫
        leftDerivedUpperStarId Λ X).hom.app (𝟙_ (DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))) =
      (upperStar Λ g).leftDerivedFunctor.map (leftDerivedUpperStarUnitIso Λ p).hom ≫
        (leftDerivedUpperStarUnitIso Λ g).hom := by
  exact (section_component_expansion Λ g p h).trans
    ((comp_right_congr ((pullback_compositor Λ g p).inv.app (𝟙_ _))
      (transport_identity Λ g p h)).trans (compositor_inverse Λ g p))

/-- The canonical pullback compositor followed by the identity comparison has the
canonical composite oplax unit as its component at the tensor unit. The comparison
is supplied with its canonical defining equality so its named functors stay folded.

Source: the second identity in blueprint
sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md; the component equations are
`leftDerivedUpperStarComp_hom_app_unit` and `leftDerivedUpperStarId_hom_app_unit`.
(blueprint: lem-sfb-canonical-derived-pullback-section-unit).

Proof: equality induction transports the unit comparison along the section equation.
Compose this equation with the identity unit equation. Cancel the pullback compositor
using its inverse and the composition unit equation. The result is the mapped unit
of the retraction followed by the unit of the section. This is exactly the canonical
unit map of the composite pullback. -/
theorem leftDerivedUpperStarSection_hom_app_unit {X S : Scheme.{u}}
    (g : X ⟶ S) (p : S ⟶ X) (h : g ≫ p = 𝟙 X)
    (s : moduleObjectDerivedPullback Λ p ⋙ moduleObjectDerivedPullback Λ g ≅
      𝟭 (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hs : s = (leftDerivedUpperStarComp Λ g p).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h) ≪≫
        leftDerivedUpperStarId Λ X) :
    s.hom.app (𝟙_ (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))) =
      (upperStar Λ g).leftDerivedFunctor.map (leftDerivedUpperStarUnitIso Λ p).hom ≫
        (leftDerivedUpperStarUnitIso Λ g).hom := by
  have he : s = (pullback_compositor Λ g p).symm ≪≫
      eqToIso (congrArg (fun f : X ⟶ X ↦ moduleObjectDerivedPullback Λ f) h) ≪≫
        leftDerivedUpperStarId Λ X := hs
  exact (iso_component_congr he (𝟙_ _)).trans (canonical_unit_components Λ g p h)

end AlgebraicGeometry.ProEtale.CondensedRing
