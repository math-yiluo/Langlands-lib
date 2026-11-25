/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# Pullback of global sections of module objects

Let `Λ` be a commutative condensed ring. A global section of a module object `M` over
`Λ_T = p_T^* Λ` on a scheme `T` is a morphism `w : 𝟙_ ⟶ M` out of the unit `Λ_T`. Its pullback
along a morphism `a : S ⟶ T` is the global section `𝟙_ ≅ a^* 𝟙_ ⟶ a^* M` of `a^* M`. For
`M = b^* N` with `b : T ⟶ B` and `a ≫ b = t`, composing with `a^* b^* N ≅ (a ≫ b)^* N = t^* N`
gives a global section of `t^* N`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarSectionMap`). These pullbacks are
functorial: pulling back along `a'` and then along `a` is pulling back along `a ≫ a'`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperStarSectionMap_upperStarSectionMap`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {S T B : Scheme.{u}}

/-- The unit of module objects, written in the syntactic form of the type of the unit
comparisons `ε` of strong monoidal functors (see the implementation notes of
`WeilConjectures.WeilObject.Sheaf.StalkUnit`): as a notation rather than a definition, since the
kernel unfolds the pullbacks when a constant occurs as an argument of their components. -/
scoped notation "𝟙ₘ" =>
  @MonoidalCategoryStruct.tensorUnit _ _ MonoidalCategory.toMonoidalCategoryStruct

/-- The pullback of a global section `w : 𝟙_ ⟶ b^* N` along `a : S ⟶ T`, as a global section of
`t^* N` for `a ≫ b = t`: the composite `𝟙_ ≅ a^* 𝟙_ ⟶ a^* b^* N ≅ (a ≫ b)^* N = t^* N`. The
transport along `a ≫ b = t` is an `eqToHom` of objects, which keeps the kernel from unfolding
the pullbacks. -/
noncomputable def upperStarSectionMap (a : S ⟶ T) {b : T ⟶ B} {t : S ⟶ B} (h : a ≫ b = t)
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (w : 𝟙ₘ ⟶ (b)^*⟦Λ⟧.obj N) : 𝟙ₘ ⟶ (t)^*⟦Λ⟧.obj N :=
  (Functor.Monoidal.εIso (a)^*⟦Λ⟧).hom ≫ (a)^*⟦Λ⟧.map w ≫
    (upperStarComp Λ a b).inv.app N ≫ eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) h)

/-- The pullback of global sections only depends on the morphism up to equality. -/
lemma upperStarSectionMap_congr {a a' : S ⟶ T} (e : a = a') {b : T ⟶ B} {t : S ⟶ B}
    (h : a ≫ b = t) (h' : a' ≫ b = t)
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (w : 𝟙ₘ ⟶ (b)^*⟦Λ⟧.obj N) :
    upperStarSectionMap Λ a h N w = upperStarSectionMap Λ a' h' N w := by
  subst e
  rfl

/-- The unit comparison of the pullback along a composite: `ε_{a ≫ a'}` is `ε_a`, then
`a^* ε_{a'}`, then the composition isomorphism. -/
lemma εIso_hom_comp {R : Scheme.{u}} (a : S ⟶ T) (a' : T ⟶ R) :
    (Functor.Monoidal.εIso (a ≫ a')^*⟦Λ⟧).hom =
      (Functor.Monoidal.εIso (a)^*⟦Λ⟧).hom ≫ (a)^*⟦Λ⟧.map (Functor.Monoidal.εIso (a')^*⟦Λ⟧).hom ≫
        (upperStarComp Λ a a').inv.app _ := by
  rw [← cancel_mono (Functor.Monoidal.εIso (a ≫ a')^*⟦Λ⟧).inv, Iso.hom_inv_id,
    ← upperStarComp_hom_app_unit Λ a a', Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

/-- **The pullback of global sections is functorial**: pulling back along `a'` and then along
`a` is pulling back along `a ≫ a'`. -/
lemma upperStarSectionMap_upperStarSectionMap {R : Scheme.{u}} (a : S ⟶ T) (a' : T ⟶ R)
    {b : R ⟶ B} {t' : T ⟶ B} {t : S ⟶ B} (h₂ : a' ≫ b = t') (h₁ : a ≫ t' = t)
    (h₃ : (a ≫ a') ≫ b = t)
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))
    (w : 𝟙ₘ ⟶ (b)^*⟦Λ⟧.obj N) :
    upperStarSectionMap Λ a h₁ N (upperStarSectionMap Λ a' h₂ N w) =
      upperStarSectionMap Λ (a ≫ a') h₃ N w := by
  subst h₂ h₁
  have hc := upperStarComp_hom_app_comp_upperStarComp_hom_app Λ a a' b N
  rw [upperStarCongr_hom_app_eq_eqToHom] at hc
  have hc' : (upperStarComp Λ a a').inv.app ((b)^*⟦Λ⟧.obj N) ≫
      (upperStarComp Λ (a ≫ a') b).inv.app N ≫
        eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) h₃) =
      (a)^*⟦Λ⟧.map ((upperStarComp Λ a' b).inv.app N ≫
          eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) (rfl : a' ≫ b = a' ≫ b))) ≫
        (upperStarComp Λ a (a' ≫ b)).inv.app N ≫
          eqToHom (congrArg (fun s ↦ (s)^*⟦Λ⟧.obj N) (rfl : a ≫ a' ≫ b = a ≫ a' ≫ b)) := by
    conv_rhs => simp only [eqToHom_refl, Category.comp_id]
    rw [← cancel_epi ((upperStarComp Λ (a ≫ a') b).hom.app N ≫
      (upperStarComp Λ a a').hom.app ((b)^*⟦Λ⟧.obj N))]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  rw [upperStarSectionMap, upperStarSectionMap, upperStarSectionMap, εIso_hom_comp,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (upperStarComp Λ a a').inv.naturality_assoc w, Functor.comp_map, hc']

end AlgebraicGeometry.ProEtale.CondensedRing
