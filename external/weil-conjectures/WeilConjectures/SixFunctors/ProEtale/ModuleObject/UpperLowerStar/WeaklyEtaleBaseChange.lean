/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.PushforwardFamilyTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.DisjointUnion

/-!

# Weakly étale base change for the pushforward of module objects

For a cartesian square `g' ≫ f = f' ≫ g` of schemes with `g` and `g'` weakly étale, the
base-change morphism `g^* f_* ⟶ f'_* g'^*` of module objects over a condensed ring `Λ`
(`ProEtale.CondensedRing.lowerStarBaseChange`) is an isomorphism
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isPullback`).

On underlying sheaves, the pullback of module objects is the pullback of sheaves up to the
isomorphism `ProEtale.CondensedRing.upperStarUnitHom` (the extension of scalars being along an
isomorphism), and the pushforward is the pushforward of sheaves. These identifications are
pseudonatural (`ProEtale.CondensedRing.pullbackPseudonatural_upperStarForgetIso`) and compatible
with the units and the counits, so the base-change morphism of module objects is, on underlying
sheaves, the exchange morphism of the comparison of the pullbacks of sheaves
(`CategoryTheory.PullbackPseudonatural.isIso_map_pushforwardBaseChange_app`). The latter is the
weakly étale base change map of sheaves (`ProEtale.baseChangeMap_eq_mateEquiv`), an isomorphism
for a cartesian square (`ProEtale.isIso_baseChangeMap_of_isPullback`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- The underlying sheaf of the pullback of a module object is the pullback of its underlying
sheaf, through `upperStarUnitHom`. -/
noncomputable def upperStarForgetIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.forget (condensedRingObj Λ Y) ⋙ (f)^*[Ab.{u + 1}] ≅
      (f)^*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ X) :=
  NatIso.ofComponents (fun M ↦ asIso (upperStarUnitHom Λ f M))
    fun h ↦ (upperStarUnitHom_map_hom Λ f h).symm

@[simp]
lemma upperStarForgetIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarForgetIso Λ f).hom.app M = upperStarUnitHom Λ f M :=
  rfl

/-- The underlying sheaf of the pushforward of a module object is the pushforward of its
underlying sheaf. -/
noncomputable def lowerStarForgetIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod.forget (condensedRingObj Λ X) ⋙ (f)_*[Ab.{u + 1}] ≅
      (f)_*⟦Λ⟧ ⋙ Mod.forget (condensedRingObj Λ Y) :=
  Iso.refl _

/-- The unit of `f^* ⊣ f_*` on module objects is, on underlying sheaves, the unit on sheaves
followed by the identifications `upperStarForgetIso` and `lowerStarForgetIso`. -/
lemma forget_map_upperStarLowerStarAdjunction_unit_app' {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (Mod.forget _).map ((upperStarLowerStarAdjunction Λ f).unit.app M) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app ((Mod.forget _).obj M) ≫
        (f)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ f).hom.app M) ≫
        (lowerStarForgetIso Λ f).hom.app ((f)^*⟦Λ⟧.obj M) :=
  (upperStarLowerStarAdjunction_unit_app_hom Λ f M).trans (Category.comp_id _).symm

/-- The counit of `f^* ⊣ f_*` on module objects is, on underlying sheaves, the counit on sheaves,
through the identifications `upperStarForgetIso` and `lowerStarForgetIso`. -/
lemma forget_map_upperStarLowerStarAdjunction_counit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (f)^*[Ab.{u + 1}].map ((lowerStarForgetIso Λ f).hom.app N) ≫
        (upperStarForgetIso Λ f).hom.app ((f)_*⟦Λ⟧.obj N) ≫
        (Mod.forget _).map ((upperStarLowerStarAdjunction Λ f).counit.app N) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).counit.app ((Mod.forget _).obj N) := by
  have h₁ : (f)^*[Ab.{u + 1}].map ((lowerStarForgetIso Λ f).hom.app N) = 𝟙 _ :=
    (f)^*[Ab.{u + 1}].map_id _
  rw [h₁, Category.id_comp]
  apply ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
  have h := upperStarLowerStarAdjunction_homEquiv_hom Λ f ((f)_*⟦Λ⟧.obj N) N
    ((upperStarLowerStarAdjunction Λ f).counit.app N)
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Mod.id_hom'] at h
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, upperStarForgetIso_hom_app]
  erw [Adjunction.right_triangle_components]
  exact h.symm

/-- The identifications `upperStarForgetIso` of the pullbacks of module objects with the
pullbacks of their underlying sheaves are compatible with the composition isomorphisms. -/
lemma upperStarComp_hom_app_upperStarForgetIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
    (ProEtale.upperStarComp Ab.{u + 1} f g).hom.app ((Mod.forget _).obj M) ≫
        (f)^*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) ≫
        (upperStarForgetIso Λ f).hom.app ((g)^*⟦Λ⟧.obj M) =
      (upperStarForgetIso Λ (f ≫ g)).hom.app M ≫
        (Mod.forget _).map ((upperStarComp Λ f g).hom.app M) :=
  (upperStarUnitHom_upperStarComp_hom_app_hom Λ f g M).symm

/-- The identifications `upperStarForgetIso` are pseudonatural. -/
lemma pullbackPseudonatural_upperStarForgetIso :
    PullbackPseudonatural (C := Scheme.{u})
      (D := fun X ↦ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (E := fun X ↦ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (P := fun f ↦ (f)^*[Ab.{u + 1}]) (fun f g ↦ ProEtale.upperStarComp Ab.{u + 1} f g)
      (L := fun f ↦ (f)^*⟦Λ⟧) (fun f g ↦ upperStarComp Λ f g)
      (H := fun X ↦ Mod.forget (condensedRingObj Λ X)) (fun f ↦ upperStarForgetIso Λ f) :=
  PullbackPseudonatural.of_hom_app fun f g M ↦ upperStarComp_hom_app_upperStarForgetIso Λ f g M

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The base-change morphism of module objects is that of the family of pullbacks of module
objects. -/
lemma lowerStarBaseChange_eq_pushforwardBaseChange (sq : CommSq g' f' f g) :
    lowerStarBaseChange Λ sq = pushforwardBaseChange (P := fun f ↦ (f)^*⟦Λ⟧)
      (fun f g ↦ upperStarComp Λ f g) (fun f ↦ upperStarLowerStarAdjunction Λ f) sq.w :=
  rfl

/-- **Weakly étale base change for the pushforward of module objects**: for a cartesian square
`g' ≫ f = f' ≫ g` with `g` and `g'` weakly étale, the base-change morphism
`g^* f_* ⟶ f'_* g'^*` of module objects is an isomorphism. -/
theorem isIso_lowerStarBaseChange_of_isPullback (hsq : IsPullback g' f' f g) [WeaklyEtale g]
    [WeaklyEtale g'] : IsIso (lowerStarBaseChange Λ hsq.toCommSq) := by
  have hb : pushforwardBaseChange (P := fun f ↦ (f)^*[Ab.{u + 1}])
      (fun f g ↦ ProEtale.upperStarComp Ab.{u + 1} f g)
      (fun f ↦ ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f) hsq.w =
      ProEtale.baseChangeMap Ab.{u + 1} hsq.toCommSq.flip := by
    rw [ProEtale.baseChangeMap_eq_mateEquiv, pushforwardBaseChange,
      Adjunction.exchangeRight_eq_mateEquiv]
    rfl
  have hiso : IsIso (pushforwardBaseChange (P := fun f ↦ (f)^*[Ab.{u + 1}])
      (fun f g ↦ ProEtale.upperStarComp Ab.{u + 1} f g)
      (fun f ↦ ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f) hsq.w) := by
    rw [hb]
    exact ProEtale.isIso_baseChangeMap_of_isPullback Ab.{u + 1} hsq.flip
  clear hb
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h := PullbackPseudonatural.isIso_map_pushforwardBaseChange_app
    (@pullbackPseudonatural_upperStarForgetIso Λ _ _)
    (fun f ↦ upperStarLowerStarAdjunction Λ f)
    (fun f ↦ ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f) (fun f ↦ lowerStarForgetIso Λ f)
    (fun f K ↦ forget_map_upperStarLowerStarAdjunction_unit_app' Λ f K)
    (fun f K ↦ forget_map_upperStarLowerStarAdjunction_counit_app Λ f K) hsq.w hiso M
  rw [← lowerStarBaseChange_eq_pushforwardBaseChange] at h
  exact isIso_of_reflects_iso _ (Mod.forget _)

end AlgebraicGeometry.ProEtale.CondensedRing
