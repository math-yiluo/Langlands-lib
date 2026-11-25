/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!

# The base-change morphism of the pushforward of module objects

The base-change morphism `g^* f_* ⟶ f'_* g'^*` of a commutative square `g' ≫ f = f' ≫ g` of
schemes, on module objects over a condensed ring `Λ` on the pro-étale sites
(`ProEtale.CondensedRing.lowerStarBaseChange`), is the exchange morphism
`CategoryTheory.Adjunction.exchangeRight` of the comparison
`ProEtale.CondensedRing.upperStarSquareComparison` of the composition isomorphisms of the
pullbacks. It is an isomorphism when the horizontal maps are isomorphisms
(`ProEtale.CondensedRing.isIso_lowerStarBaseChange_of_isIso`), and the base-change morphisms of
horizontally pasted squares paste (`ProEtale.CondensedRing.lowerStarBaseChange_app_paste`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section BaseChange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback of module objects along an isomorphism of schemes is an equivalence, with
inverse the pullback along the inverse. -/
instance isEquivalence_upperStar_of_isIso {S T : Scheme.{u}} (t : S ⟶ T) [IsIso t] :
    (t)^*⟦Λ⟧.IsEquivalence :=
  (CategoryTheory.Equivalence.mk (t)^*⟦Λ⟧ (inv t)^*⟦Λ⟧
    ((upperStarId Λ T).symm ≪≫ upperStarCongr Λ (IsIso.inv_hom_id t).symm ≪≫
      upperStarComp Λ (inv t) t)
    ((upperStarComp Λ t (inv t)).symm ≪≫ upperStarCongr Λ (IsIso.hom_inv_id t) ≪≫
      upperStarId Λ S)).isEquivalence_functor

/-- The comparison `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` of pullbacks of module objects along a commutative
square `g' ≫ f = f' ≫ g`, through the composition isomorphisms `upperStarComp`. -/
noncomputable def upperStarSquareComparison (sq : CommSq g' f' f g) :
    (g)^*⟦Λ⟧ ⋙ (f')^*⟦Λ⟧ ≅ (f)^*⟦Λ⟧ ⋙ (g')^*⟦Λ⟧ :=
  (upperStarComp Λ f' g).symm ≪≫ eqToIso (by rw [sq.w]) ≪≫ upperStarComp Λ g' f

/-- The base-change morphism `g^* f_* ⟶ f'_* g'^*` on module objects of a commutative square
`g' ≫ f = f' ≫ g`: the exchange morphism of `upperStarSquareComparison` under the adjunctions
`f^* ⊣ f_*` and `f'^* ⊣ f'_*`. -/
noncomputable def lowerStarBaseChange (sq : CommSq g' f' f g) :
    (f)_*⟦Λ⟧ ⋙ (g)^*⟦Λ⟧ ⟶ (g')^*⟦Λ⟧ ⋙ (f')_*⟦Λ⟧ :=
  Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarSquareComparison Λ sq)

/-- The base-change morphism of a square whose horizontal maps are isomorphisms is an
isomorphism. -/
instance isIso_lowerStarBaseChange_of_isIso (sq : CommSq g' f' f g) [IsIso g] [IsIso g'] :
    IsIso (lowerStarBaseChange Λ sq) :=
  Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _

/-- `lowerStarBaseChange` as an exchange morphism. -/
lemma lowerStarBaseChange_eq (sq : CommSq g' f' f g) :
    lowerStarBaseChange Λ sq = Adjunction.exchangeRight (upperStarLowerStarAdjunction Λ f)
      (upperStarLowerStarAdjunction Λ f') (upperStarSquareComparison Λ sq) :=
  rfl

/-- The comparison `upperStarSquareComparison`, with the transport along the equation of the
square written as `upperStarCongr`. -/
lemma upperStarSquareComparison_eq (sq : CommSq g' f' f g) :
    upperStarSquareComparison Λ sq =
      (upperStarComp Λ f' g).symm ≪≫ upperStarCongr Λ sq.w.symm ≪≫ upperStarComp Λ g' f :=
  rfl

/-- The component of `upperStarSquareComparison` at a module object. -/
lemma upperStarSquareComparison_hom_app (sq : CommSq g' f' f g)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (upperStarSquareComparison Λ sq).hom.app N = (upperStarComp Λ f' g).inv.app N ≫
      (upperStarCongr Λ sq.w.symm).hom.app N ≫ (upperStarComp Λ g' f).hom.app N := by
  rw [upperStarSquareComparison_eq, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_hom]

/-- The component of the transport of the pullback along an equality as an `eqToHom`. -/
lemma upperStarCongr_hom_app_eq_eqToHom {S T : Scheme.{u}} {a b : S ⟶ T} (e : a = b)
    (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :
    (upperStarCongr Λ e).hom.app N = eqToHom (by rw [e]) := by
  subst e
  rfl

/-- The composition isomorphism `(a ≫ t)^* ≅ t^* ⋙ a^*` is compatible with the transport along
an equality `a = b`. -/
@[reassoc]
lemma upperStarComp_hom_app_upperStarCongr_hom_app {S T U : Scheme.{u}} {a b : S ⟶ T}
    (e : a = b) (t : T ⟶ U)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ a t).hom.app N ≫ (upperStarCongr Λ e).hom.app ((t)^*⟦Λ⟧.obj N) =
      (upperStarCongr Λ (congrArg (· ≫ t) e)).hom.app N ≫ (upperStarComp Λ b t).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The composition isomorphism `(t ≫ a)^* ≅ a^* ⋙ t^*` is compatible with the transport along
an equality `a = b`. -/
@[reassoc]
lemma upperStarComp_hom_app_map_upperStarCongr_hom_app {S T U : Scheme.{u}} (t : S ⟶ T)
    {a b : T ⟶ U} (e : a = b)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (upperStarComp Λ t a).hom.app N ≫ (t)^*⟦Λ⟧.map ((upperStarCongr Λ e).hom.app N) =
      (upperStarCongr Λ (congrArg (t ≫ ·) e)).hom.app N ≫ (upperStarComp Λ t b).hom.app N := by
  subst e
  simp [upperStarCongr_self]

/-- The associativity law for the composition isomorphisms of the pullbacks of module objects,
solved for the composite `(a ≫ b ≫ c)^* ⟶ a^* b^* c^*` through `(a ≫ b) ≫ c`. -/
@[reassoc]
lemma upperStarComp_hom_app_comp_map_upperStarComp_hom_app {S T U V : Scheme.{u}} (a : S ⟶ T)
    (b : T ⟶ U) (c : U ⟶ V)
    (M : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V)) :
    (upperStarComp Λ a (b ≫ c)).hom.app M ≫ (a)^*⟦Λ⟧.map ((upperStarComp Λ b c).hom.app M) =
      (upperStarCongr Λ (Category.assoc a b c).symm).hom.app M ≫
        (upperStarComp Λ (a ≫ b) c).hom.app M ≫
          (upperStarComp Λ a b).hom.app ((c)^*⟦Λ⟧.obj M) := by
  rw [upperStarComp_hom_app_comp_upperStarComp_hom_app, upperStarCongr_hom_app_trans_assoc,
    upperStarCongr_self, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

variable {X'' Y'' : Scheme.{u}} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

/-- **Pasting law of the pullback comparisons**: the comparison of the outer square of two
horizontally pasted squares is the pasting of their comparisons, through the composition
isomorphisms `upperStarComp`. The squares are
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
-/
lemma upperStarSquareComparison_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f'')^*⟦Λ⟧.map ((upperStarComp Λ h g).hom.app N) ≫
        (upperStarSquareComparison Λ sq₂).hom.app ((g)^*⟦Λ⟧.obj N) ≫
          (h')^*⟦Λ⟧.map ((upperStarSquareComparison Λ sq₁).hom.app N) =
      (upperStarSquareComparison Λ sq).hom.app N ≫
        (upperStarComp Λ h' g').hom.app ((f)^*⟦Λ⟧.obj N) := by
  rw [← cancel_epi ((upperStarComp Λ f'' (h ≫ g)).hom.app N),
    upperStarSquareComparison_hom_app, upperStarSquareComparison_hom_app,
    upperStarSquareComparison_hom_app]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [upperStarComp_hom_app_comp_map_upperStarComp_hom_app_assoc Λ f'' h g,
    Iso.hom_inv_id_app_assoc,
    upperStarComp_hom_app_upperStarCongr_hom_app_assoc Λ sq₂.w.symm g,
    upperStarComp_hom_app_comp_upperStarComp_hom_app_assoc Λ h' f' g,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    upperStarComp_hom_app_map_upperStarCongr_hom_app_assoc Λ h' sq₁.w.symm,
    upperStarComp_hom_app_comp_map_upperStarComp_hom_app Λ h' g' f]
  simp only [upperStarCongr_hom_app_eq_eqToHom, eqToHom_trans_assoc]

/-- **Pasting law of the base-change morphisms**: the base-change morphism of the outer square of
two horizontally pasted squares is the pasting of their base-change morphisms, through the
composition isomorphisms `upperStarComp`. The squares are
```
X'' --h'--> X' --g'--> X
 |f''       |f'        |f
 v          v          v
Y'' --h---> Y' --g---> Y
```
-/
lemma lowerStarBaseChange_app_paste (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (upperStarComp Λ h g).hom.app ((f)_*⟦Λ⟧.obj M) ≫
        (h)^*⟦Λ⟧.map ((lowerStarBaseChange Λ sq₁).app M) ≫
          (lowerStarBaseChange Λ sq₂).app ((g')^*⟦Λ⟧.obj M) =
      (lowerStarBaseChange Λ sq).app M ≫ (f'')_*⟦Λ⟧.map ((upperStarComp Λ h' g').hom.app M) := by
  rw [lowerStarBaseChange_eq, lowerStarBaseChange_eq, lowerStarBaseChange_eq]
  have hp := Adjunction.exchangeRight_app_paste (G := (h ≫ g)^*⟦Λ⟧) (G' := (h' ≫ g')^*⟦Λ⟧)
    (G₁ := (g)^*⟦Λ⟧) (G₁' := (g')^*⟦Λ⟧) (G₂ := (h)^*⟦Λ⟧) (G₂' := (h')^*⟦Λ⟧)
    (upperStarLowerStarAdjunction Λ f) (upperStarLowerStarAdjunction Λ f')
    (upperStarLowerStarAdjunction Λ f'') (upperStarSquareComparison Λ sq₁)
    (upperStarSquareComparison Λ sq₂) (upperStarSquareComparison Λ sq) (upperStarComp Λ h g)
    (upperStarComp Λ h' g') (upperStarSquareComparison_paste Λ sq₁ sq₂ sq) M
  exact hp

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
