/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# The base-change morphism under a flat change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that every coefficient change
`a_X : Λ_X ⟶ Λ'_X` is flat, and write `T^X = L(Ext_{a_X})` for the derived extension of scalars.
For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

we show that, if the comparison isomorphisms `derivedPullIso a : Lh^*_Λ ⋙ T ≅ T ⋙ Lh^*_Λ'` are
compatible with the composition of derived pullbacks (the hypothesis
`ProEtale.CondensedRing.DerivedPullIsoCompCoherence`) and the comparisons
`derivedPushHom a : Rh_*^Λ ⋙ T ⟶ T ⋙ Rh_*^Λ'` are invertible at `K` for `h = f` and at `Lg'^* K`
for `h = f'`, then `T^{Y'}` of the base-change morphism `BC_sq^Λ` at `K` and the base-change
morphism `BC_sq^Λ'` at `T^X K` are isomorphic arrows: on the ambient derived categories
(`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars`), and on the
bounded constructible derived categories
(`ProEtale.CondensedRing.nonempty_arrowIso_boundedConstructibleBaseChange_extendScalars`).

This is the formal part of blueprint `lemma-naturality-pasting-comparison`: by the cube law of
mates (`CategoryTheory.mateEquiv_app_cube`), the compatibility of `derivedPullIso` with the
pullback square comparisons transposes to the compatibility of the base-change morphisms with
`derivedPullIso` and `derivedPushHom`, the latter being the mate of the former
(`CategoryTheory.Adjunction.pushHomOfComapIso_eq_mateEquiv`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

section Ambient

/-- The comparison isomorphisms `derivedPullIso a : Lh^*_Λ ⋙ T ≅ T ⋙ Lh^*_Λ'` are compatible with
the composition isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*`: for composable `p`, `q` and every `M`,
```
T L(p ≫ q)^* M ⟶ L(p ≫ q)^* T M ⟶ Lp^* Lq^* T M
  = T L(p ≫ q)^* M ⟶ T Lp^* Lq^* M ⟶ Lp^* T Lq^* M ⟶ Lp^* Lq^* T M.
```
-/
def DerivedPullIsoCompCoherence : Prop :=
  ∀ ⦃X Y Z : Scheme.{u}⦄ (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))),
    (derivedPullIso a (p ≫ q)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' p q).hom.app
          ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj M) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp Λ p q).hom.app M) ≫
        (derivedPullIso a p).hom.app ((q)^*⟦Λ⟧.leftDerivedFunctor.obj M) ≫
        (p)^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedPullIso a q).hom.app M)

/-- The comparison isomorphisms `derivedPullIso a` commute with the `eqToHom`s induced by an
equality `u = v` of morphisms of schemes. -/
lemma derivedPullIso_hom_app_eqToHom {X Y : Scheme.{u}} {u v : X ⟶ Y} (e : u = v)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (derivedPullIso a u).hom.app M ≫
        eqToHom (by rw [e] : (u)^*⟦Λ'⟧.leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M) =
          (v)^*⟦Λ'⟧.leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          (eqToHom (by rw [e] : (u)^*⟦Λ⟧.leftDerivedFunctor.obj M =
            (v)^*⟦Λ⟧.leftDerivedFunctor.obj M)) ≫
        (derivedPullIso a v).hom.app M := by
  subst e
  simp

omit [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] in
private lemma inv_inv_comp_eq_comp_inv_inv {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i₁ : O₂ ≅ O₁) (i₂ : O₃ ≅ O₂) (x : O₃ ⟶ O₄) (y : O₁ ⟶ O₅) (j₁ : O₆ ≅ O₅) (j₂ : O₄ ≅ O₆)
    (h : x ≫ j₂.hom ≫ j₁.hom = i₂.hom ≫ i₁.hom ≫ y) :
    i₁.inv ≫ i₂.inv ≫ x = y ≫ j₁.inv ≫ j₂.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, ← reassoc_of% h]
  simp

omit [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))] in
private lemma cube_aux {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ Q₁ Q₂ Q₃ Q₄ : C}
    (t₁ : O₁ ⟶ O₂) (t₂ : O₂ ⟶ O₃) (t₃ : O₃ ⟶ O₄) (u₁ : O₄ ⟶ O₅) (u₂ : O₅ ⟶ O₆) (v₁ : O₁ ⟶ Q₁)
    (v₂ : Q₁ ⟶ Q₂) (w₁ : Q₂ ⟶ Q₃) (w₂ : Q₃ ⟶ Q₄) (w₃ : Q₄ ⟶ O₆) (P₁ : O₂ ⟶ Q₃) (P₂ : O₃ ⟶ Q₄)
    (s : O₂ ⟶ O₁) (s' : Q₃ ⟶ Q₂) (hs : t₁ ≫ s = 𝟙 O₁) (hs' : s' ≫ w₁ = 𝟙 Q₃)
    (H₁ : P₁ ≫ s' = s ≫ v₁ ≫ v₂) (H₂ : P₂ ≫ w₃ = t₃ ≫ u₁ ≫ u₂) (H₃ : P₁ ≫ w₂ = t₂ ≫ P₂) :
    t₁ ≫ t₂ ≫ t₃ ≫ u₁ ≫ u₂ = v₁ ≫ v₂ ≫ w₁ ≫ w₂ ≫ w₃ := by
  have h : t₁ ≫ P₁ = v₁ ≫ v₂ ≫ w₁ := by
    rw [← Category.comp_id P₁, ← hs', reassoc_of% H₁, reassoc_of% hs]
  rw [← H₂, reassoc_of% H₃.symm, reassoc_of% h]

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- unifying objects of the derived categories given by composites of derived pullbacks is slow
/-- The cube condition of `CategoryTheory.mateEquiv_app_cube` for the derived pullbacks with
coefficients `Λ` and `Λ'` along a commutative square, their pullback square comparisons and the
comparison isomorphisms `derivedPullIso a`, assuming the compatibility of `derivedPullIso a` with
the composition of derived pullbacks. -/
lemma derivedPullIso_cube (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' f' f g)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (f')^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedPullIso a g).inv.app M) ≫
        (derivedPullIso a f').inv.app ((g)^*⟦Λ⟧.leftDerivedFunctor.obj M) ≫
        (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map
          ((pullbackSquareComparison Λ sq).hom.app M) =
      (pullbackSquareComparison Λ' sq).hom.app
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M) ≫
        (g')^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedPullIso a f).inv.app M) ≫
        (derivedPullIso a g').inv.app ((f)^*⟦Λ⟧.leftDerivedFunctor.obj M) := by
  refine inv_inv_comp_eq_comp_inv_inv ((f')^*⟦Λ'⟧.leftDerivedFunctor.mapIso
    ((derivedPullIso a g).app M)) ((derivedPullIso a f').app _) _ _
    ((g')^*⟦Λ'⟧.leftDerivedFunctor.mapIso ((derivedPullIso a f).app M))
    ((derivedPullIso a g').app _) ?_
  have H₁ := H f' g M
  have H₂ := H g' f M
  have H₃ := derivedPullIso_hom_app_eqToHom a sq.w.symm M
  simp only [Iso.app_hom, Functor.mapIso_hom, pullbackSquareComparison_hom_app, Functor.map_comp,
    Category.assoc]
  exact cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [← Functor.map_comp]) (by simp) H₁ H₂ H₃

/-- **The base-change morphism under a flat change of coefficients**, on the ambient derived
categories. Assume that `derivedPullIso a` is compatible with the composition of derived pullbacks,
and that the comparisons `derivedPushHom a f` at `K` and `derivedPushHom a f'` at `Lg'^* K` are
invertible. Then `T^{Y'}` of the base-change morphism `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` with
coefficients `Λ` and the base-change morphism with coefficients `Λ'` at `T^X K` are isomorphic
arrows. -/
theorem nonempty_arrowIso_map_exchangeRight_derivedExtendScalars
    (H : DerivedPullIsoCompCoherence a) (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedPushHom a f).app K))
    (h₂ : IsIso ((derivedPushHom a f').app ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Y')).leftDerivedFunctor.map
        ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
          (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)).app K)) ≅
      Arrow.mk ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ' f)
          (derivedUpperStarLowerStarAdjunction Λ' f') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  Adjunction.nonempty_arrowIso_map_exchangeRight_app _ _ _ _ _ _ (derivedPullIso a f)
    (derivedPullIso a f') (derivedPullIso a g) (derivedPullIso a g') (derivedPullIso_cube a H sq)
    (derivedPushHom a f) (Adjunction.pushHomOfComapIso_eq_mateEquiv _ _ _ _ _)
    (derivedPushHom a f') (Adjunction.pushHomOfComapIso_eq_mateEquiv _ _ _ _ _) K h₁ h₂

end Ambient

end AlgebraicGeometry.ProEtale.CondensedRing
