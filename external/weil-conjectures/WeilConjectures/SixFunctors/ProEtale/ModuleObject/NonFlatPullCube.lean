/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-!

# The base-change morphism under an arbitrary change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, not necessarily flat, and write
`T^X = L(Ext_{a_X})` for the derived extension of scalars. The derived (Pull) isomorphism
`ProEtale.CondensedRing.derivedUpperStarExtendScalarsIso a h : Lh^*_Λ ⋙ T ≅ T ⋙ Lh^*_Λ'` exists
for every `a`. For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

we show that, if the isomorphisms `derivedUpperStarExtendScalarsIso a` are compatible with the
composition of derived pullbacks (the hypothesis
`ProEtale.CondensedRing.DerivedUpperStarExtendScalarsIsoCompCoherence`) and their mates
`Rh_*^Λ ⋙ T ⟶ T ⋙ Rh_*^Λ'` along the derived adjunctions `Lh^* ⊣ Rh_*`
(`ProEtale.CondensedRing.derivedUpperStarExtendScalarsPushHom`) are invertible at `K` for
`h = f` and at `Lg'^* K` for `h = f'`, then `T^{Y'}` of the base-change morphism `BC_sq^Λ` at
`K` and the base-change morphism `BC_sq^Λ'` at `T^X K` are isomorphic arrows
(`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat`).

This is the analogue, without flatness, of
`ProEtale.CondensedRing.nonempty_arrowIso_map_exchangeRight_derivedExtendScalars`; the proof is
the same application of the cube law of mates
(`CategoryTheory.Adjunction.nonempty_arrowIso_map_exchangeRight_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The isomorphisms `derivedUpperStarExtendScalarsIso a : Lh^*_Λ ⋙ T ≅ T ⋙ Lh^*_Λ'` are
compatible with the composition isomorphisms `L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` along `p` and `q`:
for every `M`,
```
T L(p ≫ q)^* M ⟶ L(p ≫ q)^* T M ⟶ Lp^* Lq^* T M
  = T L(p ≫ q)^* M ⟶ T Lp^* Lq^* M ⟶ Lp^* T Lq^* M ⟶ Lp^* Lq^* T M.
```
-/
def DerivedUpperStarExtendScalarsIsoCompCoherenceAt {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) : Prop :=
  ∀ M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
    (derivedUpperStarExtendScalarsIso a (p ≫ q)).hom.app M ≫
        (leftDerivedUpperStarComp Λ' p q).hom.app
          ((Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj M) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          ((leftDerivedUpperStarComp Λ p q).hom.app M) ≫
        (derivedUpperStarExtendScalarsIso a p).hom.app ((q)^*⟦Λ⟧.leftDerivedFunctor.obj M) ≫
        (p)^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedUpperStarExtendScalarsIso a q).hom.app M)

/-- The compatibility `DerivedUpperStarExtendScalarsIsoCompCoherenceAt a p q` for all composable
morphisms `p` and `q` of schemes. -/
def DerivedUpperStarExtendScalarsIsoCompCoherence : Prop :=
  ∀ ⦃X Y Z : Scheme.{u}⦄ (p : X ⟶ Y) (q : Y ⟶ Z),
    DerivedUpperStarExtendScalarsIsoCompCoherenceAt a p q

/-- The comparison `Rh_*^Λ ⋙ T ⟶ T ⋙ Rh_*^Λ'` between the derived pushforwards and the derived
extensions of scalars along an arbitrary coefficient change: the mate of the inverse of
`derivedUpperStarExtendScalarsIso a h` along the derived adjunctions `Lh^* ⊣ Rh_*`. -/
noncomputable def derivedUpperStarExtendScalarsPushHom {X Y : Scheme.{u}} (h : X ⟶ Y) :
    R((h)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y)) ⟶
      L(Mod.extendScalars (coefficientMap a X)) ⋙ R((h)_*⟦Λ'⟧) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction Λ h) (derivedUpperStarLowerStarAdjunction Λ' h)
    (derivedUpperStarExtendScalarsIso a h).inv)

/-- The isomorphisms `derivedUpperStarExtendScalarsIso a` commute with the `eqToHom`s induced by
an equality `u = v` of morphisms of schemes. -/
lemma derivedUpperStarExtendScalarsIso_hom_app_eqToHom {X Y : Scheme.{u}} {u v : X ⟶ Y}
    (e : u = v)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (derivedUpperStarExtendScalarsIso a u).hom.app M ≫
        eqToHom (by rw [e] : (u)^*⟦Λ'⟧.leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M) =
          (v)^*⟦Λ'⟧.leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M)) =
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
          (eqToHom (by rw [e] : (u)^*⟦Λ⟧.leftDerivedFunctor.obj M =
            (v)^*⟦Λ⟧.leftDerivedFunctor.obj M)) ≫
        (derivedUpperStarExtendScalarsIso a v).hom.app M := by
  subst e
  simp

omit [IsMonHom a] in
private lemma inv_inv_comp_eq_comp_inv_inv {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (i₁ : O₂ ≅ O₁) (i₂ : O₃ ≅ O₂) (x : O₃ ⟶ O₄) (y : O₁ ⟶ O₅) (j₁ : O₆ ≅ O₅) (j₂ : O₄ ≅ O₆)
    (h : x ≫ j₂.hom ≫ j₁.hom = i₂.hom ≫ i₁.hom ≫ y) :
    i₁.inv ≫ i₂.inv ≫ x = y ≫ j₁.inv ≫ j₂.inv := by
  rw [Iso.inv_comp_eq, Iso.inv_comp_eq, ← reassoc_of% h]
  simp

omit [IsMonHom a] in
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
isomorphisms `derivedUpperStarExtendScalarsIso a`, assuming the compatibility of the latter with
the composition of derived pullbacks along `f' ≫ g` and `g' ≫ f`. -/
lemma derivedUpperStarExtendScalarsIso_cube (sq : CommSq g' f' f g)
    (H₁ : DerivedUpperStarExtendScalarsIsoCompCoherenceAt a f' g)
    (H₂ : DerivedUpperStarExtendScalarsIsoCompCoherenceAt a g' f)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (f')^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedUpperStarExtendScalarsIso a g).inv.app M) ≫
        (derivedUpperStarExtendScalarsIso a f').inv.app ((g)^*⟦Λ⟧.leftDerivedFunctor.obj M) ≫
        (Mod.extendScalars (coefficientMap a X')).leftDerivedFunctor.map
          ((pullbackSquareComparison Λ sq).hom.app M) =
      (pullbackSquareComparison Λ' sq).hom.app
          ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj M) ≫
        (g')^*⟦Λ'⟧.leftDerivedFunctor.map ((derivedUpperStarExtendScalarsIso a f).inv.app M) ≫
        (derivedUpperStarExtendScalarsIso a g').inv.app ((f)^*⟦Λ⟧.leftDerivedFunctor.obj M) := by
  refine inv_inv_comp_eq_comp_inv_inv ((f')^*⟦Λ'⟧.leftDerivedFunctor.mapIso
    ((derivedUpperStarExtendScalarsIso a g).app M))
    ((derivedUpperStarExtendScalarsIso a f').app _) _ _
    ((g')^*⟦Λ'⟧.leftDerivedFunctor.mapIso ((derivedUpperStarExtendScalarsIso a f).app M))
    ((derivedUpperStarExtendScalarsIso a g').app _) ?_
  have H₁ := H₁ M
  have H₂ := H₂ M
  have H₃ := derivedUpperStarExtendScalarsIso_hom_app_eqToHom a sq.w.symm M
  simp only [Iso.app_hom, Functor.mapIso_hom, pullbackSquareComparison_hom_app, Functor.map_comp,
    Category.assoc]
  exact cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp [← Functor.map_comp]) (by simp) H₁ H₂ H₃

/-- **The base-change morphism under an arbitrary change of coefficients**, on the ambient
derived categories. Assume that `derivedUpperStarExtendScalarsIso a` is compatible with the
composition of derived pullbacks along `f' ≫ g` and `g' ≫ f`, and that the comparisons
`derivedUpperStarExtendScalarsPushHom a f` at `K` and `derivedUpperStarExtendScalarsPushHom a f'`
at `Lg'^* K` are invertible. Then `T^{Y'}` of the base-change morphism `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K`
with coefficients `Λ` and the base-change morphism with coefficients `Λ'` at `T^X K` are
isomorphic arrows. No flatness of `a` is needed. -/
theorem nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat
    (sq : CommSq g' f' f g) (H₁ : DerivedUpperStarExtendScalarsIsoCompCoherenceAt a f' g)
    (H₂ : DerivedUpperStarExtendScalarsIsoCompCoherenceAt a g' f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a f).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a f').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Y')).leftDerivedFunctor.map
        ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
          (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)).app K)) ≅
      Arrow.mk ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ' f)
          (derivedUpperStarLowerStarAdjunction Λ' f') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  Adjunction.nonempty_arrowIso_map_exchangeRight_app _ _ _ _ _ _
    (derivedUpperStarExtendScalarsIso a f) (derivedUpperStarExtendScalarsIso a f')
    (derivedUpperStarExtendScalarsIso a g) (derivedUpperStarExtendScalarsIso a g')
    (derivedUpperStarExtendScalarsIso_cube a sq H₁ H₂)
    (derivedUpperStarExtendScalarsPushHom a f) rfl
    (derivedUpperStarExtendScalarsPushHom a f') rfl K h₁ h₂

/-- `nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat`, assuming the
compatibility of `derivedUpperStarExtendScalarsIso a` with all compositions of derived
pullbacks. -/
theorem nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat'
    (H : DerivedUpperStarExtendScalarsIsoCompCoherence a) (sq : CommSq g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (h₁ : IsIso ((derivedUpperStarExtendScalarsPushHom a f).app K))
    (h₂ : IsIso ((derivedUpperStarExtendScalarsPushHom a f').app
      ((g')^*⟦Λ⟧.leftDerivedFunctor.obj K))) :
    Nonempty (Arrow.mk ((Mod.extendScalars (coefficientMap a Y')).leftDerivedFunctor.map
        ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ f)
          (derivedUpperStarLowerStarAdjunction Λ f') (pullbackSquareComparison Λ sq)).app K)) ≅
      Arrow.mk ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction Λ' f)
          (derivedUpperStarLowerStarAdjunction Λ' f') (pullbackSquareComparison Λ' sq)).app
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K))) :=
  nonempty_arrowIso_map_exchangeRight_derivedExtendScalars_of_nonFlat a sq (H f' g) (H g' f) K
    h₁ h₂

end AlgebraicGeometry.ProEtale.CondensedRing
