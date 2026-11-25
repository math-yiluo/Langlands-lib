/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!

# The derived pullback and pushforward of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `Φ_X : X ⟶ X`, `Φ_Y : Y ⟶ Y` endomorphisms
compatible with `f`, that is `Φ_X ≫ f = f ≫ Φ_Y` (`hf`). Write `Φ_X` and `Φ_Y` also for the
Frobenius pullbacks `LΦ_X^*` and `LΦ_Y^*` on the bounded constructible derived categories
`Dᵇc(-)⟦ℚ̲̄_ℓ⟧` of `ℚ̄_ℓ`-sheaves (`WeilConjectures.WeilObject.BoundedConstructible.Defs`). For a
functor `G` between these categories with a commutation isomorphism `b_G`, the Weil structure of
`G K` is the composite

```
φ_{GK} : Φ (G K) --b_G(K)--> G (Φ K) --G(φ_K)--> G K,
```

which is `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso b_G`. This file supplies `b_G` for
the derived pullback and the derived pushforward.

* **Pullback.** The comparison `b^* : Lf^* ⋙ Φ_X ≅ Φ_Y ⋙ Lf^*` (that is `Φ_X Lf^* ≅ Lf^* Φ_Y`) is
  the pullback comparison `boundedConstructiblePullbackSquareComparison` of the Frobenius square
  `Φ_X ≫ f = f ≫ Φ_Y`, built from the composition isomorphisms of the derived pullback. No base
  change theorem is needed, and `Φ_X`, `Φ_Y` need not be isomorphisms
  (`ProEtale.CondensedRing.weilUpperStarComparison`, `ProEtale.CondensedRing.weilUpperStar`).
  For `f = x` a rational point fixed by `Φ_X`, this is the stalk of a Weil object
  (`WeilConjectures.TraceFormula.Stalk`).
* **Pushforward.** For automorphisms `Φ_X = e_X.hom` and `Φ_Y = e_Y.hom`, the comparison
  `b_* : Rf_* ⋙ Φ_Y ⟶ Φ_X ⋙ Rf_*` (that is
  `Φ_Y Rf_* ⟶ Rf_* Φ_X`) is the base-change morphism `boundedConstructibleBaseChange` of the
  Frobenius square (`ProEtale.CondensedRing.weilLowerStarComparison`). It is invertible since the
  horizontal maps of the square are isomorphisms
  (`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`); no properness of `f`
  is needed. This gives the Weil pushforward `ProEtale.CondensedRing.weilLowerStar`.

## Base change along isomorphisms

`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isIso`: the base-change morphism of
a commutative square whose horizontal maps `g` and `g'` are isomorphisms is an isomorphism. The
derived pullbacks along `g` and `g'` are equivalences, with inverses the pullbacks along `g⁻¹`
and `g'⁻¹` (`ProEtale.CondensedRing.boundedConstructibleUpperStarEquivalenceOfIsIso`), and the
exchange morphism of an isomorphism along equivalences is an isomorphism
(`CategoryTheory.Adjunction.isIso_exchangeRight_of_isEquivalence`).

## Main definitions

- `ProEtale.CondensedRing.weilUpperStar`: the derived pullback
  `WeilBoundedConstructible ℓ Φ_Y ⥤ WeilBoundedConstructible ℓ Φ_X` of Weil objects.
- `ProEtale.CondensedRing.weilLowerStar`: the derived pushforward
  `WeilBoundedConstructible ℓ e_X.hom ⥤ WeilBoundedConstructible ℓ e_Y.hom` of Weil objects, for
  automorphisms `e_X` and `e_Y`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section BaseChangeOfIsIso

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The derived pullback `Lg^*` along an isomorphism `g` on bounded constructible complexes is an
equivalence, with inverse `L(g⁻¹)^*`: the composition isomorphisms identify both composites with
the pullbacks along identities, which are the identity functors. -/
noncomputable def boundedConstructibleUpperStarEquivalenceOfIsIso (g : Y' ⟶ Y) [IsIso g] :
    Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ≌ Dᵇc(Y'.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  CategoryTheory.Equivalence.mk (boundedConstructibleUpperStar _ ℓ g)
    (boundedConstructibleUpperStar _ ℓ (inv g))
    ((boundedConstructibleUpperStarId _ ℓ Y).symm ≪≫
      eqToIso (by rw [IsIso.inv_hom_id]) ≪≫ boundedConstructibleUpperStarComp _ ℓ (inv g) g)
    ((boundedConstructibleUpperStarComp _ ℓ g (inv g)).symm ≪≫
      eqToIso (by rw [IsIso.hom_inv_id]) ≪≫ boundedConstructibleUpperStarId _ ℓ Y')

instance isEquivalence_boundedConstructibleUpperStar_of_isIso (g : Y' ⟶ Y) [IsIso g] :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).IsEquivalence :=
  (boundedConstructibleUpperStarEquivalenceOfIsIso ℓ g).isEquivalence_functor

/-- Base change along isomorphisms: for a commutative square `g' ≫ f = f' ≫ g` of schemes whose
horizontal maps `g` and `g'` are isomorphisms, the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on bounded constructible `ℚ̄_ℓ`-sheaves is an isomorphism.
No properness of `f` is needed. See the module docstring for the argument. -/
theorem isIso_boundedConstructibleBaseChange_of_isIso [IsIso g] [IsIso g']
    (sq : CommSq g' f' f g) :
    IsIso (boundedConstructibleBaseChange ℓ sq) := by
  rw [boundedConstructibleBaseChange_eq_exchangeRight]
  exact Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _

end BaseChangeOfIsIso

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-! ### The pullback -/

section UpperStar

variable (ΦX : X ⟶ X) (ΦY : Y ⟶ Y) (f : X ⟶ Y) (hf : ΦX ≫ f = f ≫ ΦY)

/-- The Frobenius comparison `b^* : Lf^* ⋙ LΦ_X^* ≅ LΦ_Y^* ⋙ Lf^*` of the derived pullback, that
is `Φ_X Lf^* ≅ Lf^* Φ_Y`: the pullback comparison of the Frobenius square
`Φ_X ≫ f = f ≫ Φ_Y`. -/
noncomputable def weilUpperStarComparison :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦX ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ ΦY ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
    (CommSq.mk hf)).symm

/-- The Frobenius comparison of the pullback at an object, through the composition isomorphisms
`L(Φ_X ≫ f)^* ≅ LΦ_X^* Lf^*` and `L(f ≫ Φ_Y)^* ≅ Lf^* LΦ_Y^*`. -/
lemma weilUpperStarComparison_hom_app (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (weilUpperStarComparison ℓ ΦX ΦY f hf).hom.app K =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ ΦX f).inv.app K ≫
        eqToHom (by rw [hf]) ≫
        (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ f ΦY).hom.app K := by
  simp only [weilUpperStarComparison, boundedConstructiblePullbackSquareComparison, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, Category.assoc]

/-- The derived pullback `Lf^*` of Weil objects: a Weil object `(K, φ_K)` for `Φ_Y` is sent to
`Lf^* K` with the structure isomorphism
`Φ_X Lf^* K ≅ Lf^* Φ_Y K ≅ Lf^* K` given by `weilUpperStarComparison` and `Lf^* φ_K`. -/
noncomputable def weilUpperStar :
    WeilBoundedConstructible ℓ ΦY ⥤ WeilBoundedConstructible ℓ ΦX :=
  IsoAlgebra.mapOfNatIso (weilUpperStarComparison ℓ ΦX ΦY f hf)

@[simp]
lemma weilUpperStar_obj_carrier (K : WeilBoundedConstructible ℓ ΦY) :
    ((weilUpperStar ℓ ΦX ΦY f hf).obj K).carrier =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K.carrier :=
  rfl

lemma weilUpperStar_obj_str (K : WeilBoundedConstructible ℓ ΦY) :
    ((weilUpperStar ℓ ΦX ΦY f hf).obj K).str =
      (weilUpperStarComparison ℓ ΦX ΦY f hf).app K.carrier ≪≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The derived pullback of Weil objects lifts the derived pullback on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the
forgetful functors. -/
lemma weilUpperStar_comp_forget :
    weilUpperStar ℓ ΦX ΦY f hf ⋙ WeilBoundedConstructible.forget ℓ ΦX =
      WeilBoundedConstructible.forget ℓ ΦY ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f :=
  rfl

end UpperStar

/-! ### The pushforward -/

section LowerStar

variable (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- The Frobenius comparison `b_* : Rf_* ⋙ Le_Y^* ⟶ Le_X^* ⋙ Rf_*` of the derived pushforward,
that is `Φ_Y Rf_* ⟶ Rf_* Φ_X` (`ℚ̄_ℓ`-coefficient): the base-change morphism of the Frobenius square
`e_X ≫ f = f ≫ e_Y`. -/
noncomputable def weilLowerStarComparison :
    boundedConstructibleLowerStar ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY.hom ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom ⋙
        boundedConstructibleLowerStar ℓ f :=
  boundedConstructibleBaseChange ℓ (CommSq.mk hf)

/-- The Frobenius comparison of the derived pushforward is an isomorphism, the Frobenius
automorphisms being isomorphisms. -/
instance isIso_weilLowerStarComparison : IsIso (weilLowerStarComparison ℓ eX eY f hf) :=
  isIso_boundedConstructibleBaseChange_of_isIso ℓ _

/-- The derived pushforward `Rf_*` of Weil objects: a Weil object `(K, φ_K)` for `e_X` is sent to
`Rf_* K` with the structure isomorphism `Φ_Y Rf_* K ≅ Rf_* Φ_X K ≅ Rf_* K` given by the inverted
`weilLowerStarComparison` and `Rf_* φ_K`. -/
noncomputable def weilLowerStar :
    WeilBoundedConstructible ℓ eX.hom ⥤ WeilBoundedConstructible ℓ eY.hom :=
  IsoAlgebra.mapOfNatIso (asIso (weilLowerStarComparison ℓ eX eY f hf))

/-- The underlying complex of the image under `weilLowerStar` (`ℚ̄_ℓ`-coefficient). -/
@[simp]
lemma weilLowerStar_obj_carrier (K : WeilBoundedConstructible ℓ eX.hom) :
    ((weilLowerStar ℓ eX eY f hf).obj K).carrier =
      (boundedConstructibleLowerStar ℓ f).obj K.carrier :=
  rfl

/-- The Weil structure of the image under `weilLowerStar` (`ℚ̄_ℓ`-coefficient). -/
lemma weilLowerStar_obj_str (K : WeilBoundedConstructible ℓ eX.hom) :
    ((weilLowerStar ℓ eX eY f hf).obj K).str =
      (asIso (weilLowerStarComparison ℓ eX eY f hf)).app K.carrier ≪≫
        (boundedConstructibleLowerStar ℓ f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The derived pushforward of Weil objects lifts the derived pushforward on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along
the forgetful functors. -/
lemma weilLowerStar_comp_forget :
    weilLowerStar ℓ eX eY f hf ⋙ WeilBoundedConstructible.forget ℓ eY.hom =
      WeilBoundedConstructible.forget ℓ eX.hom ⋙
        boundedConstructibleLowerStar ℓ f :=
  rfl

end LowerStar

end AlgebraicGeometry.ProEtale.CondensedRing
