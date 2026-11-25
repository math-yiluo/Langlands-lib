/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange

/-!

# The compact-support base-change morphism on bounded constructible module objects

Let `Λ` be a commutative condensed ring. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`. This file constructs the compact-support base-change
morphisms on the bounded constructible derived categories `Dᵇc(-)⟦Λ⟧` of module objects over
`Λ_X = p_X^* Λ` (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`).
The extension-by-zero exchange is stated for a general `Λ`; the morphisms involving the
pushforward are defined for each of the `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` (in
the namespaces `ProEtale.CondensedRing`, `ProEtale.CondensedRing.ContinuousMapRingObj` and
`ProEtale.CondensedRing.PadicIntegersRingObj`).

* **For a compactification.** For a compactification `c : X ⟶[i] Z ⟶[p] Y` of `f` and its base
  change `c.ofIsPullback sq`, a compactification of `f'`, the morphism
  `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` (in diagrammatic `⋙`-order), where
  `Rf_!^c := i_! ⋙ Rp_*`
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactification`),
  exactly as the étale `Etale.lowerShriekBaseChange`. It is the pasting of two exchange
  morphisms:
  - the *direct-image exchange* `Ex_* : Rp_* ⋙ Lg^* ⟶ Lḡ^* ⋙ Rp'_*` for the proper square of the
    base-changed compactification, which is the base-change morphism
    `ProEtale.CondensedRing.boundedConstructibleBaseChange`;
  - the *extension-by-zero exchange* for the open-immersion square of the base-changed
    compactification. Its canonical mate goes in the direction `Lg'^* ⋙ i'_! ⟶ i_! ⋙ Lḡ^*`,
    base change for extension by zero asserts that it is an isomorphism
    (`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`),
    and the pasting uses its inverse.
* **For the lower shriek.** For the coefficient rings `E̲` of a finite subextension `E ⊆ ℚ̄_ℓ` and
  `ℚ̲̄_ℓ`, the morphism `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for the lower shriek
  `ProEtale.CondensedRing.boundedConstructibleLowerShriek` of the chosen compactifications: the
  pasting for the chosen compactification of `f`, followed by the identification of the lower
  shriek attached to its base change with the lower shriek of `f'`, by the independence of the
  lower shriek from the compactification
  (`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso`).

All schemes are separated and of finite type over a field `k` of characteristic `p > 0` with
`p ≠ ℓ`, and all morphisms are morphisms of `Over (Spec (.of k))`; the compactification `Z` of
`f.left` and `Z ×_Y Y'` are then so as well, as objects of `Over (Spec (.of k))`
(`Compactification.overObj` of `WeilConjectures.Compactification.Over`).

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange`: the
  canonical exchange morphism `Lg'^* ⋙ j'_! ⟶ j_! ⋙ Lg^*` for a commutative square of open
  immersions, and its three steps; for a cartesian square, its inverse
  `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChangeIso`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`:
  the morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}` for a compactification `c`.
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange` and
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl`: the morphism
  `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` for `E`- and `ℚ̄_ℓ`-sheaves.

## Main results

- `ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange`: base
  change for extension by zero. The morphism is the exchange morphism
  `boundedConstructibleOpenImmersionLowerShriekBaseChange'` of
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`, which is
  an isomorphism by `isIso_boundedConstructibleOpenImmersionLowerShriekBaseChange'` (blueprint
  `sk-def-sfb-open-base-change`).

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### For a compactification -/

section Compactification

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-! ### The compact-support base-change morphism for a compactification -/

section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`ℚ̄_ℓ`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ c ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ c.overG) _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ) ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStarOfIsProper ℓ (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ c sq =
      (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ c.overG) _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicAlgClRingObj ℓ) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.padicAlgClRingObj ℓ)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStarOfIsProper ℓ (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

/-! #### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)


section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`E`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ E (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ E c.overG) _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.continuousMapRingObj E) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso (Profinite.continuousMapRingObj E)
        ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStarOfIsProper ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`E`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E c sq =
      (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ E c.overG) _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.continuousMapRingObj E) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.continuousMapRingObj E)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStarOfIsProper ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom :=
  by delta boundedConstructibleLowerShriekOfCompactificationBaseChangePasting; rfl

end LowerShriek

end ContinuousMapRingObj

/-! #### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]


section LowerShriek

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The compact-support base-change morphism `Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c.ofIsPullback sq}`
on bounded constructible complexes, for a cartesian square `sq` and a compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f`, *into the base-changed compactification* of `f'` (`𝒪_E`-coefficient):
with `Rf_!^c = i_! ⋙ Rp_*`, it is the pasting of the direct-image exchange
`boundedConstructibleBaseChange` of the proper square of the base-changed compactification with
the inverse of the extension-by-zero exchange of its open-immersion square,

`i_! ⋙ Rp_* ⋙ Lg^* ⟶ i_! ⋙ Lḡ^* ⋙ Rp'_* ⟶ Lg'^* ⋙ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactification ℓ E c ⋙
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g' ⋙
        boundedConstructibleLowerShriekOfCompactification ℓ E (c.ofIsPullback sq.overLeft) :=
  (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ E c.overG) _).hom ≫
    Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
      (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI)
      (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
        (Profinite.padicIntegersRingObj ℓ E) ℓ
        (c.overBaseChange_isPullback_i sq)).hom
      (boundedConstructibleLowerStarOfIsProper ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
    (Functor.associator _ _ _).hom

/-- The defining equation of `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
(`𝒪_E`-coefficient). -/
lemma boundedConstructibleLowerShriekOfCompactificationBaseChangePasting_eq
    (c : Compactification f.left) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E c sq =
      (Functor.associator _ (boundedConstructibleLowerStarOfIsProper ℓ E c.overG) _).hom ≫
        Functor.whiskerLeft (boundedConstructibleOpenImmersionLowerShriek
          (Profinite.padicIntegersRingObj ℓ E) ℓ c.overI)
          (boundedConstructibleBaseChange ℓ E (c.overBaseChange_isPullback_g sq).toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso
            (Profinite.padicIntegersRingObj ℓ E)
            ℓ
            (c.overBaseChange_isPullback_i sq)).hom
          (boundedConstructibleLowerStarOfIsProper ℓ E (c.ofIsPullback sq.overLeft).overG) ≫
        (Functor.associator _ _ _).hom := by
  rw [boundedConstructibleLowerShriekOfCompactificationBaseChangePasting]

end LowerShriek

end PadicIntegersRingObj

end Compactification

/-! ### For the lower shriek -/

section Chosen

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}


/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `E`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism `boundedConstructibleLowerShriekOfCompactificationBaseChangePasting`
into `Rf'_!^{c_f.ofIsPullback sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekBaseChange (sq : IsPullback g' f' f g) :
    ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f ⋙
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ g' ⋙
        ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f' :=
  ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

/-- The defining equation of `boundedConstructibleLowerShriekBaseChange` (`E`-coefficient). -/
lemma boundedConstructibleLowerShriekBaseChange_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange ℓ E sq =
      ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ E
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso ℓ E
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange]

/-- The *compact-support base-change morphism* `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!` on bounded
constructible `ℚ̄_ℓ`-sheaves for a cartesian square `sq`, where `Rf_!` and `Rf'_!` are the lower
shrieks `boundedConstructibleLowerShriek` for the chosen compactifications `c_f` and `c_{f'}`:
the morphism
`boundedConstructibleLowerShriekOfCompactificationBaseChangePasting` into `Rf'_!^{c_f.ofIsPullback
sq}`, followed by its identification
`boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl` with `Rf'_! = Rf'_!^{c_{f'}}`. -/
noncomputable irreducible_def boundedConstructibleLowerShriekBaseChange_padicAlgCl
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriek ℓ f ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g' ⋙
        boundedConstructibleLowerShriek ℓ f' :=
  boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
      (compactificationOverField f) sq ≫
    Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
      ((compactificationOverField f).ofIsPullback sq.overLeft) (compactificationOverField f')).hom

/-- The defining equation of `boundedConstructibleLowerShriekBaseChange_padicAlgCl`
(`ℚ̄_ℓ`-coefficient). -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      boundedConstructibleLowerShriekOfCompactificationBaseChangePasting ℓ
          (compactificationOverField f) sq ≫
        Functor.whiskerLeft _ (boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ
          ((compactificationOverField f).ofIsPullback sq.overLeft)
          (compactificationOverField f')).hom := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_def]

end Chosen

end AlgebraicGeometry.ProEtale.CondensedRing
