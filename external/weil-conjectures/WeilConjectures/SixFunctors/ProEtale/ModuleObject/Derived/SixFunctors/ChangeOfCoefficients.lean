/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! Declarations of ours that lived in the upstream file
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
(moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20:
upstream files are verbatim in live). -/

/-!

# Compatibility of the six functors with a change of condensed coefficient rings

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings, i.e. of commutative ring objects
of abelian sheaves on `*_proét`. For a scheme `X`, its pullback along `p_X` is a morphism of ring
objects `a_X : Λ_X ⟶ Λ'_X` (`ProEtale.coefficientMap`), inducing the *derived extension of
scalars*
```
T^X = Λ'_X ⊗ᴸ_{Λ_X} - = L(Ext_{a_X}) : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ'_X}).
```
This file constructs the *canonical comparison transformations* between these and the derived
functors `Lf^*`, `Rf_*`, `Rf_!` on module objects of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`, for a morphism of schemes `f : X ⟶ Y`.
Following Corollary `cor:coeff-functor` of `WeilConjectures/RefactorInstruction.tex`, the
coefficient changes `a_X` are compatible with the canonical coefficient morphisms: the squares
```
  f^* Λ_Y --f^* a_Y--> f^* Λ'_Y              Λ_Y ----a_Y----> Λ'_Y
     |                     |                   |                |
    α_f                   α_f                 η_f              η_f
     ↓                     ↓                   ↓                ↓
    Λ_X -------a_X------> Λ'_X              f_* Λ_X --f_* a_X--> f_* Λ'_X
```
commute (`ProEtale.map_coefficientMap_comp_condensedPullbackHom`,
`ProEtale.condensedPushforwardHom_comp_map_coefficientMap`): the first is the naturality in `Λ`
of the comparison `f^* ∘ p_Y^* ≅ p_X^*`, and the second follows by adjunction. From these
squares, by the mate and conjugate constructions of
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`:

* **restriction of scalars commutes with the pushforward**, strictly
  (`ProEtale.CondensedRing.comapLowerStarIso`): both composites are `mapMod(f_*)` followed by
  the restriction of scalars along the common composite of the square; and in the derived
  categories (`ProEtale.CondensedRing.derivedComapLowerStarIso`), when `Λ'_X` is flat over
  `Λ_X`, so that the restriction of scalars preserves K-injective complexes;
* **(Pull)** `Lf^*_Λ ⋙ T^X ≅ T^Y ⋙ Lf^*_Λ'` (`ProEtale.CondensedRing.derivedPullIso`, and the
  underived `ProEtale.CondensedRing.pullIso`): the *conjugates* of the previous isomorphisms
  along `Lf^* ⊣ Rf_*` and `L(Ext) ⊣ D(Res)`, hence isomorphisms on all unbounded objects;
* **(Push)** `Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` (`ProEtale.CondensedRing.derivedPushHom`, and the
  underived `ProEtale.CondensedRing.pushHom`): the *mates* of the previous isomorphisms. They
  are not isomorphisms in general;
* **restriction of scalars commutes with the pullback**
  (`ProEtale.CondensedRing.comapUpperStarIso`), since every `α_f` is an isomorphism, and with
  the extension by zero along an open immersion `j`
  (`ProEtale.CondensedRing.comapOpenImmersionLowerShriekIso`). Hence the comparison
  `j_!^Λ ⋙ T^X ≅ T^U ⋙ j_!^Λ'` is an *isomorphism*, being the conjugate of the former along
  `j_! ⊣ j^*` (`ProEtale.CondensedRing.openImmersionShriekIso`, and its derived version
  `ProEtale.CondensedRing.derivedOpenImmersionShriekIso`);
* **(Shriek)** `Rf_!^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_!^Λ'`
  (`ProEtale.CondensedRing.derivedLowerShriekHom`), for `Rf_! = Di_! ⋙ Rg_*` attached to the
  chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the derived (Push) for the proper `g`
  followed by the derived (Shriek) isomorphism for the open immersion `i`. It is an
  isomorphism whenever (Push) is one for `g`
  (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom`).

The compatibilities with the derived tensor product, the derived hom and `Rf^!` are not
treated: they require the strong monoidality of the extension of scalars, respectively
perfectness or duality hypotheses, which are not formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The coefficient changes `a_X` and the coefficient morphisms -/

section CoefficientMap

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [MonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end CoefficientMap

namespace CondensedRing

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-! ### Pushforward and pullback -/

section UpperLowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

end UpperLowerStar

/-! ### Derived pushforward and pullback, for a flat coefficient change -/

section Derived

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The source composite of the derived coefficient pushforward comparison. Keeping the
composite as a named functor avoids repeated expansion of derived-functor data in signatures. -/
noncomputable def derivedPushSource :=
  R((f)_*⟦Λ⟧) ⋙ L(Mod.extendScalars (coefficientMap a Y))

/-- The target composite of the derived coefficient pushforward comparison. -/
noncomputable def derivedPushTarget :=
  L(Mod.extendScalars (coefficientMap a X)) ⋙ R((f)_*⟦Λ'⟧)

end Derived

/-! ### Extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

end OpenImmersion

/-! ### Derived lower shriek -/

section LowerShriek

variable [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

end LowerShriek

end CondensedRing

end AlgebraicGeometry.ProEtale
