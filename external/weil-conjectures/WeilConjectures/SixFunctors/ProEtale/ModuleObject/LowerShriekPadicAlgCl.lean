/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# Extension by zero commutes with `ℚ̄_ℓ ⊗_E -` on bounded below objects

Let `ℓ` be a prime, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ`, and `f : X ⟶ Y` a morphism of
schemes with a compactification `X ⟶[i] Z ⟶[g] Y`. The comparison **(Shriek)**
`ℚ̄_ℓ,Y ⊗ᴸ Rf_! K ⟶ Rf_!(ℚ̄_ℓ,X ⊗ᴸ K)` for the inclusion `E̲ ⟶ ℚ̲̄_ℓ`
(`ProEtale.CondensedRing.derivedLowerShriekHom`) is an isomorphism at every bounded below
`K ∈ D(E_X)` (`ProEtale.CondensedRing.isIso_derivedLowerShriekHom_app_padicAlgCl_of_isGE`). It is
(Push) for the proper `g` at `Di_! K`, which is bounded below since `i_!` is exact
(`ProEtale.CondensedRing.isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE`),
followed by the (Shriek) isomorphism for the open immersion `i`.

This is the (Shriek) part of item 3 of blueprint `sk-prop-sfb-finite-extension-compatibility`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}}
  (f : X ⟶ Y) [HasCompactification f]

/-- **(Shriek) for `E ⟶ ℚ̄_ℓ` on bounded below objects**: for a morphism `f` with a
compactification, the comparison `ℚ̄_ℓ,Y ⊗ᴸ Rf_! K ⟶ Rf_!(ℚ̄_ℓ,X ⊗ᴸ K)` is an isomorphism for
every bounded below `K ∈ D(E_X)`. -/
theorem isIso_derivedLowerShriekHom_app_padicAlgCl_of_isGE
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedLowerShriekHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K) := by
  have := Functor.isGE_mapDerivedCategory_obj (openImmersionLowerShriek
    (Profinite.continuousMapRingObj E) (HasCompactification.compactification f).i) K n
  have h := isIso_derivedPushHom_app_padicSubfieldRingObjToPadicAlgCl_of_isGE ℓ E
    (HasCompactification.compactification f).g
    ((openImmersionLowerShriek (Profinite.continuousMapRingObj E)
      (HasCompactification.compactification f).i).mapDerivedCategory.obj K) n
  simp only [derivedLowerShriekHom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]
  exact IsIso.comp_isIso' (IsIso.id _) (IsIso.comp_isIso' h inferInstance)

end AlgebraicGeometry.ProEtale.CondensedRing
