/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# Trivializations of pullbacks of module objects

Let `Λ` be a commutative condensed ring and `f : X ⟶ X` an endomorphism of a scheme. The pullback
of `Λ`-modules is `f^* = mapMod(f^*) ⋙ Ext_{α_f}`, extension of scalars along the coefficient
morphism `α_f : f^* Λ_X ⟶ Λ_X` (`ProEtale.CondensedRing.upperStar`). A monoidal trivialization
`κ : f^* ≅ 𝟭` of the pullback of abelian sheaves which agrees with `α_f` at `Λ_X` gives a
trivialization of the pullback of `Λ`-modules:
```
f^* = mapMod(f^*) ⋙ Ext_{α_f} ≅ Res_{α_f} ⋙ Ext_{α_f} ≅ Res_{α_f} ⋙ Res_{α_f⁻¹} ≅ 𝟭,
```
the first isomorphism being `κ` on the underlying sheaves (`Functor.mapModIsoComapOfIsoId`).

## Main definitions

- `ProEtale.CondensedRing.upperStarIsoIdOfIsoId`: the trivialization `f^* ≅ 𝟭` on `Λ`-modules.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X : Scheme.{u}} (f : X ⟶ X)

/-- The trivialization `f^* ≅ 𝟭` of the pullback of `Λ`-modules along an endomorphism `f`
induced by a monoidal trivialization `κ : f^* ≅ 𝟭` of the pullback of abelian sheaves whose
component at the coefficient ring `Λ_X` is the coefficient morphism `α_f`. -/
noncomputable def upperStarIsoIdOfIsoId (κ : (f)^*[Ab.{u + 1}] ≅ 𝟭 _)
    [NatTrans.IsMonoidal κ.hom]
    (hκ : κ.hom.app (condensedRingObj Λ X) = condensedPullbackHom Λ f) :
    (f)^*⟦Λ⟧ ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (Functor.mapModIsoComapOfIsoId κ _ _ hκ)
      (Mod.extendScalars (condensedPullbackHom Λ f)) ≪≫
    Functor.isoWhiskerLeft (Mod.comap (condensedPullbackHom Λ f))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) ≪≫
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).unitIso.symm

end AlgebraicGeometry.ProEtale.CondensedRing
