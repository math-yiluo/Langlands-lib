/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# The pullback of module objects is strong monoidal

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The pullback
`f^* : Mod_{Λ_Y} ⥤ Mod_{Λ_X}` of module objects over the coefficient rings is
`mapMod(f^*) ⋙ Ext_{α_f}`, the transport of module objects along the pullback of sheaves followed
by the extension of scalars along the coefficient isomorphism `α_f : f^* Λ_Y ≅ Λ_X`
(`ProEtale.CondensedRing.upperStar`). Both are strong monoidal for the relative tensor products
(`WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`):

* the pullback of sheaves `f^*` is braided strong monoidal
  (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal`) and preserves
  coequalizers, being a left adjoint, so `mapMod(f^*)` is strong monoidal
  (`Functor.monoidal_mapMod`);
* `α_f` is an isomorphism of commutative ring objects, so `Ext_{α_f}` is strong monoidal
  (`Mod.monoidal_extendScalars`).

Hence `f^*` on module objects is strong monoidal
(`ProEtale.CondensedRing.monoidal_upperStar`): there are isomorphisms
```
f^* (M ⊗_{Λ_Y} N) ≅ f^* M ⊗_{Λ_X} f^* N,      f^* Λ_Y ≅ Λ_X,
```
coherent with the associativity and unit constraints. This is the underived input of the
monoidality of the derived pullback.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of sheaves `f^*` preserves coequalizers, being a left adjoint. -/
noncomputable instance preservesColimitsOfShape_walkingParallelPair_sheafUpperStar :
    PreservesColimitsOfShape WalkingParallelPair (f)^*[Ab.{u + 1}] :=
  have : PreservesColimitsOfSize.{0, 0} (f)^*[Ab.{u + 1}] :=
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).leftAdjoint_preservesColimits
  inferInstance

/-- The pullback of sheaves `f^*` is braided strong monoidal: its strong monoidal structure
together with its lax braidedness. -/
noncomputable instance braided_sheafUpperStar : (f)^*[Ab.{u + 1}].Braided where

/-- The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over `Λ` is strong monoidal
for the relative tensor products, as the composite of two strong monoidal functors. -/
noncomputable instance monoidal_upperStar : (f)^*⟦Λ⟧.Monoidal :=
  inferInstanceAs ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)).Monoidal

end AlgebraicGeometry.ProEtale.CondensedRing
