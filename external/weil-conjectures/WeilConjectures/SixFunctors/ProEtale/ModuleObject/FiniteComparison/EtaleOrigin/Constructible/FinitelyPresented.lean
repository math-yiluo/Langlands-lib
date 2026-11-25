/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Finite presentation along two pullbacks of module objects

Let `Λ` be a commutative condensed ring and `g : S ⟶ X`, `h : W ⟶ S` morphisms of schemes. If
the module object `h^* g^* M` over the ring object `h^* g^* Λ_X` (pulled back as abelian sheaves,
`Functor.mapMod`) is finitely presented, so is the pullback `(h)^*⟦Λ⟧ ((g)^*⟦Λ⟧ M)` over `Λ_W`:
since the coefficient comparisons `α_g`, `α_h` are isomorphisms, the extension of scalars along
them is the restriction of scalars along their inverses, which commutes with `mapMod`.

## Main statements

- `ProEtale.CondensedRing.isFinitelyPresented_upperStar_obj_upperStar_obj`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X S W : Scheme.{u}}

/-- The pullback of module objects `(h)^*⟦Λ⟧ ((g)^*⟦Λ⟧ M)` is the double pullback of abelian
sheaves `h^* g^* M`, with scalars restricted along the inverses of the coefficient comparisons
`α_h` and `h^* α_g`. -/
noncomputable def comapComapMapModMapModIsoUpperStarObjUpperStarObj (g : S ⟶ X) (h : W ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.comap (asIso (condensedPullbackHom Λ h)).inv).obj
        ((Mod.comap ((ProEtale.upperStar Ab.{u + 1} h).map
          (asIso (condensedPullbackHom Λ g)).inv)).obj
          (((ProEtale.upperStar Ab.{u + 1} h).mapMod _).obj
            (((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj M))) ≅
      (h)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M) :=
  (Mod.comap (asIso (condensedPullbackHom Λ h)).inv).mapIso
      ((((ProEtale.upperStar Ab.{u + 1} h).mapModComapIso
        (asIso (condensedPullbackHom Λ g)).inv).app _).symm ≪≫
      ((ProEtale.upperStar Ab.{u + 1} h).mapMod _).mapIso
        ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)).app _).symm) ≪≫
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ h)).app _).symm

/-- If the double pullback of abelian sheaves `h^* g^* M` is finitely presented over
`h^* g^* Λ_X`, then the pullback of module objects `(h)^*⟦Λ⟧ ((g)^*⟦Λ⟧ M)` is finitely presented
over `Λ_W`. -/
theorem isFinitelyPresented_upperStar_obj_upperStar_obj (g : S ⟶ X) (h : W ⟶ S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} h).obj ((ProEtale.upperStar Ab.{u + 1} g).obj
        (condensedRingObj Λ X)))
      (((ProEtale.upperStar Ab.{u + 1} h).mapMod _).obj
        (((ProEtale.upperStar Ab.{u + 1} g).mapMod _).obj M))) :
    Mod.IsFinitelyPresented (condensedRingObj Λ W) ((h)^*⟦Λ⟧.obj ((g)^*⟦Λ⟧.obj M)) :=
  ((hM.comap _).comap _).of_iso (comapComapMapModMapModIsoUpperStarObjUpperStarObj Λ g h M)

end AlgebraicGeometry.ProEtale.CondensedRing
