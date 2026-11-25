/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.ProjectionFormula

/-!
# Open–closed operations on module sheaves over a sheaf of rings

Let `R` be a commutative ring (e.g. `ULift ℤ`) and `B` a sheaf of `R`-algebras on `X_proét`,
i.e. a monoid object in the monoidal category of pro-étale sheaves of `R`-modules. The
`B`-module sheaves are the module objects `Mod (Sheaf (ProEt.topology X) (ModuleCat R)) B`.
This file defines the operations of blueprint
`proposition-extension-zero-restriction-closed-subscheme` on them; on underlying sheaves of
`R`-modules they are the operations of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient` (all
the `*_comp_forget` lemmas are `rfl`).

* `ProEtale.RingSheaf.upperStar B g : Mod B ⥤ Mod (g^* B)`, the pullback along any `g`, the
  coefficient ring being the inverse image `g^* B` (a monoid object since `g^*` is strong
  monoidal);
* `ProEtale.RingSheaf.lowerStar B g : Mod (g^* B) ⥤ Mod B`, the pushforward `g_*` with
  `B` acting through the unit `B ⟶ g_* g^* B`, right adjoint to `upperStar`
  (`ProEtale.RingSheaf.upperStarLowerStarAdjunction`);
* `ProEtale.RingSheaf.openImmersionLowerShriek B i j hij : Mod (j^* B) ⥤ Mod B`, the
  extension by zero along a quasi-compact open immersion `j` with closed complement `i`, with
  `B` acting through the projection formula `B ⊗ j_! N ≅ j_!(j^* B ⊗ N)`
  (`ProEtale.hasProjectionFormula_openImmersion_of_isCompl`), left adjoint to `upperStar B j`
  (`ProEtale.RingSheaf.openImmersionLowerShriekUpperStarAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Y Z U X : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]

section UpperLowerStar

variable (g : Y ⟶ X)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: the
pullback `g^*` from `B`-module sheaves on `X_proét` to `g^* B`-module sheaves on `Y_proét`: the
transport of module objects along the strong monoidal pullback of sheaves of `R`-modules. -/
noncomputable abbrev upperStar :
    Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B ⥤
      Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ((g)^*[ModuleCat.{u + 1} R].obj B) :=
  (g)^*[ModuleCat.{u + 1} R].mapMod B

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: the
pushforward `g_*` from `g^* B`-module sheaves on `Y_proét` to `B`-module sheaves on `X_proét`:
the transport along the lax monoidal pushforward, followed by restriction of scalars along the
unit `B ⟶ g_* g^* B`. -/
noncomputable abbrev lowerStar :
    Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ((g)^*[ModuleCat.{u + 1} R].obj B) ⥤
      Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B :=
  (g)_*[ModuleCat.{u + 1} R].mapMod _ ⋙
    Mod.comap ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unitAlgHom B)

/-- The underlying sheaf of `g^* M` is the pullback of the underlying sheaf of `M`. -/
lemma upperStar_comp_forget :
    upperStar B g ⋙ Mod.forget _ = Mod.forget B ⋙ (g)^*[ModuleCat.{u + 1} R] := rfl

/-- The underlying sheaf of `g_* N` is the pushforward of the underlying sheaf of `N`. -/
lemma lowerStar_comp_forget :
    lowerStar B g ⋙ Mod.forget B = Mod.forget _ ⋙ (g)_*[ModuleCat.{u + 1} R] := rfl

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: the adjunction `g^* ⊣ g_*`
on module sheaves, lifted from the monoidal adjunction on sheaves of `R`-modules. -/
noncomputable def upperStarLowerStarAdjunction : upperStar B g ⊣ lowerStar B g :=
  (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).mapModAdjunction B

@[simp]
lemma upperStarLowerStarAdjunction_unit_app_hom
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    ((RingSheaf.upperStarLowerStarAdjunction B g).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).unit.app M.X :=
  Adjunction.mapModAdjunction_unit_app_hom _ _ M

@[simp]
lemma upperStarLowerStarAdjunction_counit_app_hom
    (N : Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
      ((g)^*[ModuleCat.{u + 1} R].obj B)) :
    ((RingSheaf.upperStarLowerStarAdjunction B g).counit.app N).hom =
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) g).counit.app N.X :=
  Adjunction.mapModAdjunction_counit_app_hom _ _ N

end UpperLowerStar

section OpenImmersion

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

include i hij

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: the
extension by zero `j_!` from `j^* B`-module sheaves on `U_proét` to `B`-module sheaves on
`X_proét`, for a quasi-compact open immersion `j` with closed complement `i`. The underlying
sheaf of `j_! N` is the extension by zero of the underlying sheaf of `N`, with `B` acting
through the projection formula `B ⊗ j_! N ≅ j_!(j^* B ⊗ N) ⟶ j_! N`. -/
noncomputable def openImmersionLowerShriek :
    Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) ((j)^*[ModuleCat.{u + 1} R].obj B) ⥤
      Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B :=
  have := hasProjectionFormula_openImmersion_of_isCompl (R := R) i j hij
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).mapModLeft B

/-- The underlying sheaf of `j_! N` is the extension by zero of the underlying sheaf. -/
lemma openImmersionLowerShriek_comp_forget :
    openImmersionLowerShriek B i j hij ⋙ Mod.forget B =
      Mod.forget _ ⋙ (j)_!open[ModuleCat.{u + 1} R] := rfl

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (1): the adjunction
`j_! ⊣ j^*` on module sheaves. -/
noncomputable def openImmersionLowerShriekUpperStarAdjunction :
    openImmersionLowerShriek B i j hij ⊣ upperStar B j :=
  have := hasProjectionFormula_openImmersion_of_isCompl (R := R) i j hij
  (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j
    ).mapModLeftAdjunction

@[simp]
lemma openImmersionLowerShriekUpperStarAdjunction_unit_app_hom
    (N : Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))
      ((j)^*[ModuleCat.{u + 1} R].obj B)) :
    ((RingSheaf.openImmersionLowerShriekUpperStarAdjunction B i j hij).unit.app N).hom =
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).unit.app
        N.X :=
  have := hasProjectionFormula_openImmersion_of_isCompl (R := R) i j hij
  Adjunction.mapModLeftAdjunction_unit_app_hom _ N

@[simp]
lemma openImmersionLowerShriekUpperStarAdjunction_counit_app_hom
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    ((RingSheaf.openImmersionLowerShriekUpperStarAdjunction B i j hij).counit.app M).hom =
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) j).counit.app
        M.X :=
  have := hasProjectionFormula_openImmersion_of_isCompl (R := R) i j hij
  Adjunction.mapModLeftAdjunction_counit_app_hom _ M

end OpenImmersion

end AlgebraicGeometry.ProEtale.RingSheaf
