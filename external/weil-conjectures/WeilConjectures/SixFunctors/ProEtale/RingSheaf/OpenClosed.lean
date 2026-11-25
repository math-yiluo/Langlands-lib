/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.Defs

/-!
# The open–closed sequence for module sheaves over a sheaf of rings

Let `R` be a commutative ring, `B` a sheaf of `R`-algebras on `X_proét`, `j : U ⟶ X` a
quasi-compact open immersion and `i : Z ⟶ X` a closed immersion onto its complement. This file
proves, for the operations on `B`-module sheaves of
`WeilConjectures.SixFunctors.ProEtale.RingSheaf.Defs`, the assertions (1)–(3) of blueprint
`proposition-extension-zero-restriction-closed-subscheme`:

* `j^*`, `j_!`, `i^*` are exact, `i_*` is exact
  (`ProEtale.RingSheaf.preservesFiniteColimits_lowerStar_of_isCompl`);
* the unit `N ⟶ j^* j_! N` and the counit `i^* i_* G ⟶ G` are isomorphisms, so `j_!` and `i_*`
  are fully faithful, and `j^* i_* = 0`;
* for every `B`-module sheaf `M` the sequence `0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0` is exact
  (`ProEtale.RingSheaf.shortExact_openClosedShortComplex`).

Following the blueprint proof, everything is checked on underlying sheaves of `R`-modules: the
forgetful functor from module objects is faithful, exact, and reflects isomorphisms, and the
operations on module sheaves lie over those on sheaves of `R`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  {A : C} [MonObj A]

/-- A module object whose underlying object is zero is zero. -/
lemma isZero_of_isZero_X {M : Mod C A} (h : IsZero M.X) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext
  exact h.eq_of_src _ _

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Y Z U X : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]

/-! ### Exactness -/

instance preservesFiniteColimits_upperStar (g : Y ⟶ X) :
    PreservesFiniteColimits (upperStar B g) :=
  have := (upperStarLowerStarAdjunction B g).isLeftAdjoint
  inferInstance

instance preservesFiniteLimits_lowerStar (g : Y ⟶ X) :
    PreservesFiniteLimits (lowerStar B g) :=
  have := (upperStarLowerStarAdjunction B g).isRightAdjoint
  inferInstance

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))

instance preservesFiniteColimits_openImmersionLowerShriek :
    PreservesFiniteColimits (openImmersionLowerShriek B i j hij) :=
  have := (openImmersionLowerShriekUpperStarAdjunction B i j hij
    ).isLeftAdjoint
  inferInstance

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (1): the extension by
zero on module sheaves is left exact, since it is so on underlying sheaves. -/
instance preservesFiniteLimits_openImmersionLowerShriek :
    PreservesFiniteLimits (openImmersionLowerShriek B i j hij) := by
  have : PreservesFiniteLimits (openImmersionLowerShriek B i j hij ⋙ Mod.forget B) :=
    inferInstanceAs (PreservesFiniteLimits (Mod.forget _ ⋙ (j)_!open[ModuleCat.{u + 1} R]))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget B)

include j hij in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (2), and blueprint
`proposition-extension-zero-restriction-closed-subscheme--4` for module sheaves: the pushforward
`i_*` along a closed immersion with quasi-compact open complement is exact on module sheaves. -/
theorem preservesFiniteColimits_lowerStar_of_isCompl :
    PreservesFiniteColimits (lowerStar B i) := by
  have := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl (R := R) i j hij
  have : PreservesFiniteColimits (lowerStar B i ⋙ Mod.forget B) :=
    inferInstanceAs (PreservesFiniteColimits (Mod.forget _ ⋙ (i)_*[ModuleCat.{u + 1} R]))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (Mod.forget B)

/-! ### Units, counits and vanishing -/

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (2): the counit
`i^* i_* G ⟶ G` on module sheaves is an isomorphism. -/
instance isIso_upperStarLowerStarAdjunction_counit :
    IsIso (upperStarLowerStarAdjunction B i).counit := by
  have (N : Mod (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))
      ((i)^*[ModuleCat.{u + 1} R].obj B)) :
      IsIso ((upperStarLowerStarAdjunction B i).counit.app N) := by
    have : IsIso ((Mod.forget _).map ((upperStarLowerStarAdjunction B i).counit.app N)) := by
      rw [Mod.forget_map, upperStarLowerStarAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (2): the pushforward
along a closed immersion is fully faithful on module sheaves. -/
noncomputable def fullyFaithfulLowerStar : (lowerStar B i).FullyFaithful :=
  (upperStarLowerStarAdjunction B i).fullyFaithfulROfIsIsoCounit

instance : (lowerStar B i).Full := (fullyFaithfulLowerStar B i).full

instance : (lowerStar B i).Faithful := (fullyFaithfulLowerStar B i).faithful

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (1): the unit
`N ⟶ j^* j_! N` on module sheaves is an isomorphism. -/
instance isIso_openImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (openImmersionLowerShriekUpperStarAdjunction B i j hij).unit := by
  have (N : Mod (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R))
      ((j)^*[ModuleCat.{u + 1} R].obj B)) :
      IsIso ((openImmersionLowerShriekUpperStarAdjunction B i j hij).unit.app N) := by
    have : IsIso ((Mod.forget _).map
        ((openImmersionLowerShriekUpperStarAdjunction B i j hij).unit.app N)) := by
      rw [Mod.forget_map, openImmersionLowerShriekUpperStarAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- The extension by zero is fully faithful on module sheaves. -/
noncomputable def fullyFaithfulOpenImmersionLowerShriek :
    (openImmersionLowerShriek B i j hij).FullyFaithful :=
  (openImmersionLowerShriekUpperStarAdjunction B i j hij).fullyFaithfulLOfIsIsoUnit

omit [IsClosedImmersion i] [QuasiCompact j] in
include hij in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (2): `j^* i_* = 0` on
module sheaves. -/
lemma isZero_upperStar_obj_lowerStar_obj
    (N : Mod (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))
      ((i)^*[ModuleCat.{u + 1} R].obj B)) :
    IsZero ((upperStar B j).obj ((lowerStar B i).obj N)) :=
  Mod.isZero_of_isZero_X (isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint N.X)

/-! ### The open–closed sequence -/

/-- The open–closed short complex `j_! j^* M ⟶ M ⟶ i_* i^* M` of a module sheaf `M`, formed by
the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`. -/
noncomputable def openClosedShortComplex (M : Mod (Sheaf (ProEt.topology X)
    (ModuleCat.{u + 1} R)) B) : ShortComplex (Mod (Sheaf (ProEt.topology X)
    (ModuleCat.{u + 1} R)) B) where
  f := (openImmersionLowerShriekUpperStarAdjunction B i j hij).counit.app M
  g := (upperStarLowerStarAdjunction B i).unit.app M
  zero := by
    apply (Mod.forget B).map_injective
    rw [Functor.map_comp, Functor.map_zero, Mod.forget_map, Mod.forget_map,
      openImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
      upperStarLowerStarAdjunction_unit_app_hom]
    exact (ProEtale.openClosedShortComplex R i j hij M.X).zero

/-- The underlying short complex of sheaves of `R`-modules of the open–closed short complex of
a module sheaf `M` is the open–closed short complex of the underlying sheaf of `M`. -/
noncomputable def openClosedShortComplexMapForgetIso
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    (openClosedShortComplex B i j hij M).map (Mod.forget B) ≅
      ProEtale.openClosedShortComplex R i j hij M.X :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (openImmersionLowerShriekUpperStarAdjunction_counit_app_hom B i j hij M).symm)
    (by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact (upperStarLowerStarAdjunction_unit_app_hom B i M).symm)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (3), and the exact
sequence of blueprint `proposition-extension-zero-restriction-closed-subscheme`: let `i : Z ⟶ X` be
a closed immersion with quasi-compact open complement `j : U ⟶ X` and `B` a sheaf of `R`-algebras on
`X_proét`. For every `B`-module sheaf `M` the sequence `0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0`, formed
by the counit of `j_! ⊣ j^*` and the unit of `i^* ⊣ i_*`, is exact. It is so on underlying sheaves
(`AlgebraicGeometry.ProEtale.shortExact_openClosedShortComplex`), and the forgetful functor
reflects short exactness. -/
theorem shortExact_openClosedShortComplex
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    (openClosedShortComplex B i j hij M).ShortExact := by
  have h : ((openClosedShortComplex B i j hij M).map (Mod.forget B)).ShortExact :=
    ShortComplex.shortExact_of_iso (openClosedShortComplexMapForgetIso B i j hij M).symm
      (ProEtale.shortExact_openClosedShortComplex i j hij M.X)
  exact
    { exact := (ShortComplex.exact_map_iff_of_faithful _ (Mod.forget B)).1 h.exact
      mono_f := (Mod.forget B).mono_of_mono_map h.mono_f
      epi_g := (Mod.forget B).epi_of_epi_map h.epi_g }

end AlgebraicGeometry.ProEtale.RingSheaf
