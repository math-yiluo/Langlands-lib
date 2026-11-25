/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenClosed

/-!
# Base change of the open–closed sequence of module sheaves over a sheaf of rings

For a morphism `g : X' ⟶ X` and base changes `i' : Z' ⟶ X'`, `j' : U' ⟶ X'` of a closed
immersion `i` and its quasi-compact open complement `j`, the pullback `g^*` from `B`-module
sheaves to `g^* B`-module sheaves carries the open–closed sequence of `M` to the open–closed
sequence of `g^* M` (`ProEtale.RingSheaf.openClosedShortComplexBaseChangeIso`), part (4) of
blueprint `proposition-extension-zero-restriction-closed-subscheme`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R] {Z U X Z' U' X' : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (g : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i'] (j' : U' ⟶ X') [IsOpenImmersion j']
  [QuasiCompact j'] (gZ : Z' ⟶ Z) (gU : U' ⟶ U)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4), and the base
change assertion of blueprint `proposition-extension-zero-restriction-closed-subscheme` for the
sequence: for a sheaf of `R`-algebras `B`, the pullback `g^*` carries the open–closed sequence
`0 ⟶ j_! j^* M ⟶ M ⟶ i_* i^* M ⟶ 0` of a `B`-module sheaf `M` to the open–closed sequence of the
`g^* B`-module sheaf `g^* M`, by an isomorphism of short complexes which is the identity on `g^* M`.
Both are short exact, and the first map of each composes to zero with the second map of the other,
as it does on underlying sheaves
(`AlgebraicGeometry.ProEtale.upperStar_map_counit_comp_unit_eq_zero`,
`AlgebraicGeometry.ProEtale.counit_comp_upperStar_map_unit_eq_zero`). -/
noncomputable def openClosedShortComplexBaseChangeIso
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    (openClosedShortComplex B i j hij M).map (upperStar B g) ≅
      openClosedShortComplex ((g)^*[ModuleCat.{u + 1} R].obj B) i' j' hij'
        ((upperStar B g).obj M) :=
  ShortComplex.ShortExact.isoOfCompEqZero
    ((shortExact_openClosedShortComplex B i j hij M).map_of_exact _)
    (shortExact_openClosedShortComplex _ i' j' hij' _)
    (Iso.refl _)
    (by
      rw [Iso.refl_hom]
      erw [Category.id_comp]
      apply (Mod.forget _).map_injective
      rw [Functor.map_comp, Functor.map_zero]
      have e₁ : (Mod.forget _).map (((openClosedShortComplex B i j hij M).map
          (upperStar B g)).f) = (g)^*[ModuleCat.{u + 1} R].map
            ((ProEtale.openImmersionLowerShriekUpperStarAdjunction _ j).counit.app M.X) := by
        change (g)^*[ModuleCat.{u + 1} R].map
          ((openImmersionLowerShriekUpperStarAdjunction B i j hij).counit.app M).hom = _
        rw [openImmersionLowerShriekUpperStarAdjunction_counit_app_hom]
      have e₂ : (Mod.forget _).map (openClosedShortComplex ((g)^*[ModuleCat.{u + 1} R].obj B)
          i' j' hij' ((upperStar B g).obj M)).g =
          (ProEtale.upperStarLowerStarAdjunction _ i').unit.app
            ((g)^*[ModuleCat.{u + 1} R].obj M.X) :=
        upperStarLowerStarAdjunction_unit_app_hom _ i' _
      rw [e₁, e₂]
      exact ProEtale.upperStar_map_counit_comp_unit_eq_zero i j g i' gZ hij hi M.X)
    (by
      rw [Iso.refl_inv]
      erw [Category.id_comp]
      apply (Mod.forget _).map_injective
      rw [Functor.map_comp, Functor.map_zero]
      have e₁ : (Mod.forget _).map (((openClosedShortComplex B i j hij M).map
          (upperStar B g)).g) = (g)^*[ModuleCat.{u + 1} R].map
            ((ProEtale.upperStarLowerStarAdjunction _ i).unit.app M.X) := by
        change (g)^*[ModuleCat.{u + 1} R].map
          ((upperStarLowerStarAdjunction B i).unit.app M).hom = _
        rw [upperStarLowerStarAdjunction_unit_app_hom]
      have e₂ : (Mod.forget _).map (openClosedShortComplex ((g)^*[ModuleCat.{u + 1} R].obj B)
          i' j' hij' ((upperStar B g).obj M)).f =
          (ProEtale.openImmersionLowerShriekUpperStarAdjunction _ j').counit.app
            ((g)^*[ModuleCat.{u + 1} R].obj M.X) :=
        openImmersionLowerShriekUpperStarAdjunction_counit_app_hom _ i' j' hij' _
      rw [e₁, e₂]
      exact ProEtale.counit_comp_upperStar_map_unit_eq_zero i j g j' gU hij hj M.X)

@[simp]
lemma openClosedShortComplexBaseChangeIso_hom_τ₂
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
    (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)
    (M : Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) B) :
    (openClosedShortComplexBaseChangeIso B i j g i' j' gZ gU hij hij' hi hj M).hom.τ₂ = 𝟙 _ :=
  rfl

end AlgebraicGeometry.ProEtale.RingSheaf
