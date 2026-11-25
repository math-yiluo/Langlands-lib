/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.TraceFormula.PushforwardFamily
public import WeilConjectures.TraceFormula.WeilSheafLowerStarDefs

/-!

# The pushforward of Weil sheaves

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `e_X`, `e_Y` automorphisms with
`e_X ≫ f = f ≫ e_Y`. The pushforward `f_*` of module objects over `ℚ̲̄_ℓ` sends Weil sheaves for
`e_X` to Weil sheaves for `e_Y` (`ProEtale.CondensedRing.weilSheafLowerStar`): the structure
isomorphism of `f_* F` is `e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F`, through the base-change morphism of
the square `e_X ≫ f = f ≫ e_Y` (`ProEtale.CondensedRing.lowerStarBaseChange`), an isomorphism
since `e_X` and `e_Y` are.

The base-change morphism of module objects is defined in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange`.

## Main definitions

- `ProEtale.CondensedRing.weilSheafLowerStar`: the pushforward of Weil sheaves.

## Main results

- `ProEtale.CondensedRing.nonempty_pow_weilSheafLowerStar_iso`: the pushforward commutes with
  the iterated Weil structures, `(f_* F)^{(n+1)} ≅ f_* F^{(n+1)}` as Weil sheaves for `e_Y^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

/-- **The pushforward commutes with the iterated Weil structures**: for a Weil sheaf `F` for
`e_X`, the Weil sheaf `(f_* F)^{(n+1)}` for `e_Y^{n+1}` is the pushforward of the Weil sheaf
`F^{(n+1)}` for `e_X^{n+1}`: the iterated structure isomorphisms agree by the pasting law of the
base-change morphisms (`CategoryTheory.Iso.powSuccStr_pushforwardBaseChange`). -/
theorem nonempty_pow_weilSheafLowerStar_iso (F : WeilSheaf ℓ eX) (n : ℕ) :
    Nonempty (WeilSheaf.pow ℓ ((weilSheafLowerStar ℓ eX eY hf).obj F) (n + 1) ≅
      (weilSheafLowerStar ℓ (eX.pow (n + 1)) (eY.pow (n + 1))
        (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)).obj
        (WeilSheaf.pow ℓ F (n + 1))) := by
  have H := Endofunctor.IsoAlgebra.nonempty_overPowSucc_mapOfNatIso_iso_of_eq
    (P := upperStar (Profinite.padicAlgClRingObj ℓ))
    (c := fun {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) ↦
      upperStarComp (Profinite.padicAlgClRingObj ℓ) f g)
    (Q := lowerStar (Profinite.padicAlgClRingObj ℓ))
    (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ upperStarLowerStarAdjunction _ f)
    (fun f g h ↦ upperStarComp_assoc _ f g h) eX eY f hf n
    (weilSheafLowerStarComparison ℓ eX eY hf) rfl
    (weilSheafLowerStarComparison ℓ (eX.pow (n + 1)) (eY.pow (n + 1))
      (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)) rfl
    (WeilSheaf ℓ eX) (WeilSheaf ℓ eY) (WeilSheaf ℓ (eX.pow (n + 1)))
    (WeilSheaf ℓ (eY.pow (n + 1))) F
    (weilSheafLowerStar ℓ eX eY hf)
    (weilSheafLowerStar ℓ (eX.pow (n + 1)) (eY.pow (n + 1))
      (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n))
    _ _ rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  obtain ⟨i⟩ := H
  exact ⟨eqToIso (WeilSheaf.pow_succ ℓ _ n) ≪≫ i ≪≫
    (weilSheafLowerStar ℓ (eX.pow (n + 1)) (eY.pow (n + 1))
      (Iso.pow_hom_comp_eq_comp_pow_hom eX eY hf n)).mapIso
        (eqToIso (WeilSheaf.pow_succ ℓ F n)).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
