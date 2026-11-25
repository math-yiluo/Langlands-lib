/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!

# The lower and upper shriek of Weil objects

Let `f : X ⟶ Y` be a morphism of schemes and `e_X : X ≅ X`, `e_Y : Y ≅ Y` automorphisms
compatible with `f`, that is `e_X ≫ f = f ≫ e_Y` (`hf`), and write `Φ_X = Le_X^*` and
`Φ_Y = Le_Y^*` for the Frobenius pullbacks on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`
(`WeilConjectures.WeilObject.BoundedConstructible.Defs`). As in
`WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar`, a functor `G` with a commutation
isomorphism `b_G` transports Weil objects by `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`.
The Weil objects here are those for the automorphisms, `WeilBoundedConstructible ℓ e_X.hom`. For a
Frobenius endomorphism, which is not an isomorphism and whose Frobenius square is not cartesian,
the lower shriek of Weil objects is `ProEtale.CondensedRing.weilLowerShriekOfFrobenius` of
`WeilConjectures.TraceFormula.CompactCohomology`.
This file supplies `b_G` for the lower shriek `Rf_!` and the upper shriek `Rf^!` attached to the
chosen compactification of `f` (`ProEtale.CondensedRing.boundedConstructibleLowerShriek` and
`ProEtale.CondensedRing.boundedConstructibleUpperShriek`).

The Frobenius square `e_X ≫ f = f ≫ e_Y` is cartesian, its horizontal maps being isomorphisms
(`ProEtale.CondensedRing.weilFrobeniusSquare`).

* **Lower shriek.** The comparison `b_! : Rf_! ⋙ Φ_Y ≅ Φ_X ⋙ Rf_!`
  (`ProEtale.CondensedRing.weilLowerShriekComparison`) is the compact-support base-change
  morphism of the Frobenius square (`boundedConstructibleLowerShriekBaseChange_padicAlgCl`), an
  isomorphism by the compactly supported base change theorem
  (`isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`).
* **Upper shriek.** The comparison `b^! : Rf^! ⋙ Φ_X ⟶ Φ_Y ⋙ Rf^!` is the mate of the
  inverse of `b_!` for the adjunction `Rf_! ⊣ Rf^!` on both sides
  (`ProEtale.CondensedRing.weilUpperShriekComparison`).

The Frobenius pullback `Φ_X = Le_X^*` is an equivalence, with inverse the pullback along `e_X⁻¹`
(`ProEtale.CondensedRing.isEquivalence_boundedConstructibleUpperStar_of_iso`), by the
composition and identity isomorphisms of the derived pullback.

That the mate `b^!` is an isomorphism (`ProEtale.CondensedRing.isIso_weilUpperShriekComparison`)
follows: the mate of an isomorphism along equivalences is an isomorphism
(`CategoryTheory.isIso_mateEquiv_of_isEquivalence`).

The compactly supported base change theorem is an input from
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek`.

## Main definitions

- `ProEtale.CondensedRing.weilLowerShriek`: the lower shriek `Rf_!` of Weil objects.
- `ProEtale.CondensedRing.weilUpperShriek`: the upper shriek `Rf^!` of Weil objects.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Equivalence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The derived pullback `Le^*` on bounded constructible `ℚ̄_ℓ`-sheaves along an automorphism
`e` of a scheme over `Spec k` is an equivalence: its inverse is the pullback along `e⁻¹`, and
the unit and counit are the composition isomorphisms `L(e⁻¹)^* ⋙ Le^* ≅ L(e ≫ e⁻¹)^* = L(𝟙)^*`
and `Le^* ⋙ L(e⁻¹)^* ≅ L(𝟙)^*`, followed by the identity isomorphism `L(𝟙)^* ≅ 𝟭`
(`boundedConstructibleUpperStarId`). -/
instance isEquivalence_boundedConstructibleUpperStar_of_iso :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.hom)
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ e.inv)
    ((boundedConstructibleUpperStarId _ ℓ X).symm ≪≫ eqToIso (by rw [e.inv_hom_id]) ≪≫
      boundedConstructibleUpperStarComp _ ℓ e.inv e.hom)
    ((boundedConstructibleUpperStarComp _ ℓ e.hom e.inv).symm ≪≫
      eqToIso (by rw [e.hom_inv_id]) ≪≫
      boundedConstructibleUpperStarId _ ℓ X)).isEquivalence_functor

end Equivalence

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y)
  {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
include hf in
/-- The Frobenius square `e_X ≫ f = f ≫ e_Y` is cartesian, its horizontal maps being
isomorphisms. -/
theorem weilFrobeniusSquare : IsPullback eX.hom f f eY.hom :=
  IsPullback.of_horiz_isIso ⟨hf⟩

/-! ### The lower shriek -/

section LowerShriek

/-- The Frobenius comparison `b_! : Rf_! ⋙ Le_Y^* ≅ Le_X^* ⋙ Rf_!` of the lower shriek `Rf_!`
for the chosen compactification of `f` (`ℚ̄_ℓ`-coefficient): the compact-support base-change
morphism `boundedConstructibleLowerShriekBaseChange_padicAlgCl` of the Frobenius square, an
isomorphism by the compactly supported base change theorem
(`isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl`). -/
noncomputable def weilLowerShriekComparison :
    boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY.hom ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom ⋙
        boundedConstructibleLowerShriek ℓ f :=
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ
    (weilFrobeniusSquare eX eY hf)
  asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (weilFrobeniusSquare eX eY hf))

lemma weilLowerShriekComparison_hom :
    (weilLowerShriekComparison ℓ eX eY hf).hom =
      boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (weilFrobeniusSquare eX eY hf) :=
  rfl

/-- The lower shriek `Rf_!` of Weil objects: a Weil object `(K, φ_K)` for `e_X` is sent to
`Rf_! K` with the structure isomorphism `Φ_Y Rf_! K ≅ Rf_! Φ_X K ≅ Rf_! K` given by
`weilLowerShriekComparison` and `Rf_! φ_K`. -/
noncomputable def weilLowerShriek :
    WeilBoundedConstructible ℓ eX.hom ⥤ WeilBoundedConstructible ℓ eY.hom :=
  IsoAlgebra.mapOfNatIso (weilLowerShriekComparison ℓ eX eY hf)

/-- The underlying complex of the image under `weilLowerShriek` (`ℚ̄_ℓ`-coefficient). -/
@[simp]
lemma weilLowerShriek_obj_carrier (K : WeilBoundedConstructible ℓ eX.hom) :
    ((weilLowerShriek ℓ eX eY hf).obj K).carrier =
      (boundedConstructibleLowerShriek ℓ f).obj K.carrier :=
  rfl

/-- The Weil structure of the image under `weilLowerShriek` (`ℚ̄_ℓ`-coefficient). -/
lemma weilLowerShriek_obj_str (K : WeilBoundedConstructible ℓ eX.hom) :
    ((weilLowerShriek ℓ eX eY hf).obj K).str =
      (weilLowerShriekComparison ℓ eX eY hf).app K.carrier ≪≫
        (boundedConstructibleLowerShriek ℓ f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The lower shriek of Weil objects lifts the lower shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the forgetful
functors. -/
lemma weilLowerShriek_comp_forget :
    weilLowerShriek ℓ eX eY hf ⋙ WeilBoundedConstructible.forget ℓ eY.hom =
      WeilBoundedConstructible.forget ℓ eX.hom ⋙
        boundedConstructibleLowerShriek ℓ f :=
  rfl

end LowerShriek

/-! ### The upper shriek -/

section UpperShriek

/-- The Frobenius comparison `b^! : Rf^! ⋙ Le_X^* ⟶ Le_Y^* ⋙ Rf^!` of the upper shriek `Rf^!`
for the chosen compactification of `f` (`ℚ̄_ℓ`-coefficient): the mate, for the adjunction `Rf_! ⊣
Rf^!` on both sides, of the inverse `Φ_X ⋙ Rf_! ⟶ Rf_! ⋙ Φ_Y` of the lower shriek comparison
`weilLowerShriekComparison`. -/
noncomputable def weilUpperShriekComparison :
    boundedConstructibleUpperShriek ℓ f ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eX.hom ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ eY.hom ⋙
        boundedConstructibleUpperShriek ℓ f :=
  (mateEquiv
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (TwoSquare.mk _ _ _ _ (weilLowerShriekComparison ℓ eX eY hf).inv))

/-- The Frobenius comparison of the upper shriek is an isomorphism: it is the mate of an
isomorphism along the Frobenius pullbacks, which are equivalences
(`ProEtale.CondensedRing.isEquivalence_boundedConstructibleUpperStar_of_iso`). -/
instance isIso_weilUpperShriekComparison :
    IsIso (weilUpperShriekComparison ℓ eX eY hf) :=
  isIso_mateEquiv_of_isEquivalence _ _
    (TwoSquare.mk _ _ _ _ (weilLowerShriekComparison ℓ eX eY hf).inv)

/-- The upper shriek `Rf^!` of Weil objects: a Weil object `(K, φ_K)` for `e_Y` is sent to
`Rf^! K` with the structure isomorphism `Φ_X Rf^! K ≅ Rf^! Φ_Y K ≅ Rf^! K` given by
`weilUpperShriekComparison` and `Rf^! φ_K`. -/
noncomputable def weilUpperShriek :
    WeilBoundedConstructible ℓ eY.hom ⥤ WeilBoundedConstructible ℓ eX.hom :=
  IsoAlgebra.mapOfNatIso (asIso (weilUpperShriekComparison ℓ eX eY hf))

/-- The underlying complex of the image under `weilUpperShriek` (`ℚ̄_ℓ`-coefficient). -/
@[simp]
lemma weilUpperShriek_obj_carrier (K : WeilBoundedConstructible ℓ eY.hom) :
    ((weilUpperShriek ℓ eX eY hf).obj K).carrier =
      (boundedConstructibleUpperShriek ℓ f).obj K.carrier :=
  rfl

/-- The Weil structure of the image under `weilUpperShriek` (`ℚ̄_ℓ`-coefficient). -/
lemma weilUpperShriek_obj_str (K : WeilBoundedConstructible ℓ eY.hom) :
    ((weilUpperShriek ℓ eX eY hf).obj K).str =
      (asIso (weilUpperShriekComparison ℓ eX eY hf)).app K.carrier ≪≫
        (boundedConstructibleUpperShriek ℓ f).mapIso K.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ K

/-- The upper shriek of Weil objects lifts the upper shriek on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` along the
forgetful functors. -/
lemma weilUpperShriek_comp_forget :
    weilUpperShriek ℓ eX eY hf ⋙ WeilBoundedConstructible.forget ℓ eX.hom =
      WeilBoundedConstructible.forget ℓ eY.hom ⋙
        boundedConstructibleUpperShriek ℓ f :=
  rfl

end UpperShriek

end AlgebraicGeometry.ProEtale.CondensedRing
