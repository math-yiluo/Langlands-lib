/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!
# The pushforward of Weil sheaves: definition

Let `f : X ⟶ Y` be a morphism of schemes over `Spec k` and `e_X`, `e_Y` automorphisms with
`e_X ≫ f = f ≫ e_Y`. The pushforward `f_*` of module objects over `ℚ̲̄_ℓ` sends Weil sheaves for
`e_X` to Weil sheaves for `e_Y` (`ProEtale.CondensedRing.weilSheafLowerStar`). Its compatibility
with the iterated Weil structures is in `WeilConjectures.TraceFormula.WeilSheafLowerStar`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)

include hf in
lemma commSq_left_of_comp_eq : CommSq eX.hom.left f.left f.left eY.hom.left :=
  ⟨by rw [← Over.comp_left, hf, Over.comp_left]⟩

/-- The Frobenius comparison `f_* ⋙ e_Y^* ≅ e_X^* ⋙ f_*` of the pushforward of module objects:
the base-change morphism of the square `e_X ≫ f = f ≫ e_Y`, an isomorphism since `e_X` and `e_Y`
are. -/
noncomputable def weilSheafLowerStarComparison :
    (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (eY.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (eX.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  asIso (lowerStarBaseChange _ (commSq_left_of_comp_eq eX eY hf))

lemma weilSheafLowerStarComparison_hom :
    (weilSheafLowerStarComparison ℓ eX eY hf).hom =
      lowerStarBaseChange _ (commSq_left_of_comp_eq eX eY hf) :=
  rfl

/-- The pushforward `f_*` of Weil sheaves along `f : X ⟶ Y` with `e_X ≫ f = f ≫ e_Y`: a Weil
sheaf `(F, φ_F)` for `e_X` is sent to `f_* F` with the structure isomorphism
`e_Y^* f_* F ≅ f_* e_X^* F ≅ f_* F` given by `weilSheafLowerStarComparison` and `f_* φ_F`. -/
noncomputable def weilSheafLowerStar : WeilSheaf ℓ eX ⥤ WeilSheaf ℓ eY :=
  IsoAlgebra.mapOfNatIso (weilSheafLowerStarComparison ℓ eX eY hf)

@[simp]
lemma weilSheafLowerStar_obj_carrier (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).carrier =
      (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  rfl

lemma weilSheafLowerStar_obj_str (F : WeilSheaf ℓ eX) :
    ((weilSheafLowerStar ℓ eX eY hf).obj F).str =
      (weilSheafLowerStarComparison ℓ eX eY hf).app F.carrier ≪≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso F.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F

/-- `weilSheafLowerStar` as a transport of algebras. -/
lemma weilSheafLowerStar_eq :
    weilSheafLowerStar ℓ eX eY hf =
      IsoAlgebra.mapOfNatIso (weilSheafLowerStarComparison ℓ eX eY hf) :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
