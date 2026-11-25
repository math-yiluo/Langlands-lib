/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenBaseChange
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare

/-!
# Base change isomorphisms for `j_!` and `i_*` on module sheaves over a sheaf of rings

Let `B` be a sheaf of `R`-algebras on `X_proét`, `i : Z ⟶ X` a closed immersion with
quasi-compact open complement `j : U ⟶ X`, `g : X' ⟶ X` a morphism, and `i' : Z' ⟶ X'`,
`j' : U' ⟶ X'`, `g_Z : Z' ⟶ Z`, `g_U : U' ⟶ U` the base changes, with `i' ≫ g = g_Z ≫ i` and
`j' ≫ g = g_U ≫ j`. This file constructs the canonical isomorphisms of functors on module
sheaves of part (4) of blueprint `proposition-extension-zero-restriction-closed-subscheme`:

* `ProEtale.RingSheaf.openImmersionLowerShriekBaseChangeIso`: `j'_! ∘ g_U^* ≅ g^* ∘ j_!`;
* `ProEtale.RingSheaf.lowerStarBaseChangeIso`: `g^* ∘ i_* ≅ i'_* ∘ g_Z^*`.

Here the `g_U^* j^* B`-module `g_U^* N` is viewed as a `j'^* g^* B`-module along the
isomorphism of coefficient rings `ProEtale.RingSheaf.squareCoeffHom`, and similarly over `Z'`.

Both are assembled from isomorphisms already available on module sheaves, without computing on
underlying sheaves: `j'^* g^* j_! N ≅ g_U^* j^* j_! N ≅ g_U^* N` (the commutative square and
the unit of `j_! ⊣ j^*`) is adjoint to a map `j'_! g_U^* N ⟶ g^* j_! N` which is an isomorphism
since `g^* j_! N` is supported on `U'`
(`ProEtale.RingSheaf.isIso_counit_app_upperStar_obj_openImmersionLowerShriek_obj`); dually
`g^* i_* G ⟶ i'_* i'^* g^* i_* G ≅ i'_* g_Z^* i^* i_* G ≅ i'_* g_Z^* G`, the first map being an
isomorphism since `g^* i_* G` is supported on `Z'`
(`ProEtale.RingSheaf.isIso_unit_app_upperStar_obj_lowerStar_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

variable {R : Type (u + 1)} [CommRing R]

section Restriction

variable {T S₁ S₂ Y : Scheme.{u}} (B : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
  [MonObj B] (f₁ : S₁ ⟶ Y) (f₂ : S₂ ⟶ Y) (h₁ : T ⟶ S₁) (h₂ : T ⟶ S₂)
  (w : h₁ ≫ f₁ = h₂ ≫ f₂) {C : Type*} [Category* C]

/-- For a commutative square `h₁ ≫ f₁ = h₂ ≫ f₂` and a functor `P` to `B`-module sheaves with
`P ⋙ f₂^* ≅ E`, the iterated pullback `h₁^* f₁^* P` is `h₂^* E`, up to restriction of scalars
along `ProEtale.RingSheaf.squareCoeffHom`. -/
noncomputable def upperStarSquareRestrictionIso (E : C ⥤ Mod (Sheaf (ProEt.topology S₂)
      (ModuleCat.{u + 1} R)) ((f₂)^*[ModuleCat.{u + 1} R].obj B))
    (P : C ⥤ Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) B)
    (e : E ≅ P ⋙ upperStar B f₂) :
    E ⋙ upperStar _ h₂ ⋙ Mod.comap (squareCoeffHom B f₁ f₂ h₁ h₂ w) ≅
      P ⋙ upperStar B f₁ ⋙ upperStar _ h₁ :=
  Functor.isoWhiskerRight e _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P ((Functor.associator _ _ _).symm ≪≫
      (upperStarSquareIso B f₁ f₂ h₁ h₂ w).symm)

end Restriction

variable {Z U X Z' U' X' : Scheme.{u}}
  (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj B]
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (g : X' ⟶ X) (i' : Z' ⟶ X') [IsClosedImmersion i'] (j' : U' ⟶ X') [IsOpenImmersion j']
  [QuasiCompact j'] (gZ : Z' ⟶ Z) (gU : U' ⟶ U)
  (hij : IsCompl (Set.range i.base) (Set.range j.base))
  (hij' : IsCompl (Set.range i'.base) (Set.range j'.base))
  (hi : i' ≫ g = gZ ≫ i) (hj : j' ≫ g = gU ≫ j)

/-! ### Extension by zero -/

/-- The restriction to `U'` of `g^* j_! N` is `g_U^* N`: `j'^* g^* j_! N ≅ g_U^* j^* j_! N ≅
g_U^* N`, by the commutative square `j' ≫ g = g_U ≫ j` and the unit of `j_! ⊣ j^*`. -/
noncomputable def upperStarOpenImmersionLowerShriekRestrictionIso :
    upperStar _ gU ⋙ Mod.comap (squareCoeffHom B g j j' gU hj) ≅
      openImmersionLowerShriek B i j hij ⋙ upperStar B g ⋙ upperStar _ j' :=
  (Functor.leftUnitor _).symm ≪≫ upperStarSquareRestrictionIso B g j j' gU hj (𝟭 _) _
    (asIso (openImmersionLowerShriekUpperStarAdjunction B i j hij).unit)

/-- The base change map `j'_! g_U^* ⟶ g^* j_!` on module sheaves: the adjoint, for
`j'_! ⊣ j'^*`, of `ProEtale.RingSheaf.upperStarOpenImmersionLowerShriekRestrictionIso`. -/
noncomputable def openImmersionLowerShriekBaseChangeHom :
    (upperStar _ gU ⋙ Mod.comap (squareCoeffHom B g j j' gU hj)) ⋙
        openImmersionLowerShriek _ i' j' hij' ⟶
      openImmersionLowerShriek B i j hij ⋙ upperStar B g :=
  Functor.whiskerRight (upperStarOpenImmersionLowerShriekRestrictionIso B i j g j' gU hij hj).hom
      (openImmersionLowerShriek _ i' j' hij') ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (openImmersionLowerShriek B i j hij ⋙ upperStar B g)
      (openImmersionLowerShriekUpperStarAdjunction _ i' j' hij').counit ≫
    (Functor.rightUnitor _).hom

include hi in
/-- The base change map `j'_! g_U^* ⟶ g^* j_!` is an isomorphism, since `g^* j_! N` is supported
on `U'`. -/
theorem isIso_openImmersionLowerShriekBaseChangeHom :
    IsIso (openImmersionLowerShriekBaseChangeHom B i j g i' j' gU hij hij' hj) := by
  have (N : _) :
      IsIso ((openImmersionLowerShriekBaseChangeHom B i j g i' j' gU hij hij' hj).app N) := by
    have := isIso_counit_app_upperStar_obj_openImmersionLowerShriek_obj B i j g i' j' gZ hij hij'
      hi N
    simp only [openImmersionLowerShriekBaseChangeHom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' this (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4), and the base
change assertion of blueprint `proposition-extension-zero-restriction-closed-subscheme` for `j_!`:
for a sheaf of `R`-algebras `B` on `X_proét`, a quasi-compact open immersion `j : U ⟶ X` with closed
complement `i`, a morphism `g : X' ⟶ X` and the base changes `j' : U' ⟶ X'`, `i' : Z' ⟶ X'`,
`g_U : U' ⟶ U`, `g_Z : Z' ⟶ Z`, the canonical isomorphism `j'_! g_U^* ≅ g^* j_!` of functors from
`j^* B`-module sheaves on `U_proét` to `g^* B`-module sheaves on `X'_proét`. Here `g_U^* N` is a
`j'^* g^* B`-module along the isomorphism of coefficient rings
`ProEtale.RingSheaf.squareCoeffHom`. It is adjoint to the identification
`j'^* g^* j_! ≅ g_U^* j^* j_! ≅ g_U^*`, and invertible since `g^* j_! N` is supported on
`U'`. -/
noncomputable def openImmersionLowerShriekBaseChangeIso :
    (upperStar _ gU ⋙ Mod.comap (squareCoeffHom B g j j' gU hj)) ⋙
        openImmersionLowerShriek _ i' j' hij' ≅
      openImmersionLowerShriek B i j hij ⋙ upperStar B g :=
  have := isIso_openImmersionLowerShriekBaseChangeHom B i j g i' j' gZ gU hij hij' hi hj
  asIso (openImmersionLowerShriekBaseChangeHom B i j g i' j' gU hij hij' hj)

/-- The forward map of `openImmersionLowerShriekBaseChangeIso` is
`openImmersionLowerShriekBaseChangeHom`. -/
@[simp]
lemma openImmersionLowerShriekBaseChangeIso_hom :
    (openImmersionLowerShriekBaseChangeIso B i j g i' j' gZ gU hij hij' hi hj).hom =
      openImmersionLowerShriekBaseChangeHom B i j g i' j' gU hij hij' hj :=
  rfl

/-! ### Pushforward along the closed immersion -/

/-- The restriction to `Z'` of `g^* i_* G` is `g_Z^* G`: `i'^* g^* i_* G ≅ g_Z^* i^* i_* G ≅
g_Z^* G`, by the commutative square `i' ≫ g = g_Z ≫ i` and the counit of `i^* ⊣ i_*`. -/
noncomputable def upperStarLowerStarRestrictionIso :
    upperStar _ gZ ⋙ Mod.comap (squareCoeffHom B g i i' gZ hi) ≅
      lowerStar B i ⋙ upperStar B g ⋙ upperStar _ i' :=
  (Functor.leftUnitor _).symm ≪≫ upperStarSquareRestrictionIso B g i i' gZ hi (𝟭 _) _
    (asIso (upperStarLowerStarAdjunction B i).counit).symm

/-- The base change map `g^* i_* ⟶ i'_* g_Z^*` on module sheaves: the unit of `i'^* ⊣ i'_*`
followed by `i'_*` of the inverse of
`ProEtale.RingSheaf.upperStarLowerStarRestrictionIso`. -/
noncomputable def lowerStarBaseChangeHom :
    lowerStar B i ⋙ upperStar B g ⟶
      (upperStar _ gZ ⋙ Mod.comap (squareCoeffHom B g i i' gZ hi)) ⋙ lowerStar _ i' :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (lowerStar B i ⋙ upperStar B g)
      (upperStarLowerStarAdjunction ((g)^*[ModuleCat.{u + 1} R].obj B) i').unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (upperStarLowerStarRestrictionIso B i g i' gZ hi).inv (lowerStar _ i')

omit [QuasiCompact j] in
include j hij hij' hj in
/-- The base change map `g^* i_* ⟶ i'_* g_Z^*` is an isomorphism, since `g^* i_* G` is supported
on `Z'`. -/
theorem isIso_lowerStarBaseChangeHom :
    IsIso (lowerStarBaseChangeHom B i g i' gZ hi) := by
  have (G : Mod (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R))
      ((i)^*[ModuleCat.{u + 1} R].obj B)) :
      IsIso ((lowerStarBaseChangeHom B i g i' gZ hi).app G) := by
    have := isIso_unit_app_upperStar_obj_lowerStar_obj B i j g i' j' gU hij hij' hj G
    simp only [lowerStarBaseChangeHom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
      Category.id_comp]
    exact IsIso.comp_isIso' this (Functor.map_isIso _ _)
  exact NatIso.isIso_of_isIso_app _

omit [QuasiCompact j] in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`, part (4), and the base
change assertion of blueprint `proposition-extension-zero-restriction-closed-subscheme` for `i_*`:
for a sheaf of `R`-algebras `B` on `X_proét`, a closed immersion `i : Z ⟶ X` with quasi-compact open
complement `j`, a morphism `g : X' ⟶ X` and the base changes `i' : Z' ⟶ X'`, `j' : U' ⟶ X'`,
`g_Z : Z' ⟶ Z`, `g_U : U' ⟶ U`, the canonical isomorphism `g^* i_* ≅ i'_* g_Z^*` of functors from
`i^* B`-module sheaves on `Z_proét` to `g^* B`-module sheaves on `X'_proét`. Here `g_Z^* G` is
an `i'^* g^* B`-module along the isomorphism of coefficient rings
`ProEtale.RingSheaf.squareCoeffHom`. It is the unit `g^* i_* ⟶ i'_* i'^* g^* i_*`, invertible
since `g^* i_* G` is supported on `Z'`, followed by `i'_*` of the identification
`i'^* g^* i_* ≅ g_Z^* i^* i_* ≅ g_Z^*`. -/
noncomputable def lowerStarBaseChangeIso :
    lowerStar B i ⋙ upperStar B g ≅
      (upperStar _ gZ ⋙ Mod.comap (squareCoeffHom B g i i' gZ hi)) ⋙ lowerStar _ i' :=
  have := isIso_lowerStarBaseChangeHom B i j g i' j' gZ gU hij hij' hi hj
  asIso (lowerStarBaseChangeHom B i g i' gZ hi)

omit [QuasiCompact j] in
/-- The forward map of `lowerStarBaseChangeIso` is `lowerStarBaseChangeHom`. -/
@[simp]
lemma lowerStarBaseChangeIso_hom :
    (lowerStarBaseChangeIso B i j g i' j' gZ gU hij hij' hi hj).hom =
      lowerStarBaseChangeHom B i g i' gZ hi :=
  rfl

end AlgebraicGeometry.ProEtale.RingSheaf
