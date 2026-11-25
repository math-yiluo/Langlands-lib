/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.BaseChange

/-!
# The comparison `g_* g^* ⟶ g'_* g'^*` along a morphism of weakly étale covers

For weakly étale `g : Y ⟶ X`, `g' : Y' ⟶ X` and `s : Y' ⟶ Y` over `X`, the restriction along `s`
(`AlgebraicGeometry.ProEtale.restrictionHom`) conjugated with the comparisons `g^* ≅ j_g^*`
is a monoidal natural transformation `g^* ⋙ g_* ⟶ g'^* ⋙ g'_*`
(`AlgebraicGeometry.ProEtale.upperStarLowerStarHom`). It is compatible with the units of
`g^* ⊣ g_*` and `g'^* ⊣ g'_*` and with the actions of automorphisms of `Y` and `Y'` over `X`
(`AlgebraicGeometry.ProEtale.galoisActionNatTrans_comp_upperStarLowerStarHom`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y Y' Y'' : Scheme.{u}} (g : Y ⟶ X) (g' : Y' ⟶ X) (g'' : Y'' ⟶ X) [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

/-- The action restriction along an automorphism is the restriction along it. -/
lemma galoisActionRestrictionNatTrans_eq_restrictionHom (s : Y ⟶ Y) (hs : s ≫ g = g) :
    galoisActionRestrictionNatTrans g s hs = restrictionHom g g s hs :=
  rfl

variable {g g'} in
lemma restrictionHom_congr {s t : Y' ⟶ Y} (hs : s ≫ g = g') (hst : s = t) :
    restrictionHom g g' s hs = restrictionHom g g' t (hst ▸ hs) := by
  subst hst
  rfl

/-- The restriction `H(V ×_X Y) ⟶ H(V ×_X Y')` along a morphism `s : Y' ⟶ Y` over `X`, as a
natural transformation `g^* ⋙ g_* ⟶ g'^* ⋙ g'_*` of functors of abelian pro-étale sheaves. -/
noncomputable def upperStarLowerStarHom (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    (g)^*[AddCommGrpCat.{u + 1}] ⋙ (g)_*[AddCommGrpCat.{u + 1}] ⟶
      (g')^*[AddCommGrpCat.{u + 1}] ⋙ (g')_*[AddCommGrpCat.{u + 1}] :=
  Functor.whiskerRight (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g
      inferInstance).hom (g)_*[AddCommGrpCat.{u + 1}] ≫
    restrictionHom g g' s hs ≫
    Functor.whiskerRight (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g'
      inferInstance).inv (g')_*[AddCommGrpCat.{u + 1}]

instance isMonoidal_upperStarLowerStarHom (s : Y' ⟶ Y) (hs : s ≫ g = g') :
    NatTrans.IsMonoidal (upperStarLowerStarHom g g' s hs) := by
  unfold upperStarLowerStarHom
  infer_instance

variable {g g' g''}

/-- The unit of `g'^* ⊣ g'_*` is the unit of `j_{g'}^* ⊣ g'_*` followed by `j_{g'}^* ≅ g'^*`. -/
lemma upperStarLowerStarAdjunction_unit_app_eq
    (H : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit.app H =
      (localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g'
        inferInstance).unit.app H ≫
        (g')_*[AddCommGrpCat.{u + 1}].map
          ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} g' inferInstance).inv.app
            H) := by
  erw [← upperStarLowerStarAdjunction_unit_app_comp_assoc g' H]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, comp_id]

/-- The comparison along `s` is compatible with the units of `g^* ⊣ g_*` and `g'^* ⊣ g'_*`. -/
@[reassoc]
lemma upperStarLowerStarAdjunction_unit_comp_upperStarLowerStarHom (s : Y' ⟶ Y)
    (hs : s ≫ g = g') :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit ≫
        upperStarLowerStarHom g g' s hs =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit := by
  ext H : 2
  rw [NatTrans.comp_app, upperStarLowerStarHom, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerRight_app]
  erw [upperStarLowerStarAdjunction_unit_app_comp_assoc]
  have h := congr_app (localizationRestrictionLowerStarAdjunction_unit_comp_restrictionHom s hs) H
  rw [NatTrans.comp_app] at h
  erw [reassoc_of% h]
  rw [upperStarLowerStarAdjunction_unit_app_eq]

variable (g) in
lemma upperStarLowerStarHom_id : upperStarLowerStarHom g g (𝟙 Y) (by simp) = 𝟙 _ := by
  rw [upperStarLowerStarHom, restrictionHom_id, id_comp, ← Functor.whiskerRight_comp,
    Iso.hom_inv_id, Functor.whiskerRight_id']

lemma upperStarLowerStarHom_congr {s t : Y' ⟶ Y} (hs : s ≫ g = g') (hst : s = t) :
    upperStarLowerStarHom g g' s hs = upperStarLowerStarHom g g' t (hst ▸ hs) := by
  subst hst
  rfl

/-- The comparisons along composable morphisms compose. -/
@[reassoc]
lemma upperStarLowerStarHom_comp (s' : Y'' ⟶ Y') (hs' : s' ≫ g' = g'') (s : Y' ⟶ Y)
    (hs : s ≫ g = g') :
    upperStarLowerStarHom g g' s hs ≫ upperStarLowerStarHom g' g'' s' hs' =
      upperStarLowerStarHom g g'' (s' ≫ s) (by rw [assoc, hs, hs']) := by
  simp only [upperStarLowerStarHom, assoc]
  rw [← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id, Functor.whiskerRight_id',
    id_comp, restrictionHom_comp_assoc]

/-- The comparison along `s` intertwines the actions of automorphisms `a` of `Y` and `b` of `Y'`
over `X` with `s ≫ a = b ≫ s`. -/
@[reassoc]
lemma upperStarLowerStarHom_comp_upperStarLowerStarHom_of_comp_eq (s : Y' ⟶ Y)
    (hs : s ≫ g = g') (a : Y ⟶ Y) (ha : a ≫ g = g) (b : Y' ⟶ Y') (hb : b ≫ g' = g')
    (hab : s ≫ a = b ≫ s) :
    upperStarLowerStarHom g g a ha ≫ upperStarLowerStarHom g g' s hs =
      upperStarLowerStarHom g g' s hs ≫ upperStarLowerStarHom g' g' b hb := by
  rw [upperStarLowerStarHom_comp, upperStarLowerStarHom_comp]
  simp only [upperStarLowerStarHom]
  rw [restrictionHom_congr _ hab]

/-- The Galois action on `g_* g^*` is the comparison along the automorphism. -/
lemma galoisActionNatTrans_eq {Γ : Type u} {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g) (i : Γ) :
    galoisActionNatTrans g hρ i = upperStarLowerStarHom g g (ρ i) (hρ i) :=
  rfl

end AlgebraicGeometry.ProEtale
